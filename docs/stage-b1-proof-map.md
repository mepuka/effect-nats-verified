# Stage B1 proof map — architecture, proof plot, and the proof packets (r4)

- **Date:** 2026-08-23
- **Pin:** Foldable `f160f50` (snapshot r4 frozen at `8fc740c`; the cleanup lane merged at
  `cd5743a`); the runtime model transliterates `src/internal/JetStreamMemory.ts` @ `bec02ac`
  and `effect/src/Queue.ts` @ `4.0.0-rc.111`.
- **Spec:** `research/2026-08-23-subscriber-stage-b.md` (§0 plain summary; §2 contract; §4
  counterexample; §12 representation; §14–§16 Pass B dispositions, probe record, probe table;
  §17 proof order); statements frozen in `docs/signature-snapshot.md`, "Stage B1 (r4)".
- **Purpose:** what the stage-B1 proofs are, how they fit, and — because the proofs are ground by
  a driven prover (the owner's opencode skill) in packets — exactly what each packet contains: the
  statement verbatim, the allowed edit region, the definitions it reads, the expected shape, the
  gate, and the acceptance criterion. Packets are fired in the order of §3; a packet whose
  statement will not prove as written is a **handoff** (the prover reports the smallest failing
  goal and the hypothesis it believes is missing), never a statement edit.
- **Citation root:** this package directory; `:line` anchors opened at `f160f50`.

## 0. In plain terms

Stage A's theorems describe the subscriber machinery with whole actions; the runtime model
(`Runtime.lean`) describes it with the small steps the program actually takes, and assumption
A4 says the two agree. The proofs below make that a theorem. There are four layers: the queue's
own laws (a pull takes everything; a failure keeps the buffer; a shutdown drops it); an
invariant that every reachable runtime state satisfies (the buffer fits, a parked consumer is
not on a dead queue, a publish in flight has a consistent to-do list); commutation (what one
consumer does never changes what the publisher decides about *another* consumer); and the main
theorem, proved by walking any runtime execution step by step while keeping, on the abstract side,
an "IOU" — the abstract publish and the pulls of already-visited consumers that the abstract side
still owes — and paying it at the end of the fan-out.

## 1. The model in one page

| Module | Defines | Role |
|---|---|---|
| `EffectQueue.lean` | `EffectQueue`, `OfferResult`, `TakeResult`, `size`, `offer`, `fail`, `shutdown`, `takeAll`, `wake` | the queue component (frozen carrier) |
| `Runtime.lean` | `Outcome`, `FanKind`, `FanOut`, `RtSubscriber`, `RtState`, `RtLabel`, `fanOutIds`, `deleteIds`, `rtOp` … `rtCloseB`, `rtStep`, `RtNext`, `ReachableRt`, `RtSubscriber.erase`, `eraseRt`, `rtHistory` | the runtime LTS (frozen) |
| `RtInvariants.lean` | `QueueInv`, `RtSubInv`, `FanOutInv`, `RtInv` | the invariant (clauses frozen) |
| `RtTraces.lean` | `RtTrace`, `runRtSteps`, `finalRt`, `runRtTrace`, `runLabels`, the four scenarios, `allRtTraces` | kernel witnesses (proved) |
| `Sim.lean` | `rtSerial`, `labelSerial`, `abstractHistoryFrom`, `abstractHistory`, `A4Inclusion`, `A4Complete` | the statements (frozen) |
| `EffectQueueLaws.lean` | the nine SB1 theorems (proved 2026-08-23, P1) | queue laws |
| `RtReachable.lean` (to write) | per-label `RtInv` preservation, `rtInv_reachable`, `core_frame`, `core_reachable`, `pending_le_capacity_rt` | SB3, SB6, SB7 |
| `RtCommute.lean` (to write) | `bindStep`, `commute_consumer_publisher`, `commute_consumers` | SB2 |
| `SimRelation.lean` | `pointPassed`, `owedOp`, `corrSub`, `corrOn`, `OwedOk`, `Rel`, `RelHist` — the relation as definitions (proof-side; reshapeable) | the target of P4b |
| `ApplyLemmas.lean` | `lookupSub_updateSub_ne`, `applyPull_other`, `applyUnsubscribe_other`, `applyOp_publish_each`, `applyOp_delete_each`, `applyOp_other_frame`, `applyOp_error_frame` (proved 2026-08-23, P4a); `pullStep_third_none`, `pull_third_none` (proved 2026-08-23, T2) | the abstract independence lemmas; the at-most-two-returning-pulls bound P5 rests on |
| `SimAgree.lean` | `AgreeAt`, `agreeAt_refl`, `agreeAt_symm`, `agreeAt_trans`, `applyPull_agreeAt`, `apply_agreeAt`, `observedOf_agreeAt` (proved 2026-08-23, P5a); `abstractHistoryFrom_agreeAt`, `abstractHistoryFrom_strip_pull` (proved 2026-08-23, P5b-prep) | agreement at one subscriber: the helpers `a4_complete` uses to move other subscribers' pulls without changing what subscriber `k` sees or what its history records |
| `RtWitnesses.lean` | `allSubTraces_count`, `allRtTraces_count`, `sb1_witness`, `sb3_witness`, `a4complete_witness`, `a4inclusion_witness` (proved 2026-08-23, P6a) | non-vacuity witnesses and empty-list guards for the B1 frozen statements |
| `SimProof.lean` (to write) | the abstract independence lemmas, the relation's preservation, `a4_inclusion`, `a4_complete` | SB4, SB5 |

Dependency order: `EffectQueue → Runtime → RtInvariants → RtTraces → Sim → EffectQueueLaws →
RtReachable → RtCommute → SimProof`; all imported by the root. Every proof module is added to
`scripts/Axioms.lean`.

## 2. The proof plot

### 2.1 Queue laws (SB1)

Each law is `cases` on `q.status` (and on `q.buffer` for the empty/non-empty split) followed by
`simp [EffectQueue.takeAll]`-style unfolding or `rfl`; `offer_admits` needs `if_pos hr`,
`offer_refused` needs the status to pick the `_` arm. No invariant involved.

### 2.2 The invariant (SB3) and its corollaries (SB6, SB7)

One preservation lemma per `RtLabel`, then `rtInv_reachable` by the one induction over
`ReachableRt` (the stage-A rule: no second induction; later facts project from `RtInv`). What
each label can break, and the fact that repairs it:

| label | clauses touched | repair |
|---|---|---|
| `op` (publish) | `fanOut` clauses: a new `FanOut` with `remaining := fanOutIds …` | `fanOutIds` is a filter over `subs` with the keys in order → `remainingNodup` from `RtInv.shape`; `remainingKnown` from membership; `decided = none`; `core` by the first slice's `step_preserves_inv` |
| `op` (delete) | `registeredStream` (the stream leaves `core` while subscribers are still registered) | exactly the deletion exemption in the clause |
| `op` (other) | `core` | `step_preserves_inv`; `subs` untouched |
| `register` | `shape` (append `nextId`), `registeredStream` (fresh subscriber: `replayBound` gives `l₀ < nextSequence`), `capacityPos` (guard `capacity ≠ 0`) | as in stage A's `applyRegister_inv` |
| `check` | `decidedRoom`/`decidedNotRemaining` (the decision is recorded; `i` leaves `remaining`) | `size` vs the clause: if the queue is open, `size = buffer.length` (`size_eq_length`) and the decision is `¬(n ≤ length)` → `length < n`; if finished, `status ≠ opened` — the disjunct |
| `resolve` (overflow) | `registeredOpen`, `closingNonempty`/`doneEmpty` for the failed queue | `fail_nonempty`/`fail_empty`; `registered := false` clears `registeredOpen`'s premise |
| `resolve` (admit) | `capacity` (the buffer grows by one) | `decidedRoom`'s first disjunct + `offer_admits`; the second disjunct gives `offer_refused` (no growth) |
| `resolve` (delete kind) | as overflow, with `streamNotFound` | same laws |
| `endFanOut` | `fanOut := none` | nothing to preserve |
| `pull` | `takerLive` (parks only on an open queue), `doneEmpty`/`closingNonempty` (a drained `closing` becomes `done` with `[]`) | `takeAll_drains`, `takeAll_closing`, `exit_after_drain`; the `closeStarted` guard keeps `closeStartedOpen` |
| `wake` | same as `pull` | `wake`'s cases mirror `takeAll` |
| `closeA` | `registeredOpen` (premise cleared), `closeStartedOpen` (status ≠ shutDown from the guard) | the guard `status ≠ shutDown` |
| `closeB` | `shutDownClear`, `takerLive` (taker cleared), `closeStartedOpen` (premise cleared) | `shutdown_clears` and the definition of `shutdown` |

`core_frame` is by cases on the label: every case but `op` is `{ s with subs := … }` (or
`fanOut := …`). `core_reachable`: `ReachableRt s → Reachable s.core` by the same induction,
using the first slice's `Reachable.step` for `op` and `core_frame` elsewhere.
`pending_le_capacity_rt` projects `QueueInv.capacity`.

### 2.3 Commutation (SB2)

Both theorems are `rcases` on the label disjunctions, then `unfold` of the two `rt*` functions
and the observation that they read and write disjoint parts of the state: a consumer step of `j`
reads/writes `lookupRt s.subs j` / `updateRt s.subs j _`; a publisher step of `i` reads
`s.fanOut`, `lookupRt s.subs i`, writes `updateRt s.subs i _` and `fanOut`. The list lemmas
needed: `lookupRt_updateRt_ne : i ≠ j → lookupRt (updateRt l j f) i = lookupRt l i` and
`updateRt_updateRt_comm : i ≠ j → updateRt (updateRt l j g) i f = updateRt (updateRt l i f) j g`
(both by induction on `l`). The `RtInv` hypothesis is used only for `lookupRt`'s stability
(keys are distinct — `RtInv.shape`); if a proof needs nothing from it, bind it as `_hinv`.

### 2.4 The main theorem (SB4) — the relation

**Label mapping** (what each runtime step corresponds to on the abstract side):

| runtime step | abstract | when |
|---|---|---|
| `op` publish/delete (store) | nothing yet — the abstract `op` is **owed** | a fan-out begins |
| `check i`, `resolve i` | nothing | internal |
| `endFanOut` | the owed `op`, then the owed suffix (pulls and unsubscribes of visited subscribers, in runtime order) | pays the IOU |
| `op` (other), `register` | the same label | immediately |
| `pull j` / `wake j` returning a chunk or the exit | `pull j` — **immediately** if no fan-out is in flight or `j`'s linearization point has not passed (`j ∈ remaining`, or `decided = some (j, false)`: an admit decision is linearized at its `resolve`); **owed** if it has (`j ∈ visited`, or `decided = some (j, true)`: an overflow decision is linearized at its `check`, the stale `size` read being the abstract overflow test) | corrected 2026-08-23 (overwatch T7, `research/logs/rt_probe10.lean`: `RtTraces.caseBetween` falsifies the "visited" rule) |
| `pull j` parking | nothing | internal |
| `closeA j` | `unsubscribe j` — **immediately**, whichever side of a fan-out it lands on (measured: both placements are witnesses, because `closeStarted` freezes `j`'s history — overwatch T8) | the `Set` delete is the count change; matching here is what makes the count conjunct hold between the two close steps |
| `closeB j` | nothing | internal |

**The relation.** `Rel (s : RtState) (labels owed : List Label) : Prop` with `sPre := runLabels
initialSub labels` (the abstract state *before* the owed publish):

- `sPre = some sA` for some `sA`, and `labelSerial labels ++ labelSerial owed = rtSerial` of the
  execution so far (kept as a parameter of the induction);
- if `s.fanOut = none`: `owed = []` and **per subscriber** `corr s sA id` (below);
- if `s.fanOut = some f` with `f.kind = publish stream m el`: `owed = .op (publish …) (.ok
  (.sequence m.sequence)) :: suffix` where `suffix` holds only `pull`/`unsubscribe` labels of
  subscribers whose point has passed; for `j ∈ f.remaining` or `f.decided = some (j, false)`:
  `corr s sA j` (pre-publish); for `(i, _) ∈ f.visited` or `f.decided = some (i, true)`: `corr s sPost i` where `sPost` is
  `runLabels sA ([owed publish] ++ (suffix restricted to i))`; `f.remaining ++ (f.decided ids) ++
  (f.visited ids)` is exactly the abstract publish's fan-out set of `sA` (registered, stream,
  filters) — so the abstract publish at `endFanOut` visits the same subscribers with the same
  buffers the runtime's `check` saw;
- the delete kind likewise with `endOne` in place of `deliverOne` and no `decided`;
- histories: for every registered `id`, `abstractHistoryFrom id initialSub [] (labels ++ owed_id)
  = some (rtHistory s id)` where `owed_id` is the owed labels that concern `id` (empty for an
  unvisited one).

`corr s sA id` (one subscriber): with `r := lookupRt s.subs id` and `a := lookupSub sA.subs id`:
if `r.closeStarted ∨ r.queue.status = .shutDown` then `a.status = .shutDown ∧ a.registered =
false` (the runtime queue may still hold a buffer nobody can take — E5); otherwise
`r.erase = a` except that `lastEnqueued` may differ only when `a.status = .shutDown`
(refused offers advance it on the runtime side). Because `observed := chunks.flatten` by
definition, the history clause implies the `observed` equality.

**Why the owed suffix is sound** — the abstract publish applied at `endFanOut` to `sA` makes,
for each subscriber `i` past its point, the same decision the runtime made: for an overflow,
`check i` read `size` equal to the abstract buffer length of `i` in `sA` (`corr` held until the
check) and nothing the runtime did to `i` afterwards is reflected in `sA` (its later pulls are
owed); for an admit, the offer at `resolve i` appended to a buffer equal to `sA`'s (`corr` held
until the resolve — a pull of `i` between the admit `check` and its `resolve` is matched
immediately, shrinking both buffers alike, and `decidedRoom` keeps the admit valid). The abstract independence lemmas
make the per-subscriber bookkeeping local (§3, packet P4a).

**Per-label preservation of `Rel`** is the induction step; **extraction** at a quiescent state
takes `labels` as the witness (`owed = []`), `sA` as the state, the history clause, and the count
clause from `corr` (a registered runtime subscriber ↔ a registered abstract one; the closeA
matching makes de-registration simultaneous).

### 2.5 Completeness of the acceptance sets (SB5)

From `a4_inclusion`'s witness for a run with no scope closures and a fixture trace without
`unsubscribe` labels: the witness is the trace's labels with `pull` labels inserted; show it is
produced by `outcomesFrom` — pulls of `id` inserted at gaps, at most two consecutively (an
`opened` drain disables the next pull; a `closing` drain then the exit pull is two) — and that
other subscribers' pulls do not change `id`'s history (independence again). The conclusion is
membership in `historiesWith apply t id`.

## 3. The packets (fire in order; each is self-contained)

Every packet: **(S)** the statements verbatim from the snapshot; **(M)** the module and its
imports; **(R)** the allowed edit region — the new module and proved helper lemmas only;
**(D)** the definitions the proof reads, by `path:line`; **(E)** the expected proof shape;
**(G)** the gate: `bash scripts/gate.sh` from the package directory, plus
`lake env lean ../../research/logs/sig_probe.lean` diffed against
`research/logs/sig_probe.main.txt` (must be empty); **(A)** acceptance: the gate green, the
statements byte-identical to the snapshot, the module in the root import list and in
`scripts/Axioms.lean`, `README.md` "Layout" and §1 above updated, one commit.

### P1 — `EffectQueueLaws.lean` (SB1)

(S) the nine theorems under "Theorem statements (frozen with r4)", block `EffectQueueLaws.lean`.
(M) `import EffectNatsSubstrate.EffectQueue`. (D) `EffectQueue.lean:57-61` (`size`), `:73-78`
(`offer`), `:82-85` (`fail`), `:88-89` (`shutdown`), `:104-113` (`takeAll`), `:119-130` (`wake`). (E) §2.1. Budget:
small; if any law resists `simp`/`rfl`, report the goal.

### P2 — `RtReachable.lean` (SB3, SB6, SB7)

(S) `rtInv_reachable`, `core_frame`, `core_reachable`, `pending_le_capacity_rt`. (M) `import
EffectNatsSubstrate.RtInvariants`, `EffectNatsSubstrate.EffectQueueLaws`, and the first slice's
`Proofs` (for `step_preserves_inv`, `reachable_inv`, `Reachable`). (D) `Runtime.lean:137-159`
(`rtOp`), `:161-177` (`rtRegister`), `:179-193` (`rtCheck`), `:195-238` (`rtResolve`),
`:240-249` (`rtEndFanOut`), `:251-266` (`rtPull`), `:268-279` (`rtWake`), `:281-286` (`rtCloseA`),
`:288-294` (`rtCloseB`), `:296-305` (`rtStep`); `RtInvariants.lean` for the clauses. (E) §2.2: one lemma per label —
`rtOp_inv`, `rtRegister_inv`, `rtCheck_inv`, `rtResolve_inv`, `rtEndFanOut_inv`, `rtPull_inv`,
`rtWake_inv`, `rtCloseA_inv`, `rtCloseB_inv` — then `rtStep_inv` by cases, then the induction.
Helper lemmas expected: `lookupRt_updateRt_self`, `lookupRt_updateRt_ne`, `mem_updateRt`
(shape preserved), `fanOutIds_nodup`, `fanOutIds_subset`. The probe table (slice §16) names the
state each clause excludes — when a case looks impossible, that is the clause to use.

### P3 — `RtCommute.lean` (SB2)

(S) `bindStep`, `commute_consumer_publisher`, `commute_consumers`. (M) `import
EffectNatsSubstrate.RtReachable`. (D) as P2 plus `lookupRt`/`updateRt` (`Runtime.lean:80-88`).
(E) §2.3. Note the non-commutation that is *not* claimed: `closeA i` against `op` — `op` fixes the
fan-out list from the still-registered subscribers; SB2 is scoped to the fan-out's internal labels.

### P4a — abstract independence lemmas (SB4 prerequisite, in `ApplyLemmas.lean`)

(M) `EffectNatsSubstrate/ApplyLemmas.lean`, `import EffectNatsSubstrate.SubReachable` (reuses
`lookupSub_map`, `updateSub_keys`, `lookupSub_updateSub_self`; adds `lookupSub_updateSub_ne`).
Proof-side helpers, not frozen: the seven statements are elaborated in
`research/logs/p4a_statements.lean` (overwatch round 4, `rt_probe13.lean`, 0 failures on 1 088
abstract states) and may be reshaped by P4b with a Lane-log note. Independent of P2/P3 — runs as
its own lane. On stage A's `apply`: `applyPull_other : i ≠ j → lookupSub (applyPull pull s i).subs j =
lookupSub s.subs j` (when enabled); `applyUnsubscribe_other` likewise; `applyOp_publish_each :
apply s (.op (publish …) (.ok (.sequence seq))) = some s' → lookupSub s'.subs j = (lookupSub
s.subs j).map (deliverOne stream m)` (from `afterOp`'s `map`), and the `deleteStream` analogue
with `endOne`; `applyOp_other_frame` for the other operations; `applyOp_error_frame : apply s (.op o (.error err)) = some s' → s' = s`
(the error branch, `Next.lean:119`). (D) `Next.lean:106-124`
(`afterOp`, `applyOp`), `:134-163` (`applyRegister`, `applyPull`, `applyUnsubscribe`), `:165-169`
(`applyWith`). These
are the "per-subscriber independence" assumption of the stage-A slice document §14, now proved.

### P4b — the relation and its preservation (SB4)

(S) `a4_inclusion : A4Inclusion`. (M) `import EffectNatsSubstrate.RtCommute`,
`EffectNatsSubstrate.Sim`, `EffectNatsSubstrate.SubHistory` (if `pendingLast` is needed for a
pre-offer `lastEnqueued`; the relation as designed avoids it by keeping the pre-publish abstract
state rather than undoing offers). (E) §2.4; the relation is already defined in `SimRelation.lean` (`Rel`, `RelHist`, `corrSub`,
`pointPassed`, `owedOp`) — reshape it only if a preservation step proves it too strong or too weak,
and say so in the Lane log. Prove `rel_initial`, one `rel_step_<label>` per label (the mapping table says which abstract labels to append to `labels`
or to `owed`), `rel_endFanOut` (the IOU is paid: apply the owed publish and the suffix; the
abstract decisions agree with the runtime's — use `corr` for the visited subscribers at their
check time, carried as a clause of `Rel`), then `a4_inclusion` by induction on `rls` and
extraction at `fanOut = none`. The proof may generalise `A4Inclusion` to an auxiliary statement
over `rls`, `labels`, `owed` and derive the frozen one; the frozen statement is the acceptance.

### P5 — `a4_complete : A4Complete` (SB5)

(S) `A4Complete` **as of r4.1** (valid-trace hypothesis; the r4 form is refuted in
`scripts/A4CompleteR4Refutation.lean`). The proof needs, from P4b, an auxiliary form of
`a4_inclusion` whose witness `labels` contains only `.op`/`.register`/`.pull` labels when the run has
no `closeA`/`closeB` (the frozen `A4Inclusion` does not say so) — P4b must prove and export that
auxiliary statement. Then: other subscribers' pulls can be moved to the trace's positions without
changing `id`'s history or any label's enabledness (`ApplyLemmas.lean`, a per-label "agree except at
`j`" induction), and a valid placement of `id`'s pulls into `labelsWithoutPulls t id` with at most
two consecutive (`pull_third_none`) is enumerated by `outcomesFrom`. (E) §2.5, from `a4_inclusion`'s witness; helper: `historiesFrom_contains_of_valid`
(a valid label sequence of the trace's serial with `id`'s pulls inserted, at most two
consecutively, is enumerated by `outcomesFrom`). **Required, not optional:** the "at most two returning pulls
per abstract gap" bound that `pullsAtGap`'s fuel encodes (`SubPlacements.lean`) is proved as a
named lemma (each returning pull either empties `pending` or moves `done` to `shutDown`, and
`pullStep` is `none` on an empty open buffer or a shut-down subscriber — `Next.lean:75-87` — so a
third consecutive pull of one subscriber never returns) before `a4_complete` uses it; an enumeration probe is not acceptance evidence
(overwatch Q12, disposed 2026-08-23).

### P6 — `RtWitnesses.lean`: non-vacuity witnesses and empty-list guards (owner's request, 2026-08-23)

Every frozen theorem with hypotheses gets a kernel-checked instance where the hypotheses hold and
the conclusion is not trivial, and every `decide`d trace theorem gets a guard against an empty list.
Proof-side module, `import EffectNatsSubstrate.RtCommute` (for the frozen `bindStep`) — so after
P3 merges. Statements elaborated and **decided true** in `research/logs/p6_witnesses.lean`:
`allSubTraces_count : allSubTraces.length = 9`, `allRtTraces_count : allRtTraces.length = 4`;
`midFanOut` (the §4.2 run just after its second publish; a fan-out in flight, remaining `[0, 1]`);
`sb2_witness` (at `midFanOut`, `pull 1` and `check 0` are enabled in either order and the orders
agree — pairing `pull 1` with `check 1` is the §4.2 non-commutation SB2 excludes by `i ≠ j`, and the
probe confirmed it does not commute); `sb3_witness` (`midFanOut` has a fan-out in flight and a
non-empty buffer — SB3/SB7 have something to say); `a4complete_witness` (`abstract42` is a valid
trace without `unsubscribe`, the `counterexample` run has its serial labels, ends quiescent without
closes, and both acceptance sets have ≥ 2 histories). Plus, per SB1 law, one concrete queue
satisfying its hypotheses (cheap; list them in the module). All in `scripts/Axioms.lean`. The B1
assurance review cites this module for axis "statement non-vacuity".

## 4. Gate

`bash scripts/gate.sh` (build clean, forbidden sweep, `#print axioms` over `scripts/Axioms.lean`,
exporter twice in both modes) and the signature probe diff, after every change. A statement
change is not proof repair: it returns to the slice document and the snapshot with an old/new
entry in the r4 revision log.
