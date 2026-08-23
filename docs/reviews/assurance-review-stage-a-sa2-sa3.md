# Assurance review — Stage A SA2/SA3 at `bedc54e`

- **Date:** 2026-08-22
- **Reviewed commit:** `bedc54e228064b9d9772a1bb39480bc21fc87eb0`
- **Parent:** `06879532289f1e57d02689e141f00cadc0dab9f7`
- **Primary delta:** `SubReachable.lean`, plus the argument-order change to `SubInv.core_eq`
- **Method:** independent proof jury, semantic/refinement referee, literature referee, and fresh
  detached-worktree acceptance gates
- **Mutation:** no proof, model, fixture, or implementation file was changed. Uncommitted files in
  the user's working tree, including `SubStatements.lean`, were excluded from the review.

## Headline verdict

**Accept the Lean derivation as a local safety proof; require major revision before treating the
commit as a verified implementation seam or as discharge of the full prose SA2 contract.**

At the reviewed commit, Lean 4.33.0 accepts that every state in the project-defined
`ReachableSub` closure satisfies `StateInv`, quantified over the actual eleven-field `SubInv`, and
hence every subscriber pair in such a state has `pending.length ≤ policy.capacity`. No
proof-invalidity, undischarged Lean premise, dependency cycle, forbidden proof mechanism, or
trust-policy violation was found.

More precisely, no premise needed to derive these theorems from the committed Lean definitions is
missing; the runtime-transfer premises and relations discussed below do not exist yet.

That is the strongest supported claim. It does not establish:

- the stale prose clause that every pending message remains in current retained core storage;
- that runtime pulls/unsubscribe are atomic only between interpreter operations;
- that Effect Queue or `JetStreamMemory.ts` refines the Lean transition system;
- exact consume-protocol behavior, T8′–T13′, or T14′ liveness;
- live-adapter, durable-consumer, acknowledgment, redelivery, crash, or recovery behavior.

## 1. Proof and trust verdict

### 1.1 Obligation chain

```text
lookupSub ──> mem_of_lookupSub ───────────────┐
updateSub ──> mem_updateSub ───────────────┐  │
SubInv ─────> SubInv.core_eq               │  │
                                             v  v
step/afterOp ─> afterOp_inv ─> applyOp_inv
newSubscriber_inv + reachable_sequences_strict ─> applyRegister_inv
pullStep_inv ────────────────────────────────────> applyPull_inv
unsubscribe_inv ─────────────────────────────────> applyUnsubscribe_inv
        four label-preservation theorems ────────> apply_inv
reachableSub_core + apply_inv ───────────────────> stateInv_reachable
stateInv_reachable + SubInv.capacity ────────────> pending_le_capacity
```

The new proof factors preservation by label, dispatches once in `apply_inv`, and performs one
induction over `ReachableSub` (`EffectNatsSubstrate/SubReachable.lean:51-206`). SA3 is exactly the
projection of the `capacity` field from SA2 (`EffectNatsSubstrate/SubReachable.lean:208-211`). This
respects the package's state-transition seam and avoids a second reachability induction.

The load-bearing applications discharge their hypotheses:

- publish obtains the source stream, exact core update, returned sequence, non-decreasing lookups,
  and strict head bump from `publishStep_ok_eq` and `applyPublish`
  (`SubReachable.lean:55-86`; `Step.lean:95-105`);
- registration obtains positive capacity from the guard, replay bounds from the successful branch,
  and replay ordering from `reachable_sequences_strict`
  (`SubReachable.lean:131-158`);
- pull and unsubscribe recover source-list membership through `lookupSub`/`updateSub` and apply the
  already-proved local preservation lemmas (`SubReachable.lean:160-192`).

### 1.2 Fresh gates

A second detached checkout had no pre-existing `.lake` and produced:

```text
lake build
# Build completed successfully (19 jobs), no warnings or errors
```

The forbidden-mechanism sweep found no `sorry`, `admit`, custom `axiom`, `native_decide`,
`bv_decide`, `unsafe`, `extern`, `implemented_by`, or `sorryAx` in the package sources. The toolchain
is `leanprover/lean4:v4.33.0`; `lake-manifest.json` has no dependencies.

`#print axioms` on all ten added theorems, plus the changed public helper `SubInv.core_eq`, reported:

- `mem_of_lookupSub`, `mem_updateSub`: `propext`;
- every other new theorem and `SubInv.core_eq`: `propext`, `Classical.choice`, `Quot.sound`.

This is within the package policy. Two warmed exporter executions were byte-identical (12,341
characters); the first uncached invocation differed only because Lake prepended build progress.

### 1.3 Proof-jury verdict

| Question | Verdict |
|---|---|
| Theorems accepted as stated over committed definitions | **PASS** |
| SA3 / T14′ capacity safety of the Lean LTS | **PASS** |
| Full prose SA2 contract discharged | **FAIL — statement/model mismatch** |
| Runtime or live-system fidelity | **UNKNOWN / not established** |

## 2. Findings

### F1 — proofs landed before the advertised r3 freeze

- **Class / severity / status:** `spec-mismatch`, **major**, confirmed.
- **Evidence:** the slice says its statements are proposals until r3 is frozen
  (`research/2026-08-22-subscriber-stage-a.md:3-9`). The prior design acceptance requires r3 to
  freeze the statements before any proof
  (`research/2026-08-22-effect-nats-subscriber-model-design-note.md:415-425`). At the reviewed
  commit, the snapshot still says “proposed, pending owner ratification”
  (`docs/signature-snapshot.md:217-225`), while the slices plan records SA2/SA3 as proved and r3 as
  still proposed (`research/2026-08-22-effect-nats-lean-slices-plan.md:74-81`).
- **Additional drift:** the package README still says there are no subscribers
  (`README.md:30-35`), although the root library imports `SubReachable` and the commit proves
  subscriber theorems. The snapshot describes `SubInv` as eight clauses
  (`docs/signature-snapshot.md:244-247`), while the implemented structure has eleven fields
  (`EffectNatsSubstrate/SubInvariants.lean:29-43`).
- **Correction:** describe the current result as a proof against a candidate r3 contract. Correct
  the contract and public package scope, then obtain owner ratification before calling the surface
  frozen.

### F2 — the Stage A atomicity assumption regresses a known Verify finding

- **Class / severity / status:** `model-mismatch` / `implementation-gap`, **major**, confirmed.
- **Evidence:** Stage A says pulls may interleave between operations but “never run inside” one
  because operations hold the permit (`research/2026-08-22-subscriber-stage-a.md:88-102`), and
  repeats that as a domain assumption (`:284-295`). The corrected design note says the opposite:
  a consumer fiber may run between publisher steps while the permit is held
  (`research/2026-08-22-effect-nats-subscriber-model-design-note.md:114-129`). VP1-04 had already
  classified the old conclusion as a confirmed major mismatch
  (`research/2026-08-22-effect-nats-substrate-vp1.md:130-143`).
- **Pinned source:** publish performs separate Effect steps for `Queue.size`, `Queue.fail`, and
  `Queue.offer` (`effect-nats` `872bd7f`, `src/internal/JetStreamMemory.ts:181-200`); the permit
  remains held around a restored, schedulable body (`effect/src/Semaphore.ts:287-309`).
- **Consequence:** the Lean model allows whole `pull` labels only between whole `op` labels
  (`EffectNatsSubstrate/Next.lean:25-38,165-180`). T14′'s numeric bound is plausibly robust to the
  omitted interleavings, and TerminateOnLag executions may admit a quiescent linearization, but no
  theorem establishes that transfer. Unsubscribe during a snapshotted fan-out is another omitted
  interleaving seam.
- **Correction:** either phase-split publish/fan-out into an open-system relation with environment
  actions, or explicitly call Stage A a quiescent abstraction and prove a stuttering/linearizability
  or trace-inclusion bridge from the runtime.

### F3 — SA2's prose invariant contains a false current-storage clause

- **Class / severity / status:** `spec-mismatch`, **major**, confirmed.
- **Evidence:** the slice says every pending entry matches filters **and is stored in `core`**
  (`research/2026-08-22-subscriber-stage-a.md:297-307`). Actual `SubInv` has matching, ordering,
  bounds, and status fields, but no core-message membership field
  (`EffectNatsSubstrate/SubInvariants.lean:29-45`).
- **Counterexamples:**
  - stream deletion removes the core stream while `endOne` deliberately keeps a non-empty pending
    buffer for drain-before-failure (`EffectNatsSubstrate/Next.lean:62-71,105-114`);
  - with per-subject retention 1 and subscriber capacity 2, two publishes yield pending
    `[m1,m2]` while current core storage retains only `m2`. A kernel-evaluated probe returned
    `(m1 ∈ pending = true, m1 ∈ core = false, pending.length = 2, core.length = 1)`.
- **Internal evidence of drift:** the slice's later handoff recognizes that pruning and rollup make
  historical messages non-derivable from current state and rejects a ghost list for the executable
  model (`research/2026-08-22-subscriber-stage-a.md:413-430`), but the earlier obligation was not
  corrected.
- **Correction:** SA2 proves exactly the implemented eleven-field `SubInv`. If enqueue provenance is
  required for SA5/refinement, relate pending entries to a proof-only committed-history variable or
  transition trace, not to current retained storage.

### F4 — Q1–Q3 are encoded semantics, not discharged assumptions

- **Class / severity / status:** `implementation-gap` / `external-trust`, **major**, confirmed.
- **Evidence:** the snapshot acknowledges Q1–Q3 are unproved until Stage B
  (`docs/signature-snapshot.md:250-253`). In Lean they are built into `pullStep`, `endOne`, and
  unsubscribe (`EffectNatsSubstrate/Next.lean:17-20,62-87,156-163`); SA2/SA3 have no runtime queue
  premise (`EffectNatsSubstrate/SubReachable.lean:194-211`).
- **Consequence:** kernel acceptance validates the list model that defines whole-buffer drain,
  drain-before-failure, and shutdown-discard. It does not prove those facts about Effect Queue.
- **Correction:** Stage B needs an `EffectQueue` transition system plus an observation projection and
  simulation from queue/fiber executions to the Stage A list steps. Scheduler assumptions remain
  external even after the queue source is transliterated.

### F5 — no Stage A implementation/refinement bridge exists at this commit

- **Class / severity / status:** `implementation-gap`, **major**, confirmed.
- **Evidence:** the earlier r2 assurance review already recorded the absent refinement relation as
  F5 (`docs/reviews/assurance-review-r2.md:85-98`). Stage A assigns harness realizability and live
  behavior to deployment tests (`research/2026-08-22-subscriber-stage-a.md:323-329,396-411`). The
  committed exporter still prints only sequential schema-1 traces, not `allSubTraces`
  (`Main.lean:117-134`).
- **Correction:** until the schema-2 harness exists, the strongest implementation wording is
  “the abstract transitions were derived from the pinned sources under declared carrier and
  scheduling abstractions, with finite model witnesses,” not “the memory interpreter satisfies
  SA2/SA3.” The harness will add differential evidence, not a universal proof; an explicit
  refinement or trace-inclusion theorem remains the higher assurance goal.

### F6 — the commit claims an absorbed prior-art artifact that it does not contain

- **Class / severity / status:** `external-trust` / provenance gap, **major**, confirmed.
- **Evidence:** the snapshot says the Lean prior-art survey's closing map B was absorbed
  (`docs/signature-snapshot.md:217-223`), and the slice repeats that claim
  (`research/2026-08-22-subscriber-stage-a.md:413-430`). The file
  `research/2026-08-22-lean-prior-art-session-automata-queues.md` is absent from the `bedc54e` tree;
  it exists only as an untracked post-commit file in the user's current worktree. The earlier
  prior-art ledger in the same slice still calls the sweep pending (`subscriber-stage-a.md:331-340`).
- **Correction:** commit and index the evidence artifact, or remove the absorbed claim, before r3
  ratification. The post-commit file agrees with the chosen small-LTS architecture but cannot
  retroactively support the reviewed commit.

### F7 — SA2/SA3 are intentionally too weak to certify consume behavior

- **Class / severity / status:** `observational-gap`, **minor for SA3; major if generalized to
  protocol correctness**, confirmed.
- **Evidence:** `visible` appends pending entries as future-visible, while `entrySequences` erases
  `CaughtUp`, failures, payloads, headers, and timestamps (`SubInvariants.lean:21-27`). The invariant
  constrains sequence order and capacity, not the exact `Observed` protocol.
- **Wrong-model probe:** a mutant that silently replaces a full buffer with the newest message and
  stays registered fails the full `saLag` witness, but after the C13 overflow prefix reports
  `(pending.length=1, capacity=1, registered=true, opened=true, pending=[4])`. Thus the capacity
  formula is compatible with bounded silent loss. A drop-all-publishes mutant is even more plainly
  capacity-safe.
- **Correction:** do not inflate SA2/SA3 into loss-freedom, lag correctness, or `CaughtUp`/failure
  ordering. Planned exact-observation theorems SA5/SA7 and implementation replay are the relevant
  discriminators.

### F8 — two useful state-shape/refinement obligations remain explicit

- **Class / severity / status:** `model-mismatch` / `observational-gap`, **minor**, confirmed.
- **Subscriber shape:** `SubState` says subscriber ids are ascending, but `StateInv` does not state
  id uniqueness/order, `id < nextId`, or exact `nextId` correspondence
  (`Subscriber.lean:90-96`; `SubInvariants.lean:45`). SA3 does not need these facts, but the claimed
  JS `Set` insertion-order seam does.
- **Registration widening:** memory registration fixes `lastDelivered = nextSequence - 1`
  (`effect-nats` `872bd7f`, `JetStreamMemory.ts:233-239`), while `replayBound` accepts any
  environment-supplied value that bounds replay and is below the head
  (`EffectNatsSubstrate/Next.lean:122-145`). For `newOnly`, any `l₀ < nextSequence` is admitted,
  including histories the memory interpreter cannot produce.
- **Correction:** add a reachable `SubStateShape` theorem and a memory-specific registration
  refinement/constructor deriving the exact initial value. Keep the wider generic model only if its
  abstraction purpose is named.

## 3. Referee and literature synthesis

The separately indexed literature review is
`research/2026-08-22-effect-nats-subscriber-stage-a-literature-referee.md`. Its main conclusions are:

- **Auxiliary history:** Abadi–Lamport refinement mappings and Lamport–Merz auxiliary variables fit
  the pruning/rollup seam. A proof-only monotone committed history can retain provenance without
  polluting the reducible executable state.
- **Open systems and fairness:** I/O automata distinguish input/output/internal actions and put
  fairness on executions. Stage A is accurately a partial LTS; it should not acquire I/O-automaton
  or liveness claims until request, suspension, wake-up, completion, and fairness are represented.
- **Reified interpreters:** Interaction/Choice Tree work supports separating syntax, handlers, and
  behavioral refinement when recursive programs or scheduler nondeterminism enter. A free program
  layer would be disproportionate for SA2's one-step invariant, but the architectural separation is
  useful for Stage B.
- **Concurrent queue proofs:** recent linearizability/simulation work reinforces the need for an
  invocation/response history and a refinement layer. Results assuming deterministic non-blocking
  sequential specifications do not transfer directly to Effect Queue's blocking/closing lifecycle.
- **Durable/session boundaries:** ack/redelivery/recovery and communicating-role projection are not
  represented here. Their omission is appropriate. Applying JetStream durable-consumer or
  session/CFSM results to this centralized local queue would be a category error until those states,
  roles, and channels exist.

## 4. Evidence bundle

```text
proved       : stateInv_reachable and pending_le_capacity over the committed Lean LTS;
               fresh kernel build; axioms within {propext, Classical.choice, Quot.sound}
modelChecked : — (no bounded exhaustive state-space search)
tested       : eight named Stage A finite model witnesses and W1/W2 negative controls by kernel
               decide; no Stage A TypeScript schema-2 replay at bedc54e; sequential schema-1 bridge only
measured     : —
monitored    : —
assumed      : Q1–Q3 source readings; Lean kernel/core library/toolchain; source derivation under
               declared carrier restrictions
unknown      : runtime-to-LTS refinement; scheduler/interleaving adequacy; Stage A harness fidelity;
               validation of the quiescent model restriction; T8′–T13′; T14′ liveness; live,
               durable, and failure/recovery behavior
```

## 5. Per-axis and end-to-end verdict

| Axis | Verdict | Reason |
|---|---|---|
| Intent → formal model | **NEEDS REWORK** | unfrozen r3, stale/false invariant prose, atomicity regression |
| Model → theorem | **PASS WITH NARROW SCOPE** | proof exactly establishes the actual eleven-field invariant and capacity corollary |
| Proof trust | **PASS** | clean build, accepted dependencies, policy-compliant axioms, no forbidden mechanisms |
| Implementation/refinement | **GAP** | Q1–Q3 encoded; no runtime simulation/trace-inclusion; no schema-2 replay |
| External/deployment | **GAP / OUT OF SCOPE** | scheduler, live adapter, durability, fairness, failures not modeled |
| End to end | **MAJOR REVISION** | accept local LTS safety only; reject broader verification wording |

## 6. Recommended order of work

1. Correct the Stage A atomicity statement and the false current-storage clause; reconcile the
   eleven-field invariant, README, snapshot, plan, and missing prior-art artifact; then ratify r3.
2. Keep SA2/SA3's proof meaning and architecture. Do not weaken or rewrite a proof that already
   establishes the intended local capacity bound.
3. Add `SubStateShape` and a proof-only committed-history/refinement layer before SA5/SA7 rely on
   list order or historical provenance.
4. Decide the runtime seam explicitly: a phase-split open-system model, or a quiescent abstraction
   plus weak/stuttering simulation from Effect Queue and `JetStreamMemory.ts`.
5. Complete exact-observation SA5–SA7, schema-2 export/replay, and negative-control coverage. Treat
   replay as differential evidence and keep the universal refinement obligation visible.
6. Add Stage B blocking/closing execution semantics and named fairness before attempting T14′
   liveness. Keep durable and session/CFSM claims in later, separately related layers.

## Correction log (append-only)

Correct pass of 2026-08-22 over this review (F1–F8), the same-day Standards/Spec review of
`61b3663..bedc54e` (S1–S6 and its smell list; Spec findings), and the literature referee
(`research/2026-08-22-effect-nats-subscriber-stage-a-literature-referee.md`, LR-01–08). Every
finding was re-verified against the tree before its entry (precedence tree > pass > document).
Owner of every entry: the Claude lane; the two reviews were left unedited above this line.

- [claude | slice doc, snapshot, plan, package AGENTS/README | F1] APPLIED — snapshot r3 → r3.1, still proposed; plan row 4 records that SA1–SA3 (and SA4b) were proved ahead of its "frozen before proofs" gate; package `AGENTS.md` "Statement freeze" now states that a proposed section is not a licence to prove; `README.md` and `AGENTS.md` scope/pins updated (two citation roots; "Deferred means absent" rewritten); snapshot carriers block says eleven clauses and names them.
- [claude | slice doc §2.4, §9.1, §13; snapshot assumptions | F2] APPLIED — the sentence "they never run inside an operation, because operations hold the permit" (a regression of VP1-04) → assumption **A4**: pulls and scope closures never take the permit (only registration does, `JetStreamMemory.ts:224` @ `872bd7f`); the model is a quiescent abstraction whose linearizability argument for `TerminateOnLag` is stated, not proved, and assigned to the stage-B bridge / falsifiable by the schema-2 harness.
- [claude | slice doc §9.2, §11 | F3] APPLIED — "every pending entry … is stored in `core`" removed with the rollup, pruning, and deletion counterexamples; the eleven implemented clauses listed; the global T8′ form restated over an Abadi–Lamport history variable (SA5h, erasure + lifting + `visible_global`) — the review's own correction, adopted.
- [claude | — | F4] no change — Q1–Q3 were already declared "named, not proved" (snapshot assumptions); wording unchanged.
- [claude | package README | F5] APPLIED (wording only) — README scope now says nothing here is a statement about Effect `Queue`, the interpreter, or `nats-server` beyond compatibility on replayed histories; schema-2 export/replay stays SA9, pending.
- [claude | tree; slice doc §10 | F6] APPLIED — `research/2026-08-22-lean-prior-art-session-automata-queues.md` and `research/2026-08-22-session-types-pilot-vp1.md` committed (their README rows were already at HEAD); the §10 ledger row now cites the landed document.
- [claude | — | F7] no change — SA2/SA3 keep their meaning; the silent-loss mutant probe is the recorded reason SA3 is never read as loss-freedom (slice §8 already bounds the claim).
- [claude | slice doc §4.2, §9.1, §9.2, §11, §13; snapshot; `SubInvariants.lean` | F8] APPLIED — `SubShape` defined (ids strictly ascending, all `< nextId`), `subShape_reachable` a freeze candidate; the `lastEnqueued₀` envelope named as an abstraction wider than memory's histories, with SA4d (`memory_lastEnqueued_admissible`) pinning memory's `nextSequence - 1`.
- [claude | `Subscriber.lean`, `Next.lean`, slice doc §2.1–§2.3 | S1 citations carried across the pin move] APPLIED — re-opened in `git show 872bd7f:src/internal/JetStreamMemory.ts`: `:177`→`:182`, `:183`→`:188`, `:195`→`:200`, `:176-178`→`:181-183`, `:181-192`→`:185-195`, `:194-195`→`:199-200`, `:194`→`:199`, `:176-199`→`:181-200`, `:126-135`→`:127-136`; §2.3 `:129`→`:131`, `:130-134`→`:132-135` (not in the review; found while re-opening). Package `AGENTS.md` now requires re-opening every `:line` citation when a pin moves.
- [claude | tree | S2 index rows to absent files] APPLIED — see F6.
- [claude | package `AGENTS.md`, `README.md`, snapshot header | S3 stale package contract] APPLIED — see F1.
- [claude | — | S4 proofs before the freeze] APPLIED — see F1; proofs of SA4–SA7 resume after ratification.
- [claude | — | S5 snippet rule] REJECTED — `research/AGENTS.md`'s "snippets ≤10 lines" governs quoted source; the cited blocks are the documents' own declarations.
- [claude | `research/2026-08-22-nats-queue-groups-sniff.md` | S6 machine-specific citation root] APPLIED — root restated as the repository root. [claude | — | S6 vp1 placement] DEFERRED — moving `2026-08-22-effect-nats-substrate-vp1.md` beside its brief is churn for no reader gain while the README row resolves it; revisit when the verification directory is next touched.
- [claude | — | S smells] DEFERRED to the post-ratification proof pass: factor the three `SubInv` rebuilds onto `SubInv.of_stream_lookup`; replace `simp [applyPublish]` in `SubReachable.lean:75,86` by `publish_assigns` (now a package rule); namespace the trace helpers (`roomy`, `opts`, `msg`, `pub`, `reg`, `pullE`, `create`) and give `pullE` a `counts` parameter; one `applyRegister_enabled` lemma for the duplicated `hid`/`hcap` derivations. REJECTED — a generic association list over both `lookupStream` and `lookupSub`: the core side is frozen (the review's own override).
- [claude | slice doc §4.2, §9.1, §9.2, §11, §12, §13; snapshot | Spec: `replayBound` and the five `SubInv` clauses landed in code before the document] APPLIED — recorded after the fact (the spec-first order was violated in `dad5773`; acknowledged in the plan row and the package contract).
- [claude | slice doc §4.1, §9.2 | Spec: `endOne` ends only registered subscribers] APPLIED — document wording corrected; the code and §2.3 (`Set` members, `:133`) were right.
- [claude | snapshot revision log | Spec: `register_observed` / `selectReplay_lastPerSubject` statement drift] APPLIED — old/new recorded with the missing assumption for each (`SubShape`; `hstrict`).
- [claude | snapshot | Spec: `lagged_carries_last_observed` dead disjunct] APPLIED — dropped; reason logged.
- [claude | slice doc §6 | Spec: SA-starts prose] APPLIED — prose now matches the trace (`afterSequence 4` at head 4 → `[caughtUp]`; `afterSequence 2` → `[k2, k3, caughtUp]`; `afterSequence 0` → four entries).
- [claude | snapshot | Spec: "(frozen with r3)"] APPLIED — "(freeze candidates)".
- [claude | slice doc §12 | Spec: module split vs the Pass A DAG] APPLIED — DAG rewritten as implemented, with the reason for the split.
- [claude | snapshot | Spec: `w1_passes_replay`/`w2_passes_drain` unrequested] no change — kept as the deliberately-wrong-model discrimination probes; now named in §12/§13.
- [claude | — | Spec: SA5–SA7, `apply … = none` witnesses, T1–T7 instances, schema 2] DEFERRED — statements now in the snapshot (`all_sub_negatives`, `sub_core_inv`, SA4d, SA5h); proofs after ratification; schema 2 is SA9.
- [claude | — | LR-01] no change — the declared F5 boundary; no document claims a verified seam. [LR-02] = F6 APPLIED. [LR-03] = F3 APPLIED. [LR-04] APPLIED as SA5h. [LR-05, LR-07, LR-08] no change — scope statements, agreed. [LR-06] = SA9, pending. [referee §1.3] = F8 APPLIED.
- done — applied 20, rejected 2, deferred 4, no change 7.
