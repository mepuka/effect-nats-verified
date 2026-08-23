# Stage A proof map — architecture, proof plot, and the cleanup worklist (r3.1)

- **Date:** 2026-08-22 (late night)
- **Pin:** Foldable `cdb4709` (every r3.1 statement proved); stage-A modules transliterate
  `mepuka/effect-nats` @ `872bd7f`; the sequential core stays at `d06223f`.
- **Spec:** `research/2026-08-22-subscriber-stage-a.md` (§4 operations, §9.2 obligations, §11
  representation, §12 DAG); statements frozen in `docs/signature-snapshot.md`, "Stage A (r3.1)".
- **Purpose:** what the stage-A proofs are, how they fit, and the cleanup a maintenance lane may do
  without touching a frozen statement. Written for the lane that does the cleanup and for
  reviewers of `cdb4709`.
- **Citation root:** this package directory; `:line` anchors were opened at `cdb4709`.
- **Revision:** 2026-08-23 — §5b (cleanup worklist 2) added and §7 repointed at the lanes plan;
  §5b anchors were opened at `c11f652` (no package code changed between the two pins other
  than the merged cleanup lane, which §5 records).

## 1. The model in one page

| Module | Defines | Role |
|---|---|---|
| `Subscriber.lean` | `SubId`, `Policy`, `StartPosition`, `ConsumeOptions`, `SubError`, `QueueStatus`, `Observed`, `Subscriber`, `SubState`, `initialSub`, `lookupSub`, `updateSub`, `subscriberCount` | carriers (plain data, `DecidableEq`, so traces check by `decide`) |
| `SelectReplay.lean` | `isLastOfSubject`, `selectReplay`, `replayObserved` | the registration snapshot, five start positions |
| `Next.lean` | `Label`, `deliverOne`, `endOne`, `pullStep`, `newSubscriber`, `replayBound`, the `applyWith` skeleton (`afterOp`, `applyOp`, `applyRegister`, `applyPull`, `applyUnsubscribe`), `apply`, `Next`, `ReachableSub` | the labelled transition system; `apply s l = none` is "disabled" |
| `SubTraces.lean` | `SubTraceStep`, `SubTrace`, `runSubTraceWith`, W1 `pullStepW1`, W2 `deliverOneW2`, eight traces, helpers | kernel witnesses; wrong models through the same runner |
| `SubInvariants.lean` | `entrySequences`, `visible`, `SubInv` (eleven clauses), `StateInv`, `SubShape` | the invariants as predicates |
| `SubCore.lean` | lookups through `updateStream`/`removeStream`/`insertStream` (incl. `lookupStream_removeStream_self`); `applyPublish_nextSequence`, `publishStep_ok_eq`, `deleteStep_ok_eq`, `createStep_lookup_preserved`, `createStep_ok_shape`, `getStep_ok_eq`, `lastMsgStep_ok_eq`, `step_lookup_preserved`; `entrySequences_*` list helpers and the `visible` equations (`entrySequences_visible_admit`, `visible_admit`, `visible_drain`, `visible_drain_done`); `pairwise_*`; `SubInv.of_stream_lookup` | facts about the first-slice core and the `visible` equations the subscriber layer consumes |
| `SubProofs.lean` | `*_core` frame lemmas, `applyOp_ok_eq`, SA1 `reachableSub_core`; `selectReplay_sublist/_mem/_pairwise`; `SubInv.core_eq`, `SubInv.of_lookups` (both instances of `of_stream_lookup`); the three faces `deliverOne_admit`/`_overflow`/`_skip` and `endOne_skip`; per-label preservation `newSubscriber_inv`, `pullStep_inv`, `unsubscribe_inv`, `deliverOne_inv` (through the faces), `endOne_inv` | one preservation lemma per transition function |
| `SubReachable.lean` | `mem_of_lookupSub`, `mem_updateSub_eq` (strong form; `mem_updateSub` derived), `applyRegister_enabled`; `afterOp_inv`, `applyOp_inv`, `applyRegister_inv`, `applyPull_inv`, `applyUnsubscribe_inv`, `apply_inv`; SA2 `stateInv_reachable`, SA3 `pending_le_capacity`; **`reachableSub_all`**; `lookupSub_*` (update/fresh/append/map/of_mem_pairwise), `updateSub_keys`, `keys_map_snd`, `shape_of_keys`, `apply_shape`, `subShape_reachable` | the only `ReachableSub` induction and the principle everything else uses |
| `SubStatements.lean` | `sub_core_inv`; `publishedMessage`; `afterOp_publish_sub`, `publish_sub`; SA4a/c/d; SA5; SA6; `LagInv`, `LagState`, `lagInv_*`, `lagState_afterOp`, `apply_lag`, `lagState_reachable`; SA7 (`lagged_iff_of_open`, the explicit-premise form, with `lagged_iff` as its corollary); `applyAll`, `Negative`, `subNegatives`, `all_sub_negatives` | the frozen statements beyond SA1–SA3 |
| `SubHistory.lean` | `RegInfo`, `SubStateH`, `initialSubH`, `erase`, `lookupReg`, `labelMessage`, `committedAfter`, `regsAfter`, `applyH`, `NextH`, `ReachableSubH`, `liveKeep`, `liveOf`, `liveEntries`; AV1/AV2; `lookupReg_*`, `liveOf_*` (`liveOf_admit`); `HistInv`, `histInv_*`, `histInv_reachable`; SA5h `visible_global`, `entries_committed` | the proof-only ledger (history variable) |

Dependency order: `Subscriber → SelectReplay → Next → SubTraces → SubInvariants → SubCore →
SubProofs → SubReachable → SubStatements → SubHistory`; all imported by the root
`EffectNatsSubstrate.lean` (an unimported module is invisible to the gate).

## 2. The proof plot

The whole stage is one pattern applied four times: **state a predicate on one subscriber, prove
it preserved by each transition function (`deliverOne`, `endOne`, `pullStep`, the unsubscribe
update, `newSubscriber`), dispatch once over the four labels, and induct once over
`ReachableSub`.** Everything public is then a projection of a predicate on reachable states or a
direct computation on one `apply` step.

### 2.1 Frame (SA1)

`apply_core : apply s l = some s' → Reachable s.core → Reachable s'.core` by cases on the label;
`op` labels step the core with the first slice's `step`, the other three leave it unchanged.
`reachableSub_core` is the induction; `sub_core_inv` is `reachable_inv ∘ reachableSub_core`
(T1–T7 transported).

### 2.2 The representation invariant (SA2, SA3)

`SubInv s sub` has eleven clauses (§3). `afterOp_inv` handles a successful operation: for a
publish it obtains the stored stream, the exact core update, and the returned sequence from
`publishStep_ok_eq`, then maps `deliverOne_inv` over every subscriber; for a deletion it maps
`endOne_inv`; the other three operations keep every subscriber through lookup preservation
(`SubInv.of_lookups`). `applyRegister_inv` uses `newSubscriber_inv` with `replayBound` and
`reachable_sequences_strict`; `applyPull_inv`/`applyUnsubscribe_inv` go through
`mem_updateSub`. `apply_inv` dispatches; `stateInv_reachable` is the induction;
`pending_le_capacity` projects `capacity`.

### 2.3 The induction principle and the state shape

`reachableSub_all {P} (hinit) (hstep : ∀ {s s' l}, ReachableSub s → StateInv s → P s →
apply s l = some s' → P s') : ReachableSub s → P s` — the step case may assume the pre-state
satisfies `StateInv`, which is what every later invariant needs. Package rule: no other
`induction h` over `ReachableSub`; state a predicate and use this.

`SubShape s := (s.subs.map Prod.fst).Pairwise (· < ·) ∧ ∀ p ∈ s.subs, p.1 < s.nextId`.
`apply_shape` (via `shape_of_keys`: the key list is unchanged by a value map
`keys_map_snd` or by `updateSub_keys`, and `register` appends exactly `nextId`);
`subShape_reachable := reachableSub_all …`. It is what makes `lookupSub` after a registration
well-defined (`lookupSub_append_fresh`) and `lookupSub_of_mem_pairwise` (membership determines
the lookup) — used by SA4a and by `visible_global`.

### 2.4 Registration (SA4)

`register_observed`: `applyRegister_enabled` gives `id = nextId` and positive capacity; after
the `replayBound` branch the new pair is `(id, newSubscriber …)` appended, and
`lookupSub_append_fresh` needs every old id `≠ nextId` — from `SubShape`.
`selectReplay_lastPerSubject`: `isLastOfSubject` compares by `sequence`, so
`eq_of_sequence_eq_of_pairwise` (equal sequences in a strictly increasing list are the same
message) turns `lastForSubject … = some l` with `l.sequence = m.sequence` into `l = m`.
`memory_lastEnqueued_admissible`: `replayBound st.messages opts (nextSequence - 1) nextSequence`
from `reachable_sequences_strict` (every stored sequence `< nextSequence`) and
`reachable_positive` (`0 < nextSequence`).

### 2.5 The consumer-visible sequence, per transition (SA5)

`applyOp_ok_eq` exposes a successful operation as `step s.core o = .ok (core', r)` and
`s' = afterOp deliverOne s core' o r`; `afterOp_publish_sub`/`publish_sub` then identify the
subscriber after a publish as `deliverOne stream (publishedMessage …) sub` through
`lookupSub_map`. `deliverOne` has three faces, each a rewrite lemma with its exact conditions:
`deliverOne_admit` (matching, registered, room, open → append to `pending`, advance
`lastEnqueued`), `deliverOne_overflow` (matching, registered, full → de-register, `closing`
or `done` with the pre-overflow `lastEnqueued`), `deliverOne_skip` (condition false →
unchanged). `publish_visible` is a case split on room versus full; `op_visible_frame` is
`deliverOne_skip` for a non-matching publish and the catch-all `afterOp` arm otherwise;
`pull_visible` is `pullStep` on an open subscriber (drain moves `pending` into `observed`,
`visible` is the concatenation so it is unchanged); `visible_sequences_strict` projects
`visibleStrict`.

### 2.6 Deletion and re-creation (SA6)

`delete_ends`: `endOne` on a registered subscriber of the stream; the status is the
`isEmpty` conditional, handled by `split` after `dsimp only` reduces the record projection.
`create_restarts`: `createStep` on an absent stream inserts
`{ config, messages := [], nextSequence := 1 }`; `validate_ok_sound` gives
`config.name = raw.name`, `lookup_insert` reads it back.

### 2.7 The lag error (SA7)

`lagged_iff` needs `ReachableSub s`: without it a registered subscriber already in
`closing (consumerLagged …)` (unreachable by `registeredOpen`) satisfies the left side with a
non-full buffer, and an over-full buffer (unreachable by `capacity`) overflows with
`pending.length ≠ n`. With the invariant the split is `n ≤ pending.length`
(`deliverOne_overflow`) against room (`deliverOne_admit`, status stays `opened`).

`lagged_carries_last_observed` is a reachable-state fact that `SubInv` does not carry, so it
goes through a separate predicate rather than widening the frozen `SubInv`:

```text
LagInv sub :  closingLag  status = closing (consumerLagged _ n) → n = lastEnqueued
              doneLag     status = done (consumerLagged _ n)    → (entrySequences observed).getLast? = some n
              failedLag   observed.getLast? = some (failed (consumerLagged _ n)) → same conclusion
```

The chain a lag follows: overflow sets `closing (consumerLagged stream lastEnqueued)` with
`pending ≠ []` (capacity ≥ 1 rules out `done` here — `capacityPos`); the drain pull moves
`pending` to `observed`, whose last entry sequence is `lastEnqueued` (`pendingLast`), and sets
`done`; the next pull appends `failed e` (`entrySequences` ignores it). Preservation per
transition function is `lagInv_newSubscriber`, `lagInv_deliverOne` (uses `SubInv` for
`registeredOpen` and `capacityPos`), `lagInv_endOne`, `lagInv_pullStep` (uses
`closingNonempty`, `pendingLast`), `lagInv_unsubscribe`; `lagState_afterOp`/`apply_lag`
dispatch; `lagState_reachable := reachableSub_all …`.

### 2.8 Negative witnesses

`applyAll` folds labels; each `Negative` is a prefix, a label, and whether the label is
`disabled` (`apply = none`) or `unchanged` (`apply = some s`); ten cases, `all_sub_negatives`
by `decide`. The states are concrete (`kvConfigRaw`, one subject), so the kernel evaluates them.

### 2.9 The ledger (SA5h)

`SubStateH := { base, committed : List (StreamName × StoredMessage), regs : List (SubId × RegInfo) }`
with `RegInfo := { index : Nat, initial : List Observed }` (`at`/`prefix` are keywords).
`applyH` is `apply` on `base`; a successful publish appends `(stream, publishedMessage …)` to
`committed` (`labelMessage`, `committedAfter`); a successful registration appends
`(id, { index := committed.length, initial := replayObserved st.messages opts })`
(`regsAfter`, which re-reads `lookupStream` — the same `st` `applyRegister` used).

- AV1 `applyH_erase`: cases on `apply sH.base l`, both arms `rfl`.
- AV2 `applyH_lift`: the successor is the literal `{ base := s', committed := …, regs := … }`;
  `reachableSub_lift` is `reachableSub_all` with `P s := ∃ sH, ReachableSubH sH ∧ erase sH = s`.
- `reachableSubH_erase` (the other direction, an induction over `ReachableSubH`) supplies
  `StateInv` of the base to the ledger preservation proofs.
- `HistInv sH`: `coreCommitted` (every stored message is in the ledger), `regsBelow` (ledger ids
  `< nextId`, so a fresh registration's id is not in `regs`), and per subscriber a record `r`
  with `lookupReg regs id = some r`, `r.index ≤ committed.length` (so `List.drop` through an
  append behaves — `liveOf_append_of_pos/neg`), the global equation while registered
  (`visible = r.initial ++ (liveOf committed sub r).map entry`), and provenance
  (`entry m ∈ visible → (sub.stream, m) ∈ committed`).
- Preservation: `histInv_publish` (the new message is in the ledger; a subscriber's live list
  grows by exactly the message iff the skip condition is false — `liveKeep` — using the three
  faces and `liveOf_admit`; storage membership after `applyPublish` through
  `pruneSubject_sublist`/`publishBase_sublist`), `histInv_delete`
  (`lookupStream_removeStream_self/_other`; `endOne` either de-registers or is the identity),
  `histInv_create` (`createStep_ok_shape`), `histInv_get`/`histInv_last` (state unchanged),
  `histInv_register` (the new record is fresh by `regsBelow`; `liveOf_at_length` makes the live
  list empty; the prefix's entries are stored hence committed), `histInv_pull`
  (`mem_updateSub_eq` keeps `p.1 = id`; a `done` pull keeps `pending`, so entries are traced
  through both halves), `histInv_unsubscribe`; `histInv_step` cases the label;
  `histInv_reachable` inducts over `ReachableSubH`.
- `visible_global`: the record from `HistInv`, and `lookupSub_of_mem_pairwise` (from
  `SubShape` of the erased state) to unfold `liveEntries`; `entries_committed` projects.
- Why an index and not a sequence head: a deleted and re-created stream restarts at 1, so
  "sequence > head at registration" would admit the old incarnation's messages.

## 3. The invariant clauses and why each exists

`SubInv s sub` (`SubInvariants.lean`): `capacityPos` (overflow with an empty buffer is
impossible, SA7), `capacity` (SA3), `registeredOpen` (kills `deliverOne`'s dead third branch
and makes `closing`/`done` subscribers unregistered), `registeredStream` (the stream exists
and `lastEnqueued < head` — a newly stored message is larger than everything visible),
`closingNonempty` (Q2: a failure after a non-empty buffer drains first), `doneEmpty`,
`shutDownClear`, `pendingMatch` (T9), `visibleStrict` (T11), `visibleBound` (every visible
sequence `≤ lastEnqueued`), `pendingLast` (the last buffered sequence is `lastEnqueued`, what
the lag error carries). `SubShape`, `LagInv`, `HistInv`: §2.3, §2.7, §2.9. `SubInv` is
frozen (named in the snapshot); the other three are proof-side predicates and may be
reshaped if their consumers still prove the frozen statements.

## 4. Conventions and gotchas (core Lean, v4.33; learned while proving)

- Nested `if`s: after `unfold`, `rw [if_pos h]` / `rw [if_neg h]` with an explicit hypothesis
  beats `split`; `split` on a `match sub.policy with` single-constructor match is fine.
- `cases hx : e with` *replaces* `e` in the goal (so a later witness is `rfl`, not the
  equation); `rw [hx] at h` followed by `simp only at h` reduces a `match` on a constructor
  — but a pair discriminant must be destructured first (`obtain ⟨a, b⟩ := p`).
- `split at h` on a `match` whose discriminant is a variable *cases the variable*; on a
  concrete discriminant it may still emit impossible arms — close them with
  `first | cases h | contradiction | (rename_i hc; cases hc)`.
- `rw`'s closing `rfl` runs at reducible transparency: `List.map f [a]` and `Option.map f
  (some a)` do not reduce there (add `rfl` or `show`), while projections of constructors do
  (then an explicit `rfl` errors with "no goals").
- Structure-instance continuation lines must start at a column ≥ the first field's column;
  a lower column parses as "expected '}'". Prefer one-line literals or the `{ x with`-newline
  form with aligned fields. `at`, `prefix`, `infix` are keywords.
- `nomatch h, …` swallows the following comma-separated terms — parenthesise inside `⟨…⟩`.
- `omega` does not see through `abbrev SubId := Nat` atoms: `Nat.lt_succ_of_lt`,
  `Nat.lt_succ_self`, `Nat.ne_of_lt`. `List.mem_of_mem_filter` is not core: use
  `(List.mem_filter.mp h).1` or `mem_forSubject`.
- `simp only at h` can turn `some a = some b` into `a = b` (then `cases h` still substitutes);
  `simp at h` with `h : none = some _` closes the goal — do not follow it with another tactic.
- Reducing record projections before a rewrite: `dsimp only` (or `show`), otherwise a pattern
  like `liveOf (sH.committed ++ …)` does not find `liveOf ({…} : SubStateH).committed …`.
- Unused-hypothesis and unused-simp-argument linters count as warnings under the gate
  (`lake build` must print none): bind unused frozen hypotheses as `_h`; keep simp sets tight.

## 5. Cleanup worklist (deferred from the 2026-08-22 review round)

**Status 2026-08-22 (late night):** items 1–7 and the `lagged_iff_of_open` helper (GitHub issue #1)
were done by the cleanup lane and merged (branch `proofCompleteCleanup`, ten commits); the
signature probe confirmed identical elaborated types for every frozen declaration. Item 8 is
still open; the module table in §1 reflects the moves.

Constraints for all items: no frozen statement changes (names and elaborated types in the
snapshot's "Stage A (r3.1)" section — including `SubInv`'s clauses and the module a frozen
theorem is stated in: SA1 in `SubProofs`, SA2/SA3 in `SubReachable`, SA4–SA7 and
`all_sub_negatives` in `SubStatements`, SA5h in `SubHistory`); helper lemmas may move,
merge, or be renamed; `Next.lean` definitions are frozen (do not rewrite `afterOp`'s `let` to
`publishedMessage` even though it is definitionally equal); every change re-runs the gate (§6);
`README.md` "Layout" and the slice document §12 DAG name module contents — update both when a
lemma moves. Commit per item or per coherent group; nothing else in the same commit.

1. **Three copies of the eleven-field `SubInv` rebuild.** `SubInv.core_eq` and
   `SubInv.of_lookups` (`SubProofs.lean:264-285`) restate what `SubInv.of_stream_lookup`
   (`SubCore.lean:189-199`) already proves. Replace both bodies by an application of
   `of_stream_lookup`: for `core_eq`, `hinv.of_stream_lookup (fun _ st₀ hl => ⟨st₀, by rw [← h];
   exact hl, Nat.le_refl _⟩)`; for `of_lookups`, `hinv.of_stream_lookup (fun _ st₀ hl =>
   hcore _ _ hl)`. Keep their names — `SubReachable` and `SubProofs` call them.
2. **Pipeline unfolding outside `Views.lean`.** `SubReachable.lean:75` and `:86` prove
   `st.nextSequence ≤/< (applyPublish …).1.nextSequence` by `simp [applyPublish]`. Add
   `theorem applyPublish_nextSequence … : (applyPublish st subject payload headers rollup
   now).1.nextSequence = st.nextSequence + 1 := rfl` in `SubCore.lean` (step-shape section)
   and use `rw [applyPublish_nextSequence]; exact Nat.le_succ _` / `exact Nat.lt_succ_self _`.
   Package rule: a stage-A proof that unfolds `applyPublish` is missing a core fact.
3. **Duplicated `register` guard derivations.** `applyRegister_inv` (`SubReachable.lean:152-155`)
   re-derives `opts.buffer.capacity ≠ 0` from the guard; `applyRegister_enabled` (same file,
   later) proves both guard facts. Move `applyRegister_enabled` (and its section header) above
   `applyRegister_inv`, then in `applyRegister_inv` take
   `have hcap := (applyRegister_enabled h).2` before `unfold applyRegister at h` and delete the
   inner `have hcap … simp [hz]`.
4. **Trace helpers in the package namespace.** `roomy`, `opts`, `msg`, `pub`, `create`, `reg`,
   `pullE` (`SubTraces.lean:122-143`) are top-level in `EffectNatsSubstrate`, and `opts` is also a
   binder name in most theorems. Wrap them in `namespace SATrace … end SATrace` and `open SATrace`
   for the remainder of the file; give `pullE` a `(counts : List (StreamName × Nat) := [])`
   parameter like `reg` and replace the `|> fun t => { t with counts := … }` at `:311-312`.
   The traces are `decide`-checked: a changed helper is re-evaluated, nothing else moves.
5. **Two membership lemmas for `updateSub`.** `mem_updateSub` (`SubReachable.lean`) is the weak
   form; `mem_updateSub_eq` (`SubHistory.lean`) also yields `p.1 = id`. Keep the strong one in
   `SubReachable` next to `mem_of_lookupSub`, derive the weak one from it (or replace its three
   call sites), and remove the copy from `SubHistory`.
6. **Core step shapes stranded in `SubHistory`.** `lookupStream_removeStream_self`,
   `createStep_ok_shape`, `getStep_ok_eq`, `lastMsgStep_ok_eq` belong with the step shapes in
   `SubCore.lean` (§12 DAG); move them and update the DAG/README lines.
7. **`visible` lemma surface split across files.** `entrySequences_visible_admit`
   (`SubProofs`), `visible_admit`, `visible_drain`, `visible_drain_done`, `liveKeep_admit`,
   `liveOf_admit` (`SubHistory`) are the equations every later proof uses. Gather the
   `visible`/`entrySequences` ones in `SubCore.lean`'s list-helper section (the `liveOf` ones stay
   in `SubHistory`), and consider rewriting `deliverOne_inv`/`lagInv_deliverOne` with the three
   faces (`deliverOne_admit/_overflow/_skip`, currently in `SubStatements`, which would then move
   to `SubProofs` before `deliverOne_inv`) instead of re-unfolding `deliverOne` — optional; only
   if the proofs get shorter, not just different.
8. **`pullStep_inv` repeats one constructor block three times** (`SubProofs.lean`, the
   `opened`/`closing`/`done` arms). A small `SubInv.pulled` lemma for "observed grew by entries
   of the buffer, buffer emptied" would serve all three; optional.
9. **Exporter coverage (not cleanup — slice work).** `SubTraceStep` has no `replay` flag and
   `Main.lean` still prints schema 1 (`allTraces` only). Schema 2 (slice §14) is the next slice
   task, with the codex harness brief; do not start it inside a cleanup commit.

Not to do: change `SubInv` (frozen); add `SubShape`/`LagInv` clauses into `SubInv`; rename
any frozen theorem; "simplify" `lagged_iff` by dropping `hreach` (the bare statement is false;
the amendment is logged in the snapshot and awaits the owner's approval); reformat files
wholesale (diffs must stay reviewable).

## 5b. Cleanup worklist 2 (2026-08-23; for the cleanup lane)

**Status:** open. Written for the lane that did items 1–7: same constraints as §5 (no frozen
statement changes — names, elaborated types, `SubInv`'s clauses, and the module a frozen theorem
is stated in; `Next.lean` definitions frozen; helper lemmas may move, merge, or be renamed; the
gate of §6 after every change; `README.md` "Layout", §1 of this document, and the slice
document §12 DAG updated in the same commit as any move; one commit per item, nothing else in
it). Work in a fresh worktree on a branch named for the lane; the merge gate is §6 plus the
signature probe (`pp.all` on every frozen declaration before and after; identical output).
Every `file:line` below was opened at Foldable `c11f652`; re-open before editing — lines move.

Ordered by value over risk: deletions and one-line substitutions first, eliminators next,
optional rewrites last. Items 17–18 are gate hardening, not proof work.

1. **Four dead lemmas.** Declared and referenced nowhere else in `EffectNatsSubstrate/` or
   `Main.lean`: `mem_entrySequences` (`SubCore.lean:209-222`), `lookupSub_nextId`
   (`SubReachable.lean:431-434`; also named in §1's `SubReachable` row — delete the mention),
   `liveKeep_admit` (`SubHistory.lean:300-302`; named in §1's `SubHistory` row and in §5 item 7 —
   keep it if you prefer a `rfl` witness for why `liveOf_admit` is trivial, else delete and fix
   the mention), `keepLatest_zero` (`Views.lean:120-122`; `keepLatest` is a frozen carrier, the
   lemma is not). No proof changes.
2. **`pairwise_lt_append_singleton` (`SubCore.lean:245-252`) is `pairwise_append_singleton`
   (`Views.lean:58-65`) at `Nat`/`(· < ·)`.** Delete it; add `import EffectNatsSubstrate.Views`
   to `SubCore.lean` (cycle-free: `SubCore` already imports `Invariants`, which sits below
   `Views`); replace the two call sites `SubProofs.lean:376` (`deliverOne_inv`) and
   `SubReachable.lean:391` (`apply_shape`) — same argument order. The import also serves items 3
   and 12.
3. **The last two `simp only [applyPublish]` outside `Views.lean`.** `Proofs.lean:501-507`
   (`reachable_positive`) and `SubHistory.lean:326-334` (`histInv_publish`, `coreCommitted` arm)
   unfold the pipeline to prove "a stored message after a commit was stored before or is the new
   one". Add, in `Proofs.lean` after `publishBase_sublist` (`:68-73`):
   `theorem mem_applyPublish {st subject payload headers rollup now m}
   (h : m ∈ (applyPublish st subject payload headers rollup now).1.messages) :
   m ∈ st.messages ∨ m = newMessage st subject payload headers now` and use it at both sites.
   Bodies only; `reachable_positive` is frozen (r2) in statement.
4. **§5 item 8 — `pullStep_inv` (`SubProofs.lean:167-237`).** The `done` (`:172-192`),
   `opened` (`:193-213`), and `closing` (`:214-236`) arms each rebuild the eleven-field `SubInv`
   with `constructor` + eleven bullets (`:181-192`, `:202-213`, `:225-236`); bullets 1, 9, 10 are
   byte-identical across all three, bullets 2, 3, 4, 5, 8, 11 between `opened` and `closing`;
   the `hvis` equation is restated three times (`:177-180`, `:198-201`, `:221-224`). Add beside
   `SubInv.of_stream_lookup` (`SubCore.lean:262-272`):
   `theorem SubInv.pulled {s sub} (hinv : SubInv s sub) {obs' st' reg'}
   (hvis : entrySequences (visible { sub with observed := obs', pending := [], status := st',
   registered := reg' }) = entrySequences (visible sub)) (hopen : reg' = true → st' = .opened)
   (hclosing : ∀ e, st' ≠ .closing e) (hshut : st' = .shutDown → reg' = false)
   (hstream : reg' = true → ∃ st₀, lookupStream s.core sub.stream = some st₀ ∧
   sub.lastEnqueued < st₀.nextSequence) : SubInv s { sub with … }` — every clause discharges
   uniformly (`capacity := Nat.zero_le _`, `pendingMatch := fun _ hm => nomatch hm`,
   `pendingLast := fun h => absurd rfl h`, `visibleStrict`/`visibleBound` through `hvis`). The
   three arms then supply `hvis` and the side conditions (≈ 8 lines each), and
   `unsubscribe_inv` (`SubProofs.lean:238-260`) is the fourth instance with `reg' := false`.
   Callers `applyPull_inv` (`SubReachable.lean:205`) and `applyUnsubscribe_inv` (`:222`) are
   unchanged. Take item 10 first so `hvis` is `congrArg entrySequences (visible_drain …)`.
5. **`deliverOne_overflow_closing`.** The derivation "capacity positive ⇒ full buffer non-empty
   ⇒ status is `closing`, not `done`" is written at `SubProofs.lean:334-343` (`deliverOne_inv`,
   with a 4-line `cases` for `hempty`) and `SubStatements.lean:332-337` (`lagInv_deliverOne`,
   one line via `List.isEmpty_eq_false_iff.mpr`), then consumed by two 6-line `have h' … rw
   [hempty, if_neg …] at h'; cases h'` blocks at `SubStatements.lean:340-351`. Add after
   `deliverOne_overflow` (`SubProofs.lean:288-300`):
   `theorem deliverOne_overflow_closing {s stream m sub n} (hinv : SubInv s sub)
   (hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters m.subject) = true)
   (hpol : sub.policy = .terminateOnLag n) (hfull : n ≤ sub.pending.length) :
   deliverOne stream m sub = { sub with registered := false, status := .closing
   (.consumerLagged stream sub.lastEnqueued) } ∧ sub.pending ≠ []`. `deliverOne_overflow` stays
   (used by `publish_visible`, `lagged_iff_of_open`, `histInv_publish`).
6. **`endOne_end`, the positive face `endOne_skip` (`SubProofs.lean:308-312`) lacks.** The
   `if sub.pending.isEmpty then .done … else .closing …` term is restated by hand at
   `SubProofs.lean:409-410`, `:415-416`, `:421-422` (`endOne_inv`), `SubStatements.lean:373-374`,
   `:377-378` (`lagInv_endOne`), and `unfold endOne; rw [if_pos hc]` at
   `SubHistory.lean:276-278`, `:287-289`, `:290-292` (`histInv_delete`) and
   `SubStatements.lean:259-266` (`delete_ends`, frozen statement, body only). Add next to
   `endOne_skip`: `theorem endOne_end {name sub} (hcond : (sub.stream == name && sub.registered)
   = true) : endOne name sub = { sub with registered := false, status := if sub.pending.isEmpty
   then .done (.streamNotFound name) else .closing (.streamNotFound name) }`.
7. **`pullStep_ok_eq` — five sites re-split `pullStep`'s four arms.** `SubProofs.lean:169-236`,
   `SubStatements.lean:168-174` (`pull_visible`, frozen statement, body only),
   `SubStatements.lean:386-449` (`lagInv_pullStep`), and `SubHistory.lean:542-564` **and**
   `:566-589` (the same 23-line ladder twice inside `histInv_pull`). Add before `pullStep_inv`:
   `theorem pullStep_ok_eq {sub sub'} (h : pullStep sub = some sub') :
   (∃ e, sub.status = .done e ∧ sub' = { sub with observed := sub.observed ++ [.failed e],
   status := .shutDown }) ∨ (sub.status = .opened ∧ sub.pending ≠ [] ∧ sub' = { sub with
   observed := sub.observed ++ sub.pending.map Observed.entry, pending := [] }) ∨ (∃ e,
   sub.status = .closing e ∧ sub.pending ≠ [] ∧ sub' = { sub with observed := sub.observed ++
   sub.pending.map Observed.entry, pending := [], status := .done e })`. `pullStep`
   (`Next.lean:75-87`) is frozen and read only.
8. **`apply*_ok_eq` — the widest repeat; four commits, one per eliminator.** `unfold applyX at
   h; split at h; …` ladders: `applyPull` at `SubProofs.lean:62-67`, `SubReachable.lean:192-205`,
   `:409-415`, `SubStatements.lean:158-167`, `:510-523` (line-for-line the `SubReachable:192-205`
   copy), `SubHistory.lean:524-531`; `applyUnsubscribe` at `SubProofs.lean:71-76`,
   `SubReachable.lean:209-222`, `:418-424`, `SubStatements.lean:526-539`,
   `SubHistory.lean:596-606`; `applyRegister` at `SubProofs.lean:48-58`,
   `SubReachable.lean:66-78`, `:169-188`, `:378-406`, `SubStatements.lean:79-96`, `:491-507`,
   `SubHistory.lean:447-517` (79 lines, arm-closer `all_goals first | cases h' | …` at `:461`);
   the `applyOp` error arm at `SubProofs.lean:37-42`, `SubReachable.lean:158-161`, `:370-373`,
   `SubStatements.lean:232-238`, `:484-487`, `SubHistory.lean:424-438`. Add in `SubProofs.lean`
   (the pull/register ones inside `section Frame`, generic in `deliver`/`pull`, so `pullStepW1`
   and `deliverOneW2` are served too):
   `applyPull_ok_eq {s s' id} (h : applyPull pull s id = some s') : ∃ sub sub', lookupSub s.subs
   id = some sub ∧ pull sub = some sub' ∧ s' = { s with subs := updateSub s.subs id (fun _ =>
   sub') }`;
   `applyUnsubscribe_ok_eq {s s' id} (h : applyUnsubscribe s id = some s') : ∃ sub, lookupSub
   s.subs id = some sub ∧ sub.status ≠ .shutDown ∧ s' = { s with subs := updateSub s.subs id
   (fun sub => { sub with registered := false, pending := [], status := .shutDown }) }`;
   `applyRegister_ok_eq {s s' stream opts l₀ id e} (h : applyRegister s stream opts l₀ id e =
   some s') : (lookupStream s.core stream = none ∧ e = .error (.streamNotFound stream) ∧ s' = s)
   ∨ (∃ st, lookupStream s.core stream = some st ∧ e = .ok .unit ∧ replayBound st.messages
   opts l₀ st.nextSequence = true ∧ s' = { s with subs := s.subs ++ [(id, newSubscriber stream
   opts l₀ st.messages)], nextId := id + 1 })`;
   `applyOp_error_eq {s s' o err} (h : applyOp deliver s o (.error err) = some s') : s' = s ∧
   step s.core o = .error err`.
   Prerequisite move in the first of the four commits: `applyOp_ok_eq`
   (`SubStatements.lean:31-49`, not frozen, already consumed from `SubHistory.lean:417`) joins
   them in `SubProofs.lean`'s `Frame` section; §1 rows and the §12 DAG follow. Frozen statements
   whose bodies change: `register_observed`, `pull_visible`, `create_restarts`, `delete_ends`,
   `memory_lastEnqueued_admissible` — they stay in `SubStatements`. Expected net −150 to −200
   lines.
9. **An 8-line block twice inside `lagInv_pullStep`** (`SubStatements.lean:419-425` and
   `:443-449`, byte-identical from `exfalso` on). Add to `SubCore.lean`'s `visible` section:
   `theorem getLast?_visible_ne_failed {sub} (hne : sub.pending ≠ []) {e} : (sub.observed ++
   sub.pending.map Observed.entry).getLast? ≠ some (Observed.failed e)`; 16 lines → 2.
10. **`visible_drain`/`visible_drain_done` (`SubCore.lean:234-243`) re-proved by `simp
    [visible]`** at `SubProofs.lean:198-201` and `:221-224`; `unfold visible` at
    `SubProofs.lean:241` and `:257` (`unsubscribe_inv`); `entrySequences_append,
    entrySequences_failed, List.append_nil` recomputed at `SubStatements.lean:401`. Use
    `congrArg entrySequences (visible_drain sub)` / `(visible_drain_done sub e)`; add the
    missing sibling for the `done` arm (`SubProofs.lean:177-180`):
    `theorem entrySequences_visible_fail (sub) (e) : entrySequences (visible { sub with observed
    := sub.observed ++ [Observed.failed e], status := .shutDown }) = entrySequences (visible
    sub)` — the existing proof passes `hpend` to `simp`; check on compile whether the equation
    needs it (it should not). Same commit: move `entrySequences_visible_newSubscriber`
    (`SubProofs.lean:126-134`; consumers `:153`, `:156`) to `SubCore.lean`'s equations section —
    §5 item 7's rule applied to the sites item 7 did not reach.
11. **`apply_lag` (`SubStatements.lean:473-540`, 68 lines) is `apply_inv`
    (`SubReachable.lean:224-231`, 9 lines) inlined.** Arms `:476-488` (op), `:489-507`
    (register), `:508-523` (pull), `:524-539` (unsubscribe) mirror `applyOp_inv`,
    `applyRegister_inv`, `applyPull_inv`, `applyUnsubscribe_inv`. Introduce `lagState_applyOp`,
    `lagState_applyRegister`, `lagState_applyPull`, `lagState_applyUnsubscribe` next to
    `lagState_afterOp` (`:459-471`) so `apply_lag` becomes the same `cases l with` dispatch;
    with item 8 landed each is 4–6 lines. `lagged_carries_last_observed` (`:544-547`, frozen)
    unchanged. Add the four names to §1's `SubStatements` row.
12. **`create_restarts` (`SubStatements.lean:268-287`, frozen statement) re-unfolds
    `createStep`** (`:275`) and re-derives `validate_ok_sound` (`:279`) although
    `createStep_ok_shape` (`SubCore.lean:132-146`) returns exactly the needed disjunction
    (`histInv_create`, `SubHistory.lean:210`, already uses it). Body only:
    `rcases createStep_ok_shape hc with rfl | ⟨config, hval, hlook, rfl⟩`, then
    `(validate_ok_sound hval).1` and `lookup_insert`. ≈ 20 → 10 lines.
13. **`replayBound` unfolded two ways** — `SubProofs.lean:142` (`simp only [replayBound, …]`)
    and `SubStatements.lean:143-149` (`unfold replayBound; rw …`). Optional face in
    `SubCore.lean`: `theorem replayBound_eq_true_iff {messages opts l₀ nextSeq} : replayBound
    messages opts l₀ nextSeq = true ↔ (∀ m ∈ selectReplay messages opts, m.sequence ≤ l₀) ∧ l₀ <
    nextSeq`. Two sites, ≈ 8 lines: bundle with item 12 or drop.
14. **`histInv_get` (`SubHistory.lean:220-230`) and `histInv_last` (`:231-243`) are one proof**
    (only the step lemma and the `show`n label differ; both end in the identical
    `exact histInv_of_same hinv hinv.coreCommitted rfl rfl`). One `histInv_readonly`
    parameterised by `o : Op` with hypotheses `core' = sH.base.core` and `afterOp deliverOne
    sH.base core' o r = { sH.base with core := core' }`, the two kept as two-line corollaries.
    The hypothesis shape needs a compile check (`committedAfter`/`regsAfter` must still reduce for
    a variable `r`) — a needs-verification item, not a mechanical edit.
15. **`op_visible_frame` (`SubStatements.lean`, frozen statement) closes six arms with the same
    one-liner** (`:223`, `:224`, `:225`, `:227`, `:228`, `:230`: `simp only [afterOp] at ha; rw
    [hb] at ha; cases ha; rfl`). After the two special arms, `all_goals (…)`. Cosmetic; last.
16. **Sequential: `pairwise_of_sublist` (`Proofs.lean:29-41`, private) is
    `List.Pairwise.sublist` with swapped arguments**, which `SubProofs.lean:124` and
    `SubStatements.lean:130` already call directly. Delete it; rewrite `Proofs.lean:214` and
    `:234` (`applyPublish_inv`) as `List.Pairwise.sublist hbase h.1` / `List.Pairwise.sublist
    hsub happPair`. Statements unchanged.
17. **Gate as a committed script, and CI parity.** The package's
    `.github/workflows/lean_action_ci.yml` runs the exporter without `--foldable-commit`
    (`:18-19`; the documented gate runs it with, §6), has no forbidden-token sweep, no
    `#print axioms` probe, and uses `leanprover/lean-action@v1` unpinned (`:14`). The workflow is
    live in the standalone publication (`effect-nats-verified`, a subtree split whose root is this
    directory), not in the Foldable monorepo. Add `scripts/gate.sh` (build; the grep of §6; `lake
    env lean scripts/Axioms.lean` where that file `#print axioms` every name in §6's list and the
    r1–r2 frozen theorems; the exporter twice with `--foldable-commit $(git rev-parse HEAD)` and
    `cmp`; exit non-zero on any failure) and call it from the workflow; pin the action by
    commit SHA. `scripts/` is outside the library, so nothing changes under the kernel.
18. **Documentation that no longer matches the tree** (doc-only commit; verify each claim against
    the code before rewording): `README.md:110` says `SubReachable.lean` holds "the one induction
    over reachable states" — there are three over `ReachableSub` (`SubProofs.lean:91`
    `reachableSub_core`; `SubReachable.lean:234` `stateInv_reachable`; `:250` `reachableSub_all`)
    and two over `ReachableSubH` (`SubHistory.lean:107`, `:639`); the first two are the bootstrap
    of the third (`reachableSub_all`, `:246-252`, is built from `stateInv_reachable`, built from
    `reachableSub_core`), so restate the rule here (§2, `:62-63`) and in `README.md` as "no
    `induction` over `ReachableSub` other than the two bootstrap inductions and `reachableSub_all`;
    every later fact goes through `reachableSub_all`". `README.md:108` calls `SubCore.lean` "facts
    about the core" although it now owns the `visible`/`entrySequences` equations
    (`SubCore.lean:190-256`). §1's `SubProofs` row omits `entrySequences_visible_newSubscriber`
    and `registered_false_of_status` (`SubProofs.lean:161-166`); the `SubStatements` row omits
    `eq_of_sequence_eq_of_pairwise` (`SubStatements.lean:100-113`), `NegKind`, `negativeHolds`,
    `negOpts`/`negCreate`/`negPublish`/`negRegister`. The slice document §12 DAG (`research/…
    -subscriber-stage-a.md:443-476`) is stale in the `SubCore`, `SubProofs`, `SubReachable`,
    `SubHistory`, and `SubStatements` rows (names added by §5 items 2, 6, 7 and the proofs);
    correct it in the same commit under the Correct workflow (`research/AGENTS.md`).

**Not in this worklist (owner's call, recorded for the next snapshot revision):**
`docs/signature-snapshot.md:3-5` still reads "revision 2.1 … 31 frozen declarations … 76
non-private theorems" although r3.1 is ratified below it and the package holds 214 non-private
theorems; and its approved edit regions (`:379-381`) name `SubProofs`/`SubReachable`/
`SubStatements` but not `SubCore`/`SubHistory`, where §5 moved helper lemmas. Both are freeze
documents: they change with the next snapshot revision, not in a cleanup commit.

**Not to do (looks like cleanup, touches something frozen):** delete the eight `sa_*_trace`
singletons or the sequential `*_trace` ones even though `all_sub_traces`/`all_traces` subsume
them and double the kernel `decide` cost — frozen names, in the axiom-probe list; fold `LagInv`
into `SubInv`; drop `hreach` from `lagged_iff`; rewrite `afterOp`'s `let` (`Next.lean:108-110`)
to `publishedMessage`; move SA1 out of `SubProofs`, SA2/SA3 out of `SubReachable`, SA4–SA7 or
`all_sub_negatives` out of `SubStatements`, SA5h out of `SubHistory` (item 8 moves
`applyOp_ok_eq` only — it is not frozen); "simplify" `reachableSub_core` or `stateInv_reachable`
through `reachableSub_all` (a dependency cycle, not a style lapse); add any `set_option` (the
package has none; the gate greps for it); add `@[simp]` attributes (the package uses none —
`simp` sets stay explicit and tight for the linter); rename `SubInv.core_eq`/`of_lookups`
(eight call sites, no gain).

## 6. The gate and the freeze

From this directory, after every change:

```text
lake build                                   # clean: no errors, no warnings (linters included)
grep -rn "sorry\|native_decide\|axiom\|unsafe\|set_option" EffectNatsSubstrate/ Main.lean   # nothing
lake env lean <scratch with #print axioms on every r3.1 theorem>   # ⊆ {propext, Classical.choice, Quot.sound}
lake build effect_nats_traces && lake exe effect_nats_traces -- --foldable-commit <HEAD> twice; cmp
```

The r3.1 theorem list for the axiom probe: `reachableSub_core`, `stateInv_reachable`,
`pending_le_capacity`, `subShape_reachable`, `sub_core_inv`, `register_observed`,
`selectReplay_mem`, `selectReplay_lastPerSubject`, `memory_lastEnqueued_admissible`,
`pull_visible`, `publish_visible`, `op_visible_frame`, `visible_sequences_strict`,
`delete_ends`, `create_restarts`, `lagged_iff`, `lagged_carries_last_observed`,
`all_sub_traces`, `w1_fails_drain`, `w2_fails_lag`, `all_sub_negatives`, `erase_initialSubH`,
`applyH_erase`, `applyH_lift`, `reachableSub_lift`, `visible_global`, `entries_committed`.
Every module under `EffectNatsSubstrate/` must be imported by the root. A statement change
is not cleanup: it returns to the slice document and the snapshot with an old/new log entry
and owner approval.

## 7. After the cleanup

The order of work across both repositories, the lanes that run in parallel with this one, and
the file-ownership boundaries are in `research/2026-08-23-effect-nats-lanes-plan.md` (Foldable).
In short: exporter schema 2 with the stage-A traces and `pull` labels (slice §14, corrected) and
the codex harness brief (effect-nats `docs/architecture/lean-subscriber-trace-replay-brief.md`);
then the r3.1 assurance review (five axes, `docs/reviews/`); then stage B (`EffectQueue`, the
quiescence assumption A4 discharged as a weak forward simulation, T14′). This worklist merges
independently of all of them: the signature probe is the only coupling.
