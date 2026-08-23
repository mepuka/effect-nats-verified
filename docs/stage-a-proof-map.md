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

## 1. The model in one page

| Module | Defines | Role |
|---|---|---|
| `Subscriber.lean` | `SubId`, `Policy`, `StartPosition`, `ConsumeOptions`, `SubError`, `QueueStatus`, `Observed`, `Subscriber`, `SubState`, `initialSub`, `lookupSub`, `updateSub`, `subscriberCount` | carriers (plain data, `DecidableEq`, so traces check by `decide`) |
| `SelectReplay.lean` | `isLastOfSubject`, `selectReplay`, `replayObserved` | the registration snapshot, five start positions |
| `Next.lean` | `Label`, `deliverOne`, `endOne`, `pullStep`, `newSubscriber`, `replayBound`, the `applyWith` skeleton (`afterOp`, `applyOp`, `applyRegister`, `applyPull`, `applyUnsubscribe`), `apply`, `Next`, `ReachableSub` | the labelled transition system; `apply s l = none` is "disabled" |
| `SubTraces.lean` | `SubTraceStep`, `SubTrace`, `runSubTraceWith`, W1 `pullStepW1`, W2 `deliverOneW2`, eight traces, helpers | kernel witnesses; wrong models through the same runner |
| `SubInvariants.lean` | `entrySequences`, `visible`, `SubInv` (eleven clauses), `StateInv`, `SubShape` | the invariants as predicates |
| `SubCore.lean` | lookups through `updateStream`/`removeStream`/`insertStream` (incl. `lookupStream_removeStream_self`); `applyPublish_nextSequence`, `publishStep_ok_eq`, `deleteStep_ok_eq`, `createStep_lookup_preserved`, `createStep_ok_shape`, `getStep_ok_eq`, `lastMsgStep_ok_eq`, `step_lookup_preserved`; `entrySequences_*` list helpers and the `visible` equations (`entrySequences_visible_admit`, `visible_admit`, `visible_drain`, `visible_drain_done`); `pairwise_*`; `SubInv.of_stream_lookup` | facts about the first-slice core and the `visible` equations the subscriber layer consumes |
| `SubProofs.lean` | `*_core` frame lemmas, SA1 `reachableSub_core`; `selectReplay_sublist/_mem/_pairwise`; `SubInv.core_eq`, `SubInv.of_lookups` (both instances of `of_stream_lookup`); the three faces `deliverOne_admit`/`_overflow`/`_skip` and `endOne_skip`; per-label preservation `newSubscriber_inv`, `pullStep_inv`, `unsubscribe_inv`, `deliverOne_inv` (through the faces), `endOne_inv` | one preservation lemma per transition function |
| `SubReachable.lean` | `mem_of_lookupSub`, `mem_updateSub_eq` (strong form; `mem_updateSub` derived), `applyRegister_enabled`; `afterOp_inv`, `applyOp_inv`, `applyRegister_inv`, `applyPull_inv`, `applyUnsubscribe_inv`, `apply_inv`; SA2 `stateInv_reachable`, SA3 `pending_le_capacity`; **`reachableSub_all`**; `lookupSub_*` (update/fresh/append/map/of_mem_pairwise), `updateSub_keys`, `keys_map_snd`, `shape_of_keys`, `apply_shape`, `subShape_reachable`, `lookupSub_nextId` | the only `ReachableSub` induction and the principle everything else uses |
| `SubStatements.lean` | `sub_core_inv`; `publishedMessage`; `applyOp_ok_eq`, `afterOp_publish_sub`, `publish_sub`; SA4a/c/d; SA5; SA6; `LagInv`, `LagState`, `lagInv_*`, `lagState_afterOp`, `apply_lag`, `lagState_reachable`; SA7 (`lagged_iff_of_open`, the explicit-premise form, with `lagged_iff` as its corollary); `applyAll`, `Negative`, `subNegatives`, `all_sub_negatives` | the frozen statements beyond SA1–SA3 |
| `SubHistory.lean` | `RegInfo`, `SubStateH`, `initialSubH`, `erase`, `lookupReg`, `labelMessage`, `committedAfter`, `regsAfter`, `applyH`, `NextH`, `ReachableSubH`, `liveKeep`, `liveOf`, `liveEntries`; AV1/AV2; `lookupReg_*`, `liveOf_*` (incl. `liveKeep_admit`, `liveOf_admit`); `HistInv`, `histInv_*`, `histInv_reachable`; SA5h `visible_global`, `entries_committed` | the proof-only ledger (history variable) |

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

Exporter schema 2 with the stage-A traces and `pull` labels (slice §14) and the codex harness
brief; then the r3.1 assurance review (five axes, `docs/reviews/`); then stage B
(`EffectQueue`, the quiescence assumption A4 discharged as a weak forward simulation, T14′).
