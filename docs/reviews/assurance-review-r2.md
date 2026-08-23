# Assurance review — signature snapshot r2 (T3–T7)

- **Date:** 2026-08-22
- **Scope:** `formal/effect_nats_substrate/` at `docs/signature-snapshot.md` r2; the
  first-slice proposal `research/2026-08-22-first-slice-jetstream-memory-lean-model.md`
  §4.1; transliteration pin `mepuka/effect-nats` @ `d06223f`.
- **Reviewer:** the session that produced the slice. This is a self-review against the
  five-axis schema; an independent pass (the corpus's **Verify** workflow) is the next
  assurance step and is not replaced by this record.
- **Mutation:** none during the review. The one change that followed it (an absence check
  added to the third trace, F2) was made after the findings were recorded and re-gated.

## Claim

- **Headline, exact scope:** every state reachable from the empty state by the five
  sequential operations satisfies T1–T7 as stated in snapshot r2; three concrete histories
  mirroring conformance C1–C6 check under the Lean kernel.
- **Source intent:** proposal §4.1 rows T1–T7; conformance cases C1–C6 and the memory
  interpreter `src/internal/JetStreamMemory.ts` at the pin.
- **Formal declarations:** the 25 theorems of snapshot r2 (`docs/signature-snapshot.md`).
- **Implementation link claimed:** line-by-line transliteration of
  `src/internal/Subject.ts` and the sequential part of `src/internal/JetStreamMemory.ts`.
  No trace replay, no refinement relation — see F5.

## Axes

### 1. Intent → model

- `forSubject` is the TS `forSubject` local (`:167`); `keepLatest` is specification-side and
  is proved equal to what `pruneSubject` leaves (`forSubject_pruneSubject_self`), so the T6
  statement is not a restatement of the implementation in its own terms.
- `lastSequenceFor` returns `0` for an empty subject exactly as `:148` does; the sentinel
  reading needs positivity of stored sequences, which is `seqPositive`, not an assumption.
- The rollup gate and the CAS gate are checked in the implementation's order (`:139-152`);
  `publish_ok_iff` is the success conjunction and carries no order — the order is pinned by
  the error-specific theorems. Probe: swapping the rollup and CAS
  gates changes which error a publish that fails both raises; `publish_rollup_denied` takes
  no CAS hypothesis, `publish_cas_mismatch` takes the rollup hypothesis — consistent with
  the order.
- **F1 (model-mismatch, minor, confirmed, by design):** a negative `maxMessagesPerSubject`
  is "unlimited" in the implementation (`:166`) and a typed rejection in the model
  (`validate_rejects_negative`). Recorded in the proposal §3.1; not new in r2.
- **F6 (model-mismatch, minor, found by `research/2026-08-22-effect-nats-substrate-vp1.md`
  VP1-01):** `headerLookup` is first-match over `List (String × String)` while the seam's
  `ReadonlyMap` has one value per key; a repeated key makes the two disagree. Declared as a
  carrier restriction (proposal §3.1), not modeled.

### 2. Model → theorem

- Witnesses: trace 1 exercises `publish_cas_iff` (success) and `lastMessage_max`; trace 2
  exercises `createStream_conflict` and `publish_unbound`; trace 3 exercises
  `publish_retains_latest` (limit 2, three publishes), `publish_rollup_view` and
  `publish_other_subjects_unchanged` (rollup beside an untouched subject),
  `publish_rollup_denied`, `publish_cas_mismatch` (expected 0 / actual 1), and — after F2 —
  `lastMessage_absent`.
- Vacuity probes: every hypothesis set of T3–T7 is inhabited by one of the traces' states
  (a fresh stream satisfies `forSubject st.messages subject = []`; the stale CAS satisfies
  `e ≠ lastSequenceFor …`; the no-rollup stream satisfies `allowRollup = false`).
- Counterexample retained: `publish_drops_oldest` is stated with `m ∉ st'.messages`; a
  version quantifying over `forSubject` alone would miss that the new message is in `st'` but
  not in `st`. The statement's direction (pre-state message, absent afterwards) avoids it.
- **F2 (observational-gap, minor, confirmed, fixed):** C4's typed absence had no trace
  witness; `lastMessage_absent` was proved but un-witnessed. An absence check was added to
  trace 3 after the review.
- **F3 (observational-gap, minor, confirmed):** C5/C6 observe storage through `consume`
  (`test/JetStreamConformance.ts:125-132`, `:148-155`); trace 3 inspects `forSubject` of the
  state instead. "Mirrors" means the same storage outcome, not the same observation path —
  the proposal §3.3 says so. Closes only with the subscriber slice.

### 3. Proof

- Gate (from a clean `.lake/build`): `lake build` succeeds, no warnings; `grep` for
  `sorry|native_decide|axiom|unsafe` in `EffectNatsSubstrate/` finds nothing;
  `#print axioms` on all 25 theorems reports at most `propext`, `Classical.choice`,
  `Quot.sound` (`validate_ok_sound`: `propext` only; `validate_rejects_negative`:
  `propext`, `Quot.sound`).
- Mechanism: traces close by `decide` (kernel reduction), not `native_decide`; no
  `implemented_by`, `extern`, or options in the package.
- Imports: Lean core only, `leanprover/lean4:v4.33.0`; `lake-manifest.json` has no packages.
- Statement lock: the r1 declarations are byte-identical in type; `lastForSubject`'s body
  changed from the inline filter to `(forSubject …).getLast?`, definitionally the same term
  (the r1 traces still close by `decide` without change). `streamInv` was not widened.
- **F4 (proof-debt): none.**

### 4. Implementation / refinement

- **F5 (implementation-gap, major, confirmed, unchanged from r1):** there is no refinement
  relation between `step` and the TypeScript interpreter; fidelity rests on the module-header
  transliteration diff. The strongest supported claim is "the Lean `step` agrees with the
  memory interpreter on the three kernel-checked histories and was transliterated line by
  line"; not "the interpreter satisfies T1–T7". Owner: the trace-ingestion slice
  (proposal §6).
- Deliberately wrong implementation probe (thought experiment, not executed): an
  interpreter that pruned the newest message instead of the oldest would pass
  `reachable_capacity` and fail `publish_drops_oldest`; one that applied rollup after
  pruning would pass `publish_rollup_view` and fail nothing in r2 — the order of rollup and
  prune is observationally irrelevant when rollup leaves one message. Recorded so nobody
  reads a theorem into that order.

### 5. External / observational

- **F6 (external-trust, minor, assumed):** the trusted base is the Lean 4.33.0 kernel and
  the core library's `List`/`String` lemmas (`LawfulBEq String` in particular). No FFI, no
  generated code.
- The conformance suite is the only link from the model to `nats-server`; it runs on the
  memory interpreter and the live adapter, not on this model. Server behaviour on
  order-sensitive `ConfigEq` remains an open finding target (proposal §7).

## Evidence bundle

```text
proved       : 25 theorems of snapshot r2; kernel; axioms ⊆ {propext, Classical.choice, Quot.sound}
modelChecked : —
tested       : C1–C6 on the memory interpreter and live adapter (effect-nats test suite at the pin),
               not on this model
measured     : —
monitored    : —
assumed      : F6 trusted base; transliteration faithfulness (module headers)
unknown      : refinement to the TS interpreter (F5); server agreement on ConfigEq (proposal §7)
```

## Verdict

- Intent → model: **CONFIRMED-WITH-ERRATA** (F1 by design, F3 recorded).
- Model → theorem: **CONFIRMED** (F2 fixed).
- Proof: **CONFIRMED**.
- Implementation: **GAP** (F5) — no claim about the interpreter beyond transliteration.
- External: **GAP** — no claim about the server.
- End to end: the headline claim above is the strongest supported statement; anything
  stronger ("the interpreter is correct", "the model equals the server") is not supported by
  this slice.
