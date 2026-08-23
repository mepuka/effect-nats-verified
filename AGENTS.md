# formal/effect_nats_substrate/ — package rules

Extends `../../AGENTS.md`. This package is the Lean model of the effect-nats JetStream
sequential core; its specification is a research document, and the model follows the
document, never the other way around.

## Contract

- **The spec is a slice document.** The sequential core follows
  `research/2026-08-22-first-slice-jetstream-memory-lean-model.md` (corrected revision); the
  stage-A subscriber layer follows `research/2026-08-22-subscriber-stage-a.md`. Each fixes
  scope, obligations, and deferrals. A change to the model's scope, an enabling condition, an
  invariant clause, or a theorem statement starts as a correction to the slice document, not
  as an edit here — also while the snapshot that covers it is only proposed.
- **Citation roots.** Module headers cite `src/…` and `test/…` paths meaning
  `mepuka/effect-nats` @ `d06223f` for the sequential core (`Subject` … `Traces`) and
  @ `872bd7f` for the stage-A modules (`Subscriber`, `SelectReplay`, `Next`, `SubTraces`,
  `Sub*`); the five sequential operations are byte-identical between the two pins (slice
  document header). Transliteration is line-by-line against the declaring pin under the
  declared carrier restrictions (unique header keys — the seam's `ReadonlyMap` — and
  non-negative capacity; proposal §3.1): an input outside them is not a claim about the seam.
  When a pin moves, re-diff the transliterated sources *and re-open every `:line` citation*
  before touching any proof — line numbers never survive a pin move unverified.
- **Elaboration is not fidelity.** A successful Lean elaboration proves the stated
  proposition, not that the proposition models the intended system. The model-fidelity
  boundary is the transliteration diff plus, later, trace replay — compatibility on recorded
  histories, never "equivalence". A trace's `mirrors` labels are unchecked metadata, not
  evidence.
- **Deferred means absent.** `TerminateOnLag` subscribers entered through the stage-A slice
  document (`pending`, `lastEnqueued`, a status, an explicit `pull`; snapshot r3, proposed).
  Still absent, not stubbed: `PullWindow` and its `Blocked` state, the `EffectQueue` runtime
  model that discharges Q1–Q3 and the quiescence assumption A4 (stage B), JSONL trace
  ingestion, payload hashing, `.nuscr` printing. Each enters only through a new slice
  document.
- **Statement freeze.** `docs/signature-snapshot.md` records the frozen public surface.
  Proof repair may change proof bodies or add proved helper lemmas; changing a frozen
  statement updates the snapshot and the proposal in the same change. A proposed (unratified)
  snapshot section is not a licence to prove: the slices plan's gate for the slice decides
  when proofs may start, and a statement that tightens while a candidate is being proved is
  logged old/new in the snapshot's revision log in the same change.
- **Per-subject statements read through `forSubject`.** `Views.lean` is the only module
  that reasons about `dropOldest`, `pruneSubject`, and `publishBase` directly; it ends in
  the two equations that characterise a committed publish
  (`forSubject_applyPublish_self`, `forSubject_applyPublish_other`). A new per-subject
  theorem is stated on the view and proved from those two equations; a proof that needs to
  unfold the pipeline again is a sign the view lemmas are missing a fact, which then goes
  into `Views.lean`.
- **Per-stream invariants go through `reachable_all`.** A new invariant on reachable streams
  is a predicate with a create case and an `applyPublish` case; do not write a second
  induction over `Reachable`. Likewise stage-A invariants go through `stateInv_reachable`: a
  new per-subscriber fact is a clause of `SubInv` (or a predicate with one preservation lemma
  per label), and `SubReachable.lean` holds the only induction over `ReachableSub`. A stage-A
  proof that unfolds `applyPublish` is missing a `Views.lean`/`Proofs.lean` fact
  (`publish_assigns`).
- **Traces are data.** A new trace is a `Trace` value, its `runTrace … = true` theorem, and an
  entry in `allTraces`; the exporter prints `allTraces`, and the effect-nats fixture is
  regenerated from it (slices plan, slice 2). A step the memory interpreter cannot replay
  (boundary validation the model performs and the interpreter does not) carries
  `replay := false`; nothing else is ever hidden from the fixture. `Main.lean` is the only
  module that may import `Lean`; the library stays on `Init`.

## Gate

Run from this directory before saving work:

```text
lake build   # must be clean: no errors, no warnings
```

- Every module under `EffectNatsSubstrate/` is imported by the root `EffectNatsSubstrate.lean`;
  an unimported module is invisible to the gate.
- Zero `sorry`, zero `axiom` declarations, zero `native_decide`, zero `unsafe` in the package
  (`grep -rn "sorry\|native_decide\|axiom\|unsafe" EffectNatsSubstrate/` finds nothing).
- `#print axioms` on every public theorem reports at most `propext`, `Classical.choice`,
  `Quot.sound`.
- Toolchain stays `leanprover/lean4:v4.33.0` (matching `../jetstream_workflows/`); no
  external dependencies — Lean core only.
- `decide`-checked traces stay kernel-reducible: structural recursion only in anything `step`
  evaluates (no `String.splitOn`-style well-founded helpers).
- The exporter is deterministic: `lake build effect_nats_traces && lake exe effect_nats_traces`
  twice, `cmp` the outputs (Foldable law 4 — no timestamps, paths, or randomness).
- No nested `.git`; `.lake/` stays gitignored.
