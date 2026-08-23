# formal/effect_nats_substrate/ — package rules

Extends `../../AGENTS.md`. This package is the Lean model of the effect-nats JetStream
sequential core; its specification is a research document, and the model follows the
document, never the other way around.

## Contract

- **The spec is the first-slice proposal.**
  `research/2026-08-22-first-slice-jetstream-memory-lean-model.md` (corrected revision) fixes
  scope, obligations, and deferrals. A change to the model's scope or theorem statements
  starts as a correction to that document, not as an edit here.
- **Citation root.** Module headers cite `src/…` and `test/…` paths meaning
  `mepuka/effect-nats` @ `d06223f`. Transliteration is line-by-line against that pin under
  the declared carrier restrictions (unique header keys — the seam's `ReadonlyMap` — and
  non-negative capacity; proposal §3.1): an input outside them is not a claim about the seam.
  When the pin moves, re-diff `Subject`/`State`/`Step` against the TS sources before touching
  any proof.
- **Elaboration is not fidelity.** A successful Lean elaboration proves the stated
  proposition, not that the proposition models the intended system. The model-fidelity
  boundary is the transliteration diff plus, later, trace replay — compatibility on recorded
  histories, never "equivalence". A trace's `mirrors` labels are unchecked metadata, not
  evidence.
- **Deferred means absent.** Subscribers, `consume`, buffer policies, `unsubscribe`, JSONL
  trace ingestion, payload hashing, `.nuscr` printing: not modeled, not stubbed. They enter
  only through a new slice document that freezes the pending/pull subscriber semantics
  (proposal §4.3; design note
  `research/2026-08-22-effect-nats-subscriber-model-design-note.md`) — a subscriber model
  needs `pending`, `lastEnqueued`, a status, and an explicit pull operation, because the
  implementation decides overflow on pending occupancy.
- **Statement freeze.** `docs/signature-snapshot.md` records the frozen public surface.
  Proof repair may change proof bodies or add proved helper lemmas; changing a frozen
  statement updates the snapshot and the proposal in the same change.
- **Per-subject statements read through `forSubject`.** `Views.lean` is the only module
  that reasons about `dropOldest`, `pruneSubject`, and `publishBase` directly; it ends in
  the two equations that characterise a committed publish
  (`forSubject_applyPublish_self`, `forSubject_applyPublish_other`). A new per-subject
  theorem is stated on the view and proved from those two equations; a proof that needs to
  unfold the pipeline again is a sign the view lemmas are missing a fact, which then goes
  into `Views.lean`.
- **Per-stream invariants go through `reachable_all`.** A new invariant on reachable streams
  is a predicate with a create case and an `applyPublish` case; do not write a second
  induction over `Reachable`.
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
