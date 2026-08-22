# Effect-NATS substrate model

Executable Lean 4 reference model of the **sequential core** of effect-nats's in-memory
JetStream interpreter (`mepuka/effect-nats` @ `d06223f`): configuration, subject matching,
stream storage, and the five non-streaming operations, with the sequential-core invariant
proofs (T1–T7) and kernel-checked worked traces. Scope, corrected obligations, and deferrals
are fixed by
[the first-slice proposal](../../research/2026-08-22-first-slice-jetstream-memory-lean-model.md);
this package implements exactly its §3 bootstrap boundary.

It separates three questions:

1. what the seam's sequential state and transitions are (`Subject`, `Config`, `State`, `Step`);
2. which properties those transitions have from the empty state (`Invariants`, `Views`,
   `Proofs` — T1 create-idempotence/conflict, T2 strict per-stream sequence discipline,
   T3 last-message-is-max, T4 compare-and-set, T5 rollup, T6 capacity and most-recent
   retention, T7 subject binding);
3. what a recorded history looks like against the model (`Traces` — a positive, a rejected,
   and a prune/rollup/CAS trace, checked by the kernel with `decide`).

Deliberately small: no subscribers, no consume/buffer policies, no JSONL trace ingestion, no
`.nuscr` printer — deferred until the pending/pull subscriber semantics are frozen (proposal
§4.3, §6; design note `research/2026-08-22-effect-nats-subscriber-model-design-note.md`).
This is the parent discussion's (§18) trace-replay bridge at its honest size: the sequential
spine first, kernel-checked traces standing in for the replay harness until the
observation-ordering question is answered.

## Run

```text
lake build   # elaborates every module, all proofs, and the three kernel-checked traces
```

## Layout

```text
EffectNatsSubstrate/
  Subject.lean     token-level NATS subject matching (structural splitter, decide-reducible)
  Config.lean      RawStreamConfig → validate → StreamConfig; ConfigEq; canonicalize
  State.lean       StoredMessage, StreamState, JSState association list; forSubject
  Step.lean        Op / JSError / Ret; step : JSState → Op → Except JSError (JSState × Ret)
  Invariants.lean  streamInv / stateInv / Reachable; seqPositive, capacityBounded, keepLatest
  Views.lean       forSubject through publishBase / newMessage / pruneSubject
  Proofs.lean      T1–T7; zero sorry; standard axioms only
  Traces.lean      positive, rejected, and prune/rollup/CAS worked traces, kernel-checked
```

Every per-subject theorem is an equation on `forSubject` (the storage-order filter, the TS
`forSubject` local). `Views.lean` is the only module that reasons about `dropOldest`,
`pruneSubject`, and `publishBase` directly; it ends in the two equations that characterise
a committed publish — the published subject's view becomes
`keepLatest limit (prior-or-[] ++ [new])`, every other subject's view is unchanged — and
`Proofs.lean` works from those.

[docs/signature-snapshot.md](docs/signature-snapshot.md) freezes the public proof surface.
Naming follows the corpus conventions: distinct identifier names (`StreamName`, `SubjectName`,
`StreamSeq`, `PayloadHash`), a deterministic `step` now with the nondeterministic `Next`
relation reserved for the subscriber slice, and `step`/`Reachable` vocabulary compatible with
cslib's LTS layer when the protocol slice arrives. Lean is pinned by `lean-toolchain`
(`leanprover/lean4:v4.33.0`); the package intentionally has no external dependencies.
