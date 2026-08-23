# Effect-NATS substrate model

A Lean 4 model of the in-memory JetStream interpreter in
[`effect-nats`](https://github.com/mepuka/effect-nats) — the component that stands in for a
NATS server in that library's tests — with kernel-checked proofs of how it behaves. The model
is a line-by-line transliteration of the TypeScript at a pinned commit. Its theorems are about
the model; the link back to the code is a fixture of recorded histories that effect-nats
replays against both the memory interpreter and a live server.

This repository is the package `formal/effect_nats_substrate/` of the Foldable research
repository, published on its own with its history. The slice documents, reviews, and plan it
cites under `research/…` live in Foldable.

## What is proved

The sequential core covers stream creation, lookup, deletion, publish, and last-message
lookup. Seven theorems (T1–T7) hold on every state reachable from the empty state: creating a
stream twice with the same configuration is idempotent and conflicts otherwise; sequence
numbers within a stream strictly increase; the last message of a subject carries that
subject's highest sequence; compare-and-set publish succeeds exactly when the expected
sequence matches; a rollup publish replaces the subject's history; a per-subject capacity
keeps the most recent messages; a publish to an unbound subject is rejected.

The subscriber layer (stage A) covers `consume` with the `TerminateOnLag` buffer policy:
registration with every start position, a bounded pending buffer, whole-buffer pulls,
termination on overflow, stream deletion, and unsubscribe. Its theorems (SA1–SA7, SA5h) say
that the buffer never exceeds its capacity; that registration hands the consumer exactly the
replay snapshot the TypeScript computes; that a pull changes nothing the consumer can see, a
matching publish appends exactly the stored message when there is room and ends the
subscription when there is none, and every other operation leaves the visible sequence alone;
that deleting a stream ends its registered subscribers and re-creating it restarts at
sequence 1; that the lag error carries the sequence of the last entry the consumer saw; and,
the global form, that what a registered subscriber can see is its replay snapshot followed by
exactly the matching messages published after it registered. Storage forgets pruned and
rolled-up messages, so that last statement is proved on a proof-only ledger of every
publish (a history variable in the sense of Abadi and Lamport), with theorems showing the
ledger changes no behaviour.

Witnesses accompany the theorems. Sixteen traces mirror the conformance cases of the
TypeScript test suite and are checked by the kernel with `decide`; ten negative witnesses
show which steps the model refuses; two deliberately wrong models — one-element pulls, and a
`lastDelivered` that advances on the overflowing message — fail the traces built to catch them
and pass the rest.

The package has zero `sorry`, declares no axioms, uses no `native_decide`, and closes every
theorem under `propext`, `Classical.choice`, and `Quot.sound`. It depends on Lean core only
(`leanprover/lean4:v4.33.0`).

## What the proofs do not say

A theorem here is a fact about the model. Whether the model matches the TypeScript rests on
the transliteration (pins `d06223f` for the core, `872bd7f` for subscribers), the declared
carrier restrictions (unique header keys; non-negative capacity), and replay of the exported
traces. Replay evidence exists today for the sequential core; the subscriber traces are not
yet exported in a form the harness can run.

Four facts about the runtime are assumed, named, and not proved here. Q1: a pull drains the
whole buffer. Q2: failing a queue delivers its buffer before the error. Q3: shutdown discards
the buffer. A4: the model places whole pulls between whole operations, while the runtime can
schedule a consumer's pull inside a publish's fan-out; for `TerminateOnLag` every such
interleaving is assumed equivalent to one of the model's placements. Stage B discharges them.

Out of scope: the `PullWindow` policy and its blocked state, the Effect `Queue` itself,
acknowledgements, redelivery, durable consumers, and any claim about `nats-server` beyond what
a replay records.

## What comes next

- Export the subscriber traces (fixture schema 2) and extend the effect-nats replay harness
  to realise them, with a free-running consumer mode to test assumption A4 empirically.
- An assurance review of the stage-A result across specification, model, proof,
  implementation, and deployment assumptions.
- Stage B: a model of Effect's `Queue` transliterated from its source, proofs of Q1–Q3, a
  simulation from runtime steps to the model's labels that discharges A4, the `PullWindow`
  policy, and liveness stated under a named fairness assumption.
- A session-type pilot: the consume protocol as a binary session type checked against the
  subscriber model, then a multiparty family over N subscribers.

## Run

```text
lake build                                # every module, every proof, the sixteen traces
lake build effect_nats_traces
lake exe effect_nats_traces [-- --foldable-commit <hash>] > sequential-traces.json   # schema 1
lake exe effect_nats_traces -- --subscriber [--foldable-commit <hash>] > subscriber-traces.json   # schema 2
```

The exporter is deterministic: two runs of either mode produce identical bytes. Schema 2 prints
the stage-A subscriber traces as labels with their `events`, `counts`, `finalObserved`, and each
subscriber's free-running acceptance set (`SubPlacements.lean`; slice document §14). effect-nats
keeps both fixtures at `test/fixtures/lean/` with the producing commit embedded and regenerates
them by hand when the traces change.

## Layout

```text
EffectNatsSubstrate/
  Subject.lean       NATS subject matching
  Config.lean        stream configuration, validation, equality
  State.lean         messages, streams, the state as an association list
  Step.lean          the five operations as one step function
  Invariants.lean    per-stream invariants and reachability
  Views.lean         per-subject views of a committed publish
  Proofs.lean        T1–T7
  Traces.lean        the sequential traces, checked by decide
  Subscriber.lean    subscriber carriers
  SelectReplay.lean  the replay snapshot for each start position
  Next.lean          labels, fan-out, pull, the transition function, reachability
  SubTraces.lean     the subscriber traces and the two wrong models
  SubInvariants.lean the subscriber invariant and the visible sequence
  SubCore.lean       core facts and the visible/entrySequences equations the subscriber proofs use
  SubProofs.lean     preservation of the invariant by each transition
  SubReachable.lean  reachability: two bootstrap inductions and reachableSub_all, which every later fact goes through
  ApplyLemmas.lean   the abstract independence lemmas behind a4_inclusion (stage-B1 P4a)
  SimAgree.lean      agreement at one subscriber: the helpers a4_complete uses (stage-B1 P5a)
  SubStatements.lean SA4–SA7 and the negative witnesses
  SubHistory.lean    the ledger model and the global statement SA5h
  SubPlacements.lean the free-running acceptance sets (chunk histories over every pull placement)
  EffectQueue.lean   the Effect queue component (stage B1)
  Runtime.lean       the runtime LTS at A4's step granularity
  RtInvariants.lean  the runtime invariant
  RtTraces.lean      the stage-B1 scenarios, checked by decide
  Sim.lean           the stage-B1 statements: A4Inclusion, A4Complete
  EffectQueueLaws.lean the queue laws Q1–Q3 as theorems (SB1)
  SimRelation.lean   the relation behind a4_inclusion: linearization points, corrSub, Rel, RelHist
  SimProof.lean      the simulation: per-label preservation of the relation, the induction,
                     and a4_inclusion_of_rtInv (stage-B1 P4b)
  RtWitnesses.lean   non-vacuity witnesses and empty-list guards for the B1 frozen statements (P6a)
  ApplyLaws.lean     the laws stage A assumes of deliver/pull, and one theorem re-derived over them (L7a)
  SimPlaced.lean     the acceptance sets enumerate every enabled pull placement (stage-B1 P5b)
  SimComplete.lean   the merge that turns a4_inclusion's witness into a pull placement of the
                     trace's labels, and a4_complete_of_rtInv (stage-B1 P5c)
Main.lean            the fixture exporter
```

[docs/signature-snapshot.md](docs/signature-snapshot.md) records the frozen theorem
statements; a statement changes only through the slice document and the snapshot together.
[docs/stage-a-proof-map.md](docs/stage-a-proof-map.md) explains how the stage-A proofs fit
together; [docs/stage-b1-proof-map.md](docs/stage-b1-proof-map.md) does the same for stage B1 and
holds the proof packets. Reviews are under `docs/reviews/`.
