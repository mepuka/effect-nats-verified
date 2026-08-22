import EffectNatsSubstrate.Step

/-!
# Invariants and reachability

The frozen statement surface (proposal §4.1). Invariants are extrinsic — plain
data plus propositions, proven over reachable states — because
publish/prune/rollup create no invalid intermediate states worth typing away,
and intrinsic sortedness would tax every operation.

`Reachable` needs no error case: errors return through `Except` without a new
state.

`streamInv` is the first slice's invariant and is kept exactly as frozen; the
second slice (T3–T7) adds `seqPositive` and `capacityBounded` beside it rather
than widening it, so the first slice's statements are untouched.
-/

namespace EffectNatsSubstrate

/-- Per-stream invariant: message sequences strictly increase along the list,
and every stored sequence is below `nextSequence`. This is invariant I1 of the
parent discussion §15.2 (monobox order per stream) at the storage layer. -/
def streamInv (st : StreamState) : Prop :=
  st.messages.Pairwise (fun a b => a.sequence < b.sequence)
    ∧ ∀ m ∈ st.messages, m.sequence < st.nextSequence

def stateInv (s : JSState) : Prop := ∀ p ∈ s, streamInv p.2

/-- States reachable from empty by successful steps. -/
inductive Reachable : JSState → Prop
  | init : Reachable emptyState
  | step {s s' : JSState} {op : Op} {r : Ret} :
      Reachable s → step s op = .ok (s', r) → Reachable s'

/-- Sequences are assigned from `1` (`src/internal/JetStreamMemory.ts:113`), so
`0` is never a stored sequence — which is what lets
`expectedLastSubjectSequence = 0` assert "the subject has no message yet"
(`src/internal/JetStream.ts:37`). -/
def seqPositive (st : StreamState) : Prop :=
  0 < st.nextSequence ∧ ∀ m ∈ st.messages, 0 < m.sequence

/-- A positive `maxMessagesPerSubject` bounds every subject's retained history
(`src/internal/JetStreamMemory.ts:165-172`); `0` is unlimited. -/
def capacityBounded (st : StreamState) : Prop :=
  0 < st.config.maxMessagesPerSubject →
    ∀ subject, (forSubject st.messages subject).length ≤ st.config.maxMessagesPerSubject

/-- The most recent `limit` entries of a storage-ordered list; `0` keeps all.
Specification-side: what pruning must leave for the published subject (T6). -/
def keepLatest (limit : Nat) (l : List StoredMessage) : List StoredMessage :=
  if limit = 0 then l else l.drop (l.length - limit)

end EffectNatsSubstrate
