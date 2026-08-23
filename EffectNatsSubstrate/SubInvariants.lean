import EffectNatsSubstrate.Next

/-!
# Stage-A invariants and observables — definitions

The representation invariant `SubInv` (slice document §9.2, §11), the
consumer-visible sequence `visible`, and the helpers the r3 statements use.
Definitions only; the theorems live in `SubProofs.lean`.
-/

namespace EffectNatsSubstrate

/-- The sequences of the entries in an observed list, in order. -/
def entrySequences (obs : List Observed) : List StreamSeq :=
  obs.filterMap (fun o => match o with | .entry m => some m.sequence | _ => none)

/-- The consumer-visible sequence: what has been pulled plus what is buffered. -/
def visible (sub : Subscriber) : List Observed :=
  sub.observed ++ sub.pending.map Observed.entry

/-- Representation invariant of one subscriber in a state (SA2). -/
structure SubInv (s : SubState) (sub : Subscriber) : Prop where
  capacity : sub.pending.length ≤ sub.policy.capacity
  registeredOpen : sub.registered = true → sub.status = .opened
  registeredStream : sub.registered = true → (lookupStream s.core sub.stream).isSome = true
  closingNonempty : ∀ e, sub.status = .closing e → sub.pending ≠ []
  shutDownClear : sub.status = .shutDown → sub.registered = false ∧ sub.pending = []
  pendingMatch : ∀ m ∈ sub.pending, matchesAny sub.filters m.subject = true
  pendingStrict : sub.pending.Pairwise (fun a b => a.sequence < b.sequence)
  pendingAfterObserved :
    ∀ m ∈ sub.pending, ∀ m', Observed.entry m' ∈ sub.observed → m'.sequence < m.sequence

def StateInv (s : SubState) : Prop := ∀ p ∈ s.subs, SubInv s p.2

end EffectNatsSubstrate
