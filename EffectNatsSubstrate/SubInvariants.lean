import EffectNatsSubstrate.Next

/-!
# Stage-A invariants and observables — definitions

The representation invariant `SubInv` (slice document §9.2, §11), the
consumer-visible sequence `visible`, and the helpers the r3 statements use.
Definitions only; the theorems live in `SubProofs.lean`.

The clauses are the ones preservation needs: besides the capacity bound and
the status discipline, `lastEnqueued` bounds every entry the consumer can see
(pulled or buffered), equals the last buffered entry while the buffer is
non-empty, and stays below the stream head while the subscriber is registered —
so a newly stored message (sequence = the head) is larger than everything
visible, which is what keeps `visible` strictly increasing (T11) and makes the
lag failure carry the last visible entry (T13′).
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
  capacityPos : 1 ≤ sub.policy.capacity
  capacity : sub.pending.length ≤ sub.policy.capacity
  registeredOpen : sub.registered = true → sub.status = .opened
  registeredStream : sub.registered = true →
    ∃ st, lookupStream s.core sub.stream = some st ∧ sub.lastEnqueued < st.nextSequence
  closingNonempty : ∀ e, sub.status = .closing e → sub.pending ≠ []
  doneEmpty : ∀ e, sub.status = .done e → sub.pending = []
  shutDownClear : sub.status = .shutDown → sub.registered = false ∧ sub.pending = []
  pendingMatch : ∀ m ∈ sub.pending, matchesAny sub.filters m.subject = true
  visibleStrict : (entrySequences (visible sub)).Pairwise (· < ·)
  visibleBound : ∀ n ∈ entrySequences (visible sub), n ≤ sub.lastEnqueued
  pendingLast : sub.pending ≠ [] →
    (sub.pending.map (·.sequence)).getLast? = some sub.lastEnqueued

def StateInv (s : SubState) : Prop := ∀ p ∈ s.subs, SubInv s p.2

/-- State shape (slice document §9.2 `subShape`): subscriber ids are strictly
ascending in `subs` — the JS `Set`'s insertion order is registration order —
and every id is below `nextId`, which is what `lookupSub` after `register`
relies on (SA4a). Preserved by `apply`; proved over `ReachableSub` as
`subShape_reachable`. -/
def SubShape (s : SubState) : Prop :=
  (s.subs.map Prod.fst).Pairwise (· < ·) ∧ ∀ p ∈ s.subs, p.1 < s.nextId

end EffectNatsSubstrate
