import EffectNatsSubstrate.Sim
import EffectNatsSubstrate.RtInvariants

/-!
# The relation behind `a4_inclusion` — definitions (stage B1, proof-side)

The induction that proves `A4Inclusion` (`docs/stage-b1-proof-map.md` §2.4) walks a runtime
execution keeping an abstract prefix `labels` (already matched) and an owed suffix (the abstract
publish or deletion of the fan-out in flight, followed by the consumer labels of subscribers whose
linearization point has passed). These definitions fix the relation exactly; they are proof-side
predicates like `LagInv`/`HistInv` in stage A — not frozen, reshapeable as long as the frozen
statements still follow.

**Linearization point** of the fan-out for subscriber `i` (overwatch T7, kernel-checked in
`research/logs/rt_probe10.lean`): its `check` when the recorded decision is overflow (the stale
`Queue.size` read is the abstract `deliverOne`'s overflow test), its `resolve` when the decision
is admit (the offer is the abstract append). A consumer label of `i` before the point is matched
at once against the pre-publish abstract state; after it, it is owed until `endFanOut`.

**`closeA` is `unsubscribe`**, matched at the subscriber's own point: before it, immediately (into
`labels`, ahead of the owed operation); after it, into the owed suffix. Either way the `Set` delete
is what `subscriberCount` sees and `closeStarted` freezes the subscriber's history on both sides
(the runtime disables its pulls; the abstract subscriber is `shutDown`).

**The check/resolve window** (`pendingOf`). A `check` that decided overflow linearizes the abstract
publish for that subscriber, but the runtime performs the `Set` delete and the `Queue.fail` only at
its `resolve`; in between, the runtime subscriber is the abstract one *minus* that failure. The
relation therefore compares the abstract state against `pendingOf f id r` — `r` itself except for
the one subscriber whose overflow is decided and unresolved, which is compared after the failure
the `resolve` will perform. `resolve` then re-establishes the relation by definitional equality.
-/

namespace EffectNatsSubstrate

/-! ## The fan-out's view of one subscriber -/

/-- The abstract publish/deletion of the fan-out in flight has already been applied to `id`. -/
def pointPassed (f : FanOut) (id : SubId) : Bool :=
  f.visited.any (fun p => p.1 == id) || (f.decided == some (id, true))

/-- The abstract label a fan-out in flight owes. -/
def owedOp : FanKind → Label
  | .publish stream m expectedLast =>
    .op (.publish stream m.subject m.payload m.headers expectedLast m.timestampMillis)
        (.ok (.sequence m.sequence))
  | .delete name => .op (.deleteStream name) (.ok .unit)

/-- The subscriber is still scheduled by the fan-out in flight. -/
def Scheduled (f : FanOut) (id : SubId) : Prop :=
  id ∈ f.remaining ∨ ∃ b, f.decided = some (id, b)

/-! ## One subscriber's correspondence -/

/-- Nothing can be observed from this subscriber any more: its scope is closing, or its queue is
shut down. -/
def Closed (r : RtSubscriber) : Prop := r.closeStarted = true ∨ r.queue.status = .shutDown

/-- One subscriber's correspondence. A closed subscriber is only required to agree on what
`A4Inclusion` reads — its chunk history and its de-registration — because nothing can be observed
from it any more (the runtime queue may still hold a buffer, E5). Every other subscriber erases
exactly. -/
def corrSub (r : RtSubscriber) (a : Subscriber) : Prop :=
  (Closed r → a.status = .shutDown ∧ a.registered = false ∧ a.observed = r.chunks.flatten) ∧
  (¬ Closed r → a = r.erase)

/-- The `Set` delete and the `Queue.fail` an overflow `resolve` performs (`Runtime.lean:209-210`). -/
def rtFail (e : SubError) (r : RtSubscriber) : RtSubscriber :=
  { r with registered := false, queue := r.queue.fail e }

def failOpt : Option SubError → RtSubscriber → RtSubscriber
  | none, r => r
  | some e, r => rtFail e r

/-- The failure a `check` has decided and the matching `resolve` has not yet performed. -/
def pendingFail (f : FanOut) (id : SubId) (r : RtSubscriber) : Option SubError :=
  match f.kind, f.decided with
  | .publish stream _ _, some (i, true) =>
    if i = id then some (.consumerLagged stream r.lastEnqueued) else none
  | _, _ => none

/-- The runtime subscriber as the abstract side already sees it. -/
def pendingOf (f : FanOut) (id : SubId) (r : RtSubscriber) : RtSubscriber :=
  failOpt (pendingFail f id r) r

/-- Correspondence at every subscriber — the quiescent case. -/
def CorrAll (s : RtState) (sA : SubState) : Prop :=
  ∀ id r, lookupRt s.subs id = some r → ∃ a, lookupSub sA.subs id = some a ∧ corrSub r a

/-- Correspondence of the subscribers the fan-out has not passed, against the pre-operation
abstract state. -/
def CorrPre (s : RtState) (f : FanOut) (sA : SubState) : Prop :=
  ∀ id r, lookupRt s.subs id = some r → pointPassed f id = false →
    ∃ a, lookupSub sA.subs id = some a ∧ corrSub r a

/-- … and of the subscribers it has passed, against the state after the owed operation and the
owed consumer labels. -/
def CorrPost (s : RtState) (f : FanOut) (sPost : SubState) : Prop :=
  ∀ id r, lookupRt s.subs id = some r → pointPassed f id = true →
    ∃ a, lookupSub sPost.subs id = some a ∧ corrSub (pendingOf f id r) a

/-! ## The fan-out's bookkeeping -/

/-- The owed suffix: consumer labels of subscribers past their point, in runtime order — applied
after the owed operation. -/
def OwedOk (f : FanOut) (owed : List Label) : Prop :=
  ∀ l ∈ owed, ∃ i, (l = .pull i ∨ l = .unsubscribe i) ∧ pointPassed f i = true

/-- A subscriber is visited once: nothing still scheduled has been visited. -/
def FanFresh (f : FanOut) : Prop :=
  ∀ id, Scheduled f id → f.visited.any (fun p => p.1 == id) = false

/-- The guard of `deliverOne` (`Next.lean:47`) / `endOne` (`:65`): would the owed operation act
on this abstract subscriber? -/
def isTargetOf : FanKind → Subscriber → Bool
  | .publish stream m _, a => a.stream == stream && a.registered && matchesAny a.filters m.subject
  | .delete name, a => a.stream == name && a.registered

/-- What the fan-out list means abstractly. A subscriber the fan-out has not passed is either
still scheduled or not a target of the owed operation at all (one-sided: a `closeA` can turn a
scheduled target into a non-target, which the runtime still visits and the abstract operation
skips — unobservably, since `closeStarted` freezes it); and everything still scheduled *is* a
target unless it has been shut down meanwhile, which is what makes the runtime's `check` and the
abstract `deliverOne` decide alike. -/
def RelPre (f : FanOut) (sA : SubState) : Prop :=
  ∀ id a, lookupSub sA.subs id = some a → pointPassed f id = false →
    (Scheduled f id ∨ isTargetOf f.kind a = false) ∧
    (Scheduled f id → a.status = .shutDown ∨ isTargetOf f.kind a = true)

/-- The owed operation's core step: the abstract core is what the runtime stored from. -/
def RelCore (f : FanOut) (sA : SubState) (s : RtState) : Prop :=
  (∀ stream m el, f.kind = .publish stream m el →
      step sA.core (.publish stream m.subject m.payload m.headers el m.timestampMillis)
        = .ok (s.core, .sequence m.sequence)) ∧
  (∀ name, f.kind = .delete name → step sA.core (.deleteStream name) = .ok (s.core, .unit))

/-! ## The relation -/

/-- The relation. `labels` is the matched abstract prefix; `owed` the suffix still to be applied.
Both sides have the same subscriber ids (they only grow at `register`, the same label on both
sides). Quiescent: `owed = []`, the abstract state `sA` erases to `s` subscriber by subscriber and
the cores agree. In flight: `sA` is the pre-operation abstract state; subscribers before their
point erase to it, subscribers past their point erase to the state after the owed operation and
the owed consumer labels. -/
def Rel (s : RtState) (labels owed : List Label) : Prop :=
  ∃ sA, runLabels initialSub labels = some sA ∧
    sA.nextId = s.nextId ∧
    sA.subs.map Prod.fst = s.subs.map Prod.fst ∧
    (s.fanOut = none → owed = [] ∧ sA.core = s.core ∧ CorrAll s sA) ∧
    (∀ f, s.fanOut = some f →
      FanFresh f ∧ RelPre f sA ∧ RelCore f sA s ∧ CorrPre s f sA ∧
      ∃ owedRest sPost, owed = owedOp f.kind :: owedRest ∧ OwedOk f owedRest ∧
        runLabels sA owed = some sPost ∧ CorrPost s f sPost)

/-- What the induction carries besides `Rel`: the histories. A subscriber past its point has the
history of the whole prefix including the owed suffix; one before it, the history of the matched
prefix alone. -/
def RelHist (s : RtState) (labels owed : List Label) : Prop :=
  ∀ id, (lookupRt s.subs id).isSome = true →
    (s.fanOut = none → abstractHistory labels id = some (rtHistory s id)) ∧
    (∀ f, s.fanOut = some f →
      (pointPassed f id = true → abstractHistory (labels ++ owed) id = some (rtHistory s id)) ∧
      (pointPassed f id = false → abstractHistory labels id = some (rtHistory s id)))

end EffectNatsSubstrate
