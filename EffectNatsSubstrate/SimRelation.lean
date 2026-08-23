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

**`closeA` is `unsubscribe`**, matched immediately whichever side of a fan-out it lands on: the
`Set` delete is what `subscriberCount` sees, and `closeStarted` freezes the subscriber's history
on both sides (the runtime disables its pulls; the abstract subscriber is `shutDown`).
-/

namespace EffectNatsSubstrate

/-- The abstract publish/deletion of the fan-out in flight has already been applied to `id`. -/
def pointPassed (f : FanOut) (id : SubId) : Bool :=
  f.visited.any (fun p => p.1 == id) || (f.decided == some (id, true))

/-- The abstract label a fan-out in flight owes. -/
def owedOp : FanKind → Label
  | .publish stream m expectedLast =>
    .op (.publish stream m.subject m.payload m.headers expectedLast m.timestampMillis)
        (.ok (.sequence m.sequence))
  | .delete name => .op (.deleteStream name) (.ok .unit)

/-- One subscriber's correspondence. A subscriber whose scope is closing, or whose queue is
shut down, is only required to agree on what `A4Inclusion` reads — its chunk history and its
de-registration — because nothing can be observed from it any more (the runtime queue may still
hold a buffer, E5). Every other subscriber erases exactly. -/
def corrSub (r : RtSubscriber) (a : Subscriber) : Prop :=
  if r.closeStarted || r.queue.status = .shutDown then
    a.status = .shutDown ∧ a.registered = false ∧ a.observed = r.chunks.flatten
  else
    a = r.erase

/-- Correspondence of every subscriber of `s` against an abstract state `sA`, for the
subscribers selected by `sel` (the others are related to a different abstract state). -/
def corrOn (s : RtState) (sA : SubState) (sel : SubId → Bool) : Prop :=
  ∀ id r, lookupRt s.subs id = some r → sel id = true →
    ∃ a, lookupSub sA.subs id = some a ∧ corrSub r a

/-- The owed suffix: the consumer labels (pulls, unsubscribes) of subscribers past their point,
in runtime order — applied after the owed operation. -/
def OwedOk (f : FanOut) (owed : List Label) : Prop :=
  ∀ l ∈ owed, match l with
    | .pull i => pointPassed f i = true
    | .unsubscribe i => pointPassed f i = true
    | _ => False

/-- The relation. `labels` is the matched abstract prefix; `owed` the suffix still to be applied.
Quiescent: `owed = []`, the abstract state `sA` erases to `s` subscriber by subscriber and the
cores agree. In flight: `sA` is the pre-operation abstract state — its core is what the runtime
stored from, subscribers before their point erase to it, subscribers past their point erase to
the state after the owed operation and their owed labels, and the fan-out's lists cover exactly
the abstract operation's targets. -/
def Rel (s : RtState) (labels owed : List Label) : Prop :=
  ∃ sA, runLabels initialSub labels = some sA ∧
    sA.nextId = s.nextId ∧
    match s.fanOut with
    | none =>
      owed = [] ∧ sA.core = s.core ∧ corrOn s sA (fun _ => true)
    | some f =>
      (∃ owedRest, owed = owedOp f.kind :: owedRest ∧ OwedOk f owedRest ∧
        ∃ sPost, runLabels sA owed = some sPost ∧
          corrOn s sA (fun id => !pointPassed f id) ∧
          corrOn s sPost (fun id => pointPassed f id)) ∧
      (match f.kind with
        | .publish stream m el =>
          step sA.core (.publish stream m.subject m.payload m.headers el m.timestampMillis)
            = .ok (s.core, .sequence m.sequence)
        | .delete name => step sA.core (.deleteStream name) = .ok (s.core, .unit))

/-- What the induction carries besides `Rel`: the serial bookkeeping and the histories. -/
def RelHist (s : RtState) (labels owed : List Label) : Prop :=
  ∀ id, (lookupRt s.subs id).isSome →
    match s.fanOut with
    | none => abstractHistory labels id = some (rtHistory s id)
    | some f =>
      if pointPassed f id then abstractHistory (labels ++ owed) id = some (rtHistory s id)
      else abstractHistory labels id = some (rtHistory s id)

end EffectNatsSubstrate
