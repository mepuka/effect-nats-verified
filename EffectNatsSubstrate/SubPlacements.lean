import EffectNatsSubstrate.SubTraces

/-!
# Pull placements — the free-running acceptance sets (slice document §14, decision P1)

The stage-A traces fix where each `pull` happens. A free-running consumer pulls
whenever it is scheduled, so the harness that attacks assumption A4 (slice
document §2.4) needs, per subscriber, the set of consumer histories the model
admits over *every* placement of that subscriber's pulls: the trace's own
`pull` labels for that subscriber removed, then zero or more pulls inserted at
every gap between whole labels and after the last, each while `pullStep` is
enabled (a drain, then the trailing `failed` once a subscriber is `done` — at
most two in a row, hence the fuel).

A history is the consumer's chunks: the registration prefix, then one chunk per
pull. Final `observed` lists would not do — W1 (one-element pull) reaches final
lists on `sa-drain` that the model also reaches, while its chunk history does
not (`w1_outside_outcomes`).

Conventions shared with the harness (§14): an `unsubscribe` of a subscriber
that has already finished is a no-op, not a disabled step; the other labels run
through `apply` only — `events` and `counts` are placement-specific.

Assumption named in §14 (a theorem candidate for the next snapshot revision):
enumerating one subscriber's pulls with every other label fixed is sound
because no transition reads another subscriber's state and no label's
enabledness does (`Next.lean`).

Everything here is computed by structural recursion so the kernel can evaluate
it (`decide`); the exporter prints `placementsOf` as `freeRunning.outcomes`.
-/

namespace EffectNatsSubstrate

/-- A consumer history: the registration prefix, then one chunk per pull. -/
abbrev History := List (List Observed)

/-- The events a transition appended to `id`'s `observed`. -/
def appended (before after : SubState) (id : SubId) : List Observed :=
  (observedOf after id).drop (observedOf before id).length

/-- Up to `fuel` further pulls of `id` at the current gap; `k` continues from
each intermediate state (including the one with no pull). -/
def pullsAtGap (applyFn : SubState → Label → Option SubState) (id : SubId) :
    Nat → SubState → History → (SubState → History → List History) → List History
  | 0, s, h, k => k s h
  | fuel + 1, s, h, k =>
    k s h ++
      match applyFn s (.pull id) with
      | some s' => pullsAtGap applyFn id fuel s' (h ++ [appended s s' id]) k
      | none => []

/-- The history after a label as written: a registration of `id` starts the
history with the replay prefix; a pull of `id` appends its chunk. -/
def afterLabel (before after : SubState) (id : SubId) (h : History) : Label → History
  | .register _ _ _ i _ => if i = id then [observedOf after id] else h
  | .pull i => if i = id then h ++ [appended before after id] else h
  | _ => h

/-- Every history of `id` over the labels, with up to two pulls of `id` inserted
at every gap and after the last label; the labels themselves are applied as
written. -/
def historiesFrom (applyFn : SubState → Label → Option SubState) (id : SubId) :
    SubState → History → List Label → List History
  | s, h, [] => pullsAtGap applyFn id 2 s h (fun _ h' => [h'])
  | s, h, l :: rest =>
    pullsAtGap applyFn id 2 s h (fun s' h' =>
      match applyFn s' l with
      | some s'' => historiesFrom applyFn id s'' (afterLabel s' s'' id h' l) rest
      | none =>
        match l with
        | .unsubscribe i => if i = id then historiesFrom applyFn id s' h' rest else []
        | _ => [])

/-- The subscribers a trace registers, in registration order. -/
def subIds (t : SubTrace) : List SubId :=
  t.steps.filterMap (fun st =>
    match st.label with
    | .register _ _ _ i _ => some i
    | _ => none)

/-- The labels of a trace without `id`'s own pulls. -/
def labelsWithoutPulls (t : SubTrace) (id : SubId) : List Label :=
  (t.steps.map (·.label)).filter (fun l => l ≠ .pull id)

/-- All histories (with repeats) of `id` under a given model. -/
def historiesWith (applyFn : SubState → Label → Option SubState) (t : SubTrace) (id : SubId) :
    List History :=
  historiesFrom applyFn id initialSub [] (labelsWithoutPulls t id)

/-- The acceptance set of the stage-A model, without repeats — what the
exporter prints. -/
def placementsOf (t : SubTrace) (id : SubId) : List History :=
  (historiesWith apply t id).eraseDups

/-- The gated history a trace records for `id`: the `events` of its
registration and of each of its pulls, in order — what the gated harness mode
checks label by label. -/
def gatedHistory (t : SubTrace) (id : SubId) : History :=
  t.steps.filterMap (fun st =>
    match st.label with
    | .register _ _ _ i _ => if i = id then some st.events else none
    | .pull i => if i = id then some st.events else none
    | _ => none)

/-- Every trace's gated history is one of its own free-running outcomes. -/
theorem gated_in_outcomes :
    allSubTraces.all (fun t =>
      (subIds t).all (fun id => (historiesWith apply t id).contains (gatedHistory t id))) = true := by
  decide

/-- The acceptance set discriminates the wrong models: W1 (one-element pull)
admits a history on `sa-drain` that the model does not … -/
theorem w1_outside_outcomes :
    (historiesWith (applyWith deliverOne pullStepW1) saDrain 0).any
      (fun h => !(historiesWith apply saDrain 0).contains h) = true := by
  decide

/-- … and W2 (`lastEnqueued` advanced on the overflowing message) admits one on
`sa-lag`. -/
theorem w2_outside_outcomes :
    (historiesWith (applyWith deliverOneW2 pullStep) saLag 0).any
      (fun h => !(historiesWith apply saLag 0).contains h) = true := by
  decide

end EffectNatsSubstrate
