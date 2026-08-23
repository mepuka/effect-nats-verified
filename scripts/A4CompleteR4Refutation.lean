import EffectNatsSubstrate

/-!
# Refutation of `A4Complete` as frozen in snapshot r4

The r4 statement (`docs/signature-snapshot.md`, revision log r4.1) quantified over every
`t : SubTrace` without requiring `t` to be a valid stage-A trace. `outcomesFrom`
(`SubPlacements.lean`) drops a placement when a label of *another* subscriber is disabled, so a
trace in which subscriber 1 pulls on an empty open buffer has an empty acceptance set for
subscriber 0, while a runtime run with the same serial labels exists and is quiescent. Found by the
coordinator while drafting P5's enumeration-completeness helper (2026-08-23); r4.1 adds the
hypothesis `(runLabels initialSub (t.steps.map (·.label))).isSome = true`.

Not part of the library (not in the root import list); check it with
`lake env lean scripts/A4CompleteR4Refutation.lean` from the package directory. Standard axioms only
(`#print axioms` at the end).
-/

namespace EffectNatsSubstrate

/-- `A4Complete` exactly as frozen in r4 (`Sim.lean` at `2b0d88b`). -/
def A4CompleteR4 : Prop :=
  ∀ (t : SubTrace),
    t.steps.all (fun st => match st.label with | .unsubscribe _ => false | _ => true) = true →
    ∀ (rls : List RtLabel) (s : RtState),
      runRtSteps initialRt rls = some s → s.fanOut = none →
      rls.all (fun l => match l with | .closeA _ => false | .closeB _ => false | _ => true) = true →
      rtSerial rls = labelSerial (t.steps.map (·.label)) →
      ∀ id, id ∈ subIds t → (historiesWith apply t id).contains (rtHistory s id) = true

open SATrace in
/-- Two subscribers on an empty stream; subscriber 1's pull is disabled (open, empty buffer). -/
def badTrace : SubTrace :=
  { name := "r4-refutation-invalid-other-pull"
    mirrors := []
    steps :=
      [ create kvConfigRaw
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 2)) 0 0 [.caughtUp]
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 2)) 0 1 [.caughtUp]
      , pullE 1 [] ]
    finalObserved := [] }

open SATrace in
/-- The runtime run with the same serial labels, quiescent, without closes. -/
def badRun : List RtLabel :=
  [ .op (.createStream kvConfigRaw) (.ok .unit)
  , .register "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 2)) 0 0 (.ok .unit)
  , .register "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 2)) 0 1 (.ok .unit) ]

/-- The trace is not a valid stage-A trace — exactly what r4.1's new hypothesis excludes. -/
theorem badTrace_invalid : (runLabels initialSub (badTrace.steps.map (·.label))).isSome = false := by
  decide

theorem badPair_check :
    (match runRtSteps initialRt badRun with
      | some s => s.fanOut.isNone && !(historiesWith apply badTrace 0).contains (rtHistory s 0)
      | none => false) = true := by decide

theorem badTrace_noUnsub :
    badTrace.steps.all (fun st => match st.label with | .unsubscribe _ => false | _ => true) = true := by
  decide

theorem badRun_noClose :
    badRun.all (fun l => match l with | .closeA _ => false | .closeB _ => false | _ => true) = true := by
  decide

theorem badPair_serial : rtSerial badRun = labelSerial (badTrace.steps.map (·.label)) := by decide

theorem badTrace_sub0 : 0 ∈ subIds badTrace := by decide

theorem a4CompleteR4_false : ¬ A4CompleteR4 := by
  intro h
  have hc := badPair_check
  revert hc
  cases hs : runRtSteps initialRt badRun with
  | none => simp
  | some s =>
    intro hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hc
    have := h badTrace badTrace_noUnsub badRun s hs hc.1 badRun_noClose badPair_serial 0 badTrace_sub0
    rw [this] at hc
    exact Bool.noConfusion hc.2

end EffectNatsSubstrate

#print axioms EffectNatsSubstrate.a4CompleteR4_false
