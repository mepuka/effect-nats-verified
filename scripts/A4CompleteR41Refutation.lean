import EffectNatsSubstrate

/-!
# Refutation of `A4Complete` as frozen in snapshot r4.1

The r4.1 statement (`Sim.lean`; snapshot revision log r4.1) concludes for **every**
`id ∈ subIds t`. `subIds` collects the id of *every* `register` label of the trace, including one
that reports `StreamNotFound` and creates no subscriber. For such an id the two sides disagree by
construction:

- the abstract side starts `id`'s chunk history at the register label whatever its outcome —
  `afterLabel` (`SubPlacements.lean:60`) is `if i = id then [observedOf after id] else h`, and
  `observedOf` of an absent subscriber is `[]`, so the history is `[[]]`;
- the runtime side has no subscriber, and `rtHistory` (`Runtime.lean:100-103`) is `[]` for an
  absent one.

So the acceptance set is `[[[]]]` and the runtime history is `[]`: `List.contains` is `false`.
`A4Inclusion` does not have this hole because its history conjunct is guarded by
`(lookupRt s.subs id).isSome`; `A4Complete` has no such guard.

Found by the P5c lane while locking the target of packet P5c (2026-08-23), before any proof work.
The repair is r4.2: the guard `A4Inclusion` already carries, `(lookupRt s.subs id).isSome = true`.

Not part of the library (not in the root import list); check it with
`lake env lean scripts/A4CompleteR41Refutation.lean` from the package directory. Standard axioms
only (`#print axioms` at the end).
-/

namespace EffectNatsSubstrate

namespace R41Refutation

/-- `A4Complete` exactly as frozen in r4.1 (`Sim.lean` at `2e20ee7`, before the r4.2 guard). -/
def A4CompleteR41 : Prop :=
  ∀ (t : SubTrace),
    (runLabels initialSub (t.steps.map (·.label))).isSome = true →
    t.steps.all (fun st => match st.label with | .unsubscribe _ => false | _ => true) = true →
    ∀ (rls : List RtLabel) (s : RtState),
      runRtSteps initialRt rls = some s → s.fanOut = none →
      rls.all (fun l => match l with | .closeA _ => false | .closeB _ => false | _ => true) = true →
      rtSerial rls = labelSerial (t.steps.map (·.label)) →
      ∀ id, id ∈ subIds t → (historiesWith apply t id).contains (rtHistory s id) = true

def badOpts : ConsumeOptions :=
  { filters := ["$KV.b.>"], start := .newOnly, buffer := .terminateOnLag 2 }

/-- A registration that reports `StreamNotFound`: a valid stage-A label that creates nothing. -/
def badLabel : Label := .register "KV_b" badOpts 0 0 (.error (.streamNotFound "KV_b"))

/-- One step: the failed registration of subscriber `0`. -/
def badTrace : SubTrace :=
  { name := "r41-refutation-failed-registration"
    mirrors := []
    steps := [{ label := badLabel }]
    finalObserved := [] }

/-- The runtime run with the same serial labels: quiescent, without closes. -/
def badRun : List RtLabel := [.register "KV_b" badOpts 0 0 (.error (.streamNotFound "KV_b"))]

/-- Every hypothesis of `A4Complete` holds — including r4.1's validity hypothesis. -/
theorem badTrace_valid :
    (runLabels initialSub (badTrace.steps.map (·.label))).isSome = true := by decide

theorem badTrace_noUnsub :
    badTrace.steps.all (fun st => match st.label with | .unsubscribe _ => false | _ => true)
      = true := by decide

theorem badRun_noClose :
    badRun.all (fun l => match l with | .closeA _ => false | .closeB _ => false | _ => true)
      = true := by decide

theorem badPair_serial : rtSerial badRun = labelSerial (badTrace.steps.map (·.label)) := by decide

theorem badTrace_sub0 : 0 ∈ subIds badTrace := by decide

/-- … and the conclusion fails: the acceptance set is `[[[]]]`, the runtime history is `[]`. -/
theorem badPair_check :
    (match runRtSteps initialRt badRun with
      | some s => s.fanOut.isNone && !(historiesWith apply badTrace 0).contains (rtHistory s 0)
      | none => false) = true := by decide

/-- The runtime subscriber the conclusion is about does not exist — this is exactly the case
`A4Inclusion` excludes with `(lookupRt s.subs id).isSome`. -/
theorem badPair_absent :
    (match runRtSteps initialRt badRun with
      | some s => (lookupRt s.subs 0).isSome
      | none => true) = false := by decide

theorem a4CompleteR41_false : ¬ A4CompleteR41 := by
  intro h
  have hc := badPair_check
  revert hc
  cases hs : runRtSteps initialRt badRun with
  | none => simp
  | some s =>
    intro hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hc
    have hmem := h badTrace badTrace_valid badTrace_noUnsub badRun s hs hc.1 badRun_noClose
      badPair_serial 0 badTrace_sub0
    rw [hmem] at hc
    exact Bool.noConfusion hc.2

end R41Refutation

end EffectNatsSubstrate

#print axioms EffectNatsSubstrate.R41Refutation.a4CompleteR41_false
