import EffectNatsSubstrate.RtTraces

/-!
# The stage-B1 statement: A4 as trace inclusion at quiescent points

What is preserved between the runtime model and stage A is **not** the global
order of visible events: in the §4.2 counterexample the runtime stores `m₂`
before subscriber 1 pulls, while the only stage-A placement with the same
histories has subscriber 1's pull *before* the publish. What is preserved — and
what the schema-2 harness checks — is the sequence of operations and
registrations (serialised by the permit on both sides), every subscriber's
chunk history, and the subscriber counts (stage-B slice document §2.3).

So the statement is trace inclusion at quiescent points (`A4Inclusion`): for
every runtime execution that ends with no fan-out in flight, some stage-A label
sequence has the same serial sequence, runs, gives every subscriber the same
chunk history, and leaves the same subscriber counts. A labelled weak
simulation in cslib's form was considered and set aside for the statement: the
abstract side has no internal steps, and one runtime step (`endFanOut`) must be
matched by the abstract publish *followed by the owed pulls* of subscribers the
fan-out had already visited — several abstract steps for one runtime step. The
proof is therefore a direct induction on the runtime execution carrying the
owed abstract suffix (increment 4 (i)); cslib's `IsSimulation`/`sim_trace`
(`Cslib/Foundations/Semantics/LTS/Simulation.lean` @ `2e1824a`) remain the
pattern, not a dependency.

Definitions only: the statement is the r4 candidate for SB4 (+ SB5 through the
bridge lemma the slice document names); nothing here is proved beyond the
kernel-checked instance on the §4.2 scenario.
-/

namespace EffectNatsSubstrate

/-! ## The serial sequence and the histories of an execution -/

/-- The operations and registrations of a runtime execution, in order — one
entry per permit-holding step. A publish or deletion is counted where it
starts (`op`); `endFanOut` carries no payload of its own, and no other
operation can start before it (`rtOp`/`rtRegister` are disabled while a
fan-out is in flight), so the order is the order of completions too. -/
def rtSerial : List RtLabel → List Label
  | [] => []
  | .op o e :: rest => .op o e :: rtSerial rest
  | .register stream opts l₀ id e :: rest => .register stream opts l₀ id e :: rtSerial rest
  | _ :: rest => rtSerial rest

def labelSerial : List Label → List Label
  | [] => []
  | .op o e :: rest => .op o e :: labelSerial rest
  | .register stream opts l₀ id e :: rest => .register stream opts l₀ id e :: labelSerial rest
  | _ :: rest => labelSerial rest

/-- The chunk history stage A gives `id` along a label sequence (`afterLabel`
records the registration prefix and each pull's chunk). `none` if a label is
disabled. -/
def abstractHistoryFrom (id : SubId) : SubState → History → List Label → Option History
  | _, h, [] => some h
  | s, h, l :: rest =>
    match apply s l with
    | some s' => abstractHistoryFrom id s' (afterLabel s s' id h l) rest
    | none => none

def abstractHistory (labels : List Label) (id : SubId) : Option History :=
  abstractHistoryFrom id initialSub [] labels

/-! ## The statement -/

/-- **A4 as trace inclusion at quiescent points** (stage-B slice document
§10, SB4; a Pass B candidate). Every runtime execution that ends with no
fan-out in flight is matched by a stage-A label sequence that runs, has the
same serial sequence, gives every registered subscriber the same chunk
history, and leaves every stream the same subscriber count. The witness has
the serial sequence with `pull` and `unsubscribe` labels inserted — that is
what `labelSerial labels = rtSerial rls` says. -/
def A4Inclusion : Prop :=
  ∀ (rls : List RtLabel) (s : RtState),
    runRtSteps initialRt rls = some s → s.fanOut = none →
    ∃ (labels : List Label) (sA : SubState),
      runLabels initialSub labels = some sA ∧
      labelSerial labels = rtSerial rls ∧
      (∀ id, (lookupRt s.subs id).isSome → abstractHistory labels id = some (rtHistory s id)) ∧
      (∀ stream, subscriberCount sA stream = subscriberCount (eraseRt s) stream)

/-- **Completeness of the acceptance sets for the runtime model** (SB5; a Pass
B candidate; **r4.1**). For a *valid* stage-A trace (`runLabels` accepts its
labels as written) without `unsubscribe` labels, every runtime execution with
the trace's serial sequence and no scope closures ends, at quiescence, with
each registered subscriber's chunk history in the set the exporter prints for
it (`historiesWith apply t id`, the enumeration behind `freeRunning.outcomes`).
This is the theorem the harness's free-running membership check rests on.
Scope closures and the one trace with `unsubscribe` labels (`sa-accounting`,
whose subscribers never pull) are outside it by hypothesis. The validity
hypothesis was missing in r4: `outcomesFrom` drops a placement at a disabled
label of *another* subscriber, so an invalid trace (a pull on an empty buffer)
has an empty acceptance set — `scripts/A4CompleteR4Refutation.lean` proves
`¬ A4CompleteR4` for the r4 form. -/
def A4Complete : Prop :=
  ∀ (t : SubTrace),
    (runLabels initialSub (t.steps.map (·.label))).isSome = true →
    t.steps.all (fun st => match st.label with | .unsubscribe _ => false | _ => true) = true →
    ∀ (rls : List RtLabel) (s : RtState),
      runRtSteps initialRt rls = some s → s.fanOut = none →
      rls.all (fun l => match l with | .closeA _ => false | .closeB _ => false | _ => true) = true →
      rtSerial rls = labelSerial (t.steps.map (·.label)) →
      ∀ id, id ∈ subIds t → (historiesWith apply t id).contains (rtHistory s id) = true

/-! ## The §4.2 instance, kernel-checked -/

namespace RtScenario

/-- The witness for the counterexample: `rightOrder` runs, has the runtime's
serial sequence, reproduces both chunk histories, and leaves the same count. -/
theorem counterexample_inclusion_witness :
    (match runLabels initialSub rightOrder with
      | some sA =>
        (labelSerial rightOrder == rtSerial counterexample.steps) &&
        (abstractHistory rightOrder 0 == some (rtHistory (finalRt counterexample) 0)) &&
        (abstractHistory rightOrder 1 == some (rtHistory (finalRt counterexample) 1)) &&
        (subscriberCount sA "KV_b" == subscriberCount (eraseRt (finalRt counterexample)) "KV_b")
      | none => false) = true := by
  decide

/-- And `wrongOrder` — the same serial sequence, the publish before subscriber
1's pull — is not a witness. -/
theorem counterexample_wrong_witness :
    ((labelSerial wrongOrder == rtSerial counterexample.steps) &&
     (abstractHistory wrongOrder 1 == some (rtHistory (finalRt counterexample) 1))) = false := by
  decide

end RtScenario

end EffectNatsSubstrate
