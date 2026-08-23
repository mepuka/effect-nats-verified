import EffectNatsSubstrate.Runtime

/-!
# Runtime traces — the stage-B1 scenarios, kernel-checked

The scenarios of the stage-B slice document §4.1 (the three A4 cases) and §4.2
(the counterexample to "the publish linearizes when the message is stored") as
`RtTrace` values run by `decide`. For each, the runtime chunk histories are
checked to be in the stage-A acceptance set of the corresponding abstract trace
(`SubPlacements.historiesWith apply`), which is what the stage-B simulation
will establish for every runtime execution. The wrong linearization is
falsified on §4.2: placing the abstract publish before the mid-fan-out pull
gives subscriber 1 a different `observed`.
-/

namespace EffectNatsSubstrate

structure RtTrace where
  name : String
  steps : List RtLabel
  finalHistories : List (SubId × History)
  deriving Repr

def runRtSteps : RtState → List RtLabel → Option RtState
  | s, [] => some s
  | s, l :: rest =>
    match rtStep s l with
    | some s' => runRtSteps s' rest
    | none => none

def finalRt (t : RtTrace) : RtState := (runRtSteps initialRt t.steps).getD initialRt

def checkHistories (s : RtState) : List (SubId × History) → Bool
  | [] => true
  | (id, h) :: rest => (rtHistory s id == h) && checkHistories s rest

def runRtTrace (t : RtTrace) : Bool :=
  match runRtSteps initialRt t.steps with
  | some s => checkHistories s t.finalHistories
  | none => false

/-- Fold stage A's `apply` over a label list (no inserted pulls). -/
def runLabels : SubState → List Label → Option SubState
  | s, [] => some s
  | s, l :: rest =>
    match apply s l with
    | some s' => runLabels s' rest
    | none => none

namespace RtScenario

open SATrace

def create : RtLabel := .op (.createStream kvConfigRaw) (.ok .unit)

def pub (payload : String) (seq : StreamSeq) : RtLabel :=
  .op (.publish "KV_b" "$KV.b.k" payload [] none seq) (.ok (.sequence seq))

def reg (id : SubId) (cap : Nat) : RtLabel :=
  .register "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag cap)) 0 id (.ok .unit)

def m (payload : String) (seq : StreamSeq) : StoredMessage := msg "$KV.b.k" seq payload seq

/-- The abstract counterparts, for the acceptance sets (pulls are inserted by
the enumeration, so none are listed). -/
def aCreate : SubTraceStep := SATrace.create kvConfigRaw
def aPub (payload : String) (seq : StreamSeq) : SubTraceStep := SATrace.pub "KV_b" "$KV.b.k" payload seq seq
def aReg (id : SubId) (cap : Nat) : SubTraceStep :=
  SATrace.reg "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag cap)) 0 id []

/-- A full publish fan-out to one subscriber, uninterrupted. -/
def fanOut1 (id : SubId) : List RtLabel := [.check id, .resolve id, .endFanOut]

/-! ## §4.1, case 1: the pull lands before `check`. -/

def caseBefore : RtTrace :=
  { name := "rt-pull-before-check"
    steps :=
      [ create, reg 0 1
      , pub "v1" 1 ] ++ fanOut1 0 ++
      [ pub "v2" 2, .pull 0, .check 0, .resolve 0, .endFanOut, .pull 0 ]
    finalHistories := [ (0, [[.caughtUp], [.entry (m "v1" 1)], [.entry (m "v2" 2)]]) ] }

theorem rt_before_trace : runRtTrace caseBefore = true := by decide

/-! ## §4.1, case 2: the pull lands between `check` (overflow) and `fail`. -/

def caseBetween : RtTrace :=
  { name := "rt-pull-between-check-and-fail"
    steps :=
      [ create, reg 0 1
      , pub "v1" 1 ] ++ fanOut1 0 ++
      [ pub "v2" 2, .check 0, .pull 0, .resolve 0, .endFanOut, .pull 0 ]
    finalHistories :=
      [ (0, [[.caughtUp], [.entry (m "v1" 1)], [.failed (.consumerLagged "KV_b" 1)]]) ] }

theorem rt_between_trace : runRtTrace caseBetween = true := by decide

/-! ## §4.1, case 3: the pull lands after `offer` (capacity 2 so `v2` is admitted). -/

def caseAfter : RtTrace :=
  { name := "rt-pull-after-offer"
    steps :=
      [ create, reg 0 2
      , pub "v1" 1 ] ++ fanOut1 0 ++
      [ pub "v2" 2, .check 0, .resolve 0, .endFanOut, .pull 0 ]
    finalHistories := [ (0, [[.caughtUp], [.entry (m "v1" 1), .entry (m "v2" 2)]]) ] }

theorem rt_after_trace : runRtTrace caseAfter = true := by decide

/-! ## §4.2: two full subscribers; subscriber 1 pulls after the fan-out failed
subscriber 0 and before it reached subscriber 1. -/

def counterexample : RtTrace :=
  { name := "rt-linearization-counterexample"
    steps :=
      [ create, reg 0 1, reg 1 1
      , pub "v1" 1, .check 0, .resolve 0, .check 1, .resolve 1, .endFanOut
      , pub "v2" 2, .check 0, .resolve 0, .pull 1, .check 1, .resolve 1, .endFanOut
      , .pull 0, .pull 0, .pull 1 ]
    finalHistories :=
      [ (0, [[.caughtUp], [.entry (m "v1" 1)], [.failed (.consumerLagged "KV_b" 1)]])
      , (1, [[.caughtUp], [.entry (m "v1" 1)], [.entry (m "v2" 2)]]) ] }

theorem rt_counterexample_trace : runRtTrace counterexample = true := by decide

/-- The abstract trace of §4.2 without pulls; the enumeration places them. -/
def abstract42 : SubTrace :=
  { name := "sa-linearization-counterexample", mirrors := []
    steps := [ aCreate, aReg 0 1, aReg 1 1, aPub "v1" 1, aPub "v2" 2 ]
    finalObserved := [] }

/-- Every runtime history of §4.2 is one the stage-A model admits. -/
theorem rt_counterexample_admitted :
    ((historiesWith apply abstract42 0).contains (rtHistory (finalRt counterexample) 0) &&
     (historiesWith apply abstract42 1).contains (rtHistory (finalRt counterexample) 1)) = true := by
  decide

/-- The wrong linearization — the abstract publish taken before subscriber 1's
pull — makes subscriber 1 overflow, which the runtime did not. -/
def wrongOrder : List Label :=
  [ aCreate.label, (aReg 0 1).label, (aReg 1 1).label, (aPub "v1" 1).label, (aPub "v2" 2).label
  , .pull 1, .pull 1 ]

theorem wrong_linearization_differs :
    (match runLabels initialSub wrongOrder with
      | some s => observedOf s 1 == (rtHistory (finalRt counterexample) 1).flatten
      | none => true) = false := by
  decide

/-- The right one: subscriber 1's pull before the abstract publish. -/
def rightOrder : List Label :=
  [ aCreate.label, (aReg 0 1).label, (aReg 1 1).label, (aPub "v1" 1).label
  , .pull 1, (aPub "v2" 2).label, .pull 0, .pull 0, .pull 1 ]

theorem right_linearization_agrees :
    (match runLabels initialSub rightOrder with
      | some s => (observedOf s 0 == (rtHistory (finalRt counterexample) 0).flatten) &&
                  (observedOf s 1 == (rtHistory (finalRt counterexample) 1).flatten)
      | none => false) = true := by
  decide

/-- The three §4.1 runtime histories are admitted by their abstract traces. -/
def abstract1 (cap : Nat) : SubTrace :=
  { name := "sa-one-subscriber", mirrors := []
    steps := [ aCreate, aReg 0 cap, aPub "v1" 1, aPub "v2" 2 ], finalObserved := [] }

theorem rt_cases_admitted :
    ((historiesWith apply (abstract1 1) 0).contains (rtHistory (finalRt caseBefore) 0) &&
     (historiesWith apply (abstract1 1) 0).contains (rtHistory (finalRt caseBetween) 0) &&
     (historiesWith apply (abstract1 2) 0).contains (rtHistory (finalRt caseAfter) 0)) = true := by
  decide

end RtScenario

/-- Every B1 scenario, for the exporter and the gate. -/
def allRtTraces : List RtTrace :=
  [ RtScenario.caseBefore, RtScenario.caseBetween, RtScenario.caseAfter, RtScenario.counterexample ]

theorem all_rt_traces : allRtTraces.all runRtTrace = true := by decide

end EffectNatsSubstrate
