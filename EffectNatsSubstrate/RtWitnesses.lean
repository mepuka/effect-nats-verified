import EffectNatsSubstrate.SimAgree
import EffectNatsSubstrate.Sim
import EffectNatsSubstrate.RtCommute

/-!
# Non-vacuity witnesses for the stage-B1 frozen statements (proof map P6a)

Every frozen stage-B1 statement with hypotheses gets a kernel-checked concrete
instance where the hypotheses hold and the conclusion would not be trivial,
and every `decide`d "all traces" list gets a length guard against the empty
list. These are the facts the B1 assurance review cites for the "statement
non-vacuity" axis. The SB2 witnesses were added once P3 landed `bindStep`
(packet P6b): they close the file below `a4inclusion_witness`.
-/

namespace EffectNatsSubstrate

open RtScenario

/-- The exporter's stage-A list is not empty, so the trace theorems over
`allSubTraces` are never vacuous. -/
theorem allSubTraces_count : allSubTraces.length = 9 := by decide

/-- Likewise for stage B1's four scenarios. -/
theorem allRtTraces_count : allRtTraces.length = 4 := by decide

/-- An open queue holding one message under capacity 2: every SB1 law's
hypotheses are satisfiable (its conclusion is exercised on this queue too). -/
def wq : EffectQueue :=
  { buffer := [SATrace.msg "$KV.b.k" 1 "v1" 1], status := .opened, taker := false }

theorem sb1_witness :
    (decide (wq.status = .opened) && !wq.buffer.isEmpty && decide (wq.buffer.length < 2)
      && decide (wq.takeAll ≠ (wq, .parked))
      && decide (wq.offer 2 (SATrace.msg "$KV.b.k" 2 "v2" 2) ≠ (wq, .refused))
      && decide (wq.size = 1)) = true := by decide

/-- The §4.2 run just after its second publish opened the fan-out (remaining
`[0, 1]`). -/
def midFanOut : Option RtState :=
  runRtSteps initialRt
    [ create, reg 0 1, reg 1 1
    , pub "v1" 1, .check 0, .resolve 0, .check 1, .resolve 1, .endFanOut
    , pub "v2" 2 ]

/-- A reachable runtime state with a fan-out in flight *and* a non-empty
buffer exists, so SB3 (`rtInv_reachable`) and SB7 (`pending_le_capacity_rt`)
have something to say. -/
theorem sb3_witness :
    (match midFanOut with
      | some s => s.fanOut.isSome && s.subs.any (fun p => !p.2.queue.buffer.isEmpty)
      | none => false) = true := by decide

/-- `A4Complete` (r4.1) is not vacuous: `abstract42` is a valid trace without
unsubscribe labels, the §4.2 run realises its serial sequence, ends quiescent
without scope closures, and both acceptance sets hold at least two histories. -/
theorem a4complete_witness :
    ((runLabels initialSub (abstract42.steps.map (·.label))).isSome
      && abstract42.steps.all (fun st => match st.label with | .unsubscribe _ => false | _ => true)
      && (runRtSteps initialRt counterexample.steps).isSome
      && (match runRtSteps initialRt counterexample.steps with
          | some s => s.fanOut.isNone | none => false)
      && counterexample.steps.all (fun l => match l with | .closeA _ => false | .closeB _ => false | _ => true)
      && decide (rtSerial counterexample.steps = labelSerial (abstract42.steps.map (·.label)))
      && decide (2 ≤ (historiesWith apply abstract42 0).eraseDups.length)
      && decide (2 ≤ (historiesWith apply abstract42 1).eraseDups.length)) = true := by decide

/-- `A4Inclusion` has a witness to produce: the §4.2 run ends quiescent with
two registered subscribers. -/
theorem a4inclusion_witness :
    (match runRtSteps initialRt counterexample.steps with
      | some s => s.fanOut.isNone && decide (s.subs.length = 2)
      | none => false) = true := by decide

/-- SB2 is not vacuous: at `midFanOut` (fan-out in flight, remaining `[0, 1]`), subscriber 1's pull and
the fan-out's `check 0` are both enabled in either order and the orders agree. -/
theorem sb2_witness :
    (match midFanOut with
      | some s => (bindStep s (.pull 1) (.check 0)).isSome && (bindStep s (.check 0) (.pull 1)).isSome
                  && decide (bindStep s (.pull 1) (.check 0) = bindStep s (.check 0) (.pull 1))
      | none => false) = true := by decide

/-- The §4.2 run after subscriber 0's decision: the fan-out's next check is subscriber 1's. -/
def midFanOut1 : Option RtState :=
  runRtSteps initialRt
    [ create, reg 0 1, reg 1 1
    , pub "v1" 1, .check 0, .resolve 0, .check 1, .resolve 1, .endFanOut
    , pub "v2" 2, .check 0, .resolve 0 ]

/-- SB2's `i ≠ j` is load-bearing: the *same* subscriber's pull and check do not commute — pulling
before the check empties the buffer and the check admits; checking first sees the full buffer and
decides overflow. This is the §4.2 counterexample at the level of two labels. -/
theorem sb2_same_subscriber_noncommuting :
    (match midFanOut1 with
      | some s => (bindStep s (.pull 1) (.check 1)).isSome && (bindStep s (.check 1) (.pull 1)).isSome
                  && decide (bindStep s (.pull 1) (.check 1) ≠ bindStep s (.check 1) (.pull 1))
      | none => false) = true := by decide


end EffectNatsSubstrate
