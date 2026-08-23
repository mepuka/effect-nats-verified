import EffectNatsSubstrate.RtTraces

/-!
# The stage-B1 statement: A4 as trace inclusion, and the simulation vocabulary

What is preserved between the runtime model and stage A is **not** the global
order of visible events: in the §4.2 counterexample the runtime stores `m₂`
before subscriber 1 pulls, while the only stage-A placement with the same
histories has subscriber 1's pull *before* the publish. What is preserved — and
what the schema-2 harness checks — is the sequence of operations and
registrations (serialised by the permit on both sides) together with every
subscriber's chunk history (stage-B slice document §2.3).

So the statement is trace inclusion at quiescent points (`A4Inclusion`): for
every runtime execution that ends with no fan-out in flight, some stage-A label
sequence has the same serial sequence, runs, and gives every subscriber the
same chunk history. The proof method will be a forward simulation whose
relation carries the abstract labels the abstract side still owes (the
counterexample shows a visited subscriber's pull must be placed after the
abstract publish, an unvisited one's before); the generic vocabulary below is
cslib's (`Cslib/Foundations/Semantics/LTS/{Basic,HasTau,Simulation}.lean` @
`2e1824a`, Apache-2.0), re-stated in core because the package has no
dependencies and core lacks `Relation.ReflTransGen`.

Definitions only: the statement is a Pass B candidate (`SB4`+`SB5`); nothing
here is proved beyond the kernel-checked instance on the §4.2 scenario.
-/

namespace EffectNatsSubstrate

/-! ## Generic: labelled transition systems and simulation (adapted from cslib) -/

structure LTS (State : Type) (Label : Type) where
  Tr : State → Label → State → Prop

/-- τ-closure (cslib `τSTr`, `HasTau.lean:32-33`). -/
inductive TauStar {S L : Type} (lts : LTS S L) (τ : L) : S → S → Prop where
  | refl {s : S} : TauStar lts τ s s
  | step {s s' s'' : S} : lts.Tr s τ s' → TauStar lts τ s' s'' → TauStar lts τ s s''

/-- Weak transition τ* μ τ* (cslib `STr`, `HasTau.lean:40-42`). -/
inductive WeakTr {S L : Type} (lts : LTS S L) (τ : L) : S → L → S → Prop where
  | refl {s : S} : WeakTr lts τ s τ s
  | tr {s₁ s₂ s₃ s₄ : S} {μ : L} :
      TauStar lts τ s₁ s₂ → lts.Tr s₂ μ s₃ → TauStar lts τ s₃ s₄ → WeakTr lts τ s₁ μ s₄

/-- cslib `saturate` (`HasTau.lean:46-47`). -/
def LTS.saturate {S L : Type} (lts : LTS S L) (τ : L) : LTS S L := ⟨WeakTr lts τ⟩

/-- cslib `IsSimulation` (`Simulation.lean:55-57`). -/
def IsSimulation {S₁ S₂ L : Type} (lts₁ : LTS S₁ L) (lts₂ : LTS S₂ L)
    (r : S₁ → S₂ → Prop) : Prop :=
  ∀ s₁ s₂, r s₁ s₂ → ∀ μ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂'

/-! ## The two systems as LTSs over the abstract label alphabet, with τ -/

/-- The runtime LTS: every `rtStep` is a transition; the label is the stage-A
label it realises, or `none` for an internal step. Visible: an operation that
completes in one step, a registration, `endFanOut` (the operation the fan-out
belongs to), a returning pull or wake, and the second half of a close. -/
def rtVisible (s : RtState) : RtLabel → Option Label
  | .op o e =>
    match s.fanOut, o, e with
    | _, .publish _ _ _ _ _ _, .ok _ => none
    | _, .deleteStream _, .ok _ => none
    | _, _, _ => some (.op o e)
  | .register stream opts l₀ id e => some (.register stream opts l₀ id e)
  | .check _ => none
  | .resolve _ => none
  | .endFanOut =>
    match s.fanOut with
    | some { kind := .publish stream m, .. } =>
      some (.op (.publish stream m.subject m.payload m.headers none m.timestampMillis)
               (.ok (.sequence m.sequence)))
    | some { kind := .delete name, .. } => some (.op (.deleteStream name) (.ok .unit))
    | none => none
  | .pull id =>
    match lookupRt s.subs id with
    | some r => if r.queue.status = .opened && r.queue.buffer.isEmpty then none else some (.pull id)
    | none => none
  | .wake id =>
    match lookupRt s.subs id with
    | some r => if r.queue.status = .shutDown then none else some (.pull id)
    | none => none
  | .closeA _ => none
  | .closeB id => some (.unsubscribe id)

def runtimeLTS : LTS RtState (Option Label) :=
  ⟨fun s μ s' => ∃ rl, rtStep s rl = some s' ∧ rtVisible s rl = μ⟩

/-- Stage A's LTS over the same alphabet (no internal steps of its own). -/
def abstractLTS : LTS SubState (Option Label) :=
  ⟨fun s μ s' => ∃ l, μ = some l ∧ apply s l = some s'⟩

/-! ## The serial sequence and the histories of an execution -/

/-- The operations and registrations of a runtime execution, in order — one
entry per permit-holding step. A publish or deletion is counted where it
starts (`op`), since `endFanOut` carries no payload of its own. -/
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
records the registration prefix and each pull's chunk). -/
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
§10, SB4 + SB5; a Pass B candidate). Every runtime execution that ends with no
fan-out in flight is matched by a stage-A label sequence with the same serial
sequence and the same chunk history for every registered subscriber. -/
def A4Inclusion : Prop :=
  ∀ (rls : List RtLabel) (s : RtState),
    runRtSteps initialRt rls = some s → s.fanOut = none →
    ∃ labels : List Label,
      (runLabels initialSub labels).isSome ∧
      labelSerial labels = rtSerial rls ∧
      ∀ id, (lookupRt s.subs id).isSome →
        abstractHistory labels id = some (rtHistory s id)

/-! ## The §4.2 instance, kernel-checked -/

namespace RtScenario

/-- The witness for the counterexample: `rightOrder` has the runtime's serial
sequence and reproduces both chunk histories. -/
theorem counterexample_inclusion_witness :
    ((runLabels initialSub rightOrder).isSome &&
     (labelSerial rightOrder == rtSerial counterexample.steps) &&
     (abstractHistory rightOrder 0 == some (rtHistory (finalRt counterexample) 0)) &&
     (abstractHistory rightOrder 1 == some (rtHistory (finalRt counterexample) 1))) = true := by
  decide

/-- And `wrongOrder` — the same serial sequence, the publish before subscriber
1's pull — is not a witness. -/
theorem counterexample_wrong_witness :
    ((labelSerial wrongOrder == rtSerial counterexample.steps) &&
     (abstractHistory wrongOrder 1 == some (rtHistory (finalRt counterexample) 1))) = false := by
  decide

end RtScenario

end EffectNatsSubstrate
