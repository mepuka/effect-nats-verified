import EffectNatsSubstrate.Next

/-!
# Stage-A traces — subscriber histories as data

A subscriber trace is a list of labels, each with the consumer-visible events
the label must produce for its subscriber (`register`: the replay entries then
`CaughtUp`; `pull`: the drained suffix) and the `subscriberCount` values to
check afterwards, plus the final `observed` lists. `runSubTraceWith` folds a
given `apply` over the labels; `runSubTrace` uses the model, `runSubTraceW1`
and `runSubTraceW2` the two deliberately wrong models of the slice document §7
(one-element pull; `lastEnqueued` advanced on the overflowing message). Every
trace below is kernel-checked with `decide`; the same data will be printed by
the exporter as schema-2 fixtures (slice document §14).

Traces mirror the conformance cases at effect-nats `872bd7f`
(`test/JetStreamConformance.ts`: C7 `:168`, C8 `:195`, C9 `:245`, C10 `:261`,
C13 `:336`, C14 `:373`, C15 `:431`; `test/JetStreamMemory.test.ts`: M1 `:36`).
Pull placements are explicit; where the conformance suite drains "as fast as
scheduled", the trace places one pull per delivered batch.
-/

namespace EffectNatsSubstrate

structure SubTraceStep where
  label : Label
  /-- For `register`/`pull`: the suffix appended to the subscriber's `observed`. -/
  events : List Observed := []
  /-- `subscriberCount` checks after the label. -/
  counts : List (StreamName × Nat) := []
  deriving Repr

structure SubTrace where
  name : String
  /-- Conformance cases the trace mirrors — metadata, unread by the runner. -/
  mirrors : List String
  steps : List SubTraceStep
  finalObserved : List (SubId × List Observed)
  deriving Repr

def labelSub : Label → Option SubId
  | .register _ _ _ id _ => some id
  | .pull id => some id
  | _ => none

def observedOf (s : SubState) (id : SubId) : List Observed :=
  match lookupSub s.subs id with
  | some sub => sub.observed
  | none => []

def checkCounts (s : SubState) : List (StreamName × Nat) → Bool
  | [] => true
  | (stream, n) :: rest => (subscriberCount s stream == n) && checkCounts s rest

def checkEvents (before after : SubState) (t : SubTraceStep) : Bool :=
  match labelSub t.label with
  | some id => observedOf after id == observedOf before id ++ t.events
  | none => t.events.isEmpty

def runSubStepsWith (applyFn : SubState → Label → Option SubState) :
    SubState → List SubTraceStep → Option SubState
  | s, [] => some s
  | s, t :: rest =>
    match applyFn s t.label with
    | none => none
    | some s' =>
      if checkEvents s s' t && checkCounts s' t.counts then runSubStepsWith applyFn s' rest
      else none

def checkFinal (s : SubState) : List (SubId × List Observed) → Bool
  | [] => true
  | (id, obs) :: rest => (observedOf s id == obs) && checkFinal s rest

def runSubTraceWith (applyFn : SubState → Label → Option SubState) (t : SubTrace) : Bool :=
  match runSubStepsWith applyFn initialSub t.steps with
  | some s => checkFinal s t.finalObserved
  | none => false

def runSubTrace : SubTrace → Bool := runSubTraceWith apply

/-! ## The two deliberately wrong models (slice document §7) -/

/-- W1: a pull removes one element instead of draining the buffer. -/
def pullStepW1 (sub : Subscriber) : Option Subscriber :=
  match sub.status, sub.pending with
  | .shutDown, _ => none
  | .done e, _ => some { sub with observed := sub.observed ++ [.failed e], status := .shutDown }
  | .opened, [] => none
  | .opened, m :: rest => some { sub with observed := sub.observed ++ [.entry m], pending := rest }
  | .closing _, [] => none
  | .closing e, m :: rest =>
    some { sub with
             observed := sub.observed ++ [.entry m]
             pending := rest
             status := if rest.isEmpty then .done e else .closing e }

def runSubTraceW1 : SubTrace → Bool := runSubTraceWith (applyWith deliverOne pullStepW1)

/-- W2: the overflowing message advances `lastEnqueued` before the failure is
recorded. -/
def deliverOneW2 (stream : StreamName) (m : StoredMessage) (sub : Subscriber) : Subscriber :=
  if sub.stream == stream && sub.registered && matchesAny sub.filters m.subject then
    match sub.policy with
    | .terminateOnLag n =>
      if n ≤ sub.pending.length then
        { sub with
            registered := false
            lastEnqueued := m.sequence
            status :=
              if sub.pending.isEmpty then .done (.consumerLagged stream m.sequence)
              else .closing (.consumerLagged stream m.sequence) }
      else if sub.status = .opened then
        { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence }
      else
        { sub with lastEnqueued := m.sequence }
  else sub

def runSubTraceW2 : SubTrace → Bool := runSubTraceWith (applyWith deliverOneW2 pullStep)

/-! ## Helpers for the traces -/

def roomy : Policy := .terminateOnLag 4096

def opts (filters : List SubjectName) (start : StartPosition) (buffer : Policy := roomy) :
    ConsumeOptions :=
  { filters := filters, start := start, buffer := buffer }

def msg (subject : SubjectName) (seq : StreamSeq) (payload : PayloadHash) (now : Nat) :
    StoredMessage :=
  { subject := subject, sequence := seq, payload := payload, headers := [], timestampMillis := now }

def pub (stream subject payload : String) (seq : StreamSeq) (now : Nat) : SubTraceStep :=
  { label := .op (.publish stream subject payload [] none now) (.ok (.sequence seq)) }

def create (raw : RawStreamConfig) : SubTraceStep :=
  { label := .op (.createStream raw) (.ok .unit) }

def reg (stream : String) (o : ConsumeOptions) (l₀ : StreamSeq) (id : SubId)
    (events : List Observed) (counts : List (StreamName × Nat) := []) : SubTraceStep :=
  { label := .register stream o l₀ id (.ok .unit), events := events, counts := counts }

def pullE (id : SubId) (events : List Observed) : SubTraceStep :=
  { label := .pull id, events := events }

/-! ## The traces -/

/-- C7: replay, `CaughtUp`, then live. -/
def saReplay : SubTrace :=
  { name := "sa-replay"
    mirrors := ["C7"]
    steps :=
      [ create kvConfigRaw
      , pub "KV_b" "$KV.b.a" "e1" 1 1
      , pub "KV_b" "$KV.b.b" "e2" 2 2
      , reg "KV_b" (opts ["$KV.b.>"] .allHistory) 2 0
          [.entry (msg "$KV.b.a" 1 "e1" 1), .entry (msg "$KV.b.b" 2 "e2" 2), .caughtUp] [("KV_b", 1)]
      , pub "KV_b" "$KV.b.c" "e3" 3 3
      , pullE 0 [.entry (msg "$KV.b.c" 3 "e3" 3)] ]
    finalObserved :=
      [ (0, [ .entry (msg "$KV.b.a" 1 "e1" 1), .entry (msg "$KV.b.b" 2 "e2" 2), .caughtUp
            , .entry (msg "$KV.b.c" 3 "e3" 3) ]) ] }

theorem sa_replay_trace : runSubTrace saReplay = true := by decide

/-- C8 and C15: every start position, `AfterSequence` at the head and at zero. -/
def saStarts : SubTrace :=
  { name := "sa-starts"
    mirrors := ["C8", "C15"]
    steps :=
      [ create kvConfigRaw
      , pub "KV_b" "$KV.b.k1" "k1-old" 1 1
      , pub "KV_b" "$KV.b.k1" "k1-new" 2 2
      , pub "KV_b" "$KV.b.k2" "k2" 3 3
      , reg "KV_b" (opts ["$KV.b.>"] .lastPerSubject) 3 0
          [.entry (msg "$KV.b.k1" 2 "k1-new" 2), .entry (msg "$KV.b.k2" 3 "k2" 3), .caughtUp]
      , reg "KV_b" (opts ["$KV.b.>"] (.fromSequence 2)) 3 1
          [.entry (msg "$KV.b.k1" 2 "k1-new" 2), .entry (msg "$KV.b.k2" 3 "k2" 3), .caughtUp]
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly) 3 2 [.caughtUp] [("KV_b", 3)]
      , pub "KV_b" "$KV.b.k3" "k3" 4 4
      , pullE 2 [.entry (msg "$KV.b.k3" 4 "k3" 4)]
      , reg "KV_b" (opts ["$KV.b.>"] (.afterSequence 4)) 4 3 [.caughtUp]
      , reg "KV_b" (opts ["$KV.b.>"] (.afterSequence 2)) 4 4
          [.entry (msg "$KV.b.k2" 3 "k2" 3), .entry (msg "$KV.b.k3" 4 "k3" 4), .caughtUp]
      , reg "KV_b" (opts ["$KV.b.>"] (.afterSequence 0)) 4 5
          [ .entry (msg "$KV.b.k1" 1 "k1-old" 1), .entry (msg "$KV.b.k1" 2 "k1-new" 2)
          , .entry (msg "$KV.b.k2" 3 "k2" 3), .entry (msg "$KV.b.k3" 4 "k3" 4), .caughtUp ]
      , reg "KV_b" (opts ["$KV.b.>"] (.fromSequence 1)) 4 6
          [ .entry (msg "$KV.b.k1" 1 "k1-old" 1), .entry (msg "$KV.b.k1" 2 "k1-new" 2)
          , .entry (msg "$KV.b.k2" 3 "k2" 3), .entry (msg "$KV.b.k3" 4 "k3" 4), .caughtUp ]
          [("KV_b", 7)] ]
    finalObserved :=
      [ (0, [ .entry (msg "$KV.b.k1" 2 "k1-new" 2), .entry (msg "$KV.b.k2" 3 "k2" 3), .caughtUp ])
      , (2, [ .caughtUp, .entry (msg "$KV.b.k3" 4 "k3" 4) ]) ] }

theorem sa_starts_trace : runSubTrace saStarts = true := by decide

/-- C9: filters restrict replay and live delivery. -/
def saFilters : SubTrace :=
  { name := "sa-filters"
    mirrors := ["C9"]
    steps :=
      [ create kvConfigRaw
      , pub "KV_b" "$KV.b.auth.user" "in" 1 1
      , pub "KV_b" "$KV.b.other" "out" 2 2
      , reg "KV_b" (opts ["$KV.b.auth.>"] .allHistory) 2 0
          [.entry (msg "$KV.b.auth.user" 1 "in" 1), .caughtUp]
      , pub "KV_b" "$KV.b.other" "out2" 3 3
      , pub "KV_b" "$KV.b.auth.x" "in2" 4 4
      , pullE 0 [.entry (msg "$KV.b.auth.x" 4 "in2" 4)] ]
    finalObserved :=
      [ (0, [ .entry (msg "$KV.b.auth.user" 1 "in" 1), .caughtUp
            , .entry (msg "$KV.b.auth.x" 4 "in2" 4) ]) ] }

theorem sa_filters_trace : runSubTrace saFilters = true := by decide

/-- C10 and T12′: deletion ends the subscriber with `StreamNotFound`; the name
is re-creatable and restarts at sequence 1. -/
def saDelete : SubTrace :=
  { name := "sa-delete"
    mirrors := ["C10"]
    steps :=
      [ create kvConfigRaw
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly) 0 0 [.caughtUp] [("KV_b", 1)]
      , { label := .op (.deleteStream "KV_b") (.ok .unit), counts := [("KV_b", 0)] }
      , pullE 0 [.failed (.streamNotFound "KV_b")]
      , { label := .op (.getStream "KV_b") (.error (.streamNotFound "KV_b")) }
      , create kvConfigRaw
      , pub "KV_b" "$KV.b.k" "again" 1 5
      , reg "KV_b" (opts ["$KV.b.>"] .allHistory) 1 1
          [.entry (msg "$KV.b.k" 1 "again" 5), .caughtUp] [("KV_b", 1)] ]
    finalObserved := [ (0, [.caughtUp, .failed (.streamNotFound "KV_b")]) ] }

theorem sa_delete_trace : runSubTrace saDelete = true := by decide

/-- C13: `TerminateOnLag 1` overflows on the third publish; the failure carries
the last *enqueued* sequence (2), the buffered entry is observed before it, and
the publisher is spared. -/
def saLag : SubTrace :=
  { name := "sa-lag"
    mirrors := ["C13"]
    steps :=
      [ create kvConfigRaw
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 1)) 0 0 [.caughtUp]
      , pub "KV_b" "$KV.b.k" "v1" 1 1
      , pullE 0 [.entry (msg "$KV.b.k" 1 "v1" 1)]
      , pub "KV_b" "$KV.b.k" "v2" 2 2
      , { label := .op (.publish "KV_b" "$KV.b.k" "v3" [] none 3) (.ok (.sequence 3))
          counts := [("KV_b", 0)] }
      , pub "KV_b" "$KV.b.k" "v4" 4 4
      , pullE 0 [.entry (msg "$KV.b.k" 2 "v2" 2)]
      , pullE 0 [.failed (.consumerLagged "KV_b" 2)] ]
    finalObserved :=
      [ (0, [ .caughtUp, .entry (msg "$KV.b.k" 1 "v1" 1), .entry (msg "$KV.b.k" 2 "v2" 2)
            , .failed (.consumerLagged "KV_b" 2) ]) ] }

theorem sa_lag_trace : runSubTrace saLag = true := by decide

/-- C14: resume after lag with `AfterSequence(lastDelivered)`, gap-free and
without duplicates. -/
def saResume : SubTrace :=
  { name := "sa-resume"
    mirrors := ["C14"]
    steps :=
      [ create kvConfigRaw
      , reg "KV_b" (opts ["$KV.b.>"] .allHistory (.terminateOnLag 1)) 0 0 [.caughtUp]
      , pub "KV_b" "$KV.b.k" "v1" 1 1
      , pullE 0 [.entry (msg "$KV.b.k" 1 "v1" 1)]
      , pub "KV_b" "$KV.b.k" "v2" 2 2
      , pub "KV_b" "$KV.b.k" "v3" 3 3
      , pub "KV_b" "$KV.b.k" "v4" 4 4
      , pullE 0 [.entry (msg "$KV.b.k" 2 "v2" 2)]
      , pullE 0 [.failed (.consumerLagged "KV_b" 2)]
      , reg "KV_b" (opts ["$KV.b.>"] (.afterSequence 2)) 4 1
          [.entry (msg "$KV.b.k" 3 "v3" 3), .entry (msg "$KV.b.k" 4 "v4" 4), .caughtUp]
          [("KV_b", 1)] ]
    finalObserved :=
      [ (0, [ .caughtUp, .entry (msg "$KV.b.k" 1 "v1" 1), .entry (msg "$KV.b.k" 2 "v2" 2)
            , .failed (.consumerLagged "KV_b" 2) ])
      , (1, [ .entry (msg "$KV.b.k" 3 "v3" 3), .entry (msg "$KV.b.k" 4 "v4" 4), .caughtUp ]) ] }

theorem sa_resume_trace : runSubTrace saResume = true := by decide

/-- M1: subscriber accounting returns to baseline after unsubscribes. -/
def saAccounting : SubTrace :=
  { name := "sa-accounting"
    mirrors := ["M1"]
    steps :=
      [ create kvConfigRaw
      , { label := .op (.getStream "KV_b") (.ok (.config kvConfig)), counts := [("KV_b", 0)] }
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 64)) 0 0 [.caughtUp]
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 64)) 0 1 [.caughtUp] [("KV_b", 2)]
      , { label := .unsubscribe 0, counts := [("KV_b", 1)] }
      , { label := .unsubscribe 1, counts := [("KV_b", 0)] } ]
    finalObserved := [ (0, [.caughtUp]), (1, [.caughtUp]) ] }

theorem sa_accounting_trace : runSubTrace saAccounting = true := by decide

/-- The Q1 witness: two publishes between two pulls on `TerminateOnLag 2` never
overflow when a pull drains the whole buffer. -/
def saDrain : SubTrace :=
  { name := "sa-drain"
    mirrors := []
    steps :=
      [ create kvConfigRaw
      , reg "KV_b" (opts ["$KV.b.>"] .newOnly (.terminateOnLag 2)) 0 0 [.caughtUp]
      , pub "KV_b" "$KV.b.k" "v1" 1 1
      , pub "KV_b" "$KV.b.k" "v2" 2 2
      , pullE 0 [.entry (msg "$KV.b.k" 1 "v1" 1), .entry (msg "$KV.b.k" 2 "v2" 2)]
      , pub "KV_b" "$KV.b.k" "v3" 3 3
      , pub "KV_b" "$KV.b.k" "v4" 4 4
      , pullE 0 [.entry (msg "$KV.b.k" 3 "v3" 3), .entry (msg "$KV.b.k" 4 "v4" 4)]
          |> fun t => { t with counts := [("KV_b", 1)] } ]
    finalObserved :=
      [ (0, [ .caughtUp, .entry (msg "$KV.b.k" 1 "v1" 1), .entry (msg "$KV.b.k" 2 "v2" 2)
            , .entry (msg "$KV.b.k" 3 "v3" 3), .entry (msg "$KV.b.k" 4 "v4" 4) ]) ] }

theorem sa_drain_trace : runSubTrace saDrain = true := by decide

/-- Every stage-A trace, in fixture order. -/
def allSubTraces : List SubTrace :=
  [ saReplay, saStarts, saFilters, saDelete, saLag, saResume, saAccounting, saDrain ]

theorem all_sub_traces : allSubTraces.all runSubTrace = true := by decide

/-! ## Falsification of the wrong models -/

/-- A one-element pull lags `sa-drain` on the fourth publish. -/
theorem w1_fails_drain : runSubTraceW1 saDrain = false := by decide

/-- Advancing `lastEnqueued` on the overflowing message makes `sa-lag` carry 3. -/
theorem w2_fails_lag : runSubTraceW2 saLag = false := by decide

/-- The wrong models are not wrong everywhere: each still passes traces that do
not exercise its defect, so the falsifying traces are the discriminating ones. -/
theorem w1_passes_replay : runSubTraceW1 saReplay = true := by decide
theorem w2_passes_drain : runSubTraceW2 saDrain = true := by decide

end EffectNatsSubstrate
