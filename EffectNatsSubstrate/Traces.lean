import EffectNatsSubstrate.Step

/-!
# Worked traces — the replay artifact

A trace is **data**: a named list of steps (an `Op` with its expected outcome)
and a list of views of the final state (the payload tokens of `forSubject`, or
of the whole stream). `runTrace` folds `step` over the steps and checks the
views; every trace is kernel-checked with `decide`, and the same data is
printed by the exporter (`Main.lean`) as a deterministic JSON fixture that the
effect-nats suite replays against the memory interpreter and the live server
(slices plan, slice 2).

Traces mirror the conformance cases they are named after (proposal §2.3):

- `positiveTrace` — C1 (get), C3 (CAS success), C4 (last message).
- `rejectedTrace` — C1 (conflict, missing stream), C2 (unbound subject,
  missing stream on publish); plus the model-only negative-capacity rejection
  the memory interpreter does not perform (`replay := false`).
- `pruneTrace` — C5 and C4's typed absence.
- `rollupTrace`, `rollupDeniedTrace` — C6.
- `casTrace` — C3 including the expected/actual carried by the failure.
- `deleteTrace` — C10's `getStream` after deletion and the re-creation restart
  at sequence 1 (proposal T12′, sequential part).
- `configOrderTrace` — order-sensitive `ConfigEq` (proposal §3.1, §7): the
  memory interpreter rejects a re-create with the same subjects in another
  order; whether the live server agrees is a finding the replay produces.

The conformance suite observes storage through `consume`, which this package
does not model; views are the model's stand-in, and the replay harness reads
them through `consume AllHistory` with the view's subject as the filter.
Payloads are opaque tokens. `timestampMillis` is carried by `Op.publish` and
never comparable across interpreters; the fixture says so.
-/

namespace EffectNatsSubstrate

/-- Expected outcome of one step. -/
inductive Expect where
  | ok (r : Ret)
  | error (e : JSError)
  deriving Repr, DecidableEq

structure TraceStep where
  op : Op
  expect : Expect
  /-- `false` marks a step the TypeScript replay skips: boundary validation the
  model performs and the memory interpreter does not. Errors leave the state
  unchanged, so skipping such a step keeps the rest of the trace valid. -/
  replay : Bool := true
  deriving Repr

/-- A view of the final state: the payload tokens of `forSubject` for `subject`,
or of the whole stream when `subject = none`, in storage order. -/
structure ViewCheck where
  stream : StreamName
  subject : Option SubjectName
  payloads : List PayloadHash
  deriving Repr

structure Trace where
  name : String
  /-- Conformance cases the trace mirrors (labels of proposal §2.3). -/
  mirrors : List String
  steps : List TraceStep
  views : List ViewCheck
  deriving Repr

/-- Fold `step` over the steps, requiring each outcome to match exactly; an
error leaves the state where it was. -/
def runSteps : JSState → List TraceStep → Option JSState
  | s, [] => some s
  | s, t :: rest =>
    match step s t.op, t.expect with
    | .ok (s', r), .ok r' => if r = r' then runSteps s' rest else none
    | .error e, .error e' => if e = e' then runSteps s rest else none
    | _, _ => none

def viewPayloads (s : JSState) (v : ViewCheck) : Option (List PayloadHash) :=
  match lookupStream s v.stream with
  | none => none
  | some st =>
    match v.subject with
    | some subject => some ((forSubject st.messages subject).map (·.payload))
    | none => some (st.messages.map (·.payload))

def checkViews (s : JSState) : List ViewCheck → Bool
  | [] => true
  | v :: rest => (viewPayloads s v == some v.payloads) && checkViews s rest

def runTrace (t : Trace) : Bool :=
  match runSteps emptyState t.steps with
  | some s => checkViews s t.views
  | none => false

/-! ## The traces -/

def kvConfigRaw : RawStreamConfig :=
  { name := "KV_b"
    subjects := ["$KV.b.>"]
    maxMessagesPerSubject := 0
    allowRollup := true }

def kvConfig : StreamConfig :=
  { name := "KV_b"
    subjects := ["$KV.b.>"]
    maxMessagesPerSubject := 0
    allowRollup := true }

def positiveTrace : Trace :=
  { name := "positive"
    mirrors := ["C1", "C3", "C4"]
    steps :=
      [ { op := .createStream kvConfigRaw, expect := .ok .unit }
      , { op := .getStream "KV_b", expect := .ok (.config kvConfig) }
      , { op := .publish "KV_b" "$KV.b.k" "h1" [] none 100, expect := .ok (.sequence 1) }
      , { op := .publish "KV_b" "$KV.b.k" "h2" [] (some 1) 200, expect := .ok (.sequence 2) }
      , { op := .lastMessageForSubject "KV_b" "$KV.b.k"
          expect := .ok (.message { subject := "$KV.b.k", sequence := 2, payload := "h2",
                                    headers := [], timestampMillis := 200 }) } ]
    views := [ { stream := "KV_b", subject := some "$KV.b.k", payloads := ["h1", "h2"] } ] }

theorem positive_trace : runTrace positiveTrace = true := by decide

def rejectedTrace : Trace :=
  { name := "rejected"
    mirrors := ["C1", "C2"]
    steps :=
      [ { op := .createStream kvConfigRaw, expect := .ok .unit }
      , { op := .createStream { kvConfigRaw with maxMessagesPerSubject := 5 }
          expect := .error (.streamConfigConflict "KV_b") }
      , { op := .publish "KV_b" "$KV.other.k" "h" [] none 0
          expect := .error (.subjectNotBound "KV_b" "$KV.other.k") }
      , { op := .publish "KV_nope" "$KV.nope.k" "x" [] none 0
          expect := .error (.streamNotFound "KV_nope") }
      , { op := .getStream "KV_nope", expect := .error (.streamNotFound "KV_nope") }
      , { op := .createStream { name := "bad", subjects := [], maxMessagesPerSubject := -1,
                                allowRollup := false }
          expect := .error (.invalidConfig (.negativeCapacity "bad" (-1)))
          replay := false }
      , { op := .createStream kvConfigRaw, expect := .ok .unit } ]
    views := [ { stream := "KV_b", subject := none, payloads := [] } ] }

theorem rejected_trace : runTrace rejectedTrace = true := by decide

def pruneTrace : Trace :=
  { name := "prune"
    mirrors := ["C5", "C4"]
    steps :=
      [ { op := .createStream { name := "KV_p", subjects := ["$KV.p.>"],
                                maxMessagesPerSubject := 2, allowRollup := true }
          expect := .ok .unit }
      , { op := .publish "KV_p" "$KV.p.k" "v1" [] none 1, expect := .ok (.sequence 1) }
      , { op := .publish "KV_p" "$KV.p.k" "v2" [] none 2, expect := .ok (.sequence 2) }
      , { op := .publish "KV_p" "$KV.p.k" "v3" [] none 3, expect := .ok (.sequence 3) }
      , { op := .lastMessageForSubject "KV_p" "$KV.p.k"
          expect := .ok (.message { subject := "$KV.p.k", sequence := 3, payload := "v3",
                                    headers := [], timestampMillis := 3 }) }
      , { op := .lastMessageForSubject "KV_p" "$KV.p.none"
          expect := .error (.noMessageForSubject "KV_p" "$KV.p.none") } ]
    views :=
      [ { stream := "KV_p", subject := some "$KV.p.k", payloads := ["v2", "v3"] }
      , { stream := "KV_p", subject := none, payloads := ["v2", "v3"] } ] }

theorem prune_trace : runTrace pruneTrace = true := by decide

def rollupTrace : Trace :=
  { name := "rollup"
    mirrors := ["C6"]
    steps :=
      [ { op := .createStream kvConfigRaw, expect := .ok .unit }
      , { op := .publish "KV_b" "$KV.b.k" "v1" [] none 1, expect := .ok (.sequence 1) }
      , { op := .publish "KV_b" "$KV.b.other" "keep" [] none 2, expect := .ok (.sequence 2) }
      , { op := .publish "KV_b" "$KV.b.k" "purged" [("Nats-Rollup", "sub")] none 3
          expect := .ok (.sequence 3) }
      , { op := .lastMessageForSubject "KV_b" "$KV.b.k"
          expect := .ok (.message { subject := "$KV.b.k", sequence := 3, payload := "purged",
                                    headers := [("Nats-Rollup", "sub")], timestampMillis := 3 }) } ]
    views :=
      [ { stream := "KV_b", subject := some "$KV.b.k", payloads := ["purged"] }
      , { stream := "KV_b", subject := some "$KV.b.other", payloads := ["keep"] }
      , { stream := "KV_b", subject := none, payloads := ["keep", "purged"] } ] }

theorem rollup_trace : runTrace rollupTrace = true := by decide

def rollupDeniedTrace : Trace :=
  { name := "rollup-denied"
    mirrors := ["C6"]
    steps :=
      [ { op := .createStream { name := "KV_x", subjects := ["$KV.x.>"],
                                maxMessagesPerSubject := 0, allowRollup := false }
          expect := .ok .unit }
      , { op := .publish "KV_x" "$KV.x.k" "v" [("Nats-Rollup", "sub")] none 1
          expect := .error (.rollupNotPermitted "KV_x") }
      , { op := .publish "KV_x" "$KV.x.k" "v" [] none 2, expect := .ok (.sequence 1) } ]
    views := [ { stream := "KV_x", subject := some "$KV.x.k", payloads := ["v"] } ] }

theorem rollup_denied_trace : runTrace rollupDeniedTrace = true := by decide

def casTrace : Trace :=
  { name := "cas"
    mirrors := ["C3"]
    steps :=
      [ { op := .createStream kvConfigRaw, expect := .ok .unit }
      , { op := .publish "KV_b" "$KV.b.k" "v1" [] (some 0) 1, expect := .ok (.sequence 1) }
      , { op := .publish "KV_b" "$KV.b.k" "v2" [] (some 0) 2
          expect := .error (.wrongLastSequence "KV_b" "$KV.b.k" 0 1) }
      , { op := .publish "KV_b" "$KV.b.other" "x" [] none 3, expect := .ok (.sequence 2) }
      , { op := .publish "KV_b" "$KV.b.k" "v2" [] (some 1) 4, expect := .ok (.sequence 3) }
      , { op := .lastMessageForSubject "KV_b" "$KV.b.k"
          expect := .ok (.message { subject := "$KV.b.k", sequence := 3, payload := "v2",
                                    headers := [], timestampMillis := 4 }) } ]
    views := [ { stream := "KV_b", subject := some "$KV.b.k", payloads := ["v1", "v2"] } ] }

theorem cas_trace : runTrace casTrace = true := by decide

def deleteTrace : Trace :=
  { name := "delete-recreate"
    mirrors := ["C10"]
    steps :=
      [ { op := .createStream { name := "KV_d", subjects := ["$KV.d.>"],
                                maxMessagesPerSubject := 0, allowRollup := true }
          expect := .ok .unit }
      , { op := .publish "KV_d" "$KV.d.k" "x1" [] none 1, expect := .ok (.sequence 1) }
      , { op := .deleteStream "KV_d", expect := .ok .unit }
      , { op := .getStream "KV_d", expect := .error (.streamNotFound "KV_d") }
      , { op := .publish "KV_d" "$KV.d.k" "x2" [] none 2, expect := .error (.streamNotFound "KV_d") }
      , { op := .deleteStream "KV_d", expect := .error (.streamNotFound "KV_d") }
      , { op := .createStream { name := "KV_d", subjects := ["$KV.d.>"],
                                maxMessagesPerSubject := 0, allowRollup := true }
          expect := .ok .unit }
      , { op := .publish "KV_d" "$KV.d.k" "x2" [] none 3, expect := .ok (.sequence 1) } ]
    views := [ { stream := "KV_d", subject := some "$KV.d.k", payloads := ["x2"] } ] }

theorem delete_trace : runTrace deleteTrace = true := by decide

def configOrderTrace : Trace :=
  { name := "config-order"
    mirrors := ["C1"]
    steps :=
      [ { op := .createStream { name := "KV_o", subjects := ["$KV.o.a.>", "$KV.o.b.>"],
                                maxMessagesPerSubject := 0, allowRollup := true }
          expect := .ok .unit }
      , { op := .createStream { name := "KV_o", subjects := ["$KV.o.b.>", "$KV.o.a.>"],
                                maxMessagesPerSubject := 0, allowRollup := true }
          expect := .error (.streamConfigConflict "KV_o") }
      , { op := .createStream { name := "KV_o", subjects := ["$KV.o.a.>", "$KV.o.b.>"],
                                maxMessagesPerSubject := 0, allowRollup := true }
          expect := .ok .unit }
      , { op := .publish "KV_o" "$KV.o.b.k" "y" [] none 1, expect := .ok (.sequence 1) } ]
    views := [ { stream := "KV_o", subject := none, payloads := ["y"] } ] }

theorem config_order_trace : runTrace configOrderTrace = true := by decide

/-- Every trace the exporter prints, in fixture order. -/
def allTraces : List Trace :=
  [ positiveTrace, rejectedTrace, pruneTrace, rollupTrace, rollupDeniedTrace, casTrace,
    deleteTrace, configOrderTrace ]

theorem all_traces : allTraces.all runTrace = true := by decide

end EffectNatsSubstrate
