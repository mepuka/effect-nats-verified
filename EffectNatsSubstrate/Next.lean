import EffectNatsSubstrate.SelectReplay
import EffectNatsSubstrate.Traces

/-!
# Labels and the transition relation — stage A

The environment chooses labels; each label's effect is deterministic.
`apply : SubState → Label → Option SubState` returns `none` for a disabled or
mislabelled step, `Next s l s' := apply s l = some s'`, and `ReachableSub` is
the closure of `initialSub` under `Next` (slice document §4).

Source lines are `src/internal/JetStreamMemory.ts` @ `872bd7f` unless stated.
The fan-out step and the pull step are parameters of `applyWith` so that the
two deliberately wrong models of the slice document (§7) are instances of the
same skeleton; `apply` is the model.

Queue facts assumed (slice document §2.4, discharged in stage B):
Q1 — a pull drains the whole buffer (`Stream.fromQueue` pulls with `takeAll`);
Q2 — `fail` delivers the buffer, then the error (`Open → Closing → Done`);
Q3 — `shutdown` discards the buffer.
-/

namespace EffectNatsSubstrate

inductive Label where
  /-- One of the five sequential operations with its expected outcome; the
  core steps by `step`, then a successful `publish` fans out and a successful
  `deleteStream` ends the stream's subscribers. -/
  | op (o : Op) (expect : Expect)
  /-- `consume` registration (`:220-256`): the snapshot and `CaughtUp` enter
  `observed` at once (design note decision 5); `lastEnqueued₀` is the
  interpreter's pre-enqueue value (memory: the stream's `nextSequence - 1`). -/
  | register (stream : StreamName) (opts : ConsumeOptions) (lastEnqueued₀ : StreamSeq)
      (id : SubId) (expect : Expect)
  /-- One consumer pull (Q1: the whole buffer). -/
  | pull (id : SubId)
  /-- Scope closure: `Set.delete`, then `Queue.shutdown` (Q3). -/
  | unsubscribe (id : SubId)
  deriving Repr, DecidableEq

/-- Fan-out to one subscriber for a stored message of `stream` (`:176-199`):
`TerminateOnLag` with a full buffer leaves the `Set` and fails the queue with
the *pre-overflow* `lastDelivered` (`:181-192`); otherwise the message is
offered and `lastDelivered` advances (`:194-195`), the offer's result being
discarded even when the queue is no longer open. -/
def deliverOne (stream : StreamName) (m : StoredMessage) (sub : Subscriber) : Subscriber :=
  if sub.stream == stream && sub.registered && matchesAny sub.filters m.subject then
    match sub.policy with
    | .terminateOnLag n =>
      if n ≤ sub.pending.length then
        { sub with
            registered := false
            status :=
              if sub.pending.isEmpty then .done (.consumerLagged stream sub.lastEnqueued)
              else .closing (.consumerLagged stream sub.lastEnqueued) }
      else if sub.status = .opened then
        { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence }
      else
        { sub with lastEnqueued := m.sequence }
  else sub

/-- `deleteStream` fails every queue still in the `Set` with `StreamNotFound`
(`:126-135`); Q2 decides `closing` versus `done`. -/
def endOne (stream : StreamName) (sub : Subscriber) : Subscriber :=
  if sub.stream == stream && sub.registered then
    { sub with
        registered := false
        status :=
          if sub.pending.isEmpty then .done (.streamNotFound stream)
          else .closing (.streamNotFound stream) }
  else sub

/-- One pull on a subscriber (Q1, Q2): `none` when the pull would suspend
(empty open buffer) or the subscriber is finished. -/
def pullStep (sub : Subscriber) : Option Subscriber :=
  match sub.status with
  | .shutDown => none
  | .done e => some { sub with observed := sub.observed ++ [.failed e], status := .shutDown }
  | .opened =>
    if sub.pending.isEmpty then none
    else some { sub with observed := sub.observed ++ sub.pending.map Observed.entry, pending := [] }
  | .closing e =>
    if sub.pending.isEmpty then none
    else some { sub with
                  observed := sub.observed ++ sub.pending.map Observed.entry
                  pending := []
                  status := .done e }

def newSubscriber (stream : StreamName) (opts : ConsumeOptions) (lastEnqueued₀ : StreamSeq)
    (messages : List StoredMessage) : Subscriber :=
  { stream := stream
    filters := opts.filters
    policy := opts.buffer
    pending := []
    status := .opened
    registered := true
    lastEnqueued := lastEnqueued₀
    observed := replayObserved messages opts }

section Skeleton

variable (deliver : StreamName → StoredMessage → Subscriber → Subscriber)
variable (pull : Subscriber → Option Subscriber)

/-- The subscriber-side effect of a successful sequential operation. -/
def afterOp (s : SubState) (core' : JSState) : Op → Ret → SubState
  | .publish stream subject payload headers _ now, .sequence seq =>
    let m : StoredMessage :=
      { subject := subject, sequence := seq, payload := payload, headers := headers,
        timestampMillis := now }
    { s with core := core', subs := s.subs.map (fun p => (p.1, deliver stream m p.2)) }
  | .deleteStream name, _ =>
    { s with core := core', subs := s.subs.map (fun p => (p.1, endOne name p.2)) }
  | _, _ => { s with core := core' }

def applyOp (s : SubState) (o : Op) (e : Expect) : Option SubState :=
  match step s.core o, e with
  | .ok (core', r), .ok r' => if r = r' then some (afterOp deliver s core' o r) else none
  | .error err, .error err' => if err = err' then some s else none
  | _, _ => none

/-- The environment's pre-enqueue value is admissible when it bounds every
replayed entry and sits below the stream head — true of the memory interpreter's
`nextSequence - 1` and of the live adapter's `0` with an empty replay
(slice document §4.2, §9.1). -/
def replayBound (messages : List StoredMessage) (opts : ConsumeOptions)
    (lastEnqueued₀ nextSequence : StreamSeq) : Bool :=
  (selectReplay messages opts).all (fun m => decide (m.sequence ≤ lastEnqueued₀))
    && decide (lastEnqueued₀ < nextSequence)

/-- Registration is enabled for the next id, a capacity `≥ 1`, and an admissible
`lastEnqueued₀`; on a missing stream it reports `StreamNotFound` and changes
nothing (`requireStream`, `:226`, fails before any acquisition). -/
def applyRegister (s : SubState) (stream : StreamName) (opts : ConsumeOptions)
    (lastEnqueued₀ : StreamSeq) (id : SubId) (e : Expect) : Option SubState :=
  if id ≠ s.nextId || opts.buffer.capacity = 0 then none
  else
    match lookupStream s.core stream, e with
    | none, .error (.streamNotFound name) => if name = stream then some s else none
    | some st, .ok .unit =>
      if replayBound st.messages opts lastEnqueued₀ st.nextSequence then
        some { s with
                 subs := s.subs ++ [(id, newSubscriber stream opts lastEnqueued₀ st.messages)]
                 nextId := id + 1 }
      else none
    | _, _ => none

def applyPull (s : SubState) (id : SubId) : Option SubState :=
  match lookupSub s.subs id with
  | none => none
  | some sub =>
    match pull sub with
    | none => none
    | some sub' => some { s with subs := updateSub s.subs id (fun _ => sub') }

def applyUnsubscribe (s : SubState) (id : SubId) : Option SubState :=
  match lookupSub s.subs id with
  | none => none
  | some sub =>
    if sub.status = .shutDown then none
    else some { s with
                  subs := updateSub s.subs id (fun sub =>
                    { sub with registered := false, pending := [], status := .shutDown }) }

def applyWith (s : SubState) : Label → Option SubState
  | .op o e => applyOp deliver s o e
  | .register stream opts l₀ id e => applyRegister s stream opts l₀ id e
  | .pull id => applyPull pull s id
  | .unsubscribe id => applyUnsubscribe s id

end Skeleton

/-- The stage-A model. -/
def apply : SubState → Label → Option SubState := applyWith deliverOne pullStep

def Next (s : SubState) (l : Label) (s' : SubState) : Prop := apply s l = some s'

inductive ReachableSub : SubState → Prop
  | init : ReachableSub initialSub
  | step {s s' : SubState} {l : Label} : ReachableSub s → Next s l s' → ReachableSub s'

end EffectNatsSubstrate
