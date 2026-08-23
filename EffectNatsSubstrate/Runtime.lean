import EffectNatsSubstrate.EffectQueue
import EffectNatsSubstrate.SubPlacements

/-!
# The runtime model — stage B1 (`TerminateOnLag`)

The memory interpreter's subscriber machinery at the step granularity assumption
A4 is about (stage-B slice document §2.2): a publish is `op` (the core's
`publishStep` under the permit, which fixes the fan-out list from the `Set`),
then per matching subscriber `check i` (`Queue.size`, `:186-187`) and
`resolve i` (`Set` delete + `Queue.fail`, `:188-196`, or `Queue.offer` +
`lastDelivered`, `:199-200`), then `endFanOut` (`:202-204`). A deletion is `op`
then `resolve i` per subscriber of the stream (`:132-136`). Pulls (`takeAll`),
parked-taker wake-ups, and the two halves of a scope closure (`Set` delete,
then `shutdown`) never take the permit and may interleave with any of those
steps. Registration and the other operations take the permit and are one step.

Source lines are `src/internal/JetStreamMemory.ts` @ `bec02ac` (the subscriber
path is byte-identical to `872bd7f`, stage A's pin).

`rtStep` is total-or-disabled, like stage A's `apply`, so runtime traces are
kernel-checkable by `decide`. `eraseRt` projects a runtime state to a stage-A
state; a subscriber's `observed` is the flattening of its chunk history.
-/

namespace EffectNatsSubstrate

/-- What a fan-out did to one subscriber (ghost data the simulation relation
reads; computed, never branched on by a later step). -/
inductive Outcome where
  | admitted
  | overflowed
  | skipped
  | ended
  deriving Repr, DecidableEq

inductive FanKind where
  /-- The stored message and the publish's `expectedLastSubjectSequence`, so
  the abstract label can be rebuilt exactly. -/
  | publish (stream : StreamName) (m : StoredMessage) (expectedLast : Option StreamSeq)
  | delete (name : StreamName)
  deriving Repr, DecidableEq

/-- A fan-out in progress: the publisher holds the permit until `endFanOut`. -/
structure FanOut where
  kind : FanKind
  /-- Subscribers still to visit, in `Set` (= `SubId`) order, fixed when the
  operation stored the message (`:182`). -/
  remaining : List SubId
  /-- After `check i`: the overflow decision, waiting for `resolve i`. -/
  decided : Option (SubId × Bool)
  visited : List (SubId × Outcome)
  deriving Repr, DecidableEq

structure RtSubscriber where
  stream : StreamName
  filters : List SubjectName
  policy : Policy
  /-- Membership in the stream's `Set`. -/
  registered : Bool
  /-- The implementation's `lastDelivered` (`:200`, `:237`). -/
  lastEnqueued : StreamSeq
  queue : EffectQueue
  /-- The consumer's history: the registration chunk, then one chunk per
  returning `takeAll`. -/
  chunks : History
  /-- Between the two steps of a scope closure. -/
  closeStarted : Bool
  deriving Repr, DecidableEq

structure RtState where
  core : JSState
  subs : List (SubId × RtSubscriber)
  nextId : SubId
  fanOut : Option FanOut
  deriving Repr, DecidableEq

def initialRt : RtState := { core := emptyState, subs := [], nextId := 0, fanOut := none }

def lookupRt : List (SubId × RtSubscriber) → SubId → Option RtSubscriber
  | [], _ => none
  | (i, sub) :: rest, id => if i = id then some sub else lookupRt rest id

def updateRt : List (SubId × RtSubscriber) → SubId → (RtSubscriber → RtSubscriber) →
    List (SubId × RtSubscriber)
  | [], _, _ => []
  | (i, sub) :: rest, id, f =>
    if i = id then (i, f sub) :: updateRt rest id f else (i, sub) :: updateRt rest id f

/-- The erasure to stage A: the queue's buffer and status are `pending` and
`status`; `observed` is the flattened chunk history. -/
def RtSubscriber.erase (r : RtSubscriber) : Subscriber :=
  { stream := r.stream, filters := r.filters, policy := r.policy, pending := r.queue.buffer
    status := r.queue.status, registered := r.registered, lastEnqueued := r.lastEnqueued
    observed := r.chunks.flatten }

def eraseRt (s : RtState) : SubState :=
  { core := s.core, subs := s.subs.map (fun p => (p.1, p.2.erase)), nextId := s.nextId }

def rtHistory (s : RtState) (id : SubId) : History :=
  match lookupRt s.subs id with
  | some r => r.chunks
  | none => []

inductive RtLabel where
  /-- One of the five sequential operations with its expected outcome. A
  successful publish or deletion opens a fan-out; the others complete here. -/
  | op (o : Op) (expect : Expect)
  | register (stream : StreamName) (opts : ConsumeOptions) (lastEnqueued₀ : StreamSeq)
      (id : SubId) (expect : Expect)
  /-- `Queue.size` and the overflow decision for the next subscriber. -/
  | check (id : SubId)
  /-- `Set` delete + `Queue.fail`, or `Queue.offer` + `lastDelivered`, per the
  recorded decision; for a deletion, `Queue.fail` with `StreamNotFound`. -/
  | resolve (id : SubId)
  | endFanOut
  /-- `takeAll` by the consumer of `id`. -/
  | pull (id : SubId)
  /-- A parked `takeAll` resumes. -/
  | wake (id : SubId)
  /-- Scope closure, first finalizer: `Set` delete (`:244`). -/
  | closeA (id : SubId)
  /-- Scope closure, second finalizer: `Queue.shutdown` (`:231`). -/
  | closeB (id : SubId)
  deriving Repr, DecidableEq

/-- The fan-out list a successful publish fixes at `:182`: registered
subscribers of the stream whose filters match, in `SubId` order. -/
def fanOutIds (s : RtState) (stream : StreamName) (subject : SubjectName) : List SubId :=
  (s.subs.filter (fun p =>
    p.2.registered && p.2.stream == stream && matchesAny p.2.filters subject)).map Prod.fst

/-- The deletion's list: every subscriber in the stream's `Set` (`:133`). -/
def deleteIds (s : RtState) (name : StreamName) : List SubId :=
  (s.subs.filter (fun p => p.2.registered && p.2.stream == name)).map Prod.fst

def rtOp (s : RtState) (o : Op) (e : Expect) : Option RtState :=
  if s.fanOut.isSome then none
  else
    match step s.core o, e with
    | .error err, .error err' => if err = err' then some s else none
    | .ok (core', r), .ok r' =>
      if r ≠ r' then none
      else
        match o, r with
        | .publish stream subject payload headers expected? now, .sequence seq =>
          let m : StoredMessage :=
            { subject := subject, sequence := seq, payload := payload, headers := headers,
              timestampMillis := now }
          some { s with core := core'
                        fanOut := some { kind := .publish stream m expected?
                                         remaining := fanOutIds s stream subject
                                         decided := none, visited := [] } }
        | .deleteStream name, _ =>
          some { s with core := core'
                        fanOut := some { kind := .delete name, remaining := deleteIds s name
                                         decided := none, visited := [] } }
        | _, _ => some { s with core := core' }
    | _, _ => none

def rtRegister (s : RtState) (stream : StreamName) (opts : ConsumeOptions)
    (l₀ : StreamSeq) (id : SubId) (e : Expect) : Option RtState :=
  if s.fanOut.isSome || id ≠ s.nextId || opts.buffer.capacity = 0 then none
  else
    match lookupStream s.core stream, e with
    | none, .error (.streamNotFound name) => if name = stream then some s else none
    | some st, .ok .unit =>
      if replayBound st.messages opts l₀ st.nextSequence then
        let r : RtSubscriber :=
          { stream := stream, filters := opts.filters, policy := opts.buffer, registered := true
            lastEnqueued := l₀, queue := EffectQueue.empty
            chunks := [replayObserved st.messages opts], closeStarted := false }
        some { s with subs := s.subs ++ [(id, r)], nextId := id + 1 }
      else none
    | _, _ => none

/-- `check i`: the next subscriber of a publish fan-out; `Queue.size` against
the policy's capacity. -/
def rtCheck (s : RtState) (id : SubId) : Option RtState :=
  match s.fanOut with
  | some f =>
    match f.kind, f.decided, f.remaining with
    | .publish _ _ _, none, i :: rest =>
      if i ≠ id then none
      else
        match lookupRt s.subs id with
        | none => none
        | some r =>
          let overflow := match r.policy with
            | .terminateOnLag n => decide (n ≤ r.queue.size)
          some { s with fanOut := some { f with remaining := rest, decided := some (id, overflow) } }
    | _, _, _ => none
  | none => none

def rtResolve (s : RtState) (id : SubId) : Option RtState :=
  match s.fanOut with
  | none => none
  | some f =>
    match f.kind with
    | .publish stream m _ =>
      match f.decided with
      | some (i, overflow) =>
        if i ≠ id then none
        else
          match lookupRt s.subs id with
          | none => none
          | some r =>
            if overflow then
              let r' := { r with registered := false
                                 queue := r.queue.fail (.consumerLagged stream r.lastEnqueued) }
              some { s with subs := updateRt s.subs id (fun _ => r')
                            fanOut := some { f with decided := none
                                                    visited := f.visited ++ [(id, .overflowed)] } }
            else
              let (q', res) := r.queue.offer r.policy.capacity m
              match res with
              | .wouldSuspend => none
              | _ =>
                let r' := { r with queue := q', lastEnqueued := m.sequence }
                some { s with subs := updateRt s.subs id (fun _ => r')
                              fanOut := some { f with decided := none
                                                      visited := f.visited ++
                                                        [(id, if res = .accepted then .admitted
                                                              else .skipped)] } }
      | none => none
    | .delete name =>
      match f.decided, f.remaining with
      | none, i :: rest =>
        if i ≠ id then none
        else
          match lookupRt s.subs id with
          | none => none
          | some r =>
            let r' := { r with registered := false, queue := r.queue.fail (.streamNotFound name) }
            some { s with subs := updateRt s.subs id (fun _ => r')
                          fanOut := some { f with remaining := rest
                                                  visited := f.visited ++ [(id, .ended)] } }
      | _, _ => none

def rtEndFanOut (s : RtState) : Option RtState :=
  match s.fanOut with
  | some f => if f.remaining.isEmpty && f.decided.isNone then some { s with fanOut := none } else none
  | none => none

def chunkOf : EffectQueue.TakeResult → Option (List Observed)
  | .chunk ms => some (ms.map Observed.entry)
  | .exit e => some [.failed e]
  | .parked => none
  | .interrupted => none

def rtPull (s : RtState) (id : SubId) : Option RtState :=
  match lookupRt s.subs id with
  | none => none
  | some r =>
    -- the scope-closure finalizers run only once the consumer fiber has stopped
    -- (the stream ended or the fiber was interrupted), so no pull follows `closeA`
    if r.queue.taker || r.queue.status = .shutDown || r.closeStarted then none
    else
      let (q', res) := r.queue.takeAll
      match res with
      | .interrupted => none
      | _ =>
        let chunks' := match chunkOf res with
          | some c => r.chunks ++ [c]
          | none => r.chunks
        some { s with subs := updateRt s.subs id (fun _ => { r with queue := q', chunks := chunks' }) }

def rtWake (s : RtState) (id : SubId) : Option RtState :=
  match lookupRt s.subs id with
  | none => none
  | some r =>
    if r.closeStarted then none else
    match r.queue.wake with
    | none => none
    | some (q', res) =>
      let chunks' := match chunkOf res with
        | some c => r.chunks ++ [c]
        | none => r.chunks
      some { s with subs := updateRt s.subs id (fun _ => { r with queue := q', chunks := chunks' }) }

def rtCloseA (s : RtState) (id : SubId) : Option RtState :=
  match lookupRt s.subs id with
  | none => none
  | some r =>
    if r.closeStarted || r.queue.status = .shutDown then none
    else some { s with subs := updateRt s.subs id (fun _ => { r with registered := false, closeStarted := true }) }

def rtCloseB (s : RtState) (id : SubId) : Option RtState :=
  match lookupRt s.subs id with
  | none => none
  | some r =>
    if !r.closeStarted then none
    else some { s with subs := updateRt s.subs id (fun _ =>
                  { r with queue := r.queue.shutdown, closeStarted := false }) }

def rtStep (s : RtState) : RtLabel → Option RtState
  | .op o e => rtOp s o e
  | .register stream opts l₀ id e => rtRegister s stream opts l₀ id e
  | .check id => rtCheck s id
  | .resolve id => rtResolve s id
  | .endFanOut => rtEndFanOut s
  | .pull id => rtPull s id
  | .wake id => rtWake s id
  | .closeA id => rtCloseA s id
  | .closeB id => rtCloseB s id

def RtNext (s : RtState) (l : RtLabel) (s' : RtState) : Prop := rtStep s l = some s'

inductive ReachableRt : RtState → Prop
  | init : ReachableRt initialRt
  | step {s s' : RtState} {l : RtLabel} : ReachableRt s → RtNext s l s' → ReachableRt s'

end EffectNatsSubstrate
