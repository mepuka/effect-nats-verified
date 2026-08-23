import EffectNatsSubstrate.Step

/-!
# Subscriber carriers — stage A

The subscriber layer of the memory interpreter for `TerminateOnLag` buffers,
stated over the sequential core. Source: `src/internal/JetStreamMemory.ts` @
`872bd7f` (`Subscriber` record `:25-30`, the `Set` of subscribers `:32-37`,
registration `:220-256`), the seam `src/internal/JetStream.ts:30-76`, and the
slice document `research/2026-08-22-subscriber-stage-a.md` §3.

Stage A has no `PullWindow` and no `Blocked` state (slices plan D4); those are
stage B. Every carrier here is plain data so that traces check by `decide`.
-/

namespace EffectNatsSubstrate

/-- Registration order; also the fan-out order (the JS `Set` iterates in
insertion order, `:177`). -/
abbrev SubId := Nat

/-- `ConsumeBuffer` restricted to stage A. `n ≥ 1` is enforced at the seam
(`validateConsumeBuffer`, `src/internal/JetStream.ts:72-76`) before any
registration; the model's `register` label is enabled only for `n ≥ 1`. -/
inductive Policy where
  | terminateOnLag (n : Nat)
  deriving Repr, DecidableEq

def Policy.capacity : Policy → Nat
  | .terminateOnLag n => n

/-- `StartPosition` (`src/internal/JetStream.ts:30-35`), including ADR-0008's
exclusive `AfterSequence`. -/
inductive StartPosition where
  | allHistory
  | lastPerSubject
  | newOnly
  | fromSequence (n : StreamSeq)
  | afterSequence (n : StreamSeq)
  deriving Repr, DecidableEq

structure ConsumeOptions where
  filters : List SubjectName
  start : StartPosition
  buffer : Policy
  deriving Repr, DecidableEq

/-- The two failures a subscription's queue can end with
(`src/internal/JetStream.ts:125-135`; the seam's `consume` error union minus
the live-only `SequenceNotProvablyExact`). -/
inductive SubError where
  | streamNotFound (stream : StreamName)
  | consumerLagged (stream : StreamName) (lastDelivered : StreamSeq)
  deriving Repr, DecidableEq

/-- Effect `Queue` lifecycle as the consumer sees it: `Open`, `Closing` (failed
with a non-empty buffer, still draining), `Done` (the failure is next), and the
scope's `shutdown`. `opened` is Effect's `Open` (`open` is a Lean keyword). -/
inductive QueueStatus where
  | opened
  | closing (e : SubError)
  | done (e : SubError)
  | shutDown
  deriving Repr, DecidableEq

/-- One consumer-visible event: the per-subscriber trace interface
(slices plan, Reconciliation §19.3). -/
inductive Observed where
  | entry (m : StoredMessage)
  | caughtUp
  | failed (e : SubError)
  deriving Repr, DecidableEq

structure Subscriber where
  stream : StreamName
  filters : List SubjectName
  policy : Policy
  /-- The bounded queue's buffer, oldest first. -/
  pending : List StoredMessage
  status : QueueStatus
  /-- Membership in the stream's `Set` (`:242-245`, removed at `:183` on overflow). -/
  registered : Bool
  /-- The implementation's `lastDelivered` (`:195`): advanced on enqueue, never on
  the overflowing message. -/
  lastEnqueued : StreamSeq
  /-- What the consumer has pulled so far. -/
  observed : List Observed
  deriving Repr, DecidableEq

structure SubState where
  /-- The first slice's state, unchanged. -/
  core : JSState
  /-- Ascending `SubId`. -/
  subs : List (SubId × Subscriber)
  nextId : SubId
  deriving Repr, DecidableEq

def initialSub : SubState := { core := emptyState, subs := [], nextId := 0 }

def lookupSub : List (SubId × Subscriber) → SubId → Option Subscriber
  | [], _ => none
  | (i, sub) :: rest, id => if i = id then some sub else lookupSub rest id

def updateSub : List (SubId × Subscriber) → SubId → (Subscriber → Subscriber) →
    List (SubId × Subscriber)
  | [], _, _ => []
  | (i, sub) :: rest, id, f =>
    if i = id then (i, f sub) :: updateSub rest id f else (i, sub) :: updateSub rest id f

/-- The memory interpreter's diagnostic (`:262-265`): the `Set` size, `0` for an
absent stream. -/
def subscriberCount (s : SubState) (stream : StreamName) : Nat :=
  (s.subs.filter (fun p => p.2.registered && p.2.stream == stream)).length

end EffectNatsSubstrate
