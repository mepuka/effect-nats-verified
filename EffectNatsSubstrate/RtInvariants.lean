import EffectNatsSubstrate.Runtime
import EffectNatsSubstrate.Invariants

/-!
# Stage-B1 invariants — definitions

The representation invariant of the runtime model (stage-B slice document
§12, as corrected by the Pass B probes of 2026-08-23: every clause below holds
on every reachable state of the probe families — 4 126 states — and each
clause is named by the proof site that needs it). Definitions only; the
theorems are r4 obligations (`RtInvariants` proofs, `SimProof`).

Clauses that were proposed and are **false** on reachable states, and why
(overwatch round 2, B2/B13): "a parked taker sees an empty buffer" — `offer`
appends to a queue with a parked taker and only *schedules* its release
(`Queue.ts:666-667`), so `taker ∧ buffer ≠ []` is reachable; "an overflow
decision finds the queue still open" — `closeA`/`closeB` may shut it between
`check` and `resolve`; "a registered subscriber's stream exists" — false
between a deletion's `op` and its per-subscriber `resolve`.
-/

namespace EffectNatsSubstrate

/-- The queue of one subscriber with policy capacity `cap`. -/
structure QueueInv (cap : Nat) (q : EffectQueue) : Prop where
  /-- A parked taker is cleared by `shutdown`; it can coexist with a non-empty
  buffer (the release is scheduled, not inline). -/
  takerLive : q.taker = true → q.status ≠ .shutDown
  /-- `fail` finishes an empty buffer at once; `takeAll` finishes a drained
  `closing` queue in the same step. -/
  doneEmpty : ∀ e, q.status = .done e → q.buffer = []
  /-- `fail` keeps a non-empty buffer; nothing empties it without finishing. -/
  closingNonempty : ∀ e, q.status = .closing e → q.buffer ≠ []
  shutDownClear : q.status = .shutDown → q.buffer = [] ∧ q.taker = false
  /-- T14′ on runtime states; `offer` admits only below capacity. -/
  capacity : q.buffer.length ≤ cap

structure RtSubInv (s : RtState) (r : RtSubscriber) : Prop where
  capacityPos : 1 ≤ r.policy.capacity
  queue : QueueInv r.policy.capacity r.queue
  /-- A registered subscriber's queue is open and its scope is not closing:
  `resolve` de-registers before failing, `closeA` de-registers before `closeB`. -/
  registeredOpen : r.registered = true → r.queue.status = .opened ∧ r.closeStarted = false
  /-- Between the two close steps: de-registered, not yet shut down (the pull
  guard `¬closeStarted` keeps the queue from finishing in between). -/
  closeStartedOpen : r.closeStarted = true → r.registered = false ∧ r.queue.status ≠ .shutDown
  /-- While registered and no deletion fan-out is in flight, the stream exists
  and `lastEnqueued` is below its head. -/
  registeredStream : r.registered = true →
    (∀ name, s.fanOut.map FanOut.kind ≠ some (.delete name)) →
    ∃ st, lookupStream s.core r.stream = some st ∧ r.lastEnqueued < st.nextSequence

structure FanOutInv (s : RtState) (f : FanOut) : Prop where
  /-- A subscriber is visited once. -/
  remainingNodup : f.remaining.Nodup
  remainingKnown : ∀ i, i ∈ f.remaining → (lookupRt s.subs i).isSome
  decidedNotRemaining : ∀ i b, f.decided = some (i, b) → i ∉ f.remaining
  decidedKnown : ∀ i b, f.decided = some (i, b) → (lookupRt s.subs i).isSome
  /-- An admit decision still has room when resolved, or the queue has
  finished meanwhile (then `size` read `0` and `offer` is refused): the
  `wouldSuspend` outcome is unreachable under `TerminateOnLag`. -/
  decidedRoom : ∀ i, f.decided = some (i, false) →
    ∀ r, lookupRt s.subs i = some r →
      r.queue.buffer.length < r.policy.capacity ∨ r.queue.status ≠ .opened

structure RtInv (s : RtState) : Prop where
  subs : ∀ p ∈ s.subs, RtSubInv s p.2
  shape : (s.subs.map Prod.fst).Pairwise (· < ·) ∧ ∀ p ∈ s.subs, p.1 < s.nextId
  fanOut : ∀ f, s.fanOut = some f → FanOutInv s f
  core : stateInv s.core

end EffectNatsSubstrate
