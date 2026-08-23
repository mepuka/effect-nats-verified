import EffectNatsSubstrate.Subscriber

/-!
# `EffectQueue` — the bounded Effect queue as the consumer sees it (stage B1)

Transliteration of the parts of `effect/src/Queue.ts` @ `4.0.0-rc.111` that a
`TerminateOnLag` subscription exercises, at the granularity of one Effect step
per operation (stage-B slice document §2.1–§2.2; the `Queue.ts` lines are the
design note's verified §3.1–§3.3):

- `size` is the buffer length unless the queue is finished (`sizeUnsafe`,
  `Queue.ts:1789`: `Done` → 0);
- `offer` appends to an `Open` queue with room and reports `accepted`; on any
  other state it reports `refused` and changes nothing (`:645-648`); at capacity
  under the default `"suspend"` strategy the real `offer` parks the publisher
  (`:649`, `:659`; `Queue.bounded(n)` is `make({ capacity: n })`, `:500`, `:458`)
  — the model reports `wouldSuspend` and the runtime step that would take it is
  disabled, so the B1/B2 boundary is explicit: under `TerminateOnLag` the size
  check precedes every offer and `wouldSuspend` is unreachable (an `RtInv`
  clause); stage B2 gives it a transition;
- `fail` on an `Open` queue with an empty buffer finishes it at once (`done e`);
  with a non-empty buffer it becomes `closing e` and keeps the buffer
  (`failCauseUnsafe`, `:1000-1015`); on a non-open queue it is a no-op;
- `takeAll` returns the whole buffer (`takeBetween(self, 1, +∞)`, `:1297-1298`,
  `:1994-1998`) and clears it; a `closing` queue whose buffer is now empty
  finishes (`releaseCapacity`, `:2040-2047` — which is also why an empty
  `closing` queue never exists: the finalisation happens in the same step as
  the emptying); on a `done` queue the stored exit is returned (`takeUnsafe`,
  `:1607-1608`); on an `open` empty buffer the taker parks until an offer, a
  failure, or a shutdown. A parked taker is resumed by the scheduled release an
  `offer` queues (`:667`, `:1969-1975`, `releaseTakers` `:1955-1967`, which
  returns early only on `Done`) — so it also resumes on a `closing` queue, takes
  the kept buffer, and the queue finishes;
- `shutdown` clears the buffer and finishes the queue (`:1191-1210`); the
  consumer fiber whose scope closed is interrupted, so nothing is observed after.

`QueueStatus` is stage A's: `opened`/`closing e`/`done e`/`shutDown` —
`shutDown` is `Done` with the interrupt exit, `done e` is `Done` with the
failure `e`. The buffer is stage A's `pending` list, oldest first, so the
erasure to stage A is a projection.
-/

namespace EffectNatsSubstrate

structure EffectQueue where
  buffer : List StoredMessage
  status : QueueStatus
  /-- A `takeAll` parked on an open empty buffer. -/
  taker : Bool
  deriving Repr, DecidableEq

namespace EffectQueue

def empty : EffectQueue := { buffer := [], status := .opened, taker := false }

/-- `sizeUnsafe`: buffered items only; `0` once finished. -/
def size (q : EffectQueue) : Nat :=
  match q.status with
  | .done _ => 0
  | .shutDown => 0
  | _ => q.buffer.length

/-- What one `offer` did. -/
inductive OfferResult where
  | accepted
  /-- The queue is not `Open`: `false`, no change. -/
  | refused
  /-- At capacity: the real offer would park the publisher (stage B2). -/
  | wouldSuspend
  deriving Repr, DecidableEq

/-- `offer` against the queue's capacity. -/
def offer (cap : Nat) (q : EffectQueue) (m : StoredMessage) : EffectQueue × OfferResult :=
  match q.status with
  | .opened =>
    if q.buffer.length < cap then ({ q with buffer := q.buffer ++ [m] }, .accepted)
    else (q, .wouldSuspend)
  | _ => (q, .refused)

/-- `fail`: `done` on an empty buffer, `closing` on a non-empty one; no-op
unless `Open`. -/
def fail (q : EffectQueue) (e : SubError) : EffectQueue :=
  match q.status with
  | .opened => if q.buffer.isEmpty then { q with status := .done e } else { q with status := .closing e }
  | _ => q

/-- `shutdown`: clear and finish; a parked taker is interrupted with its fiber. -/
def shutdown (_q : EffectQueue) : EffectQueue :=
  { buffer := [], status := .shutDown, taker := false }

/-- What one `takeAll` yields. -/
inductive TakeResult where
  /-- The whole buffer, as one chunk. -/
  | chunk (ms : List StoredMessage)
  /-- The stored failure exit; the consumer fiber ends. -/
  | exit (e : SubError)
  /-- Nothing yet: the taker parks. -/
  | parked
  /-- The fiber was interrupted (its scope closed); nothing is observed. -/
  | interrupted
  deriving Repr, DecidableEq

/-- `takeAll` on a queue with no parked taker. -/
def takeAll (q : EffectQueue) : EffectQueue × TakeResult :=
  match q.status with
  | .shutDown => (q, .interrupted)
  | .done e => ({ q with status := .shutDown }, .exit e)
  | .opened =>
    if q.buffer.isEmpty then ({ q with taker := true }, .parked)
    else ({ q with buffer := [] }, .chunk q.buffer)
  | .closing e =>
    if q.buffer.isEmpty then (q, .interrupted)
    else ({ q with buffer := [], status := .done e }, .chunk q.buffer)

/-- A parked taker resumes: after an offer it takes the buffer (and, if the
queue was failed meanwhile, finishes it — `releaseTakers` resumes on `Closing`
too); after a failure on the empty buffer it takes the exit. `shutdown` clears
the taker, so no parked taker survives a shutdown. -/
def wake (q : EffectQueue) : Option (EffectQueue × TakeResult) :=
  if !q.taker then none
  else
    match q.status with
    | .opened =>
      if q.buffer.isEmpty then none
      else some ({ q with buffer := [], taker := false }, .chunk q.buffer)
    | .closing e =>
      if q.buffer.isEmpty then none
      else some ({ q with buffer := [], status := .done e, taker := false }, .chunk q.buffer)
    | .done e => some ({ q with status := .shutDown, taker := false }, .exit e)
    | .shutDown => none

end EffectQueue

end EffectNatsSubstrate
