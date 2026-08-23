import EffectNatsSubstrate.Subscriber

/-!
# `EffectQueue` — the bounded Effect queue as the consumer sees it (stage B1)

Transliteration of the parts of `effect/src/Queue.ts` @ `4.0.0-rc.111` that a
`TerminateOnLag` subscription exercises, at the granularity of one Effect step
per operation (stage-B slice document §2.1–§2.2; the `Queue.ts` lines are the
design note's verified §3.1–§3.3):

- `size` is the buffer length unless the queue is finished (`sizeUnsafe`,
  `Queue.ts:1789`: `Done` → 0);
- `offer` appends to an `Open` queue and returns `true`; on any other state it
  returns `false` and changes nothing (`:645-648`). Under `TerminateOnLag` the
  size check precedes every offer, so the suspending branch (`:659`) is never
  reached — it is stage B2's subject;
- `fail` on an `Open` queue with an empty buffer finishes it at once (`done e`);
  with a non-empty buffer it becomes `closing e` and keeps the buffer
  (`failCauseUnsafe`, `:1000-1015`); on a non-open queue it is a no-op;
- `takeAll` returns the whole buffer (`takeBetween(self, 1, +∞)`, `:1297-1298`,
  `:1994-1998`) and clears it; a `closing` queue whose buffer is now empty
  finishes (`releaseCapacity`, `:2040-2047`); on a `done` queue the stored exit
  is returned (`takeUnsafe`, `:1607-1608`); on an `open` empty buffer the taker
  parks until an offer, a failure, or a shutdown;
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

/-- `offer`: append if `Open`, else `false` and no change. -/
def offer (q : EffectQueue) (m : StoredMessage) : EffectQueue × Bool :=
  match q.status with
  | .opened => ({ q with buffer := q.buffer ++ [m] }, true)
  | _ => (q, false)

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

/-- A parked taker resumes: after an offer it takes the buffer; after a failure
on the empty buffer it takes the exit; after a shutdown it is interrupted. -/
def wake (q : EffectQueue) : Option (EffectQueue × TakeResult) :=
  if !q.taker then none
  else
    match q.status with
    | .opened =>
      if q.buffer.isEmpty then none
      else some ({ q with buffer := [], taker := false }, .chunk q.buffer)
    | .done e => some ({ q with status := .shutDown, taker := false }, .exit e)
    | .shutDown => some ({ q with taker := false }, .interrupted)
    | .closing _ => none

end EffectQueue

end EffectNatsSubstrate
