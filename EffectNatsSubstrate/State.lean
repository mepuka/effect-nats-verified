import EffectNatsSubstrate.Config

/-!
# Stream state

Sequential-core state of the effect-nats memory model
(`src/internal/JetStreamMemory.ts:24-36` @ `d06223f`), minus subscribers —
those are deferred until the pending/pull semantics are frozen (proposal §4.3).

`JSState` is an association list keyed by stream name; `lookupStream` finds the
first entry, `insertStream` prepends, and `removeStream`/`updateStream` touch
every entry with the key so no hidden key-uniqueness assumption is needed.

`forSubject` is the per-subject projection of a stream's storage — the TS
`forSubject` local at `src/internal/JetStreamMemory.ts:167` — and the
observation through which every per-subject theorem (T3–T6) is stated.
-/

namespace EffectNatsSubstrate

structure StoredMessage where
  subject : SubjectName
  sequence : StreamSeq
  payload : PayloadHash
  headers : List (String × String)
  /-- Carried as data, supplied by `Op.publish`; never reasoned about. -/
  timestampMillis : Nat
  deriving Repr, DecidableEq

structure StreamState where
  config : StreamConfig
  messages : List StoredMessage
  nextSequence : StreamSeq
  deriving Repr, DecidableEq

abbrev JSState := List (StreamName × StreamState)

def emptyState : JSState := []

def lookupStream : JSState → StreamName → Option StreamState
  | [], _ => none
  | (n, st) :: rest, name => if n = name then some st else lookupStream rest name

def insertStream (s : JSState) (name : StreamName) (st : StreamState) : JSState :=
  (name, st) :: s

def removeStream : JSState → StreamName → JSState
  | [], _ => []
  | (n, st) :: rest, name =>
    if n = name then removeStream rest name else (n, st) :: removeStream rest name

def updateStream : JSState → StreamName → (StreamState → StreamState) → JSState
  | [], _, _ => []
  | (n, st) :: rest, name, f =>
    if n = name then (n, f st) :: updateStream rest name f
    else (n, st) :: updateStream rest name f

/-- The messages carrying `subject`, in storage order
(`src/internal/JetStreamMemory.ts:167`). -/
def forSubject (messages : List StoredMessage) (subject : SubjectName) : List StoredMessage :=
  messages.filter (fun m => m.subject == subject)

/-- The last stored message for a subject — the max-sequence one, given the
per-stream sortedness invariant. Mirrors `lastForSubject`
(`src/internal/JetStreamMemory.ts:54-62`), which scans from the tail. -/
def lastForSubject (messages : List StoredMessage) (subject : SubjectName) :
    Option StoredMessage :=
  (forSubject messages subject).getLast?

/-- CAS reference point: last sequence for the subject, `0` when the subject
has no message (`src/internal/JetStreamMemory.ts:148`). -/
def lastSequenceFor (messages : List StoredMessage) (subject : SubjectName) : StreamSeq :=
  match lastForSubject messages subject with
  | some m => m.sequence
  | none => 0

end EffectNatsSubstrate
