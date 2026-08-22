import EffectNatsSubstrate.Subject
import EffectNatsSubstrate.State

/-!
# Sequential transitions

`step : JSState → Op → Except JSError (JSState × Ret)` — the five non-streaming
operations of the seam (`src/internal/JetStream.ts:122-157` @ `d06223f`),
transliterated from the memory interpreter (`src/internal/JetStreamMemory.ts`).
Check order inside `publish` mirrors the implementation exactly: subject
binding, rollup permission, CAS, then commit.

Errors leave the state unchanged by construction — `step` returns `Except`, so
replaying an error keeps the prior state; there is no theorem to state.

Time is an explicit input (`Op.publish` carries `timestampMillis`); there is no
clock in `step`. A deterministic `step` is the right shape for the sequential
core; the nondeterministic `Next` relation sharing its constructors enters with
the subscriber slice, where delivery interleaving is genuinely open.
-/

namespace EffectNatsSubstrate

def rollupHeader : String := "Nats-Rollup"
def rollupSubject : String := "sub"

def headerLookup (headers : List (String × String)) (key : String) : Option String :=
  match headers.find? (fun p => p.1 == key) with
  | some p => some p.2
  | none => none

def isRollup (headers : List (String × String)) : Bool :=
  headerLookup headers rollupHeader == some rollupSubject

inductive Op where
  | createStream (raw : RawStreamConfig)
  | getStream (name : StreamName)
  | deleteStream (name : StreamName)
  | publish (stream : StreamName) (subject : SubjectName) (payload : PayloadHash)
      (headers : List (String × String)) (expectedLastSubjectSequence : Option StreamSeq)
      (timestampMillis : Nat)
  | lastMessageForSubject (stream : StreamName) (subject : SubjectName)
  deriving Repr, DecidableEq

inductive JSError where
  | invalidConfig (e : ConfigError)
  | streamNotFound (stream : StreamName)
  | streamConfigConflict (stream : StreamName)
  | subjectNotBound (stream : StreamName) (subject : SubjectName)
  | wrongLastSequence (stream : StreamName) (subject : SubjectName)
      (expected actual : StreamSeq)
  | rollupNotPermitted (stream : StreamName)
  | noMessageForSubject (stream : StreamName) (subject : SubjectName)
  deriving Repr, DecidableEq

inductive Ret where
  | unit
  | config (c : StreamConfig)
  | sequence (n : StreamSeq)
  | message (m : StoredMessage)
  deriving Repr, DecidableEq

/-- Drop the oldest `n` messages carrying `subject`, preserving everything
else. The list is sequence-sorted, so the first matches are the oldest —
mirrors the drop-set construction at `src/internal/JetStreamMemory.ts:165-172`. -/
def dropOldest : List StoredMessage → SubjectName → Nat → List StoredMessage
  | ms, _, 0 => ms
  | [], _, _ + 1 => []
  | m :: ms, subject, n + 1 =>
    if m.subject == subject then dropOldest ms subject n
    else m :: dropOldest ms subject (n + 1)

/-- Enforce `maxMessagesPerSubject`; `0` means unlimited. -/
def pruneSubject (messages : List StoredMessage) (subject : SubjectName)
    (limit : Nat) : List StoredMessage :=
  if limit == 0 then messages
  else if (forSubject messages subject).length ≤ limit then messages
  else dropOldest messages subject ((forSubject messages subject).length - limit)

/-- Rollup drops every prior message for the subject
(`src/internal/JetStreamMemory.ts:161-163`). -/
def publishBase (st : StreamState) (subject : SubjectName) (rollup : Bool) :
    List StoredMessage :=
  if rollup then st.messages.filter (fun m => !(m.subject == subject))
  else st.messages

def newMessage (st : StreamState) (subject : SubjectName) (payload : PayloadHash)
    (headers : List (String × String)) (now : Nat) : StoredMessage :=
  { subject := subject
    sequence := st.nextSequence
    payload := payload
    headers := headers
    timestampMillis := now }

/-- The committed publish: assigned sequence is the pre-state `nextSequence`. -/
def applyPublish (st : StreamState) (subject : SubjectName) (payload : PayloadHash)
    (headers : List (String × String)) (rollup : Bool) (now : Nat) :
    StreamState × StreamSeq :=
  ({ st with
      messages :=
        pruneSubject
          (publishBase st subject rollup ++ [newMessage st subject payload headers now])
          subject st.config.maxMessagesPerSubject
      nextSequence := st.nextSequence + 1 },
   st.nextSequence)

def createStep (s : JSState) (raw : RawStreamConfig) : Except JSError (JSState × Ret) :=
  match validate raw with
  | .error e => .error (.invalidConfig e)
  | .ok config =>
    match lookupStream s config.name with
    | some st =>
      if st.config = config then .ok (s, .unit)
      else .error (.streamConfigConflict config.name)
    | none =>
      .ok (insertStream s config.name
            { config := config, messages := [], nextSequence := 1 }, .unit)

def getStep (s : JSState) (name : StreamName) : Except JSError (JSState × Ret) :=
  match lookupStream s name with
  | some st => .ok (s, .config st.config)
  | none => .error (.streamNotFound name)

def deleteStep (s : JSState) (name : StreamName) : Except JSError (JSState × Ret) :=
  match lookupStream s name with
  | some _ => .ok (removeStream s name, .unit)
  | none => .error (.streamNotFound name)

def commitPublish (s : JSState) (stream : StreamName) (st : StreamState)
    (subject : SubjectName) (payload : PayloadHash)
    (headers : List (String × String)) (now : Nat) : Except JSError (JSState × Ret) :=
  .ok (updateStream s stream
        (fun _ => (applyPublish st subject payload headers (isRollup headers) now).1),
       .sequence (applyPublish st subject payload headers (isRollup headers) now).2)

def publishStep (s : JSState) (stream : StreamName) (subject : SubjectName)
    (payload : PayloadHash) (headers : List (String × String))
    (expected? : Option StreamSeq) (now : Nat) : Except JSError (JSState × Ret) :=
  match lookupStream s stream with
  | none => .error (.streamNotFound stream)
  | some st =>
    if matchesAny st.config.subjects subject then
      if isRollup headers && !st.config.allowRollup then
        .error (.rollupNotPermitted stream)
      else
        match expected? with
        | some e =>
          if e = lastSequenceFor st.messages subject then
            commitPublish s stream st subject payload headers now
          else
            .error (.wrongLastSequence stream subject e (lastSequenceFor st.messages subject))
        | none => commitPublish s stream st subject payload headers now
    else .error (.subjectNotBound stream subject)

def lastMsgStep (s : JSState) (stream : StreamName) (subject : SubjectName) :
    Except JSError (JSState × Ret) :=
  match lookupStream s stream with
  | none => .error (.streamNotFound stream)
  | some st =>
    match lastForSubject st.messages subject with
    | some m => .ok (s, .message m)
    | none => .error (.noMessageForSubject stream subject)

def step (s : JSState) : Op → Except JSError (JSState × Ret)
  | .createStream raw => createStep s raw
  | .getStream name => getStep s name
  | .deleteStream name => deleteStep s name
  | .publish stream subject payload headers expected? now =>
    publishStep s stream subject payload headers expected? now
  | .lastMessageForSubject stream subject => lastMsgStep s stream subject

end EffectNatsSubstrate
