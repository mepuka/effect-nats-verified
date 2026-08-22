# Signature snapshot — public proof surface

**Snapshot:** 2026-08-22, revision 2 — second slice (T3–T7) frozen over the first slice
(T1/T2).
**Imports:** Lean core only (`leanprover/lean4:v4.33.0`); no Std/Batteries/Mathlib.
**Semantic contract:** `research/2026-08-22-first-slice-jetstream-memory-lean-model.md`
§3–§4 (corrected revision); transliteration pin `mepuka/effect-nats` @ `d06223f`.
**Axiom baseline:** every theorem below closes under at most `propext`, `Classical.choice`,
`Quot.sound` (verified with `#print axioms`).
**Status:** frozen. A statement change updates this file and the proposal in the same change;
proof bodies and proved helper lemmas may change freely.

## Revision log

- **r1** (2026-08-22): first slice — carriers, `step`, `streamInv`/`stateInv`/`Reachable`,
  validator theorems, T1, T2, two kernel-checked traces.
- **r2** (2026-08-22): second slice — adds `forSubject` (the per-subject projection;
  `lastForSubject` now reads `(forSubject …).getLast?`, definitionally the same term),
  `seqPositive`, `capacityBounded`, `keepLatest`, theorems T3–T7, and a third trace. No r1
  declaration changed type or meaning; `streamInv` is kept exactly as frozen and the new
  invariants sit beside it rather than widening it.

## Carriers and transitions

```text
abbrev StreamName  := String
abbrev SubjectName := String
abbrev StreamSeq   := Nat
abbrev PayloadHash := String

structure RawStreamConfig  -- maxMessagesPerSubject : Int (wire carrier)
structure StreamConfig     -- maxMessagesPerSubject : Nat, 0 = unlimited
inductive ConfigError      -- negativeCapacity
def validate : RawStreamConfig → Except ConfigError StreamConfig
def ConfigEq (a b : StreamConfig) : Prop   -- order-sensitive structural equality
def canonicalize : StreamConfig → StreamConfig   -- defined, unused by step

structure StoredMessage
structure StreamState
abbrev JSState := List (StreamName × StreamState)
def forSubject : List StoredMessage → SubjectName → List StoredMessage   -- r2: storage-order filter
def lastForSubject : List StoredMessage → SubjectName → Option StoredMessage
def lastSequenceFor : List StoredMessage → SubjectName → StreamSeq       -- 0 when absent

inductive Op       -- createStream | getStream | deleteStream | publish | lastMessageForSubject
inductive JSError  -- invalidConfig | streamNotFound | streamConfigConflict | subjectNotBound
                   -- | wrongLastSequence | rollupNotPermitted | noMessageForSubject
inductive Ret      -- unit | config | sequence | message
def isRollup : List (String × String) → Bool
def matchesAny : List String → String → Bool
def step : JSState → Op → Except JSError (JSState × Ret)

def streamInv : StreamState → Prop        -- r1: strictly increasing sequences, all < nextSequence
def stateInv  : JSState → Prop
inductive Reachable : JSState → Prop
def seqPositive     : StreamState → Prop  -- r2: 0 < nextSequence ∧ every stored sequence > 0
def capacityBounded : StreamState → Prop  -- r2: positive limit ⇒ ∀ subject, |forSubject| ≤ limit
def keepLatest : Nat → List StoredMessage → List StoredMessage   -- r2: spec-side "most recent n"
```

## Frozen theorems — r1

```text
-- validator soundness / typed rejection
theorem validate_ok_sound :
  validate raw = .ok c →
  c.name = raw.name ∧ c.subjects = raw.subjects ∧ c.allowRollup = raw.allowRollup
    ∧ (c.maxMessagesPerSubject : Int) = raw.maxMessagesPerSubject
theorem validate_rejects_negative :
  raw.maxMessagesPerSubject < 0 →
  validate raw = .error (.negativeCapacity raw.name raw.maxMessagesPerSubject)

-- T1
theorem createStream_idempotent :
  step s (.createStream raw) = .ok (s', r) →
  step s' (.createStream raw) = .ok (s', .unit)
theorem createStream_conflict :
  validate raw = .ok config → lookupStream s config.name = some st → st.config ≠ config →
  step s (.createStream raw) = .error (.streamConfigConflict config.name)

-- T2
theorem reachable_inv : Reachable s → stateInv s
theorem reachable_sequences_strict :
  Reachable s → lookupStream s name = some st →
  st.messages.Pairwise (fun a b => a.sequence < b.sequence)
    ∧ ∀ m ∈ st.messages, m.sequence < st.nextSequence
theorem publish_assigns :
  step s (.publish stream subject payload headers expected? now) = .ok (s', r) →
  ∃ st, lookupStream s stream = some st ∧ r = .sequence st.nextSequence
    ∧ ∃ st', lookupStream s' stream = some st' ∧ st'.nextSequence = st.nextSequence + 1

-- worked traces (kernel-checked)
theorem positive_trace : positiveTraceChecks = true
theorem rejected_trace : rejectedTraceChecks = true
```

## Frozen theorems — r2

Every per-subject statement is phrased through `forSubject`; `new` abbreviates the literal
`{ subject, sequence := st.nextSequence, payload, headers, timestampMillis := now }` spelled
out in the source.

```text
-- T3 — lastMessageForSubject
theorem lastMessage_ok_iff :
  lookupStream s stream = some st →
  ((∃ s' r, step s (.lastMessageForSubject stream subject) = .ok (s', r))
    ↔ forSubject st.messages subject ≠ [])
theorem lastMessage_absent :
  lookupStream s stream = some st → forSubject st.messages subject = [] →
  step s (.lastMessageForSubject stream subject) = .error (.noMessageForSubject stream subject)
theorem lastMessage_max :
  Reachable s → step s (.lastMessageForSubject stream subject) = .ok (s', r) →
  s' = s ∧ ∃ st m, lookupStream s stream = some st ∧ r = .message m
    ∧ m ∈ st.messages ∧ m.subject = subject
    ∧ ∀ m' ∈ st.messages, m'.subject = subject → m'.sequence ≤ m.sequence

-- T4 — compare-and-set
theorem publish_ok_iff :
  (∃ s' r, step s (.publish stream subject payload headers expected? now) = .ok (s', r))
    ↔ ∃ st, lookupStream s stream = some st
        ∧ matchesAny st.config.subjects subject = true
        ∧ (isRollup headers = true → st.config.allowRollup = true)
        ∧ ∀ e, expected? = some e → e = lastSequenceFor st.messages subject
theorem publish_cas_iff :
  lookupStream s stream = some st → matchesAny st.config.subjects subject = true →
  (isRollup headers = true → st.config.allowRollup = true) →
  ((∃ s' r, step s (.publish stream subject payload headers (some e) now) = .ok (s', r))
    ↔ e = lastSequenceFor st.messages subject)
theorem publish_cas_mismatch :
  lookupStream s stream = some st → matchesAny st.config.subjects subject = true →
  (isRollup headers = true → st.config.allowRollup = true) →
  e ≠ lastSequenceFor st.messages subject →
  step s (.publish stream subject payload headers (some e) now)
    = .error (.wrongLastSequence stream subject e (lastSequenceFor st.messages subject))
theorem lastSequenceFor_eq_zero_iff :
  Reachable s → lookupStream s stream = some st →
  (lastSequenceFor st.messages subject = 0 ↔ forSubject st.messages subject = [])

-- T5 — rollup
theorem publish_rollup_denied :
  lookupStream s stream = some st → matchesAny st.config.subjects subject = true →
  isRollup headers = true → st.config.allowRollup = false →
  step s (.publish stream subject payload headers expected? now) = .error (.rollupNotPermitted stream)
theorem publish_rollup_view :
  step s (.publish stream subject payload headers expected? now) = .ok (s', r) →
  isRollup headers = true →
  lookupStream s stream = some st → lookupStream s' stream = some st' →
  forSubject st'.messages subject = [new]
theorem publish_other_subjects_unchanged :
  step s (.publish stream subject payload headers expected? now) = .ok (s', r) →
  lookupStream s stream = some st → lookupStream s' stream = some st' → other ≠ subject →
  forSubject st'.messages other = forSubject st.messages other

-- T6 — capacity
theorem reachable_positive : Reachable s → lookupStream s name = some st → seqPositive st
theorem reachable_capacity : Reachable s → lookupStream s name = some st → capacityBounded st
theorem publish_retains_latest :
  step s (.publish stream subject payload headers expected? now) = .ok (s', r) →
  isRollup headers = false →
  lookupStream s stream = some st → lookupStream s' stream = some st' →
  forSubject st'.messages subject
    = keepLatest st.config.maxMessagesPerSubject (forSubject st.messages subject ++ [new])
theorem publish_drops_oldest :
  Reachable s →
  step s (.publish stream subject payload headers expected? now) = .ok (s', r) →
  lookupStream s stream = some st → lookupStream s' stream = some st' →
  ∀ m ∈ st.messages, m ∉ st'.messages →
    ∀ m' ∈ st'.messages, m'.subject = m.subject → m.sequence < m'.sequence

-- T7 — subject binding
theorem publish_unbound :
  lookupStream s stream = some st → matchesAny st.config.subjects subject = false →
  step s (.publish stream subject payload headers expected? now)
    = .error (.subjectNotBound stream subject)

-- worked trace (kernel-checked), mirrors conformance C3/C5/C6
theorem prune_rollup_trace : pruneRollupTraceChecks = true
```

Errors preserve state by construction (`step` returns `Except`); there is no theorem to
state, and none should be added for it. `publish_ok_iff` is the success characterisation;
`publish_unbound`, `publish_rollup_denied`, and `publish_cas_mismatch` pin *which* error each
failed gate raises, in the implementation's check order.
