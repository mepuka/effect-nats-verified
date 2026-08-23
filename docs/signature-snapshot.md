# Signature snapshot — public proof surface

**Snapshot:** 2026-08-22, revision 2.1 — second slice (T3–T7) frozen over the first slice
(T1/T2); r2.1 restates the traces as data (revision log). 31 frozen declarations below; the
package holds 76 non-private theorems in all.
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
- **r2.1** (2026-08-22, slices plan slice 2): traces became data — `Expect`, `TraceStep`,
  `ViewCheck`, `Trace`, `runTrace` — and the trace theorems are restated as
  `runTrace t = true` (eight traces plus `all_traces`; the former `positiveTraceChecks`,
  `rejectedTraceChecks`, `pruneRollupTraceChecks` are gone, their content redistributed). No
  T1–T7 statement changed. `Main.lean` (`lake exe effect_nats_traces`) prints `allTraces` as
  the deterministic replay fixture; it is the only module importing `Lean`.
- **r2.1 errata** (2026-08-22, Correct pass after
  `research/2026-08-22-effect-nats-substrate-vp1.md`): `configOrderTrace.mirrors` is `[]` — the
  trace mirrors no conformance case (C1 never permutes `subjects`); `mirrors` is metadata
  `runTrace` does not read. No statement changed. The header carrier's unique-key restriction
  is declared in the proposal (§3.1) rather than modeled: `headerLookup` is first-match, the
  seam's `ReadonlyMap` has one value per key.

- **r3 — proposed 2026-08-22, pending owner ratification** (slices plan slice 4, stage A): the
  subscriber layer for `TerminateOnLag` buffers over the unchanged core, stated in the section
  "Stage A (r3)" at the end of this file. Statements there are the freeze candidates; nothing in
  r1–r2.1 changes. The transliteration pin of the new modules is effect-nats `872bd7f`.

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

structure StoredMessage    -- headers : List (String × String); unique keys by seam contract
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

inductive Expect      -- r2.1: ok (r : Ret) | error (e : JSError)
structure TraceStep   -- r2.1: op, expect, replay : Bool (false = model-only, not exported)
structure ViewCheck   -- r2.1: stream, subject?, expected payload tokens of the view
structure Trace       -- r2.1: name, mirrors, steps, views
def runTrace : Trace → Bool   -- r2.1: fold step over steps, exact outcomes, then check views
def allTraces : List Trace    -- r2.1: what the exporter prints, in fixture order
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

-- worked traces (kernel-checked; r2.1 form)
theorem positive_trace : runTrace positiveTrace = true     -- C1, C3, C4
theorem rejected_trace : runTrace rejectedTrace = true     -- C1, C2 (+ model-only negative capacity)
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

-- worked traces (kernel-checked; r2.1)
theorem prune_trace         : runTrace pruneTrace = true          -- C5, C4 typed absence
theorem rollup_trace        : runTrace rollupTrace = true         -- C6
theorem rollup_denied_trace : runTrace rollupDeniedTrace = true   -- C6 gate
theorem cas_trace           : runTrace casTrace = true            -- C3 incl. expected/actual
theorem delete_trace        : runTrace deleteTrace = true         -- C10 getStream after delete; T12′ restart at 1
theorem config_order_trace  : runTrace configOrderTrace = true    -- order-sensitive ConfigEq (live finding target)
theorem all_traces          : allTraces.all runTrace = true
```

Errors preserve state by construction (`step` returns `Except`); there is no theorem to
state, and none should be added for it. `publish_ok_iff` is the success characterisation;
`publish_unbound`, `publish_rollup_denied`, and `publish_cas_mismatch` pin *which* error each
failed gate raises, in the implementation's check order.

## Stage A (r3) — proposed, pending owner ratification

Source: `research/2026-08-22-subscriber-stage-a.md` (§3–§4 representation, §9.2 obligations);
pin effect-nats `872bd7f` (`Subscriber.lean`, `SelectReplay.lean`, `Next.lean` headers cite the
lines). Prior art absorbed: `research/2026-08-22-lean-prior-art-session-automata-queues.md`
closing map B (no mechanized source replaces the project-specific state; `decide` is the stable
boundary for finite traces; structural induction + `simp`/`grind`/`omega` for the rest).

### Carriers, labels, transition (frozen with r3)

```text
abbrev SubId := Nat
inductive Policy | terminateOnLag (n : Nat)                      -- n ≥ 1 at the label boundary
inductive StartPosition | allHistory | lastPerSubject | newOnly | fromSequence n | afterSequence n
structure ConsumeOptions   -- filters, start, buffer
inductive SubError | streamNotFound stream | consumerLagged stream lastDelivered
inductive QueueStatus | opened | closing e | done e | shutDown   -- opened = Effect's Open
inductive Observed | entry m | caughtUp | failed e
structure Subscriber       -- stream filters policy pending status registered lastEnqueued observed
structure SubState         -- core : JSState, subs : List (SubId × Subscriber), nextId
def initialSub, lookupSub, updateSub, subscriberCount
def isLastOfSubject, selectReplay, replayObserved
inductive Label | op o expect | register stream opts lastEnqueued₀ id expect | pull id | unsubscribe id
def deliverOne, endOne, pullStep, newSubscriber
def afterOp, applyOp, applyRegister, applyPull, applyUnsubscribe, applyWith   -- the skeleton
def apply : SubState → Label → Option SubState := applyWith deliverOne pullStep
def Next (s l s') : Prop := apply s l = some s'
inductive ReachableSub : SubState → Prop   -- init : initialSub; step : Next
def entrySequences, visible (sub) := observed ++ pending.map entry
structure SubInv (s sub) : Prop   -- eight clauses, SubInvariants.lean
def StateInv (s) := ∀ p ∈ s.subs, SubInv s p.2
```

Assumptions named, not proved here (discharged in stage B against `EffectQueue`): Q1 a pull
drains the whole buffer; Q2 `fail` delivers the buffer then the error; Q3 `shutdown` discards the
buffer. Boundary restrictions: `messages ≥ 1`; unique header keys and non-negative capacity as in
r2.1.

### Theorem statements (freeze candidates)

```lean
-- SA1 frame
theorem reachableSub_core {s : SubState} (h : ReachableSub s) : Reachable s.core

-- SA2 / SA3 invariant and T14′-safety
theorem stateInv_reachable {s : SubState} (h : ReachableSub s) : StateInv s
theorem pending_le_capacity {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, p.2.pending.length ≤ p.2.policy.capacity

-- SA4 registration and selectReplay
theorem register_observed {s s' : SubState} {stream opts l₀ id}
    (h : apply s (.register stream opts l₀ id (.ok .unit)) = some s') :
    ∃ st, lookupStream s.core stream = some st ∧
      lookupSub s'.subs id = some (newSubscriber stream opts l₀ st.messages)
theorem selectReplay_mem {messages opts m} (h : m ∈ selectReplay messages opts) :
    m ∈ messages ∧ matchesAny opts.filters m.subject = true
theorem selectReplay_lastPerSubject {messages opts} (h : opts.start = .lastPerSubject) :
    ∀ m ∈ selectReplay messages opts,
      lastForSubject (messages.filter (fun x => matchesAny opts.filters x.subject)) m.subject = some m

-- SA5 the consumer-visible sequence (T8′/T9/T10/T11 as per-transition equations)
theorem pull_visible {s s' id sub sub'} (h : apply s (.pull id) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (ho : sub.status = .opened) : visible sub' = visible sub
theorem publish_visible {s stream subject payload headers x now seq s' id sub sub'}
    (h : apply s (.op (.publish stream subject payload headers x now) (.ok (.sequence seq))) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hr : sub.registered = true) (ho : sub.status = .opened) (hs : sub.stream = stream)
    (hm : matchesAny sub.filters subject = true) :
    (sub.pending.length < sub.policy.capacity →
        visible sub' = visible sub ++ [.entry { subject, sequence := seq, payload, headers,
                                                timestampMillis := now }]) ∧
    (sub.pending.length = sub.policy.capacity → visible sub' = visible sub ∧ sub'.registered = false)
theorem op_visible_frame {s o e s' id sub sub'} (h : apply s (.op o e) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hnm : ∀ stream subject payload headers x now, o = .publish stream subject payload headers x now →
        (sub.stream ≠ stream ∨ matchesAny sub.filters subject = false))
    (hnd : ∀ name, o ≠ .deleteStream name) : visible sub' = visible sub
theorem visible_sequences_strict {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, (entrySequences (visible p.2)).Pairwise (· < ·)

-- SA6 T12′
theorem delete_ends {s name s' id sub sub'} (h : apply s (.op (.deleteStream name) (.ok .unit)) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hr : sub.registered = true) (hs : sub.stream = name) :
    sub'.registered = false ∧
      (sub'.status = .closing (.streamNotFound name) ∨ sub'.status = .done (.streamNotFound name)) ∧
      visible sub' = visible sub
theorem create_restarts {s raw s' st} (h : apply s (.op (.createStream raw) (.ok .unit)) = some s')
    (habsent : lookupStream s.core raw.name = none) (hst : lookupStream s'.core raw.name = some st) :
    st.nextSequence = 1

-- SA7 T13′
theorem lagged_iff {s stream subject payload headers x now seq s' id sub sub' n}
    (h : apply s (.op (.publish stream subject payload headers x now) (.ok (.sequence seq))) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hp : sub.policy = .terminateOnLag n) (hr : sub.registered = true) (hs : sub.stream = stream)
    (hm : matchesAny sub.filters subject = true) :
    (sub'.status = .closing (.consumerLagged stream sub.lastEnqueued) ∨
     sub'.status = .done (.consumerLagged stream sub.lastEnqueued)) ↔ sub.pending.length = n
theorem lagged_carries_last_observed {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, ∀ stream n, p.2.observed.getLast? = some (.failed (.consumerLagged stream n)) →
      (entrySequences p.2.observed).getLast? = some n ∨
        (n = p.2.lastEnqueued ∧ ∀ m, Observed.entry m ∉ p.2.observed)

-- traces (already proved, SubTraces.lean): sa_replay_trace … sa_drain_trace, all_sub_traces,
-- w1_fails_drain, w2_fails_lag, w1_passes_replay, w2_passes_drain
```

Witnesses: the eight traces of `SubTraces.lean` (C7–C10, C13–C15, M1, and the Q1 witness);
counterexamples: W1 (one-element pull) and W2 (advance on overflow) through the same runner.
Approved edit regions after ratification: proof bodies in `SubProofs.lean` and proved helper
lemmas; changing any declaration above or a statement returns to the slice document.
