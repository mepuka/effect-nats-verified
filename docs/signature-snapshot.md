# Signature snapshot — public proof surface

**Snapshot:** 2026-08-23, revision 4 — stage B1 (r4) frozen over stage A (r3.1, ratified
2026-08-22; r3.2 addition 2026-08-23) over the sequential core (r1–r2.1). The frozen surface is the
union of the sections below (r1, r2, Stage A (r3.1), Stage B1 (r4)); the package holds 230
non-private theorems in all, of which the r4 obligations are not yet proved.
**Imports:** Lean core only (`leanprover/lean4:v4.33.0`); no Std/Batteries/Mathlib.
**Semantic contract:** `research/2026-08-22-first-slice-jetstream-memory-lean-model.md`
§3–§4 (corrected revision); transliteration pins `mepuka/effect-nats` @ `d06223f` (r1–r2.1) and
`872bd7f` (stage A, r3; `research/2026-08-22-subscriber-stage-a.md`).
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

- **r3 — proposed 2026-08-22; r3.1 ratified by the owner 2026-08-22 (late night)** (slices plan slice 4, stage A): the
  subscriber layer for `TerminateOnLag` buffers over the unchanged core, stated in the section
  "Stage A (r3.1)" at the end of this file. Statements there are frozen; nothing in
  r1–r2.1 changes. The transliteration pin of the new modules is effect-nats `872bd7f`.
  **Revised 2026-08-22 to r3.1 and ratified the same night**, after the review round over `61b3663..bedc54e`
  (Standards/Spec review; `docs/reviews/assurance-review-stage-a-sa2-sa3.md` F1–F8 with its
  correction log; `research/2026-08-22-effect-nats-subscriber-stage-a-literature-referee.md`
  LR-01–08): `replayBound` and the eleven-clause `SubInv` recorded, `SubShape` added, SA4a/SA4c
  tightened (statement revision log at the end of the section), SA7's dead disjunct dropped,
  SA4d and the negative witnesses added, assumption A4 named. SA1–SA3 were proved while r3 was
  proposed — ahead of the slices plan's "frozen before proofs" gate; those proofs are evidence
  for the candidates, not of ratification.
- **r4 (2026-08-23, stage B1 frozen).** The runtime model (`EffectQueue`, `Runtime`, `RtTraces`,
  `Sim`, `RtInvariants`) and the stage-B1 obligations SB1–SB7 (`A4Inclusion`, `A4Complete`, the
  queue laws, commutation, `RtInv` preservation, the core frame, T14′ on runtime states); see the
  Stage B1 (r4) section. Frozen under the owner's standing delegation of 2026-08-23 after the Pass B
  probes (slice document increment 5).
- **r3.2 (2026-08-23, addition; no statement changed).** A ninth stage-A trace `saReplayLag` /
  `sa_replay_lag_trace` (`SubTraces.lean`): replay into a `TerminateOnLag 1` buffer, the one shape
  that can reach the live adapter's replay-through-the-queue class (ADR-0008; overwatch finding
  F12); `allSubTraces` gains it, so `all_sub_traces` and the `SubPlacements` theorems now cover
  nine traces with unchanged statements. Non-frozen additions the same day: `SubPlacements.lean`
  (acceptance sets `placementsOf`, `terminalPlacementsOf`; `gated_in_outcomes`,
  `w1_outside_outcomes`, `w2_outside_outcomes`) and the stage-B1 modules `EffectQueue`,
  `Runtime`, `RtTraces`, `Sim` (definitions and kernel-checked scenarios; their statements are
  r4 candidates, frozen only at stage B's Pass B). The exporter's `--subscriber` mode prints
  schema 2 with `freeRunning.outcomes` and `freeRunning.terminalOutcomes`.

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

## Stage A (r3.1) — frozen; ratified by the owner 2026-08-22

Source: `research/2026-08-22-subscriber-stage-a.md` (§3–§4 representation, §9.2 obligations);
pin effect-nats `872bd7f` (`Subscriber.lean`, `SelectReplay.lean`, `Next.lean` headers cite the
lines). Prior art absorbed: `research/2026-08-22-lean-prior-art-session-automata-queues.md`
closing map B (no mechanized source replaces the project-specific state; `decide` is the stable
boundary for finite traces; structural induction + `simp`/`grind`/`omega` for the rest).

### Carriers, labels, transition (frozen with r3.1)

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
def replayBound (messages opts lastEnqueued₀ nextSequence) : Bool
     -- admissible lastEnqueued₀: every replayed entry ≤ it, and it < the stream head (slice §4.2)
def afterOp, applyOp, applyRegister, applyPull, applyUnsubscribe, applyWith   -- the skeleton;
     -- register is enabled only for id = nextId, capacity ≥ 1, and replayBound
def apply : SubState → Label → Option SubState := applyWith deliverOne pullStep
def Next (s l s') : Prop := apply s l = some s'
inductive ReachableSub : SubState → Prop   -- init : initialSub; step : Next
def entrySequences, visible (sub) := observed ++ pending.map entry
structure SubInv (s sub) : Prop   -- eleven clauses, SubInvariants.lean: capacityPos, capacity,
     -- registeredOpen, registeredStream, closingNonempty, doneEmpty, shutDownClear, pendingMatch,
     -- visibleStrict, visibleBound, pendingLast (slice §9.2)
def StateInv (s) := ∀ p ∈ s.subs, SubInv s p.2
def SubShape (s) : Prop := (s.subs.map Prod.fst).Pairwise (· < ·) ∧ ∀ p ∈ s.subs, p.1 < s.nextId
```

Assumptions named, not proved here (discharged in stage B against `EffectQueue`): Q1 a pull
drains the whole buffer; Q2 `fail` delivers the buffer then the error; Q3 `shutdown` discards the
buffer. A4 (slice §2.4): stage A is a quiescent abstraction of the runtime's fan-out
interleavings — pulls and unsubscribes do not take the permit; the model's placement of whole
pulls between whole operations is assumed observationally faithful for `TerminateOnLag`, to be
discharged by the stage-B bridge. `lastEnqueued₀` is admitted within `replayBound`, the envelope
of memory's `nextSequence - 1` and live's last-replayed-or-`0`; SA4d pins memory's value. Boundary
restrictions: `messages ≥ 1`; unique header keys and non-negative capacity as in r2.1.

### Theorem statements (frozen with r3.1)

```lean
-- SA1 frame
theorem reachableSub_core {s : SubState} (h : ReachableSub s) : Reachable s.core

-- SA2 / SA3 invariant and T14′-safety
theorem stateInv_reachable {s : SubState} (h : ReachableSub s) : StateInv s
theorem pending_le_capacity {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, p.2.pending.length ≤ p.2.policy.capacity
theorem subShape_reachable {s : SubState} (h : ReachableSub s) : SubShape s
theorem sub_core_inv {s : SubState} (h : ReachableSub s) : stateInv s.core   -- T1–T7 as corollaries

-- SA4 registration and selectReplay
theorem register_observed {s s' : SubState} {stream opts l₀ id} (hs : SubShape s)
    (h : apply s (.register stream opts l₀ id (.ok .unit)) = some s') :
    ∃ st, lookupStream s.core stream = some st ∧
      lookupSub s'.subs id = some (newSubscriber stream opts l₀ st.messages)
theorem selectReplay_mem {messages opts m} (h : m ∈ selectReplay messages opts) :
    m ∈ messages ∧ matchesAny opts.filters m.subject = true
theorem selectReplay_lastPerSubject {messages opts}
    (hstrict : messages.Pairwise (fun a b => a.sequence < b.sequence))
    (h : opts.start = .lastPerSubject) :
    ∀ m ∈ selectReplay messages opts,
      lastForSubject (messages.filter (fun x => matchesAny opts.filters x.subject)) m.subject = some m
theorem memory_lastEnqueued_admissible {s : JSState} {stream : StreamName} {st : StreamState}
    (h : Reachable s) (hl : lookupStream s stream = some st) (opts : ConsumeOptions) :
    replayBound st.messages opts (st.nextSequence - 1) st.nextSequence = true      -- SA4d

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

-- SA5h the global form on the history-extended model (SubHistory.lean; proof-only auxiliary state,
-- never executed, traced, or exported — slice §9.2)
structure RegInfo          -- index : Nat (committed.length at registration), initial : List Observed
                           --   (`at` and `prefix` are Lean keywords)
structure SubStateH        -- base : SubState, committed : List (StreamName × StoredMessage), regs : List (SubId × RegInfo)
def erase (sH : SubStateH) : SubState := sH.base
def lookupReg : List (SubId × RegInfo) → SubId → Option RegInfo
def applyH : SubStateH → Label → Option SubStateH      -- apply on base, plus the history appends
def initialSubH, NextH, ReachableSubH                 -- as initialSub / Next / ReachableSub, over applyH
def liveEntries (sH : SubStateH) (id : SubId) : List StoredMessage
     -- committed.drop r.index, this subscriber's stream, matching its filters, in order
theorem applyH_erase (sH : SubStateH) (l : Label) : (applyH sH l).map erase = apply (erase sH) l
theorem erase_initialSubH : erase initialSubH = initialSub
theorem applyH_lift {sH : SubStateH} {l : Label} {s' : SubState} (h : ReachableSubH sH)
    (hstep : apply (erase sH) l = some s') : ∃ sH', applyH sH l = some sH' ∧ erase sH' = s'   -- AV2, one step
theorem reachableSub_lift {s : SubState} (h : ReachableSub s) : ∃ sH, ReachableSubH sH ∧ erase sH = s
theorem visible_global {sH : SubStateH} (h : ReachableSubH sH) :
    ∀ p ∈ sH.base.subs, ∀ r, lookupReg sH.regs p.1 = some r → p.2.registered = true →
      visible p.2 = r.initial ++ (liveEntries sH p.1).map Observed.entry
theorem entries_committed {sH : SubStateH} (h : ReachableSubH sH) :
    ∀ p ∈ sH.base.subs, ∀ m, Observed.entry m ∈ visible p.2 → (p.2.stream, m) ∈ sH.committed

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
    (hreach : ReachableSub s)
    (h : apply s (.op (.publish stream subject payload headers x now) (.ok (.sequence seq))) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hp : sub.policy = .terminateOnLag n) (hr : sub.registered = true) (hs : sub.stream = stream)
    (hm : matchesAny sub.filters subject = true) :
    (sub'.status = .closing (.consumerLagged stream sub.lastEnqueued) ∨
     sub'.status = .done (.consumerLagged stream sub.lastEnqueued)) ↔ sub.pending.length = n
theorem lagged_carries_last_observed {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, ∀ stream n, p.2.observed.getLast? = some (.failed (.consumerLagged stream n)) →
      (entrySequences p.2.observed).getLast? = some n

-- traces (already proved, SubTraces.lean): sa_replay_trace … sa_drain_trace, all_sub_traces,
-- w1_fails_drain, w2_fails_lag, w1_passes_replay, w2_passes_drain
-- negative witnesses (slice §7, by decide): all_sub_negatives — pull on an empty open buffer,
-- register with terminateOnLag 0, pull/unsubscribe of a shutDown or unknown id, an op whose
-- expectation disagrees with step, registration on a missing stream (state unchanged)
```

Witnesses: the eight traces of `SubTraces.lean` (C7–C10, C13–C15, M1, and the Q1 witness);
counterexamples: W1 (one-element pull) and W2 (advance on overflow) through the same runner.
Approved edit regions after ratification: proof bodies in `SubProofs.lean`, `SubReachable.lean`,
`SubStatements.lean`, and — since the cleanup lane moved helper lemmas there — `SubCore.lean` and
`SubHistory.lean`, plus proved helper lemmas; changing any declaration above or a statement
returns to the slice document.

### Statement revision log (r3 proposed → r3.1 ratified)

- `register_observed` — old: no state hypothesis; new: `(hs : SubShape s)`. Missing assumption:
  `lookupSub` returns the first match, so a `subs` already holding the key `nextId` (unreachable,
  but expressible) makes the bare statement false. `SubShape` is the minimal hypothesis;
  `subShape_reachable` gives the reachable corollary.
- `selectReplay_lastPerSubject` — old: no ordering hypothesis; new: `hstrict` (strictly increasing
  stored sequences). Missing assumption: `isLastOfSubject` compares by `sequence`, so two stored
  messages with one sequence (unreachable, but expressible) let a non-last message pass. Reachable
  cores satisfy `hstrict` (`reachable_sequences_strict`).
- `lagged_carries_last_observed` — old: a second disjunct for an entry-free history; new: dropped.
  Dead under `capacityPos` and `pendingLast`: overflow needs `pending ≠ []`, whose last sequence is
  `lastEnqueued`, and those entries are pulled before the failure is.
- Added: `subShape_reachable`, `sub_core_inv`, `memory_lastEnqueued_admissible` (SA4d),
  `all_sub_negatives`; `replayBound` and `SubShape` in the carriers block; the SA5h block
  (history-extended model, slice §9.2 — the global T8′ form the Pass A text stated, now over an
  Abadi–Lamport history variable with an erasure theorem). Downstream: none of SA1–SA3 changes.
- `lagged_iff` — **post-ratification amendment (2026-08-22, late night), approved by the owner
  the same night**: old: no state hypothesis; new: `(hreach : ReachableSub s)`. The
  explicit-premise helper `lagged_iff_of_open` (`status = opened`, `pending.length ≤ n` in
  place of reachability) landed with the cleanup lane; `lagged_iff` is its corollary. Missing assumption:
  without it a registered subscriber already in `closing (consumerLagged …)` — unreachable by
  `registeredOpen`, but expressible — satisfies the left side with `pending.length < n`, and an
  over-full buffer — unreachable by `capacity` — overflows with `pending.length ≠ n`. The
  reachable form is the T13′ statement of the slice document (§9.2).
- Representation details fixed while proving: `RegInfo`'s fields are `index`/`initial` (`at`
  and `prefix` are Lean keywords); `applyH_lift`'s reachability hypothesis is unused by its
  proof and bound as `_h` (type unchanged); the negative witnesses carry one extra case,
  `register-inadmissible-lastEnqueued`, exercising `replayBound`.
- **Proved 2026-08-22 (late night), the commit after ratification:** every statement of this
  section — SA1–SA4 (`reachableSub_core`, `stateInv_reachable`, `pending_le_capacity`,
  `subShape_reachable`, `sub_core_inv`, `register_observed`, `selectReplay_mem`,
  `selectReplay_lastPerSubject`, `memory_lastEnqueued_admissible`), SA5 (`pull_visible`,
  `publish_visible`, `op_visible_frame`, `visible_sequences_strict`), SA6 (`delete_ends`,
  `create_restarts`), SA7 (`lagged_iff`, `lagged_carries_last_observed`), the traces and
  negative witnesses (`all_sub_traces`, `w1_fails_drain`, `w2_fails_lag`, `all_sub_negatives`),
  and SA5h (`erase_initialSubH`, `applyH_erase`, `applyH_lift`, `reachableSub_lift`,
  `visible_global`, `entries_committed`) — closes under the standard axioms
  (`#print axioms`; `erase_initialSubH` under none). Modules: `SubReachable` (the one
  `ReachableSub` induction, `reachableSub_all`, the shape theorem), `SubStatements` (SA4–SA7,
  the lag invariant `LagInv`, the negatives), `SubHistory` (SA5h through the ledger invariant
  `HistInv`). SA7 goes through `LagInv` (a separate per-subscriber predicate proved with
  `reachableSub_all`, not a widening of `SubInv`).


## Stage B1 (r4) — frozen 2026-08-23 under the owner's standing delegation

- **Status:** frozen 2026-08-23 by the Claude lane under the owner's delegation of 2026-08-23
  ("none of that required escalation … get everything else done"), recorded in
  `research/2026-08-23-effect-nats-lanes-plan.md`; the owner may reopen any statement at the
  next check-in. Pass A ratified by the owner 2026-08-23
  (`research/2026-08-23-subscriber-stage-b.md`, increments 1–2); representation, statement, and
  the Pass B probes in increments 3–5 of the same document.
- **Pin:** the runtime model transliterates `src/internal/JetStreamMemory.ts` @ `bec02ac`
  (subscriber path byte-identical to `872bd7f`) and `effect/src/Queue.ts` @ `4.0.0-rc.111`.
- **Scope:** `TerminateOnLag` only; `PullWindow`'s suspended offers are `wouldSuspend`, an
  outcome the runtime model cannot take (stage B2). Environment assumptions E1–E5 of the slice
  document §2.4 are kept, not discharged.
- **Probe record (Pass B):** every candidate statement was run against an exhaustive enumeration
  of reachable runtime states in four families (129 + 3 801 + 90 + 106 states; one and two
  subscribers, capacities 1–2, two to three publishes, a deletion, all scope-closure steps):
  no stuck consumer, every `RtInv` clause true, `wouldSuspend` unreachable, and for every
  quiescent state a stage-A witness with its serial sequence, all its chunk histories and its
  subscriber count (`research/logs/rt_probe9.lean`; the overwatch's `rt_probe{,2..8}.lean` found
  the three definition defects and four false clauses this freeze corrected — slice document
  increment 5).

### Carriers, labels, transition (frozen with r4)

```text
-- EffectQueue.lean
structure EffectQueue where buffer : List StoredMessage; status : QueueStatus; taker : Bool
inductive EffectQueue.OfferResult | accepted | refused | wouldSuspend
inductive EffectQueue.TakeResult | chunk (ms : List StoredMessage) | exit (e : SubError) | parked | interrupted
def EffectQueue.empty : EffectQueue
def EffectQueue.size (q : EffectQueue) : Nat
def EffectQueue.offer (cap : Nat) (q : EffectQueue) (m : StoredMessage) : EffectQueue × OfferResult
def EffectQueue.fail (q : EffectQueue) (e : SubError) : EffectQueue
def EffectQueue.shutdown (_q : EffectQueue) : EffectQueue
def EffectQueue.takeAll (q : EffectQueue) : EffectQueue × TakeResult
def EffectQueue.wake (q : EffectQueue) : Option (EffectQueue × TakeResult)
-- Runtime.lean
inductive Outcome | admitted | overflowed | skipped | ended
inductive FanKind | publish (stream : StreamName) (m : StoredMessage) (expectedLast : Option StreamSeq) | delete (name : StreamName)
structure FanOut where kind : FanKind; remaining : List SubId; decided : Option (SubId × Bool); visited : List (SubId × Outcome)
structure RtSubscriber where stream : StreamName; filters : List SubjectName; policy : Policy; registered : Bool;
  lastEnqueued : StreamSeq; queue : EffectQueue; chunks : History; closeStarted : Bool
structure RtState where core : JSState; subs : List (SubId × RtSubscriber); nextId : SubId; fanOut : Option FanOut
def initialRt : RtState
def lookupRt : List (SubId × RtSubscriber) → SubId → Option RtSubscriber
def updateRt : List (SubId × RtSubscriber) → SubId → (RtSubscriber → RtSubscriber) → List (SubId × RtSubscriber)
def RtSubscriber.erase (r : RtSubscriber) : Subscriber        -- observed := r.chunks.flatten
def eraseRt (s : RtState) : SubState
def rtHistory (s : RtState) (id : SubId) : History
inductive RtLabel | op (o : Op) (expect : Expect) | register (stream) (opts) (lastEnqueued₀) (id) (expect)
  | check (id : SubId) | resolve (id : SubId) | endFanOut | pull (id : SubId) | wake (id : SubId)
  | closeA (id : SubId) | closeB (id : SubId)
def fanOutIds (s : RtState) (stream : StreamName) (subject : SubjectName) : List SubId
def deleteIds (s : RtState) (name : StreamName) : List SubId
def rtOp, rtRegister, rtCheck, rtResolve, rtEndFanOut, rtPull, rtWake, rtCloseA, rtCloseB   -- as in Runtime.lean
def rtStep (s : RtState) : RtLabel → Option RtState
def RtNext (s : RtState) (l : RtLabel) (s' : RtState) : Prop := rtStep s l = some s'
inductive ReachableRt : RtState → Prop | init | step
-- RtTraces.lean
structure RtTrace where name : String; steps : List RtLabel; finalHistories : List (SubId × History)
def runRtSteps : RtState → List RtLabel → Option RtState
def finalRt (t : RtTrace) : RtState
def runRtTrace (t : RtTrace) : Bool
def runLabels : SubState → List Label → Option SubState
def allRtTraces : List RtTrace          -- caseBefore, caseBetween, caseAfter, counterexample
-- Sim.lean
def rtSerial : List RtLabel → List Label
def labelSerial : List Label → List Label
def abstractHistoryFrom (id : SubId) : SubState → History → List Label → Option History
def abstractHistory (labels : List Label) (id : SubId) : Option History
def A4Inclusion : Prop      -- as in Sim.lean (serial sequence, chunk histories, subscriber counts)
def A4Complete : Prop       -- as in Sim.lean (membership in historiesWith apply t id)
-- SubPlacements.lean (r3.2 definitions now read by frozen statements)
abbrev History := List (List Observed)
def appended, afterLabel, pullsAtGap, outcomesFrom, historiesFrom, subIds, labelsWithoutPulls,
    historiesWith, placementsOf, terminalPlacementsOf, gatedHistory
-- RtInvariants.lean (proof-side predicate whose clauses are frozen, like SubInv)
structure QueueInv (cap : Nat) (q : EffectQueue) : Prop  -- takerLive, doneEmpty, closingNonempty, shutDownClear, capacity
structure RtSubInv (s : RtState) (r : RtSubscriber) : Prop -- capacityPos, queue, registeredOpen, closeStartedOpen, registeredStream
structure FanOutInv (s : RtState) (f : FanOut) : Prop    -- remainingNodup, remainingKnown, decidedNotRemaining, decidedKnown, decidedRoom
structure RtInv (s : RtState) : Prop                     -- subs, shape, fanOut, core
```

### Theorem statements (frozen with r4)

Stated in the named modules; proof bodies and proved helper lemmas are the only edits allowed.

```lean
-- EffectQueueLaws.lean (SB1: Q1–Q3 as theorems)
theorem takeAll_drains (q : EffectQueue) (h : q.status = .opened) (hne : q.buffer ≠ []) :
    q.takeAll = ({ q with buffer := [] }, .chunk q.buffer)
theorem takeAll_closing (q : EffectQueue) (e : SubError) (h : q.status = .closing e) (hne : q.buffer ≠ []) :
    q.takeAll = ({ q with buffer := [], status := .done e }, .chunk q.buffer)
theorem fail_empty (q : EffectQueue) (e : SubError) (h : q.status = .opened) (hb : q.buffer = []) :
    q.fail e = { q with status := .done e }
theorem fail_nonempty (q : EffectQueue) (e : SubError) (h : q.status = .opened) (hb : q.buffer ≠ []) :
    q.fail e = { q with status := .closing e }
theorem exit_after_drain (q : EffectQueue) (e : SubError) (h : q.status = .done e) :
    q.takeAll = ({ q with status := .shutDown }, .exit e)
theorem shutdown_clears (q : EffectQueue) : q.shutdown.buffer = [] ∧ q.shutdown.status = .shutDown
theorem size_eq_length (q : EffectQueue) (h : q.status = .opened ∨ ∃ e, q.status = .closing e) :
    q.size = q.buffer.length
theorem offer_admits (cap : Nat) (q : EffectQueue) (m : StoredMessage) (h : q.status = .opened)
    (hr : q.buffer.length < cap) : q.offer cap m = ({ q with buffer := q.buffer ++ [m] }, .accepted)
theorem offer_refused (cap : Nat) (q : EffectQueue) (m : StoredMessage) (h : q.status ≠ .opened) :
    q.offer cap m = (q, .refused)

-- RtCommute.lean (SB2)
def bindStep (s : RtState) (a b : RtLabel) : Option RtState := (rtStep s a).bind (fun s' => rtStep s' b)
theorem commute_consumer_publisher (s : RtState) (hinv : RtInv s) (i j : SubId) (hij : i ≠ j)
    (c p : RtLabel) (hc : c = .pull j ∨ c = .wake j ∨ c = .closeA j ∨ c = .closeB j)
    (hp : p = .check i ∨ p = .resolve i) : bindStep s c p = bindStep s p c
theorem commute_consumers (s : RtState) (hinv : RtInv s) (i j : SubId) (hij : i ≠ j)
    (c c' : RtLabel) (hc : c = .pull i ∨ c = .wake i ∨ c = .closeA i ∨ c = .closeB i)
    (hc' : c' = .pull j ∨ c' = .wake j ∨ c' = .closeA j ∨ c' = .closeB j) : bindStep s c c' = bindStep s c' c

-- RtReachable.lean (SB3, SB6, SB7)
theorem rtInv_reachable {s : RtState} (h : ReachableRt s) : RtInv s
theorem core_frame {s s' : RtState} {l : RtLabel} (h : rtStep s l = some s') (hl : ∀ o e, l ≠ .op o e) :
    s'.core = s.core
theorem core_reachable {s : RtState} (h : ReachableRt s) : Reachable s.core
theorem pending_le_capacity_rt {s : RtState} (h : ReachableRt s) :
    ∀ p ∈ s.subs, p.2.queue.buffer.length ≤ p.2.policy.capacity

-- SimProof.lean (SB4, SB5)
theorem a4_inclusion : A4Inclusion
theorem a4_complete : A4Complete
```

Witnesses already proved (`RtTraces.lean`, `Sim.lean`, frozen names): `rt_before_trace`,
`rt_between_trace`, `rt_after_trace`, `rt_counterexample_trace`, `rt_cases_admitted`,
`rt_counterexample_admitted`, `wrong_linearization_differs`, `right_linearization_agrees`,
`all_rt_traces`, `counterexample_inclusion_witness`, `counterexample_wrong_witness`.

Approved edit regions after this freeze: the four new proof modules named above and proved
helper lemmas anywhere under `EffectNatsSubstrate/`; a change to any declaration listed here
returns to the slice document with an old/new entry in the statement revision log below.
Axiom policy unchanged (`propext`, `Classical.choice`, `Quot.sound`); no `set_option`; `decide`
only on concrete data.

### Statement revision log (r4)

- 2026-08-23, at the freeze: the Pass B probes changed three definitions before any statement
  was frozen (`EffectQueue.wake` on `closing`; `EffectQueue.offer` capacity-aware with
  `wouldSuspend`; `rtPull`/`rtWake` disabled once `closeStarted`), and four draft `RtInv`
  clauses (the parked-taker clause, `closeStartedOpen`, the overflow-decision clause dropped,
  `registeredStream` exempting a deletion fan-out); `A4Inclusion` gained the subscriber-count
  conjunct; the cslib `IsSimulation` block was removed from `Sim.lean` (not a statement). None of
  these is a post-freeze change.
