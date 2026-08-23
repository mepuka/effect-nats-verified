import EffectNatsSubstrate.SubStatements
import EffectNatsSubstrate.SubPlacements

/-!
# The law layer over stage A's parametric skeleton (packet L7a)

`Next.lean:100-176` states the transition function as `applyWith deliver pull`, with the fan-out
step and the pull step as parameters; `apply := applyWith deliverOne pullStep` is the model. This
module names what stage A actually *assumes* about those two parameters — `DeliverLaws` and
`PullLaws` — proves the concrete steps satisfy them, and re-derives one stage-A theorem over the
laws alone, so an alternative representation of `deliver`/`pull` inherits it (lanes plan, decision
P6).

Every law here is a **frame** condition on one subscriber: what a step may not change (`stream`,
`filters`), how `observed` may move (only grow), and when a step is a no-op or disabled. No law
constrains `pending`, `status`, `lastEnqueued`, `registered`, or `policy`; the inventory that
justifies each law, one named consumer at a time, is the L7a Part-1 record.

**The finding this module carries.** The frame laws do *not* discriminate the slice document's two
deliberately wrong models (`research/2026-08-22-subscriber-stage-a.md` §7). `pullStepW1`
(one-element pull) satisfies every `PullLaws` clause and `deliverOneW2` (`lastEnqueued` advanced on
the overflowing message) satisfies every `DeliverLaws` clause — both proved below, and each paired
with its trace-level exclusion. The one law-shaped fact that *would* exclude W1 is queue fact Q1's
drain equation, which pins `pull` down to its definition on `.opened` and so is not a law but the
definition; certifying a replacement `pull` is a simulation obligation (L7b), not a law obligation.
Frame laws alone do not certify a replacement.

Nothing frozen changes here: `Next.lean`, `SubTraces.lean`, `SubProofs.lean` and the frozen
statements are untouched, and `op_visible_frame_is_instance` checks that the re-derived statement is
literally `SubStatements.op_visible_frame`'s.
-/

namespace EffectNatsSubstrate

/-! ## The laws -/

/-- What a fan-out step may do to one subscriber. `not_target` and `not_matching` are the two
law-usable halves of `deliverOne_skip` (`SubProofs.lean:383`); `observed_grows` is what makes
`SubPlacements.appended` (`SubPlacements.lean:42`) — a `drop` of the earlier length — mean "the
events this transition appended". -/
structure DeliverLaws (deliver : StreamName → StoredMessage → Subscriber → Subscriber) : Prop where
  /-- A delivery never re-homes a subscriber (`SubInv.registeredStream` reads `sub.stream`). -/
  stream_stable : ∀ st m a, (deliver st m a).stream = a.stream
  /-- A delivery never rewrites the filters (`SubInv.pendingMatch` reads `sub.filters`). -/
  filters_stable : ∀ st m a, (deliver st m a).filters = a.filters
  /-- A delivery only ever appends to what the consumer has already seen. -/
  observed_grows : ∀ st m a, ∃ suffix, (deliver st m a).observed = a.observed ++ suffix
  /-- A subscriber of another stream is untouched. -/
  not_target : ∀ st m a, (a.stream = st → False) → deliver st m a = a
  /-- A subscriber whose filters reject the subject is untouched. -/
  not_matching : ∀ st m a, matchesAny a.filters m.subject = false → deliver st m a = a

/-- What a pull step may do to its subscriber. The four clauses are frame conditions; how much a
pull drains is deliberately not among them (see the module header). -/
structure PullLaws (pull : Subscriber → Option Subscriber) : Prop where
  /-- A pull never re-homes its subscriber. -/
  stream_stable : ∀ a a', pull a = some a' → a'.stream = a.stream
  /-- A pull never rewrites the filters. -/
  filters_stable : ∀ a a', pull a = some a' → a'.filters = a.filters
  /-- A pull only ever appends to what the consumer has already seen. -/
  observed_grows : ∀ a a', pull a = some a' → ∃ suffix, a'.observed = a.observed ++ suffix
  /-- A shut-down subscriber is quiescent (`ApplyLemmas.pullStep_third_none`'s base case). -/
  shutDown_disabled : ∀ a, a.status = .shutDown → pull a = none

/-! ## The model discharges them -/

/-- The obligation an alternative fan-out representation would also have to discharge. -/
theorem deliverOne_laws : DeliverLaws deliverOne := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro st m a
    unfold deliverOne
    repeat' split
    all_goals rfl
  · intro st m a
    unfold deliverOne
    repeat' split
    all_goals rfl
  · intro st m a
    refine ⟨[], ?_⟩
    rw [List.append_nil]
    unfold deliverOne
    repeat' split
    all_goals rfl
  · intro st m a h
    unfold deliverOne
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact h hc.1.1
  · intro st m a h
    unfold deliverOne
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.2] at h
    cases h

/-- The obligation an alternative pull representation would also have to discharge. -/
theorem pullStep_laws : PullLaws pullStep := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a a' h
    rcases pullStep_ok_eq h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  · intro a a' h
    rcases pullStep_ok_eq h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  · intro a a' h
    rcases pullStep_ok_eq h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · intro a h
    unfold pullStep
    rw [h]

/-! ## The wrong models satisfy the laws — the L7a finding

The packet's sketch expected `¬ PullLaws pullStepW1`. It is false: W1 differs from the model in
*how much* a pull drains, which no frame law mentions. Rather than invent a law to exclude it, the
negation is proved. -/

/-- W1 (one-element pull, `SubTraces.lean:84`) satisfies every law in `PullLaws`. -/
theorem pullStepW1_laws : PullLaws pullStepW1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a a' h
    unfold pullStepW1 at h
    split at h <;> cases h <;> rfl
  · intro a a' h
    unfold pullStepW1 at h
    split at h <;> cases h <;> rfl
  · intro a a' h
    unfold pullStepW1 at h
    split at h <;> (try cases h) <;> exact ⟨_, rfl⟩
  · intro a h
    unfold pullStepW1
    rw [h]

/-- W2 (`lastEnqueued` advanced on the overflowing message, `SubTraces.lean:101`) satisfies every
law in `DeliverLaws`: it changes only `registered`, `status`, `pending`, and `lastEnqueued`, none of
which any law constrains. -/
theorem deliverOneW2_laws : DeliverLaws deliverOneW2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro st m a
    unfold deliverOneW2
    repeat' split
    all_goals rfl
  · intro st m a
    unfold deliverOneW2
    repeat' split
    all_goals rfl
  · intro st m a
    refine ⟨[], ?_⟩
    rw [List.append_nil]
    unfold deliverOneW2
    repeat' split
    all_goals rfl
  · intro st m a h
    unfold deliverOneW2
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact h hc.1.1
  · intro st m a h
    unfold deliverOneW2
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.2] at h
    cases h

/-- The finding as one statement: W1 is law-abiding, and is excluded only by the trace-level
acceptance set of `sa-drain` (`SubPlacements.lean:131`). -/
theorem w1_law_abiding_but_trace_excluded :
    PullLaws pullStepW1 ∧
      (historiesWith (applyWith deliverOne pullStepW1) saDrain 0).any
        (fun h => !(historiesWith apply saDrain 0).contains h) = true :=
  ⟨pullStepW1_laws, w1_outside_outcomes⟩

/-- The same for W2 on `sa-lag` (`SubPlacements.lean:138`): satisfying every frame law is not a
certificate. -/
theorem w2_law_abiding_but_trace_excluded :
    DeliverLaws deliverOneW2 ∧
      (historiesWith (applyWith deliverOneW2 pullStep) saLag 0).any
        (fun h => !(historiesWith apply saLag 0).contains h) = true :=
  ⟨deliverOneW2_laws, w2_outside_outcomes⟩

/-! ## One generic re-derivation (the proof of concept)

`SubStatements.op_visible_frame` (`:177`) — an operation that is neither a publish this subscriber
matches nor a deletion leaves what the subscriber sees unchanged — restated over
`applyWith deliver pull` and proved from `DeliverLaws` alone. -/

/-- `SubStatements.afterOp_publish_sub` (`:31`) over the skeleton: the subscriber a publish leaves
behind is the parameter applied to the old one. No law needed. -/
theorem afterOp_publish_sub_generic
    {deliver : StreamName → StoredMessage → Subscriber → Subscriber}
    {s : SubState} {core' : JSState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {x : Option StreamSeq} {now : Nat}
    {seq : StreamSeq} {id : SubId} {sub sub' : Subscriber}
    (hb : lookupSub s.subs id = some sub)
    (ha : lookupSub (afterOp deliver s core' (.publish stream subject payload headers x now)
      (.sequence seq)).subs id = some sub') :
    sub' = deliver stream (publishedMessage subject seq payload headers now) sub := by
  simp only [afterOp] at ha
  rw [lookupSub_map, hb] at ha
  exact (Option.some.inj ha).symm

/-- The generic form of `SubStatements.op_visible_frame`: it needs exactly two laws, `not_target`
and `not_matching`, one per disjunct of `hnm`. -/
theorem op_visible_frame_generic
    {deliver : StreamName → StoredMessage → Subscriber → Subscriber}
    {pull : Subscriber → Option Subscriber} (hd : DeliverLaws deliver)
    {s : SubState} {o : Op} {e : Expect} {s' : SubState} {id : SubId}
    {sub sub' : Subscriber} (h : applyWith deliver pull s (.op o e) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hnm : ∀ stream subject payload headers x now,
        o = .publish stream subject payload headers x now →
        (sub.stream ≠ stream ∨ matchesAny sub.filters subject = false))
    (hnd : ∀ name, o ≠ .deleteStream name) : visible sub' = visible sub := by
  cases e with
  | ok r =>
    obtain ⟨core', -, rfl⟩ :=
      applyOp_ok_eq (deliver := deliver) (show applyOp deliver s o (.ok r) = some s' from h)
    cases o with
    | publish stream subject payload headers x now =>
      cases r with
      | sequence seq =>
        obtain rfl := afterOp_publish_sub_generic hb ha
        rcases hnm stream subject payload headers x now rfl with hne | hfalse
        · rw [hd.not_target _ _ _ hne]
        · rw [hd.not_matching _ _ _ hfalse]
      | unit => exact visible_eq_of_subs_unchanged hb ha rfl
      | config c => exact visible_eq_of_subs_unchanged hb ha rfl
      | message m => exact visible_eq_of_subs_unchanged hb ha rfl
    | deleteStream name => exact absurd rfl (hnd name)
    | createStream raw => exact visible_eq_of_subs_unchanged hb ha rfl
    | getStream name => exact visible_eq_of_subs_unchanged hb ha rfl
    | lastMessageForSubject stream subject => exact visible_eq_of_subs_unchanged hb ha rfl
  | error err =>
    obtain ⟨heq, -⟩ :=
      applyOp_error_eq (deliver := deliver) (show applyOp deliver s o (.error err) = some s' from h)
    rw [heq] at ha
    rw [hb] at ha
    cases ha
    rfl

/-- The concrete theorem as an instance of the generic one, at `deliverOne_laws`. The statement is
`SubStatements.op_visible_frame`'s, verbatim. -/
theorem op_visible_frame_of_laws {s : SubState} {o : Op} {e : Expect} {s' : SubState} {id : SubId}
    {sub sub' : Subscriber} (h : apply s (.op o e) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hnm : ∀ stream subject payload headers x now, o = .publish stream subject payload headers x now →
        (sub.stream ≠ stream ∨ matchesAny sub.filters subject = false))
    (hnd : ∀ name, o ≠ .deleteStream name) : visible sub' = visible sub :=
  op_visible_frame_generic (pull := pullStep) deliverOne_laws h hb ha hnm hnd

/-- … and "verbatim" is checked, not asserted: the two declarations have the same type, so `rfl`
(with proof irrelevance) elaborates. If the frozen statement moved, this would fail. -/
theorem op_visible_frame_is_instance : @op_visible_frame = @op_visible_frame_of_laws := rfl

end EffectNatsSubstrate
