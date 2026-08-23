import EffectNatsSubstrate.SubReachable

/-!
# Stage-A statements — SA4, SA5, SA6, SA7, the negative witnesses (snapshot r3.1)

Proofs of the frozen r3.1 statements (`docs/signature-snapshot.md`, "Stage A
(r3.1)"): `sub_core_inv` (T1–T7 as corollaries), SA4a `register_observed`,
SA4c `selectReplay_lastPerSubject`, SA4d `memory_lastEnqueued_admissible`,
SA5 `pull_visible` / `publish_visible` / `op_visible_frame` /
`visible_sequences_strict`, SA6 `delete_ends` / `create_restarts`, SA7
`lagged_iff` / `lagged_carries_last_observed` (through the lag invariant
`LagInv`, proved over `ReachableSub` with `reachableSub_all`), and
`all_sub_negatives` (slice document §7, by `decide`).
-/

namespace EffectNatsSubstrate

/-- T1–T7 as corollaries of the frame: the embedded core satisfies the
sequential invariant on every reachable stage-A state. -/
theorem sub_core_inv {s : SubState} (h : ReachableSub s) : stateInv s.core :=
  reachable_inv (reachableSub_core h)

/-- The stored message a successful `publish` label commits (the `new` of `afterOp`). -/
abbrev publishedMessage (subject : SubjectName) (seq : StreamSeq) (payload : PayloadHash)
    (headers : List (String × String)) (now : Nat) : StoredMessage :=
  { subject := subject, sequence := seq, payload := payload, headers := headers,
    timestampMillis := now }

/-! ## The subscriber a successful operation leaves behind -/

theorem applyOp_ok_eq {s s' : SubState} {o : Op} {r : Ret}
    (h : applyOp deliverOne s o (.ok r) = some s') :
    ∃ core', step s.core o = .ok (core', r) ∧ s' = afterOp deliverOne s core' o r := by
  unfold applyOp at h
  cases hstep : step s.core o with
  | error err =>
    rw [hstep] at h
    simp at h
  | ok p =>
    obtain ⟨core', r₀⟩ := p
    rw [hstep] at h
    simp only at h
    split at h
    · rename_i hrr
      cases h
      subst hrr
      exact ⟨core', rfl, rfl⟩
    · cases h

theorem afterOp_publish_sub {s : SubState} {core' : JSState} {stream : StreamName}
    {subject : SubjectName} {payload : PayloadHash} {headers : List (String × String)}
    {x : Option StreamSeq} {now : Nat} {seq : StreamSeq} {id : SubId} {sub sub' : Subscriber}
    (hb : lookupSub s.subs id = some sub)
    (ha : lookupSub (afterOp deliverOne s core' (.publish stream subject payload headers x now)
      (.sequence seq)).subs id = some sub') :
    sub' = deliverOne stream (publishedMessage subject seq payload headers now) sub := by
  simp only [afterOp] at ha
  rw [lookupSub_map, hb] at ha
  exact (Option.some.inj ha).symm

theorem publish_sub {s s' : SubState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {x : Option StreamSeq} {now : Nat}
    {seq : StreamSeq} {id : SubId} {sub sub' : Subscriber}
    (h : apply s (.op (.publish stream subject payload headers x now) (.ok (.sequence seq))) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub') :
    sub' = deliverOne stream (publishedMessage subject seq payload headers now) sub := by
  obtain ⟨core', _, rfl⟩ := applyOp_ok_eq h
  exact afterOp_publish_sub hb ha

/-! ## SA4a — registration materializes the snapshot -/

theorem register_observed {s s' : SubState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} (hs : SubShape s)
    (h : apply s (.register stream opts l₀ id (.ok .unit)) = some s') :
    ∃ st, lookupStream s.core stream = some st ∧
      lookupSub s'.subs id = some (newSubscriber stream opts l₀ st.messages) := by
  have h' : applyRegister s stream opts l₀ id (.ok .unit) = some s' := h
  obtain ⟨hid, _⟩ := applyRegister_enabled h'
  unfold applyRegister at h'
  split at h'
  · cases h'
  · cases hl : lookupStream s.core stream with
    | none =>
      rw [hl] at h'
      simp at h'
    | some st =>
      rw [hl] at h'
      simp only at h'
      split at h'
      · cases h'
        refine ⟨st, rfl, ?_⟩
        apply lookupSub_append_fresh
        intro p hp
        rw [hid]
        exact Nat.ne_of_lt (hs.2 p hp)
      · cases h'

/-! ## SA4c — `lastPerSubject` through `lastForSubject` -/

theorem eq_of_sequence_eq_of_pairwise :
    ∀ {l : List StoredMessage}, l.Pairwise (fun a b => a.sequence < b.sequence) →
      ∀ {a b : StoredMessage}, a ∈ l → b ∈ l → a.sequence = b.sequence → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: xs, hp, a, b, ha, hb, heq => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hx, hxs⟩ := hp
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd heq (Nat.ne_of_lt (hx b hb'))
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd heq.symm (Nat.ne_of_lt (hx a ha'))
      · exact eq_of_sequence_eq_of_pairwise hxs ha' hb' heq

theorem selectReplay_lastPerSubject {messages : List StoredMessage} {opts : ConsumeOptions}
    (hstrict : messages.Pairwise (fun a b => a.sequence < b.sequence))
    (hs : opts.start = .lastPerSubject) :
    ∀ m ∈ selectReplay messages opts,
      lastForSubject (messages.filter (fun x => matchesAny opts.filters x.subject)) m.subject
        = some m := by
  intro m hm
  simp only [selectReplay, hs] at hm
  obtain ⟨hmem, hlast⟩ := List.mem_filter.mp hm
  unfold isLastOfSubject at hlast
  split at hlast
  · rename_i l hl
    simp only [beq_iff_eq] at hlast
    have hpw : (messages.filter (fun x => matchesAny opts.filters x.subject)).Pairwise
        (fun a b => a.sequence < b.sequence) :=
      List.Pairwise.sublist List.filter_sublist hstrict
    have hlmem : l ∈ messages.filter (fun x => matchesAny opts.filters x.subject) :=
      (mem_forSubject.mp (getLast?_mem hl)).1
    rw [hl, eq_of_sequence_eq_of_pairwise hpw hlmem hmem hlast]
  · cases hlast

/-! ## SA4d — the memory interpreter's initial `lastDelivered` is admissible -/

theorem memory_lastEnqueued_admissible {s : JSState} {stream : StreamName} {st : StreamState}
    (h : Reachable s) (hl : lookupStream s stream = some st) (opts : ConsumeOptions) :
    replayBound st.messages opts (st.nextSequence - 1) st.nextSequence = true := by
  have hbelow := (reachable_sequences_strict h hl).2
  have hpos := (reachable_positive h hl).1
  unfold replayBound
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · intro m hm
    have hlt : m.sequence < st.nextSequence := hbelow m (selectReplay_mem hm).1
    exact decide_eq_true (Nat.le_sub_one_of_lt hlt)
  · exact decide_eq_true (Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hpos))

/-! ## SA5 — the consumer-visible sequence, per transition -/

theorem pull_visible {s s' : SubState} {id : SubId} {sub sub' : Subscriber}
    (h : apply s (.pull id) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (ho : sub.status = .opened) : visible sub' = visible sub := by
  have h' : applyPull pullStep s id = some s' := h
  unfold applyPull at h'
  rw [hb] at h'
  simp only at h'
  split at h'
  · cases h'
  · rename_i sub₁ hpull
    cases h'
    have ha' : lookupSub (updateSub s.subs id (fun _ => sub₁)) id = some sub' := ha
    rw [lookupSub_updateSub_self _ hb] at ha'
    cases ha'
    unfold pullStep at hpull
    rw [ho] at hpull
    simp only at hpull
    split at hpull
    · cases hpull
    · cases hpull
      simp [visible]

theorem publish_visible {s : SubState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {x : Option StreamSeq} {now : Nat}
    {seq : StreamSeq} {s' : SubState} {id : SubId} {sub sub' : Subscriber}
    (h : apply s (.op (.publish stream subject payload headers x now) (.ok (.sequence seq))) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hr : sub.registered = true) (ho : sub.status = .opened) (hs : sub.stream = stream)
    (hm : matchesAny sub.filters subject = true) :
    (sub.pending.length < sub.policy.capacity →
        visible sub' = visible sub ++ [.entry { subject := subject, sequence := seq, payload := payload,
                                                headers := headers, timestampMillis := now }]) ∧
    (sub.pending.length = sub.policy.capacity →
        visible sub' = visible sub ∧ sub'.registered = false) := by
  obtain rfl := publish_sub h hb ha
  have hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters
      (publishedMessage subject seq payload headers now).subject) = true := by
    simp [hs, hr, hm]
  cases hpol : sub.policy with
  | terminateOnLag n =>
    refine ⟨fun hroom => ?_, fun hfull => ?_⟩
    · simp only [Policy.capacity] at hroom
      rw [deliverOne_admit hcond hpol hroom ho]
      simp [visible, publishedMessage, List.map_append, List.append_assoc]
    · simp only [Policy.capacity] at hfull
      rw [deliverOne_overflow hcond hpol (Nat.le_of_eq hfull.symm)]
      exact ⟨rfl, rfl⟩

theorem op_visible_frame {s : SubState} {o : Op} {e : Expect} {s' : SubState} {id : SubId}
    {sub sub' : Subscriber} (h : apply s (.op o e) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hnm : ∀ stream subject payload headers x now, o = .publish stream subject payload headers x now →
        (sub.stream ≠ stream ∨ matchesAny sub.filters subject = false))
    (hnd : ∀ name, o ≠ .deleteStream name) : visible sub' = visible sub := by
  have h' : applyOp deliverOne s o e = some s' := h
  unfold applyOp at h'
  split at h'
  · rename_i core' r r' hstep
    split at h'
    · cases h'
      cases o with
      | publish stream subject payload headers x now =>
        cases r with
        | sequence seq =>
          obtain rfl := afterOp_publish_sub hb ha
          rw [deliverOne_skip]
          rcases hnm stream subject payload headers x now rfl with hne | hfalse
          · simp [hne]
          · simp [hfalse]
        | unit => simp only [afterOp] at ha; rw [hb] at ha; cases ha; rfl
        | config c => simp only [afterOp] at ha; rw [hb] at ha; cases ha; rfl
        | message m => simp only [afterOp] at ha; rw [hb] at ha; cases ha; rfl
      | deleteStream name => exact absurd rfl (hnd name)
      | createStream raw => simp only [afterOp] at ha; rw [hb] at ha; cases ha; rfl
      | getStream name => simp only [afterOp] at ha; rw [hb] at ha; cases ha; rfl
      | lastMessageForSubject stream subject =>
        simp only [afterOp] at ha; rw [hb] at ha; cases ha; rfl
    · cases h'
  · rename_i err err' hstep
    split at h'
    · cases h'
      rw [hb] at ha
      cases ha
      rfl
    · cases h'
  · cases h'

theorem visible_sequences_strict {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, (entrySequences (visible p.2)).Pairwise (· < ·) :=
  fun p hp => (stateInv_reachable h p hp).visibleStrict

/-! ## SA6 — T12′: deletion ends the stream's registered subscribers; re-creation restarts -/

theorem delete_ends {s : SubState} {name : StreamName} {s' : SubState} {id : SubId}
    {sub sub' : Subscriber}
    (h : apply s (.op (.deleteStream name) (.ok .unit)) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hr : sub.registered = true) (hs : sub.stream = name) :
    sub'.registered = false ∧
      (sub'.status = .closing (.streamNotFound name) ∨ sub'.status = .done (.streamNotFound name)) ∧
      visible sub' = visible sub := by
  obtain ⟨core', _, rfl⟩ := applyOp_ok_eq h
  simp only [afterOp] at ha
  rw [lookupSub_map, hb] at ha
  obtain rfl := (Option.some.inj ha).symm
  unfold endOne
  have hcond : (sub.stream == name && sub.registered) = true := by simp [hs, hr]
  rw [if_pos hcond]
  refine ⟨rfl, ?_, rfl⟩
  dsimp only
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem create_restarts {s : SubState} {raw : RawStreamConfig} {s' : SubState} {st : StreamState}
    (h : apply s (.op (.createStream raw) (.ok .unit)) = some s')
    (habsent : lookupStream s.core raw.name = none) (hst : lookupStream s'.core raw.name = some st) :
    st.nextSequence = 1 := by
  obtain ⟨core', hstep, rfl⟩ := applyOp_ok_eq h
  simp only [afterOp] at hst
  have hc : createStep s.core raw = .ok (core', .unit) := hstep
  unfold createStep at hc
  split at hc
  · cases hc
  · rename_i config hval
    have hname : config.name = raw.name := (validate_ok_sound hval).1
    split at hc
    · rename_i st₀ hlook
      rw [hname, habsent] at hlook
      cases hlook
    · cases hc
      rw [hname, lookup_insert] at hst
      cases hst
      rfl

/-! ## SA7 — T13′ through the lag invariant -/

/-- What a `consumerLagged` error carries, in every reachable state: while `closing` it
is the current `lastEnqueued`, once `done` (and once pulled as `failed`) it is the last
entry sequence the consumer saw. -/
structure LagInv (sub : Subscriber) : Prop where
  closingLag : ∀ stream n, sub.status = .closing (.consumerLagged stream n) → n = sub.lastEnqueued
  doneLag : ∀ stream n, sub.status = .done (.consumerLagged stream n) →
    (entrySequences sub.observed).getLast? = some n
  failedLag : ∀ stream n, sub.observed.getLast? = some (.failed (.consumerLagged stream n)) →
    (entrySequences sub.observed).getLast? = some n

def LagState (s : SubState) : Prop := ∀ p ∈ s.subs, LagInv p.2

theorem lagInv_newSubscriber (stream : StreamName) (opts : ConsumeOptions) (l₀ : StreamSeq)
    (messages : List StoredMessage) : LagInv (newSubscriber stream opts l₀ messages) := by
  refine ⟨?_, ?_, ?_⟩
  · intro stream' n h; cases h
  · intro stream' n h; cases h
  · intro stream' n h
    have h' : ((selectReplay messages opts).map Observed.entry ++ [Observed.caughtUp]).getLast?
        = some (.failed (.consumerLagged stream' n)) := h
    rw [List.getLast?_concat] at h'
    cases h'

theorem lagInv_deliverOne {s : SubState} {stream : StreamName} {m : StoredMessage}
    {sub : Subscriber} (hinv : SubInv s sub) (hl : LagInv sub) :
    LagInv (deliverOne stream m sub) := by
  cases hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters m.subject) with
  | false => rw [deliverOne_skip hcond]; exact hl
  | true =>
    have hreg : sub.registered = true := by
      have hc := hcond
      simp only [Bool.and_eq_true] at hc
      exact hc.1.2
    have ho : sub.status = .opened := hinv.registeredOpen hreg
    cases hpol : sub.policy with
    | terminateOnLag n =>
      by_cases hfull : n ≤ sub.pending.length
      · obtain ⟨heq, _hne⟩ := deliverOne_overflow_closing hinv hcond hpol hfull
        rw [heq]
        refine ⟨?_, ?_, ?_⟩
        · intro stream' n' h
          have h' : QueueStatus.closing (.consumerLagged stream sub.lastEnqueued)
              = .closing (.consumerLagged stream' n') := h
          injection h' with h1
          injection h1 with _ hn'
          exact hn'.symm
        · intro stream' n' h
          have h' : QueueStatus.closing (.consumerLagged stream sub.lastEnqueued)
              = .done (.consumerLagged stream' n') := h
          cases h'
        · intro stream' n' h
          exact hl.failedLag stream' n' h
      · rw [deliverOne_admit hcond hpol (Nat.lt_of_not_le hfull) ho]
        refine ⟨?_, ?_, ?_⟩
        · intro stream' n' h
          have h' : sub.status = .closing (.consumerLagged stream' n') := h
          rw [ho] at h'
          cases h'
        · intro stream' n' h
          have h' : sub.status = .done (.consumerLagged stream' n') := h
          rw [ho] at h'
          cases h'
        · intro stream' n' h
          exact hl.failedLag stream' n' h

theorem lagInv_endOne {name : StreamName} {sub : Subscriber} (hl : LagInv sub) :
    LagInv (endOne name sub) := by
  unfold endOne
  split
  · refine ⟨?_, ?_, ?_⟩
    · intro stream' n' h
      have h' : (if sub.pending.isEmpty then QueueStatus.done (.streamNotFound name)
          else .closing (.streamNotFound name)) = .closing (.consumerLagged stream' n') := h
      split at h' <;> cases h'
    · intro stream' n' h
      have h' : (if sub.pending.isEmpty then QueueStatus.done (.streamNotFound name)
          else .closing (.streamNotFound name)) = .done (.consumerLagged stream' n') := h
      split at h' <;> cases h'
    · intro stream' n' h
      exact hl.failedLag stream' n' h
  · exact hl

theorem lagInv_pullStep {s : SubState} {sub sub' : Subscriber} (hinv : SubInv s sub)
    (hl : LagInv sub) (h : pullStep sub = some sub') : LagInv sub' := by
  unfold pullStep at h
  split at h
  · cases h
  · rename_i e hst
    cases h
    refine ⟨?_, ?_, ?_⟩
    · intro stream' n' h'; cases h'
    · intro stream' n' h'; cases h'
    · intro stream' n' h'
      have h'' : (sub.observed ++ [Observed.failed e]).getLast?
          = some (.failed (.consumerLagged stream' n')) := h'
      rw [List.getLast?_concat] at h''
      cases h''
      show (entrySequences (sub.observed ++ [Observed.failed (.consumerLagged stream' n')])).getLast?
        = some n'
      rw [entrySequences_append, entrySequences_failed, List.append_nil]
      exact hl.doneLag stream' n' hst
  · rename_i hst
    split at h
    · cases h
    · rename_i hne
      cases h
      have hne' : sub.pending ≠ [] := fun hnil => hne (List.isEmpty_iff.mpr hnil)
      refine ⟨?_, ?_, ?_⟩
      · intro stream' n' h'
        have h'' : sub.status = .closing (.consumerLagged stream' n') := h'
        rw [hst] at h''
        cases h''
      · intro stream' n' h'
        have h'' : sub.status = .done (.consumerLagged stream' n') := h'
        rw [hst] at h''
        cases h''
      · intro stream' n' h'
        exfalso
        have h'' : (sub.observed ++ sub.pending.map Observed.entry).getLast?
            = some (.failed (.consumerLagged stream' n')) := h'
        rw [List.getLast?_append, List.getLast?_map] at h''
        cases hlast : sub.pending.getLast? with
        | none => exact hne' (List.getLast?_eq_none_iff.mp hlast)
        | some x => rw [hlast] at h''; simp at h''
  · rename_i e hst
    split at h
    · cases h
    · rename_i hne
      cases h
      have hne' : sub.pending ≠ [] := fun hnil => hne (List.isEmpty_iff.mpr hnil)
      refine ⟨?_, ?_, ?_⟩
      · intro stream' n' h'; cases h'
      · intro stream' n' h'
        have h'' : QueueStatus.done e = .done (.consumerLagged stream' n') := h'
        cases h''
        show (entrySequences (sub.observed ++ sub.pending.map Observed.entry)).getLast? = some n'
        rw [entrySequences_append, entrySequences_map_entry, List.getLast?_append,
          hinv.pendingLast hne']
        show some sub.lastEnqueued = some n'
        rw [hl.closingLag stream' n' hst]
      · intro stream' n' h'
        exfalso
        have h'' : (sub.observed ++ sub.pending.map Observed.entry).getLast?
            = some (.failed (.consumerLagged stream' n')) := h'
        rw [List.getLast?_append, List.getLast?_map] at h''
        cases hlast : sub.pending.getLast? with
        | none => exact hne' (List.getLast?_eq_none_iff.mp hlast)
        | some x => rw [hlast] at h''; simp at h''

theorem lagInv_unsubscribe {sub : Subscriber} (hl : LagInv sub) :
    LagInv { sub with registered := false, pending := [], status := .shutDown } := by
  refine ⟨?_, ?_, ?_⟩
  · intro stream' n' h; cases h
  · intro stream' n' h; cases h
  · intro stream' n' h
    exact hl.failedLag stream' n' h

theorem lagState_afterOp {s : SubState} {core' : JSState} {o : Op} {r : Ret}
    (hinv : StateInv s) (hl : LagState s) : LagState (afterOp deliverOne s core' o r) := by
  unfold afterOp
  split
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact lagInv_deliverOne (hinv q hq) (hl q hq)
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact lagInv_endOne (hl q hq)
  · exact hl

theorem apply_lag {s s' : SubState} {l : Label} (hinv : StateInv s) (hl : LagState s)
    (h : apply s l = some s') : LagState s' := by
  cases l with
  | op o e =>
    have h' : applyOp deliverOne s o e = some s' := h
    unfold applyOp at h'
    split at h'
    · rename_i core' r r' hstep
      split at h'
      · cases h'; exact lagState_afterOp hinv hl
      · cases h'
    · rename_i err err' hstep
      split at h'
      · cases h'; exact hl
      · cases h'
    · cases h'
  | register stream opts l₀ id e =>
    have h' : applyRegister s stream opts l₀ id e = some s' := h
    unfold applyRegister at h'
    split at h'
    · cases h'
    · split at h'
      · split at h'
        · cases h'; exact hl
        · cases h'
      · split at h'
        · cases h'
          intro p hp
          have hp' : p ∈ s.subs ++ [(id, newSubscriber stream opts l₀ _)] := hp
          rcases List.mem_append.mp hp' with hold | hnew
          · exact hl p hold
          · rw [List.mem_singleton.mp hnew]
            exact lagInv_newSubscriber _ _ _ _
        · cases h'
      · cases h'
  | pull id =>
    have h' : applyPull pullStep s id = some s' := h
    unfold applyPull at h'
    split at h'
    · cases h'
    · rename_i sub hsub
      split at h'
      · cases h'
      · rename_i sub' hpull
        cases h'
        intro p hp
        have hp' : p ∈ updateSub s.subs id (fun _ => sub') := hp
        rcases mem_updateSub hp' with hold | ⟨_, _, hp2⟩
        · exact hl p hold
        · rw [hp2]
          exact lagInv_pullStep (hinv _ (mem_of_lookupSub hsub)) (hl _ (mem_of_lookupSub hsub)) hpull
  | unsubscribe id =>
    have h' : applyUnsubscribe s id = some s' := h
    unfold applyUnsubscribe at h'
    split at h'
    · cases h'
    · rename_i sub hsub
      split at h'
      · cases h'
      · cases h'
        intro p hp
        have hp' : p ∈ updateSub s.subs id
            (fun sub => { sub with registered := false, pending := [], status := .shutDown }) := hp
        rcases mem_updateSub hp' with hold | ⟨sub₀, h₀, hp2⟩
        · exact hl p hold
        · rw [hp2]
          exact lagInv_unsubscribe (hl _ h₀)

theorem lagState_reachable {s : SubState} (h : ReachableSub s) : LagState s :=
  reachableSub_all (fun _ hp => nomatch hp) (fun _ hinv hl hnext => apply_lag hinv hl hnext) h

theorem lagged_carries_last_observed {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, ∀ stream n, p.2.observed.getLast? = some (.failed (.consumerLagged stream n)) →
      (entrySequences p.2.observed).getLast? = some n :=
  fun p hp stream n hlast => (lagState_reachable h p hp).failedLag stream n hlast

/-- Explicit-premise form of the lag decision: it rests on exactly two facts about the
pre-state subscriber — it is `opened`, and its buffer fits the policy bound. The stage-B
bridge re-establishes these from the runtime model rather than from `ReachableSub`. -/
theorem lagged_iff_of_open {s : SubState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {x : Option StreamSeq} {now : Nat}
    {seq : StreamSeq} {s' : SubState} {id : SubId} {sub sub' : Subscriber} {n : Nat}
    (h : apply s (.op (.publish stream subject payload headers x now) (.ok (.sequence seq))) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hp : sub.policy = .terminateOnLag n) (hr : sub.registered = true) (hs : sub.stream = stream)
    (hm : matchesAny sub.filters subject = true)
    (ho : sub.status = .opened) (hcap : sub.pending.length ≤ n) :
    (sub'.status = .closing (.consumerLagged stream sub.lastEnqueued) ∨
     sub'.status = .done (.consumerLagged stream sub.lastEnqueued)) ↔ sub.pending.length = n := by
  obtain rfl := publish_sub h hb ha
  have hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters
      (publishedMessage subject seq payload headers now).subject) = true := by
    simp [hs, hr, hm]
  by_cases hfull : n ≤ sub.pending.length
  · rw [deliverOne_overflow hcond hp hfull]
    constructor
    · intro _
      exact Nat.le_antisymm hcap hfull
    · intro _
      dsimp only
      split
      · exact Or.inr rfl
      · exact Or.inl rfl
  · rw [deliverOne_admit hcond hp (Nat.lt_of_not_le hfull) ho]
    constructor
    · intro hor
      rcases hor with h1 | h1
      · have h1' : sub.status = .closing (.consumerLagged stream sub.lastEnqueued) := h1
        rw [ho] at h1'
        cases h1'
      · have h1' : sub.status = .done (.consumerLagged stream sub.lastEnqueued) := h1
        rw [ho] at h1'
        cases h1'
    · intro heq
      exact absurd (Nat.le_of_eq heq.symm) hfull

theorem lagged_iff {s : SubState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {x : Option StreamSeq} {now : Nat}
    {seq : StreamSeq} {s' : SubState} {id : SubId} {sub sub' : Subscriber} {n : Nat}
    (hreach : ReachableSub s)
    (h : apply s (.op (.publish stream subject payload headers x now) (.ok (.sequence seq))) = some s')
    (hb : lookupSub s.subs id = some sub) (ha : lookupSub s'.subs id = some sub')
    (hp : sub.policy = .terminateOnLag n) (hr : sub.registered = true) (hs : sub.stream = stream)
    (hm : matchesAny sub.filters subject = true) :
    (sub'.status = .closing (.consumerLagged stream sub.lastEnqueued) ∨
     sub'.status = .done (.consumerLagged stream sub.lastEnqueued)) ↔ sub.pending.length = n := by
  have hinv : SubInv s sub := stateInv_reachable hreach _ (mem_of_lookupSub hb)
  exact lagged_iff_of_open h hb ha hp hr hs hm (hinv.registeredOpen hr) (by
    have hc := hinv.capacity
    rw [hp] at hc
    simpa [Policy.capacity] using hc)

/-! ## The negative witnesses (slice document §7) -/

def applyAll : SubState → List Label → Option SubState
  | s, [] => some s
  | s, l :: ls =>
    match apply s l with
    | none => none
    | some s' => applyAll s' ls

inductive NegKind where
  /-- `apply … = none`. -/
  | disabled
  /-- `apply … = some s` — the state is unchanged. -/
  | unchanged

structure Negative where
  name : String
  before : List Label
  label : Label
  kind : NegKind

def negativeHolds (n : Negative) : Bool :=
  match applyAll initialSub n.before with
  | none => false
  | some s =>
    match n.kind with
    | .disabled => (apply s n.label).isNone
    | .unchanged => apply s n.label == some s

def negOpts (buffer : Policy) : ConsumeOptions :=
  { filters := ["$KV.b.>"], start := .newOnly, buffer := buffer }

def negCreate : Label := .op (.createStream kvConfigRaw) (.ok .unit)

def negPublish (seq : StreamSeq) : Label :=
  .op (.publish "KV_b" "$KV.b.a" "p" [] none 1) (.ok (.sequence seq))

def negRegister (buffer : Policy) (l₀ : StreamSeq) (id : SubId) : Label :=
  .register "KV_b" (negOpts buffer) l₀ id (.ok .unit)

def subNegatives : List Negative :=
  [ { name := "pull-on-empty-open-buffer"
      before := [negCreate, negRegister (.terminateOnLag 1) 0 0], label := .pull 0
      kind := .disabled }
  , { name := "register-capacity-zero"
      before := [negCreate], label := negRegister (.terminateOnLag 0) 0 0, kind := .disabled }
  , { name := "pull-shutDown"
      before := [negCreate, negRegister (.terminateOnLag 1) 0 0, .unsubscribe 0]
      label := .pull 0, kind := .disabled }
  , { name := "unsubscribe-shutDown"
      before := [negCreate, negRegister (.terminateOnLag 1) 0 0, .unsubscribe 0]
      label := .unsubscribe 0, kind := .disabled }
  , { name := "pull-unknown-id", before := [negCreate], label := .pull 7, kind := .disabled }
  , { name := "unsubscribe-unknown-id", before := [negCreate], label := .unsubscribe 7
      kind := .disabled }
  , { name := "expectation-disagrees-with-step"
      before := [negCreate], label := negPublish 5, kind := .disabled }
  , { name := "register-not-next-id"
      before := [negCreate], label := negRegister (.terminateOnLag 1) 0 3, kind := .disabled }
  , { name := "register-inadmissible-lastEnqueued"
      before := [negCreate, negPublish 1], label := negRegister (.terminateOnLag 1) 2 0
      kind := .disabled }
  , { name := "register-missing-stream"
      before := []
      label := .register "KV_b" (negOpts (.terminateOnLag 1)) 0 0 (.error (.streamNotFound "KV_b"))
      kind := .unchanged } ]

theorem all_sub_negatives : subNegatives.all negativeHolds = true := by decide

end EffectNatsSubstrate
