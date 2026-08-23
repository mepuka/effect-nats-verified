import EffectNatsSubstrate.Views

/-!
# Proofs: T1–T7

T1 — `createStream` idempotence and conflict rejection (conformance case C1).
T2 — over reachable states, per-stream sequences strictly increase and stay
below `nextSequence`; a successful `publish` returns the pre-state
`nextSequence` and increments it by one (C2).
T3 — `lastMessageForSubject` is the max-sequence message for the subject, or
`NoMessageForSubject` (C4).
T4 — compare-and-set succeeds iff the expected sequence is the subject's last,
`0` iff the subject is empty (C3).
T5 — rollup leaves exactly the new message for its subject, touches no other
subject, and is `RollupNotPermitted` without `allowRollup` (C6).
T6 — a positive `maxMessagesPerSubject` bounds every subject's history; pruning
keeps the most recent messages (C5).
T7 — an unbound subject is `SubjectNotBound` (C2).

A successful elaboration proves the stated proposition, not that the
proposition models the intended system; the model-fidelity boundary is the
line-by-line transliteration recorded in each module header.
-/

namespace EffectNatsSubstrate

/-! ## List lemmas (core-only; hand-rolled where core names are unstable) -/

private theorem pairwise_of_sublist {α : Type} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, l₁.Sublist l₂ → l₂.Pairwise R → l₁.Pairwise R := by
  intro l₁ l₂ h
  induction h with
  | slnil => intro _; exact .nil
  | cons a _ ih =>
    intro hp
    cases hp with
    | cons _ hp => exact ih hp
  | cons_cons a h ih =>
    intro hp
    cases hp with
    | cons ha hp => exact .cons (fun b hb => ha b (h.subset hb)) (ih hp)

theorem dropOldest_sublist (ms : List StoredMessage) (subject : SubjectName) (n : Nat) :
    (dropOldest ms subject n).Sublist ms := by
  induction ms generalizing n with
  | nil =>
    cases n with
    | zero => exact List.Sublist.refl _
    | succ n => exact List.Sublist.refl _
  | cons m ms ih =>
    cases n with
    | zero => exact List.Sublist.refl _
    | succ n =>
      simp only [dropOldest]
      split
      · exact List.Sublist.cons m (ih n)
      · exact List.Sublist.cons_cons m (ih (n + 1))

theorem pruneSubject_sublist (messages : List StoredMessage) (subject : SubjectName)
    (limit : Nat) : (pruneSubject messages subject limit).Sublist messages := by
  unfold pruneSubject
  split
  · exact List.Sublist.refl _
  · split
    · exact List.Sublist.refl _
    · exact dropOldest_sublist _ _ _

theorem publishBase_sublist (st : StreamState) (subject : SubjectName) (rollup : Bool) :
    (publishBase st subject rollup).Sublist st.messages := by
  unfold publishBase
  split
  · exact List.filter_sublist
  · exact List.Sublist.refl _

/-- A stored message after a commit was stored before, or is the committed one. -/
theorem mem_applyPublish {st : StreamState} {subject : SubjectName} {payload : PayloadHash}
    {headers : List (String × String)} {rollup : Bool} {now : Nat} {m : StoredMessage}
    (h : m ∈ (applyPublish st subject payload headers rollup now).1.messages) :
    m ∈ st.messages ∨ m = newMessage st subject payload headers now := by
  simp only [applyPublish] at h
  rcases List.mem_append.mp
      ((pruneSubject_sublist
        (publishBase st subject rollup ++ [newMessage st subject payload headers now])
        subject st.config.maxMessagesPerSubject).subset h) with hold | hnew
  · exact Or.inl ((publishBase_sublist st subject rollup).subset hold)
  · exact Or.inr (List.mem_singleton.mp hnew)

/-! ## Association-list lemmas -/

theorem lookup_mem : ∀ {s : JSState} {name : StreamName} {st : StreamState},
    lookupStream s name = some st → (name, st) ∈ s := by
  intro s
  induction s with
  | nil => intro name st h; cases h
  | cons q rest ih =>
    intro name st h
    match q with
    | (n, st₀) =>
      simp only [lookupStream] at h
      split at h
      next hc =>
        injection h with h2
        subst hc
        subst h2
        exact List.Mem.head _
      next =>
        exact List.Mem.tail _ (ih h)

theorem lookup_insert (s : JSState) (name : StreamName) (st : StreamState) :
    lookupStream (insertStream s name st) name = some st := by
  simp [insertStream, lookupStream]

theorem lookup_update_const : ∀ {s : JSState} {name : StreamName} {st st' : StreamState},
    lookupStream s name = some st →
    lookupStream (updateStream s name (fun _ => st')) name = some st' := by
  intro s
  induction s with
  | nil => intro name st st' h; cases h
  | cons q rest ih =>
    intro name st st' h
    match q with
    | (n, st₀) =>
      simp only [lookupStream] at h
      split at h
      next hc =>
        subst hc
        simp [updateStream, lookupStream]
      next hc =>
        simp only [updateStream]
        rw [if_neg hc]
        simp only [lookupStream]
        rw [if_neg hc]
        exact ih h

theorem mem_update_const : ∀ {s : JSState} {name : StreamName} {st' : StreamState}
    {p : StreamName × StreamState},
    p ∈ updateStream s name (fun _ => st') → p.2 = st' ∨ p ∈ s := by
  intro s
  induction s with
  | nil => intro name st' p hp; simp only [updateStream] at hp; cases hp
  | cons q rest ih =>
    intro name st' p hp
    match q with
    | (n, st₀) =>
      simp only [updateStream] at hp
      split at hp
      · cases hp with
        | head => exact Or.inl rfl
        | tail _ hp =>
          cases ih hp with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (List.mem_cons_of_mem _ h)
      · cases hp with
        | head => exact Or.inr (List.Mem.head _)
        | tail _ hp =>
          cases ih hp with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_remove : ∀ {s : JSState} {name : StreamName} {p : StreamName × StreamState},
    p ∈ removeStream s name → p ∈ s := by
  intro s
  induction s with
  | nil => intro name p hp; simp only [removeStream] at hp; cases hp
  | cons q rest ih =>
    intro name p hp
    match q with
    | (n, st₀) =>
      simp only [removeStream] at hp
      split at hp
      · exact List.mem_cons_of_mem _ (ih hp)
      · cases hp with
        | head => exact List.Mem.head _
        | tail _ hp => exact List.mem_cons_of_mem _ (ih hp)

theorem stateInv_update_const : ∀ {s : JSState} {name : StreamName} {st' : StreamState},
    stateInv s → streamInv st' → stateInv (updateStream s name (fun _ => st')) := by
  intro s
  induction s with
  | nil =>
    intro name st' _ _ p hp
    simp only [updateStream] at hp
    cases hp
  | cons q rest ih =>
    intro name st' h h' p hp
    match q with
    | (n, st₀) =>
      have hrest : stateInv rest := fun p hp => h p (List.mem_cons_of_mem _ hp)
      simp only [updateStream] at hp
      split at hp
      · cases hp with
        | head => exact h'
        | tail _ hp => exact ih hrest h' p hp
      · cases hp with
        | head => exact h (n, st₀) (List.Mem.head _)
        | tail _ hp => exact ih hrest h' p hp

theorem stateInv_remove : ∀ {s : JSState} {name : StreamName},
    stateInv s → stateInv (removeStream s name) := by
  intro s
  induction s with
  | nil =>
    intro name _ p hp
    simp only [removeStream] at hp
    cases hp
  | cons q rest ih =>
    intro name h p hp
    match q with
    | (n, st₀) =>
      have hrest : stateInv rest := fun p hp => h p (List.mem_cons_of_mem _ hp)
      simp only [removeStream] at hp
      split at hp
      · exact ih hrest p hp
      · cases hp with
        | head => exact h (n, st₀) (List.Mem.head _)
        | tail _ hp => exact ih hrest p hp

/-! ## Publish preserves the stream invariant -/

theorem applyPublish_inv {st : StreamState} (h : streamInv st)
    (subject : SubjectName) (payload : PayloadHash)
    (headers : List (String × String)) (rollup : Bool) (now : Nat) :
    streamInv (applyPublish st subject payload headers rollup now).1 := by
  have hbase := publishBase_sublist st subject rollup
  have hbasePair : (publishBase st subject rollup).Pairwise
      (fun a b => a.sequence < b.sequence) :=
    pairwise_of_sublist hbase h.1
  have hbaseBound : ∀ m ∈ publishBase st subject rollup, m.sequence < st.nextSequence :=
    fun m hm => h.2 m (hbase.subset hm)
  have happPair : ((publishBase st subject rollup)
        ++ [newMessage st subject payload headers now]).Pairwise
      (fun a b => a.sequence < b.sequence) :=
    pairwise_append_singleton hbasePair (fun a ha => hbaseBound a ha)
  have happBound : ∀ m ∈ (publishBase st subject rollup)
        ++ [newMessage st subject payload headers now],
      m.sequence < st.nextSequence + 1 := by
    intro m hm
    cases List.mem_append.mp hm with
    | inl hml => exact Nat.lt_succ_of_lt (hbaseBound m hml)
    | inr hmr =>
      have hbeq := List.mem_singleton.mp hmr
      subst hbeq
      exact Nat.lt_succ_self _
  have hsub := pruneSubject_sublist
    ((publishBase st subject rollup) ++ [newMessage st subject payload headers now])
    subject st.config.maxMessagesPerSubject
  exact ⟨pairwise_of_sublist hsub happPair, fun m hm => happBound m (hsub.subset hm)⟩

theorem commitPublish_inv {s : JSState} {stream : StreamName} {st : StreamState}
    {subject : SubjectName} {payload : PayloadHash}
    {headers : List (String × String)} {now : Nat} {s' : JSState} {r : Ret}
    (h : stateInv s) (hlook : lookupStream s stream = some st)
    (hs : commitPublish s stream st subject payload headers now = .ok (s', r)) :
    stateInv s' := by
  unfold commitPublish at hs
  cases hs
  exact stateInv_update_const h
    (applyPublish_inv (h _ (lookup_mem hlook)) subject payload headers (isRollup headers) now)

/-! ## Step preserves the state invariant -/

theorem createStep_inv {s : JSState} {raw : RawStreamConfig} {s' : JSState} {r : Ret}
    (h : stateInv s) (hs : createStep s raw = .ok (s', r)) : stateInv s' := by
  unfold createStep at hs
  split at hs
  · cases hs
  · split at hs
    · split at hs
      · cases hs; exact h
      · cases hs
    · cases hs
      intro p hp
      cases hp with
      | head => exact ⟨.nil, fun m hm => nomatch hm⟩
      | tail _ hp => exact h p hp

theorem getStep_inv {s : JSState} {name : StreamName} {s' : JSState} {r : Ret}
    (h : stateInv s) (hs : getStep s name = .ok (s', r)) : stateInv s' := by
  unfold getStep at hs
  split at hs
  · cases hs; exact h
  · cases hs

theorem deleteStep_inv {s : JSState} {name : StreamName} {s' : JSState} {r : Ret}
    (h : stateInv s) (hs : deleteStep s name = .ok (s', r)) : stateInv s' := by
  unfold deleteStep at hs
  split at hs
  · cases hs; exact stateInv_remove h
  · cases hs

theorem lastMsgStep_inv {s : JSState} {stream : StreamName} {subject : SubjectName}
    {s' : JSState} {r : Ret}
    (h : stateInv s) (hs : lastMsgStep s stream subject = .ok (s', r)) : stateInv s' := by
  unfold lastMsgStep at hs
  split at hs
  · cases hs
  · split at hs
    · cases hs; exact h
    · cases hs

theorem publishStep_inv {s : JSState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {s' : JSState} {r : Ret}
    (h : stateInv s)
    (hs : publishStep s stream subject payload headers expected? now = .ok (s', r)) :
    stateInv s' := by
  unfold publishStep at hs
  split at hs
  · cases hs
  next st hlook =>
    split at hs
    · split at hs
      · cases hs
      · split at hs
        · split at hs
          · exact commitPublish_inv h hlook hs
          · cases hs
        · exact commitPublish_inv h hlook hs
    · cases hs

theorem step_preserves_inv {s s' : JSState} {op : Op} {r : Ret}
    (h : stateInv s) (hs : step s op = .ok (s', r)) : stateInv s' := by
  cases op with
  | createStream raw => exact createStep_inv h hs
  | getStream name => exact getStep_inv h hs
  | deleteStream name => exact deleteStep_inv h hs
  | publish stream subject payload headers expected? now => exact publishStep_inv h hs
  | lastMessageForSubject stream subject => exact lastMsgStep_inv h hs

/-! ## T2 — sequence discipline over reachable states -/

theorem reachable_inv {s : JSState} (h : Reachable s) : stateInv s := by
  induction h with
  | init => intro p hp; cases hp
  | step _ hstep ih => exact step_preserves_inv ih hstep

/-- T2, storage half: per-stream sequences strictly increase and stay below
`nextSequence` (invariant I1, monobox order per stream, at the storage layer). -/
theorem reachable_sequences_strict {s : JSState} {name : StreamName} {st : StreamState}
    (h : Reachable s) (hl : lookupStream s name = some st) :
    st.messages.Pairwise (fun a b => a.sequence < b.sequence)
      ∧ ∀ m ∈ st.messages, m.sequence < st.nextSequence :=
  reachable_inv h _ (lookup_mem hl)

/-- T2, assignment half: a successful publish returns the pre-state
`nextSequence` and increments it by exactly one. -/
theorem publish_assigns {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject : SubjectName} {payload : PayloadHash}
    {headers : List (String × String)} {expected? : Option StreamSeq} {now : Nat}
    (hs : step s (.publish stream subject payload headers expected? now) = .ok (s', r)) :
    ∃ st, lookupStream s stream = some st
      ∧ r = .sequence st.nextSequence
      ∧ ∃ st', lookupStream s' stream = some st'
        ∧ st'.nextSequence = st.nextSequence + 1 := by
  have hp : publishStep s stream subject payload headers expected? now = .ok (s', r) := hs
  unfold publishStep at hp
  split at hp
  · cases hp
  next st hlook =>
    split at hp
    · split at hp
      · cases hp
      · split at hp
        · split at hp
          · unfold commitPublish at hp
            cases hp
            exact ⟨st, hlook, rfl, _, lookup_update_const hlook, rfl⟩
          · cases hp
        · unfold commitPublish at hp
          cases hp
          exact ⟨st, hlook, rfl, _, lookup_update_const hlook, rfl⟩
    · cases hp

/-! ## T1 — createStream idempotence and conflict rejection -/

theorem create_ok_establishes {s s' : JSState} {raw : RawStreamConfig} {r : Ret}
    (h : createStep s raw = .ok (s', r)) :
    ∃ config st, validate raw = .ok config
      ∧ lookupStream s' config.name = some st ∧ st.config = config := by
  unfold createStep at h
  split at h
  · cases h
  next config hval =>
    split at h
    next st hlook =>
      split at h
      next hcfg =>
        cases h
        exact ⟨config, st, hval, hlook, hcfg⟩
      · cases h
    next hlook =>
      cases h
      exact ⟨config, _, hval, lookup_insert .., rfl⟩

theorem createStep_of_lookup {s : JSState} {raw : RawStreamConfig}
    {config : StreamConfig} {st : StreamState}
    (hval : validate raw = .ok config) (hlook : lookupStream s config.name = some st)
    (hcfg : st.config = config) :
    createStep s raw = .ok (s, .unit) := by
  unfold createStep
  simp only [hval]
  simp only [hlook]
  rw [if_pos hcfg]

/-- T1, idempotence: a successful create followed by the same raw config
succeeds and leaves the state unchanged. -/
theorem createStream_idempotent {s s' : JSState} {raw : RawStreamConfig} {r : Ret}
    (h : step s (.createStream raw) = .ok (s', r)) :
    step s' (.createStream raw) = .ok (s', .unit) := by
  have hc : createStep s raw = .ok (s', r) := h
  show createStep s' raw = .ok (s', .unit)
  exact match create_ok_establishes hc with
  | ⟨_, _, hval, hlook, hcfg⟩ => createStep_of_lookup hval hlook hcfg

/-- T1, conflict: a differing config on an existing name is
`StreamConfigConflict`. State preservation on error is by construction. -/
theorem createStream_conflict {s : JSState} {raw : RawStreamConfig}
    {config : StreamConfig} {st : StreamState}
    (hval : validate raw = .ok config) (hlook : lookupStream s config.name = some st)
    (hcfg : st.config ≠ config) :
    step s (.createStream raw) = .error (.streamConfigConflict config.name) := by
  show createStep s raw = _
  unfold createStep
  simp only [hval]
  simp only [hlook]
  rw [if_neg hcfg]

/-! ## Per-stream invariants beyond `streamInv`

A per-stream predicate holds on every reachable stream as soon as it holds on
a freshly created stream and is preserved by `applyPublish`: `get` and
`lastMessageForSubject` do not change state, `delete` only removes entries,
and `create` only inserts a fresh one. -/

theorem reachable_all {P : StreamState → Prop}
    (hcreate : ∀ config : StreamConfig,
      P { config := config, messages := [], nextSequence := 1 })
    (hpublish : ∀ (st : StreamState) (subject : SubjectName) (payload : PayloadHash)
      (headers : List (String × String)) (rollup : Bool) (now : Nat),
      P st → P (applyPublish st subject payload headers rollup now).1)
    {s : JSState} (hr : Reachable s) : ∀ p ∈ s, P p.2 := by
  induction hr with
  | init => intro p hp; cases hp
  | @step s s' op r _ hstep ih =>
    cases op with
    | createStream raw =>
      have hc : createStep s raw = .ok (s', r) := hstep
      unfold createStep at hc
      split at hc
      · cases hc
      · split at hc
        · split at hc
          · cases hc; exact ih
          · cases hc
        · cases hc
          intro p hp
          cases hp with
          | head => exact hcreate _
          | tail _ hp => exact ih p hp
    | getStream name =>
      have hg : getStep s name = .ok (s', r) := hstep
      unfold getStep at hg
      split at hg
      · cases hg; exact ih
      · cases hg
    | deleteStream name =>
      have hd : deleteStep s name = .ok (s', r) := hstep
      unfold deleteStep at hd
      split at hd
      · cases hd; exact fun p hp => ih p (mem_remove hp)
      · cases hd
    | publish stream subject payload headers expected? now =>
      have hp : publishStep s stream subject payload headers expected? now = .ok (s', r) := hstep
      unfold publishStep at hp
      split at hp
      · cases hp
      next st hlook =>
        have hst : P st := ih _ (lookup_mem hlook)
        have hcommit : ∀ {s'' : JSState} {r' : Ret},
            commitPublish s stream st subject payload headers now = .ok (s'', r') →
            ∀ p ∈ s'', P p.2 := by
          intro s'' r' hc p hp
          unfold commitPublish at hc
          cases hc
          cases mem_update_const hp with
          | inl h => rw [h]; exact hpublish _ _ _ _ _ _ hst
          | inr h => exact ih p h
        split at hp
        · split at hp
          · cases hp
          · split at hp
            · split at hp
              · exact hcommit hp
              · cases hp
            · exact hcommit hp
        · cases hp
    | lastMessageForSubject stream subject =>
      have hl : lastMsgStep s stream subject = .ok (s', r) := hstep
      unfold lastMsgStep at hl
      split at hl
      · cases hl
      · split at hl
        · cases hl; exact ih
        · cases hl

/-- Sequences start at `1` and only ever grow, so `0` is never stored. -/
theorem reachable_positive {s : JSState} {name : StreamName} {st : StreamState}
    (hr : Reachable s) (hl : lookupStream s name = some st) : seqPositive st :=
  reachable_all (P := seqPositive)
    (fun _ => ⟨Nat.one_pos, fun _ hm => nomatch hm⟩)
    (fun st subject payload headers rollup now hst => by
      refine ⟨Nat.succ_pos _, ?_⟩
      intro m hm
      rcases mem_applyPublish hm with hold | hnew
      · exact hst.2 m hold
      · rw [hnew]; exact hst.1)
    hr _ (lookup_mem hl)

/-- T6, bound: a positive `maxMessagesPerSubject` bounds every subject's
history on every reachable stream. -/
theorem reachable_capacity {s : JSState} {name : StreamName} {st : StreamState}
    (hr : Reachable s) (hl : lookupStream s name = some st) : capacityBounded st :=
  reachable_all (P := capacityBounded)
    (fun _ _ _ => Nat.zero_le _)
    (fun st subject payload headers rollup now hcap hpos subj => by
      have hpos2 : 0 < st.config.maxMessagesPerSubject := hpos
      show (forSubject (applyPublish st subject payload headers rollup now).1.messages subj).length
        ≤ st.config.maxMessagesPerSubject
      by_cases hsub : subj = subject
      · subst hsub
        rw [forSubject_applyPublish_self]
        exact length_keepLatest_le hpos2 _
      · rw [forSubject_applyPublish_other _ _ _ hsub]
        exact hcap hpos2 subj)
    hr _ (lookup_mem hl)

/-! ## The committed state of a successful publish -/

theorem publish_ok_state {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject : SubjectName} {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {st : StreamState}
    (hs : step s (.publish stream subject payload headers expected? now) = .ok (s', r))
    (hl : lookupStream s stream = some st) :
    lookupStream s' stream
        = some (applyPublish st subject payload headers (isRollup headers) now).1
      ∧ r = .sequence st.nextSequence := by
  have hp : publishStep s stream subject payload headers expected? now = .ok (s', r) := hs
  unfold publishStep at hp
  split at hp
  · cases hp
  next st₀ hlook =>
    rw [hlook] at hl
    cases hl
    split at hp
    · split at hp
      · cases hp
      · split at hp
        · split at hp
          · unfold commitPublish at hp
            cases hp
            exact ⟨lookup_update_const hlook, rfl⟩
          · cases hp
        · unfold commitPublish at hp
          cases hp
          exact ⟨lookup_update_const hlook, rfl⟩
    · cases hp

/-! ## T7 — subject binding -/

/-- T7: a subject not matched by `config.subjects` is `SubjectNotBound`
(`src/internal/JetStreamMemory.ts:139-141`). -/
theorem publish_unbound {s : JSState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {st : StreamState}
    (hl : lookupStream s stream = some st)
    (hnb : matchesAny st.config.subjects subject = false) :
    step s (.publish stream subject payload headers expected? now)
      = .error (.subjectNotBound stream subject) := by
  show publishStep s stream subject payload headers expected? now = _
  simp [publishStep, hl, hnb]

/-! ## T5 — rollup -/

/-- T5, gate: `Nats-Rollup: sub` without `allowRollup` is `RollupNotPermitted`
(`src/internal/JetStreamMemory.ts:142-145`). -/
theorem publish_rollup_denied {s : JSState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {st : StreamState}
    (hl : lookupStream s stream = some st)
    (hbound : matchesAny st.config.subjects subject = true)
    (hroll : isRollup headers = true) (hdeny : st.config.allowRollup = false) :
    step s (.publish stream subject payload headers expected? now)
      = .error (.rollupNotPermitted stream) := by
  show publishStep s stream subject payload headers expected? now = _
  simp [publishStep, hl, hbound, hroll, hdeny]

/-- T5, effect: a rollup publish leaves exactly the new message for its subject. -/
theorem publish_rollup_view {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject : SubjectName} {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {st st' : StreamState}
    (hs : step s (.publish stream subject payload headers expected? now) = .ok (s', r))
    (hroll : isRollup headers = true)
    (hl : lookupStream s stream = some st) (hl' : lookupStream s' stream = some st') :
    forSubject st'.messages subject =
      [{ subject := subject, sequence := st.nextSequence, payload := payload,
         headers := headers, timestampMillis := now }] := by
  have ⟨hl₂, _⟩ := publish_ok_state hs hl
  rw [hl₂] at hl'
  cases hl'
  rw [forSubject_applyPublish_self, hroll, if_pos rfl, List.nil_append, keepLatest_singleton]
  rfl

/-- T5/T6, frame: a publish on `subject` leaves every other subject's view
exactly as it was — rollup and pruning are subject-local. -/
theorem publish_other_subjects_unchanged {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject other : SubjectName} {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {st st' : StreamState}
    (hs : step s (.publish stream subject payload headers expected? now) = .ok (s', r))
    (hl : lookupStream s stream = some st) (hl' : lookupStream s' stream = some st')
    (hne : other ≠ subject) :
    forSubject st'.messages other = forSubject st.messages other := by
  have ⟨hl₂, _⟩ := publish_ok_state hs hl
  rw [hl₂] at hl'
  cases hl'
  exact forSubject_applyPublish_other _ _ _ hne _ _ _ _

/-! ## T4 — compare-and-set -/

private theorem rollup_gate_false {headers : List (String × String)} {st : StreamState}
    (hroll : isRollup headers = true → st.config.allowRollup = true) :
    (isRollup headers && !st.config.allowRollup) = false := by
  cases h : isRollup headers with
  | false => rfl
  | true => rw [hroll h]; rfl

/-- T4, mismatch: the error carries the expected and the actual last sequence
(`src/internal/JetStreamMemory.ts:146-152`). -/
theorem publish_cas_mismatch {s : JSState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {e : StreamSeq} {now : Nat}
    {st : StreamState} (hl : lookupStream s stream = some st)
    (hbound : matchesAny st.config.subjects subject = true)
    (hroll : isRollup headers = true → st.config.allowRollup = true)
    (hne : e ≠ lastSequenceFor st.messages subject) :
    step s (.publish stream subject payload headers (some e) now)
      = .error (.wrongLastSequence stream subject e (lastSequenceFor st.messages subject)) := by
  show publishStep s stream subject payload headers (some e) now = _
  simp [publishStep, hl, hbound, rollup_gate_false hroll, hne]

/-- Success characterisation of `publish`: the four gates, in the
implementation's check order. -/
theorem publish_ok_iff {s : JSState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} :
    (∃ s' r, step s (.publish stream subject payload headers expected? now) = .ok (s', r))
      ↔ ∃ st, lookupStream s stream = some st
          ∧ matchesAny st.config.subjects subject = true
          ∧ (isRollup headers = true → st.config.allowRollup = true)
          ∧ ∀ e, expected? = some e → e = lastSequenceFor st.messages subject := by
  constructor
  · intro ⟨s', r, hs⟩
    have hp : publishStep s stream subject payload headers expected? now = .ok (s', r) := hs
    unfold publishStep at hp
    split at hp
    · cases hp
    next st hlook =>
      refine ⟨st, hlook, ?_⟩
      split at hp
      next hbound =>
        refine ⟨hbound, ?_⟩
        split at hp
        · cases hp
        next hgate =>
          have hroll : isRollup headers = true → st.config.allowRollup = true := by
            intro hr
            cases ha : st.config.allowRollup with
            | true => rfl
            | false => exact absurd (by rw [hr, ha]; rfl) hgate
          refine ⟨hroll, ?_⟩
          split at hp
          next e =>
            split at hp
            next heq => intro e2 he2; cases he2; exact heq
            · cases hp
          · intro e2 he2; cases he2
      · cases hp
  · intro ⟨st, hl, hbound, hroll, hcas⟩
    show ∃ s' r, publishStep s stream subject payload headers expected? now = .ok (s', r)
    unfold publishStep
    rw [hl]
    simp only [hbound, rollup_gate_false hroll]
    cases expected? with
    | none => exact ⟨_, _, rfl⟩
    | some e =>
      have := hcas e rfl
      simp only [this, commitPublish]
      exact ⟨_, _, rfl⟩

/-- T4: with the stream bound and rollup admissible, a CAS publish succeeds
iff the expected sequence is the subject's current last sequence. -/
theorem publish_cas_iff {s : JSState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {e : StreamSeq} {now : Nat}
    {st : StreamState} (hl : lookupStream s stream = some st)
    (hbound : matchesAny st.config.subjects subject = true)
    (hroll : isRollup headers = true → st.config.allowRollup = true) :
    (∃ s' r, step s (.publish stream subject payload headers (some e) now) = .ok (s', r))
      ↔ e = lastSequenceFor st.messages subject := by
  rw [publish_ok_iff]
  constructor
  · intro ⟨st₀, hl₀, _, _, hcas⟩
    rw [hl₀] at hl
    cases hl
    exact hcas e rfl
  · intro h
    exact ⟨st, hl, hbound, hroll, fun e2 he2 => by cases he2; exact h⟩

/-- T4, sentinel: on a reachable stream the CAS reference point is `0` exactly
when the subject has no message (`src/internal/JetStream.ts:37`). -/
theorem lastSequenceFor_eq_zero_iff {s : JSState} {stream : StreamName}
    {subject : SubjectName} {st : StreamState}
    (hr : Reachable s) (hl : lookupStream s stream = some st) :
    lastSequenceFor st.messages subject = 0 ↔ forSubject st.messages subject = [] := by
  have hpos := reachable_positive hr hl
  unfold lastSequenceFor
  constructor
  · intro h
    match hlast : lastForSubject st.messages subject with
    | some m =>
      simp only [hlast] at h
      have hm : 0 < m.sequence := hpos.2 m (mem_forSubject.mp (getLast?_mem hlast)).1
      rw [h] at hm
      exact absurd hm (Nat.lt_irrefl 0)
    | none => exact List.getLast?_eq_none_iff.mp hlast
  · intro h
    have hnone : lastForSubject st.messages subject = none := by
      show (forSubject st.messages subject).getLast? = none
      rw [h]; rfl
    rw [hnone]

/-! ## T3 — lastMessageForSubject -/

/-- T3, absence: an empty subject view is `NoMessageForSubject`
(`src/internal/JetStreamMemory.ts:207-210`). -/
theorem lastMessage_absent {s : JSState} {stream : StreamName} {subject : SubjectName}
    {st : StreamState} (hl : lookupStream s stream = some st)
    (h : forSubject st.messages subject = []) :
    step s (.lastMessageForSubject stream subject)
      = .error (.noMessageForSubject stream subject) := by
  have hnone : lastForSubject st.messages subject = none := by
    show (forSubject st.messages subject).getLast? = none
    rw [h]; rfl
  show lastMsgStep s stream subject = _
  simp only [lastMsgStep, hl, hnone]

/-- T3, success characterisation: the read succeeds iff the subject has a message. -/
theorem lastMessage_ok_iff {s : JSState} {stream : StreamName} {subject : SubjectName}
    {st : StreamState} (hl : lookupStream s stream = some st) :
    (∃ s' r, step s (.lastMessageForSubject stream subject) = .ok (s', r))
      ↔ forSubject st.messages subject ≠ [] := by
  constructor
  · intro ⟨s', r, hs⟩ hnil
    rw [lastMessage_absent hl hnil] at hs
    cases hs
  · intro hne
    match hlast : lastForSubject st.messages subject with
    | some m =>
      refine ⟨s, .message m, ?_⟩
      show lastMsgStep s stream subject = _
      simp only [lastMsgStep, hl, hlast]
    | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) hne

/-- T3: on a reachable state the read leaves the state unchanged and returns a
stored message of the subject whose sequence bounds every other message of that
subject. -/
theorem lastMessage_max {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject : SubjectName} (hr : Reachable s)
    (hs : step s (.lastMessageForSubject stream subject) = .ok (s', r)) :
    s' = s ∧ ∃ st m, lookupStream s stream = some st ∧ r = .message m
      ∧ m ∈ st.messages ∧ m.subject = subject
      ∧ ∀ m' ∈ st.messages, m'.subject = subject → m'.sequence ≤ m.sequence := by
  have hm : lastMsgStep s stream subject = .ok (s', r) := hs
  unfold lastMsgStep at hm
  split at hm
  · cases hm
  next st hlook =>
    split at hm
    next m hlast =>
      cases hm
      have hmem := mem_forSubject.mp (getLast?_mem hlast)
      refine ⟨rfl, st, m, hlook, rfl, hmem.1, hmem.2, ?_⟩
      intro m2 hm2 hsub
      have hpair : (forSubject st.messages subject).Pairwise
          (fun a b => a.sequence < b.sequence) :=
        (reachable_sequences_strict hr hlook).1.filter _
      exact getLast?_max hpair hlast m2 (mem_forSubject.mpr ⟨hm2, hsub⟩)
    · cases hm

/-! ## T6 — retention -/

/-- T6, retention: without rollup, the published subject's view is the prior
view plus the new message, cut to the most recent `maxMessagesPerSubject`
(`src/internal/JetStreamMemory.ts:164-172`). -/
theorem publish_retains_latest {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject : SubjectName} {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {st st' : StreamState}
    (hs : step s (.publish stream subject payload headers expected? now) = .ok (s', r))
    (hroll : isRollup headers = false)
    (hl : lookupStream s stream = some st) (hl' : lookupStream s' stream = some st') :
    forSubject st'.messages subject =
      keepLatest st.config.maxMessagesPerSubject
        (forSubject st.messages subject ++
          [{ subject := subject, sequence := st.nextSequence, payload := payload,
             headers := headers, timestampMillis := now }]) := by
  have ⟨hl₂, _⟩ := publish_ok_state hs hl
  rw [hl₂] at hl'
  cases hl'
  rw [forSubject_applyPublish_self, hroll, if_neg Bool.false_ne_true]
  rfl

theorem applyPublish_drops_oldest {st : StreamState} (hinv : streamInv st)
    (subject : SubjectName) (payload : PayloadHash) (headers : List (String × String))
    (rollup : Bool) (now : Nat) :
    ∀ m ∈ st.messages, m ∉ (applyPublish st subject payload headers rollup now).1.messages →
      ∀ m' ∈ (applyPublish st subject payload headers rollup now).1.messages,
        m'.subject = m.subject → m.sequence < m'.sequence := by
  intro m hm hnot m2 hm2 hsubj
  by_cases hms : m.subject = subject
  · have hm2v : m2 ∈ forSubject
        (applyPublish st subject payload headers rollup now).1.messages subject :=
      mem_forSubject.mpr ⟨hm2, by rw [hsubj, hms]⟩
    have hnotv : m ∉ forSubject
        (applyPublish st subject payload headers rollup now).1.messages subject :=
      fun h => hnot (mem_forSubject.mp h).1
    rw [forSubject_applyPublish_self] at hm2v hnotv
    cases rollup with
    | true =>
      rw [if_pos rfl, List.nil_append, keepLatest_singleton] at hm2v
      rw [List.mem_singleton.mp hm2v]
      exact hinv.2 m hm
    | false =>
      rw [if_neg Bool.false_ne_true] at hm2v hnotv
      have hmv : m ∈ forSubject st.messages subject
          ++ [newMessage st subject payload headers now] :=
        List.mem_append.mpr (Or.inl (mem_forSubject.mpr ⟨hm, hms⟩))
      have hpair : (forSubject st.messages subject
          ++ [newMessage st subject payload headers now]).Pairwise
            (fun a b => a.sequence < b.sequence) :=
        pairwise_append_singleton (hinv.1.filter _)
          (fun a ha => hinv.2 a (mem_forSubject.mp ha).1)
      by_cases h0 : st.config.maxMessagesPerSubject = 0
      · rw [keepLatest, if_pos h0] at hnotv
        exact absurd hmv hnotv
      · rw [keepLatest, if_neg h0] at hm2v hnotv
        exact pairwise_take_drop hpair (mem_take_of_not_mem_drop hmv hnotv) hm2v
  · have hview := forSubject_applyPublish_other st subject m.subject hms payload headers rollup now
    have hmv : m ∈ forSubject st.messages m.subject := mem_forSubject.mpr ⟨hm, rfl⟩
    rw [← hview] at hmv
    exact absurd (mem_forSubject.mp hmv).1 hnot

/-- T6, most-recent: whatever a publish drops — by pruning or by rollup — is
older than everything it keeps for the same subject. -/
theorem publish_drops_oldest {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject : SubjectName} {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat} {st st' : StreamState}
    (hr : Reachable s)
    (hs : step s (.publish stream subject payload headers expected? now) = .ok (s', r))
    (hl : lookupStream s stream = some st) (hl' : lookupStream s' stream = some st') :
    ∀ m ∈ st.messages, m ∉ st'.messages →
      ∀ m' ∈ st'.messages, m'.subject = m.subject → m.sequence < m'.sequence := by
  have ⟨hl₂, _⟩ := publish_ok_state hs hl
  rw [hl₂] at hl'
  cases hl'
  exact applyPublish_drops_oldest (reachable_sequences_strict hr hl) _ _ _ _ _

end EffectNatsSubstrate
