import EffectNatsSubstrate.SubInvariants
import EffectNatsSubstrate.Invariants
import EffectNatsSubstrate.Views

/-!
# Stage-A proof infrastructure

Lookups through the sequential operations, the state shape of each successful
`step`, and the list facts about `entrySequences` that the preservation proofs
use. Nothing here is a statement of the snapshot.
-/

namespace EffectNatsSubstrate

/-! ## Lookups through `updateStream`, `removeStream`, `insertStream` -/

theorem lookupStream_updateStream_self :
    ∀ (s : JSState) (name : StreamName) (st : StreamState) (f : StreamState → StreamState),
      lookupStream s name = some st → lookupStream (updateStream s name f) name = some (f st)
  | [], _, _, _, h => by simp [lookupStream] at h
  | (n, st') :: rest, name, st, f, h => by
    by_cases hn : n = name
    · subst hn
      simp [lookupStream, updateStream] at h ⊢
      exact h ▸ rfl
    · simp [lookupStream, updateStream, hn] at h ⊢
      exact lookupStream_updateStream_self rest name st f h

theorem lookupStream_updateStream_other :
    ∀ (s : JSState) (name n : StreamName) (f : StreamState → StreamState),
      n ≠ name → lookupStream (updateStream s name f) n = lookupStream s n
  | [], _, _, _, _ => rfl
  | (m, st') :: rest, name, n, f, hne => by
    by_cases hm : m = name
    · subst hm
      have hmn : ¬ m = n := fun h => hne h.symm
      simp [lookupStream, updateStream, hmn]
      exact lookupStream_updateStream_other rest m n f hne
    · by_cases hmn : m = n
      · subst hmn; simp [lookupStream, updateStream, hm]
      · simp [lookupStream, updateStream, hm, hmn]
        exact lookupStream_updateStream_other rest name n f hne

theorem lookupStream_removeStream_other :
    ∀ (s : JSState) (name n : StreamName),
      n ≠ name → lookupStream (removeStream s name) n = lookupStream s n
  | [], _, _, _ => rfl
  | (m, st') :: rest, name, n, hne => by
    by_cases hm : m = name
    · subst hm
      have hmn : ¬ m = n := fun h => hne h.symm
      simp [lookupStream, removeStream, hmn]
      exact lookupStream_removeStream_other rest m n hne
    · by_cases hmn : m = n
      · subst hmn; simp [lookupStream, removeStream, hm]
      · simp [lookupStream, removeStream, hm, hmn]
        exact lookupStream_removeStream_other rest name n hne

theorem lookupStream_removeStream_self :
    ∀ (s : JSState) (name : StreamName),
      lookupStream (removeStream s name) name = none
  | [], _ => rfl
  | (n, st) :: rest, name => by
    by_cases hn : n = name
    · simp only [removeStream, if_pos hn]
      exact lookupStream_removeStream_self rest name
    · simp only [removeStream, if_neg hn, lookupStream]
      exact lookupStream_removeStream_self rest name

theorem lookupStream_insertStream_other (s : JSState) (name n : StreamName) (st : StreamState)
    (hne : name ≠ n) : lookupStream (insertStream s name st) n = lookupStream s n := by
  simp [lookupStream, insertStream, hne]

/-! ## The state shape of each successful operation -/

/-- A committed publish advances the head by exactly one. -/
theorem applyPublish_nextSequence (st : StreamState) (subject : SubjectName)
    (payload : PayloadHash) (headers : List (String × String)) (rollup : Bool) (now : Nat) :
    (applyPublish st subject payload headers rollup now).1.nextSequence = st.nextSequence + 1 :=
  rfl

theorem publishStep_ok_eq {s s' : JSState} {r : Ret} {stream : StreamName}
    {subject : SubjectName} {payload : PayloadHash} {headers : List (String × String)}
    {expected? : Option StreamSeq} {now : Nat}
    (h : publishStep s stream subject payload headers expected? now = .ok (s', r)) :
    ∃ st, lookupStream s stream = some st ∧
      s' = updateStream s stream
            (fun _ => (applyPublish st subject payload headers (isRollup headers) now).1) ∧
      r = .sequence st.nextSequence := by
  unfold publishStep at h
  split at h
  · cases h
  · rename_i st hl
    split at h
    · split at h
      · cases h
      · split at h
        · split at h
          · unfold commitPublish at h
            cases h
            exact ⟨st, hl, rfl, rfl⟩
          · cases h
        · unfold commitPublish at h
          cases h
          exact ⟨st, hl, rfl, rfl⟩
    · cases h

theorem deleteStep_ok_eq {s s' : JSState} {r : Ret} {name : StreamName}
    (h : deleteStep s name = .ok (s', r)) : s' = removeStream s name := by
  unfold deleteStep at h
  split at h
  · cases h; rfl
  · cases h

theorem createStep_lookup_preserved {s s' : JSState} {r : Ret} {raw : RawStreamConfig}
    {n : StreamName} {st : StreamState}
    (h : createStep s raw = .ok (s', r)) (hl : lookupStream s n = some st) :
    lookupStream s' n = some st := by
  unfold createStep at h
  split at h
  · cases h
  · rename_i config hval
    split at h
    · split at h
      · cases h; exact hl
      · cases h
    · rename_i habsent
      cases h
      by_cases hn : config.name = n
      · subst hn; rw [hl] at habsent; cases habsent
      · rw [lookupStream_insertStream_other _ _ _ _ hn]; exact hl

theorem createStep_ok_shape {s s' : JSState} {raw : RawStreamConfig} {r : Ret}
    (h : createStep s raw = .ok (s', r)) :
    s' = s ∨ ∃ config, validate raw = .ok config ∧ lookupStream s config.name = none ∧
      s' = insertStream s config.name { config := config, messages := [], nextSequence := 1 } := by
  unfold createStep at h
  split at h
  · cases h
  · rename_i config hval
    split at h
    · split at h
      · cases h; exact Or.inl rfl
      · cases h
    · rename_i hlook
      cases h
      exact Or.inr ⟨config, hval, hlook, rfl⟩

theorem getStep_ok_eq {s s' : JSState} {name : StreamName} {r : Ret}
    (h : getStep s name = .ok (s', r)) : s' = s := by
  unfold getStep at h
  split at h
  · cases h; rfl
  · cases h

theorem lastMsgStep_ok_eq {s s' : JSState} {stream : StreamName} {subject : SubjectName} {r : Ret}
    (h : lastMsgStep s stream subject = .ok (s', r)) : s' = s := by
  unfold lastMsgStep at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

/-- The successful non-publish, non-delete operations keep every lookup that
existed; `step` on them is `createStep`, `getStep`, or `lastMsgStep`. -/
theorem step_lookup_preserved {s s' : JSState} {r : Ret} {o : Op} {n : StreamName}
    {st : StreamState} (h : step s o = .ok (s', r)) (hl : lookupStream s n = some st)
    (hnp : ∀ stream subject payload headers x now, o ≠ .publish stream subject payload headers x now)
    (hnd : ∀ name, o ≠ .deleteStream name) :
    lookupStream s' n = some st := by
  cases o with
  | createStream raw => exact createStep_lookup_preserved h hl
  | getStream name =>
    have h' : getStep s name = .ok (s', r) := h
    unfold getStep at h'
    split at h'
    · cases h'; exact hl
    · cases h'
  | deleteStream name => exact absurd rfl (hnd name)
  | publish stream subject payload headers x now => exact absurd rfl (hnp stream subject payload headers x now)
  | lastMessageForSubject stream subject =>
    have h' : lastMsgStep s stream subject = .ok (s', r) := h
    unfold lastMsgStep at h'
    split at h'
    · cases h'
    · split at h'
      · cases h'; exact hl
      · cases h'

/-! ## `entrySequences` and `Pairwise` -/

theorem entrySequences_append (a b : List Observed) :
    entrySequences (a ++ b) = entrySequences a ++ entrySequences b := by
  simp [entrySequences, List.filterMap_append]

theorem entrySequences_map_entry (l : List StoredMessage) :
    entrySequences (l.map Observed.entry) = l.map (·.sequence) := by
  induction l with
  | nil => rfl
  | cons m rest ih => simp [entrySequences] at ih ⊢; exact ih

theorem entrySequences_caughtUp : entrySequences [Observed.caughtUp] = [] := rfl

theorem entrySequences_entry_singleton (m : StoredMessage) :
    entrySequences [Observed.entry m] = [m.sequence] := rfl

theorem entrySequences_failed (e : SubError) : entrySequences [Observed.failed e] = [] := rfl

/-! ## Equations for `visible` across an admitted message or a drain -/

theorem entrySequences_visible_admit (sub : Subscriber) (m : StoredMessage) :
    entrySequences (visible { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence })
      = entrySequences (visible sub) ++ [m.sequence] := by
  simp [visible, entrySequences_append, entrySequences_map_entry, entrySequences_entry_singleton,
    List.map_append]

/-- A recorded failure adds no entry sequence, whatever is still buffered. -/
theorem entrySequences_visible_fail (sub : Subscriber) (e : SubError) :
    entrySequences (visible { sub with observed := sub.observed ++ [Observed.failed e],
                                       status := .shutDown })
      = entrySequences (visible sub) := by
  simp only [visible]
  rw [entrySequences_append, entrySequences_append, entrySequences_failed, List.append_nil,
    entrySequences_append]

/-- Registration's visible sequences are exactly the replay, without the `caughtUp` marker. -/
theorem entrySequences_visible_newSubscriber (stream : StreamName) (opts : ConsumeOptions)
    (l₀ : StreamSeq) (messages : List StoredMessage) :
    entrySequences (visible (newSubscriber stream opts l₀ messages))
      = (selectReplay messages opts).map (·.sequence) := by
  simp [visible, newSubscriber, replayObserved, entrySequences_append, entrySequences_map_entry,
    entrySequences_caughtUp]

theorem visible_admit (sub : Subscriber) (m : StoredMessage) :
    visible { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence }
      = visible sub ++ [Observed.entry m] := by
  simp [visible, List.map_append, List.append_assoc]

theorem visible_drain (sub : Subscriber) :
    visible { sub with observed := sub.observed ++ sub.pending.map Observed.entry, pending := [] }
      = visible sub := by
  simp [visible]

theorem visible_drain_done (sub : Subscriber) (e : SubError) :
    visible { sub with observed := sub.observed ++ sub.pending.map Observed.entry, pending := [],
                       status := QueueStatus.done e }
      = visible sub := by
  simp [visible]

theorem getLast?_visible_ne_failed {sub : Subscriber} {e : SubError}
    (hne : sub.pending ≠ []) :
    (sub.observed ++ sub.pending.map Observed.entry).getLast?
      ≠ some (Observed.failed e) := by
  intro h''
  rw [List.getLast?_append, List.getLast?_map] at h''
  cases hlast : sub.pending.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) hne
  | some x => rw [hlast] at h''; simp at h''

theorem pairwise_sublist_of_append_left {l₁ l₂ : List Nat}
    (h : (l₁ ++ l₂).Pairwise (· < ·)) : l₁.Pairwise (· < ·) :=
  (List.pairwise_append.mp h).1

/-! ## `SubInv` across a core change that keeps the subscriber's stream -/

/-- A subscriber untouched by a transition keeps `SubInv` when, while it is registered,
its own stream's lookup survives with a non-decreasing head. -/
theorem SubInv.of_stream_lookup {s s' : SubState} {sub : Subscriber} (hinv : SubInv s sub)
    (hcore : sub.registered = true → ∀ st₀, lookupStream s.core sub.stream = some st₀ →
      ∃ st₁, lookupStream s'.core sub.stream = some st₁ ∧ st₀.nextSequence ≤ st₁.nextSequence) :
    SubInv s' sub := by
  refine ⟨hinv.capacityPos, hinv.capacity, hinv.registeredOpen, ?_, hinv.closingNonempty,
    hinv.doneEmpty, hinv.shutDownClear, hinv.pendingMatch, hinv.visibleStrict, hinv.visibleBound,
    hinv.pendingLast⟩
  intro hr
  obtain ⟨st₀, hl, hlt⟩ := hinv.registeredStream hr
  obtain ⟨st₁, hl', hle⟩ := hcore hr _ hl
  exact ⟨st₁, hl', Nat.lt_of_lt_of_le hlt hle⟩

/-- A drain: the buffer emptied into `observed`, with the status and registration flag possibly
changed. Every clause discharges from the old invariant plus where the entries went; the three
`pullStep` success arms are its instances. -/
theorem SubInv.pulled {s : SubState} {sub sub' : Subscriber} (hinv : SubInv s sub)
    (hempty : sub'.pending = []) (hpol : sub'.policy = sub.policy)
    (hlast : sub'.lastEnqueued = sub.lastEnqueued)
    (hvis : entrySequences (visible sub') = entrySequences (visible sub))
    (hopen : sub'.registered = true → sub'.status = .opened)
    (hclosing : ∀ e, sub'.status ≠ .closing e)
    (hshut : sub'.status = .shutDown → sub'.registered = false)
    (hstream : sub'.registered = true → ∃ st₀, lookupStream s.core sub'.stream = some st₀ ∧
      sub'.lastEnqueued < st₀.nextSequence) :
    SubInv s sub' := by
  refine ⟨?_, ?_, hopen, hstream, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpol]; exact hinv.capacityPos
  · rw [hempty]; exact Nat.zero_le _
  · intro e he; exact absurd he (hclosing e)
  · intro _ _; exact hempty
  · intro he; exact ⟨hshut he, hempty⟩
  · intro m hm; rw [hempty] at hm; cases hm
  · rw [hvis]; exact hinv.visibleStrict
  · intro n hn; rw [hvis] at hn; rw [hlast]; exact hinv.visibleBound n hn
  · intro hcon; rw [hempty] at hcon; exact absurd rfl hcon

end EffectNatsSubstrate
