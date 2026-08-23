import EffectNatsSubstrate.SubCore

/-!
# Stage-A proofs

Proofs of the r3 statements over `ReachableSub`. This file starts with the
frame theorem (SA1): every label either leaves the sequential core unchanged
or moves it by one `step`, so `Reachable` — and with it T1–T7 — holds of the
core of every reachable subscriber state.
-/

namespace EffectNatsSubstrate

section Frame

variable {deliver : StreamName → StoredMessage → Subscriber → Subscriber}
variable {pull : Subscriber → Option Subscriber}

theorem afterOp_core (s : SubState) (core' : JSState) (o : Op) (r : Ret) :
    (afterOp deliver s core' o r).core = core' := by
  unfold afterOp
  split <;> rfl

theorem applyOp_core {s s' : SubState} {o : Op} {e : Expect}
    (h : applyOp deliver s o e = some s') :
    s'.core = s.core ∨ ∃ r, step s.core o = .ok (s'.core, r) := by
  unfold applyOp at h
  split at h
  · rename_i core' r r' hstep
    split at h
    · cases h
      right
      refine ⟨r, ?_⟩
      rw [afterOp_core]
      exact hstep
    · cases h
  · rename_i err err' hstep
    split at h
    · cases h
      left
      rfl
    · cases h
  · cases h

theorem applyRegister_core {s s' : SubState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} {e : Expect}
    (h : applyRegister s stream opts l₀ id e = some s') : s'.core = s.core := by
  unfold applyRegister at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · split at h
      · cases h; rfl
      · cases h
    · cases h

theorem applyPull_core {s s' : SubState} {id : SubId}
    (h : applyPull pull s id = some s') : s'.core = s.core := by
  unfold applyPull at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem applyUnsubscribe_core {s s' : SubState} {id : SubId}
    (h : applyUnsubscribe s id = some s') : s'.core = s.core := by
  unfold applyUnsubscribe at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem apply_core {s s' : SubState} {l : Label} (h : apply s l = some s') :
    s'.core = s.core ∨ ∃ o r, step s.core o = .ok (s'.core, r) := by
  cases l with
  | op o e =>
    rcases applyOp_core (deliver := deliverOne) h with hc | ⟨r, hr⟩
    · exact Or.inl hc
    · exact Or.inr ⟨o, r, hr⟩
  | register stream opts l₀ id e => exact Or.inl (applyRegister_core h)
  | pull id => exact Or.inl (applyPull_core (pull := pullStep) h)
  | unsubscribe id => exact Or.inl (applyUnsubscribe_core h)

/-- SA1 — the frame theorem: T1–T7 hold of the core of every reachable state. -/
theorem reachableSub_core {s : SubState} (h : ReachableSub s) : Reachable s.core := by
  induction h with
  | init => exact Reachable.init
  | step _ hnext ih =>
    rcases apply_core hnext with hc | ⟨o, r, hr⟩
    · rw [hc]; exact ih
    · exact Reachable.step ih hr

end Frame

/-! ## `selectReplay` (SA4b, and what registration needs) -/

theorem selectReplay_sublist (messages : List StoredMessage) (opts : ConsumeOptions) :
    (selectReplay messages opts).Sublist messages := by
  cases hs : opts.start <;> simp only [selectReplay, hs]
  · exact List.filter_sublist
  · exact List.filter_sublist.trans List.filter_sublist
  · exact List.nil_sublist _
  · exact List.filter_sublist.trans List.filter_sublist
  · exact List.filter_sublist.trans List.filter_sublist

theorem selectReplay_mem {messages : List StoredMessage} {opts : ConsumeOptions}
    {m : StoredMessage} (h : m ∈ selectReplay messages opts) :
    m ∈ messages ∧ matchesAny opts.filters m.subject = true := by
  cases hs : opts.start <;> simp only [selectReplay, hs] at h
  · exact List.mem_filter.mp h
  · exact List.mem_filter.mp (List.mem_filter.mp h).1
  · cases h
  · exact List.mem_filter.mp (List.mem_filter.mp h).1
  · exact List.mem_filter.mp (List.mem_filter.mp h).1

theorem selectReplay_pairwise {messages : List StoredMessage} {opts : ConsumeOptions}
    (h : messages.Pairwise (fun a b => a.sequence < b.sequence)) :
    (selectReplay messages opts).Pairwise (fun a b => a.sequence < b.sequence) :=
  List.Pairwise.sublist (selectReplay_sublist messages opts) h

theorem entrySequences_visible_newSubscriber (stream : StreamName) (opts : ConsumeOptions)
    (l₀ : StreamSeq) (messages : List StoredMessage) :
    entrySequences (visible (newSubscriber stream opts l₀ messages))
      = (selectReplay messages opts).map (·.sequence) := by
  simp [visible, newSubscriber, replayObserved, entrySequences_append, entrySequences_map_entry,
    entrySequences_caughtUp]

/-! ## Preservation of `SubInv` under `register`, `pull`, `unsubscribe` -/

theorem newSubscriber_inv {s : SubState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {st : StreamState}
    (hl : lookupStream s.core stream = some st) (hcap : opts.buffer.capacity ≠ 0)
    (hbound : replayBound st.messages opts l₀ st.nextSequence = true)
    (hstrict : st.messages.Pairwise (fun a b => a.sequence < b.sequence)) :
    SubInv s (newSubscriber stream opts l₀ st.messages) := by
  have hrb := hbound
  simp only [replayBound, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrb
  obtain ⟨hall, hlt⟩ := hrb
  constructor
  · exact Nat.pos_of_ne_zero hcap
  · exact Nat.zero_le _
  · intro _; rfl
  · intro _; exact ⟨st, hl, hlt⟩
  · intro e h; cases h
  · intro e h; cases h
  · intro h; cases h
  · intro m hm; cases hm
  · rw [entrySequences_visible_newSubscriber, List.pairwise_map]
    exact selectReplay_pairwise hstrict
  · intro n hn
    rw [entrySequences_visible_newSubscriber, List.mem_map] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    exact hall m hm
  · intro h; exact absurd rfl h

theorem registered_false_of_status {s : SubState} {sub : Subscriber} (hinv : SubInv s sub)
    (hne : sub.status ≠ .opened) : sub.registered = false := by
  cases hr : sub.registered with
  | false => rfl
  | true => exact absurd (hinv.registeredOpen hr) hne

theorem pullStep_inv {s : SubState} {sub sub' : Subscriber} (hinv : SubInv s sub)
    (h : pullStep sub = some sub') : SubInv s sub' := by
  unfold pullStep at h
  split at h
  · cases h
  · rename_i e hst
    cases h
    have hpend : sub.pending = [] := hinv.doneEmpty e hst
    have hreg : sub.registered = false :=
      registered_false_of_status hinv (by rw [hst]; intro h'; cases h')
    have hvis : entrySequences (visible { sub with observed := sub.observed ++ [.failed e],
                                                   status := .shutDown })
        = entrySequences (visible sub) := by
      simp [visible, hpend, entrySequences_append, entrySequences_failed]
    constructor
    · exact hinv.capacityPos
    · exact hinv.capacity
    · intro hr; have hr' : sub.registered = true := hr; simp [hreg] at hr'
    · intro hr; have hr' : sub.registered = true := hr; simp [hreg] at hr'
    · intro e' h'; cases h'
    · intro e' h'; cases h'
    · intro _; exact ⟨hreg, hpend⟩
    · exact hinv.pendingMatch
    · rw [hvis]; exact hinv.visibleStrict
    · intro n hn; rw [hvis] at hn; exact hinv.visibleBound n hn
    · intro h'; exact absurd hpend h'
  · rename_i hst
    split at h
    · cases h
    · rename_i hne
      cases h
      have hvis : entrySequences (visible { sub with observed := sub.observed ++ sub.pending.map Observed.entry,
                                                     pending := [] })
          = entrySequences (visible sub) := by
        simp [visible]
      constructor
      · exact hinv.capacityPos
      · exact Nat.zero_le _
      · intro hr; have hr' : sub.registered = true := hr; exact hinv.registeredOpen hr'
      · intro hr; have hr' : sub.registered = true := hr; exact hinv.registeredStream hr'
      · intro e' h'; have h'' : sub.status = .closing e' := h'; simp [hst] at h''
      · intro e' h'; have h'' : sub.status = .done e' := h'; simp [hst] at h''
      · intro h'; have h'' : sub.status = .shutDown := h'; simp [hst] at h''
      · intro m hm; cases hm
      · rw [hvis]; exact hinv.visibleStrict
      · intro n hn; rw [hvis] at hn; exact hinv.visibleBound n hn
      · intro h'; exact absurd rfl h'
  · rename_i e hst
    split at h
    · cases h
    · rename_i hne
      cases h
      have hreg : sub.registered = false :=
        registered_false_of_status hinv (by rw [hst]; intro h'; cases h')
      have hvis : entrySequences (visible { sub with observed := sub.observed ++ sub.pending.map Observed.entry,
                                                     pending := [], status := .done e })
          = entrySequences (visible sub) := by
        simp [visible]
      constructor
      · exact hinv.capacityPos
      · exact Nat.zero_le _
      · intro hr; have hr' : sub.registered = true := hr; simp [hreg] at hr'
      · intro hr; have hr' : sub.registered = true := hr; simp [hreg] at hr'
      · intro e' h'; cases h'
      · intro e' _; rfl
      · intro h'; cases h'
      · intro m hm; cases hm
      · rw [hvis]; exact hinv.visibleStrict
      · intro n hn; rw [hvis] at hn; exact hinv.visibleBound n hn
      · intro h'; exact absurd rfl h'

theorem unsubscribe_inv {s : SubState} {sub : Subscriber} (hinv : SubInv s sub) :
    SubInv s { sub with registered := false, pending := [], status := .shutDown } := by
  have hstrict := hinv.visibleStrict
  unfold visible at hstrict
  rw [entrySequences_append] at hstrict
  constructor
  · exact hinv.capacityPos
  · exact Nat.zero_le _
  · intro hr; cases hr
  · intro hr; cases hr
  · intro e h; cases h
  · intro e h; cases h
  · intro _; exact ⟨rfl, rfl⟩
  · intro m hm; cases hm
  · simp only [visible, List.map_nil, List.append_nil]
    exact pairwise_sublist_of_append_left hstrict
  · intro n hn
    simp only [visible, List.map_nil, List.append_nil] at hn
    apply hinv.visibleBound
    unfold visible
    rw [entrySequences_append]
    exact List.mem_append_left _ hn
  · intro h; exact absurd rfl h

end EffectNatsSubstrate
