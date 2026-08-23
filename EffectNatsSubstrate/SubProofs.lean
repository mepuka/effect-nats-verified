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
    exact SubInv.pulled hinv hpend rfl rfl (entrySequences_visible_fail sub e)
      (fun hr => absurd hr (by simp [hreg])) (fun _ he => by simp at he) (fun _ => hreg)
      hinv.registeredStream
  · rename_i hst
    split at h
    · cases h
    · cases h
      refine SubInv.pulled hinv rfl rfl rfl (congrArg entrySequences (visible_drain sub))
        hinv.registeredOpen ?_ ?_ hinv.registeredStream
      · intro e' he'
        have h'' : sub.status = .closing e' := he'
        simp [hst] at h''
      · intro h'
        have h'' : sub.status = .shutDown := h'
        simp [hst] at h''
  · rename_i e hst
    split at h
    · cases h
    · cases h
      have hreg : sub.registered = false :=
        registered_false_of_status hinv (by rw [hst]; intro h'; cases h')
      refine SubInv.pulled hinv rfl rfl rfl (congrArg entrySequences (visible_drain_done sub e))
        (fun hr => absurd hr (by simp [hreg])) ?_ ?_ hinv.registeredStream
      · intro e' he'
        have h'' : QueueStatus.done e = .closing e' := he'
        simp at h''
      · intro h'
        have h'' : QueueStatus.done e = .shutDown := h'
        simp at h''

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

/-! ## `SubInv` depends on the state only through its core -/

theorem SubInv.core_eq {s s' : SubState} {sub : Subscriber} (hinv : SubInv s sub)
    (h : s.core = s'.core) : SubInv s' sub :=
  hinv.of_stream_lookup fun _ st₀ hl => ⟨st₀, by rw [← h]; exact hl, Nat.le_refl _⟩

/-- A subscriber untouched by a transition keeps `SubInv` when the core's lookups survive
with non-decreasing heads. -/
theorem SubInv.of_lookups {s s' : SubState} {sub : Subscriber} (hinv : SubInv s sub)
    (hcore : ∀ n st₀, lookupStream s.core n = some st₀ →
      ∃ st₁, lookupStream s'.core n = some st₁ ∧ st₀.nextSequence ≤ st₁.nextSequence) :
    SubInv s' sub :=
  hinv.of_stream_lookup fun _ _ hl => hcore _ _ hl

/-! ## Preservation under fan-out and deletion -/

theorem deliverOne_admit {stream : StreamName} {m : StoredMessage} {sub : Subscriber} {n : Nat}
    (hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters m.subject) = true)
    (hpol : sub.policy = .terminateOnLag n) (hroom : sub.pending.length < n)
    (ho : sub.status = .opened) :
    deliverOne stream m sub = { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence } := by
  unfold deliverOne
  rw [if_pos hcond]
  simp only [hpol]
  rw [if_neg (Nat.not_le.mpr hroom), if_pos ho]

theorem deliverOne_overflow {stream : StreamName} {m : StoredMessage} {sub : Subscriber} {n : Nat}
    (hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters m.subject) = true)
    (hpol : sub.policy = .terminateOnLag n) (hfull : n ≤ sub.pending.length) :
    deliverOne stream m sub =
      { sub with
          registered := false
          status :=
            if sub.pending.isEmpty then .done (.consumerLagged stream sub.lastEnqueued)
            else .closing (.consumerLagged stream sub.lastEnqueued) } := by
  unfold deliverOne
  rw [if_pos hcond]
  simp only [hpol]
  rw [if_pos hfull]

theorem deliverOne_skip {stream : StreamName} {m : StoredMessage} {sub : Subscriber}
    (hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters m.subject) = false) :
    deliverOne stream m sub = sub := by
  unfold deliverOne
  rw [if_neg (by simp [hcond])]

/-- On overflow the buffer is non-empty (`capacityPos`), so the failure is `closing`,
not `done` — the drain-first discipline of Q2. -/
theorem deliverOne_overflow_closing {s : SubState} {stream : StreamName} {m : StoredMessage}
    {sub : Subscriber} {n : Nat} (hinv : SubInv s sub)
    (hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters m.subject) = true)
    (hpol : sub.policy = .terminateOnLag n) (hfull : n ≤ sub.pending.length) :
    deliverOne stream m sub =
      { sub with registered := false,
                 status := .closing (.consumerLagged stream sub.lastEnqueued) }
    ∧ sub.pending ≠ [] := by
  have hcapPos : 1 ≤ sub.policy.capacity := hinv.capacityPos
  rw [hpol] at hcapPos
  simp only [Policy.capacity] at hcapPos
  have hne : sub.pending ≠ [] := fun hnil => by
    rw [hnil] at hfull
    simp at hfull
    omega
  have hempty : sub.pending.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  refine ⟨?_, hne⟩
  rw [deliverOne_overflow hcond hpol hfull, if_neg (by rw [hempty]; decide)]

theorem endOne_skip {name : StreamName} {sub : Subscriber}
    (hcond : (sub.stream == name && sub.registered) = false) : endOne name sub = sub := by
  unfold endOne
  rw [if_neg (by simp [hcond])]

theorem deliverOne_inv {s s' : SubState} {stream : StreamName} {st : StreamState}
    {m : StoredMessage} {sub : Subscriber} (hinv : SubInv s sub)
    (hl : lookupStream s.core stream = some st) (hseq : m.sequence = st.nextSequence)
    (hcore : ∀ n st₀, lookupStream s.core n = some st₀ →
      ∃ st₁, lookupStream s'.core n = some st₁ ∧ st₀.nextSequence ≤ st₁.nextSequence)
    (hbump : ∃ st', lookupStream s'.core stream = some st' ∧ st.nextSequence < st'.nextSequence) :
    SubInv s' (deliverOne stream m sub) := by
  by_cases hcond : (sub.stream == stream && sub.registered && matchesAny sub.filters m.subject) = true
  · obtain ⟨⟨hstream, hreg⟩, hmatch⟩ := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
    have hopen : sub.status = .opened := hinv.registeredOpen hreg
    obtain ⟨st₀, hl₀, hlt₀⟩ := hinv.registeredStream hreg
    rw [hstream, hl] at hl₀
    cases hl₀
    cases hpol : sub.policy with
    | terminateOnLag n =>
      by_cases hfull : n ≤ sub.pending.length
      · obtain ⟨heq, hne⟩ := deliverOne_overflow_closing hinv hcond hpol hfull
        rw [heq]
        refine ⟨hinv.capacityPos, hinv.capacity, ?_, ?_, ?_, ?_, ?_, hinv.pendingMatch,
          hinv.visibleStrict, hinv.visibleBound, hinv.pendingLast⟩
        · intro hr; cases hr
        · intro hr; cases hr
        · intro e h; exact hne
        · intro e h; cases h
        · intro h; cases h
      · rw [deliverOne_admit hcond hpol (Nat.lt_of_not_le hfull) hopen]
        have hlt : sub.pending.length < n := Nat.lt_of_not_le hfull
        obtain ⟨st', hl', hbump'⟩ := hbump
        have hvis := entrySequences_visible_admit sub m
        refine ⟨hinv.capacityPos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show (sub.pending ++ [m]).length ≤ sub.policy.capacity
          rw [hpol, List.length_append, List.length_singleton]
          simp only [Policy.capacity]
          omega
        · intro _; exact hopen
        · intro _
          refine ⟨st', ?_, ?_⟩
          · show lookupStream s'.core sub.stream = some st'
            rw [hstream]; exact hl'
          · show m.sequence < st'.nextSequence
            rw [hseq]; exact hbump'
        · intro e h; have h' : sub.status = .closing e := h; simp [hopen] at h'
        · intro e h; have h' : sub.status = .done e := h; simp [hopen] at h'
        · intro h; have h' : sub.status = .shutDown := h; simp [hopen] at h'
        · intro m' hm'
          have hm'' : m' ∈ sub.pending ++ [m] := hm'
          rcases List.mem_append.mp hm'' with hold | hnew
          · exact hinv.pendingMatch m' hold
          · rw [List.mem_singleton.mp hnew]; exact hmatch
        · rw [hvis]
          apply pairwise_append_singleton hinv.visibleStrict
          intro y hy
          have := hinv.visibleBound y hy
          rw [hseq]
          exact Nat.lt_of_le_of_lt this hlt₀
        · intro y hy
          rw [hvis] at hy
          show y ≤ m.sequence
          rcases List.mem_append.mp hy with hold | hnew
          · have := hinv.visibleBound y hold
            rw [hseq]
            exact Nat.le_of_lt (Nat.lt_of_le_of_lt this hlt₀)
          · rw [List.mem_singleton.mp hnew]; exact Nat.le_refl _
        · intro _
          show ((sub.pending ++ [m]).map (·.sequence)).getLast? = some m.sequence
          simp
  · rw [deliverOne_skip (by simpa using hcond)]
    exact SubInv.of_lookups hinv hcore

theorem endOne_inv {s s' : SubState} {name : StreamName} {sub : Subscriber} (hinv : SubInv s sub)
    (hcore : ∀ n st₀, n ≠ name → lookupStream s.core n = some st₀ →
      lookupStream s'.core n = some st₀) :
    SubInv s' (endOne name sub) := by
  unfold endOne
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hstream, hreg⟩ := hcond
    refine ⟨hinv.capacityPos, hinv.capacity, ?_, ?_, ?_, ?_, ?_, hinv.pendingMatch,
      hinv.visibleStrict, hinv.visibleBound, hinv.pendingLast⟩
    · intro hr; cases hr
    · intro hr; cases hr
    · intro e h
      have h' : (if sub.pending.isEmpty then QueueStatus.done (.streamNotFound name)
                  else .closing (.streamNotFound name)) = .closing e := h
      intro hnil
      rw [hnil] at h'
      simp at h'
    · intro e h
      have h' : (if sub.pending.isEmpty then QueueStatus.done (.streamNotFound name)
                  else .closing (.streamNotFound name)) = .done e := h
      cases hp : sub.pending with
      | nil => rfl
      | cons x xs => rw [hp] at h'; simp at h'
    · intro h
      have h' : (if sub.pending.isEmpty then QueueStatus.done (.streamNotFound name)
                  else .closing (.streamNotFound name)) = .shutDown := h
      split at h' <;> cases h'
  · rename_i hcond
    refine SubInv.of_stream_lookup hinv ?_
    intro hreg st₀ hl
    have hne : sub.stream ≠ name := by
      intro heq
      apply hcond
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨heq, hreg⟩
    exact ⟨st₀, hcore _ _ hne hl, Nat.le_refl _⟩

end EffectNatsSubstrate
