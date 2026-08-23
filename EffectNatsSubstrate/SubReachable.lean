import EffectNatsSubstrate.SubProofs
import EffectNatsSubstrate.Proofs

/-!
# Stage-A proofs — the invariant over `ReachableSub`

Assembles the per-label preservation lemmas of `SubProofs.lean` into SA2
(`stateInv_reachable`) and SA3 (`pending_le_capacity`, T14′ safety).
-/

namespace EffectNatsSubstrate

/-! ## Membership through `lookupSub` and `updateSub` -/

theorem mem_of_lookupSub :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {sub : Subscriber},
      lookupSub subs id = some sub → (id, sub) ∈ subs
  | [], _, _, h => by cases h
  | (i, s₀) :: rest, id, sub, h => by
    by_cases hi : i = id
    · subst hi
      simp only [lookupSub] at h
      cases h
      exact List.mem_cons_self
    · simp only [lookupSub, if_neg hi] at h
      exact List.mem_cons_of_mem _ (mem_of_lookupSub h)

theorem mem_updateSub :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {f : Subscriber → Subscriber}
      {p : SubId × Subscriber},
      p ∈ updateSub subs id f → p ∈ subs ∨ ∃ sub, (p.1, sub) ∈ subs ∧ p.2 = f sub
  | [], _, _, _, h => by cases h
  | (i, sub) :: rest, id, f, p, h => by
    by_cases hi : i = id
    · subst hi
      simp only [updateSub] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨sub, List.mem_cons_self, rfl⟩
      · rcases mem_updateSub h with h1 | ⟨sub', h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨sub', List.mem_cons_of_mem _ h1, h2⟩
    · simp only [updateSub, if_neg hi] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_updateSub h with h1 | ⟨sub', h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨sub', List.mem_cons_of_mem _ h1, h2⟩

/-! ## `StateInv` preserved by each label -/

theorem afterOp_inv {s : SubState} {core' : JSState} {o : Op} {r : Ret}
    (hinv : StateInv s) (hstep : step s.core o = .ok (core', r)) :
    StateInv (afterOp deliverOne s core' o r) := by
  cases o with
  | publish stream subject payload headers x now =>
    have hpub : publishStep s.core stream subject payload headers x now = .ok (core', r) := hstep
    obtain ⟨st, hl, hceq, hr⟩ := publishStep_ok_eq hpub
    subst hr
    simp only [afterOp]
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine deliverOne_inv (hinv q hq) hl rfl ?_ ?_
    · intro n st₀ hl₀
      by_cases hn : n = stream
      · subst hn
        rw [hl] at hl₀
        cases hl₀
        refine ⟨(applyPublish st subject payload headers (isRollup headers) now).1, ?_, ?_⟩
        · show lookupStream core' n = some _
          rw [hceq]
          exact lookupStream_updateStream_self _ _ _ _ hl
        · show st.nextSequence
            ≤ (applyPublish st subject payload headers (isRollup headers) now).1.nextSequence
          simp [applyPublish]
      · refine ⟨st₀, ?_, Nat.le_refl _⟩
        show lookupStream core' n = some st₀
        rw [hceq, lookupStream_updateStream_other _ _ _ _ hn]
        exact hl₀
    · refine ⟨(applyPublish st subject payload headers (isRollup headers) now).1, ?_, ?_⟩
      · show lookupStream core' stream = some _
        rw [hceq]
        exact lookupStream_updateStream_self _ _ _ _ hl
      · show st.nextSequence
          < (applyPublish st subject payload headers (isRollup headers) now).1.nextSequence
        simp [applyPublish]
  | deleteStream name =>
    have hdel : deleteStep s.core name = .ok (core', r) := hstep
    have hceq := deleteStep_ok_eq hdel
    simp only [afterOp]
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine endOne_inv (hinv q hq) ?_
    intro n st₀ hn hl
    show lookupStream core' n = some st₀
    rw [hceq, lookupStream_removeStream_other _ _ _ hn]
    exact hl
  | createStream raw =>
    simp only [afterOp]
    intro p hp
    exact (hinv p hp).of_lookups
      (fun n st₀ hl => ⟨st₀, createStep_lookup_preserved hstep hl, Nat.le_refl _⟩)
  | getStream name =>
    simp only [afterOp]
    intro p hp
    exact (hinv p hp).of_lookups
      (fun n st₀ hl => ⟨st₀, step_lookup_preserved hstep hl (by intros; simp) (by intros; simp),
        Nat.le_refl _⟩)
  | lastMessageForSubject stream subject =>
    simp only [afterOp]
    intro p hp
    exact (hinv p hp).of_lookups
      (fun n st₀ hl => ⟨st₀, step_lookup_preserved hstep hl (by intros; simp) (by intros; simp),
        Nat.le_refl _⟩)

theorem applyOp_inv {s s' : SubState} {o : Op} {e : Expect} (hinv : StateInv s)
    (h : applyOp deliverOne s o e = some s') : StateInv s' := by
  unfold applyOp at h
  split at h
  · rename_i core' r r' hstep
    split at h
    · cases h; exact afterOp_inv hinv hstep
    · cases h
  · rename_i err err' hstep
    split at h
    · cases h; exact hinv
    · cases h
  · cases h

theorem applyRegister_inv {s s' : SubState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} {e : Expect}
    (hreach : Reachable s.core) (hinv : StateInv s)
    (h : applyRegister s stream opts l₀ id e = some s') : StateInv s' := by
  unfold applyRegister at h
  split at h
  · cases h
  · rename_i hguard
    split at h
    · split at h
      · cases h; exact hinv
      · cases h
    · rename_i st hl
      split at h
      · rename_i hbound
        cases h
        intro p hp
        have hp' : p ∈ s.subs ++ [(id, newSubscriber stream opts l₀ st.messages)] := hp
        rcases List.mem_append.mp hp' with hold | hnew
        · exact (hinv p hold).core_eq rfl
        · rw [List.mem_singleton.mp hnew]
          have hcap : opts.buffer.capacity ≠ 0 := by
            intro hz
            apply hguard
            simp [hz]
          exact newSubscriber_inv hl hcap hbound (reachable_sequences_strict hreach hl).1
      · cases h
    · cases h

theorem applyPull_inv {s s' : SubState} {id : SubId} (hinv : StateInv s)
    (h : applyPull pullStep s id = some s') : StateInv s' := by
  unfold applyPull at h
  split at h
  · cases h
  · rename_i sub hsub
    split at h
    · cases h
    · rename_i sub' hpull
      cases h
      intro p hp
      have hp' : p ∈ updateSub s.subs id (fun _ => sub') := hp
      rcases mem_updateSub hp' with hold | ⟨_, _, hp2⟩
      · exact (hinv p hold).core_eq rfl
      · rw [hp2]
        exact (pullStep_inv (hinv _ (mem_of_lookupSub hsub)) hpull).core_eq rfl

theorem applyUnsubscribe_inv {s s' : SubState} {id : SubId} (hinv : StateInv s)
    (h : applyUnsubscribe s id = some s') : StateInv s' := by
  unfold applyUnsubscribe at h
  split at h
  · cases h
  · rename_i sub hsub
    split at h
    · cases h
    · cases h
      intro p hp
      have hp' : p ∈ updateSub s.subs id
          (fun sub => { sub with registered := false, pending := [], status := .shutDown }) := hp
      rcases mem_updateSub hp' with hold | ⟨sub₀, h₀, hp2⟩
      · exact (hinv p hold).core_eq rfl
      · rw [hp2]
        exact (unsubscribe_inv (hinv _ h₀)).core_eq rfl

theorem apply_inv {s s' : SubState} {l : Label} (hreach : Reachable s.core) (hinv : StateInv s)
    (h : apply s l = some s') : StateInv s' := by
  cases l with
  | op o e => exact applyOp_inv hinv h
  | register stream opts l₀ id e => exact applyRegister_inv hreach hinv h
  | pull id => exact applyPull_inv hinv h
  | unsubscribe id => exact applyUnsubscribe_inv hinv h

/-- SA2 — the representation invariant holds on every reachable state. -/
theorem stateInv_reachable {s : SubState} (h : ReachableSub s) : StateInv s := by
  induction h with
  | init => intro p hp; cases hp
  | step hs hnext ih => exact apply_inv (reachableSub_core hs) ih hnext

/-- SA3 — T14′ safety: the buffer never exceeds its capacity. -/
theorem pending_le_capacity {s : SubState} (h : ReachableSub s) :
    ∀ p ∈ s.subs, p.2.pending.length ≤ p.2.policy.capacity :=
  fun p hp => (stateInv_reachable h p hp).capacity

end EffectNatsSubstrate
