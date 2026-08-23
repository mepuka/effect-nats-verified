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

theorem mem_updateSub_eq :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {f : Subscriber → Subscriber}
      {p : SubId × Subscriber},
      p ∈ updateSub subs id f → p ∈ subs ∨ (p.1 = id ∧ ∃ sub, (id, sub) ∈ subs ∧ p.2 = f sub)
  | [], _, _, _, h => by cases h
  | (i, sub) :: rest, id, f, p, h => by
    by_cases hi : i = id
    · subst hi
      simp only [updateSub] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨rfl, sub, List.mem_cons_self, rfl⟩
      · rcases mem_updateSub_eq h with h1 | ⟨hp1, sub', h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨hp1, sub', List.mem_cons_of_mem _ h1, h2⟩
    · simp only [updateSub, if_neg hi] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_updateSub_eq h with h1 | ⟨hp1, sub', h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨hp1, sub', List.mem_cons_of_mem _ h1, h2⟩

theorem mem_updateSub :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {f : Subscriber → Subscriber}
      {p : SubId × Subscriber},
      p ∈ updateSub subs id f → p ∈ subs ∨ ∃ sub, (p.1, sub) ∈ subs ∧ p.2 = f sub := by
  intro subs id f p h
  rcases mem_updateSub_eq h with h1 | ⟨hp1, sub, h1, h2⟩
  · exact Or.inl h1
  · subst hp1
    exact Or.inr ⟨sub, h1, h2⟩

/-! ## The enabling condition of `register` -/

/-- A successful registration is for the next id with a positive capacity. -/
theorem applyRegister_enabled {s s' : SubState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} {e : Expect}
    (h : applyRegister s stream opts l₀ id e = some s') :
    id = s.nextId ∧ opts.buffer.capacity ≠ 0 := by
  unfold applyRegister at h
  split at h
  · cases h
  · rename_i hguard
    refine ⟨?_, ?_⟩
    · by_cases hne : id = s.nextId
      · exact hne
      · exfalso
        apply hguard
        simp [hne]
    · intro hz
      apply hguard
      simp [hz]

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
          rw [applyPublish_nextSequence]
          exact Nat.le_succ _
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
        rw [applyPublish_nextSequence]
        exact Nat.lt_succ_self _
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
  rcases e with r | err
  · obtain ⟨core', hstep, hs'⟩ := applyOp_ok_eq h
    rw [hs']
    exact afterOp_inv hinv hstep
  · obtain ⟨hs', -⟩ := applyOp_error_eq h
    rw [hs']
    exact hinv

theorem applyRegister_inv {s s' : SubState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} {e : Expect}
    (hreach : Reachable s.core) (hinv : StateInv s)
    (h : applyRegister s stream opts l₀ id e = some s') : StateInv s' := by
  have hcap : opts.buffer.capacity ≠ 0 := (applyRegister_enabled h).2
  rcases applyRegister_ok_eq h with ⟨_, _, heq⟩ | ⟨st, hl, _, hb, heq⟩
  · rw [heq]; exact hinv
  · rw [heq]
    intro p hp
    have hp' : p ∈ s.subs ++ [(id, newSubscriber stream opts l₀ st.messages)] := hp
    rcases List.mem_append.mp hp' with hold | hnew
    · exact (hinv p hold).core_eq rfl
    · rw [List.mem_singleton.mp hnew]
      exact newSubscriber_inv hl hcap hb (reachable_sequences_strict hreach hl).1

theorem applyPull_inv {s s' : SubState} {id : SubId} (hinv : StateInv s)
    (h : applyPull pullStep s id = some s') : StateInv s' := by
  obtain ⟨sub, sub', hsub, hpull, heq⟩ := applyPull_ok_eq h
  rw [heq]
  intro p hp
  have hp' : p ∈ updateSub s.subs id (fun _ => sub') := hp
  rcases mem_updateSub hp' with hold | ⟨_, _, hp2⟩
  · exact (hinv p hold).core_eq rfl
  · rw [hp2]
    exact (pullStep_inv (hinv _ (mem_of_lookupSub hsub)) hpull).core_eq rfl

theorem applyUnsubscribe_inv {s s' : SubState} {id : SubId} (hinv : StateInv s)
    (h : applyUnsubscribe s id = some s') : StateInv s' := by
  obtain ⟨sub, hsub, _, heq⟩ := applyUnsubscribe_ok_eq h
  rw [heq]
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

/-- The one induction principle every further reachable-state fact goes through
(package `AGENTS.md`): the step case may assume the pre-state is reachable and
satisfies `StateInv`. -/
theorem reachableSub_all {P : SubState → Prop} (hinit : P initialSub)
    (hstep : ∀ {s s' : SubState} {l : Label}, ReachableSub s → StateInv s → P s →
      apply s l = some s' → P s')
    {s : SubState} (h : ReachableSub s) : P s := by
  induction h with
  | init => exact hinit
  | step hr hnext ih => exact hstep hr (stateInv_reachable hr) ih hnext

/-! ## `lookupSub` through `updateSub`, appends, and value maps -/

theorem lookupSub_updateSub_self :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {sub : Subscriber}
      (f : Subscriber → Subscriber),
      lookupSub subs id = some sub → lookupSub (updateSub subs id f) id = some (f sub)
  | [], _, _, _, h => by cases h
  | (i, s₀) :: rest, id, sub, f, h => by
    by_cases hi : i = id
    · subst hi
      simp only [lookupSub] at h
      cases h
      simp [updateSub, lookupSub]
    · simp only [lookupSub, if_neg hi] at h
      simp only [updateSub, if_neg hi, lookupSub]
      exact lookupSub_updateSub_self f h

theorem lookupSub_none_of_fresh :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId},
      (∀ p ∈ subs, p.1 ≠ id) → lookupSub subs id = none
  | [], _, _ => rfl
  | (i, s₀) :: rest, id, h => by
    have hi : i ≠ id := h (i, s₀) List.mem_cons_self
    simp only [lookupSub, if_neg hi]
    exact lookupSub_none_of_fresh (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem lookupSub_append_fresh :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {sub : Subscriber},
      (∀ p ∈ subs, p.1 ≠ id) → lookupSub (subs ++ [(id, sub)]) id = some sub
  | [], _, _, _ => by simp [lookupSub]
  | (i, s₀) :: rest, id, sub, hfresh => by
    have hi : i ≠ id := hfresh (i, s₀) List.mem_cons_self
    simp only [List.cons_append, lookupSub, if_neg hi]
    exact lookupSub_append_fresh (fun p hp => hfresh p (List.mem_cons_of_mem _ hp))

/-- Looking up through a value map. -/
theorem lookupSub_map :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} (g : Subscriber → Subscriber),
      lookupSub (subs.map (fun p => (p.1, g p.2))) id = (lookupSub subs id).map g
  | [], _, _ => rfl
  | (i, s₀) :: rest, id, g => by
    by_cases hi : i = id
    · simp only [List.map_cons, lookupSub, if_pos hi]
      rfl
    · simp only [List.map_cons, lookupSub, if_neg hi]
      exact lookupSub_map g

/-- With strictly ascending ids, membership determines the lookup. -/
theorem lookupSub_of_mem_pairwise :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {sub : Subscriber},
      (subs.map Prod.fst).Pairwise (· < ·) → (id, sub) ∈ subs → lookupSub subs id = some sub
  | [], _, _, _, h => by cases h
  | (i, s₀) :: rest, id, sub, hp, h => by
    rw [List.map_cons, List.pairwise_cons] at hp
    obtain ⟨hlt, hrest⟩ := hp
    rcases List.mem_cons.mp h with heq | hmem
    · cases heq
      simp [lookupSub]
    · have hi : i ≠ id := by
        intro hi
        have hmemid : id ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(id, sub), hmem, rfl⟩
        have := hlt id hmemid
        rw [hi] at this
        exact Nat.lt_irrefl _ this
      simp only [lookupSub, if_neg hi]
      exact lookupSub_of_mem_pairwise hrest hmem

theorem updateSub_keys :
    ∀ (subs : List (SubId × Subscriber)) (id : SubId) (f : Subscriber → Subscriber),
      (updateSub subs id f).map Prod.fst = subs.map Prod.fst
  | [], _, _ => rfl
  | (i, s₀) :: rest, id, f => by
    by_cases hi : i = id
    · simp only [updateSub, if_pos hi, List.map_cons]
      rw [updateSub_keys rest id f]
    · simp only [updateSub, if_neg hi, List.map_cons]
      rw [updateSub_keys rest id f]

theorem keys_map_snd :
    ∀ (l : List (SubId × Subscriber)) (g : SubId × Subscriber → Subscriber),
      (l.map (fun p => (p.1, g p))).map Prod.fst = l.map Prod.fst
  | [], _ => rfl
  | p :: rest, g => by
    show p.1 :: (rest.map (fun p => (p.1, g p))).map Prod.fst = p.1 :: rest.map Prod.fst
    rw [keys_map_snd rest g]

/-! ## The state shape is preserved and holds on every reachable state -/

theorem shape_of_keys {s s' : SubState} (hs : SubShape s)
    (hk : s'.subs.map Prod.fst = s.subs.map Prod.fst) (hn : s.nextId ≤ s'.nextId) :
    SubShape s' := by
  obtain ⟨hasc, hids⟩ := hs
  refine ⟨by rw [hk]; exact hasc, ?_⟩
  intro p hp
  have hmem : p.1 ∈ s'.subs.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [hk] at hmem
  obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hmem
  rw [← hqp]
  exact Nat.lt_of_lt_of_le (hids q hq) hn

theorem apply_shape {s s' : SubState} {l : Label} (h : apply s l = some s') (hs : SubShape s) :
    SubShape s' := by
  cases l with
  | op o e =>
    cases e with
    | ok r =>
      obtain ⟨core', hstep, rfl⟩ :=
        applyOp_ok_eq (deliver := deliverOne)
          (show applyOp deliverOne s o (.ok r) = some s' from h)
      unfold afterOp
      split
      · exact shape_of_keys hs (keys_map_snd _ _) (Nat.le_refl _)
      · exact shape_of_keys hs (keys_map_snd _ _) (Nat.le_refl _)
      · exact shape_of_keys hs rfl (Nat.le_refl _)
    | error err =>
      obtain ⟨heq, -⟩ :=
        applyOp_error_eq (deliver := deliverOne)
          (show applyOp deliverOne s o (.error err) = some s' from h)
      rw [heq]
      exact hs
  | register stream opts l₀ id e =>
    obtain ⟨hid, _⟩ :=
      applyRegister_enabled (show applyRegister s stream opts l₀ id e = some s' from h)
    rcases applyRegister_ok_eq (s' := s')
        (show applyRegister s stream opts l₀ id e = some s' from h)
      with ⟨_, _, heq⟩ | ⟨st, hl, _, _, heq⟩
    · rw [heq]; exact hs
    · rw [heq]
      obtain ⟨hasc, hids⟩ := hs
      refine ⟨?_, ?_⟩
      · show ((s.subs ++ [(id, _)]).map Prod.fst).Pairwise (· < ·)
        rw [List.map_append]
        apply pairwise_append_singleton hasc
        intro y hy
        obtain ⟨q, hq, hqy⟩ := List.mem_map.mp hy
        rw [← hqy, hid]
        exact hids q hq
      · intro p hp
        have hp' : p ∈ s.subs ++ [(id, _)] := hp
        rcases List.mem_append.mp hp' with hold | hnew
        · show p.1 < id + 1
          have := hids p hold
          rw [← hid] at this
          exact Nat.lt_succ_of_lt this
        · rw [List.mem_singleton.mp hnew]
          exact Nat.lt_succ_self id
  | pull id =>
    obtain ⟨_, _, _, _, heq⟩ :=
      applyPull_ok_eq (s' := s') (show applyPull pullStep s id = some s' from h)
    refine shape_of_keys hs ?_ ?_
    · rw [heq]; exact updateSub_keys _ _ _
    · rw [heq]; exact Nat.le_refl _
  | unsubscribe id =>
    obtain ⟨_, _, _, heq⟩ :=
      applyUnsubscribe_ok_eq (s' := s') (show applyUnsubscribe s id = some s' from h)
    refine shape_of_keys hs ?_ ?_
    · rw [heq]; exact updateSub_keys _ _ _
    · rw [heq]; exact Nat.le_refl _

/-- The state shape holds on every reachable state: ids strictly ascending, all below `nextId`. -/
theorem subShape_reachable {s : SubState} (h : ReachableSub s) : SubShape s :=
  reachableSub_all ⟨List.Pairwise.nil, fun _ hp => nomatch hp⟩
    (fun _ _ hs hnext => apply_shape hnext hs) h

end EffectNatsSubstrate
