import EffectNatsSubstrate.SimRelation
import EffectNatsSubstrate.ApplyLemmas
import EffectNatsSubstrate.SimAgree
import EffectNatsSubstrate.EffectQueueLaws
import EffectNatsSubstrate.RtInvariants

/-!
# `a4_inclusion` — the simulation (stage B1, packet P4b)

The main stage-B1 theorem: every runtime execution that ends with no fan-out in flight is
matched by a stage-A label sequence (`docs/stage-b1-proof-map.md` §2.4, §3 P4b). The proof is a
direct induction on the runtime execution carrying the relation of `SimRelation.lean`: an already
matched abstract prefix `labels` and an owed suffix `owed` (the abstract publish or deletion of
the fan-out in flight, then the consumer labels of subscribers whose linearization point has
passed). `endFanOut` pays the IOU; extraction at a quiescent state reads the witness off `labels`.

`RtInv` on the reachable runtime state is an input: `rtInv_reachable` is packet P2 and is not on
`main` yet, so the theorems here take it as a hypothesis — `a4_inclusion_of_rtInv` is
`A4Inclusion` modulo that one fact, and the coordinator closes `a4_inclusion` after P2 merges.
-/

namespace EffectNatsSubstrate

/-! ## Runtime association lists -/

theorem mem_of_lookupRt : ∀ (l : List (SubId × RtSubscriber)) (id : SubId) (r : RtSubscriber),
    lookupRt l id = some r → (id, r) ∈ l := by
  intro l
  induction l with
  | nil => intro id r h; cases h
  | cons p rest ih =>
    obtain ⟨i, sub⟩ := p
    intro id r h
    simp only [lookupRt] at h
    by_cases hi : i = id
    · rw [if_pos hi] at h
      cases h
      cases hi
      exact List.Mem.head _
    · rw [if_neg hi] at h
      exact List.Mem.tail _ (ih id r h)

theorem lookupRt_updateRt_self : ∀ (l : List (SubId × RtSubscriber)) (id : SubId)
    (f : RtSubscriber → RtSubscriber),
    lookupRt (updateRt l id f) id = (lookupRt l id).map f := by
  intro l
  induction l with
  | nil => intro id f; rfl
  | cons p rest ih =>
    obtain ⟨i, sub⟩ := p
    intro id f
    by_cases hi : i = id
    · simp only [updateRt, if_pos hi, lookupRt]
      rfl
    · simp only [updateRt, if_neg hi, lookupRt]
      exact ih id f

theorem lookupRt_updateRt_ne : ∀ (l : List (SubId × RtSubscriber)) (i j : SubId)
    (f : RtSubscriber → RtSubscriber), i ≠ j →
    lookupRt (updateRt l j f) i = lookupRt l i := by
  intro l
  induction l with
  | nil => intro i j f _; rfl
  | cons p rest ih =>
    obtain ⟨k, sub⟩ := p
    intro i j f hij
    by_cases hkj : k = j
    · have hki : k ≠ i := fun he => hij (he.symm.trans hkj)
      simp only [updateRt, if_pos hkj, lookupRt, if_neg hki]
      exact ih i j f hij
    · simp only [updateRt, if_neg hkj, lookupRt]
      by_cases hki : k = i
      · simp only [if_pos hki]
      · simp only [if_neg hki]
        exact ih i j f hij

theorem updateRt_keys : ∀ (l : List (SubId × RtSubscriber)) (id : SubId)
    (f : RtSubscriber → RtSubscriber),
    (updateRt l id f).map Prod.fst = l.map Prod.fst := by
  intro l
  induction l with
  | nil => intro id f; rfl
  | cons p rest ih =>
    obtain ⟨i, sub⟩ := p
    intro id f
    by_cases hi : i = id
    · simp only [updateRt, if_pos hi, List.map_cons, ih]
    · simp only [updateRt, if_neg hi, List.map_cons, ih]

theorem lookupSub_updateSub_map : ∀ (subs : List (SubId × Subscriber)) (id : SubId)
    (f : Subscriber → Subscriber),
    lookupSub (updateSub subs id f) id = (lookupSub subs id).map f := by
  intro subs
  induction subs with
  | nil => intro id f; rfl
  | cons p rest ih =>
    obtain ⟨i, sub⟩ := p
    intro id f
    by_cases hi : i = id
    · simp only [updateSub, if_pos hi, lookupSub]
      rfl
    · simp only [updateSub, if_neg hi, lookupSub]
      exact ih id f

/-- Equal key lists make the two sides' lookups defined together. -/
theorem lookupSub_isSome_of_keys {rs : List (SubId × RtSubscriber)} {as : List (SubId × Subscriber)}
    (hkeys : as.map Prod.fst = rs.map Prod.fst) :
    ∀ id r, lookupRt rs id = some r → ∃ a, lookupSub as id = some a := by
  induction rs generalizing as with
  | nil => intro id r h; cases h
  | cons p rest ih =>
    obtain ⟨i, sub⟩ := p
    cases as with
    | nil => intro id r _; simp at hkeys
    | cons q qs =>
      obtain ⟨j, a⟩ := q
      simp only [List.map_cons, List.cons.injEq] at hkeys
      obtain ⟨hij, htl⟩ := hkeys
      intro id r h
      simp only [lookupRt] at h
      by_cases hi : i = id
      · exact ⟨a, by simp only [lookupSub, if_pos (hij.trans hi)]⟩
      · rw [if_neg hi] at h
        have hji : ¬ j = id := fun he => hi (hij.symm.trans he)
        obtain ⟨b, hb⟩ := ih (as := qs) htl id r h
        exact ⟨b, by simp only [lookupSub, if_neg hji]; exact hb⟩

/-! ## Folding stage-A labels -/

theorem runLabels_cons (s : SubState) (l : Label) (ls : List Label) :
    runLabels s (l :: ls) = match apply s l with | some s' => runLabels s' ls | none => none := rfl

theorem runLabels_single (s : SubState) (l : Label) : runLabels s [l] = apply s l := by
  rw [runLabels_cons]
  cases apply s l <;> rfl

theorem runLabels_append : ∀ (l₁ : List Label) {s t : SubState} (l₂ : List Label),
    runLabels s l₁ = some t → runLabels s (l₁ ++ l₂) = runLabels t l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro s t l₂ h; cases h; rfl
  | cons l rest ih =>
    intro s t l₂ h
    rw [runLabels_cons] at h
    cases hap : apply s l with
    | none => rw [hap] at h; cases h
    | some u =>
      rw [hap] at h
      show runLabels s (l :: (rest ++ l₂)) = _
      rw [runLabels_cons, hap]
      exact ih l₂ h

theorem runLabels_snoc {s t u : SubState} {ls : List Label} {l : Label}
    (h : runLabels s ls = some t) (h' : apply t l = some u) :
    runLabels s (ls ++ [l]) = some u := by
  rw [runLabels_append ls [l] h, runLabels_single]
  exact h'

/-- A list of consumer labels of subscribers other than `i` leaves `i` alone. -/
theorem runLabels_lookup_frame {i : SubId} : ∀ (ls : List Label) {s t : SubState},
    (∀ l ∈ ls, ∃ j, (l = .pull j ∨ l = .unsubscribe j) ∧ j ≠ i) →
    runLabels s ls = some t → lookupSub t.subs i = lookupSub s.subs i := by
  intro ls
  induction ls with
  | nil => intro s t _ h; cases h; rfl
  | cons l rest ih =>
    intro s t hls h
    rw [runLabels_cons] at h
    cases hap : apply s l with
    | none => rw [hap] at h; cases h
    | some u =>
      rw [hap] at h
      obtain ⟨j, hj, hji⟩ := hls l (List.Mem.head _)
      have hstep : lookupSub u.subs i = lookupSub s.subs i := by
        rcases hj with hj | hj <;> subst hj
        · exact (applyPull_other hji hap).1
        · exact (applyUnsubscribe_other hji hap).1
      exact (ih (fun m hm => hls m (List.Mem.tail _ hm)) h).trans hstep

/-- … and leaves the core, `nextId`, and the key list alone. -/
theorem runLabels_consumer_frame : ∀ (ls : List Label) {s t : SubState},
    (∀ l ∈ ls, ∃ j, l = .pull j ∨ l = .unsubscribe j) →
    runLabels s ls = some t →
    t.core = s.core ∧ t.nextId = s.nextId ∧ t.subs.map Prod.fst = s.subs.map Prod.fst := by
  intro ls
  induction ls with
  | nil => intro s t _ h; cases h; exact ⟨rfl, rfl, rfl⟩
  | cons l rest ih =>
    intro s t hls h
    rw [runLabels_cons] at h
    cases hap : apply s l with
    | none => rw [hap] at h; cases h
    | some u =>
      rw [hap] at h
      obtain ⟨j, hj⟩ := hls l (List.Mem.head _)
      have hstep : u.core = s.core ∧ u.nextId = s.nextId ∧
          u.subs.map Prod.fst = s.subs.map Prod.fst := by
        rcases hj with hj | hj <;> subst hj
        · obtain ⟨sub, sub', _, _, heq⟩ :=
            applyPull_ok_eq (pull := pullStep) (show applyPull pullStep s j = some u from hap)
          rw [heq]
          exact ⟨rfl, rfl, updateSub_keys _ _ _⟩
        · obtain ⟨_, _, _, heq⟩ :=
            applyUnsubscribe_ok_eq (show applyUnsubscribe s j = some u from hap)
          rw [heq]
          exact ⟨rfl, rfl, updateSub_keys _ _ _⟩
      obtain ⟨h₁, h₂, h₃⟩ := ih (fun m hm => hls m (List.Mem.tail _ hm)) h
      exact ⟨h₁.trans hstep.1, h₂.trans hstep.2.1, h₃.trans hstep.2.2⟩

/-! ## Agreement away from one subscriber -/

/-- Two abstract states that differ at most at `i`. -/
def AgreeExcept (i : SubId) (s t : SubState) : Prop :=
  t.core = s.core ∧ t.nextId = s.nextId ∧ t.subs.map Prod.fst = s.subs.map Prod.fst ∧
    ∀ j, j ≠ i → lookupSub t.subs j = lookupSub s.subs j

theorem agreeExcept_refl (i : SubId) (s : SubState) : AgreeExcept i s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem agreeExcept_of_pull {i : SubId} {s t : SubState} (h : apply s (.pull i) = some t) :
    AgreeExcept i s t := by
  obtain ⟨sub, sub', _, _, heq⟩ :=
    applyPull_ok_eq (pull := pullStep) (show applyPull pullStep s i = some t from h)
  refine ⟨by rw [heq], by rw [heq], by rw [heq]; exact updateSub_keys _ _ _, fun j hj => ?_⟩
  rw [heq]
  exact lookupSub_updateSub_ne s.subs i j (fun _ => sub') (fun he => hj he.symm)

theorem agreeExcept_of_unsubscribe {i : SubId} {s t : SubState}
    (h : apply s (.unsubscribe i) = some t) : AgreeExcept i s t := by
  obtain ⟨_, _, _, heq⟩ := applyUnsubscribe_ok_eq (show applyUnsubscribe s i = some t from h)
  refine ⟨by rw [heq], by rw [heq], by rw [heq]; exact updateSub_keys _ _ _, fun j hj => ?_⟩
  rw [heq]
  exact lookupSub_updateSub_ne s.subs i j _ (fun he => hj he.symm)

/-- Updating both sides at the same key other than `i` keeps the agreement. -/
theorem agreeExcept_update {i j : SubId} {s t : SubState} (hag : AgreeExcept i s t)
    (g : Subscriber → Subscriber) (hji : j ≠ i) :
    AgreeExcept i { s with subs := updateSub s.subs j g }
      { t with subs := updateSub t.subs j g } := by
  obtain ⟨hcore, hnext, hkeys, hlook⟩ := hag
  refine ⟨hcore, hnext, ?_, fun k hk => ?_⟩
  · show (updateSub t.subs j g).map Prod.fst = (updateSub s.subs j g).map Prod.fst
    rw [updateSub_keys, updateSub_keys]; exact hkeys
  · show lookupSub (updateSub t.subs j g) k = lookupSub (updateSub s.subs j g) k
    by_cases hkj : k = j
    · subst hkj
      rw [lookupSub_updateSub_map, lookupSub_updateSub_map, hlook k hk]
    · rw [lookupSub_updateSub_ne t.subs j k g (fun he => hkj he.symm),
        lookupSub_updateSub_ne s.subs j k g (fun he => hkj he.symm)]
      exact hlook k hk

/-- Every label that is not a consumer label of `i` is enabled in one of two states agreeing away
from `i` exactly when it is in the other, and the results still agree away from `i`. -/
theorem apply_agreeExcept {i : SubId} {s t s' : SubState} {l : Label}
    (hag : AgreeExcept i s t) (hl : ∀ j, (l = .pull j ∨ l = .unsubscribe j) → j ≠ i)
    (h : apply s l = some s') : ∃ t', apply t l = some t' ∧ AgreeExcept i s' t' := by
  obtain ⟨hcore, hnext, hkeys, hlook⟩ := hag
  cases l with
  | op o e =>
    have hop : applyOp deliverOne s o e = some s' := h
    rcases e with r | err
    · obtain ⟨core', hstep, hs'⟩ := applyOp_ok_eq (deliver := deliverOne) hop
      have hstept : step t.core o = .ok (core', r) := by rw [hcore]; exact hstep
      refine ⟨afterOp deliverOne t core' o r, applyOp_ok_of_step hstept, ?_⟩
      rw [hs']
      have hgen : ∀ g : SubId × Subscriber → Subscriber,
          AgreeExcept i { s with core := core', subs := s.subs.map (fun p => (p.1, g p)) }
            { t with core := core', subs := t.subs.map (fun p => (p.1, g p)) } := by
        intro g
        refine ⟨rfl, hnext, ?_, fun j hj => ?_⟩
        · show (t.subs.map (fun p => (p.1, g p))).map Prod.fst =
              (s.subs.map (fun p => (p.1, g p))).map Prod.fst
          rw [keys_map_snd, keys_map_snd, hkeys]
        · show lookupSub (t.subs.map (fun p => (p.1, g p))) j =
              lookupSub (s.subs.map (fun p => (p.1, g p))) j
          cases hb : lookupSub t.subs j with
          | none =>
            rw [lookupSub_map_pair_none g hb,
              lookupSub_map_pair_none g (by rw [← hlook j hj]; exact hb)]
          | some b =>
            rw [lookupSub_map_pair_some g hb,
              lookupSub_map_pair_some g (by rw [← hlook j hj]; exact hb)]
      have hframe : AgreeExcept i { s with core := core' } { t with core := core' } :=
        ⟨rfl, hnext, hkeys, hlook⟩
      cases o with
      | publish stream subject payload headers _el now =>
        cases r with
        | sequence seq =>
          exact hgen (fun p => deliverOne stream
            { subject := subject, sequence := seq, payload := payload, headers := headers,
              timestampMillis := now } p.2)
        | _ => exact hframe
      | deleteStream name => cases r <;> exact hgen (fun p => endOne name p.2)
      | createStream _ => cases r <;> exact hframe
      | getStream _ => cases r <;> exact hframe
      | lastMessageForSubject _ _ => cases r <;> exact hframe
    · obtain ⟨hs', hstep⟩ := applyOp_error_eq (deliver := deliverOne) hop
      refine ⟨t, applyOp_error_of_step (by rw [hcore]; exact hstep), ?_⟩
      rw [hs']
      exact ⟨hcore, hnext, hkeys, hlook⟩
  | register stream opts l₀ id e =>
    have hreg : applyRegister s stream opts l₀ id e = some s' := h
    have hguards : ¬(id ≠ s.nextId || opts.buffer.capacity = 0) := by
      intro hbad
      have : applyRegister s stream opts l₀ id e = none := by
        unfold applyRegister; rw [if_pos hbad]
      rw [this] at hreg; cases hreg
    have hguardt : ¬(id ≠ t.nextId || opts.buffer.capacity = 0) := by rw [hnext]; exact hguards
    rcases applyRegister_ok_eq hreg with ⟨hnone, he, hs'⟩ | ⟨st, hlk, he, hbound, hs'⟩
    · refine ⟨t, ?_, ?_⟩
      · show applyRegister t stream opts l₀ id e = some t
        unfold applyRegister
        split
        · rename_i hc; exact absurd hc hguardt
        · rw [hcore, hnone, he]; simp
      · rw [hs']; exact ⟨hcore, hnext, hkeys, hlook⟩
    · refine ⟨{ t with subs := t.subs ++ [(id, newSubscriber stream opts l₀ st.messages)],
                       nextId := id + 1 }, ?_, ?_⟩
      · show applyRegister t stream opts l₀ id e = _
        unfold applyRegister
        split
        · rename_i hc; exact absurd hc hguardt
        · rw [hcore, hlk, he]; simp [hbound]
      · rw [hs']
        refine ⟨hcore, rfl, ?_, fun j hj => ?_⟩
        · show (t.subs ++ [(id, newSubscriber stream opts l₀ st.messages)]).map Prod.fst =
              (s.subs ++ [(id, newSubscriber stream opts l₀ st.messages)]).map Prod.fst
          rw [List.map_append, List.map_append]
          exact congrArg (· ++ [id]) hkeys
        · show lookupSub (t.subs ++ _) j = lookupSub (s.subs ++ _) j
          rw [lookupSub_append, lookupSub_append, hlook j hj]
  | pull j =>
    have hji : j ≠ i := hl j (Or.inl rfl)
    obtain ⟨sub, sub', hlk, hpull, hs'⟩ :=
      applyPull_ok_eq (pull := pullStep) (show applyPull pullStep s j = some s' from h)
    have hlkt : lookupSub t.subs j = some sub := (hlook j hji).trans hlk
    refine ⟨{ t with subs := updateSub t.subs j (fun _ => sub') }, ?_, ?_⟩
    · show applyPull pullStep t j = _
      unfold applyPull
      simp only [hlkt, hpull]
    · rw [hs']
      exact agreeExcept_update ⟨hcore, hnext, hkeys, hlook⟩ (fun _ => sub') hji
  | unsubscribe j =>
    have hji : j ≠ i := hl j (Or.inr rfl)
    obtain ⟨sub, hlk, hst, hs'⟩ :=
      applyUnsubscribe_ok_eq (show applyUnsubscribe s j = some s' from h)
    have hlkt : lookupSub t.subs j = some sub := (hlook j hji).trans hlk
    refine ⟨{ t with subs := updateSub t.subs j (fun sub =>
                { sub with registered := false, pending := [], status := .shutDown }) }, ?_, ?_⟩
    · show applyUnsubscribe t j = _
      unfold applyUnsubscribe
      simp only [hlkt, if_neg hst]
    · rw [hs']
      exact agreeExcept_update ⟨hcore, hnext, hkeys, hlook⟩ _ hji

/-! ## Runs and the chunk history -/

theorem abstractHistoryFrom_cons (id : SubId) (s : SubState) (h : History) (l : Label)
    (ls : List Label) :
    abstractHistoryFrom id s h (l :: ls) =
      match apply s l with
      | some s' => abstractHistoryFrom id s' (afterLabel s s' id h l) ls
      | none => none := rfl

/-- A run that succeeds records a history. -/
theorem abstractHistoryFrom_isSome (id : SubId) : ∀ (ls : List Label) {s t : SubState}
    (h : History), runLabels s ls = some t → ∃ h', abstractHistoryFrom id s h ls = some h' := by
  intro ls
  induction ls with
  | nil => intro s t h _; exact ⟨h, rfl⟩
  | cons l rest ih =>
    intro s t h hrun
    rw [runLabels_cons] at hrun
    cases hap : apply s l with
    | none => rw [hap] at hrun; cases hrun
    | some u =>
      rw [hap] at hrun
      rw [abstractHistoryFrom_cons, hap]
      exact ih _ hrun

theorem abstractHistoryFrom_append (id : SubId) : ∀ (l₁ : List Label) {s t : SubState}
    {h h₁ : History} (l₂ : List Label), runLabels s l₁ = some t →
    abstractHistoryFrom id s h l₁ = some h₁ →
    abstractHistoryFrom id s h (l₁ ++ l₂) = abstractHistoryFrom id t h₁ l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro s t h h₁ l₂ hrun hhist
    cases hrun
    cases hhist
    rfl
  | cons l rest ih =>
    intro s t h h₁ l₂ hrun hhist
    rw [runLabels_cons] at hrun
    cases hap : apply s l with
    | none => rw [hap] at hrun; cases hrun
    | some u =>
      rw [hap] at hrun
      rw [abstractHistoryFrom_cons, hap] at hhist
      show abstractHistoryFrom id s h (l :: (rest ++ l₂)) = _
      rw [abstractHistoryFrom_cons, hap]
      exact ih l₂ hrun hhist

/-- Labels that are neither a pull nor a registration of `id` leave `id`'s history alone. -/
theorem abstractHistoryFrom_frame (id : SubId) : ∀ (ls : List Label) {s t : SubState}
    {h : History},
    (∀ l ∈ ls, (∀ j, l = .pull j → j ≠ id) ∧
      ∀ stream opts l₀ j e, l = .register stream opts l₀ j e → j ≠ id) →
    runLabels s ls = some t → abstractHistoryFrom id s h ls = some h := by
  intro ls
  induction ls with
  | nil => intro s t h _ _; rfl
  | cons l rest ih =>
    intro s t h hls hrun
    rw [runLabels_cons] at hrun
    cases hap : apply s l with
    | none => rw [hap] at hrun; cases hrun
    | some u =>
      rw [hap] at hrun
      rw [abstractHistoryFrom_cons, hap]
      obtain ⟨hp, hr⟩ := hls l (List.Mem.head _)
      have hafter : afterLabel s u id h l = h := by
        cases l with
        | op _ _ => rfl
        | register stream opts l₀ j e =>
          show (if j = id then [observedOf u id] else h) = h
          exact if_neg (hr stream opts l₀ j e rfl)
        | pull j =>
          show (if j = id then h ++ [(observedOf u id).drop (observedOf s id).length] else h) = h
          exact if_neg (hp j rfl)
        | unsubscribe _ => rfl
      show abstractHistoryFrom id u (afterLabel s u id h l) rest = some h
      rw [hafter]
      exact ih (fun m hm => hls m (List.Mem.tail _ hm)) hrun

/-! ## Transporting a history across an agreement -/

/-- Both sides updated at the same key by the same function keep the agreement. -/
theorem agreeAt_update {k j : SubId} {s t : SubState} (hag : AgreeAt k s t)
    (g : Subscriber → Subscriber) :
    AgreeAt k { s with subs := updateSub s.subs j g }
      { t with subs := updateSub t.subs j g } := by
  refine ⟨hag.1, hag.2.1, ?_, ?_⟩
  · show (updateSub t.subs j g).map Prod.fst = (updateSub s.subs j g).map Prod.fst
    rw [updateSub_keys, updateSub_keys]; exact hag.2.2.1
  · show lookupSub (updateSub t.subs j g) k = lookupSub (updateSub s.subs j g) k
    by_cases hkj : k = j
    · subst hkj
      rw [lookupSub_updateSub_map, lookupSub_updateSub_map, hag.2.2.2]
    · rw [lookupSub_updateSub_ne t.subs j k g (fun he => hkj he.symm),
        lookupSub_updateSub_ne s.subs j k g (fun he => hkj he.symm)]
      exact hag.2.2.2

/-- One step from two states agreeing at `k`: the results still agree and `k`'s history entry is
the same. -/
theorem apply_agree_step {k : SubId} {s t u v : SubState} {l : Label} {h : History}
    (hag : AgreeAt k s t) (hs : apply s l = some u) (ht : apply t l = some v) :
    AgreeAt k u v ∧ afterLabel s u k h l = afterLabel t v k h l := by
  have hcore : ∀ (hagu : AgreeAt k u v), afterLabel s u k h l = afterLabel t v k h l := by
    intro hagu
    cases l with
    | op _ _ => rfl
    | register stream opts l₀ j e =>
      show (if j = k then [observedOf u k] else h) = (if j = k then [observedOf v k] else h)
      by_cases hjk : j = k
      · rw [if_pos hjk, if_pos hjk, observedOf_agreeAt hagu]
      · rw [if_neg hjk, if_neg hjk]
    | pull j =>
      show (if j = k then h ++ [(observedOf u k).drop (observedOf s k).length] else h)
          = (if j = k then h ++ [(observedOf v k).drop (observedOf t k).length] else h)
      by_cases hjk : j = k
      · rw [if_pos hjk, if_pos hjk, observedOf_agreeAt hagu, observedOf_agreeAt hag]
      · rw [if_neg hjk, if_neg hjk]
    | unsubscribe _ => rfl
  have hagu : AgreeAt k u v := by
    cases l with
    | op o e =>
      obtain ⟨v', hv', hagv⟩ := apply_agreeAt hag (fun i hi => by cases hi) (fun i hi => by cases hi) hs
      cases hv'.symm.trans ht
      exact hagv
    | register stream opts l₀ j e =>
      obtain ⟨v', hv', hagv⟩ := apply_agreeAt hag (fun i hi => by cases hi) (fun i hi => by cases hi) hs
      cases hv'.symm.trans ht
      exact hagv
    | pull j =>
      by_cases hjk : j = k
      · subst hjk
        obtain ⟨v', hv', hagv⟩ := apply_agreeAt hag (fun i hi => by cases hi; rfl)
          (fun i hi => by cases hi) hs
        cases hv'.symm.trans ht
        exact hagv
      · exact agreeAt_trans (agreeAt_trans (agreeAt_symm (applyPull_agreeAt hjk hs)) hag)
          (applyPull_agreeAt hjk ht)
    | unsubscribe j =>
      obtain ⟨sub, _, _, hu⟩ := applyUnsubscribe_ok_eq (show applyUnsubscribe s j = some u from hs)
      obtain ⟨sub', _, _, hv⟩ := applyUnsubscribe_ok_eq (show applyUnsubscribe t j = some v from ht)
      rw [hu, hv]
      exact agreeAt_update hag _
  exact ⟨hagu, hcore hagu⟩

/-- Two states agreeing at `k` give `k` the same history along any label list both of them run. -/
theorem abstractHistoryFrom_congr {k : SubId} : ∀ (ls : List Label) {s t u v : SubState}
    {h : History}, AgreeAt k s t → runLabels s ls = some u → runLabels t ls = some v →
    AgreeAt k u v ∧ abstractHistoryFrom k s h ls = abstractHistoryFrom k t h ls := by
  intro ls
  induction ls with
  | nil =>
    intro s t u v h hag hs ht
    cases hs; cases ht
    exact ⟨hag, rfl⟩
  | cons l rest ih =>
    intro s t u v h hag hs ht
    rw [runLabels_cons] at hs ht
    cases hap : apply s l with
    | none => rw [hap] at hs; cases hs
    | some s₁ =>
      cases hbp : apply t l with
      | none => rw [hbp] at ht; cases ht
      | some t₁ =>
        rw [hap] at hs
        rw [hbp] at ht
        obtain ⟨hag₁, hafter⟩ := apply_agree_step (h := h) hag hap hbp
        obtain ⟨hagu, hhist⟩ := ih (h := afterLabel s s₁ k h l) hag₁ hs ht
        refine ⟨hagu, ?_⟩
        rw [abstractHistoryFrom_cons, abstractHistoryFrom_cons, hap, hbp]
        show abstractHistoryFrom k s₁ (afterLabel s s₁ k h l) rest
            = abstractHistoryFrom k t₁ (afterLabel t t₁ k h l) rest
        rw [← hafter]
        exact hhist

/-! ## The queue under a pending failure -/

theorem fail_of_ne_opened (q : EffectQueue) (e : SubError) (h : q.status ≠ .opened) :
    q.fail e = q := by
  unfold EffectQueue.fail
  cases hs : q.status with
  | opened => exact absurd hs h
  | closing _ => rfl
  | done _ => rfl
  | shutDown => rfl

theorem fail_buffer (q : EffectQueue) (e : SubError) : (q.fail e).buffer = q.buffer := by
  unfold EffectQueue.fail
  cases q.status with
  | opened => by_cases hb : q.buffer.isEmpty <;> simp [hb]
  | closing _ => rfl
  | done _ => rfl
  | shutDown => rfl

theorem fail_status (q : EffectQueue) (e : SubError) :
    (q.fail e).status =
      if q.status = .opened then (if q.buffer.isEmpty then .done e else .closing e)
      else q.status := by
  unfold EffectQueue.fail
  cases hq : q.status with
  | opened => by_cases hb : q.buffer.isEmpty = true <;> simp [hb]
  | closing _ => simp [hq]
  | done _ => simp [hq]
  | shutDown => simp [hq]

theorem fail_ne_shutDown (q : EffectQueue) (e : SubError) (h : q.status ≠ .shutDown) :
    (q.fail e).status ≠ .shutDown := by
  unfold EffectQueue.fail
  cases hs : q.status with
  | opened => by_cases hb : q.buffer.isEmpty <;> simp [hb]
  | closing _ => rw [hs] at h ⊢; exact h
  | done _ => rw [hs] at h ⊢; exact h
  | shutDown => exact absurd hs h

theorem failOpt_closeStarted (e? : Option SubError) (r : RtSubscriber) :
    (failOpt e? r).closeStarted = r.closeStarted := by
  cases e? <;> rfl

theorem failOpt_chunks (e? : Option SubError) (r : RtSubscriber) :
    (failOpt e? r).chunks = r.chunks := by
  cases e? <;> rfl

theorem failOpt_lastEnqueued (e? : Option SubError) (r : RtSubscriber) :
    (failOpt e? r).lastEnqueued = r.lastEnqueued := by
  cases e? <;> rfl

theorem failOpt_ne_shutDown {e? : Option SubError} {r : RtSubscriber}
    (h : r.queue.status ≠ .shutDown) : (failOpt e? r).queue.status ≠ .shutDown := by
  cases e? with
  | none => exact h
  | some e => exact fail_ne_shutDown r.queue e h

theorem not_closed_failOpt {e? : Option SubError} {r : RtSubscriber}
    (hcs : r.closeStarted = false) (hsd : r.queue.status ≠ .shutDown) :
    ¬ Closed (failOpt e? r) := by
  rintro (h | h)
  · rw [failOpt_closeStarted] at h; rw [h] at hcs; exact Bool.noConfusion hcs
  · exact failOpt_ne_shutDown hsd h

theorem closed_failOpt_of_closeStarted {e? : Option SubError} {r : RtSubscriber}
    (hcs : r.closeStarted = true) : Closed (failOpt e? r) :=
  Or.inl (by rw [failOpt_closeStarted]; exact hcs)

theorem closed_failOpt_of_shutDown {e? : Option SubError} {r : RtSubscriber}
    (h : r.queue.status = .shutDown) : Closed (failOpt e? r) := by
  refine Or.inr ?_
  cases e? with
  | none => exact h
  | some e => show (r.queue.fail e).status = .shutDown; rw [fail_of_ne_opened _ _ (by rw [h]; intro hc; exact QueueStatus.noConfusion hc)]; exact h

/-! ## `corrSub` -/

theorem corrSub_of_erase {r : RtSubscriber} {a : Subscriber} (h : ¬ Closed r) (heq : a = r.erase) :
    corrSub r a := ⟨fun hc => absurd hc h, fun _ => heq⟩

theorem corrSub_of_closed {r : RtSubscriber} {a : Subscriber} (h : Closed r)
    (h₁ : a.status = .shutDown) (h₂ : a.registered = false) (h₃ : a.observed = r.chunks.flatten) :
    corrSub r a := ⟨fun _ => ⟨h₁, h₂, h₃⟩, fun hc => absurd h hc⟩

theorem corrSub_observed {r : RtSubscriber} {a : Subscriber} (h : corrSub r a) :
    a.observed = r.chunks.flatten := by
  by_cases hc : Closed r
  · exact (h.1 hc).2.2
  · rw [h.2 hc]; rfl

/-- The failure a `check` decided depends only on the fan-out and on `lastEnqueued`. -/
theorem pendingFail_congr (f : FanOut) (id : SubId) {r r' : RtSubscriber}
    (h : r'.lastEnqueued = r.lastEnqueued) : pendingFail f id r' = pendingFail f id r := by
  unfold pendingFail
  rw [h]

theorem pendingOf_eq (f : FanOut) (id : SubId) (r : RtSubscriber) :
    pendingOf f id r = failOpt (pendingFail f id r) r := rfl

theorem pendingFail_of_decided_none {f : FanOut} (h : f.decided = none) (id : SubId)
    (r : RtSubscriber) : pendingFail f id r = none := by
  unfold pendingFail
  rw [h]
  cases f.kind <;> rfl

theorem pendingOf_of_decided_none {f : FanOut} (h : f.decided = none) (id : SubId)
    (r : RtSubscriber) : pendingOf f id r = r := by
  rw [pendingOf_eq, pendingFail_of_decided_none h]
  rfl

/-! ## One returning take -/

/-- The three shapes of a `takeAll`/`wake` that returns something: a drain of an open queue, a
drain of a `closing` queue (which finishes it), and the stored exit of a finished one. -/
def TakeCase (q q' : EffectQueue) (c : List Observed) : Prop :=
  (q.status = .opened ∧ q.buffer ≠ [] ∧ q'.buffer = [] ∧ q'.status = .opened ∧
      c = q.buffer.map Observed.entry) ∨
  (∃ e₀, q.status = .closing e₀ ∧ q.buffer ≠ [] ∧ q'.buffer = [] ∧ q'.status = .done e₀ ∧
      c = q.buffer.map Observed.entry) ∨
  (∃ e₀, q.status = .done e₀ ∧ q'.buffer = [] ∧ q'.status = .shutDown ∧
      c = [Observed.failed e₀])

theorem status_ne_shutDown_of_opened {q : EffectQueue} (h : q.status = .opened) :
    q.status ≠ .shutDown := by rw [h]; intro hc; exact QueueStatus.noConfusion hc

theorem takeCase_fail {q q' : EffectQueue} {c : List Observed} (e : SubError)
    (h : TakeCase q q' c) : TakeCase (q.fail e) (q'.fail e) c := by
  have hfne : ∀ (p : EffectQueue), p.status = .opened → p.buffer ≠ [] →
      (p.fail e).status = .closing e ∧ (p.fail e).buffer = p.buffer := by
    intro p hs hne
    refine ⟨?_, fail_buffer p e⟩
    unfold EffectQueue.fail
    rw [hs]
    simp [List.isEmpty_eq_false_iff.mpr hne]
  have hfe : ∀ (p : EffectQueue), p.status = .opened → p.buffer = [] →
      (p.fail e).status = .done e ∧ (p.fail e).buffer = [] := by
    intro p hs hb
    refine ⟨?_, by rw [fail_buffer, hb]⟩
    unfold EffectQueue.fail
    rw [hs]
    simp [hb]
  rcases h with ⟨hs, hne, hb, hs2, hc⟩ | ⟨e0, hs, hne, hb, hs2, hc⟩ | ⟨e0, hs, hb, hs2, hc⟩
  · refine Or.inr (Or.inl ⟨e, (hfne q hs hne).1, ?_, (hfe q' hs2 hb).2, (hfe q' hs2 hb).1, ?_⟩)
    · rw [(hfne q hs hne).2]; exact hne
    · rw [(hfne q hs hne).2]; exact hc
  · have h1 : q.fail e = q := fail_of_ne_opened q e (by rw [hs]; intro hc2; exact QueueStatus.noConfusion hc2)
    have h2 : q'.fail e = q' := fail_of_ne_opened q' e (by rw [hs2]; intro hc2; exact QueueStatus.noConfusion hc2)
    rw [h1, h2]
    exact Or.inr (Or.inl ⟨e0, hs, hne, hb, hs2, hc⟩)
  · have h1 : q.fail e = q := fail_of_ne_opened q e (by rw [hs]; intro hc2; exact QueueStatus.noConfusion hc2)
    have h2 : q'.fail e = q' := fail_of_ne_opened q' e (by rw [hs2]; intro hc2; exact QueueStatus.noConfusion hc2)
    rw [h1, h2]
    exact Or.inr (Or.inr ⟨e0, hs, hb, hs2, hc⟩)

theorem erase_queue_congr (r : RtSubscriber) {q1 q2 : EffectQueue} (hb : q1.buffer = q2.buffer)
    (hs : q1.status = q2.status) :
    ({ r with queue := q1 } : RtSubscriber).erase
      = ({ r with queue := q2 } : RtSubscriber).erase := by
  unfold RtSubscriber.erase
  simp only [hb, hs]

theorem flatten_snoc (l : History) (c : List Observed) : (l ++ [c]).flatten = l.flatten ++ c := by
  induction l with
  | nil => simp
  | cons x rest ih => simp only [List.cons_append, List.flatten_cons, ih, List.append_assoc]

theorem pullStep_opened {a : Subscriber} (hs : a.status = .opened) (hne : a.pending ≠ []) :
    pullStep a =
      some { a with observed := a.observed ++ a.pending.map Observed.entry, pending := [] } := by
  unfold pullStep
  rw [hs]
  simp [List.isEmpty_eq_false_iff.mpr hne]

theorem pullStep_closing {a : Subscriber} {e : SubError} (hs : a.status = .closing e)
    (hne : a.pending ≠ []) :
    pullStep a =
      some { a with
               observed := a.observed ++ a.pending.map Observed.entry, pending := [],
               status := .done e } := by
  unfold pullStep
  rw [hs]
  simp [List.isEmpty_eq_false_iff.mpr hne]

theorem pullStep_done {a : Subscriber} {e : SubError} (hs : a.status = .done e) :
    pullStep a = some { a with observed := a.observed ++ [Observed.failed e],
                               status := .shutDown } := by
  unfold pullStep
  rw [hs]

/-- A returning take is the abstract `pullStep`. -/
theorem take_corr_core {R : RtSubscriber} {a : Subscriber} {q2 : EffectQueue} {c : List Observed}
    (hcs : R.closeStarted = false)
    (hreg : R.registered = true → R.queue.status = .opened)
    (hae : a = R.erase)
    (hcase : TakeCase R.queue q2 c) :
    ∃ a', pullStep a = some a' ∧ a'.observed = a.observed ++ c ∧
      corrSub { R with queue := q2, chunks := R.chunks ++ [c] } a' := by
  have hst : a.status = R.queue.status := by rw [hae]; rfl
  have hpd : a.pending = R.queue.buffer := by rw [hae]; rfl
  have hclosed : ∀ st : QueueStatus, q2.status = st → st ≠ .shutDown →
      ¬ Closed ({ R with queue := q2, chunks := R.chunks ++ [c] } : RtSubscriber) := by
    intro st hstq hne hcl
    rcases hcl with hcl | hcl
    · rw [show ({ R with queue := q2, chunks := R.chunks ++ [c] } : RtSubscriber).closeStarted
          = R.closeStarted from rfl, hcs] at hcl
      exact Bool.noConfusion hcl
    · rw [show ({ R with queue := q2, chunks := R.chunks ++ [c] } : RtSubscriber).queue.status
          = q2.status from rfl, hstq] at hcl
      exact hne hcl
  rcases hcase with ⟨hs, hne, hb, hs2, hc⟩ | ⟨e0, hs, hne, hb, hs2, hc⟩ | ⟨e0, hs, hb, hs2, hc⟩
  · refine ⟨_, pullStep_opened (a := a) (by rw [hst, hs]) (by rw [hpd]; exact hne), ?_, ?_⟩
    · show a.observed ++ a.pending.map Observed.entry = a.observed ++ c
      rw [hpd, hc]
    · refine corrSub_of_erase (hclosed .opened hs2 (fun hcc => QueueStatus.noConfusion hcc)) ?_
      subst hae
      show _ = ({ R with queue := q2, chunks := R.chunks ++ [c] } : RtSubscriber).erase
      simp only [RtSubscriber.erase, hb, hs2, hs, hc, flatten_snoc]
  · refine ⟨_, pullStep_closing (a := a) (by rw [hst, hs]) (by rw [hpd]; exact hne), ?_, ?_⟩
    · show a.observed ++ a.pending.map Observed.entry = a.observed ++ c
      rw [hpd, hc]
    · refine corrSub_of_erase (hclosed (.done e0) hs2 (fun hcc => QueueStatus.noConfusion hcc)) ?_
      subst hae
      show _ = ({ R with queue := q2, chunks := R.chunks ++ [c] } : RtSubscriber).erase
      simp only [RtSubscriber.erase, hb, hs2, hc, flatten_snoc]
  · have hnr : R.registered = false := by
      cases hb2 : R.registered with
      | false => rfl
      | true =>
        rw [hreg hb2] at hs
        exact absurd hs (fun hcc => QueueStatus.noConfusion hcc)
    refine ⟨_, pullStep_done (a := a) (e := e0) (by rw [hst, hs]), ?_, ?_⟩
    · show a.observed ++ [Observed.failed e0] = a.observed ++ c
      rw [hc]
    · refine corrSub_of_closed (Or.inr hs2) rfl ?_ ?_
      · show a.registered = false
        rw [hae]
        exact hnr
      · show a.observed ++ [Observed.failed e0] = (R.chunks ++ [c]).flatten
        rw [flatten_snoc, hc, hae]
        rfl

theorem take_corr {r : RtSubscriber} {a : Subscriber} {e? : Option SubError}
    {q' : EffectQueue} {c : List Observed}
    (hro : r.registered = true → r.queue.status = .opened)
    (hcs : r.closeStarted = false)
    (hcorr : corrSub (failOpt e? r) a)
    (hcase : TakeCase r.queue q' c) :
    ∃ a', pullStep a = some a' ∧ a'.observed = a.observed ++ c ∧
      corrSub (failOpt e? { r with queue := q', chunks := r.chunks ++ [c] }) a' := by
  have hsd : r.queue.status ≠ .shutDown := by
    rcases hcase with ⟨h, _⟩ | ⟨e0, h, _⟩ | ⟨e0, h, _⟩ <;> rw [h] <;> intro hc <;>
      exact QueueStatus.noConfusion hc
  have hae : a = (failOpt e? r).erase := hcorr.2 (not_closed_failOpt hcs hsd)
  cases e? with
  | none => exact take_corr_core hcs hro hae hcase
  | some e =>
    have hR : (rtFail e r).closeStarted = false := hcs
    have hRreg : (rtFail e r).registered = true → (rtFail e r).queue.status = .opened := by
      intro hb2
      exact absurd hb2 (fun hcc => Bool.noConfusion hcc)
    obtain ⟨a', h1, h2, h3⟩ := take_corr_core (R := rtFail e r) hR hRreg hae (takeCase_fail e hcase)
    exact ⟨a', h1, h2, h3⟩

/-- A parked pull changes nothing the abstract side can see. -/
theorem park_corr {r : RtSubscriber} {a : Subscriber} {e? : Option SubError} {q' : EffectQueue}
    (hcs : r.closeStarted = false) (hsd : r.queue.status ≠ .shutDown)
    (hcorr : corrSub (failOpt e? r) a)
    (hb : q'.buffer = r.queue.buffer) (hst : q'.status = r.queue.status) :
    corrSub (failOpt e? { r with queue := q' }) a := by
  have hsd2 : q'.status ≠ .shutDown := by rw [hst]; exact hsd
  refine corrSub_of_erase (not_closed_failOpt hcs hsd2) ?_
  rw [hcorr.2 (not_closed_failOpt hcs hsd)]
  cases e? with
  | none => exact erase_queue_congr r hb.symm hst.symm
  | some e =>
    show ({ r with registered := false, queue := r.queue.fail e } : RtSubscriber).erase
        = ({ r with registered := false, queue := q'.fail e } : RtSubscriber).erase
    refine erase_queue_congr ({ r with registered := false }) ?_ ?_
    · rw [fail_buffer, fail_buffer, hb]
    · rw [fail_status, fail_status, hst, hb]

/-! ## The two halves of a scope closure -/

theorem closeA_corr {r : RtSubscriber} {a : Subscriber} {e? : Option SubError}
    (hcs : r.closeStarted = false) (hsd : r.queue.status ≠ .shutDown)
    (hcorr : corrSub (failOpt e? r) a) :
    a.status ≠ .shutDown ∧
      corrSub (failOpt e? { r with registered := false, closeStarted := true })
        { a with registered := false, pending := [], status := .shutDown } := by
  have hae : a = (failOpt e? r).erase := hcorr.2 (not_closed_failOpt hcs hsd)
  refine ⟨?_, corrSub_of_closed (closed_failOpt_of_closeStarted rfl) rfl rfl ?_⟩
  · rw [hae]
    show (failOpt e? r).queue.status ≠ .shutDown
    exact failOpt_ne_shutDown hsd
  · show a.observed = _
    rw [corrSub_observed hcorr, failOpt_chunks, failOpt_chunks]

theorem closeB_corr {r : RtSubscriber} {a : Subscriber} {e? : Option SubError}
    (hcs : r.closeStarted = true) (hcorr : corrSub (failOpt e? r) a) :
    corrSub (failOpt e? { r with queue := r.queue.shutdown, closeStarted := false }) a := by
  obtain ⟨h1, h2, h3⟩ := hcorr.1 (closed_failOpt_of_closeStarted hcs)
  refine corrSub_of_closed (closed_failOpt_of_shutDown rfl) h1 h2 ?_
  rw [h3, failOpt_chunks, failOpt_chunks]

/-! ## Reading the relation -/

theorem runLabels_agreeExcept {i : SubId} : ∀ (ls : List Label) {s t s' : SubState},
    AgreeExcept i s t → (∀ l ∈ ls, ∀ j, (l = .pull j ∨ l = .unsubscribe j) → j ≠ i) →
    runLabels s ls = some s' → ∃ t', runLabels t ls = some t' ∧ AgreeExcept i s' t' := by
  intro ls
  induction ls with
  | nil =>
    intro s t s' hag _ hrun
    cases hrun
    exact ⟨t, rfl, hag⟩
  | cons l rest ih =>
    intro s t s' hag hls hrun
    rw [runLabels_cons] at hrun
    cases hap : apply s l with
    | none => rw [hap] at hrun; cases hrun
    | some u =>
      rw [hap] at hrun
      obtain ⟨v, hv, hagv⟩ := apply_agreeExcept hag (fun j hj => hls l (List.Mem.head _) j hj) hap
      obtain ⟨t', ht', hagt⟩ := ih hagv (fun m hm => hls m (List.Mem.tail _ hm)) hrun
      refine ⟨t', ?_, hagt⟩
      rw [runLabels_cons, hv]
      exact ht'

theorem labelSerial_append : ∀ (l₁ l₂ : List Label),
    labelSerial (l₁ ++ l₂) = labelSerial l₁ ++ labelSerial l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rfl
  | cons l rest ih =>
    intro l₂
    cases l with
    | op o e => show _ :: labelSerial (rest ++ l₂) = _ :: (labelSerial rest ++ labelSerial l₂)
                rw [ih]
    | register stream opts l₀ id e =>
      show _ :: labelSerial (rest ++ l₂) = _ :: (labelSerial rest ++ labelSerial l₂)
      rw [ih]
    | pull id => exact ih l₂
    | unsubscribe id => exact ih l₂

theorem owedOp_ne_pull (k : FanKind) (j : SubId) : owedOp k ≠ .pull j := by
  cases k <;> intro h <;> exact Label.noConfusion h

theorem owedOp_ne_unsubscribe (k : FanKind) (j : SubId) : owedOp k ≠ .unsubscribe j := by
  cases k <;> intro h <;> exact Label.noConfusion h

theorem abstractHistory_append (id : SubId) (l₁ l₂ : List Label) {t : SubState} {h₁ : History}
    (hrun : runLabels initialSub l₁ = some t) (hh : abstractHistory l₁ id = some h₁) :
    abstractHistory (l₁ ++ l₂) id = abstractHistoryFrom id t h₁ l₂ :=
  abstractHistoryFrom_append id l₁ l₂ hrun hh

theorem abstractHistory_isSome (id : SubId) (ls : List Label) {t : SubState}
    (hrun : runLabels initialSub ls = some t) : ∃ h, abstractHistory ls id = some h :=
  abstractHistoryFrom_isSome id ls [] hrun

theorem lookupRt_update_self {s : RtState} {i : SubId} {r r' : RtSubscriber}
    (h : lookupRt s.subs i = some r) :
    lookupRt (updateRt s.subs i (fun _ => r')) i = some r' := by
  rw [lookupRt_updateRt_self, h]
  rfl

theorem rtHistory_eq {s : RtState} {id : SubId} {r : RtSubscriber}
    (h : lookupRt s.subs id = some r) : rtHistory s id = r.chunks := by
  unfold rtHistory
  rw [h]

theorem isTargetOf_congr {a a' : Subscriber} (hs : a'.stream = a.stream)
    (hr : a'.registered = a.registered) (hf : a'.filters = a.filters) (k : FanKind) :
    isTargetOf k a' = isTargetOf k a := by
  cases k <;> simp only [isTargetOf, hs, hr, hf]

theorem isTargetOf_of_unregistered {a : Subscriber} (h : a.registered = false) (k : FanKind) :
    isTargetOf k a = false := by
  cases k <;> simp [isTargetOf, h]

/-- What a consumer label can do to an abstract subscriber, as far as the fan-out's targeting is
concerned: it keeps the `deliverOne`/`endOne` guard (and was not enabled on a shut-down
subscriber), or it shuts the subscriber down. -/
def TargetStable (a a' : Subscriber) : Prop :=
  (a.status ≠ .shutDown ∧ a'.stream = a.stream ∧ a'.registered = a.registered ∧
      a'.filters = a.filters) ∨ (a'.status = .shutDown ∧ a'.registered = false)

/-- The witness of `A4Inclusion` has no `unsubscribe` label — the P5c export. -/
def NoUnsub (ls : List Label) : Prop := ∀ l ∈ ls, ∀ i, l ≠ .unsubscribe i

theorem noUnsub_append {l₁ l₂ : List Label} (h₁ : NoUnsub l₁) (h₂ : NoUnsub l₂) :
    NoUnsub (l₁ ++ l₂) := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · exact h₁ l h
  · exact h₂ l h

theorem noUnsub_of_append {l₁ l₂ : List Label} (h : NoUnsub (l₁ ++ l₂)) :
    NoUnsub l₁ ∧ NoUnsub l₂ :=
  ⟨fun l hl => h l (List.mem_append.mpr (Or.inl hl)),
   fun l hl => h l (List.mem_append.mpr (Or.inr hl))⟩

theorem noUnsub_single {l : Label} (h : ∀ j, l ≠ .unsubscribe j) : NoUnsub [l] := by
  intro m hm
  cases List.mem_singleton.mp hm
  exact h

theorem agreeAt_of_agreeExcept {i id : SubId} {u u' : SubState} (h : AgreeExcept i u u')
    (hne : id ≠ i) : AgreeAt id u u' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 id hne⟩

theorem applyUnsubscribe_agreeAt {k i : SubId} {s t : SubState} (hik : i ≠ k)
    (h : apply s (.unsubscribe i) = some t) : AgreeAt k s t := by
  obtain ⟨hl, hc, hn, hkeys⟩ := applyUnsubscribe_other hik h
  exact ⟨hc, hn, hkeys, hl⟩

/-- A subscriber whose point has not passed has no pending failure. -/
theorem pendingFail_of_not_passed {f : FanOut} {id : SubId} (h : pointPassed f id = false)
    (r : RtSubscriber) : pendingFail f id r = none := by
  unfold pendingFail
  cases hk : f.kind with
  | delete _ => rfl
  | publish stream m el =>
    cases hd : f.decided with
    | none => rfl
    | some p =>
      obtain ⟨j, b⟩ := p
      cases b with
      | false => simp
      | true =>
        by_cases hji : j = id
        · exfalso
          subst hji
          unfold pointPassed at h
          rw [hd] at h
          simp at h
        · simp [hji]

theorem pendingOf_of_not_passed {f : FanOut} {id : SubId} (h : pointPassed f id = false)
    (r : RtSubscriber) : pendingOf f id r = r := by
  rw [pendingOf_eq, pendingFail_of_not_passed h]
  rfl

/-! ## The plumbing shared by `pull`, `wake`, `closeA`, and `closeB` -/

/-- One consumer step of subscriber `i` matched by one abstract label. The abstract label goes
into `labels` when `i`'s linearization point has not passed (or no fan-out is in flight) and into
the owed suffix when it has. -/
theorem rel_consumer {s s' : RtState} {i : SubId} {r r' : RtSubscriber} {lab : Label}
    {ch : History} {labels owed : List Label}
    (hlk : lookupRt s.subs i = some r)
    (hupd : s' = { s with subs := updateRt s.subs i (fun _ => r') })
    (hlab : lab = .pull i ∨ lab = .unsubscribe i)
    (hchunks : r'.chunks = r.chunks ++ ch)
    (hpend : ∀ f, pendingFail f i r' = pendingFail f i r)
    (habs : ∀ (e? : Option SubError) (u : SubState) (a : Subscriber),
        lookupSub u.subs i = some a → corrSub (failOpt e? r) a →
        ∃ u' a', apply u lab = some u' ∧ AgreeExcept i u u' ∧ lookupSub u'.subs i = some a' ∧
          corrSub (failOpt e? r') a' ∧ a'.observed = a.observed ++ ch.flatten ∧
          TargetStable a a')
    (hafter : ∀ (u u' : SubState) (a a' : Subscriber) (h : History),
        lookupSub u.subs i = some a → lookupSub u'.subs i = some a' →
        a'.observed = a.observed ++ ch.flatten → afterLabel u u' i h lab = h ++ ch)
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    ∃ labels' owed', Rel s' labels' owed' ∧ RelHist s' labels' owed' ∧
      labelSerial labels' ++ labelSerial owed' = labelSerial labels ++ labelSerial owed ∧
      (NoUnsub labels → NoUnsub owed → (∀ j, lab ≠ .unsubscribe j) →
        NoUnsub labels' ∧ NoUnsub owed') := by
  obtain ⟨sA, hrun, hnext, hkeys, hquiet, hflight⟩ := hrel
  have hlk' : lookupRt s'.subs i = some r' := by rw [hupd]; exact lookupRt_update_self hlk
  have hlkne : ∀ id, id ≠ i → lookupRt s'.subs id = lookupRt s.subs id := by
    intro id hid
    rw [hupd]
    exact lookupRt_updateRt_ne s.subs id i (fun _ => r') hid
  have hkeys' : s'.subs.map Prod.fst = s.subs.map Prod.fst := by
    rw [hupd]; exact updateRt_keys s.subs i (fun _ => r')
  have hnext' : s'.nextId = s.nextId := by rw [hupd]
  have hcore' : s'.core = s.core := by rw [hupd]
  have hfan' : s'.fanOut = s.fanOut := by rw [hupd]
  have hhistNe : ∀ id, id ≠ i → rtHistory s' id = rtHistory s id := by
    intro id hid
    unfold rtHistory
    rw [hlkne id hid]
  have hhistSelf : rtHistory s' i = rtHistory s i ++ ch := by
    rw [rtHistory_eq hlk', rtHistory_eq hlk, hchunks]
  have hlabSerial : labelSerial [lab] = [] := by
    rcases hlab with h | h <;> rw [h] <;> rfl
  have hafterNe : ∀ (u u' : SubState) (h : History) (id : SubId), id ≠ i →
      afterLabel u u' id h lab = h := by
    intro u u' h id hid
    rcases hlab with hl | hl <;> subst hl
    · show (if i = id then _ else h) = h
      exact if_neg (fun he => hid he.symm)
    · rfl
  have hagreeAt : ∀ (u u' : SubState) (id : SubId), id ≠ i → apply u lab = some u' →
      AgreeAt id u u' := by
    intro u u' id hid hap
    rcases hlab with hl | hl <;> subst hl
    · exact applyPull_agreeAt (fun he => hid he.symm) hap
    · exact applyUnsubscribe_agreeAt (fun he => hid he.symm) hap
  have hisSome : ∀ id, (lookupRt s'.subs id).isSome = true → (lookupRt s.subs id).isSome = true := by
    intro id hs
    by_cases hid : id = i
    · subst hid; rw [hlk]; rfl
    · rw [← hlkne id hid]; exact hs
  cases hfan : s.fanOut with
  | none =>
    obtain ⟨howed, hcoreA, hcorr⟩ := hquiet hfan
    subst howed
    obtain ⟨a, hlka, hca⟩ := hcorr i r hlk
    obtain ⟨sA', a', hap, hag, hlka', hca', hobs', -⟩ := habs none sA a hlka hca
    refine ⟨labels ++ [lab], [], ⟨sA', runLabels_snoc hrun hap, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hag.2.1, hnext, hnext']
    · rw [hag.2.2.1, hkeys, hkeys']
    · intro _
      refine ⟨rfl, ?_, ?_⟩
      · rw [hag.1, hcoreA, hcore']
      · intro id r₀ hlkr
        by_cases hid : id = i
        · subst hid
          rw [hlk'] at hlkr
          cases hlkr
          exact ⟨a', hlka', hca'⟩
        · rw [hlkne id hid] at hlkr
          obtain ⟨b, hlkb, hcb⟩ := hcorr id r₀ hlkr
          exact ⟨b, (hag.2.2.2 id hid).trans hlkb, hcb⟩
    · intro g hg
      rw [hfan', hfan] at hg
      cases hg
    · intro id hsome
      refine ⟨fun _ => ?_, fun g hg => ?_⟩
      · have hbase : abstractHistory labels id = some (rtHistory s id) :=
          (hhist id (hisSome id hsome)).1 hfan
        rw [abstractHistory_append id labels [lab] hrun hbase]
        show (match apply sA lab with
              | some u => abstractHistoryFrom id u (afterLabel sA u id (rtHistory s id) lab) []
              | none => none) = _
        rw [hap]
        show some (afterLabel sA sA' id (rtHistory s id) lab) = _
        by_cases hid : id = i
        · subst hid
          rw [hafter sA sA' a a' (rtHistory s id) hlka hlka' hobs', ← hhistSelf]
        · rw [hafterNe sA sA' (rtHistory s id) id hid, hhistNe id hid]
      · rw [hfan', hfan] at hg
        cases hg
    · rw [labelSerial_append, hlabSerial, List.append_nil]
    · intro hnl _ hlu
      exact ⟨noUnsub_append hnl (noUnsub_single hlu), fun l hl => by cases hl⟩
  | some f =>
    obtain ⟨hfresh, hpre, hrcore, hcorrPre, owedRest, sPost, howed, howedOk, hrunPost, hcorrPost⟩ :=
      hflight f hfan
    have howedNe : ∀ l ∈ owed, ∀ j, (l = .pull j ∨ l = .unsubscribe j) → pointPassed f j = true := by
      intro l hl j hj
      rw [howed] at hl
      rcases List.mem_cons.mp hl with he | hm
      · exfalso
        subst he
        rcases hj with hj | hj
        · exact owedOp_ne_pull f.kind j hj
        · exact owedOp_ne_unsubscribe f.kind j hj
      · obtain ⟨k, hk, hpk⟩ := howedOk l hm
        rcases hk with hk | hk <;> subst hk <;> rcases hj with hj | hj <;>
          first
            | (cases hj; exact hpk)
            | exact Label.noConfusion hj
    have hgf : ∀ g, s'.fanOut = some g → g = f := by
      intro g hg
      rw [hfan', hfan] at hg
      exact (Option.some.inj hg).symm
    by_cases hpp : pointPassed f i = true
    · obtain ⟨aP, hlkaP, hcaP⟩ := hcorrPost i r hlk hpp
      obtain ⟨sPost', a', hap, hag, hlka', hca', hobs', -⟩ :=
        habs (pendingFail f i r) sPost aP hlkaP hcaP
      have hrunAll : runLabels initialSub (labels ++ owed) = some sPost :=
        (runLabels_append labels owed hrun).trans hrunPost
      refine ⟨labels, owed ++ [lab], ⟨sA, hrun, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [hnext, hnext']
      · rw [hkeys, hkeys']
      · intro hq
        rw [hfan', hfan] at hq
        cases hq
      · intro g hg
        rw [hgf g hg]
        refine ⟨hfresh, hpre, ?_, ?_, owedRest ++ [lab], sPost', ?_, ?_, ?_, ?_⟩
        · exact ⟨fun stream m el hk => by rw [hcore']; exact hrcore.1 stream m el hk,
            fun name hk => by rw [hcore']; exact hrcore.2 name hk⟩
        · intro id r₀ hlkr hnpid
          by_cases hid : id = i
          · subst hid
            rw [hpp] at hnpid
            exact Bool.noConfusion hnpid
          · rw [hlkne id hid] at hlkr
            exact hcorrPre id r₀ hlkr hnpid
        · rw [howed]; rfl
        · intro l hl
          rcases List.mem_append.mp hl with hm | hm
          · exact howedOk l hm
          · cases List.mem_singleton.mp hm
            rcases hlab with hl' | hl'
            · exact ⟨i, Or.inl hl', hpp⟩
            · exact ⟨i, Or.inr hl', hpp⟩
        · exact runLabels_snoc hrunPost hap
        · intro id r₀ hlkr hp
          by_cases hid : id = i
          · subst hid
            rw [hlk'] at hlkr
            cases hlkr
            refine ⟨a', hlka', ?_⟩
            rw [pendingOf_eq, hpend f]
            exact hca'
          · rw [hlkne id hid] at hlkr
            obtain ⟨b, hlkb, hcb⟩ := hcorrPost id r₀ hlkr hp
            exact ⟨b, (hag.2.2.2 id hid).trans hlkb, hcb⟩
      · intro id hsome
        obtain ⟨-, hf⟩ := hhist id (hisSome id hsome)
        obtain ⟨hpass, hnpass⟩ := hf f hfan
        refine ⟨fun hq => ?_, fun g hg => ?_⟩
        · rw [hfan', hfan] at hq
          cases hq
        · rw [hgf g hg]
          refine ⟨fun hp => ?_, fun hnpid => ?_⟩
          · rw [← List.append_assoc,
              abstractHistory_append id (labels ++ owed) [lab] hrunAll (hpass hp)]
            show (match apply sPost lab with
                  | some u => abstractHistoryFrom id u
                      (afterLabel sPost u id (rtHistory s id) lab) []
                  | none => none) = _
            rw [hap]
            show some (afterLabel sPost sPost' id (rtHistory s id) lab) = _
            by_cases hid : id = i
            · subst hid
              rw [hafter sPost sPost' aP a' (rtHistory s id) hlkaP hlka' hobs', ← hhistSelf]
            · rw [hafterNe sPost sPost' (rtHistory s id) id hid, hhistNe id hid]
          · have hid : id ≠ i := by
              intro he
              subst he
              rw [hpp] at hnpid
              exact Bool.noConfusion hnpid
            rw [hhistNe id hid]
            exact hnpass hnpid
      · rw [labelSerial_append, hlabSerial, List.append_nil]
      · intro hnl hno hlu
        exact ⟨hnl, noUnsub_append hno (noUnsub_single hlu)⟩
    · have hnp : pointPassed f i = false := by
        cases hb : pointPassed f i with
        | false => rfl
        | true => exact absurd hb hpp
      obtain ⟨a, hlka, hca⟩ := hcorrPre i r hlk hnp
      obtain ⟨sA', a', hap, hag, hlka', hca', hobs', htgt⟩ := habs none sA a hlka hca
      obtain ⟨sPost', hrunPost', hagPost⟩ :=
        runLabels_agreeExcept owed hag
          (fun l hl j hj he => by
            subst he
            rw [howedNe l hl j hj] at hnp
            exact Bool.noConfusion hnp)
          hrunPost
      refine ⟨labels ++ [lab], owed, ⟨sA', runLabels_snoc hrun hap, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [hag.2.1, hnext, hnext']
      · rw [hag.2.2.1, hkeys, hkeys']
      · intro hq
        rw [hfan', hfan] at hq
        cases hq
      · intro g hg
        rw [hgf g hg]
        refine ⟨hfresh, ?_, ?_, ?_, owedRest, sPost', howed, howedOk, hrunPost', ?_⟩
        · intro id b hlkb hnpb
          by_cases hid : id = i
          · subst hid
            rw [hlka'] at hlkb
            cases hlkb
            obtain ⟨hs, hpre₂⟩ := hpre id a hlka hnp
            rcases htgt with ⟨hne, hst, hrg, hfl⟩ | ⟨hsd, hrg⟩
            · refine ⟨?_, ?_⟩
              · rcases hs with hsc | hst₀
                · exact Or.inl hsc
                · exact Or.inr (by rw [isTargetOf_congr hst hrg hfl]; exact hst₀)
              · intro hsch
                rcases hpre₂ hsch with h | h
                · exact absurd h hne
                · exact Or.inr (by rw [isTargetOf_congr hst hrg hfl]; exact h)
            · exact ⟨Or.inr (isTargetOf_of_unregistered hrg _), fun _ => Or.inl hsd⟩
          · rw [hag.2.2.2 id hid] at hlkb
            exact hpre id b hlkb hnpb
        · exact ⟨fun stream m el hk => by rw [hcore', hag.1]; exact hrcore.1 stream m el hk,
            fun name hk => by rw [hcore', hag.1]; exact hrcore.2 name hk⟩
        · intro id r₀ hlkr hnpid
          by_cases hid : id = i
          · subst hid
            rw [hlk'] at hlkr
            cases hlkr
            exact ⟨a', hlka', hca'⟩
          · rw [hlkne id hid] at hlkr
            obtain ⟨b, hlkb, hcb⟩ := hcorrPre id r₀ hlkr hnpid
            exact ⟨b, (hag.2.2.2 id hid).trans hlkb, hcb⟩
        · intro id r₀ hlkr hp
          have hid : id ≠ i := by
            intro he
            subst he
            rw [hnp] at hp
            exact Bool.noConfusion hp
          rw [hlkne id hid] at hlkr
          obtain ⟨b, hlkb, hcb⟩ := hcorrPost id r₀ hlkr hp
          exact ⟨b, (hagPost.2.2.2 id hid).trans hlkb, hcb⟩
      · intro id hsome
        obtain ⟨-, hf⟩ := hhist id (hisSome id hsome)
        obtain ⟨hpass, hnpass⟩ := hf f hfan
        refine ⟨fun hq => ?_, fun g hg => ?_⟩
        · rw [hfan', hfan] at hq
          cases hq
        · rw [hgf g hg]
          refine ⟨fun hp => ?_, fun hnpid => ?_⟩
          · have hid : id ≠ i := by
              intro he
              subst he
              rw [hnp] at hp
              exact Bool.noConfusion hp
            obtain ⟨h₀, hh₀⟩ := abstractHistory_isSome id labels hrun
            have e₁ : abstractHistory (labels ++ owed) id = abstractHistoryFrom id sA h₀ owed :=
              abstractHistory_append id labels owed hrun hh₀
            have e₂ : abstractHistory (labels ++ [lab]) id = some h₀ := by
              rw [abstractHistory_append id labels [lab] hrun hh₀]
              show (match apply sA lab with
                    | some u => abstractHistoryFrom id u (afterLabel sA u id h₀ lab) []
                    | none => none) = _
              rw [hap]
              show some (afterLabel sA sA' id h₀ lab) = some h₀
              rw [hafterNe sA sA' h₀ id hid]
            rw [abstractHistory_append id (labels ++ [lab]) owed (runLabels_snoc hrun hap) e₂,
              ← (abstractHistoryFrom_congr owed (h := h₀) (hagreeAt sA sA' id hid hap)
                  hrunPost hrunPost').2, ← e₁, hhistNe id hid]
            exact hpass hp
          · rw [abstractHistory_append id labels [lab] hrun (hnpass hnpid)]
            show (match apply sA lab with
                  | some u => abstractHistoryFrom id u
                      (afterLabel sA u id (rtHistory s id) lab) []
                  | none => none) = _
            rw [hap]
            show some (afterLabel sA sA' id (rtHistory s id) lab) = _
            by_cases hid : id = i
            · subst hid
              rw [hafter sA sA' a a' (rtHistory s id) hlka hlka' hobs', ← hhistSelf]
            · rw [hafterNe sA sA' (rtHistory s id) id hid, hhistNe id hid]
      · rw [labelSerial_append, hlabSerial, List.append_nil]
      · intro hnl hno hlu
        exact ⟨noUnsub_append hnl (noUnsub_single hlu), hno⟩

/-! ## One runtime step -/

/-- What one runtime step must re-establish. -/
def RelStep (s' : RtState) (labels owed : List Label) (serial : List Label) (l : RtLabel) : Prop :=
  ∃ labels' owed', Rel s' labels' owed' ∧ RelHist s' labels' owed' ∧
    labelSerial labels' ++ labelSerial owed' = labelSerial labels ++ labelSerial owed ++ serial ∧
    ((∀ j, l ≠ .closeA j) → NoUnsub labels → NoUnsub owed → NoUnsub labels' ∧ NoUnsub owed')

theorem rtSubInv_of_lookup {s : RtState} {id : SubId} {r : RtSubscriber} (hinv : RtInv s)
    (h : lookupRt s.subs id = some r) : RtSubInv s r :=
  hinv.subs (id, r) (mem_of_lookupRt s.subs id r h)

/-- A runtime step that changes one subscriber and is matched by no abstract label. -/
theorem rel_silent {s s' : RtState} {i : SubId} {r r' : RtSubscriber} {labels owed : List Label}
    (hlk : lookupRt s.subs i = some r)
    (hupd : s' = { s with subs := updateRt s.subs i (fun _ => r') })
    (hchunks : r'.chunks = r.chunks)
    (hpend : ∀ f, pendingFail f i r' = pendingFail f i r)
    (hcorr : ∀ (e? : Option SubError) (a : Subscriber), corrSub (failOpt e? r) a →
        corrSub (failOpt e? r') a)
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    Rel s' labels owed ∧ RelHist s' labels owed := by
  obtain ⟨sA, hrun, hnext, hkeys, hquiet, hflight⟩ := hrel
  have hlk' : lookupRt s'.subs i = some r' := by rw [hupd]; exact lookupRt_update_self hlk
  have hlkne : ∀ id, id ≠ i → lookupRt s'.subs id = lookupRt s.subs id := by
    intro id hid
    rw [hupd]
    exact lookupRt_updateRt_ne s.subs id i (fun _ => r') hid
  have hkeys' : s'.subs.map Prod.fst = s.subs.map Prod.fst := by
    rw [hupd]; exact updateRt_keys s.subs i (fun _ => r')
  have hnext' : s'.nextId = s.nextId := by rw [hupd]
  have hcore' : s'.core = s.core := by rw [hupd]
  have hfan' : s'.fanOut = s.fanOut := by rw [hupd]
  have hhistEq : ∀ id, rtHistory s' id = rtHistory s id := by
    intro id
    by_cases hid : id = i
    · subst hid
      rw [rtHistory_eq hlk', rtHistory_eq hlk, hchunks]
    · unfold rtHistory
      rw [hlkne id hid]
  have hisSome : ∀ id, (lookupRt s'.subs id).isSome = true →
      (lookupRt s.subs id).isSome = true := by
    intro id hs
    by_cases hid : id = i
    · subst hid; rw [hlk]; rfl
    · rw [← hlkne id hid]; exact hs
  constructor
  · refine ⟨sA, hrun, by rw [hnext, hnext'], by rw [hkeys, hkeys'], ?_, ?_⟩
    · intro hq
      rw [hfan'] at hq
      obtain ⟨ho, hc, hca⟩ := hquiet hq
      refine ⟨ho, by rw [hc, hcore'], ?_⟩
      intro id r₀ hlkr
      by_cases hid : id = i
      · subst hid
        rw [hlk'] at hlkr
        cases hlkr
        obtain ⟨a, hlka, hcorra⟩ := hca id r hlk
        exact ⟨a, hlka, hcorr none a hcorra⟩
      · rw [hlkne id hid] at hlkr
        exact hca id r₀ hlkr
    · intro f hf
      rw [hfan'] at hf
      obtain ⟨hfresh, hpre, hrcore, hcorrPre, owedRest, sPost, howed, howedOk, hrunPost,
        hcorrPost⟩ := hflight f hf
      refine ⟨hfresh, hpre, ?_, ?_, owedRest, sPost, howed, howedOk, hrunPost, ?_⟩
      · exact ⟨fun stream m el hk => by rw [hcore']; exact hrcore.1 stream m el hk,
          fun name hk => by rw [hcore']; exact hrcore.2 name hk⟩
      · intro id r₀ hlkr hnp
        by_cases hid : id = i
        · subst hid
          rw [hlk'] at hlkr
          cases hlkr
          obtain ⟨a, hlka, hcorra⟩ := hcorrPre id r hlk hnp
          exact ⟨a, hlka, hcorr none a hcorra⟩
        · rw [hlkne id hid] at hlkr
          exact hcorrPre id r₀ hlkr hnp
      · intro id r₀ hlkr hp
        by_cases hid : id = i
        · subst hid
          rw [hlk'] at hlkr
          cases hlkr
          obtain ⟨a, hlka, hcorra⟩ := hcorrPost id r hlk hp
          refine ⟨a, hlka, ?_⟩
          rw [pendingOf_eq] at hcorra ⊢
          rw [hpend f]
          exact hcorr (pendingFail f id r) a hcorra
        · rw [hlkne id hid] at hlkr
          exact hcorrPost id r₀ hlkr hp
  · intro id hsome
    obtain ⟨hq, hf⟩ := hhist id (hisSome id hsome)
    refine ⟨fun hq' => ?_, fun f hf' => ?_⟩
    · rw [hhistEq id]
      rw [hfan'] at hq'
      exact hq hq'
    · rw [hfan'] at hf'
      obtain ⟨h₁, h₂⟩ := hf f hf'
      exact ⟨fun hp => by rw [hhistEq id]; exact h₁ hp, fun hnp => by rw [hhistEq id]; exact h₂ hnp⟩


theorem pullStep_targetStable {a a' : Subscriber} (h : pullStep a = some a') :
    TargetStable a a' := by
  rcases pullStep_ok_eq h with ⟨e, hst, heq⟩ | ⟨hst, -, heq⟩ | ⟨e, hst, -, heq⟩ <;>
    exact Or.inl ⟨by rw [hst]; intro hc; exact QueueStatus.noConfusion hc,
      by rw [heq], by rw [heq], by rw [heq]⟩

theorem flatten_single (c : List Observed) : ([c] : History).flatten = c := by simp

/-- The abstract side of one returning take, as `rel_consumer` wants it. -/
theorem pull_habs {r r' : RtSubscriber} {q' : EffectQueue} {i : SubId} {c : List Observed}
    (hro : r.registered = true → r.queue.status = .opened)
    (hcs : r.closeStarted = false)
    (hr' : r' = { r with queue := q', chunks := r.chunks ++ [c] })
    (hcase : TakeCase r.queue q' c) :
    ∀ (e? : Option SubError) (u : SubState) (a : Subscriber),
      lookupSub u.subs i = some a → corrSub (failOpt e? r) a →
      ∃ u' a', apply u (.pull i) = some u' ∧ AgreeExcept i u u' ∧
        lookupSub u'.subs i = some a' ∧ corrSub (failOpt e? r') a' ∧
        a'.observed = a.observed ++ ([c] : History).flatten ∧ TargetStable a a' := by
  intro e? u a hlka hca
  obtain ⟨a', hp, hobs, hc'⟩ := take_corr hro hcs hca hcase
  have hap : apply u (.pull i) = some { u with subs := updateSub u.subs i (fun _ => a') } := by
    show applyPull pullStep u i = _
    unfold applyPull
    simp only [hlka, hp]
  refine ⟨{ u with subs := updateSub u.subs i (fun _ => a') }, a', hap,
    agreeExcept_of_pull hap, lookupSub_updateSub_self (fun _ => a') hlka, ?_, ?_,
    pullStep_targetStable hp⟩
  · rw [hr']; exact hc'
  · rw [hobs, flatten_single]

theorem pull_hafter {i : SubId} {c : List Observed} :
    ∀ (u u' : SubState) (a a' : Subscriber) (h : History),
      lookupSub u.subs i = some a → lookupSub u'.subs i = some a' →
      a'.observed = a.observed ++ ([c] : History).flatten →
      afterLabel u u' i h (.pull i) = h ++ [c] := by
  intro u u' a a' h hlka hlka' hobs
  show (if i = i then h ++ [(observedOf u' i).drop (observedOf u i).length] else h) = h ++ [c]
  rw [if_pos rfl]
  have h1 : observedOf u i = a.observed := by unfold observedOf; rw [hlka]
  have h2 : observedOf u' i = a'.observed := by unfold observedOf; rw [hlka']
  rw [h1, h2, hobs, flatten_single, List.drop_left]

/-- The abstract side of `closeA`. -/
theorem unsub_habs {r r' : RtSubscriber} {i : SubId}
    (hcs : r.closeStarted = false) (hsd : r.queue.status ≠ .shutDown)
    (hr' : r' = { r with registered := false, closeStarted := true }) :
    ∀ (e? : Option SubError) (u : SubState) (a : Subscriber),
      lookupSub u.subs i = some a → corrSub (failOpt e? r) a →
      ∃ u' a', apply u (.unsubscribe i) = some u' ∧ AgreeExcept i u u' ∧
        lookupSub u'.subs i = some a' ∧ corrSub (failOpt e? r') a' ∧
        a'.observed = a.observed ++ ([] : History).flatten ∧ TargetStable a a' := by
  intro e? u a hlka hca
  obtain ⟨hne, hc'⟩ := closeA_corr hcs hsd hca
  have hap : apply u (.unsubscribe i) = some { u with
      subs := updateSub u.subs i
        (fun sub => { sub with registered := false, pending := [], status := .shutDown }) } := by
    show applyUnsubscribe u i = _
    unfold applyUnsubscribe
    simp only [hlka, if_neg hne]
  refine ⟨_, _, hap, agreeExcept_of_unsubscribe hap,
    lookupSub_updateSub_self _ hlka, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
  · rw [hr']; exact hc'
  · simp

theorem unsub_hafter {i : SubId} :
    ∀ (u u' : SubState) (a a' : Subscriber) (h : History),
      lookupSub u.subs i = some a → lookupSub u'.subs i = some a' →
      a'.observed = a.observed ++ ([] : History).flatten →
      afterLabel u u' i h (.unsubscribe i) = h ++ [] := by
  intro u u' a a' h _ _ _
  show h = h ++ []
  rw [List.append_nil]


theorem relStep_of_consumer {s' : RtState} {labels owed : List Label} {l : RtLabel} {lab : Label}
    (hlu : (∀ j, l ≠ RtLabel.closeA j) → ∀ j, lab ≠ Label.unsubscribe j)
    (h : ∃ labels' owed', Rel s' labels' owed' ∧ RelHist s' labels' owed' ∧
      labelSerial labels' ++ labelSerial owed' = labelSerial labels ++ labelSerial owed ∧
      (NoUnsub labels → NoUnsub owed → (∀ j, lab ≠ Label.unsubscribe j) →
        NoUnsub labels' ∧ NoUnsub owed')) :
    RelStep s' labels owed [] l := by
  obtain ⟨labels', owed', h₁, h₂, h₃, h₄⟩ := h
  exact ⟨labels', owed', h₁, h₂, by rw [h₃, List.append_nil], fun hc hl ho => h₄ hl ho (hlu hc)⟩

theorem relStep_of_silent {s' : RtState} {labels owed : List Label} {l : RtLabel}
    (h : Rel s' labels owed ∧ RelHist s' labels owed) : RelStep s' labels owed [] l :=
  ⟨labels, owed, h.1, h.2, by rw [List.append_nil], fun _ hl ho => ⟨hl, ho⟩⟩

theorem rel_step_pull {s s' : RtState} {id : SubId} (hinv : RtInv s)
    (hstep : rtPull s id = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] (.pull id) := by
  unfold rtPull at hstep
  cases hlk : lookupRt s.subs id with
  | none => simp only [hlk] at hstep; simp at hstep
  | some r =>
    simp only [hlk] at hstep
    split at hstep
    · cases hstep
    · rename_i hg
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq] at hg
      obtain ⟨⟨htk, hsd⟩, hcs0⟩ := hg
      have hcs : r.closeStarted = false := by
        cases hb : r.closeStarted with
        | false => rfl
        | true => exact absurd hb hcs0
      have hsub := rtSubInv_of_lookup hinv hlk
      have hro : r.registered = true → r.queue.status = .opened :=
        fun hb => (hsub.registeredOpen hb).1
      have hlu : (∀ j, RtLabel.pull id ≠ RtLabel.closeA j) → ∀ j, Label.pull id ≠ Label.unsubscribe j :=
        fun _ j hc => Label.noConfusion hc
      cases hst : r.queue.status with
      | shutDown => exact absurd hst hsd
      | done e =>
        rw [exit_after_drain r.queue e hst] at hstep
        simp only [chunkOf] at hstep
        cases hstep
        refine relStep_of_consumer hlu (rel_consumer (lab := Label.pull id)
          (ch := [[Observed.failed e]]) hlk rfl (Or.inl rfl) rfl
          (fun f => pendingFail_congr f id rfl)
          (pull_habs hro hcs rfl ?_) pull_hafter hrel hhist)
        exact Or.inr (Or.inr ⟨e, hst, hsub.queue.doneEmpty e hst, rfl, rfl⟩)
      | opened =>
        by_cases hb : r.queue.buffer = []
        · have htake : r.queue.takeAll = ({ r.queue with taker := true }, .parked) := by
            unfold EffectQueue.takeAll
            rw [hst]
            simp [hb, hst]
          rw [htake] at hstep
          simp only [chunkOf] at hstep
          cases hstep
          exact relStep_of_silent (rel_silent hlk rfl rfl (fun f => pendingFail_congr f id rfl)
            (fun e? a hc => park_corr hcs hsd hc rfl rfl) hrel hhist)
        · rw [takeAll_drains r.queue hst hb] at hstep
          simp only [chunkOf] at hstep
          cases hstep
          refine relStep_of_consumer hlu (rel_consumer (lab := Label.pull id)
            (ch := [r.queue.buffer.map Observed.entry]) hlk rfl (Or.inl rfl) rfl
            (fun f => pendingFail_congr f id rfl)
            (pull_habs hro hcs rfl ?_) pull_hafter hrel hhist)
          exact Or.inl ⟨hst, hb, rfl, hst, rfl⟩
      | closing e =>
        by_cases hb : r.queue.buffer = []
        · exact absurd hb (hsub.queue.closingNonempty e hst)
        · rw [takeAll_closing r.queue e hst hb] at hstep
          simp only [chunkOf] at hstep
          cases hstep
          refine relStep_of_consumer hlu (rel_consumer (lab := Label.pull id)
            (ch := [r.queue.buffer.map Observed.entry]) hlk rfl (Or.inl rfl) rfl
            (fun f => pendingFail_congr f id rfl)
            (pull_habs hro hcs rfl ?_) pull_hafter hrel hhist)
          exact Or.inr (Or.inl ⟨e, hst, hb, rfl, rfl, rfl⟩)


theorem rel_step_wake {s s' : RtState} {id : SubId} (hinv : RtInv s)
    (hstep : rtWake s id = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] (.wake id) := by
  unfold rtWake at hstep
  cases hlk : lookupRt s.subs id with
  | none => simp only [hlk] at hstep; simp at hstep
  | some r =>
    simp only [hlk] at hstep
    split at hstep
    · cases hstep
    · rename_i hcs0
      have hcs : r.closeStarted = false := by
        cases hb : r.closeStarted with
        | false => rfl
        | true => exact absurd hb hcs0
      have hsub := rtSubInv_of_lookup hinv hlk
      have hro : r.registered = true → r.queue.status = .opened :=
        fun hb => (hsub.registeredOpen hb).1
      have hlu : (∀ j, RtLabel.wake id ≠ RtLabel.closeA j) →
          ∀ j, Label.pull id ≠ Label.unsubscribe j := fun _ j hc => Label.noConfusion hc
      by_cases htk : r.queue.taker = true
      · cases hst : r.queue.status with
        | shutDown =>
          have hw : r.queue.wake = none := by unfold EffectQueue.wake; simp [htk, hst]
          rw [hw] at hstep
          simp at hstep
        | done e =>
          have hw : r.queue.wake =
              some ({ r.queue with status := .shutDown, taker := false }, .exit e) := by
            unfold EffectQueue.wake; simp [htk, hst]
          rw [hw] at hstep
          simp only [chunkOf] at hstep
          cases hstep
          refine relStep_of_consumer hlu (rel_consumer (lab := Label.pull id)
            (ch := [[Observed.failed e]]) hlk rfl (Or.inl rfl) rfl
            (fun f => pendingFail_congr f id rfl)
            (pull_habs hro hcs rfl ?_) pull_hafter hrel hhist)
          exact Or.inr (Or.inr ⟨e, hst, hsub.queue.doneEmpty e hst, rfl, rfl⟩)
        | opened =>
          by_cases hb : r.queue.buffer = []
          · have hw : r.queue.wake = none := by unfold EffectQueue.wake; simp [htk, hst, hb]
            rw [hw] at hstep
            simp at hstep
          · have hw : r.queue.wake =
                some ({ r.queue with buffer := [], taker := false }, .chunk r.queue.buffer) := by
              unfold EffectQueue.wake; simp [htk, hst, hb]
            rw [hw] at hstep
            simp only [chunkOf] at hstep
            cases hstep
            refine relStep_of_consumer hlu (rel_consumer (lab := Label.pull id)
              (ch := [r.queue.buffer.map Observed.entry]) hlk rfl (Or.inl rfl) rfl
              (fun f => pendingFail_congr f id rfl)
              (pull_habs hro hcs rfl ?_) pull_hafter hrel hhist)
            exact Or.inl ⟨hst, hb, rfl, hst, rfl⟩
        | closing e =>
          by_cases hb : r.queue.buffer = []
          · exact absurd hb (hsub.queue.closingNonempty e hst)
          · have hw : r.queue.wake =
                some ({ r.queue with buffer := [], status := .done e, taker := false },
                  .chunk r.queue.buffer) := by
              unfold EffectQueue.wake; simp [htk, hst, hb]
            rw [hw] at hstep
            simp only [chunkOf] at hstep
            cases hstep
            refine relStep_of_consumer hlu (rel_consumer (lab := Label.pull id)
              (ch := [r.queue.buffer.map Observed.entry]) hlk rfl (Or.inl rfl) rfl
              (fun f => pendingFail_congr f id rfl)
              (pull_habs hro hcs rfl ?_) pull_hafter hrel hhist)
            exact Or.inr (Or.inl ⟨e, hst, hb, rfl, rfl, rfl⟩)
      · have hw : r.queue.wake = none := by unfold EffectQueue.wake; simp [htk]
        rw [hw] at hstep
        simp at hstep

theorem rel_step_closeA {s s' : RtState} {id : SubId} (_hinv : RtInv s)
    (hstep : rtCloseA s id = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] (.closeA id) := by
  unfold rtCloseA at hstep
  cases hlk : lookupRt s.subs id with
  | none => simp only [hlk] at hstep; simp at hstep
  | some r =>
    simp only [hlk] at hstep
    split at hstep
    · cases hstep
    · rename_i hg
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq] at hg
      obtain ⟨hcs0, hsd⟩ := hg
      have hcs : r.closeStarted = false := by
        cases hb : r.closeStarted with
        | false => rfl
        | true => exact absurd hb hcs0
      cases hstep
      refine relStep_of_consumer (l := RtLabel.closeA id) (fun hc => absurd rfl (hc id))
        (rel_consumer (lab := Label.unsubscribe id) (ch := []) hlk rfl (Or.inr rfl) ?_
          (fun f => pendingFail_congr f id rfl)
          (unsub_habs hcs hsd rfl) unsub_hafter hrel hhist)
      rw [List.append_nil]

theorem rel_step_closeB {s s' : RtState} {id : SubId} (_hinv : RtInv s)
    (hstep : rtCloseB s id = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] (.closeB id) := by
  unfold rtCloseB at hstep
  cases hlk : lookupRt s.subs id with
  | none => simp only [hlk] at hstep; simp at hstep
  | some r =>
    simp only [hlk] at hstep
    split at hstep
    · cases hstep
    · rename_i hg
      have hcs : r.closeStarted = true := by
        cases hb : r.closeStarted with
        | false => rw [hb] at hg; simp at hg
        | true => rfl
      cases hstep
      exact relStep_of_silent (rel_silent hlk rfl rfl (fun f => pendingFail_congr f id rfl)
        (fun e? a hc => closeB_corr hcs hc) hrel hhist)


/-! ## Runtime association lists, continued -/

theorem lookupRt_append :
    ∀ (l : List (SubId × RtSubscriber)) (i k : SubId) (r : RtSubscriber),
      lookupRt (l ++ [(i, r)]) k =
        match lookupRt l k with
        | some b => some b
        | none => if i = k then some r else none := by
  intro l
  induction l with
  | nil => intro i k r; rfl
  | cons p rest ih =>
    obtain ⟨j, sub⟩ := p
    intro i k r
    show lookupRt ((j, sub) :: (rest ++ [(i, r)])) k = _
    simp only [lookupRt]
    by_cases hjk : j = k
    · simp only [if_pos hjk]
    · simp only [if_neg hjk]
      exact ih i k r

theorem lookupRt_none_of_fresh :
    ∀ (l : List (SubId × RtSubscriber)) (k : SubId),
      (∀ p ∈ l, p.1 ≠ k) → lookupRt l k = none := by
  intro l
  induction l with
  | nil => intro k _; rfl
  | cons p rest ih =>
    obtain ⟨j, sub⟩ := p
    intro k h
    have hjk : j ≠ k := h (j, sub) List.mem_cons_self
    simp only [lookupRt, if_neg hjk]
    exact ih k (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem lookupRt_of_mem_pairwise :
    ∀ (l : List (SubId × RtSubscriber)) (k : SubId) (r : RtSubscriber),
      (l.map Prod.fst).Pairwise (· < ·) → (k, r) ∈ l → lookupRt l k = some r := by
  intro l
  induction l with
  | nil => intro k r _ h; cases h
  | cons p rest ih =>
    obtain ⟨j, sub⟩ := p
    intro k r hp h
    rw [List.map_cons, List.pairwise_cons] at hp
    obtain ⟨hlt, hrest⟩ := hp
    rcases List.mem_cons.mp h with heq | hmem
    · cases heq
      simp [lookupRt]
    · have hjk : j ≠ k := by
        intro hj
        have hmemk : k ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(k, r), hmem, rfl⟩
        have := hlt k hmemk
        rw [hj] at this
        exact Nat.lt_irrefl _ this
      simp only [lookupRt, if_neg hjk]
      exact ih k r hrest hmem

/-! ## The core step of a deletion -/

theorem deleteStep_ret {c c' : JSState} {name : StreamName} {r : Ret}
    (h : step c (.deleteStream name) = .ok (c', r)) : r = .unit := by
  have h' : deleteStep c name = .ok (c', r) := h
  unfold deleteStep at h'
  split at h'
  · injection h' with h''
    injection h'' with _ hr
    exact hr.symm
  · cases h'

/-! ## Label lists without registrations -/

def NoRegister (ls : List Label) : Prop :=
  ∀ l ∈ ls, ∀ stream opts l₀ j e, l ≠ .register stream opts l₀ j e

theorem owedOp_ne_register (k : FanKind) (stream : StreamName) (opts : ConsumeOptions)
    (l₀ : StreamSeq) (j : SubId) (e : Expect) : owedOp k ≠ .register stream opts l₀ j e := by
  cases k <;> intro h <;> exact Label.noConfusion h

theorem apply_noRegister_frame {s t : SubState} {l : Label}
    (hl : ∀ stream opts l₀ j e, l ≠ .register stream opts l₀ j e)
    (h : apply s l = some t) :
    t.nextId = s.nextId ∧ t.subs.map Prod.fst = s.subs.map Prod.fst := by
  cases l with
  | op o e =>
    rcases e with r | err
    · obtain ⟨core', -, ht⟩ := applyOp_ok_eq (deliver := deliverOne) h
      rw [ht]
      cases o with
      | publish stream subject payload headers el now =>
        cases r <;> exact ⟨rfl, by simp only [afterOp, keys_map_snd]⟩
      | deleteStream name =>
        cases r <;> exact ⟨rfl, by simp only [afterOp, keys_map_snd]⟩
      | createStream _ => cases r <;> exact ⟨rfl, rfl⟩
      | getStream _ => cases r <;> exact ⟨rfl, rfl⟩
      | lastMessageForSubject _ _ => cases r <;> exact ⟨rfl, rfl⟩
    · obtain ⟨ht, -⟩ := applyOp_error_eq (deliver := deliverOne) h
      rw [ht]
      exact ⟨rfl, rfl⟩
  | register stream opts l₀ j e => exact absurd rfl (hl stream opts l₀ j e)
  | pull j =>
    obtain ⟨sub, sub', -, -, ht⟩ :=
      applyPull_ok_eq (pull := pullStep) (show applyPull pullStep s j = some t from h)
    rw [ht]
    exact ⟨rfl, updateSub_keys _ _ _⟩
  | unsubscribe j =>
    obtain ⟨sub, -, -, ht⟩ := applyUnsubscribe_ok_eq (show applyUnsubscribe s j = some t from h)
    rw [ht]
    exact ⟨rfl, updateSub_keys _ _ _⟩

theorem runLabels_noRegister_frame : ∀ (ls : List Label) {s t : SubState},
    NoRegister ls → runLabels s ls = some t →
    t.nextId = s.nextId ∧ t.subs.map Prod.fst = s.subs.map Prod.fst := by
  intro ls
  induction ls with
  | nil => intro s t _ h; cases h; exact ⟨rfl, rfl⟩
  | cons l rest ih =>
    intro s t hls h
    rw [runLabels_cons] at h
    cases hap : apply s l with
    | none => rw [hap] at h; cases h
    | some u =>
      rw [hap] at h
      obtain ⟨h₁, h₂⟩ := apply_noRegister_frame (fun stream opts l₀ j e =>
        hls l (List.Mem.head _) stream opts l₀ j e) hap
      obtain ⟨h₃, h₄⟩ := ih (fun m hm => hls m (List.Mem.tail _ hm)) h
      exact ⟨h₃.trans h₁, h₄.trans h₂⟩


theorem closed_rtFail {e : SubError} {r : RtSubscriber} (h : Closed r) : Closed (rtFail e r) := by
  rcases h with h | h
  · exact closed_failOpt_of_closeStarted (e? := some e) h
  · exact closed_failOpt_of_shutDown (e? := some e) h

theorem not_closed_rtFail {e : SubError} {r : RtSubscriber} (hcs : r.closeStarted = false)
    (hsd : r.queue.status ≠ .shutDown) : ¬ Closed (rtFail e r) :=
  not_closed_failOpt (e? := some e) hcs hsd

theorem corrSub_status {r : RtSubscriber} {a : Subscriber} (hcorr : corrSub r a)
    (hcl : ¬ Closed r) : a.status = r.queue.status := by rw [hcorr.2 hcl]; rfl

theorem isTargetOf_publish_registered {stream : StreamName} {m : StoredMessage}
    {el : Option StreamSeq} {a : Subscriber} (h : isTargetOf (.publish stream m el) a = true) :
    a.registered = true := by
  have h' : (a.stream == stream && a.registered && matchesAny a.filters m.subject) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1.2

theorem isTargetOf_delete_registered {name : StreamName} {a : Subscriber}
    (h : isTargetOf (.delete name) a = true) : a.registered = true := by
  have h' : (a.stream == name && a.registered) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.2

/-- A `check` that decided overflow: the abstract `deliverOne` lags the subscriber exactly as the
matching `resolve` will. -/
theorem overflow_corr {r : RtSubscriber} {a : Subscriber} {stream : StreamName}
    {m : StoredMessage} {el : Option StreamSeq} {n : Nat}
    (hpol : r.policy = .terminateOnLag n)
    (hro : r.registered = true → r.queue.status = .opened)
    (htgt : a.status = .shutDown ∨ isTargetOf (.publish stream m el) a = true)
    (hov : n ≤ r.queue.size)
    (hcorr : corrSub r a) :
    corrSub (rtFail (.consumerLagged stream r.lastEnqueued) r) (deliverOne stream m a) := by
  by_cases hcl : Closed r
  · obtain ⟨h1, h2, h3⟩ := hcorr.1 hcl
    rw [deliverOne_skip (by simp [h2])]
    exact corrSub_of_closed (closed_rtFail hcl) h1 h2 h3
  · have hae : a = r.erase := hcorr.2 hcl
    have hsd : r.queue.status ≠ .shutDown := fun h => hcl (Or.inr h)
    have hcs : r.closeStarted = false := by
      cases hb : r.closeStarted with
      | false => rfl
      | true => exact absurd (Or.inl hb) hcl
    have hstA : a.status = r.queue.status := by rw [hae]; rfl
    have hcond : isTargetOf (.publish stream m el) a = true := by
      rcases htgt with h | h
      · exact absurd (hstA.symm.trans h) hsd
      · exact h
    have hreg : r.registered = true := by
      have := isTargetOf_publish_registered hcond
      rw [hae] at this
      exact this
    have hst : r.queue.status = .opened := hro hreg
    have hpolA : a.policy = .terminateOnLag n := by rw [hae]; exact hpol
    have hfull : n ≤ a.pending.length := by
      rw [hae]
      show n ≤ r.queue.buffer.length
      rw [← size_eq_length r.queue (Or.inl hst)]
      exact hov
    rw [deliverOne_overflow hcond hpolA hfull]
    refine corrSub_of_erase (not_closed_rtFail hcs hsd) ?_
    rw [hae]
    show _ = (rtFail (.consumerLagged stream r.lastEnqueued) r).erase
    simp only [RtSubscriber.erase, rtFail, fail_buffer, fail_status, hst]
    simp

/-- A `resolve` that admits: the abstract `deliverOne` appends the same message. -/
theorem admit_corr {r : RtSubscriber} {a : Subscriber} {stream : StreamName}
    {m : StoredMessage} {el : Option StreamSeq} {q' : EffectQueue}
    {res : EffectQueue.OfferResult}
    (hro : r.registered = true → r.queue.status = .opened)
    (hroom : r.queue.buffer.length < r.policy.capacity ∨ r.queue.status ≠ .opened)
    (htgt : a.status = .shutDown ∨ isTargetOf (.publish stream m el) a = true)
    (hoffer : r.queue.offer r.policy.capacity m = (q', res))
    (hcorr : corrSub r a) :
    corrSub { r with queue := q', lastEnqueued := m.sequence } (deliverOne stream m a) := by
  by_cases hcl : Closed r
  · obtain ⟨h1, h2, h3⟩ := hcorr.1 hcl
    rw [deliverOne_skip (by simp [h2])]
    refine corrSub_of_closed ?_ h1 h2 h3
    rcases hcl with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have hqq : q' = r.queue := by
        rw [offer_refused r.policy.capacity r.queue m
          (by rw [h]; intro hc; exact QueueStatus.noConfusion hc)] at hoffer
        injection hoffer with h1 _
        exact h1.symm
      show q'.status = .shutDown
      rw [hqq]
      exact h
  · have hae : a = r.erase := hcorr.2 hcl
    have hsd : r.queue.status ≠ .shutDown := fun h => hcl (Or.inr h)
    have hcs : r.closeStarted = false := by
      cases hb : r.closeStarted with
      | false => rfl
      | true => exact absurd (Or.inl hb) hcl
    have hstA : a.status = r.queue.status := by rw [hae]; rfl
    have hcond : isTargetOf (.publish stream m el) a = true := by
      rcases htgt with h | h
      · exact absurd (hstA.symm.trans h) hsd
      · exact h
    have hreg : r.registered = true := by
      have := isTargetOf_publish_registered hcond
      rw [hae] at this
      exact this
    have hst : r.queue.status = .opened := hro hreg
    have hroom' : r.queue.buffer.length < r.policy.capacity := by
      rcases hroom with h | h
      · exact h
      · exact absurd hst h
    have hq' : q' = { r.queue with buffer := r.queue.buffer ++ [m] } := by
      rw [offer_admits r.policy.capacity r.queue m hst hroom'] at hoffer
      injection hoffer with h1 _
      exact h1.symm
    obtain ⟨n, hn⟩ : ∃ n, r.policy = .terminateOnLag n := by
      cases hp : r.policy with
      | terminateOnLag n => exact ⟨n, rfl⟩
    have hpolA : a.policy = .terminateOnLag n := by rw [hae]; exact hn
    have hcap : r.policy.capacity = n := by rw [hn]; rfl
    have hroomA : a.pending.length < n := by
      rw [hae]
      show r.queue.buffer.length < n
      rw [← hcap]
      exact hroom'
    have hopenA : a.status = .opened := hstA.trans hst
    rw [deliverOne_admit hcond hpolA hroomA hopenA]
    refine corrSub_of_erase ?_ ?_
    · rintro (h | h)
      · rw [hcs] at h; exact Bool.noConfusion h
      · rw [hq'] at h
        rw [show ({ r.queue with buffer := r.queue.buffer ++ [m] } : EffectQueue).status
              = r.queue.status from rfl, hst] at h
        cases h
    · rw [hae, hq']
      rfl

/-- A `resolve` of a deletion fan-out: the abstract `endOne` fails the same subscriber. -/
theorem end_corr {r : RtSubscriber} {a : Subscriber} {name : StreamName}
    (hro : r.registered = true → r.queue.status = .opened)
    (htgt : a.status = .shutDown ∨ isTargetOf (.delete name) a = true)
    (hcorr : corrSub r a) :
    corrSub (rtFail (.streamNotFound name) r) (endOne name a) := by
  by_cases hcl : Closed r
  · obtain ⟨h1, h2, h3⟩ := hcorr.1 hcl
    rw [endOne_skip (by simp [h2])]
    exact corrSub_of_closed (closed_rtFail hcl) h1 h2 h3
  · have hae : a = r.erase := hcorr.2 hcl
    have hsd : r.queue.status ≠ .shutDown := fun h => hcl (Or.inr h)
    have hcs : r.closeStarted = false := by
      cases hb : r.closeStarted with
      | false => rfl
      | true => exact absurd (Or.inl hb) hcl
    have hstA : a.status = r.queue.status := by rw [hae]; rfl
    have hcond : isTargetOf (.delete name) a = true := by
      rcases htgt with h | h
      · exact absurd (hstA.symm.trans h) hsd
      · exact h
    have hreg : r.registered = true := by
      have := isTargetOf_delete_registered hcond
      rw [hae] at this
      exact this
    have hst : r.queue.status = .opened := hro hreg
    rw [endOne_end hcond]
    refine corrSub_of_erase (not_closed_rtFail hcs hsd) ?_
    rw [hae]
    show _ = (rtFail (.streamNotFound name) r).erase
    simp only [RtSubscriber.erase, rtFail, fail_buffer, fail_status, hst]
    simp


/-- Where the owed operation leaves a subscriber whose point has not passed. -/
theorem owed_lookup {sA sPost : SubState} {f : FanOut} {owedRest : List Label} {id : SubId}
    {a : Subscriber}
    (hrun : runLabels sA (owedOp f.kind :: owedRest) = some sPost)
    (hok : OwedOk f owedRest) (hnp : pointPassed f id = false)
    (hlka : lookupSub sA.subs id = some a) :
    (∀ stream m el, f.kind = .publish stream m el →
        lookupSub sPost.subs id = some (deliverOne stream m a)) ∧
    (∀ name, f.kind = .delete name → lookupSub sPost.subs id = some (endOne name a)) := by
  rw [runLabels_cons] at hrun
  cases hap : apply sA (owedOp f.kind) with
  | none => rw [hap] at hrun; cases hrun
  | some sA₁ =>
    rw [hap] at hrun
    have hframe : lookupSub sPost.subs id = lookupSub sA₁.subs id :=
      runLabels_lookup_frame owedRest
        (fun l hl => by
          obtain ⟨j, hj, hpj⟩ := hok l hl
          refine ⟨j, hj, fun he => ?_⟩
          rw [he, hnp] at hpj
          exact Bool.noConfusion hpj)
        hrun
    constructor
    · intro stream m el hk
      rw [hframe]
      rw [hk] at hap
      have hpe := applyOp_publish_each
        (show apply sA (.op (.publish stream m.subject m.payload m.headers el m.timestampMillis)
          (.ok (.sequence m.sequence))) = some sA₁ from hap) id
      rw [hpe, hlka]
      rfl
    · intro name hk
      rw [hframe]
      rw [hk] at hap
      have hpe := applyOp_delete_each
        (show apply sA (.op (.deleteStream name) (.ok .unit)) = some sA₁ from hap) id
      rw [hpe, hlka]
      rfl

/-- The three shapes of a successful runtime registration, paired with the abstract step it
matches from any state agreeing on the core and on `nextId`. -/
theorem rtRegister_cases {s s' : RtState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} {e : Expect}
    (h : rtRegister s stream opts l₀ id e = some s') :
    s.fanOut = none ∧ id = s.nextId ∧
      ((s' = s ∧ ∀ (sA : SubState), sA.core = s.core → sA.nextId = s.nextId →
          applyRegister sA stream opts l₀ id e = some sA)
       ∨ (∃ st : StreamState, s' = { s with
              subs := s.subs ++ [(id,
                { stream := stream, filters := opts.filters, policy := opts.buffer,
                  registered := true, lastEnqueued := l₀, queue := EffectQueue.empty,
                  chunks := [replayObserved st.messages opts], closeStarted := false })],
              nextId := id + 1 } ∧
            ∀ (sA : SubState), sA.core = s.core → sA.nextId = s.nextId →
              applyRegister sA stream opts l₀ id e = some
                { sA with subs := sA.subs ++ [(id, newSubscriber stream opts l₀ st.messages)],
                          nextId := id + 1 })) := by
  unfold rtRegister at h
  split at h
  · cases h
  · rename_i hg
    simp only [Bool.or_eq_true, not_or, decide_eq_true_eq] at hg
    obtain ⟨⟨hfan, hid⟩, hcap⟩ := hg
    have hfan' : s.fanOut = none := by
      cases hf : s.fanOut with
      | none => rfl
      | some f => rw [hf] at hfan; exact absurd rfl hfan
    have hid' : id = s.nextId := Classical.byContradiction hid
    have hguard : ¬ (id ≠ s.nextId || opts.buffer.capacity = 0) := by
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq]
      exact ⟨hid, hcap⟩
    refine ⟨hfan', hid', ?_⟩
    split at h
    · rename_i name hls
      split at h
      · rename_i hname
        cases h
        refine Or.inl ⟨rfl, fun sA hc hn => ?_⟩
        unfold applyRegister
        rw [if_neg (by rw [hn]; exact hguard), hc, hls]
        simp only [if_pos hname]
      · cases h
    · rename_i st hls
      split at h
      · rename_i hb
        cases h
        refine Or.inr ⟨st, rfl, fun sA hc hn => ?_⟩
        unfold applyRegister
        rw [if_neg (by rw [hn]; exact hguard), hc, hls]
        simp only [if_pos hb]
      · cases h
    · cases h


theorem lookup_lt_nextId {s : RtState} (hinv : RtInv s) {id : SubId} {r : RtSubscriber}
    (h : lookupRt s.subs id = some r) : id < s.nextId :=
  hinv.shape.2 (id, r) (mem_of_lookupRt s.subs id r h)

theorem lookupSub_none_of_keys {sA : SubState} {s : RtState} {id : SubId}
    (hkeys : sA.subs.map Prod.fst = s.subs.map Prod.fst)
    (hfresh : ∀ p ∈ s.subs, p.1 ≠ id) : lookupSub sA.subs id = none := by
  refine lookupSub_none_of_fresh (fun p hp => ?_)
  have hmem : p.1 ∈ sA.subs.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [hkeys] at hmem
  obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hmem
  rw [← hq']
  exact hfresh q hq

theorem rel_step_register {s s' : RtState} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} {e : Expect} (hinv : RtInv s)
    (hstep : rtRegister s stream opts l₀ id e = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [Label.register stream opts l₀ id e]
      (.register stream opts l₀ id e) := by
  obtain ⟨hfan, hid, hcases⟩ := rtRegister_cases hstep
  obtain ⟨sA, hrun, hnext, hkeys, hquiet, -⟩ := hrel
  obtain ⟨howed, hcoreA, hcorr⟩ := hquiet hfan
  subst howed
  have hfresh : ∀ p ∈ s.subs, p.1 ≠ id := by
    intro p hp he
    have := hinv.shape.2 p hp
    rw [he, ← hid] at this
    exact Nat.lt_irrefl _ this
  have hlkNone : lookupRt s.subs id = none := lookupRt_none_of_fresh s.subs id hfresh
  have hlkNoneA : lookupSub sA.subs id = none := lookupSub_none_of_keys hkeys hfresh
  have hserial : labelSerial (labels ++ [Label.register stream opts l₀ id e]) ++ labelSerial []
      = labelSerial labels ++ labelSerial [] ++ [Label.register stream opts l₀ id e] := by
    simp [labelSerial_append, labelSerial]
  have hnu : NoUnsub labels → NoUnsub ([] : List Label) →
      NoUnsub (labels ++ [Label.register stream opts l₀ id e]) ∧ NoUnsub ([] : List Label) := by
    intro hnl _
    exact ⟨noUnsub_append hnl (noUnsub_single (fun j hc => Label.noConfusion hc)),
      fun l hl => by cases hl⟩
  rcases hcases with ⟨hs', hab⟩ | ⟨st, hs', hab⟩
  · rw [hs']
    have hapA : apply sA (Label.register stream opts l₀ id e) = some sA := hab sA hcoreA hnext
    refine ⟨labels ++ [Label.register stream opts l₀ id e], [],
      ⟨sA, runLabels_snoc hrun hapA, hnext, hkeys, ?_, ?_⟩, ?_, hserial, fun _ => hnu⟩
    · exact fun _ => ⟨rfl, hcoreA, hcorr⟩
    · intro f hf; rw [hfan] at hf; cases hf
    · intro id' hsome
      refine ⟨fun _ => ?_, fun f hf => by rw [hfan] at hf; cases hf⟩
      have hbase : abstractHistory labels id' = some (rtHistory s id') := (hhist id' hsome).1 hfan
      rw [abstractHistory_append id' labels [Label.register stream opts l₀ id e] hrun hbase]
      show (match apply sA (Label.register stream opts l₀ id e) with
            | some u => abstractHistoryFrom id' u
                (afterLabel sA u id' (rtHistory s id') (Label.register stream opts l₀ id e)) []
            | none => none) = _
      rw [hapA]
      show some (afterLabel sA sA id' (rtHistory s id') (Label.register stream opts l₀ id e)) = _
      have hne : ¬ (id = id') := by
        intro he
        subst he
        rw [hlkNone] at hsome
        exact Bool.noConfusion hsome
      show some (if id = id' then [observedOf sA id'] else rtHistory s id') = _
      rw [if_neg hne]
  · subst hs'
    have hapA : apply sA (Label.register stream opts l₀ id e) = some
        { sA with subs := sA.subs ++ [(id, newSubscriber stream opts l₀ st.messages)],
                  nextId := id + 1 } := hab sA hcoreA hnext
    refine ⟨labels ++ [Label.register stream opts l₀ id e], [],
      ⟨_, runLabels_snoc hrun hapA, rfl, ?_, ?_, ?_⟩, ?_, hserial, fun _ => hnu⟩
    · show (sA.subs ++ [(id, newSubscriber stream opts l₀ st.messages)]).map Prod.fst
          = (s.subs ++ [(id, _)]).map Prod.fst
      simp [List.map_append, hkeys]
    · intro _
      refine ⟨rfl, hcoreA, ?_⟩
      intro id' r₁ hlkr
      show ∃ a, lookupSub (sA.subs ++ [(id, newSubscriber stream opts l₀ st.messages)]) id' = some a
        ∧ corrSub r₁ a
      rw [lookupRt_append] at hlkr
      rw [lookupSub_append]
      cases hb : lookupRt s.subs id' with
      | some b =>
        rw [hb] at hlkr
        cases hlkr
        obtain ⟨a, hlka, hca⟩ := hcorr id' r₁ hb
        rw [hlka]
        exact ⟨a, rfl, hca⟩
      | none =>
        rw [hb] at hlkr
        by_cases hii : id = id'
        · rw [if_pos hii] at hlkr
          cases hlkr
          subst hii
          rw [hlkNoneA, if_pos rfl]
          refine ⟨_, rfl, corrSub_of_erase (fun hcl => ?_) ?_⟩
          · rcases hcl with hcl | hcl
            · exact Bool.noConfusion hcl
            · exact QueueStatus.noConfusion hcl
          · show newSubscriber stream opts l₀ st.messages = _
            simp [newSubscriber, RtSubscriber.erase, EffectQueue.empty]
        · rw [if_neg hii] at hlkr
          cases hlkr
    · intro f hf; rw [hfan] at hf; cases hf
    · intro id' hsome
      refine ⟨fun _ => ?_, fun f hf => by rw [hfan] at hf; cases hf⟩
      obtain ⟨h₀, hh₀⟩ := abstractHistory_isSome id' labels hrun
      rw [abstractHistory_append id' labels [Label.register stream opts l₀ id e] hrun hh₀]
      show (match apply sA (Label.register stream opts l₀ id e) with
            | some u => abstractHistoryFrom id' u
                (afterLabel sA u id' h₀ (Label.register stream opts l₀ id e)) []
            | none => none) = _
      rw [hapA]
      show some (if id = id' then
          [observedOf { sA with
              subs := sA.subs ++ [(id, newSubscriber stream opts l₀ st.messages)],
              nextId := id + 1 } id'] else h₀) = _
      by_cases hii : id = id'
      · rw [if_pos hii]
        subst hii
        show some [observedOf _ id] = some (rtHistory _ id)
        have hlkA : lookupSub (sA.subs ++ [(id, newSubscriber stream opts l₀ st.messages)]) id
            = some (newSubscriber stream opts l₀ st.messages) := by
          rw [lookupSub_append, hlkNoneA, if_pos rfl]
        have hobs : observedOf { sA with
            subs := sA.subs ++ [(id, newSubscriber stream opts l₀ st.messages)],
            nextId := id + 1 } id = replayObserved st.messages opts := by
          unfold observedOf
          rw [hlkA]
          rfl
        rw [hobs]
        show _ = some (rtHistory _ id)
        unfold rtHistory
        rw [lookupRt_append, hlkNone, if_pos rfl]
      · rw [if_neg hii]
        have hsome' : (lookupRt s.subs id').isSome = true := by
          rw [lookupRt_append] at hsome
          cases hb : lookupRt s.subs id' with
          | some b => rfl
          | none => rw [hb, if_neg hii] at hsome; exact Bool.noConfusion hsome
        have hbase : abstractHistory labels id' = some (rtHistory s id') :=
          (hhist id' hsome').1 hfan
        rw [hh₀] at hbase
        cases hbase
        show _ = some (rtHistory _ id')
        unfold rtHistory
        rw [lookupRt_append]
        cases hb : lookupRt s.subs id' with
        | some b => rfl
        | none => rw [hb] at hsome'; exact Bool.noConfusion hsome'


theorem not_closed_of_registered {s : RtState} {r : RtSubscriber} (hsub : RtSubInv s r)
    (h : r.registered = true) : ¬ Closed r := by
  rintro (hcl | hcl)
  · rw [(hsub.closeStartedOpen hcl).1] at h
    exact Bool.noConfusion h
  · rw [(hsub.registeredOpen h).1] at hcl
    exact QueueStatus.noConfusion hcl

theorem lookupRt_isSome_of_keys {rs : List (SubId × RtSubscriber)} {as : List (SubId × Subscriber)}
    (hkeys : as.map Prod.fst = rs.map Prod.fst) :
    ∀ id a, lookupSub as id = some a → ∃ r, lookupRt rs id = some r := by
  induction rs generalizing as with
  | nil =>
    intro id a h
    cases as with
    | nil => cases h
    | cons q qs => simp at hkeys
  | cons p rest ih =>
    obtain ⟨i, sub⟩ := p
    cases as with
    | nil => intro id a h; cases h
    | cons q qs =>
      obtain ⟨j, b⟩ := q
      simp only [List.map_cons, List.cons.injEq] at hkeys
      obtain ⟨hij, htl⟩ := hkeys
      intro id a h
      simp only [lookupSub] at h
      by_cases hj : j = id
      · exact ⟨sub, by simp only [lookupRt, if_pos (hij.symm.trans hj)]⟩
      · rw [if_neg hj] at h
        have hij' : ¬ i = id := fun he => hj (hij.trans he)
        obtain ⟨r, hr⟩ := ih (as := qs) htl id a h
        exact ⟨r, by simp only [lookupRt, if_neg hij']; exact hr⟩

/-- A runtime step that only advances the core. -/
theorem rel_op_plain {s : RtState} {core' : JSState} {labels : List Label} {o : Op} {e : Expect}
    {sA sA' : SubState}
    (hfan : s.fanOut = none)
    (hrun : runLabels initialSub labels = some sA)
    (hnext : sA.nextId = s.nextId) (hkeys : sA.subs.map Prod.fst = s.subs.map Prod.fst)
    (hcorr : CorrAll s sA) (hhist : RelHist s labels [])
    (hapA : apply sA (.op o e) = some sA')
    (hsub : sA'.subs = sA.subs) (hnextA : sA'.nextId = sA.nextId) (hcoreA' : sA'.core = core') :
    RelStep { s with core := core' } labels [] [Label.op o e] (.op o e) := by
  refine ⟨labels ++ [Label.op o e], [], ⟨sA', runLabels_snoc hrun hapA, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hnextA, hnext]
  · rw [hsub, hkeys]
  · intro _
    refine ⟨rfl, hcoreA', ?_⟩
    intro id r₀ hlkr
    obtain ⟨a, hlka, hca⟩ := hcorr id r₀ hlkr
    exact ⟨a, by rw [hsub]; exact hlka, hca⟩
  · intro f hf
    rw [hfan] at hf
    cases hf
  · intro id hsome
    refine ⟨fun _ => ?_, fun f hf => by rw [hfan] at hf; cases hf⟩
    have hbase : abstractHistory labels id = some (rtHistory s id) := (hhist id hsome).1 hfan
    rw [abstractHistory_append id labels [Label.op o e] hrun hbase]
    show (match apply sA (Label.op o e) with
          | some u => abstractHistoryFrom id u (afterLabel sA u id (rtHistory s id) (.op o e)) []
          | none => none) = _
    rw [hapA]
    rfl
  · simp [labelSerial_append, labelSerial]
  · intro _ hnl _
    exact ⟨noUnsub_append hnl (noUnsub_single (fun j hc => Label.noConfusion hc)),
      fun l hl => by cases hl⟩


/-- A runtime step that opens a fan-out: the abstract operation becomes the owed label. -/
theorem rel_op_fanout {s : RtState} {core' : JSState} {labels : List Label} {o : Op} {e : Expect}
    {sA sPost : SubState} {k : FanKind} {ids : List SubId}
    (hfan : s.fanOut = none)
    (hrun : runLabels initialSub labels = some sA)
    (hnext : sA.nextId = s.nextId) (hkeys : sA.subs.map Prod.fst = s.subs.map Prod.fst)
    (hcorr : CorrAll s sA) (hhist : RelHist s labels [])
    (hmem : ∀ id a, lookupSub sA.subs id = some a → isTargetOf k a = true → id ∈ ids)
    (hsched : ∀ id, id ∈ ids → ∀ a, lookupSub sA.subs id = some a →
        a.status = .shutDown ∨ isTargetOf k a = true)
    (hrcore : RelCore { kind := k, remaining := ids, decided := none, visited := [] } sA
        { s with
            core := core',
            fanOut := some { kind := k, remaining := ids, decided := none, visited := [] } })
    (hopA : apply sA (owedOp k) = some sPost)
    (hserial : labelSerial [owedOp k] = [Label.op o e]) :
    RelStep { s with
        core := core',
        fanOut := some { kind := k, remaining := ids, decided := none, visited := [] } }
      labels [] [Label.op o e] (.op o e) := by
  have hpp : ∀ id,
      pointPassed { kind := k, remaining := ids, decided := none, visited := [] } id = false :=
    fun _ => rfl
  refine ⟨labels, [owedOp k], ⟨sA, hrun, hnext, hkeys, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hq
    cases hq
  · intro f hf
    obtain rfl : { kind := k, remaining := ids, decided := none, visited := [] } = f :=
      Option.some.inj hf
    refine ⟨fun id _ => rfl, ?_, hrcore, ?_, [], sPost, rfl, (fun l hl => by cases hl), ?_, ?_⟩
    · intro id a hlka _
      refine ⟨?_, ?_⟩
      · cases htgt : isTargetOf k a with
        | true => exact Or.inl (Or.inl (hmem id a hlka htgt))
        | false => exact Or.inr rfl
      · rintro (hs | ⟨b, hb⟩)
        · exact hsched id hs a hlka
        · cases hb
    · intro id r₀ hlkr _
      exact hcorr id r₀ hlkr
    · rw [runLabels_single]
      exact hopA
    · intro id r₀ _ hp
      rw [hpp id] at hp
      exact Bool.noConfusion hp
  · intro id hsome
    refine ⟨(fun hq => by cases hq), fun f hf => ?_⟩
    obtain rfl : { kind := k, remaining := ids, decided := none, visited := [] } = f :=
      Option.some.inj hf
    refine ⟨(fun hp => by rw [hpp id] at hp; exact Bool.noConfusion hp), fun _ => ?_⟩
    exact (hhist id hsome).1 hfan
  · rw [hserial]
    simp [labelSerial]
  · intro _ hnl _
    exact ⟨hnl, noUnsub_single (fun j => owedOp_ne_unsubscribe k j)⟩


/-- The abstract subscriber of a runtime one that a fan-out targets. -/
theorem corr_erase_of_target {s : RtState} {sA : SubState} {id : SubId} {a : Subscriber}
    {r : RtSubscriber} (hcorr : CorrAll s sA) (hlkr : lookupRt s.subs id = some r)
    (hlka : lookupSub sA.subs id = some a) (hreg : a.registered = true) : a = r.erase := by
  obtain ⟨b, hlkb, hcb⟩ := hcorr id r hlkr
  rw [hlka] at hlkb
  cases hlkb
  refine hcb.2 (fun hcl => ?_)
  rw [(hcb.1 hcl).2.1] at hreg
  exact Bool.noConfusion hreg

theorem rel_step_op {s s' : RtState} {o : Op} {e : Expect} (hinv : RtInv s)
    (hstep : rtOp s o e = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [Label.op o e] (.op o e) := by
  unfold rtOp at hstep
  split at hstep
  · cases hstep
  · rename_i hfs
    have hfan : s.fanOut = none := by
      cases hf : s.fanOut with
      | none => rfl
      | some f => rw [hf] at hfs; exact absurd rfl hfs
    obtain ⟨sA, hrun, hnext, hkeys, hquiet, -⟩ := hrel
    obtain ⟨howed, hcoreA, hcorr⟩ := hquiet hfan
    subst howed
    cases hst : step s.core o with
    | error err =>
      cases e with
      | ok r' => simp only [hst] at hstep; cases hstep
      | error err' =>
        simp only [hst] at hstep
        split at hstep
        · rename_i heq
          cases hstep
          subst heq
          have hapA : apply sA (.op o (.error err)) = some sA :=
            applyOp_error_of_step (by rw [hcoreA]; exact hst)
          exact (show RelStep { s with core := s.core } labels [] [Label.op o (.error err)]
              (.op o (.error err)) from
            rel_op_plain hfan hrun hnext hkeys hcorr hhist hapA rfl rfl hcoreA)
        · cases hstep
    | ok p =>
      obtain ⟨core', r⟩ := p
      cases e with
      | error err' => simp only [hst] at hstep; cases hstep
      | ok r' =>
        simp only [hst] at hstep
        split at hstep
        · cases hstep
        · rename_i hrr
          have hrr' : r = r' := Classical.byContradiction hrr
          subst hrr'
          have hstA : step sA.core o = .ok (core', r) := by rw [hcoreA]; exact hst
          have hapA : apply sA (.op o (.ok r)) = some (afterOp deliverOne sA core' o r) :=
            applyOp_ok_of_step hstA
          cases o with
          | publish stream subject payload headers el now =>
            cases r with
            | sequence seq =>
              simp only at hstep
              cases hstep
              refine rel_op_fanout (k := .publish stream
                  { subject := subject, sequence := seq, payload := payload, headers := headers,
                    timestampMillis := now } el)
                hfan hrun hnext hkeys hcorr hhist ?_ ?_ ?_ hapA rfl
              · intro id a hlka htgt
                obtain ⟨r₀, hlkr⟩ := lookupRt_isSome_of_keys hkeys id a hlka
                have hreg : a.registered = true := isTargetOf_publish_registered htgt
                have hae : a = r₀.erase := corr_erase_of_target hcorr hlkr hlka hreg
                have h3 : (a.stream == stream) = true ∧ a.registered = true ∧
                    matchesAny a.filters subject = true := by
                  have h' : (a.stream == stream && a.registered &&
                      matchesAny a.filters subject) = true := htgt
                  simp only [Bool.and_eq_true] at h'
                  exact ⟨h'.1.1, h'.1.2, h'.2⟩
                rw [hae] at h3
                show id ∈ (s.subs.filter (fun p => p.2.registered && p.2.stream == stream &&
                  matchesAny p.2.filters subject)).map Prod.fst
                refine List.mem_map.mpr ⟨(id, r₀),
                  List.mem_filter.mpr ⟨mem_of_lookupRt s.subs id r₀ hlkr, ?_⟩, rfl⟩
                show (r₀.registered && r₀.stream == stream &&
                  matchesAny r₀.filters subject) = true
                simp only [Bool.and_eq_true]
                exact ⟨⟨h3.2.1, h3.1⟩, h3.2.2⟩
              · intro id hid a hlka
                obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hid
                obtain ⟨hqmem, hpred⟩ := List.mem_filter.mp hq
                have hlkr : lookupRt s.subs id = some q.2 := by
                  rw [← hq1]
                  exact lookupRt_of_mem_pairwise s.subs q.1 q.2 hinv.shape.1 hqmem
                have h3 : q.2.registered = true ∧ (q.2.stream == stream) = true ∧
                    matchesAny q.2.filters subject = true := by
                  simp only [Bool.and_eq_true] at hpred
                  exact ⟨hpred.1.1, hpred.1.2, hpred.2⟩
                have hae : a = q.2.erase :=
                  corr_erase_of_target hcorr hlkr hlka (by
                    obtain ⟨b, hlkb, hcb⟩ := hcorr id q.2 hlkr
                    rw [hlka] at hlkb
                    cases hlkb
                    rw [hcb.2 (not_closed_of_registered (rtSubInv_of_lookup hinv hlkr) h3.1)]
                    exact h3.1)
                refine Or.inr ?_
                show (a.stream == stream && a.registered && matchesAny a.filters subject) = true
                rw [hae]
                simp only [Bool.and_eq_true]
                exact ⟨⟨h3.2.1, h3.1⟩, h3.2.2⟩
              · exact ⟨(fun stream' m' el' hk => by cases hk; exact hstA),
                  (fun name hk => by cases hk)⟩
            | unit =>
              simp only at hstep
              cases hstep
              exact rel_op_plain hfan hrun hnext hkeys hcorr hhist hapA rfl rfl rfl
            | config c =>
              simp only at hstep
              cases hstep
              exact rel_op_plain hfan hrun hnext hkeys hcorr hhist hapA rfl rfl rfl
            | message mm =>
              simp only at hstep
              cases hstep
              exact rel_op_plain hfan hrun hnext hkeys hcorr hhist hapA rfl rfl rfl
          | deleteStream name =>
            have hru : r = .unit := deleteStep_ret hst
            subst hru
            simp only at hstep
            cases hstep
            refine rel_op_fanout (k := .delete name)
              hfan hrun hnext hkeys hcorr hhist ?_ ?_ ?_ hapA rfl
            · intro id a hlka htgt
              obtain ⟨r₀, hlkr⟩ := lookupRt_isSome_of_keys hkeys id a hlka
              have hreg : a.registered = true := isTargetOf_delete_registered htgt
              have hae : a = r₀.erase := corr_erase_of_target hcorr hlkr hlka hreg
              have h3 : (a.stream == name) = true ∧ a.registered = true := by
                have h' : (a.stream == name && a.registered) = true := htgt
                simp only [Bool.and_eq_true] at h'
                exact h'
              rw [hae] at h3
              show id ∈ (s.subs.filter (fun p => p.2.registered && p.2.stream == name)).map Prod.fst
              refine List.mem_map.mpr ⟨(id, r₀),
                List.mem_filter.mpr ⟨mem_of_lookupRt s.subs id r₀ hlkr, ?_⟩, rfl⟩
              show (r₀.registered && r₀.stream == name) = true
              simp only [Bool.and_eq_true]
              exact ⟨h3.2, h3.1⟩
            · intro id hid a hlka
              obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hid
              obtain ⟨hqmem, hpred⟩ := List.mem_filter.mp hq
              have hlkr : lookupRt s.subs id = some q.2 := by
                rw [← hq1]
                exact lookupRt_of_mem_pairwise s.subs q.1 q.2 hinv.shape.1 hqmem
              have h3 : q.2.registered = true ∧ (q.2.stream == name) = true := by
                simp only [Bool.and_eq_true] at hpred
                exact hpred
              have hae : a = q.2.erase :=
                corr_erase_of_target hcorr hlkr hlka (by
                  obtain ⟨b, hlkb, hcb⟩ := hcorr id q.2 hlkr
                  rw [hlka] at hlkb
                  cases hlkb
                  rw [hcb.2 (not_closed_of_registered (rtSubInv_of_lookup hinv hlkr) h3.1)]
                  exact h3.1)
              refine Or.inr ?_
              show (a.stream == name && a.registered) = true
              rw [hae]
              simp only [Bool.and_eq_true]
              exact ⟨h3.2, h3.1⟩
            · exact ⟨(fun stream' m' el' hk => by cases hk),
                (fun name' hk => by cases hk; exact hstA)⟩
          | createStream raw =>
            cases r <;>
              (simp only at hstep
               cases hstep
               exact rel_op_plain hfan hrun hnext hkeys hcorr hhist hapA rfl rfl rfl)
          | getStream nm =>
            cases r <;>
              (simp only at hstep
               cases hstep
               exact rel_op_plain hfan hrun hnext hkeys hcorr hhist hapA rfl rfl rfl)
          | lastMessageForSubject st sj =>
            cases r <;>
              (simp only at hstep
               cases hstep
               exact rel_op_plain hfan hrun hnext hkeys hcorr hhist hapA rfl rfl rfl)


theorem noRegister_owed {f : FanOut} {owedRest : List Label} (hok : OwedOk f owedRest) :
    NoRegister (owedOp f.kind :: owedRest) := by
  intro l hl stream opts l₀ j e
  rcases List.mem_cons.mp hl with he | hm
  · subst he
    exact owedOp_ne_register f.kind stream opts l₀ j e
  · obtain ⟨i, hi, -⟩ := hok l hm
    rcases hi with hi | hi <;> subst hi <;> intro hc <;> exact Label.noConfusion hc

theorem consumerOnly_owedRest {f : FanOut} {owedRest : List Label} (hok : OwedOk f owedRest) :
    ∀ l ∈ owedRest, ∃ j, l = .pull j ∨ l = .unsubscribe j := by
  intro l hl
  obtain ⟨i, hi, -⟩ := hok l hl
  exact ⟨i, hi⟩

/-- The owed suffix leaves the history of a subscriber whose point has not passed alone. -/
theorem owed_hist_frame {f : FanOut} {owedRest : List Label} {id : SubId}
    (hok : OwedOk f owedRest) (hnp : pointPassed f id = false) :
    ∀ l ∈ owedOp f.kind :: owedRest, (∀ j, l = .pull j → j ≠ id) ∧
      ∀ stream opts l₀ j e, l = .register stream opts l₀ j e → j ≠ id := by
  intro l hl
  rcases List.mem_cons.mp hl with he | hm
  · subst he
    exact ⟨fun j hc => absurd hc (owedOp_ne_pull f.kind j),
      fun stream opts l₀ j e hc => absurd hc (owedOp_ne_register f.kind stream opts l₀ j e)⟩
  · obtain ⟨i, hi, hpi⟩ := hok l hm
    refine ⟨fun j hc => ?_, fun stream opts l₀ j e hc => ?_⟩
    · rcases hi with hi | hi <;> subst hi
      · cases hc
        intro he
        subst he
        rw [hnp] at hpi
        exact Bool.noConfusion hpi
      · exact absurd hc (fun hcc => Label.noConfusion hcc)
    · rcases hi with hi | hi <;> subst hi <;> exact absurd hc (fun hcc => Label.noConfusion hcc)

theorem rel_step_endFanOut {s s' : RtState} (_hinv : RtInv s)
    (hstep : rtEndFanOut s = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] .endFanOut := by
  unfold rtEndFanOut at hstep
  cases hfan : s.fanOut with
  | none => simp only [hfan] at hstep; simp at hstep
  | some f =>
    simp only [hfan] at hstep
    split at hstep
    · rename_i hg
      cases hstep
      simp only [Bool.and_eq_true] at hg
      have hrem : f.remaining = [] := List.isEmpty_iff.mp hg.1
      have hdec : f.decided = none := Option.isNone_iff_eq_none.mp hg.2
      obtain ⟨sA, hrun, hnext, hkeys, -, hflight⟩ := hrel
      obtain ⟨hfresh, hpre, hrcore, hcorrPre, owedRest, sPost, howed, howedOk, hrunPost,
        hcorrPost⟩ := hflight f hfan
      subst howed
      have hnotSched : ∀ id, ¬ Scheduled f id := by
        rintro id (hm | ⟨b, hb⟩)
        · rw [hrem] at hm; cases hm
        · rw [hdec] at hb; cases hb
      have hrunAll : runLabels initialSub (labels ++ (owedOp f.kind :: owedRest)) = some sPost :=
        (runLabels_append labels _ hrun).trans hrunPost
      -- the owed operation lands on the runtime core
      rw [runLabels_cons] at hrunPost
      cases hap : apply sA (owedOp f.kind) with
      | none => rw [hap] at hrunPost; cases hrunPost
      | some sA₁ =>
        rw [hap] at hrunPost
        have hcore₁ : sA₁.core = s.core := by
          cases hk : f.kind with
          | publish stream m el =>
            rw [hk] at hap
            obtain ⟨core'', hst'', hs₁⟩ := applyOp_ok_eq (deliver := deliverOne)
              (show applyOp deliverOne sA
                (.publish stream m.subject m.payload m.headers el m.timestampMillis)
                (.ok (.sequence m.sequence)) = some sA₁ from hap)
            have := hrcore.1 stream m el hk
            rw [hst''] at this
            injection this with hthis
            injection hthis with hcc _
            rw [hs₁]
            exact hcc
          | delete name =>
            rw [hk] at hap
            obtain ⟨core'', hst'', hs₁⟩ := applyOp_ok_eq (deliver := deliverOne)
              (show applyOp deliverOne sA (.deleteStream name) (.ok .unit) = some sA₁ from hap)
            have := hrcore.2 name hk
            rw [hst''] at this
            injection this with hthis
            injection hthis with hcc _
            rw [hs₁]
            exact hcc
        obtain ⟨hcoreP, hnextP, hkeysP⟩ :=
          runLabels_consumer_frame owedRest (consumerOnly_owedRest howedOk) hrunPost
        obtain ⟨hnextAll, hkeysAll⟩ :=
          runLabels_noRegister_frame (owedOp f.kind :: owedRest) (noRegister_owed howedOk)
            (by rw [runLabels_cons, hap]; exact hrunPost)
        refine ⟨labels ++ (owedOp f.kind :: owedRest), [],
          ⟨sPost, hrunAll, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hnextAll, hnext]
        · rw [hkeysAll, hkeys]
        · intro _
          refine ⟨rfl, by rw [hcoreP, hcore₁], ?_⟩
          intro id r₀ hlkr
          cases hpp : pointPassed f id with
          | true =>
            obtain ⟨a, hlka, hca⟩ := hcorrPost id r₀ hlkr hpp
            rw [pendingOf_eq, pendingFail_of_decided_none hdec] at hca
            exact ⟨a, hlka, hca⟩
          | false =>
            obtain ⟨a, hlka, hca⟩ := hcorrPre id r₀ hlkr hpp
            obtain ⟨hpub, hdel⟩ := owed_lookup (f := f) (by rw [runLabels_cons, hap]; exact hrunPost)
              howedOk hpp hlka
            refine ⟨a, ?_, hca⟩
            have htgt : isTargetOf f.kind a = false := by
              rcases (hpre id a hlka hpp).1 with hs | ht
              · exact absurd hs (hnotSched id)
              · exact ht
            cases hk : f.kind with
            | publish stream m el =>
              rw [hpub stream m el hk]
              rw [hk] at htgt
              rw [deliverOne_skip htgt]
            | delete name =>
              rw [hdel name hk]
              rw [hk] at htgt
              rw [endOne_skip htgt]
        · intro g hg'
          cases hg'
        · intro id hsome
          refine ⟨fun _ => ?_, fun g hg' => by cases hg'⟩
          obtain ⟨-, hf⟩ := hhist id hsome
          obtain ⟨hpass, hnpass⟩ := hf f hfan
          cases hpp : pointPassed f id with
          | true => exact hpass hpp
          | false =>
            rw [abstractHistory_append id labels (owedOp f.kind :: owedRest) hrun (hnpass hpp)]
            exact abstractHistoryFrom_frame id (owedOp f.kind :: owedRest)
              (owed_hist_frame howedOk hpp) (by rw [runLabels_cons, hap]; exact hrunPost)
        · rw [labelSerial_append]
          simp [labelSerial]
        · intro _ hnl hno
          exact ⟨noUnsub_append hnl hno, fun l hl => by cases hl⟩
    · cases hstep


theorem pointPassed_of_decided_none {f : FanOut} (hdec : f.decided = none) (j : SubId) :
    pointPassed f j = f.visited.any (fun p => p.1 == j) := by
  unfold pointPassed
  rw [hdec]
  simp

theorem pointPassed_check_admit {f : FanOut} {i : SubId} {rest : List SubId}
    (hdec : f.decided = none) (j : SubId) :
    pointPassed { f with remaining := rest, decided := some (i, false) } j = pointPassed f j := by
  unfold pointPassed
  rw [hdec]
  simp

theorem pointPassed_check_overflow_self {f : FanOut} {i : SubId} {rest : List SubId} :
    pointPassed { f with remaining := rest, decided := some (i, true) } i = true := by
  unfold pointPassed
  simp

theorem pointPassed_check_overflow_ne {f : FanOut} {i : SubId} {rest : List SubId}
    (hdec : f.decided = none) {j : SubId} (hji : j ≠ i) :
    pointPassed { f with remaining := rest, decided := some (i, true) } j = pointPassed f j := by
  unfold pointPassed
  rw [hdec]
  have : ¬ (i = j) := fun h => hji h.symm
  simp [this]


theorem rel_step_check {s s' : RtState} {id : SubId} (hinv : RtInv s)
    (hstep : rtCheck s id = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] (.check id) := by
  unfold rtCheck at hstep
  cases hfan : s.fanOut with
  | none => simp only [hfan] at hstep; simp at hstep
  | some f =>
    simp only [hfan] at hstep
    cases hk : f.kind with
    | delete name => simp only [hk] at hstep; simp at hstep
    | publish stream m el =>
      cases hdec : f.decided with
      | some p => simp only [hk, hdec] at hstep; simp at hstep
      | none =>
        cases hrem : f.remaining with
        | nil => simp only [hk, hdec, hrem] at hstep; simp at hstep
        | cons i rest =>
          simp only [hk, hdec, hrem] at hstep
          split at hstep
          · simp at hstep
          · rename_i hii
            have hii' : i = id := Classical.byContradiction hii
            subst hii'
            cases hlk : lookupRt s.subs i with
            | none => simp only [hlk] at hstep; simp at hstep
            | some r =>
              simp only [hlk] at hstep
              obtain ⟨n, hn⟩ : ∃ n, r.policy = .terminateOnLag n := by
                cases hp : r.policy with
                | terminateOnLag n => exact ⟨n, rfl⟩
              simp only [hn] at hstep
              cases hstep
              rw [← hk]
              obtain ⟨sA, hrun, hnext, hkeys, -, hflight⟩ := hrel
              obtain ⟨hfresh, hpre, hrcore, hcorrPre, owedRest, sPost, howed, howedOk, hrunPost,
                hcorrPost⟩ := hflight f hfan
              subst howed
              have hsub := rtSubInv_of_lookup hinv hlk
              have hro : r.registered = true → r.queue.status = .opened :=
                fun hb => (hsub.registeredOpen hb).1
              have hnpi : pointPassed f i = false := by
                rw [pointPassed_of_decided_none hdec]
                exact hfresh i (Or.inl (by rw [hrem]; exact List.Mem.head _))
              have hschedNew : ∀ j, Scheduled f j ↔ (j ∈ rest ∨ j = i) := by
                intro j
                constructor
                · rintro (hm | ⟨b, hb⟩)
                  · rw [hrem] at hm
                    rcases List.mem_cons.mp hm with he | hm'
                    · exact Or.inr he
                    · exact Or.inl hm'
                  · rw [hdec] at hb; cases hb
                · rintro (hm | he)
                  · exact Or.inl (by rw [hrem]; exact List.Mem.tail _ hm)
                  · exact Or.inl (by rw [hrem, he]; exact List.Mem.head _)
              have hserial : labelSerial labels ++ labelSerial (owedOp f.kind :: owedRest)
                  = labelSerial labels ++ labelSerial (owedOp f.kind :: owedRest) ++ [] := by
                rw [List.append_nil]
              by_cases hovf : n ≤ r.queue.size
              · -- overflow: `i` passes its point here
                rw [decide_eq_true hovf]
                have hppSelf := pointPassed_check_overflow_self (f := f) (i := i) (rest := rest)
                have hppNe := fun {j : SubId} (hji : j ≠ i) =>
                  pointPassed_check_overflow_ne (f := f) (i := i) (rest := rest) hdec hji
                obtain ⟨aPre, hlkaPre, hcaPre⟩ := hcorrPre i r hlk hnpi
                have htgt : aPre.status = .shutDown ∨ isTargetOf f.kind aPre = true :=
                  (hpre i aPre hlkaPre hnpi).2 (Or.inl (by rw [hrem]; exact List.Mem.head _))
                rw [hk] at htgt
                obtain ⟨hpub, -⟩ := owed_lookup (f := f) hrunPost howedOk hnpi hlkaPre
                have hlkPost : lookupSub sPost.subs i = some (deliverOne stream m aPre) :=
                  hpub stream m el hk
                have hcorrNew : corrSub (rtFail (.consumerLagged stream r.lastEnqueued) r)
                    (deliverOne stream m aPre) := overflow_corr hn hro htgt hovf hcaPre
                refine ⟨labels, owedOp f.kind :: owedRest,
                  ⟨sA, hrun, hnext, hkeys, (fun hq => by cases hq), ?_⟩, ?_, hserial,
                  fun _ hnl hno => ⟨hnl, hno⟩⟩
                · intro g hg
                  have hg2 : some { f with remaining := rest, decided := some (i, true) }
                    = some g := hg
                  obtain rfl : { f with remaining := rest, decided := some (i, true) } = g :=
                    Option.some.inj hg2
                  refine ⟨?_, ?_, ?_, ?_, owedRest, sPost, rfl, ?_, hrunPost, ?_⟩
                  · intro j hs
                    rcases hs with hm | ⟨b, hb⟩
                    · exact hfresh j (Or.inl (by rw [hrem]; exact List.Mem.tail _ hm))
                    · injection hb with hb2
                      injection hb2 with hij _
                      rw [← hij]
                      exact hfresh i (Or.inl (by rw [hrem]; exact List.Mem.head _))
                  · intro j a hlka hnp
                    have hji : j ≠ i := by
                      intro he
                      rw [he, hppSelf] at hnp
                      exact Bool.noConfusion hnp
                    rw [hppNe hji] at hnp
                    obtain ⟨h1, h2⟩ := hpre j a hlka hnp
                    constructor
                    · rcases h1 with hs | ht
                      · refine Or.inl (Or.inl ?_)
                        rcases (hschedNew j).mp hs with hm | he
                        · exact hm
                        · exact absurd he hji
                      · exact Or.inr ht
                    · intro hs
                      refine h2 ((hschedNew j).mpr ?_)
                      rcases hs with hm | ⟨b, hb⟩
                      · exact Or.inl hm
                      · injection hb with hb2
                        injection hb2 with hij _
                        exact Or.inr hij.symm
                  · exact hrcore
                  · intro j r0 hlkr hnp
                    have hji : j ≠ i := by
                      intro he
                      rw [he, hppSelf] at hnp
                      exact Bool.noConfusion hnp
                    rw [hppNe hji] at hnp
                    exact hcorrPre j r0 hlkr hnp
                  · intro l hl
                    obtain ⟨j, hj, hpj⟩ := howedOk l hl
                    refine ⟨j, hj, ?_⟩
                    by_cases hji : j = i
                    · subst hji
                      exact hppSelf
                    · rw [hppNe hji]
                      exact hpj
                  · intro j r0 hlkr hp
                    by_cases hji : j = i
                    · refine ⟨deliverOne stream m aPre, by rw [hji]; exact hlkPost, ?_⟩
                      have hr0 : r0 = r := by
                        rw [hji] at hlkr
                        exact Option.some.inj (hlkr.symm.trans hlk)
                      rw [hr0, hji]
                      show corrSub (failOpt (pendingFail
                        { f with remaining := rest, decided := some (i, true) } i r) r) _
                      have hpf : pendingFail
                          { f with remaining := rest, decided := some (i, true) } i r
                          = some (.consumerLagged stream r.lastEnqueued) := by
                        unfold pendingFail
                        simp [hk]
                      rw [hpf]
                      exact hcorrNew
                    · rw [hppNe hji] at hp
                      obtain ⟨a, hlka, hca⟩ := hcorrPost j r0 hlkr hp
                      refine ⟨a, hlka, ?_⟩
                      rw [pendingOf_eq, pendingFail_of_decided_none hdec] at hca
                      show corrSub (failOpt (pendingFail
                        { f with remaining := rest, decided := some (i, true) } j r0) r0) a
                      have hij2 : ¬ (i = j) := fun h => hji h.symm
                      have hpf : pendingFail
                          { f with remaining := rest, decided := some (i, true) } j r0 = none := by
                        unfold pendingFail
                        simp [hk, hij2]
                      rw [hpf]
                      exact hca
                · intro j hsome
                  refine ⟨(fun hq => by cases hq), fun g hg => ?_⟩
                  have hg2 : some { f with remaining := rest, decided := some (i, true) }
                    = some g := hg
                  obtain rfl : { f with remaining := rest, decided := some (i, true) } = g :=
                    Option.some.inj hg2
                  obtain ⟨-, hf⟩ := hhist j hsome
                  obtain ⟨hpass, hnpass⟩ := hf f hfan
                  by_cases hji : j = i
                  · subst hji
                    refine ⟨fun _ => ?_, fun hnp => by rw [hppSelf] at hnp; exact Bool.noConfusion hnp⟩
                    rw [abstractHistory_append j labels (owedOp f.kind :: owedRest) hrun
                      (hnpass hnpi)]
                    exact abstractHistoryFrom_frame j (owedOp f.kind :: owedRest)
                      (owed_hist_frame howedOk hnpi) hrunPost
                  · rw [hppNe hji]
                    exact ⟨hpass, hnpass⟩
              · -- admit: nothing passes its point
                rw [decide_eq_false hovf]
                have hpp := pointPassed_check_admit (f := f) (i := i) (rest := rest) hdec
                refine ⟨labels, owedOp f.kind :: owedRest,
                  ⟨sA, hrun, hnext, hkeys, (fun hq => by cases hq), ?_⟩, ?_, hserial,
                  fun _ hnl hno => ⟨hnl, hno⟩⟩
                · intro g hg
                  have hg2 : some { f with remaining := rest, decided := some (i, false) }
                    = some g := hg
                  obtain rfl : { f with remaining := rest, decided := some (i, false) } = g :=
                    Option.some.inj hg2
                  refine ⟨?_, ?_, hrcore, ?_, owedRest, sPost, rfl, ?_, hrunPost, ?_⟩
                  · intro j hs
                    rcases hs with hm | ⟨b, hb⟩
                    · exact hfresh j (Or.inl (by rw [hrem]; exact List.Mem.tail _ hm))
                    · injection hb with hb2
                      injection hb2 with hij _
                      rw [← hij]
                      exact hfresh i (Or.inl (by rw [hrem]; exact List.Mem.head _))
                  · intro j a hlka hnp
                    rw [hpp j] at hnp
                    obtain ⟨h1, h2⟩ := hpre j a hlka hnp
                    constructor
                    · rcases h1 with hs | ht
                      · rcases (hschedNew j).mp hs with hm | he
                        · exact Or.inl (Or.inl hm)
                        · exact Or.inl (Or.inr ⟨false, by rw [he]⟩)
                      · exact Or.inr ht
                    · intro hs
                      refine h2 ((hschedNew j).mpr ?_)
                      rcases hs with hm | ⟨b, hb⟩
                      · exact Or.inl hm
                      · injection hb with hb2
                        injection hb2 with hij _
                        exact Or.inr hij.symm
                  · intro j r0 hlkr hnp
                    rw [hpp j] at hnp
                    exact hcorrPre j r0 hlkr hnp
                  · intro l hl
                    obtain ⟨j, hj, hpj⟩ := howedOk l hl
                    exact ⟨j, hj, by rw [hpp j]; exact hpj⟩
                  · intro j r0 hlkr hp
                    rw [hpp j] at hp
                    obtain ⟨a, hlka, hca⟩ := hcorrPost j r0 hlkr hp
                    refine ⟨a, hlka, ?_⟩
                    rw [pendingOf_eq, pendingFail_of_decided_none hdec] at hca
                    show corrSub (failOpt (pendingFail
                      { f with remaining := rest, decided := some (i, false) } j r0) r0) a
                    have hpf : pendingFail
                        { f with remaining := rest, decided := some (i, false) } j r0 = none := by
                      unfold pendingFail
                      simp [hk]
                    rw [hpf]
                    exact hca
                · intro j hsome
                  refine ⟨(fun hq => by cases hq), fun g hg => ?_⟩
                  have hg2 : some { f with remaining := rest, decided := some (i, false) }
                    = some g := hg
                  obtain rfl : { f with remaining := rest, decided := some (i, false) } = g :=
                    Option.some.inj hg2
                  obtain ⟨-, hf⟩ := hhist j hsome
                  rw [hpp j]
                  exact hf f hfan


theorem pointPassed_visit {f : FanOut} {i : SubId} {o : Outcome} {rem : List SubId}
    (hppOld : ∀ j, pointPassed f j = f.visited.any (fun p => p.1 == j)) (j : SubId) :
    pointPassed { f with
        remaining := rem, decided := none, visited := f.visited ++ [(i, o)] } j
      = (pointPassed f j || (i == j)) := by
  rw [hppOld j]
  unfold pointPassed
  simp

theorem pointPassed_resolve_keep {f : FanOut} {i : SubId} {o : Outcome}
    (hdec : f.decided = some (i, true)) (j : SubId) :
    pointPassed { f with decided := none, visited := f.visited ++ [(i, o)] } j
      = pointPassed f j := by
  have hb : ((some (i, true) : Option (SubId × Bool)) == some (j, true)) = (i == j) := by
    show (i == j && (true == true)) = _
    simp
  unfold pointPassed
  rw [hdec, hb]
  simp

/-- A `resolve` that makes its subscriber pass its point. -/
theorem rel_resolve_visit {s s' : RtState} {f f' : FanOut} {i : SubId} {r r' : RtSubscriber}
    {o : Outcome} {rem : List SubId} {labels owed : List Label} {l : RtLabel}
    (hfan : s.fanOut = some f)
    (hf' : f' = { f with
        remaining := rem, decided := none, visited := f.visited ++ [(i, o)] })
    (hppOld : ∀ j, pointPassed f j = f.visited.any (fun p => p.1 == j))
    (hpendOld : ∀ j (r₀ : RtSubscriber), pendingOf f j r₀ = r₀)
    (hlk : lookupRt s.subs i = some r)
    (hupd : s' = { s with subs := updateRt s.subs i (fun _ => r'), fanOut := some f' })
    (hchunks : r'.chunks = r.chunks)
    (hnpi : pointPassed f i = false)
    (hsched : Scheduled f i)
    (hremSub : ∀ j, j ∈ rem → Scheduled f j ∧ j ≠ i)
    (hschedNew : ∀ j, j ≠ i → Scheduled f j → j ∈ rem)
    (hcrux : ∀ (sA sPost : SubState) (owedRest : List Label) (aPre : Subscriber),
        lookupSub sA.subs i = some aPre → corrSub r aPre →
        (aPre.status = .shutDown ∨ isTargetOf f.kind aPre = true) →
        runLabels sA (owedOp f.kind :: owedRest) = some sPost → OwedOk f owedRest →
        ∃ a, lookupSub sPost.subs i = some a ∧ corrSub r' a)
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] l := by
  obtain ⟨sA, hrun, hnext, hkeys, -, hflight⟩ := hrel
  obtain ⟨hfresh, hpre, hrcore, hcorrPre, owedRest, sPost, howed, howedOk, hrunPost,
    hcorrPost⟩ := hflight f hfan
  subst howed
  have hkind : f'.kind = f.kind := by rw [hf']
  have hrem' : f'.remaining = rem := by rw [hf']
  have hdec' : f'.decided = none := by rw [hf']
  have hvis' : f'.visited = f.visited ++ [(i, o)] := by rw [hf']
  have hpp : ∀ j, pointPassed f' j = (pointPassed f j || (i == j)) := by
    rw [hf']; exact pointPassed_visit hppOld
  have hppSelf : pointPassed f' i = true := by rw [hpp i]; simp
  have hppNe : ∀ {j}, j ≠ i → pointPassed f' j = pointPassed f j := by
    intro j hji
    rw [hpp j]
    have hij : ¬ (i = j) := fun h => hji h.symm
    simp [hij]
  have hlk' : lookupRt s'.subs i = some r' := by rw [hupd]; exact lookupRt_update_self hlk
  have hlkne : ∀ j, j ≠ i → lookupRt s'.subs j = lookupRt s.subs j := by
    intro j hj
    rw [hupd]
    exact lookupRt_updateRt_ne s.subs j i (fun _ => r') hj
  have hkeys' : s'.subs.map Prod.fst = s.subs.map Prod.fst := by
    rw [hupd]; exact updateRt_keys s.subs i (fun _ => r')
  have hnext' : s'.nextId = s.nextId := by rw [hupd]
  have hcore' : s'.core = s.core := by rw [hupd]
  have hfan' : s'.fanOut = some f' := by rw [hupd]
  have hhistEq : ∀ j, rtHistory s' j = rtHistory s j := by
    intro j
    by_cases hji : j = i
    · rw [hji, rtHistory_eq hlk', rtHistory_eq hlk, hchunks]
    · unfold rtHistory
      rw [hlkne j hji]
  have hisSome : ∀ j, (lookupRt s'.subs j).isSome = true → (lookupRt s.subs j).isSome = true := by
    intro j hs
    by_cases hji : j = i
    · rw [hji, hlk]; rfl
    · rw [← hlkne j hji]; exact hs
  obtain ⟨aPre, hlkaPre, hcaPre⟩ := hcorrPre i r hlk hnpi
  have htgt : aPre.status = .shutDown ∨ isTargetOf f.kind aPre = true :=
    (hpre i aPre hlkaPre hnpi).2 hsched
  obtain ⟨aPost, hlkPost, hcorrNew⟩ :=
    hcrux sA sPost owedRest aPre hlkaPre hcaPre htgt hrunPost howedOk
  refine ⟨labels, owedOp f.kind :: owedRest,
    ⟨sA, hrun, by rw [hnext, hnext'], by rw [hkeys, hkeys'], ?_, ?_⟩, ?_, by rw [List.append_nil],
    fun _ hnl hno => ⟨hnl, hno⟩⟩
  · intro hq
    rw [hfan'] at hq
    cases hq
  · intro g hg
    rw [hfan'] at hg
    obtain rfl : f' = g := Option.some.inj hg
    refine ⟨?_, ?_, ?_, ?_, owedRest, sPost, by rw [hkind], ?_, hrunPost, ?_⟩
    · intro j hs
      have hjrem : j ∈ rem := by
        rcases hs with hm | ⟨b, hb⟩
        · rw [hrem'] at hm; exact hm
        · rw [hdec'] at hb; cases hb
      obtain ⟨hsj, hji⟩ := hremSub j hjrem
      have hij : ¬ (i = j) := fun h => hji h.symm
      rw [hvis']
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      rw [hfresh j hsj]
      simp [hij]
    · intro j a hlka hnp
      have hji : j ≠ i := by
        intro he
        rw [he, hppSelf] at hnp
        exact Bool.noConfusion hnp
      rw [hppNe hji] at hnp
      obtain ⟨h1, h2⟩ := hpre j a hlka hnp
      rw [hkind]
      refine ⟨?_, ?_⟩
      · rcases h1 with hs | ht
        · exact Or.inl (Or.inl (by rw [hrem']; exact hschedNew j hji hs))
        · exact Or.inr ht
      · intro hs
        refine h2 ?_
        rcases hs with hm | ⟨b, hb⟩
        · rw [hrem'] at hm
          exact (hremSub j hm).1
        · rw [hdec'] at hb; cases hb
    · refine ⟨fun stream m el hkk => ?_, fun name hkk => ?_⟩
      · rw [hcore']
        exact hrcore.1 stream m el (by rw [← hkind]; exact hkk)
      · rw [hcore']
        exact hrcore.2 name (by rw [← hkind]; exact hkk)
    · intro j r₀ hlkr hnp
      have hji : j ≠ i := by
        intro he
        rw [he, hppSelf] at hnp
        exact Bool.noConfusion hnp
      rw [hppNe hji] at hnp
      rw [hlkne j hji] at hlkr
      exact hcorrPre j r₀ hlkr hnp
    · intro lb hlb
      obtain ⟨j, hj, hpj⟩ := howedOk lb hlb
      refine ⟨j, hj, ?_⟩
      by_cases hji : j = i
      · rw [hji]; exact hppSelf
      · rw [hppNe hji]; exact hpj
    · intro j r₀ hlkr hp
      by_cases hji : j = i
      · rw [hji] at hlkr
        rw [hlk'] at hlkr
        cases hlkr
        refine ⟨aPost, by rw [hji]; exact hlkPost, ?_⟩
        rw [hji, pendingOf_of_decided_none hdec']
        exact hcorrNew
      · rw [hppNe hji] at hp
        rw [hlkne j hji] at hlkr
        obtain ⟨a, hlka, hca⟩ := hcorrPost j r₀ hlkr hp
        refine ⟨a, hlka, ?_⟩
        rw [pendingOf_of_decided_none hdec']
        rw [hpendOld j r₀] at hca
        exact hca
  · intro j hsome
    refine ⟨(fun hq => by rw [hfan'] at hq; cases hq), fun g hg => ?_⟩
    rw [hfan'] at hg
    obtain rfl : f' = g := Option.some.inj hg
    obtain ⟨-, hf⟩ := hhist j (hisSome j hsome)
    obtain ⟨hpass, hnpass⟩ := hf f hfan
    rw [hhistEq j]
    by_cases hji : j = i
    · refine ⟨fun _ => ?_, fun hnp => by rw [hji, hppSelf] at hnp; exact Bool.noConfusion hnp⟩
      have hnpj : pointPassed f j = false := by rw [hji]; exact hnpi
      rw [abstractHistory_append j labels (owedOp f.kind :: owedRest) hrun (hnpass hnpj)]
      exact abstractHistoryFrom_frame j (owedOp f.kind :: owedRest)
        (owed_hist_frame howedOk hnpj) hrunPost
    · rw [hppNe hji]
      exact ⟨hpass, hnpass⟩


theorem pointPassed_decided_false {f : FanOut} {i : SubId} (hdec : f.decided = some (i, false))
    (j : SubId) : pointPassed f j = f.visited.any (fun p => p.1 == j) := by
  have hb : ((some (i, false) : Option (SubId × Bool)) == some (j, true)) = false := by
    show (i == j && (false == true)) = _
    simp
  unfold pointPassed
  rw [hdec, hb]
  simp

theorem pendingOf_of_decided_false {f : FanOut} {i : SubId} (hdec : f.decided = some (i, false))
    (j : SubId) (r₀ : RtSubscriber) : pendingOf f j r₀ = r₀ := by
  rw [pendingOf_eq]
  have hpf : pendingFail f j r₀ = none := by
    unfold pendingFail
    rw [hdec]
    cases f.kind <;> rfl
  rw [hpf]
  rfl

theorem pendingOf_of_delete {f : FanOut} {name : StreamName} (hk : f.kind = .delete name)
    (j : SubId) (r₀ : RtSubscriber) : pendingOf f j r₀ = r₀ := by
  rw [pendingOf_eq]
  have hpf : pendingFail f j r₀ = none := by
    unfold pendingFail
    rw [hk]
  rw [hpf]
  rfl

/-- A `resolve` that performs the failure a `check` had already decided: the abstract side has
already seen it, so the correspondence is re-established by definition. -/
theorem rel_resolve_keep {s s' : RtState} {f f' : FanOut} {i : SubId} {r r' : RtSubscriber}
    {o : Outcome} {labels owed : List Label} {l : RtLabel}
    (hinv : RtInv s)
    (hfan : s.fanOut = some f)
    (hf' : f' = { f with decided := none, visited := f.visited ++ [(i, o)] })
    (hdec : f.decided = some (i, true))
    (hlk : lookupRt s.subs i = some r)
    (hupd : s' = { s with subs := updateRt s.subs i (fun _ => r'), fanOut := some f' })
    (hchunks : r'.chunks = r.chunks)
    (hr' : pendingOf f i r = r')
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] l := by
  obtain ⟨sA, hrun, hnext, hkeys, -, hflight⟩ := hrel
  obtain ⟨hfresh, hpre, hrcore, hcorrPre, owedRest, sPost, howed, howedOk, hrunPost,
    hcorrPost⟩ := hflight f hfan
  subst howed
  have hfinv := hinv.fanOut f hfan
  have hiNotRem : i ∉ f.remaining := hfinv.decidedNotRemaining i true hdec
  have hkind : f'.kind = f.kind := by rw [hf']
  have hrem' : f'.remaining = f.remaining := by rw [hf']
  have hdec' : f'.decided = none := by rw [hf']
  have hvis' : f'.visited = f.visited ++ [(i, o)] := by rw [hf']
  have hpp : ∀ j, pointPassed f' j = pointPassed f j := by
    rw [hf']; exact pointPassed_resolve_keep hdec
  have hppSelf : pointPassed f i = true := by
    unfold pointPassed
    rw [hdec]
    have hb : ((some (i, true) : Option (SubId × Bool)) == some (i, true)) = true := by
      show (i == i && (true == true)) = _
      simp
    rw [hb]
    simp
  have hlk' : lookupRt s'.subs i = some r' := by rw [hupd]; exact lookupRt_update_self hlk
  have hlkne : ∀ j, j ≠ i → lookupRt s'.subs j = lookupRt s.subs j := by
    intro j hj
    rw [hupd]
    exact lookupRt_updateRt_ne s.subs j i (fun _ => r') hj
  have hkeys' : s'.subs.map Prod.fst = s.subs.map Prod.fst := by
    rw [hupd]; exact updateRt_keys s.subs i (fun _ => r')
  have hnext' : s'.nextId = s.nextId := by rw [hupd]
  have hcore' : s'.core = s.core := by rw [hupd]
  have hfan' : s'.fanOut = some f' := by rw [hupd]
  have hhistEq : ∀ j, rtHistory s' j = rtHistory s j := by
    intro j
    by_cases hji : j = i
    · rw [hji, rtHistory_eq hlk', rtHistory_eq hlk, hchunks]
    · unfold rtHistory
      rw [hlkne j hji]
  have hisSome : ∀ j, (lookupRt s'.subs j).isSome = true → (lookupRt s.subs j).isSome = true := by
    intro j hs
    by_cases hji : j = i
    · rw [hji, hlk]; rfl
    · rw [← hlkne j hji]; exact hs
  refine ⟨labels, owedOp f.kind :: owedRest,
    ⟨sA, hrun, by rw [hnext, hnext'], by rw [hkeys, hkeys'], ?_, ?_⟩, ?_, by rw [List.append_nil],
    fun _ hnl hno => ⟨hnl, hno⟩⟩
  · intro hq
    rw [hfan'] at hq
    cases hq
  · intro g hg
    rw [hfan'] at hg
    obtain rfl : f' = g := Option.some.inj hg
    refine ⟨?_, ?_, ?_, ?_, owedRest, sPost, by rw [hkind], ?_, hrunPost, ?_⟩
    · intro j hs
      have hjrem : j ∈ f.remaining := by
        rcases hs with hm | ⟨b, hb⟩
        · rw [hrem'] at hm; exact hm
        · rw [hdec'] at hb; cases hb
      have hji : j ≠ i := fun he => hiNotRem (he ▸ hjrem)
      have hij : ¬ (i = j) := fun h => hji h.symm
      rw [hvis']
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      rw [hfresh j (Or.inl hjrem)]
      simp [hij]
    · intro j a hlka hnp
      rw [hpp j] at hnp
      have hji : j ≠ i := by
        intro he
        rw [he, hppSelf] at hnp
        exact Bool.noConfusion hnp
      obtain ⟨h1, h2⟩ := hpre j a hlka hnp
      rw [hkind]
      refine ⟨?_, ?_⟩
      · rcases h1 with hs | ht
        · refine Or.inl (Or.inl ?_)
          rw [hrem']
          rcases hs with hm | ⟨b, hb⟩
          · exact hm
          · rw [hdec] at hb
            injection hb with hb2
            injection hb2 with hij2 _
            exact absurd hij2.symm hji
        · exact Or.inr ht
      · intro hs
        refine h2 ?_
        rcases hs with hm | ⟨b, hb⟩
        · rw [hrem'] at hm; exact Or.inl hm
        · rw [hdec'] at hb; cases hb
    · refine ⟨fun stream m el hkk => ?_, fun name hkk => ?_⟩
      · rw [hcore']
        exact hrcore.1 stream m el (by rw [← hkind]; exact hkk)
      · rw [hcore']
        exact hrcore.2 name (by rw [← hkind]; exact hkk)
    · intro j r₀ hlkr hnp
      rw [hpp j] at hnp
      have hji : j ≠ i := by
        intro he
        rw [he, hppSelf] at hnp
        exact Bool.noConfusion hnp
      rw [hlkne j hji] at hlkr
      exact hcorrPre j r₀ hlkr hnp
    · intro lb hlb
      obtain ⟨j, hj, hpj⟩ := howedOk lb hlb
      exact ⟨j, hj, by rw [hpp j]; exact hpj⟩
    · intro j r₀ hlkr hp
      rw [hpp j] at hp
      by_cases hji : j = i
      · rw [hji] at hlkr
        rw [hlk'] at hlkr
        cases hlkr
        obtain ⟨a, hlka, hca⟩ := hcorrPost i r hlk (by rw [← hji]; exact hp)
        refine ⟨a, by rw [hji]; exact hlka, ?_⟩
        rw [hji, pendingOf_of_decided_none hdec', ← hr']
        exact hca
      · rw [hlkne j hji] at hlkr
        obtain ⟨a, hlka, hca⟩ := hcorrPost j r₀ hlkr hp
        refine ⟨a, hlka, ?_⟩
        rw [pendingOf_of_decided_none hdec']
        have hpo : pendingOf f j r₀ = r₀ := by
          rw [pendingOf_eq]
          have hpf : pendingFail f j r₀ = none := by
            unfold pendingFail
            rw [hdec]
            cases f.kind with
            | delete _ => rfl
            | publish _ _ _ =>
              have hij : ¬ (i = j) := fun h => hji h.symm
              simp [hij]
          rw [hpf]
          rfl
        rw [hpo] at hca
        exact hca
  · intro j hsome
    refine ⟨(fun hq => by rw [hfan'] at hq; cases hq), fun g hg => ?_⟩
    rw [hfan'] at hg
    obtain rfl : f' = g := Option.some.inj hg
    obtain ⟨-, hf⟩ := hhist j (hisSome j hsome)
    rw [hhistEq j, hpp j]
    exact hf f hfan


theorem rel_step_resolve {s s' : RtState} {id : SubId} (hinv : RtInv s)
    (hstep : rtResolve s id = some s') {labels owed : List Label}
    (hrel : Rel s labels owed) (hhist : RelHist s labels owed) :
    RelStep s' labels owed [] (.resolve id) := by
  unfold rtResolve at hstep
  cases hfan : s.fanOut with
  | none => simp only [hfan] at hstep; simp at hstep
  | some f =>
    simp only [hfan] at hstep
    have hfinv := hinv.fanOut f hfan
    cases hk : f.kind with
    | publish stream m el =>
      simp only [hk] at hstep
      cases hdec : f.decided with
      | none => simp only [hdec] at hstep; simp at hstep
      | some p =>
        obtain ⟨i, ovf⟩ := p
        simp only [hdec] at hstep
        split at hstep
        · simp at hstep
        · rename_i hii
          have hii2 : i = id := Classical.byContradiction hii
          subst hii2
          cases hlk : lookupRt s.subs i with
          | none => simp only [hlk] at hstep; simp at hstep
          | some r =>
            simp only [hlk] at hstep
            have hsub := rtSubInv_of_lookup hinv hlk
            have hro : r.registered = true → r.queue.status = .opened :=
              fun hb => (hsub.registeredOpen hb).1
            cases ovf with
            | true =>
              simp only [if_true] at hstep
              cases hstep
              rw [← hk]
              have hr2 : pendingOf f i r = { r with
                  registered := false,
                  queue := r.queue.fail (.consumerLagged stream r.lastEnqueued) } := by
                rw [pendingOf_eq]
                have hpf : pendingFail f i r
                    = some (.consumerLagged stream r.lastEnqueued) := by
                  unfold pendingFail
                  rw [hk, hdec]
                  simp
                rw [hpf]
                rfl
              exact rel_resolve_keep (o := .overflowed) hinv hfan rfl hdec hlk rfl rfl hr2
                hrel hhist
            | false =>
              have hfreshF : FanFresh f := by
                obtain ⟨sA0, -, -, -, -, hfl0⟩ := hrel
                exact (hfl0 f hfan).1
              have hnpi : pointPassed f i = false := by
                rw [pointPassed_decided_false hdec]
                exact hfreshF i (Or.inr ⟨false, hdec⟩)
              have hroom : r.queue.buffer.length < r.policy.capacity ∨
                  r.queue.status ≠ .opened := hfinv.decidedRoom i hdec r hlk
              cases hoff : r.queue.offer r.policy.capacity m with
              | mk q' res =>
                simp only [hoff] at hstep
                have hmain : ∀ o : Outcome, RelStep { s with
                    subs := updateRt s.subs i
                      (fun _ => { r with queue := q', lastEnqueued := m.sequence }),
                    fanOut := some { f with
                      decided := none, visited := f.visited ++ [(i, o)] } }
                    labels owed [] (.resolve i) := by
                  intro o
                  refine rel_resolve_visit (f := f) (i := i) (r := r) (o := o)
                    (rem := f.remaining) hfan rfl (pointPassed_decided_false hdec)
                    (pendingOf_of_decided_false hdec) hlk rfl rfl hnpi (Or.inr ⟨false, hdec⟩)
                    ?_ ?_ ?_ hrel hhist
                  · intro j hj
                    exact ⟨Or.inl hj, fun he => (hfinv.decidedNotRemaining i false hdec)
                      (he ▸ hj)⟩
                  · intro j hji hs
                    rcases hs with hm | ⟨b, hb⟩
                    · exact hm
                    · rw [hdec] at hb
                      injection hb with hb2
                      injection hb2 with hij2 _
                      exact absurd hij2.symm hji
                  · intro sA sPost owedRest aPre hlkaPre hcaPre htgt hrunPost howedOk
                    obtain ⟨hpub, -⟩ := owed_lookup (f := f) hrunPost howedOk hnpi hlkaPre
                    exact ⟨deliverOne stream m aPre, hpub stream m el hk,
                      admit_corr hro hroom (by rw [← hk]; exact htgt) hoff hcaPre⟩
                cases res with
                | wouldSuspend => simp at hstep
                | accepted =>
                  simp only [] at hstep
                  cases hstep
                  rw [← hk]
                  exact hmain .admitted
                | refused =>
                  simp only [] at hstep
                  cases hstep
                  rw [← hk]
                  exact hmain .skipped
    | delete name =>
      simp only [hk] at hstep
      cases hdec : f.decided with
      | some p => simp only [hdec] at hstep; simp at hstep
      | none =>
        cases hrem : f.remaining with
        | nil => simp only [hdec, hrem] at hstep; simp at hstep
        | cons i rest =>
          simp only [hdec, hrem] at hstep
          split at hstep
          · simp at hstep
          · rename_i hii
            have hii2 : i = id := Classical.byContradiction hii
            subst hii2
            cases hlk : lookupRt s.subs i with
            | none => simp only [hlk] at hstep; simp at hstep
            | some r =>
              simp only [hlk] at hstep
              cases hstep
              rw [← hk]
              have hsub := rtSubInv_of_lookup hinv hlk
              have hro : r.registered = true → r.queue.status = .opened :=
                fun hb => (hsub.registeredOpen hb).1
              have hfreshF : FanFresh f := by
                obtain ⟨sA0, -, -, -, -, hfl0⟩ := hrel
                exact (hfl0 f hfan).1
              have hnpi : pointPassed f i = false := by
                rw [pointPassed_of_decided_none hdec]
                exact hfreshF i (Or.inl (by rw [hrem]; exact List.Mem.head _))
              refine rel_resolve_visit (f := f) (i := i) (r := r) (o := .ended)
                (rem := rest) hfan rfl (pointPassed_of_decided_none hdec)
                (pendingOf_of_delete hk) hlk rfl rfl hnpi
                (Or.inl (by rw [hrem]; exact List.Mem.head _)) ?_ ?_ ?_ hrel hhist
              · intro j hj
                refine ⟨Or.inl (by rw [hrem]; exact List.Mem.tail _ hj), ?_⟩
                intro he
                have hnd := hfinv.remainingNodup
                rw [hrem] at hnd
                exact (List.pairwise_cons.mp hnd).1 j hj he.symm
              · intro j hji hs
                rcases hs with hm | ⟨b, hb⟩
                · rw [hrem] at hm
                  rcases List.mem_cons.mp hm with he | hm2
                  · exact absurd he hji
                  · exact hm2
                · rw [hdec] at hb; cases hb
              · intro sA sPost owedRest aPre hlkaPre hcaPre htgt hrunPost howedOk
                obtain ⟨-, hdel⟩ := owed_lookup (f := f) hrunPost howedOk hnpi hlkaPre
                exact ⟨endOne name aPre, hdel name hk,
                  end_corr hro (by rw [← hk]; exact htgt) hcaPre⟩


end EffectNatsSubstrate
