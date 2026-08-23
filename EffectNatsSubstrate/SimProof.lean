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

end EffectNatsSubstrate
