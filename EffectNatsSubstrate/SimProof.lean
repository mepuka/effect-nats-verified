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

end EffectNatsSubstrate
