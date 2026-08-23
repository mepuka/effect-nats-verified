import EffectNatsSubstrate.Runtime

/-!
# The runtime association-list toolkit (shared)

`lookupRt`/`updateRt` facts that every stage-B1 proof module needs. Extracted from `SimProof.lean`
(P4b) at the coordinator's consolidation of 2026-08-23, after three lanes (P2, P3, P4b) had each
proved their own copies with different statements; these are the strongest forms
(`lookupRt_updateRt_self` is the `map` equation, hypothesis-free). `RtReachable`, `RtCommute`, and
`SimProof` import this module instead of restating them.
-/

namespace EffectNatsSubstrate

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


end EffectNatsSubstrate
