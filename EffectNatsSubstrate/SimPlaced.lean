import EffectNatsSubstrate.SimAgree
import EffectNatsSubstrate.Sim

/-!
# Placements are enumerated — stage B1, packet P5b

The enumeration half of `a4_complete` (SB5): any way of inserting subscriber
`id`'s pulls into a pull-free label list, provided every inserted pull is
enabled (`abstractHistoryFrom` returns `some`), lands in the acceptance set
`historiesFrom apply id s h L` that the exporter prints as
`freeRunning.outcomes`. Enabledness supplies the at-most-two-consecutive bound
through `pull_third_none` — a third pull of one subscriber in a row is never
enabled, so the two-pull budget `pullsAtGap` spends at each gap loses nothing.
The `hfree` side condition states the intent (`labelsWithoutPulls t id` is
pull-free for `id`); round 5 could not show it needed for truth.

`Placed` and `historiesFrom_contains` are logged verbatim in
`research/logs/p5b2_statements.lean`; every other declaration here is a
proof-side helper for P5c (`SimProof.lean`).
-/

namespace EffectNatsSubstrate

/-! ## How one gap enumerates -/

/-- A gap with fuel 0 offers exactly the continuation. -/
theorem pullsAtGap_zero_eq {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s : SubState} {h : History} {k : SubState → History → List (History × SubState)} :
    pullsAtGap applyFn id 0 s h k = k s h := rfl

/-- A gap with fuel 2 offers the continuation, then (behind the first pull) a
fuel-1 gap, then (behind a second) a fuel-0 gap. -/
theorem pullsAtGap_two_eq {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s : SubState} {h : History} {k : SubState → History → List (History × SubState)} :
    pullsAtGap applyFn id 2 s h k =
      k s h ++
        match applyFn s (.pull id) with
        | some s' => pullsAtGap applyFn id 1 s' (h ++ [appended s s' id]) k
        | none => [] := rfl

/-- A gap with fuel 1 offers the continuation, then (behind the first pull) a
fuel-0 gap. -/
theorem pullsAtGap_one_eq {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s : SubState} {h : History} {k : SubState → History → List (History × SubState)} :
    pullsAtGap applyFn id 1 s h k =
      k s h ++
        match applyFn s (.pull id) with
        | some s' => pullsAtGap applyFn id 0 s' (h ++ [appended s s' id]) k
        | none => [] := rfl

theorem pullsAtGap_two_some {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s s₁ : SubState} {h : History} {k : SubState → History → List (History × SubState)}
    (hp : applyFn s (.pull id) = some s₁) :
    pullsAtGap applyFn id 2 s h k =
      k s h ++ pullsAtGap applyFn id 1 s₁ (h ++ [appended s s₁ id]) k := by
  rw [pullsAtGap_two_eq, hp]

theorem pullsAtGap_two_none {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s : SubState} {h : History} {k : SubState → History → List (History × SubState)}
    (hp : applyFn s (.pull id) = none) :
    pullsAtGap applyFn id 2 s h k = k s h ++ ([] : List (History × SubState)) := by
  rw [pullsAtGap_two_eq, hp]

theorem pullsAtGap_one_some {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s s₁ : SubState} {h : History} {k : SubState → History → List (History × SubState)}
    (hp : applyFn s (.pull id) = some s₁) :
    pullsAtGap applyFn id 1 s h k =
      k s h ++ pullsAtGap applyFn id 0 s₁ (h ++ [appended s s₁ id]) k := by
  rw [pullsAtGap_one_eq, hp]

theorem pullsAtGap_one_none {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s : SubState} {h : History} {k : SubState → History → List (History × SubState)}
    (hp : applyFn s (.pull id) = none) :
    pullsAtGap applyFn id 1 s h k = k s h ++ ([] : List (History × SubState)) := by
  rw [pullsAtGap_one_eq, hp]

/-- One enabled pull of `id` at a gap hides nothing: whatever the continuation
offers from the pulled-to state was already offered before the pull (zero-pull
branch), or sits behind a second pull whose own continuation the one-pull offer
carries too — and a third consecutive pull is never enabled (`pull_third_none`),
so nothing is enumerated after the pull that was not enumerated before it. -/
theorem pullsAtGap_transfer {id : SubId} {s s₁ : SubState} {h h' : History}
    {k : SubState → History → List (History × SubState)} {x : History × SubState}
    (hpull : apply s (.pull id) = some s₁)
    (hh : h' = h ++ [appended s s₁ id])
    (hmem : x ∈ pullsAtGap apply id 2 s₁ h' k) :
    x ∈ pullsAtGap apply id 2 s h k := by
  rw [pullsAtGap_two_some hpull, ← hh]
  refine (List.mem_append).2 (Or.inr ?_)
  cases h₂ : apply s₁ (.pull id) with
  | none =>
    rw [pullsAtGap_two_none h₂] at hmem
    rw [pullsAtGap_one_none h₂]
    exact hmem
  | some s₂ =>
    have hdead : apply s₂ (.pull id) = none := pull_third_none hpull h₂
    rw [pullsAtGap_two_some h₂, pullsAtGap_one_none hdead] at hmem
    rw [pullsAtGap_one_some h₂, pullsAtGap_zero_eq]
    simpa using hmem

/-! ## `outcomesFrom` at a gap -/

/-- The continuation `outcomesFrom` hands to `pullsAtGap` at every gap: what
the remaining labels contribute once the gap's pulls are spent. -/
def outcomesCont (applyFn : SubState → Label → Option SubState) (id : SubId)
    (L : List Label) (s : SubState) (h : History) : List (History × SubState) :=
  match L with
  | [] => [(h, s)]
  | l :: rest =>
    match applyFn s l with
    | some s'' => outcomesFrom applyFn id s'' (afterLabel s s'' id h l) rest
    | none =>
      match l with
      | .unsubscribe i => if i = id then outcomesFrom applyFn id s h rest else []
      | _ => []

/-- `outcomesFrom` is a fuel-2 gap over its own continuation. -/
theorem outcomesFrom_eq (applyFn : SubState → Label → Option SubState) (id : SubId)
    (s : SubState) (h : History) (L : List Label) :
    outcomesFrom applyFn id s h L =
      pullsAtGap applyFn id 2 s h (outcomesCont applyFn id L) := by
  cases L <;> rfl

/-- On an enabled head label the continuation takes the running branch. -/
theorem outcomesCont_cons_some {applyFn : SubState → Label → Option SubState} {id : SubId}
    {s u : SubState} {h : History} {l : Label} {rest : List Label}
    (happ : applyFn s l = some u) :
    outcomesCont applyFn id (l :: rest) s h =
      outcomesFrom applyFn id u (afterLabel s u id h l) rest := by
  simp only [outcomesCont, happ]

/-- Everything the enumeration offers from the state after an enabled pull of
`id`, it already offered before the pull. -/
theorem outcomesFrom_pull {id : SubId} {s s₁ : SubState} {h h' : History}
    {L : List Label} {x : History × SubState}
    (hpull : apply s (.pull id) = some s₁)
    (hh : h' = h ++ [appended s s₁ id])
    (hmem : x ∈ outcomesFrom apply id s₁ h' L) :
    x ∈ outcomesFrom apply id s h L := by
  rw [outcomesFrom_eq apply id s h L]
  refine pullsAtGap_transfer hpull hh ?_
  rw [← outcomesFrom_eq apply id s₁ h' L]
  exact hmem

/-! ## The placement relation -/

/-- `P` is `L` with pulls of `id` inserted at any positions. -/
inductive Placed (id : SubId) : List Label → List Label → Prop
  | nil : Placed id [] []
  | pull {L P} : Placed id L P → Placed id L (Label.pull id :: P)
  | keep {l L P} : Placed id L P → Placed id (l :: L) (l :: P)

/-! ## Every enabled placement is enumerated -/

/-- Pair-valued strengthening of `historiesFrom_contains`: the run over `P`
lands on a full outcome pair of the enumeration over `L`. Induction on the
placement derivation; the pull case transfers across the gap by
`pullsAtGap_transfer`, the keep case recurses through the running branch of
the continuation. -/
theorem placed_outcomes {id : SubId} :
    ∀ (L P : List Label) (s : SubState) (h hist : History),
      (∀ l ∈ L, l ≠ Label.pull id) →
      Placed id L P →
      abstractHistoryFrom id s h P = some hist →
      ∃ t, (hist, t) ∈ outcomesFrom apply id s h L := by
  intro L P s h hist hfree hpl hrun
  revert hfree hrun
  revert hist
  revert h
  revert s
  induction hpl with
  | nil =>
    intro s h hist _ hrun
    have hh : h = hist := by simpa [abstractHistoryFrom] using hrun
    subst hh
    refine ⟨s, ?_⟩
    rw [outcomesFrom_eq, pullsAtGap_two_eq]
    exact (List.mem_append).2 (Or.inl (by show (h, s) ∈ [(h, s)]; exact List.Mem.head _))
  | pull pre ih =>
    intro s h hist hfree hrun
    simp only [abstractHistoryFrom] at hrun
    split at hrun
    · next s₁ hs₁ =>
      have hafter : afterLabel s s₁ id h (Label.pull id) = h ++ [appended s s₁ id] := by
        simp [afterLabel]
      rw [hafter] at hrun
      obtain ⟨t, ht⟩ := ih s₁ (h ++ [appended s s₁ id]) hist hfree hrun
      exact ⟨t, outcomesFrom_pull hs₁ rfl ht⟩
    · simp at hrun
  | keep pre ih =>
    rename_i l L₀ P₀
    intro s h hist hfree hrun
    simp only [abstractHistoryFrom] at hrun
    split at hrun
    · next u hu =>
      have hfree' : ∀ m ∈ L₀, m ≠ Label.pull id := by
        intro m hm
        exact hfree m (List.mem_cons.mpr (Or.inr hm))
      obtain ⟨t, ht⟩ := ih u (afterLabel s u id h l) hist hfree' hrun
      refine ⟨t, ?_⟩
      rw [outcomesFrom_eq, pullsAtGap_two_eq]
      exact (List.mem_append).2 (Or.inl (by rw [outcomesCont_cons_some hu]; exact ht))
    · simp at hrun

theorem historiesFrom_contains {id : SubId} {L P : List Label} {s : SubState} {h hist : History}
    (hfree : ∀ l ∈ L, l ≠ .pull id)
    (hpl : Placed id L P)
    (hrun : abstractHistoryFrom id s h P = some hist) :
    hist ∈ historiesFrom apply id s h L := by
  obtain ⟨t, ht⟩ := placed_outcomes L P s h hist hfree hpl hrun
  exact (List.mem_map).2 ⟨(hist, t), ht, rfl⟩

end EffectNatsSubstrate
