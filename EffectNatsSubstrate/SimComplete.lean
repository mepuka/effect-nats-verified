import EffectNatsSubstrate.SimProof
import EffectNatsSubstrate.SimPlaced

/-!
# `a4_complete` — the runtime histories are enumerated (stage B1, packet P5c)

`A4Complete` (SB5, snapshot r4.2) says that a quiescent, close-free runtime execution whose serial
sequence is a valid `unsubscribe`-free trace's leaves every runtime subscriber with a chunk history
the exporter prints for it — membership in `historiesWith apply t id`. The two halves it needs are
already proved: P4b's `a4_inclusion_pullOnly_of_rtInv` produces, for the execution, an abstract
label list `labels` that runs, has the run's serial sequence, gives `id` exactly `rtHistory s id`,
and contains no `unsubscribe`; P5b's `historiesFrom_contains` says every *enabled* placement of
`id`'s pulls into a pull-free list is enumerated.

What is missing between them is that `labels` and the trace's own `labelsWithoutPulls t id` are two
different lists: `labels` carries the pulls the *runtime* took, the trace carries the pulls the
*trace* wrote, and neither is a placement of the other. `merge_placed` builds the placement by
walking the two along the serial spine they share (`labelSerial labels = rtSerial rls =
labelSerial (t's labels) = labelSerial (labelsWithoutPulls t id)`, since `labelSerial` already
drops pulls): `id`'s pulls are emitted where `labels` has them, `labels`' other-subscriber pulls
are dropped, and the trace's other-subscriber pulls are emitted where the trace has them. The walk
carries a two-sided agreement — `AgreeAt id` with the `labels` run, so `id`'s own pulls stay
enabled and its history is unchanged, and `AgreeExcept id` with the trace's run, so every other
subscriber's pull stays enabled at its trace position — which is exactly what
`SimAgree.apply_agreeAt` and `SimProof.apply_agreeExcept` transport.

Round 6's structural note is why nothing more is needed: the relative order of `id`'s pulls and
other subscribers' pulls inside one serial gap is *free* (other subscribers' pulls are invisible to
`id`, and `id`'s are invisible to them), so the walk may fix any order; and three consecutive pulls
of `id` — the only shape `pullsAtGap`'s fuel of 2 could miss — is never enabled (`pull_third_none`,
used inside `historiesFrom_contains`).

`RtInv` on the reachable runtime state is an input, as in P4b: `a4_complete_of_rtInv` is
`A4Complete` modulo P2's `rtInv_reachable`, and the coordinator closes `a4_inclusion` and
`a4_complete` together once P2 merges.
-/

namespace EffectNatsSubstrate

/-! ## Agreement away from one subscriber, continued -/

theorem agreeExcept_symm {i : SubId} {s t : SubState} (h : AgreeExcept i s t) :
    AgreeExcept i t s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun j hj => (h.2.2.2 j hj).symm⟩

theorem agreeExcept_trans {i : SubId} {s t u : SubState} (h : AgreeExcept i s t)
    (h' : AgreeExcept i t u) : AgreeExcept i s u :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
   fun j hj => (h'.2.2.2 j hj).trans (h.2.2.2 j hj)⟩

/-! ## Serial spines -/

/-- The labels a serial spine skips: pulls and unsubscribes. -/
theorem labelSerial_nil_mem : ∀ (ls : List Label), labelSerial ls = [] →
    ∀ l ∈ ls, (∃ j, l = .pull j) ∨ (∃ j, l = .unsubscribe j) := by
  intro ls
  induction ls with
  | nil => intro _ l hl; cases hl
  | cons m rest ih =>
    intro hser l hl
    cases m with
    | op o e =>
      have hs : Label.op o e :: labelSerial rest = [] := hser
      cases hs
    | register stream opts l₀ i e =>
      have hs : Label.register stream opts l₀ i e :: labelSerial rest = [] := hser
      cases hs
    | pull j =>
      rcases List.mem_cons.mp hl with he | hm
      · exact Or.inl ⟨j, he⟩
      · exact ih hser l hm
    | unsubscribe j =>
      rcases List.mem_cons.mp hl with he | hm
      · exact Or.inr ⟨j, he⟩
      · exact ih hser l hm

/-- A label list whose serial spine starts with `l` splits at `l`, with a serial-free prefix. -/
theorem labelSerial_split : ∀ (L : List Label) {l : Label} {R : List Label},
    labelSerial L = l :: R →
    ∃ L₁ L₂, L = L₁ ++ l :: L₂ ∧ labelSerial L₁ = [] ∧ labelSerial L₂ = R := by
  intro L
  induction L with
  | nil =>
    intro l R hser
    have hs : ([] : List Label) = l :: R := hser
    cases hs
  | cons m rest ih =>
    intro l R hser
    cases m with
    | op o e =>
      have hs : Label.op o e :: labelSerial rest = l :: R := hser
      injection hs with h1 h2
      exact ⟨[], rest, by rw [h1]; rfl, rfl, h2⟩
    | register stream opts l₀ i e =>
      have hs : Label.register stream opts l₀ i e :: labelSerial rest = l :: R := hser
      injection hs with h1 h2
      exact ⟨[], rest, by rw [h1]; rfl, rfl, h2⟩
    | pull j =>
      obtain ⟨L₁, L₂, he, h1, h2⟩ := ih (l := l) (R := R) hser
      exact ⟨Label.pull j :: L₁, L₂, by rw [he]; rfl, h1, h2⟩
    | unsubscribe j =>
      obtain ⟨L₁, L₂, he, h1, h2⟩ := ih (l := l) (R := R) hser
      exact ⟨Label.unsubscribe j :: L₁, L₂, by rw [he]; rfl, h1, h2⟩

/-- Removing `id`'s pulls does not change the serial spine. -/
theorem labelSerial_filter_pull (id : SubId) : ∀ (ls : List Label),
    labelSerial (ls.filter (fun l => l ≠ Label.pull id)) = labelSerial ls := by
  intro ls
  induction ls with
  | nil => rfl
  | cons m rest ih =>
    by_cases hm : m = Label.pull id
    · subst hm
      rw [List.filter_cons_of_neg (by simp)]
      exact ih
    · rw [List.filter_cons_of_pos (by simp [hm])]
      cases m with
      | op o e => show Label.op o e :: _ = Label.op o e :: _; rw [ih]
      | register stream opts l₀ i e =>
        show Label.register stream opts l₀ i e :: _ = Label.register stream opts l₀ i e :: _
        rw [ih]
      | pull j => exact ih
      | unsubscribe j => exact ih

/-! ## `Placed` helpers -/

theorem placed_keep_all : ∀ (L : List Label) {id : SubId} {P : List Label} {L₀ : List Label},
    Placed id L₀ P → Placed id (L ++ L₀) (L ++ P) := by
  intro L
  induction L with
  | nil => intro id P L₀ h; exact h
  | cons m rest ih => intro id P L₀ h; exact Placed.keep (ih h)

theorem placed_refl : ∀ (L : List Label) {id : SubId}, Placed id L L := by
  intro L
  induction L with
  | nil => exact Placed.nil
  | cons m rest ih => exact Placed.keep ih


/-! ## Runs of other subscribers' consumer labels -/

theorem runLabels_split : ∀ (l₁ : List Label) {s t : SubState} (l₂ : List Label),
    runLabels s (l₁ ++ l₂) = some t → ∃ u, runLabels s l₁ = some u ∧ runLabels u l₂ = some t := by
  intro l₁
  induction l₁ with
  | nil => intro s t l₂ h; exact ⟨s, rfl, h⟩
  | cons l rest ih =>
    intro s t l₂ h
    have h' : runLabels s (l :: (rest ++ l₂)) = some t := h
    rw [runLabels_cons] at h'
    cases hap : apply s l with
    | none => rw [hap] at h'; cases h'
    | some v =>
      rw [hap] at h'
      obtain ⟨u, h1, h2⟩ := ih l₂ h'
      exact ⟨u, by rw [runLabels_cons, hap]; exact h1, h2⟩

/-- A run of consumer labels of subscribers other than `k` is invisible to `k`. -/
theorem runLabels_agreeAt_other {k : SubId} : ∀ (ls : List Label) {s t : SubState},
    (∀ l ∈ ls, ∃ j, (l = Label.pull j ∨ l = Label.unsubscribe j) ∧ j ≠ k) →
    runLabels s ls = some t → AgreeAt k s t := by
  intro ls
  induction ls with
  | nil => intro s t _ h; cases h; exact agreeAt_refl k s
  | cons l rest ih =>
    intro s t hls h
    rw [runLabels_cons] at h
    cases hap : apply s l with
    | none => rw [hap] at h; cases h
    | some v =>
      rw [hap] at h
      obtain ⟨j, hj, hjk⟩ := hls l (List.Mem.head _)
      have hstep : AgreeAt k s v := by
        rcases hj with hj | hj <;> subst hj
        · exact applyPull_agreeAt hjk hap
        · exact applyUnsubscribe_agreeAt hjk hap
      exact agreeAt_trans hstep (ih (fun m hm => hls m (List.Mem.tail _ hm)) h)

/-- Dropping `id`'s pulls from a run keeps it a run, and changes nothing away from `id`. -/
theorem runLabels_strip_pulls {id : SubId} : ∀ (ls : List Label) {s t u : SubState},
    (∀ l ∈ ls, ∀ j, l ≠ Label.unsubscribe j) →
    AgreeExcept id s u → runLabels s ls = some t →
    ∃ u', runLabels u (ls.filter (fun l => l ≠ Label.pull id)) = some u' ∧
      AgreeExcept id t u' := by
  intro ls
  induction ls with
  | nil => intro s t u _ hag h; cases h; exact ⟨u, rfl, hag⟩
  | cons l rest ih =>
    intro s t u hnu hag h
    rw [runLabels_cons] at h
    cases hap : apply s l with
    | none => rw [hap] at h; cases h
    | some v =>
      rw [hap] at h
      by_cases hl : l = Label.pull id
      · subst hl
        have hagv : AgreeExcept id v u :=
          agreeExcept_trans (agreeExcept_symm (agreeExcept_of_pull hap)) hag
        obtain ⟨u', hu', hagu⟩ :=
          ih (fun m hm => hnu m (List.Mem.tail _ hm)) hagv h
        refine ⟨u', ?_, hagu⟩
        rw [List.filter_cons_of_neg (by simp)]
        exact hu'
      · obtain ⟨w, hw, hagw⟩ := apply_agreeExcept hag (fun j hj => by
          rcases hj with hj | hj
          · intro he; exact hl (by rw [hj, he])
          · exact absurd hj (hnu l (List.Mem.head _) j)) hap
        obtain ⟨u', hu', hagu⟩ := ih (fun m hm => hnu m (List.Mem.tail _ hm)) hagw h
        refine ⟨u', ?_, hagu⟩
        rw [List.filter_cons_of_pos (by simp [hl]), runLabels_cons, hw]
        exact hu'


theorem labelSerial_cons_serial {l : Label} (hp : ∀ j, l ≠ Label.pull j)
    (hu : ∀ j, l ≠ Label.unsubscribe j) (ls : List Label) :
    labelSerial (l :: ls) = l :: labelSerial ls := by
  cases l with
  | op o e => rfl
  | register _ _ _ _ _ => rfl
  | pull j => exact absurd rfl (hp j)
  | unsubscribe j => exact absurd rfl (hu j)

/-- **The merge.** `A` is a label list that runs and gives `id` the history `hist` (the witness of
`A4Inclusion`: serial labels, `id`'s pulls, and other subscribers' pulls); `L` is a
pull-free-for-`id` list with the same serial spine that runs from a state agreeing with `A`'s away
from `id` (the trace's labels minus `id`'s pulls). Walking the two along their common spine —
emitting `id`'s pulls where `A` has them, dropping `A`'s other pulls, emitting `L`'s where `L` has
them — builds a placement of `id`'s pulls into `L` that runs and gives `id` the same history. -/
theorem merge_placed {id : SubId} :
    ∀ (A : List Label) {L : List Label} {sA sL sP : SubState} {h hist : History},
      (∀ l ∈ A, ∀ j, l ≠ Label.unsubscribe j) →
      (∀ m ∈ L, (∀ j, m ≠ Label.unsubscribe j) ∧ m ≠ Label.pull id) →
      labelSerial A = labelSerial L →
      AgreeAt id sA sP → AgreeExcept id sL sP →
      abstractHistoryFrom id sA h A = some hist →
      (runLabels sL L).isSome = true →
      ∃ P, Placed id L P ∧ abstractHistoryFrom id sP h P = some hist := by
  intro A
  induction A with
  | nil =>
    intro L sA sL sP h hist _ hLsh hser hagA hagE hA hL
    have hh : h = hist := Option.some.inj hA
    subst hh
    have hnil : labelSerial L = [] := hser.symm
    have hLne : ∀ m ∈ L, ∀ j, (m = Label.pull j ∨ m = Label.unsubscribe j) → j ≠ id := by
      intro m hm j hj he
      rcases hj with hj | hj
      · exact (hLsh m hm).2 (by rw [hj, he])
      · exact (hLsh m hm).1 j hj
    have hframe : ∀ m ∈ L, (∀ j, m = Label.pull j → j ≠ id) ∧
        ∀ stream opts lz j e, m = Label.register stream opts lz j e → j ≠ id := by
      intro m hm
      rcases labelSerial_nil_mem L hnil m hm with ⟨j, hj⟩ | ⟨j, hj⟩
      · refine ⟨fun k hk => hLne m hm k (Or.inl hk), fun stream opts lz k e hk => ?_⟩
        rw [hj] at hk
        cases hk
      · exact absurd hj ((hLsh m hm).1 j)
    obtain ⟨sL', hsL'⟩ : ∃ u, runLabels sL L = some u := by
      cases hq : runLabels sL L with
      | none => rw [hq] at hL; exact Bool.noConfusion hL
      | some u => exact ⟨u, rfl⟩
    obtain ⟨sP', hsP', -⟩ := runLabels_agreeExcept L hagE hLne hsL'
    exact ⟨L, placed_refl L, abstractHistoryFrom_frame id L hframe hsP'⟩
  | cons l A' ih =>
    intro L sA sL sP h hist hAsh hLsh hser hagA hagE hA hL
    have hLne : ∀ m ∈ L, ∀ j, (m = Label.pull j ∨ m = Label.unsubscribe j) → j ≠ id := by
      intro m hm j hj he
      rcases hj with hj | hj
      · exact (hLsh m hm).2 (by rw [hj, he])
      · exact (hLsh m hm).1 j hj
    have hAsh' : ∀ m ∈ A', ∀ j, m ≠ Label.unsubscribe j :=
      fun m hm => hAsh m (List.Mem.tail _ hm)
    have hu : ∀ j, l ≠ Label.unsubscribe j := hAsh l (List.Mem.head _)
    rw [abstractHistoryFrom_cons] at hA
    cases hap : apply sA l with
    | none => rw [hap] at hA; cases hA
    | some sA₁ =>
      rw [hap] at hA
      have hA1 : abstractHistoryFrom id sA₁ (afterLabel sA sA₁ id h l) A' = some hist := hA
      clear hA
      by_cases hpull : ∃ j, l = Label.pull j
      · obtain ⟨j, hj⟩ := hpull
        subst hj
        by_cases hjid : j = id
        · subst hjid
          obtain ⟨sP₁, hsP₁, hagA₁⟩ :=
            apply_agreeAt hagA (fun i hi => by injection hi with hi'; exact hi'.symm)
              (fun i hc => by cases hc) hap
          have hafter : afterLabel sA sA₁ j h (Label.pull j)
              = afterLabel sP sP₁ j h (Label.pull j) :=
            (apply_agree_step (h := h) hagA hap hsP₁).2
          obtain ⟨P', hpl, hrunP⟩ :=
            ih hAsh' hLsh hser hagA₁
              (agreeExcept_trans hagE (agreeExcept_of_pull hsP₁)) hA1 hL
          refine ⟨Label.pull j :: P', Placed.pull hpl, ?_⟩
          rw [abstractHistoryFrom_cons, hsP₁]
          show abstractHistoryFrom j sP₁ (afterLabel sP sP₁ j h (Label.pull j)) P' = some hist
          rw [← hafter]
          exact hrunP
        · have hagA₁ : AgreeAt id sA₁ sP :=
            agreeAt_trans (agreeAt_symm (applyPull_agreeAt hjid hap)) hagA
          have hafter : afterLabel sA sA₁ id h (Label.pull j) = h := by
            show (if j = id then h ++ [appended sA sA₁ id] else h) = h
            exact if_neg hjid
          rw [hafter] at hA1
          exact ih hAsh' hLsh hser hagA₁ hagE hA1 hL
      · have hp : ∀ j, l ≠ Label.pull j := fun j hj => hpull ⟨j, hj⟩
        obtain ⟨L₁, L₂, hLeq, hL₁nil, hL₂ser⟩ :=
          labelSerial_split L (by rw [← hser, labelSerial_cons_serial hp hu])
        subst hLeq
        have hmemL : ∀ m ∈ L₁, m ∈ L₁ ++ l :: L₂ :=
          fun m hm => List.mem_append.mpr (Or.inl hm)
        have hL₁ne : ∀ m ∈ L₁, ∀ j, (m = Label.pull j ∨ m = Label.unsubscribe j) → j ≠ id :=
          fun m hm => hLne m (hmemL m hm)
        have hL₁other : ∀ m ∈ L₁, ∃ j, (m = Label.pull j ∨ m = Label.unsubscribe j) ∧ j ≠ id := by
          intro m hm
          rcases labelSerial_nil_mem L₁ hL₁nil m hm with ⟨j, hj⟩ | ⟨j, hj⟩
          · exact ⟨j, Or.inl hj, hL₁ne m hm j (Or.inl hj)⟩
          · exact ⟨j, Or.inr hj, hL₁ne m hm j (Or.inr hj)⟩
        have hL₁frame : ∀ m ∈ L₁, (∀ j, m = Label.pull j → j ≠ id) ∧
            ∀ stream opts lz j e, m = Label.register stream opts lz j e → j ≠ id := by
          intro m hm
          rcases labelSerial_nil_mem L₁ hL₁nil m hm with ⟨j, hj⟩ | ⟨j, hj⟩
          · refine ⟨fun k hk => hL₁ne m hm k (Or.inl hk), fun stream opts lz k e hk => ?_⟩
            rw [hj] at hk
            cases hk
          · exact absurd hj ((hLsh m (hmemL m hm)).1 j)
        obtain ⟨sLall, hsLall⟩ : ∃ u, runLabels sL (L₁ ++ l :: L₂) = some u := by
          cases hq : runLabels sL (L₁ ++ l :: L₂) with
          | none => rw [hq] at hL; exact Bool.noConfusion hL
          | some u => exact ⟨u, rfl⟩
        obtain ⟨sL₁, hrunL₁, hrest⟩ := runLabels_split L₁ (l :: L₂) hsLall
        rw [runLabels_cons] at hrest
        cases hapL : apply sL₁ l with
        | none => rw [hapL] at hrest; cases hrest
        | some sL₂ =>
          rw [hapL] at hrest
          obtain ⟨sP₁, hrunP₁, hagE₁⟩ := runLabels_agreeExcept L₁ hagE hL₁ne hrunL₁
          have hagAP₁ : AgreeAt id sA sP₁ :=
            agreeAt_trans hagA (runLabels_agreeAt_other L₁ hL₁other hrunP₁)
          obtain ⟨sP₂, hsP₂, hagA₂⟩ :=
            apply_agreeAt hagAP₁ (fun i hi => absurd hi (hp i)) hu hap
          obtain ⟨sP₂', hsP₂', hagE₂⟩ := apply_agreeExcept hagE₁ (fun j hj => by
            rcases hj with hj | hj
            · exact absurd hj (hp j)
            · exact absurd hj (hu j)) hapL
          have hsame : sP₂' = sP₂ := Option.some.inj (hsP₂'.symm.trans hsP₂)
          subst hsame
          have hafter : afterLabel sA sA₁ id h l = afterLabel sP₁ sP₂' id h l :=
            (apply_agree_step (h := h) hagAP₁ hap hsP₂).2
          obtain ⟨P', hpl, hrunP'⟩ :=
            ih hAsh'
              (fun m hm => hLsh m (List.mem_append.mpr (Or.inr (List.Mem.tail _ hm))))
              hL₂ser.symm hagA₂ hagE₂ hA1
              (by have hr : runLabels sL₂ L₂ = some sLall := hrest
                  rw [hr]; rfl)
          refine ⟨L₁ ++ l :: P', placed_keep_all L₁ (Placed.keep hpl), ?_⟩
          rw [abstractHistoryFrom_append id L₁ (l :: P') hrunP₁
            (abstractHistoryFrom_frame id L₁ hL₁frame hrunP₁)]
          rw [abstractHistoryFrom_cons, hsP₂]
          show abstractHistoryFrom id sP₂' (afterLabel sP₁ sP₂' id h l) P' = some hist
          rw [← hafter]
          exact hrunP'


/-- **`A4Complete` modulo the invariant** (packet P5c; the one remaining input is P2's
`rtInv_reachable`, exactly as for `a4_inclusion_of_rtInv`).

The witness of `A4Inclusion` for the runtime execution is a label list with the trace's serial
spine, `id`'s pulls where the runtime took them, and other subscribers' pulls; the trace's own
labels minus `id`'s pulls (`labelsWithoutPulls`) is a list with the same spine that runs.
`merge_placed` walks the two along the spine and produces a placement of `id`'s pulls into the
latter that runs and gives `id` the same chunk history; `historiesFrom_contains` (P5b) then says
that history is enumerated. -/
theorem a4_complete_of_rtInv
    (hinv : ∀ (rls : List RtLabel) (s : RtState), runRtSteps initialRt rls = some s → RtInv s) :
    A4Complete := by
  intro t hvalid hnounsub rls s hrun hfan hclose hserial id hid hpres
  have hTunsub : ∀ m ∈ t.steps.map (·.label), ∀ j, m ≠ Label.unsubscribe j := by
    intro m hm j he
    obtain ⟨st, hst, hstl⟩ := List.mem_map.mp hm
    have := (List.all_eq_true.mp hnounsub) st hst
    rw [hstl, he] at this
    exact Bool.noConfusion this
  -- the trace runs
  obtain ⟨sT, hsT⟩ : ∃ u, runLabels initialSub (t.steps.map (·.label)) = some u := by
    cases hq : runLabels initialSub (t.steps.map (·.label)) with
    | none => rw [hq] at hvalid; exact Bool.noConfusion hvalid
    | some u => exact ⟨u, rfl⟩
  -- and so does the trace minus `id`'s pulls
  obtain ⟨sL, hsL, -⟩ :=
    runLabels_strip_pulls (t.steps.map (·.label)) hTunsub (agreeExcept_refl id initialSub) hsT
  -- the witness of A4Inclusion
  obtain ⟨labels, sA, hrunA, hserA, hhistA, -, hnu⟩ :=
    a4_inclusion_pullOnly_of_rtInv hinv rls s hrun hfan hclose
  have hAsh : ∀ l ∈ labels, ∀ j, l ≠ Label.unsubscribe j := by
    intro l hl j he
    have := (List.all_eq_true.mp hnu) l hl
    rw [he] at this
    exact Bool.noConfusion this
  have hLsh : ∀ m ∈ labelsWithoutPulls t id,
      (∀ j, m ≠ Label.unsubscribe j) ∧ m ≠ Label.pull id := by
    intro m hm
    have hm2 : m ∈ t.steps.map (·.label) ∧ (decide (m ≠ Label.pull id)) = true :=
      List.mem_filter.mp hm
    exact ⟨hTunsub m hm2.1, by simpa using hm2.2⟩
  have hfree : ∀ m ∈ labelsWithoutPulls t id, m ≠ Label.pull id := fun m hm => (hLsh m hm).2
  have hser : labelSerial labels = labelSerial (labelsWithoutPulls t id) := by
    rw [hserA, hserial]
    exact (labelSerial_filter_pull id (t.steps.map (·.label))).symm
  obtain ⟨P, hpl, hrunP⟩ :=
    merge_placed labels hAsh hLsh hser (agreeAt_refl id initialSub)
      (agreeExcept_refl id initialSub) (hhistA id hpres)
      (by have hr : runLabels initialSub (labelsWithoutPulls t id) = some sL := hsL
          rw [hr]; rfl)
  exact List.elem_eq_true_of_mem (historiesFrom_contains hfree hpl hrunP)


end EffectNatsSubstrate
