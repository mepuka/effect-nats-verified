import EffectNatsSubstrate.Invariants

/-!
# Per-subject views of the publish pipeline

Every per-subject theorem of the second slice (T3–T6) is stated through
`forSubject`, and this module says what each stage of a committed publish —
`publishBase` (rollup), the appended `newMessage`, `pruneSubject`/`dropOldest`
(capacity) — does to that view:

* the published subject's view becomes `keepLatest limit (prior-or-[] ++ [new])`
  (`forSubject_applyPublish_self`);
* every other subject's view is unchanged (`forSubject_applyPublish_other`).

Everything else about pruning and rollup is a corollary of those two equations.
The generic list facts core does not provide in the needed form — the
`getLast?` of a strictly sorted list is its maximum; `take`/`drop` split a
`Pairwise` list — sit at the top.
-/

namespace EffectNatsSubstrate

/-! ## Generic list lemmas -/

theorem getLast?_mem {l : List StoredMessage} {x : StoredMessage} (h : l.getLast? = some x) :
    x ∈ l := by
  match List.getLast?_eq_some_iff.mp h with
  | ⟨ys, hys⟩ =>
    subst hys
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- On a strictly increasing list, `getLast?` is the maximum. -/
theorem getLast?_max {l : List StoredMessage} {x : StoredMessage}
    (hp : l.Pairwise (fun a b => a.sequence < b.sequence)) (h : l.getLast? = some x) :
    ∀ y ∈ l, y.sequence ≤ x.sequence := by
  match List.getLast?_eq_some_iff.mp h with
  | ⟨ys, hys⟩ =>
    subst hys
    intro y hy
    have hlt := (List.pairwise_append.mp hp).2.2
    cases List.mem_append.mp hy with
    | inl hyl => exact Nat.le_of_lt (hlt y hyl x (List.mem_singleton.mpr rfl))
    | inr hyx => rw [List.mem_singleton.mp hyx]; exact Nat.le_refl _

theorem pairwise_take_drop {l : List StoredMessage} {k : Nat} {a b : StoredMessage}
    (hp : l.Pairwise (fun a b => a.sequence < b.sequence))
    (ha : a ∈ l.take k) (hb : b ∈ l.drop k) : a.sequence < b.sequence := by
  rw [← List.take_append_drop k l] at hp
  exact (List.pairwise_append.mp hp).2.2 a ha b hb

theorem mem_take_of_not_mem_drop {l : List StoredMessage} {k : Nat} {a : StoredMessage}
    (ha : a ∈ l) (hnd : a ∉ l.drop k) : a ∈ l.take k := by
  rw [← List.take_append_drop k l] at ha
  cases List.mem_append.mp ha with
  | inl h => exact h
  | inr h => exact absurd h hnd

theorem pairwise_append_singleton {α : Type} {R : α → α → Prop} {x : α} :
    ∀ {l : List α}, l.Pairwise R → (∀ a ∈ l, R a x) → (l ++ [x]).Pairwise R := by
  intro l hp hx
  exact List.pairwise_append.mpr ⟨hp, List.Pairwise.cons (fun _ h => nomatch h) .nil,
    fun a ha b hb => by rw [List.mem_singleton.mp hb]; exact hx a ha⟩

/-! ## `forSubject` as a projection -/

theorem forSubject_append (l₁ l₂ : List StoredMessage) (subject : SubjectName) :
    forSubject (l₁ ++ l₂) subject = forSubject l₁ subject ++ forSubject l₂ subject :=
  List.filter_append _ _

theorem forSubject_nil (subject : SubjectName) : forSubject [] subject = [] := rfl

theorem forSubject_cons_self {m : StoredMessage} {ms : List StoredMessage}
    {subject : SubjectName} (h : m.subject = subject) :
    forSubject (m :: ms) subject = m :: forSubject ms subject := by
  simp [forSubject, h]

theorem forSubject_cons_other {m : StoredMessage} {ms : List StoredMessage}
    {subject : SubjectName} (h : m.subject ≠ subject) :
    forSubject (m :: ms) subject = forSubject ms subject := by
  simp [forSubject, h]

theorem mem_forSubject {m : StoredMessage} {ms : List StoredMessage} {subject : SubjectName} :
    m ∈ forSubject ms subject ↔ m ∈ ms ∧ m.subject = subject := by
  simp [forSubject, List.mem_filter]

/-! ## Capacity: `dropOldest` and `pruneSubject` through the view -/

/-- Dropping the oldest `n` of a subject drops the first `n` of its view. -/
theorem forSubject_dropOldest_self (ms : List StoredMessage) (subject : SubjectName)
    (n : Nat) :
    forSubject (dropOldest ms subject n) subject = (forSubject ms subject).drop n := by
  induction ms generalizing n with
  | nil => cases n <;> rfl
  | cons m ms ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [dropOldest]
      by_cases h : m.subject = subject
      · rw [if_pos (by simp [h]), forSubject_cons_self h, List.drop_succ_cons, ih]
      · rw [if_neg (by simp [h]), forSubject_cons_other h, forSubject_cons_other h, ih]

theorem forSubject_dropOldest_other (ms : List StoredMessage) (subject other : SubjectName)
    (hne : other ≠ subject) (n : Nat) :
    forSubject (dropOldest ms subject n) other = forSubject ms other := by
  induction ms generalizing n with
  | nil => cases n <;> rfl
  | cons m ms ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [dropOldest]
      by_cases h : m.subject = subject
      · rw [if_pos (by simp [h]), forSubject_cons_other (by rw [h]; exact Ne.symm hne), ih]
      · rw [if_neg (by simp [h])]
        by_cases h2 : m.subject = other
        · rw [forSubject_cons_self h2, forSubject_cons_self h2, ih]
        · rw [forSubject_cons_other h2, forSubject_cons_other h2, ih]

theorem keepLatest_zero (l : List StoredMessage) : keepLatest 0 l = l := by
  simp [keepLatest]

theorem keepLatest_of_le {limit : Nat} {l : List StoredMessage} (hpos : limit ≠ 0)
    (hle : l.length ≤ limit) : keepLatest limit l = l := by
  simp [keepLatest, hpos, Nat.sub_eq_zero_of_le hle]

theorem keepLatest_singleton (limit : Nat) (m : StoredMessage) :
    keepLatest limit [m] = [m] := by
  unfold keepLatest
  split
  · rfl
  next h =>
    have : 1 - limit = 0 := Nat.sub_eq_zero_of_le (Nat.pos_of_ne_zero h)
    simp [this]

theorem length_keepLatest_le {limit : Nat} (hpos : 0 < limit) (l : List StoredMessage) :
    (keepLatest limit l).length ≤ limit := by
  unfold keepLatest
  rw [if_neg (Nat.ne_of_gt hpos), List.length_drop]
  omega

/-- `pruneSubject` is exactly `keepLatest` on the pruned subject's view
(`src/internal/JetStreamMemory.ts:165-172`). -/
theorem forSubject_pruneSubject_self (ms : List StoredMessage) (subject : SubjectName)
    (limit : Nat) :
    forSubject (pruneSubject ms subject limit) subject
      = keepLatest limit (forSubject ms subject) := by
  unfold pruneSubject
  by_cases h0 : limit = 0
  · subst h0; simp [keepLatest]
  · rw [if_neg (by simp [h0])]
    by_cases hle : (forSubject ms subject).length ≤ limit
    · rw [if_pos hle, keepLatest_of_le h0 hle]
    · rw [if_neg hle, forSubject_dropOldest_self]
      unfold keepLatest
      rw [if_neg h0]

theorem forSubject_pruneSubject_other (ms : List StoredMessage) (subject other : SubjectName)
    (hne : other ≠ subject) (limit : Nat) :
    forSubject (pruneSubject ms subject limit) other = forSubject ms other := by
  unfold pruneSubject
  split
  · rfl
  · split
    · rfl
    · exact forSubject_dropOldest_other ms subject other hne _

/-! ## Rollup: `publishBase` through the view -/

theorem forSubject_publishBase_self (st : StreamState) (subject : SubjectName)
    (rollup : Bool) :
    forSubject (publishBase st subject rollup) subject
      = if rollup then [] else forSubject st.messages subject := by
  unfold publishBase
  cases rollup with
  | false => rfl
  | true =>
    rw [if_pos rfl, if_pos rfl]
    unfold forSubject
    rw [List.filter_filter]
    apply List.filter_eq_nil_iff.mpr
    intro m _
    simp

theorem forSubject_publishBase_other (st : StreamState) (subject other : SubjectName)
    (hne : other ≠ subject) (rollup : Bool) :
    forSubject (publishBase st subject rollup) other = forSubject st.messages other := by
  unfold publishBase
  cases rollup with
  | false => rfl
  | true =>
    rw [if_pos rfl]
    unfold forSubject
    rw [List.filter_filter]
    apply List.filter_congr
    intro m _
    by_cases h : m.subject = other
    · simp [h, hne]
    · simp [h]

/-! ## The committed publish through the view -/

/-- The published subject's view after a commit: the prior view (or nothing,
under rollup) plus the new message, cut to the most recent `limit`. -/
theorem forSubject_applyPublish_self (st : StreamState) (subject : SubjectName)
    (payload : PayloadHash) (headers : List (String × String)) (rollup : Bool) (now : Nat) :
    forSubject (applyPublish st subject payload headers rollup now).1.messages subject
      = keepLatest st.config.maxMessagesPerSubject
          ((if rollup then [] else forSubject st.messages subject)
            ++ [newMessage st subject payload headers now]) := by
  have hnew : forSubject [newMessage st subject payload headers now] subject
      = [newMessage st subject payload headers now] := forSubject_cons_self rfl
  simp only [applyPublish]
  rw [forSubject_pruneSubject_self, forSubject_append, forSubject_publishBase_self, hnew]

/-- A commit on `subject` leaves every other subject's view untouched. -/
theorem forSubject_applyPublish_other (st : StreamState) (subject other : SubjectName)
    (hne : other ≠ subject) (payload : PayloadHash) (headers : List (String × String))
    (rollup : Bool) (now : Nat) :
    forSubject (applyPublish st subject payload headers rollup now).1.messages other
      = forSubject st.messages other := by
  have hnew : forSubject [newMessage st subject payload headers now] other = [] :=
    forSubject_cons_other (Ne.symm hne)
  simp only [applyPublish]
  rw [forSubject_pruneSubject_other _ _ _ hne, forSubject_append,
    forSubject_publishBase_other _ _ _ hne, hnew, List.append_nil]

end EffectNatsSubstrate
