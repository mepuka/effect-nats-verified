import EffectNatsSubstrate.SubReachable

/-!
# Abstract independence lemmas — stage B1, packet P4a

The per-subscriber independence facts behind `a4_inclusion` (proof map §2.4):
a pull or an unsubscribe of subscriber `i` changes nothing for any other
subscriber `j`; a successful publish maps every subscriber through `deliverOne`,
a successful `deleteStream` maps every subscriber through `endOne`, every other
successful operation leaves the subscriber list untouched, and a failed
operation changes no state at all.

Proof-side helpers for `SimProof.lean`, not frozen statements; the independence
statements are logged in `research/logs/p4a_statements.lean`, the closing
two-pulls bound in `research/logs/p5_pulls_bound.lean`.
-/

namespace EffectNatsSubstrate

/-! ## Lookup through an update at another key -/

/-- Updating subscriber `i` does not change the lookup of any other key `j`
(the abstract independence assumption of the stage-A slice document §14). -/
theorem lookupSub_updateSub_ne (subs : List (SubId × Subscriber)) (i j : SubId)
    (f : Subscriber → Subscriber) (h : i ≠ j) :
    lookupSub (updateSub subs i f) j = lookupSub subs j := by
  induction subs generalizing i j f with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, sub⟩ := p
    by_cases hki : k = i
    · have hkj : k ≠ j := fun he => h ((Eq.symm hki).trans he)
      simp only [updateSub, if_pos hki, lookupSub, if_neg hkj]
      exact ih i j f h
    · simp only [updateSub, if_neg hki, lookupSub]
      by_cases hkj : k = j
      · simp only [if_pos hkj]
      · simp only [if_neg hkj]
        exact ih i j f h

/-! ## A pull or unsubscribe of `i` is a frame for every other subscriber -/

theorem applyPull_other {s s' : SubState} {i j : SubId} (hij : i ≠ j)
    (h : apply s (.pull i) = some s') :
    lookupSub s'.subs j = lookupSub s.subs j ∧ s'.core = s.core ∧ s'.nextId = s.nextId ∧
      s'.subs.map Prod.fst = s.subs.map Prod.fst := by
  obtain ⟨sub, sub', _, _, heq⟩ :=
    applyPull_ok_eq (pull := pullStep) (show applyPull pullStep s i = some s' from h)
  rw [heq]
  refine ⟨?_, rfl, rfl, ?_⟩
  · show lookupSub (updateSub s.subs i (fun _ => sub')) j = lookupSub s.subs j
    exact lookupSub_updateSub_ne s.subs i j (fun _ => sub') hij
  · rw [updateSub_keys]

theorem applyUnsubscribe_other {s s' : SubState} {i j : SubId} (hij : i ≠ j)
    (h : apply s (.unsubscribe i) = some s') :
    lookupSub s'.subs j = lookupSub s.subs j ∧ s'.core = s.core ∧ s'.nextId = s.nextId ∧
      s'.subs.map Prod.fst = s.subs.map Prod.fst := by
  obtain ⟨_, _, _, heq⟩ := applyUnsubscribe_ok_eq
    (show applyUnsubscribe s i = some s' from h)
  rw [heq]
  refine ⟨?_, rfl, rfl, ?_⟩
  · show lookupSub (updateSub s.subs i
        (fun sub => { sub with registered := false, pending := [], status := .shutDown })) j =
      lookupSub s.subs j
    exact lookupSub_updateSub_ne s.subs i j
      (fun sub => { sub with registered := false, pending := [], status := .shutDown }) hij
  · rw [updateSub_keys]

/-! ## The two fan-out operations act per subscriber -/

theorem applyOp_publish_each {s s' : SubState} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {el : Option StreamSeq}
    {now : Nat} {seq : StreamSeq}
    (h : apply s (.op (.publish stream subject payload headers el now) (.ok (.sequence seq)))
      = some s') :
    ∀ id, lookupSub s'.subs id =
      (lookupSub s.subs id).map (deliverOne stream
        { subject := subject, sequence := seq, payload := payload, headers := headers,
          timestampMillis := now }) := by
  obtain ⟨core', _, hs'⟩ := applyOp_ok_eq (deliver := deliverOne)
    (show applyOp deliverOne s (.publish stream subject payload headers el now)
      (.ok (.sequence seq)) = some s' from h)
  rw [hs']
  intro id
  simp only [afterOp, lookupSub_map]

theorem applyOp_delete_each {s s' : SubState} {name : StreamName} {r : Ret}
    (h : apply s (.op (.deleteStream name) (.ok r)) = some s') :
    ∀ id, lookupSub s'.subs id = (lookupSub s.subs id).map (endOne name) := by
  obtain ⟨core', _, hs'⟩ := applyOp_ok_eq (deliver := deliverOne)
    (show applyOp deliverOne s (.deleteStream name) (.ok r) = some s' from h)
  rw [hs']
  intro id
  simp only [afterOp, lookupSub_map]

/-! ## Every other operation is a frame on the subscriber list -/

theorem applyOp_other_frame {s s' : SubState} {o : Op} {e : Expect}
    (hp : ∀ stream subject payload headers el now,
      o ≠ .publish stream subject payload headers el now)
    (hd : ∀ name, o ≠ .deleteStream name)
    (h : apply s (.op o e) = some s') : s'.subs = s.subs := by
  rcases e with r | err
  · obtain ⟨core', _, hs'⟩ := applyOp_ok_eq (deliver := deliverOne)
      (show applyOp deliverOne s o (.ok r) = some s' from h)
    rw [hs']
    cases o with
    | publish stream subject payload headers el now =>
      exact absurd rfl (hp stream subject payload headers el now)
    | deleteStream name => exact absurd rfl (hd name)
    | createStream _ => simp only [afterOp]
    | getStream _ => simp only [afterOp]
    | lastMessageForSubject _ _ => simp only [afterOp]
  · obtain ⟨hs', -⟩ := applyOp_error_eq (deliver := deliverOne)
      (show applyOp deliverOne s o (.error err) = some s' from h)
    rw [hs']

/-- A failed operation returns the state unchanged (`applyOp`'s error branch). -/
theorem applyOp_error_frame {s s' : SubState} {o : Op} {err : JSError}
    (h : apply s (.op o (.error err)) = some s') : s' = s :=
  (applyOp_error_eq (deliver := deliverOne)
    (show applyOp deliverOne s o (.error err) = some s' from h)).1

/-! ## At most two returning pulls between serial labels -/

/-- The per-subscriber form. -/
theorem pullStep_third_none {a a₁ a₂ : Subscriber}
    (h₁ : pullStep a = some a₁) (h₂ : pullStep a₁ = some a₂) :
    pullStep a₂ = none := by
  cases ha : a.status with
  | shutDown =>
    unfold pullStep at h₁
    simp only [ha] at h₁
    simp at h₁
  | done e =>
    unfold pullStep at h₁
    simp only [ha, Option.some.injEq] at h₁
    have ha₁ : a₁.status = .shutDown := by rw [← h₁]
    unfold pullStep at h₂
    simp only [ha₁] at h₂
    simp at h₂
  | opened =>
    unfold pullStep at h₁
    simp only [ha] at h₁
    split at h₁
    · simp at h₁
    · simp only [Option.some.injEq] at h₁
      have ha₁ : pullStep a₁ = none := by rw [← h₁]; simp [pullStep]
      rw [ha₁] at h₂
      simp at h₂
  | closing e =>
    unfold pullStep at h₁
    simp only [ha] at h₁
    split at h₁
    · simp at h₁
    · simp only [Option.some.injEq] at h₁
      have ha₁ : a₁.status = .done e := by rw [← h₁]
      unfold pullStep at h₂
      simp only [ha₁, Option.some.injEq] at h₂
      have ha₂ : a₂.status = .shutDown := by rw [← h₂]
      unfold pullStep
      simp only [ha₂]

/-- After two enabled pulls of the same subscriber a third returns `none` —
the "at most two returning pulls per abstract gap" bound that P5
(`a4_complete`) rests on. -/
theorem pull_third_none {s s₁ s₂ : SubState} {id : SubId}
    (h₁ : apply s (.pull id) = some s₁) (h₂ : apply s₁ (.pull id) = some s₂) :
    apply s₂ (.pull id) = none := by
  obtain ⟨sub, sub', hl₁, hp₁, hs₁⟩ :=
    applyPull_ok_eq (pull := pullStep) (show applyPull pullStep s id = some s₁ from h₁)
  obtain ⟨a, b, hl₂, hp₂, hs₂⟩ :=
    applyPull_ok_eq (pull := pullStep) (show applyPull pullStep s₁ id = some s₂ from h₂)
  have hs₁' : lookupSub s₁.subs id = some sub' := by
    rw [hs₁]
    exact lookupSub_updateSub_self (fun _ => sub') hl₁
  have hsa : sub' = a := Option.some.inj (hs₁'.symm.trans hl₂)
  have hp₂' : pullStep sub' = some b := by rw [hsa]; exact hp₂
  rw [hs₂]
  show applyPull pullStep _ id = none
  unfold applyPull
  simp only [lookupSub_updateSub_self (fun _ => b) hl₂,
    pullStep_third_none hp₁ hp₂']

end EffectNatsSubstrate
