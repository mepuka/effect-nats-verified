import EffectNatsSubstrate.SubReachable

/-!
# Abstract independence lemmas — stage B1, packet P4a

The per-subscriber independence facts behind `a4_inclusion` (proof map §2.4):
a pull or an unsubscribe of subscriber `i` changes nothing for any other
subscriber `j`; a successful publish maps every subscriber through `deliverOne`,
a successful `deleteStream` maps every subscriber through `endOne`, every other
successful operation leaves the subscriber list untouched, and a failed
operation changes no state at all.

Proof-side helpers for `SimProof.lean`, not frozen statements; the statements
are logged in `research/logs/p4a_statements.lean`.
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

end EffectNatsSubstrate
