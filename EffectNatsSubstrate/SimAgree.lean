import EffectNatsSubstrate.ApplyLemmas
import EffectNatsSubstrate.SubPlacements

/-!
# Agreement at one subscriber — stage B1, packet P5a

Two abstract states that agree on the core, `nextId`, the key list, and the
subscriber stored at `k` are indistinguishable as far as `k`'s own evolution
is concerned: every label other than another subscriber's pull or unsubscribe
(an operation, any registration, `k`'s own pull) is enabled in one exactly when
it is in the other, the results still agree at `k`, and what the trace runner
reads (`observedOf`) is unchanged. These are the helpers `a4_complete` uses to
move other subscribers' pulls without changing what subscriber `k` sees
(proof map §3 P5).

Proof-side helpers for `SimProof.lean`, not frozen statements; logged verbatim
in `research/logs/p5a_statements.lean`.
-/

namespace EffectNatsSubstrate

/-! ## Lookup through appending a fresh pair -/

/-- Appending `(i, a)` looks up at `k` as the old lookup when that finds
something, and as `if i = k then some a else none` when it does not — so an
append's lookup effect is decided by the pre-append lookup alone. -/
theorem lookupSub_append :
    ∀ (l : List (SubId × Subscriber)) (i k : SubId) (a : Subscriber),
      lookupSub (l ++ [(i, a)]) k =
        match lookupSub l k with
        | some b => some b
        | none => if i = k then some a else none := by
  intro l
  induction l with
  | nil => intro i k a; rfl
  | cons p rest ih =>
    obtain ⟨j, sub⟩ := p
    intro i k a
    show lookupSub ((j, sub) :: (rest ++ [(i, a)])) k = _
    simp only [lookupSub]
    by_cases hjk : j = k
    · simp only [if_pos hjk]
    · simp only [if_neg hjk]
      exact ih i k a

/-- Looking up through a keyed value map, found case: the mapped entry is `g`
at the found key-value pair. -/
theorem lookupSub_map_pair_some {l : List (SubId × Subscriber)} {id : SubId}
    {b : Subscriber} (g : SubId × Subscriber → Subscriber)
    (h : lookupSub l id = some b) :
    lookupSub (l.map (fun p => (p.1, g p))) id = some (g (id, b)) := by
  revert h
  induction l with
  | nil => intro h; cases h
  | cons p rest ih =>
    obtain ⟨i, s₀⟩ := p
    intro h
    show lookupSub ((i, g (i, s₀)) :: rest.map (fun p => (p.1, g p))) id = some (g (id, b))
    simp only [lookupSub] at h ⊢
    by_cases hii : i = id
    · rw [if_pos hii] at h ⊢
      cases h
      rw [hii]
    · rw [if_neg hii] at h ⊢
      exact ih h

/-- Looking up through a keyed value map, absent case. -/
theorem lookupSub_map_pair_none {l : List (SubId × Subscriber)} {id : SubId}
    (g : SubId × Subscriber → Subscriber) (h : lookupSub l id = none) :
    lookupSub (l.map (fun p => (p.1, g p))) id = none := by
  revert h
  induction l with
  | nil => intro h; rfl
  | cons p rest ih =>
    obtain ⟨i, s₀⟩ := p
    intro h
    show lookupSub ((i, g (i, s₀)) :: rest.map (fun p => (p.1, g p))) id = none
    simp only [lookupSub] at h ⊢
    by_cases hii : i = id
    · rw [if_pos hii] at h; cases h
    · rw [if_neg hii] at h ⊢
      exact ih h

/-! ## `applyOp` enabledness mirrors the core step -/

theorem applyOp_ok_of_step {s : SubState} {core' : JSState} {o : Op} {r : Ret}
    (hstep : step s.core o = .ok (core', r)) :
    applyOp deliverOne s o (.ok r) = some (afterOp deliverOne s core' o r) := by
  unfold applyOp
  rw [hstep]
  simp

theorem applyOp_error_of_step {s : SubState} {o : Op} {err : JSError}
    (hstep : step s.core o = .error err) :
    applyOp deliverOne s o (.error err) = some s := by
  unfold applyOp
  rw [hstep]
  simp

/-! ## Agreement at one subscriber -/

/-- Agreement on everything `k`'s evolution reads. -/
def AgreeAt (k : SubId) (s s' : SubState) : Prop :=
  s'.core = s.core ∧ s'.nextId = s.nextId ∧ s'.subs.map Prod.fst = s.subs.map Prod.fst ∧
    lookupSub s'.subs k = lookupSub s.subs k

theorem agreeAt_refl (k : SubId) (s : SubState) : AgreeAt k s s := ⟨rfl, rfl, rfl, rfl⟩

theorem agreeAt_symm {k : SubId} {s s' : SubState} (h : AgreeAt k s s') : AgreeAt k s' s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem agreeAt_trans {k : SubId} {s s' s'' : SubState} (h : AgreeAt k s s')
    (h' : AgreeAt k s' s'') :
    AgreeAt k s s'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

/-- Fan-out shape: mapping both subscriber lists through the same function
preserves the agreement. -/
theorem agreeAt_map_subs {k : SubId} {s s' : SubState} {core' : JSState}
    (hag : AgreeAt k s s') (g : SubId × Subscriber → Subscriber) :
    AgreeAt k { s with core := core', subs := s.subs.map (fun p => (p.1, g p)) }
                    { s' with core := core', subs := s'.subs.map (fun p => (p.1, g p)) } := by
  refine ⟨rfl, hag.2.1, ?_, ?_⟩
  · show (s'.subs.map (fun p => (p.1, g p))).map Prod.fst =
        (s.subs.map (fun p => (p.1, g p))).map Prod.fst
    rw [keys_map_snd, keys_map_snd, hag.2.2.1]
  · show lookupSub (s'.subs.map (fun p => (p.1, g p))) k =
        lookupSub (s.subs.map (fun p => (p.1, g p))) k
    have hlook : lookupSub s'.subs k = lookupSub s.subs k := hag.2.2.2
    cases hb : lookupSub s'.subs k with
    | none =>
      have hsn : lookupSub s.subs k = none := by rw [← hlook]; exact hb
      rw [lookupSub_map_pair_none g hb, lookupSub_map_pair_none g hsn]
    | some b =>
      have hss : lookupSub s.subs k = some b := by rw [← hlook]; exact hb
      rw [lookupSub_map_pair_some g hb, lookupSub_map_pair_some g hss]

/-- Frame shape: updating only the core preserves the agreement. -/
theorem agreeAt_frame_core {k : SubId} {s s' : SubState} {core' : JSState}
    (hag : AgreeAt k s s') :
    AgreeAt k { s with core := core' } { s' with core := core' } :=
  ⟨rfl, hag.2.1, hag.2.2.1, hag.2.2.2⟩

/-- Another subscriber's pull is invisible to `k`. -/
theorem applyPull_agreeAt {k i : SubId} {s t : SubState} (hik : i ≠ k)
    (h : apply s (.pull i) = some t) : AgreeAt k s t := by
  obtain ⟨hl, hc, hn, hk⟩ := applyPull_other hik h
  exact ⟨hc, hn, hk, hl⟩

/-- Every label except another subscriber's pull or unsubscribe (an operation, any
registration, `k`'s own pull) is enabled in `s'` exactly when it is in `s`, and the results
still agree at `k`. -/
theorem apply_agreeAt {k : SubId} {s s' t : SubState} {l : Label}
    (hag : AgreeAt k s s') (hp : ∀ i, l = .pull i → i = k)
    (hu : ∀ i, l ≠ .unsubscribe i)
    (h : apply s l = some t) :
    ∃ t', apply s' l = some t' ∧ AgreeAt k t t' := by
  cases l with
  | op o e =>
    have hop : applyOp deliverOne s o e = some t := h
    rcases e with r | err
    · obtain ⟨core', hstep, ht⟩ := applyOp_ok_eq (deliver := deliverOne) hop
      have hsteps' : step s'.core o = .ok (core', r) := by rw [hag.1]; exact hstep
      refine ⟨afterOp deliverOne s' core' o r, applyOp_ok_of_step hsteps', ?_⟩
      rw [ht]
      cases o with
      | publish stream subject payload headers _el now =>
        cases r with
        | sequence seq =>
          exact agreeAt_map_subs hag
            (fun p => deliverOne stream
              { subject := subject, sequence := seq, payload := payload,
                headers := headers, timestampMillis := now } p.2)
        | _ => exact agreeAt_frame_core hag
      | deleteStream name =>
        cases r <;> exact agreeAt_map_subs hag (fun p => endOne name p.2)
      | createStream _ => cases r <;> exact agreeAt_frame_core hag
      | getStream _ => cases r <;> exact agreeAt_frame_core hag
      | lastMessageForSubject _ _ => cases r <;> exact agreeAt_frame_core hag
    · obtain ⟨ht, hstep⟩ := applyOp_error_eq (deliver := deliverOne) hop
      refine ⟨s', applyOp_error_of_step (by rw [hag.1]; exact hstep), ?_⟩
      rw [ht]; exact hag
  | register stream opts l₀ id e =>
    have hreg : applyRegister s stream opts l₀ id e = some t := h
    have hguards : ¬(id ≠ s.nextId || opts.buffer.capacity = 0) := by
      intro hbad
      have hzero : applyRegister s stream opts l₀ id e = none := by
        unfold applyRegister
        rw [if_pos hbad]
      rw [hzero] at hreg
      cases hreg
    have hguards' : ¬(id ≠ s'.nextId || opts.buffer.capacity = 0) := by
      rw [hag.2.1]; exact hguards
    rcases applyRegister_ok_eq hreg with ⟨hnone, he, ht⟩ | ⟨st, hl, he, hbound, ht⟩
    · -- missing-stream report: nothing changes
      refine ⟨s', ?_, ?_⟩
      · show applyRegister s' stream opts l₀ id e = some s'
        unfold applyRegister
        split
        · rename_i hc; exact absurd hc hguards'
        · rw [hag.1, hnone, he]
          simp
      · rw [ht]; exact hag
    · -- a real registration appends the same fresh subscriber to both key lists
      refine ⟨{ s' with subs := s'.subs ++ [(id, newSubscriber stream opts l₀ st.messages)],
                        nextId := id + 1 }, ?_, ?_⟩
      · show applyRegister s' stream opts l₀ id e =
          some { s' with subs := s'.subs ++ [(id, newSubscriber stream opts l₀ st.messages)],
                         nextId := id + 1 }
        unfold applyRegister
        split
        · rename_i hc; exact absurd hc hguards'
        · rw [hag.1, hl, he]
          simp [hbound]
      · rw [ht]
        refine ⟨hag.1, rfl, ?_, ?_⟩
        · show (s'.subs ++ [(id, newSubscriber stream opts l₀ st.messages)]).map Prod.fst =
              (s.subs ++ [(id, newSubscriber stream opts l₀ st.messages)]).map Prod.fst
          rw [List.map_append, List.map_append]
          exact congrArg (· ++ [id]) hag.2.2.1
        · rw [lookupSub_append, lookupSub_append, hag.2.2.2]
  | pull i =>
    have hik : i = k := hp i rfl
    rw [hik] at h ⊢
    obtain ⟨sub, sub', hl, hpull, ht⟩ := applyPull_ok_eq (pull := pullStep)
      (show applyPull pullStep s k = some t from h)
    have hl' : lookupSub s'.subs k = some sub := hag.2.2.2.trans hl
    refine ⟨{ s' with subs := updateSub s'.subs k (fun _ => sub') }, ?_, ?_⟩
    · show applyPull pullStep s' k = some { s' with subs := updateSub s'.subs k (fun _ => sub') }
      unfold applyPull
      simp only [hl', hpull]
    · rw [ht]
      refine ⟨hag.1, hag.2.1, ?_, ?_⟩
      · rw [updateSub_keys, updateSub_keys]; exact hag.2.2.1
      · rw [lookupSub_updateSub_self (fun _ => sub') hl',
          lookupSub_updateSub_self (fun _ => sub') hl]
  | unsubscribe i => exact absurd rfl (hu i)

/-- What `afterLabel` reads is determined by the agreement. -/
theorem observedOf_agreeAt {k : SubId} {s s' : SubState} (h : AgreeAt k s s') :
    observedOf s' k = observedOf s k := by
  unfold observedOf
  rw [h.2.2.2]

end EffectNatsSubstrate
