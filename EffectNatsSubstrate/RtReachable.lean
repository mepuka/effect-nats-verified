import EffectNatsSubstrate.RtInvariants
import EffectNatsSubstrate.RtList
import EffectNatsSubstrate.EffectQueueLaws
import EffectNatsSubstrate.Proofs

/-!
# Stage-B1 reachability — `RtInv` over `ReachableRt` (SB3), frame and safety (SB6, SB7)

One preservation lemma per `RtLabel`, then the single induction over `ReachableRt`
in this package (the stage-A rule: every later fact projects from
`rtInv_reachable`). The induction carries an auxiliary invariant beside `RtInv`:
`RtInv` alone is not inductive (overwatch T9 §4, measured) — `rtResolve`'s admit
branch sets `lastEnqueued := m.sequence` and must re-establish `registeredStream`,
yet nothing in `RtInv` ties the fan-out's message and stream to `core` or to the
subscriber's stream; and after a deletion's `endFanOut` the clause's exemption
lifts with nothing saying the deleted stream's subscribers are all de-registered.
`FanAux` supplies both facts (established at `op`, preserved by every other
label); its publish membership clause is the one-sided target clause of
`SimRelation.Rel` seen from the runtime side. A third delete clause carries
registered subscribers of *other* streams through the deletion window: under a
delete fan-out `registeredStream` is vacuous for everyone, so their
existence-and-bound fact must be held explicitly until `endFanOut`.

Source lines are `Runtime.lean` (`rtOp` … `rtCloseB`); the queue laws are
`EffectQueueLaws.lean`. A successful elaboration proves the stated proposition,
not that it models the system; the fidelity boundary is the transliteration
recorded in each module header.
-/

namespace EffectNatsSubstrate

/-! ## Association-list facts for `lookupRt` / `updateRt` -/

theorem lookupRt_isSome_of_mem :
    ∀ {subs : List (SubId × RtSubscriber)} {id : SubId} {r : RtSubscriber},
      (id, r) ∈ subs → (lookupRt subs id).isSome
  | [], _, _, h => by cases h
  | (i, r₀) :: rest, id, r, h => by
    rcases List.mem_cons.mp h with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp [lookupRt]
    · by_cases hi : i = id
      · simp [lookupRt, hi]
      · simp only [lookupRt, if_neg hi]
        exact lookupRt_isSome_of_mem hmem

/-- A lookup through an update at the updated key comes from the pre-update
entry there. -/
theorem lookupRt_updateRt_eq :
    ∀ {subs : List (SubId × RtSubscriber)} {id : SubId} {v : RtSubscriber}
      (g : RtSubscriber → RtSubscriber),
      lookupRt (updateRt subs id g) id = some v →
      ∃ u, lookupRt subs id = some u ∧ v = g u
  | [], _, _, _, h => by cases h
  | (j, r₂) :: rest, id, v, g, h => by
    by_cases hj : j = id
    · subst hj
      simp [updateRt, lookupRt] at h
      exact ⟨r₂, by simp [lookupRt], h.symm⟩
    · simp only [updateRt, if_neg hj, lookupRt] at h ⊢
      exact lookupRt_updateRt_eq g h

theorem lookupRt_updateRt_neq :
    ∀ (subs : List (SubId × RtSubscriber)) (id k : SubId) (g : RtSubscriber → RtSubscriber)
      {v : RtSubscriber},
      k ≠ id → lookupRt (updateRt subs id g) k = some v → lookupRt subs k = some v
  | [], _, _, _, _, _, h => by cases h
  | (j, r₂) :: rest, id, k, g, v, hne, h => by
    by_cases hjk : j = k
    · have hjid : j ≠ id := fun hh => hne (hjk.symm.trans hh)
      simp only [updateRt, if_neg hjid, lookupRt, if_pos hjk] at h ⊢
      exact h
    · simp only [lookupRt, if_neg hjk] at h ⊢
      by_cases hjd : j = id
      · simp only [updateRt, if_pos hjd, lookupRt, if_neg hjk] at h ⊢
        exact lookupRt_updateRt_neq rest id k g hne h
      · simp only [updateRt, if_neg hjd, lookupRt, if_neg hjk] at h ⊢
        exact lookupRt_updateRt_neq rest id k g hne h

theorem mem_updateRt :
    ∀ {subs : List (SubId × RtSubscriber)} {id : SubId} {g : RtSubscriber → RtSubscriber}
      {k : SubId} {v : RtSubscriber},
      (k, v) ∈ updateRt subs id g →
      (k, v) ∈ subs ∨ (k = id ∧ ∃ u, (id, u) ∈ subs ∧ v = g u)
  | [], _, _, _, _, h => by cases h
  | (j, r₂) :: rest, id, g, k, v, h => by
    by_cases hj : j = id
    · subst hj
      simp [updateRt, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨hkj, hv⟩ | h
      · exact Or.inr ⟨hkj, r₂, List.mem_cons_self, hv⟩
      · rcases mem_updateRt h with h1 | ⟨hk, u, h0, hv⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨hk, u, List.mem_cons_of_mem _ h0, hv⟩
    · simp only [updateRt, if_neg hj, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_updateRt h with h1 | ⟨hk, u, h0, hv⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨hk, u, List.mem_cons_of_mem _ h0, hv⟩

/-- Contradiction helpers for clashing queue statuses. -/
theorem qs_ne_opened_done {s : QueueStatus} {e : SubError}
    (h1 : s = QueueStatus.opened) (h2 : s = QueueStatus.done e) : False :=
  QueueStatus.noConfusion (h1.symm.trans h2)

theorem qs_ne_opened_closing {s : QueueStatus} {e : SubError}
    (h1 : s = QueueStatus.opened) (h2 : s = QueueStatus.closing e) : False :=
  QueueStatus.noConfusion (h1.symm.trans h2)

theorem qs_ne_opened_shutDown {s : QueueStatus}
    (h1 : s = QueueStatus.opened) (h2 : s = QueueStatus.shutDown) : False :=
  QueueStatus.noConfusion (h1.symm.trans h2)

/-! ## The fan-out lists -/

theorem filter_map_fst_pairwise :
    ∀ (subs : List (SubId × RtSubscriber)) (p : (SubId × RtSubscriber) → Bool),
      (subs.map Prod.fst).Pairwise (· < ·) → ((subs.filter p).map Prod.fst).Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | (j, r₂) :: rest, p, hp => by
    rw [List.map_cons, List.pairwise_cons] at hp
    obtain ⟨hlt, hrest⟩ := hp
    by_cases hpred : p (j, r₂) = true
    · rw [List.filter_cons_of_pos hpred, List.map_cons, List.pairwise_cons]
      refine ⟨?_, filter_map_fst_pairwise rest p hrest⟩
      intro q hq
      obtain ⟨a, ha, hafst⟩ := List.mem_map.mp hq
      rw [← hafst]
      exact hlt _ (List.mem_map.mpr ⟨a, (List.mem_filter.mp ha).1, rfl⟩)
    · rw [List.filter_cons_of_neg (by simpa using hpred)]
      exact filter_map_fst_pairwise rest p hrest

theorem fanOutIds_nodup (s : RtState) (stream : StreamName) (subject : SubjectName)
    (hp : (s.subs.map Prod.fst).Pairwise (· < ·)) :
    (fanOutIds s stream subject).Nodup :=
  List.Pairwise.imp (fun hlt => Nat.ne_of_lt hlt)
    (filter_map_fst_pairwise s.subs
      (fun p => p.2.registered && p.2.stream == stream && matchesAny p.2.filters subject) hp)

theorem deleteIds_nodup (s : RtState) (name : StreamName)
    (hp : (s.subs.map Prod.fst).Pairwise (· < ·)) :
    (deleteIds s name).Nodup :=
  List.Pairwise.imp (fun hlt => Nat.ne_of_lt hlt)
    (filter_map_fst_pairwise s.subs (fun p => p.2.registered && p.2.stream == name) hp)

theorem fanOutIds_known (s : RtState) (stream : StreamName) (subject : SubjectName)
    {id : SubId} (h : id ∈ fanOutIds s stream subject) : (lookupRt s.subs id).isSome := by
  unfold fanOutIds at h
  obtain ⟨p, hp, hfst⟩ := List.mem_map.mp h
  cases p with
  | mk k v =>
    have hkeq : k = id := hfst
    subst hkeq
    exact lookupRt_isSome_of_mem (List.mem_filter.mp hp).1

theorem fanOutIds_stream {s : RtState} {stream : StreamName} {subject : SubjectName}
    {id : SubId} {r : RtSubscriber}
    (hp : (s.subs.map Prod.fst).Pairwise (· < ·))
    (h : id ∈ fanOutIds s stream subject) (hl : lookupRt s.subs id = some r) :
    r.stream = stream := by
  unfold fanOutIds at h
  obtain ⟨p, hpM, hfst⟩ := List.mem_map.mp h
  cases p with
  | mk k v =>
    have hm := (List.mem_filter.mp hpM).1
    have hcond := (List.mem_filter.mp hpM).2
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    have hkeq : k = id := hfst
    rw [hkeq] at hm
    have hv : lookupRt s.subs id = some v :=
      lookupRt_of_mem_pairwise s.subs id _ hp hm
    rw [hl] at hv
    cases hv
    exact hcond.1.2

theorem deleteIds_known (s : RtState) (name : StreamName) {id : SubId}
    (h : id ∈ deleteIds s name) : (lookupRt s.subs id).isSome := by
  unfold deleteIds at h
  obtain ⟨p, hp, hfst⟩ := List.mem_map.mp h
  cases p with
  | mk k v =>
    have hkeq : k = id := hfst
    subst hkeq
    exact lookupRt_isSome_of_mem (List.mem_filter.mp hp).1

theorem deleteIds_mem {s : RtState} {name : StreamName} {id : SubId} {r : RtSubscriber}
    (hl : lookupRt s.subs id = some r) (hr : r.registered = true) (hs : r.stream = name) :
    id ∈ deleteIds s name := by
  unfold deleteIds
  refine List.mem_map.mpr ⟨(id, r), ?_, rfl⟩
  refine List.mem_filter.mpr ⟨mem_of_lookupRt _ _ _ hl, ?_⟩
  rw [hr, hs]
  simp

/-! ## The auxiliary invariant -/

structure FanAux (s : RtState) (f : FanOut) : Prop where
  publish : ∀ stream m el, f.kind = .publish stream m el →
    (∃ st, lookupStream s.core stream = some st ∧ m.sequence < st.nextSequence) ∧
    (∀ id, (id ∈ f.remaining ∨ (∃ b, f.decided = some (id, b)) ∨ (∃ o, (id, o) ∈ f.visited)) →
      ∀ r, lookupRt s.subs id = some r → r.stream = stream)
  delete : ∀ name, f.kind = .delete name →
    lookupStream s.core name = none ∧
    (∀ id r, lookupRt s.subs id = some r → r.registered = true → r.stream = name →
      id ∈ f.remaining) ∧
    (∀ id r, lookupRt s.subs id = some r → r.registered = true → r.stream ≠ name →
      ∃ st, lookupStream s.core r.stream = some st ∧ r.lastEnqueued < st.nextSequence)

/-- `FanAux` for the fan-out in flight, if any. -/
def RtAux (s : RtState) : Prop := ∀ f, s.fanOut = some f → FanAux s f

/-- Both auxiliary clauses survive a constant update of the entry at key `id`
(the only kind of subscriber-write a consumer label performs). `h` identifies the
pre-entry `u₀` at that key and states how the written value `c` agrees with it:
same stream, registration-drop only disables premises, bound kept when
registration survives — exactly what the three delete clauses transport. -/
theorem fanAux_updateRt {s : RtState} {f : FanOut} {id : SubId}
    (c : RtSubscriber)
    (h : ∃ u₀, lookupRt s.subs id = some u₀ ∧
      c.stream = u₀.stream ∧
      (c.registered = true → u₀.registered = true) ∧
      c.lastEnqueued = u₀.lastEnqueued)
    (haux : FanAux s f) :
    FanAux { s with subs := updateRt s.subs id (fun _ => c) } f := by
  obtain ⟨u₀, hl₀, hS, hR, hL⟩ := h
  refine ⟨?_, ?_⟩
  · intro stream m el hk
    obtain ⟨hex, hmem⟩ := haux.publish stream m el hk
    refine ⟨hex, ?_⟩
    intro j hd rv hl'
    by_cases hjc : j = id
    · subst hjc
      obtain ⟨u, hu, heq⟩ := lookupRt_updateRt_eq
        (subs := s.subs) (id := j) (g := fun _ => c) hl'
      rw [heq, hS]
      exact hmem j hd u₀ hl₀
    · have hlk : lookupRt s.subs j = some rv :=
        lookupRt_updateRt_neq (subs := s.subs) (id := id) (k := j) (g := fun _ => c) hjc hl'
      exact hmem j hd rv hlk
  · intro name hk
    obtain ⟨gone, cover, others⟩ := haux.delete name hk
    refine ⟨gone, ?_, ?_⟩
    · intro j rv hl' hr' hs'
      by_cases hjc : j = id
      · subst hjc
        obtain ⟨u, hu, heq⟩ := lookupRt_updateRt_eq
          (subs := s.subs) (id := j) (g := fun _ => c) hl'
        have huu : u = u₀ := Option.some.inj (hu.symm.trans hl₀)
        rw [huu] at hu
        subst heq
        exact cover j u₀ hu (hR hr') (hS.symm.trans hs')
      · have hlk : lookupRt s.subs j = some rv :=
          lookupRt_updateRt_neq (subs := s.subs) (id := id) (k := j) (g := fun _ => c) hjc hl'
        exact cover j rv hlk hr' hs'
    · intro j rv hl' hr' hs'
      by_cases hjc : j = id
      · subst hjc
        obtain ⟨u, hu, heq⟩ := lookupRt_updateRt_eq
          (subs := s.subs) (id := j) (g := fun _ => c) hl'
        have huu : u = u₀ := Option.some.inj (hu.symm.trans hl₀)
        rw [huu] at hu
        subst heq
        obtain ⟨st, hst1, hst2⟩ := others j u₀ hu (hR hr') (by rw [← hS]; exact hs')
        refine ⟨st, ?_, ?_⟩
        · rw [hS]; exact hst1
        · rw [hL]; exact hst2
      · have hlk : lookupRt s.subs j = some rv :=
          lookupRt_updateRt_neq (subs := s.subs) (id := id) (k := j)
            (g := fun _ => c) hjc hl'
        exact others j rv hlk hr' hs'

/-- A lookup that succeeds before an update still succeeds after it. -/
theorem lookupRt_updateRt_isSome :
    ∀ (subs : List (SubId × RtSubscriber)) (id j : SubId) (g : RtSubscriber → RtSubscriber),
      (lookupRt subs j).isSome → (lookupRt (updateRt subs id g) j).isSome
  | [], _, _, _, h => Bool.noConfusion h
  | (i, r₀) :: rest, id, j, g, h => by
    by_cases hij : i = j
    · by_cases hid : i = id
      · simp only [updateRt, if_pos hid, lookupRt, if_pos hij]
        exact rfl
      · simp only [updateRt, if_neg hid, lookupRt, if_pos hij]
        exact rfl
    · by_cases hid : i = id
      · simp only [updateRt, if_pos hid, lookupRt, if_neg hij] at h ⊢
        exact lookupRt_updateRt_isSome rest id j g h
      · simp only [updateRt, if_neg hid, lookupRt, if_neg hij] at h ⊢
        exact lookupRt_updateRt_isSome rest id j g h

/-! ## Per-label preservation -/

theorem rtCloseA_invAux {s s' : RtState} {id : SubId}
    (hinv : RtInv s) (haux : RtAux s) (h : rtCloseA s id = some s') :
    RtInv s' ∧ RtAux s' := by
  have h' : rtCloseA s id = some s' := h
  unfold rtCloseA at h'
  cases hlook : lookupRt s.subs id with
  | none => rw [hlook] at h'; simp only [] at h'; simp at h'
  | some r =>
    rw [hlook] at h'
    simp only [] at h'
    split at h'
    · simp at h'
    · next hc =>
      cases h'
      have hcond : ¬(r.closeStarted = true ∨ r.queue.status = .shutDown) := by
        simpa using hc
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro q hq
        obtain ⟨k, v⟩ := q
        rcases mem_updateRt hq with hmem | ⟨hkid, u, h0, hv⟩
        · have hs0 := hinv.subs _ hmem
          exact ⟨hs0.capacityPos, hs0.queue, hs0.registeredOpen, hs0.closeStartedOpen,
            fun hr hn => hs0.registeredStream hr hn⟩
        · have hlk : lookupRt s.subs id = some u :=
            lookupRt_of_mem_pairwise _ _ _ hinv.shape.1 h0
          rw [hlk] at hlook
          have hur : u = r := Option.some.inj hlook
          subst hur
          subst hv
          subst hkid
          have hu' := hinv.subs _ h0
          exact ⟨hu'.capacityPos, hu'.queue, fun hr => Bool.noConfusion hr,
            fun _ => ⟨rfl, fun hsd => hcond (Or.inr hsd)⟩,
            fun hr => Bool.noConfusion hr⟩
      · refine ⟨by rw [updateRt_keys]; exact hinv.shape.1, ?_⟩
        intro p hp
        obtain ⟨k, v⟩ := p
        rcases mem_updateRt hp with hmem | ⟨hkid, u, h0, hv⟩
        · exact hinv.shape.2 _ hmem
        · have hlk : lookupRt s.subs id = some u :=
            lookupRt_of_mem_pairwise _ _ _ hinv.shape.1 h0
          rw [hlk] at hlook
          have hur : u = r := Option.some.inj hlook
          subst hur
          subst hv
          subst hkid
          exact hinv.shape.2 (k, u) h0
      · intro f hf
        have hf0 := hinv.fanOut f hf
        refine ⟨hf0.remainingNodup, ?_, hf0.decidedNotRemaining, ?_, ?_⟩
        · intro j hj
          exact lookupRt_updateRt_isSome s.subs id j (fun _ => { r with registered := false, closeStarted := true }) (hf0.remainingKnown j hj)
        · intro i b hb
          exact lookupRt_updateRt_isSome s.subs id i (fun _ => { r with registered := false, closeStarted := true }) (hf0.decidedKnown i b hb)
        · intro i hb rv hl
          by_cases hic : i = id
          · subst hic
            obtain ⟨u, hu, heq⟩ := lookupRt_updateRt_eq
              (g := fun _ => { r with registered := false, closeStarted := true }) hl
            rw [hu] at hlook
            have hur : u = r := Option.some.inj hlook
            subst hur
            subst heq
            exact hf0.decidedRoom i hb u hu
          · have hlk : lookupRt s.subs i = some rv :=
              lookupRt_updateRt_neq s.subs id i
                (fun _ => { r with registered := false, closeStarted := true }) hic hl
            exact hf0.decidedRoom i hb rv hlk
      · exact hinv.core
      · intro f hf
        have hbnd : ∃ u₀, lookupRt s.subs id = some u₀ ∧
            ({ r with registered := false, closeStarted := true }).stream = u₀.stream ∧
            (({ r with registered := false, closeStarted := true }).registered = true →
              u₀.registered = true) ∧
            ({ r with registered := false, closeStarted := true }).lastEnqueued =
              u₀.lastEnqueued :=
          ⟨r, hlook, rfl, fun hr => Bool.noConfusion hr, rfl⟩
        exact fanAux_updateRt _ hbnd (haux f hf)

theorem rtCloseB_invAux {s s' : RtState} {id : SubId}
    (hinv : RtInv s) (haux : RtAux s) (h : rtCloseB s id = some s') :
    RtInv s' ∧ RtAux s' := by
  have h' : rtCloseB s id = some s' := h
  unfold rtCloseB at h'
  cases hlook : lookupRt s.subs id with
  | none => rw [hlook] at h'; simp only [] at h'; simp at h'
  | some r =>
    rw [hlook] at h'
    simp only [] at h'
    split at h'
    · simp at h'
    · next hc =>
      cases h'
      have hgcs : r.closeStarted = true := by simpa using hc
      have hrs := hinv.subs (id, r) (mem_of_lookupRt _ _ _ hlook)
      have hreg : r.registered = false := (hrs.closeStartedOpen hgcs).1
      have hscl := shutdown_clears r.queue
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro q hq
        obtain ⟨k, v⟩ := q
        rcases mem_updateRt hq with hmem | ⟨hkid, u, h0, hv⟩
        · have hs0 := hinv.subs _ hmem
          exact ⟨hs0.capacityPos, hs0.queue, hs0.registeredOpen, hs0.closeStartedOpen,
            fun hr hn => hs0.registeredStream hr hn⟩
        · subst hv
          have hq : QueueInv r.policy.capacity r.queue.shutdown :=
            ⟨fun ht => by simp [EffectQueue.shutdown] at ht,
              fun e he => QueueStatus.noConfusion he,
              fun e he => QueueStatus.noConfusion he, fun _ => ⟨hscl.left, rfl⟩,
              Nat.zero_le _⟩
          exact ⟨hrs.capacityPos, hq,
            fun hr => by rw [hreg] at hr; exact Bool.noConfusion hr,
            fun hr => by simp at hr,
            fun hr => by rw [hreg] at hr; exact Bool.noConfusion hr⟩
      · refine ⟨by rw [updateRt_keys]; exact hinv.shape.1, ?_⟩
        intro p hp
        obtain ⟨k, v⟩ := p
        rcases mem_updateRt hp with hmem | ⟨hkid, u, h0, hv⟩
        · exact hinv.shape.2 _ hmem
        · have hlk : lookupRt s.subs id = some u :=
            lookupRt_of_mem_pairwise _ _ _ hinv.shape.1 h0
          rw [hlk] at hlook
          have hur : u = r := Option.some.inj hlook
          subst hur
          subst hv
          subst hkid
          exact hinv.shape.2 (k, u) h0
      · intro f hf
        have hf0 := hinv.fanOut f hf
        refine ⟨hf0.remainingNodup, ?_, hf0.decidedNotRemaining, ?_, ?_⟩
        · intro j hj
          exact lookupRt_updateRt_isSome s.subs id j (fun _ => { r with queue := r.queue.shutdown, closeStarted := false }) (hf0.remainingKnown j hj)
        · intro i b hb
          exact lookupRt_updateRt_isSome s.subs id i (fun _ => { r with queue := r.queue.shutdown, closeStarted := false }) (hf0.decidedKnown i b hb)
        · intro i hb rv hl
          by_cases hic : i = id
          · subst hic
            obtain ⟨u, hu, heq⟩ := lookupRt_updateRt_eq
              (g := fun _ => { r with queue := r.queue.shutdown, closeStarted := false }) hl
            rw [hu] at hlook
            have hur : u = r := Option.some.inj hlook
            subst hur
            subst heq
            refine Or.inr ?_
            show QueueStatus.shutDown = QueueStatus.opened → False
            exact QueueStatus.noConfusion
          · have hlk : lookupRt s.subs i = some rv :=
              lookupRt_updateRt_neq s.subs id i
                (fun _ => { r with queue := r.queue.shutdown, closeStarted := false }) hic hl
            exact hf0.decidedRoom i hb rv hlk
      · exact hinv.core
      · intro f hf
        have hbnd : ∃ u₀, lookupRt s.subs id = some u₀ ∧
            ({ r with queue := r.queue.shutdown, closeStarted := false }).stream =
              u₀.stream ∧
            (({ r with queue := r.queue.shutdown, closeStarted := false }).registered =
                true → u₀.registered = true) ∧
            ({ r with queue := r.queue.shutdown, closeStarted := false }).lastEnqueued =
              u₀.lastEnqueued := by
          refine ⟨r, hlook, rfl, fun hr => hr, rfl⟩
        exact fanAux_updateRt _ hbnd (haux f hf)

/-! ## The plumbing every subscriber write shares -/

/-- `RtSubInv` reads only the core and the fan-out of its state. -/
theorem rtSubInv_state {s : RtState} (s' : RtState) {r : RtSubscriber} (hcore : s'.core = s.core)
    (hfan : s'.fanOut = s.fanOut) (h : RtSubInv s r) : RtSubInv s' r := by
  refine ⟨h.capacityPos, h.queue, h.registeredOpen, h.closeStartedOpen, ?_⟩
  intro hr hn
  rw [hcore]
  exact h.registeredStream hr (by rw [hfan] at hn; exact hn)

/-- The key list and the `nextId` bound survive a one-key update. -/
theorem rtShape_update {s : RtState} (hinv : RtInv s) (id : SubId)
    (g : RtSubscriber → RtSubscriber) :
    ((updateRt s.subs id g).map Prod.fst).Pairwise (· < ·) ∧
      ∀ p ∈ updateRt s.subs id g, p.1 < s.nextId := by
  refine ⟨by rw [updateRt_keys]; exact hinv.shape.1, ?_⟩
  intro p hp
  obtain ⟨k, v⟩ := p
  rcases mem_updateRt hp with hmem | ⟨hkid, u, h0, hv⟩
  · exact hinv.shape.2 _ hmem
  · rw [hkid]
    exact hinv.shape.2 (id, u) h0

/-- The fan-out clauses survive a one-key update: only `decidedRoom` reads the subscriber. -/
theorem fanOutInv_update {s : RtState} {f : FanOut} {id : SubId} {c : RtSubscriber}
    (hf0 : FanOutInv s f)
    (hroom : f.decided = some (id, false) →
      c.queue.buffer.length < c.policy.capacity ∨ c.queue.status ≠ .opened) :
    FanOutInv { s with subs := updateRt s.subs id (fun _ => c) } f := by
  refine ⟨hf0.remainingNodup, ?_, hf0.decidedNotRemaining, ?_, ?_⟩
  · intro j hj
    exact lookupRt_updateRt_isSome s.subs id j _ (hf0.remainingKnown j hj)
  · intro i b hb
    exact lookupRt_updateRt_isSome s.subs id i _ (hf0.decidedKnown i b hb)
  · intro i hb rv hl
    by_cases hic : i = id
    · subst hic
      obtain ⟨u, hu, heq⟩ := lookupRt_updateRt_eq (g := fun _ => c) hl
      rw [heq]
      exact hroom hb
    · exact hf0.decidedRoom i hb rv (lookupRt_updateRt_neq s.subs id i _ hic hl)

/-- One subscriber rewritten, the fan-out untouched: `RtInv` and `RtAux` transport. -/
theorem rtInvAux_update {s : RtState} {id : SubId} {r c : RtSubscriber}
    (hinv : RtInv s) (haux : RtAux s)
    (hlook : lookupRt s.subs id = some r)
    (hsub : RtSubInv s c)
    (hroom : ∀ f, s.fanOut = some f → f.decided = some (id, false) →
      c.queue.buffer.length < c.policy.capacity ∨ c.queue.status ≠ .opened)
    (hstream : c.stream = r.stream)
    (hreg : c.registered = true → r.registered = true)
    (hlast : c.lastEnqueued = r.lastEnqueued) :
    RtInv { s with subs := updateRt s.subs id (fun _ => c) } ∧
      RtAux { s with subs := updateRt s.subs id (fun _ => c) } := by
  refine ⟨⟨?_, rtShape_update hinv id _, ?_, hinv.core⟩, ?_⟩
  · intro q hq
    obtain ⟨k, v⟩ := q
    rcases mem_updateRt hq with hmem | ⟨hkid, u, h0, hv⟩
    · exact rtSubInv_state (s := s) _ rfl rfl (hinv.subs _ hmem)
    · rw [hv]
      exact rtSubInv_state (s := s) _ rfl rfl hsub
  · intro f hf
    exact fanOutInv_update (hinv.fanOut f hf) (hroom f hf)
  · intro f hf
    exact fanAux_updateRt c ⟨r, hlook, hstream, hreg, hlast⟩ (haux f hf)

/-- The subscriber clauses of a consumer write, which touches only the queue and the chunks. -/
theorem rtSubInv_queue {s : RtState} {r : RtSubscriber} {q' : EffectQueue} {ch : History}
    (hrs : RtSubInv s r) (hcs : r.closeStarted = false)
    (hqinv : QueueInv r.policy.capacity q')
    (hopen : r.registered = true → q'.status = .opened) :
    RtSubInv s { r with queue := q', chunks := ch } :=
  ⟨hrs.capacityPos, hqinv, fun hr => ⟨hopen hr, hcs⟩,
   fun hb => by rw [hcs] at hb; exact Bool.noConfusion hb,
   fun hr hn => hrs.registeredStream hr hn⟩

/-- Every queue a returning or parking take leaves behind is drained, and never `closing`; that
is the whole queue half of `pull` and `wake`. -/
theorem queueInv_drained {cap : Nat} {q : EffectQueue} (hcap : 1 ≤ cap)
    (hbuf : q.buffer = [])
    (hstat : q.status = .opened ∨ (∃ e, q.status = .done e) ∨ q.status = .shutDown)
    (htaker : q.taker = true → q.status = .opened) :
    QueueInv cap q ∧ (q.buffer.length < cap ∨ q.status ≠ .opened) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, Or.inl ?_⟩
  · intro ht
    rw [htaker ht]
    intro hc
    exact QueueStatus.noConfusion hc
  · intro e _
    exact hbuf
  · intro e he
    rcases hstat with hs | ⟨e2, hs⟩ | hs <;> rw [hs] at he <;> exact QueueStatus.noConfusion he
  · intro hsd
    refine ⟨hbuf, ?_⟩
    cases ht : q.taker with
    | false => rfl
    | true =>
      rw [htaker ht] at hsd
      exact absurd hsd (fun hc => QueueStatus.noConfusion hc)
  · rw [hbuf]
    exact Nat.zero_le _
  · rw [hbuf]
    exact hcap

/-! ## `pull` and `wake` -/

theorem rtPull_invAux {s s' : RtState} {id : SubId}
    (hinv : RtInv s) (haux : RtAux s) (h : rtPull s id = some s') :
    RtInv s' ∧ RtAux s' := by
  unfold rtPull at h
  cases hlook : lookupRt s.subs id with
  | none => simp only [hlook] at h; simp at h
  | some r =>
    simp only [hlook] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq] at hc
      obtain ⟨⟨htk, hsd⟩, hcs0⟩ := hc
      have hcs : r.closeStarted = false := by
        cases hb : r.closeStarted with
        | false => rfl
        | true => exact absurd hb hcs0
      have htk0 : r.queue.taker = false := by
        cases hb : r.queue.taker with
        | false => rfl
        | true => exact absurd hb htk
      have hrs := hinv.subs (id, r) (mem_of_lookupRt _ _ _ hlook)
      have hqi := hrs.queue
      have hregNO : ∀ {P : Prop}, r.queue.status ≠ .opened → r.registered = true → P := by
        intro P hne hr
        exact absurd (hrs.registeredOpen hr).1 hne
      have hmain : ∀ (q' : EffectQueue) (ch : History),
          q'.buffer = [] →
          (q'.status = .opened ∨ (∃ e, q'.status = .done e) ∨ q'.status = .shutDown) →
          (q'.taker = true → q'.status = .opened) →
          (r.registered = true → q'.status = .opened) →
          RtInv { s with
              subs := updateRt s.subs id (fun _ => { r with queue := q', chunks := ch }) } ∧
            RtAux { s with
              subs := updateRt s.subs id (fun _ => { r with queue := q', chunks := ch }) } := by
        intro q' ch hbuf hstat htaker hopen
        obtain ⟨hqinv, hroom⟩ := queueInv_drained hrs.capacityPos hbuf hstat htaker
        exact rtInvAux_update hinv haux hlook (rtSubInv_queue hrs hcs hqinv hopen)
          (fun _ _ _ => hroom) rfl (fun hr => hr) rfl
      cases hstat : r.queue.status with
      | shutDown => exact absurd hstat hsd
      | done e =>
        rw [exit_after_drain r.queue e hstat] at h
        simp only [chunkOf] at h
        cases h
        have hnop : r.queue.status ≠ .opened := by
          rw [hstat]; intro hcc; exact QueueStatus.noConfusion hcc
        exact hmain _ _ (hqi.doneEmpty e hstat) (Or.inr (Or.inr rfl))
          (fun ht => by rw [ht] at htk0; exact Bool.noConfusion htk0) (hregNO hnop)
      | closing e =>
        rw [takeAll_closing r.queue e hstat (hqi.closingNonempty e hstat)] at h
        simp only [chunkOf] at h
        cases h
        have hnop : r.queue.status ≠ .opened := by
          rw [hstat]; intro hcc; exact QueueStatus.noConfusion hcc
        exact hmain _ _ rfl (Or.inr (Or.inl ⟨e, rfl⟩))
          (fun ht => by rw [ht] at htk0; exact Bool.noConfusion htk0) (hregNO hnop)
      | opened =>
        by_cases hb : r.queue.buffer = []
        · have htake : r.queue.takeAll = ({ r.queue with taker := true }, .parked) := by
            unfold EffectQueue.takeAll
            rw [hstat]
            simp [hb, hstat]
          rw [htake] at h
          simp only [chunkOf] at h
          cases h
          exact hmain _ _ hb (Or.inl hstat) (fun _ => hstat) (fun _ => hstat)
        · rw [takeAll_drains r.queue hstat hb] at h
          simp only [chunkOf] at h
          cases h
          exact hmain _ _ rfl (Or.inl hstat)
            (fun ht => by rw [ht] at htk0; exact Bool.noConfusion htk0) (fun _ => hstat)

theorem rtWake_invAux {s s' : RtState} {id : SubId}
    (hinv : RtInv s) (haux : RtAux s) (h : rtWake s id = some s') :
    RtInv s' ∧ RtAux s' := by
  unfold rtWake at h
  cases hlook : lookupRt s.subs id with
  | none => simp only [hlook] at h; simp at h
  | some r =>
    simp only [hlook] at h
    split at h
    · simp at h
    · rename_i hcs0
      have hcs : r.closeStarted = false := by
        cases hb : r.closeStarted with
        | false => rfl
        | true => exact absurd hb hcs0
      have hrs := hinv.subs (id, r) (mem_of_lookupRt _ _ _ hlook)
      have hqi := hrs.queue
      have hregNO : ∀ {P : Prop}, r.queue.status ≠ .opened → r.registered = true → P := by
        intro P hne hr
        exact absurd (hrs.registeredOpen hr).1 hne
      have hmain : ∀ (q' : EffectQueue) (ch : History),
          q'.buffer = [] →
          (q'.status = .opened ∨ (∃ e, q'.status = .done e) ∨ q'.status = .shutDown) →
          (q'.taker = true → q'.status = .opened) →
          (r.registered = true → q'.status = .opened) →
          RtInv { s with
              subs := updateRt s.subs id (fun _ => { r with queue := q', chunks := ch }) } ∧
            RtAux { s with
              subs := updateRt s.subs id (fun _ => { r with queue := q', chunks := ch }) } := by
        intro q' ch hbuf hstat htaker hopen
        obtain ⟨hqinv, hroom⟩ := queueInv_drained hrs.capacityPos hbuf hstat htaker
        exact rtInvAux_update hinv haux hlook (rtSubInv_queue hrs hcs hqinv hopen)
          (fun _ _ _ => hroom) rfl (fun hr => hr) rfl
      by_cases htk : r.queue.taker = true
      · cases hstat : r.queue.status with
        | shutDown =>
          have hw : r.queue.wake = none := by unfold EffectQueue.wake; simp [htk, hstat]
          rw [hw] at h
          simp at h
        | done e =>
          have hw : r.queue.wake =
              some ({ r.queue with status := .shutDown, taker := false }, .exit e) := by
            unfold EffectQueue.wake; simp [htk, hstat]
          rw [hw] at h
          simp only [chunkOf] at h
          cases h
          have hnop : r.queue.status ≠ .opened := by
            rw [hstat]; intro hcc; exact QueueStatus.noConfusion hcc
          exact hmain _ _ (hqi.doneEmpty e hstat) (Or.inr (Or.inr rfl))
            (fun ht => Bool.noConfusion ht) (hregNO hnop)
        | opened =>
          by_cases hb : r.queue.buffer = []
          · have hw : r.queue.wake = none := by unfold EffectQueue.wake; simp [htk, hstat, hb]
            rw [hw] at h
            simp at h
          · have hw : r.queue.wake =
                some ({ r.queue with buffer := [], taker := false }, .chunk r.queue.buffer) := by
              unfold EffectQueue.wake; simp [htk, hstat, hb]
            rw [hw] at h
            simp only [chunkOf] at h
            cases h
            exact hmain _ _ rfl (Or.inl hstat) (fun ht => Bool.noConfusion ht) (fun _ => hstat)
        | closing e =>
          by_cases hb : r.queue.buffer = []
          · exact absurd hb (hqi.closingNonempty e hstat)
          · have hw : r.queue.wake =
                some ({ r.queue with buffer := [], status := .done e, taker := false },
                  .chunk r.queue.buffer) := by
              unfold EffectQueue.wake; simp [htk, hstat, hb]
            rw [hw] at h
            simp only [chunkOf] at h
            cases h
            have hnop : r.queue.status ≠ .opened := by
              rw [hstat]; intro hcc; exact QueueStatus.noConfusion hcc
            exact hmain _ _ rfl (Or.inr (Or.inl ⟨e, rfl⟩)) (fun ht => Bool.noConfusion ht)
              (hregNO hnop)
      · have hw : r.queue.wake = none := by unfold EffectQueue.wake; simp [htk]
        rw [hw] at h
        simp at h

end EffectNatsSubstrate
