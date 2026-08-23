import EffectNatsSubstrate.RtInvariants
import EffectNatsSubstrate.EffectQueueLaws
import EffectNatsSubstrate.RtList

/-!
# Commutation of runtime steps (stage B1, SB2)

The fan-out's internal steps and a consumer's own steps read and write disjoint
parts of the state: a consumer step of `j` reads and writes `lookupRt s.subs j`
/ `updateRt s.subs j _` and leaves `fanOut` alone; a publisher step of `i`
(`check`/`resolve`) reads `s.fanOut` and `lookupRt s.subs i`, writes
`updateRt s.subs i _` and `fanOut`. So what one does never changes what the
other decides about a different subscriber (statements frozen with snapshot
r4, block `RtCommute.lean`).

The one pair that is *not* claimed is `closeA i` against `op`: `op` fixes the
fan-out list from the still-registered subscribers, so the order matters; SB2
is scoped to the fan-out's internal labels plus the consumer steps.

Shape. Two association-list facts carry the disjointness: `lookupRt_updateRt_ne`
and `lookupRt_updateRt_self` from the shared `RtList.lean`, and
`updateRt_updateRt_comm` (only needed here, so declared here). Per consumer
label, a none-invariance lemma and a transfer lemma say the step is determined
by `lookupRt s.subs j`; two frame lemmas say how `check`/`resolve` transform
when `subs` changed away from key `i`. `ConsumerPkg`/`PubPkg` bundle those
per-label facts, `consumerFun`/`publisherFun` read a label disjunction into the
bundled step function, and `bindStep_pair_comm`/`bindStep_pub_comm` assemble the
two commutations; the frozen theorems instantiate them.

The `RtInv` hypothesis is carried because the frozen statements carry it, and is
**not used**: everything above is unconditional (the overwatch's probe found no
failure on 96 768 generated `RtInv`-violating two-subscriber states either). Both
frozen theorems therefore bind it `_hinv` — an unused binder, not a weakened
statement.
-/

namespace EffectNatsSubstrate

/-! ## Association-list facts -/

theorem updateRt_updateRt_comm {l : List (SubId × RtSubscriber)} {i j : SubId}
    {f g : RtSubscriber → RtSubscriber} (hne : i ≠ j) :
    updateRt (updateRt l j g) i f = updateRt (updateRt l i f) j g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨k, sub⟩ := a
    by_cases hi : k = i <;> by_cases hj : k = j
    · subst hi
      exact absurd hj hne
    · subst hi; simp [updateRt, hj, ih]
    · subst hj; simp [updateRt, hi, ih]
    · simp [updateRt, hi, hj, ih]

theorem updateRt_id (l : List (SubId × RtSubscriber)) (i : SubId) :
    updateRt l i (fun x => x) = l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨k, sub⟩ := a
    simp only [updateRt]
    split
    · simp [ih]
    · simp [ih]

/-! ## Consumer steps are determined by `lookupRt s.subs j` -/

theorem rtPull_none_inval {s t : RtState} {j : SubId}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hn : rtPull s j = none) :
    rtPull t j = none := by
  unfold rtPull at hn ⊢
  revert hn
  rw [h]
  intro hne
  split at hne
  · exact hne
  · next sub heq =>
    split at hne
    · next g => rw [if_pos g]
    · next g =>
      rw [if_neg g]
      split at *
      split at *
      · rfl
      · exact absurd hne (by simp)
theorem rtPull_transfer {s t : RtState} {j : SubId} {w : RtState}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hw : rtPull s j = some w) :
    ∃ r' : RtSubscriber, w = { s with subs := updateRt s.subs j (fun _ => r') } ∧
      rtPull t j = some { t with subs := updateRt t.subs j (fun _ => r') } := by
  unfold rtPull at hw ⊢
  revert hw
  rw [h]
  intro hw
  split at hw
  · simp at hw
  · next sub heq =>
    split at hw
    · next g =>
      rw [if_pos g]
      exact absurd hw (by simp)
    · next g =>
      rw [if_neg g]
      split at *
      split at *
      · exact absurd hw (by simp)
      · injection hw with hc; subst hc; exact ⟨_, rfl, rfl⟩
theorem rtWake_none_inval {s t : RtState} {j : SubId}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hn : rtWake s j = none) :
    rtWake t j = none := by
  unfold rtWake at hn ⊢
  revert hn
  rw [h]
  intro hne
  split at hne
  · exact hne
  · next sub heq =>
    split at hne
    · next g => rw [if_pos g]
    · next g =>
      rw [if_neg g]
      split at hne
      · rfl
      · exact absurd hne (by simp)
theorem rtWake_transfer {s t : RtState} {j : SubId} {w : RtState}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hw : rtWake s j = some w) :
    ∃ r' : RtSubscriber, w = { s with subs := updateRt s.subs j (fun _ => r') } ∧
      rtWake t j = some { t with subs := updateRt t.subs j (fun _ => r') } := by
  unfold rtWake at hw ⊢
  revert hw
  rw [h]
  intro hw
  split at hw
  · simp at hw
  · next sub heq =>
    split at hw
    · next g =>
      rw [if_pos g]
      exact absurd hw (by simp)
    · next g =>
      rw [if_neg g]
      split at hw
      · next gnone => exact absurd hw (by simp)
      · next qp =>
        injection hw with hc; subst hc; exact ⟨_, rfl, rfl⟩
theorem rtCloseA_none_inval {s t : RtState} {j : SubId}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hn : rtCloseA s j = none) :
    rtCloseA t j = none := by
  unfold rtCloseA at hn ⊢
  revert hn
  rw [h]
  intro hne
  split at hne
  · exact hne
  · next sub heq =>
    split at hne
    · next g => rw [if_pos g]
    · next g =>
      rw [if_neg g]
      exact absurd hne (by simp)
theorem rtCloseA_transfer {s t : RtState} {j : SubId} {w : RtState}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hw : rtCloseA s j = some w) :
    ∃ r' : RtSubscriber, w = { s with subs := updateRt s.subs j (fun _ => r') } ∧
      rtCloseA t j = some { t with subs := updateRt t.subs j (fun _ => r') } := by
  unfold rtCloseA at hw ⊢
  revert hw
  rw [h]
  intro hw
  split at hw
  · simp at hw
  · next sub heq =>
    split at hw
    · next g =>
      rw [if_pos g]
      exact absurd hw (by simp)
    · next g =>
      rw [if_neg g]
      injection hw with hc; subst hc; exact ⟨_, rfl, rfl⟩
theorem rtCloseB_none_inval {s t : RtState} {j : SubId}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hn : rtCloseB s j = none) :
    rtCloseB t j = none := by
  unfold rtCloseB at hn ⊢
  revert hn
  rw [h]
  intro hne
  split at hne
  · exact hne
  · next sub heq =>
    split at hne
    · next g => rw [if_pos g]
    · next g =>
      rw [if_neg g]
      exact absurd hne (by simp)
theorem rtCloseB_transfer {s t : RtState} {j : SubId} {w : RtState}
    (h : lookupRt t.subs j = lookupRt s.subs j) (hw : rtCloseB s j = some w) :
    ∃ r' : RtSubscriber, w = { s with subs := updateRt s.subs j (fun _ => r') } ∧
      rtCloseB t j = some { t with subs := updateRt t.subs j (fun _ => r') } := by
  unfold rtCloseB at hw ⊢
  revert hw
  rw [h]
  intro hw
  split at hw
  · simp at hw
  · next sub heq =>
    split at hw
    · next g =>
      rw [if_pos g]
      exact absurd hw (by simp)
    · next g =>
      rw [if_neg g]
      injection hw with hc; subst hc; exact ⟨_, rfl, rfl⟩

/-! ## A consumer step is disabled when its key is absent -/

theorem rtPull_none_of_lookup_none {s : RtState} {j : SubId}
    (h : lookupRt s.subs j = none) : rtPull s j = none := by
  unfold rtPull; rw [h]

theorem rtWake_none_of_lookup_none {s : RtState} {j : SubId}
    (h : lookupRt s.subs j = none) : rtWake s j = none := by
  unfold rtWake; rw [h]

theorem rtCloseA_none_of_lookup_none {s : RtState} {j : SubId}
    (h : lookupRt s.subs j = none) : rtCloseA s j = none := by
  unfold rtCloseA; rw [h]

theorem rtCloseB_none_of_lookup_none {s : RtState} {j : SubId}
    (h : lookupRt s.subs j = none) : rtCloseB s j = none := by
  unfold rtCloseB; rw [h]

/-! ## Publisher frames

A publisher step of `i` reads `fanOut` and `lookupRt s.subs i`; so it is
insensitive to a change of `subs` away from key `i`. The per-arm lemmas
(`rtCheck_*`, `rtResolve_*`) describe each step's value on each shape of the
fan-out data; the frame lemmas combine them for the two states `s` and
`{ s with subs := updateRt s.subs j g }` (`i ≠ j`). The `_dep` pair ties the
transformed step's image to the original result `z` through one and the same
updater `h`.
-/

theorem rtCheck_none_fanout {s : RtState} {id : SubId} (hf : s.fanOut = none) :
    rtCheck s id = none := by
  unfold rtCheck; rw [hf]

theorem rtCheck_none_kind {s : RtState} {id : SubId} {f : FanOut} {name : StreamName}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.delete name) :
    rtCheck s id = none := by
  unfold rtCheck; simp [hf, hkind]

theorem rtCheck_none_decided {s : RtState} {id : SubId} {f : FanOut} {d : SubId × Bool}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = some d) :
    rtCheck s id = none := by
  unfold rtCheck; simp [hf, hkind, hd]

theorem rtCheck_none_nil {s : RtState} {id : SubId} {f : FanOut}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = none) (hrem : f.remaining = []) :
    rtCheck s id = none := by
  unfold rtCheck; simp [hf, hkind, hd, hrem]

theorem rtCheck_none_guard {s : RtState} {id k : SubId} {f : FanOut} {rest : List SubId}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = none) (hrem : f.remaining = k :: rest) (hne : k ≠ id) :
    rtCheck s id = none := by
  unfold rtCheck; simp [hf, hkind, hd, hrem, hne]

theorem rtCheck_none_lookup {s : RtState} {id : SubId} {f : FanOut} {rest : List SubId}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = none) (hrem : f.remaining = id :: rest)
    (hl : lookupRt s.subs id = none) :
    rtCheck s id = none := by
  unfold rtCheck; simp [hf, hkind, hd, hrem, hl]

theorem rtCheck_hit {s : RtState} {id : SubId} {f : FanOut} {rest : List SubId}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq} {r : RtSubscriber}
    {n : Nat}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = none) (hrem : f.remaining = id :: rest)
    (hl : lookupRt s.subs id = some r) (hp : r.policy = Policy.terminateOnLag n) :
    rtCheck s id =
      some { s with fanOut := some { f with remaining := rest, decided := some (id, decide (n ≤ r.queue.size)) } } := by
  unfold rtCheck
  simp [hf, hkind, hd, hrem, hl, hp]

theorem rtResolve_none_fanout {s : RtState} {id : SubId} (hf : s.fanOut = none) :
    rtResolve s id = none := by
  unfold rtResolve; rw [hf]

theorem rtResolve_none_decidedPublish {s : RtState} {id : SubId} {f : FanOut}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = none) :
    rtResolve s id = none := by
  unfold rtResolve; simp [hf, hkind, hd]

theorem rtResolve_none_decidedDelete {s : RtState} {id : SubId} {f : FanOut} {d : SubId × Bool}
    {name : StreamName}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.delete name)
    (hd : f.decided = some d) :
    rtResolve s id = none := by
  unfold rtResolve; simp [hf, hkind, hd]

theorem rtResolve_none_nil {s : RtState} {id : SubId} {f : FanOut} {name : StreamName}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.delete name)
    (hd : f.decided = none) (hrem : f.remaining = []) :
    rtResolve s id = none := by
  unfold rtResolve; simp [hf, hkind, hd, hrem]

theorem rtResolve_none_guard {s : RtState} {id k : SubId} {f : FanOut}
    {m : StoredMessage} {exp : Option StreamSeq} {ov : Bool}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = some (k, ov)) (hne : k ≠ id) :
    rtResolve s id = none := by
  unfold rtResolve; simp [hf, hkind, hd, hne]

theorem rtResolve_none_lookup {s : RtState} {id : SubId} {f : FanOut}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq} {ov : Bool}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = some (id, ov))
    (hl : lookupRt s.subs id = none) :
    rtResolve s id = none := by
  unfold rtResolve; simp [hf, hkind, hd, hl]

theorem rtResolve_overflow_hit {s : RtState} {id : SubId} {f : FanOut}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq} {ov : Bool}
    {r : RtSubscriber}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = some (id, ov))
    (hl : lookupRt s.subs id = some r) (hov : ov = true) :
    rtResolve s id =
      some { s with subs := updateRt s.subs id (fun _ => { r with registered := false, queue := r.queue.fail (.consumerLagged stream r.lastEnqueued) }), fanOut := some { f with decided := none, visited := f.visited ++ [(id, .overflowed)] } } := by
  unfold rtResolve
  simp [hf, hkind, hd, hl, hov]

theorem rtResolve_admit_wouldSuspend
    {s : RtState} {id : SubId} {f : FanOut}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq} {ov : Bool}
    {r : RtSubscriber} {q' : EffectQueue} {res : EffectQueue.OfferResult}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = some (id, ov))
    (hl : lookupRt s.subs id = some r) (hov : ov = false)
    (hq : r.queue.offer r.policy.capacity m = (q', res))
    (hres : res = EffectQueue.OfferResult.wouldSuspend) :
    rtResolve s id = none := by
  unfold rtResolve
  simp [hf, hkind, hd, hl, hov, hq, hres]

theorem rtResolve_admit_refused
    {s : RtState} {id : SubId} {f : FanOut}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq} {ov : Bool}
    {r : RtSubscriber} {q' : EffectQueue} {res : EffectQueue.OfferResult}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = some (id, ov))
    (hl : lookupRt s.subs id = some r) (hov : ov = false)
    (hq : r.queue.offer r.policy.capacity m = (q', res))
    (hres : res = EffectQueue.OfferResult.refused) :
    rtResolve s id =
      some { s with subs := updateRt s.subs id (fun _ => { r with queue := q', lastEnqueued := m.sequence }), fanOut := some { f with decided := none, visited := f.visited ++ [(id, .skipped)] } } := by
  unfold rtResolve
  simp [hf, hkind, hd, hl, hov, hq, hres]

theorem rtResolve_admit_accepted
    {s : RtState} {id : SubId} {f : FanOut}
    {stream : StreamName} {m : StoredMessage} {exp : Option StreamSeq} {ov : Bool}
    {r : RtSubscriber} {q' : EffectQueue} {res : EffectQueue.OfferResult}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.publish stream m exp)
    (hd : f.decided = some (id, ov))
    (hl : lookupRt s.subs id = some r) (hov : ov = false)
    (hq : r.queue.offer r.policy.capacity m = (q', res))
    (hres : res = EffectQueue.OfferResult.accepted) :
    rtResolve s id =
      some { s with subs := updateRt s.subs id (fun _ => { r with queue := q', lastEnqueued := m.sequence }), fanOut := some { f with decided := none, visited := f.visited ++ [(id, .admitted)] } } := by
  unfold rtResolve
  simp [hf, hkind, hd, hl, hov, hq, hres]

theorem rtResolve_none_deleteGuard {s : RtState} {id k : SubId} {f : FanOut}
    {rest : List SubId} {name : StreamName}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.delete name)
    (hd : f.decided = none) (hrem : f.remaining = k :: rest) (hne : k ≠ id) :
    rtResolve s id = none := by
  unfold rtResolve; simp [hf, hkind, hd, hrem, hne]

theorem rtResolve_none_deleteLookup {s : RtState} {id : SubId} {f : FanOut}
    {rest : List SubId} {name : StreamName}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.delete name)
    (hd : f.decided = none) (hrem : f.remaining = id :: rest)
    (hl : lookupRt s.subs id = none) :
    rtResolve s id = none := by
  unfold rtResolve; simp [hf, hkind, hd, hrem, hl]

theorem rtResolve_delete_hit {s : RtState} {id : SubId} {f : FanOut} {rest : List SubId}
    {name : StreamName} {r : RtSubscriber}
    (hf : s.fanOut = some f) (hkind : f.kind = FanKind.delete name)
    (hd : f.decided = none) (hrem : f.remaining = id :: rest)
    (hl : lookupRt s.subs id = some r) :
    rtResolve s id =
      some { s with subs := updateRt s.subs id (fun _ => { r with registered := false, queue := r.queue.fail (.streamNotFound name) }), fanOut := some { f with remaining := rest, visited := f.visited ++ [(id, .ended)] } } := by
  unfold rtResolve
  simp [hf, hkind, hd, hrem, hl]

/-- `check i` transforms across a change of `subs` away from key `i`: the
transformed step's result is the original's with only `fanOut` changed. -/
theorem rtCheck_frame_dep (g : RtSubscriber → RtSubscriber) (s : RtState) (i j : SubId)
    (hij : i ≠ j) (z : RtState) (hz : rtCheck s i = some z) :
    ∃ h : RtSubscriber → RtSubscriber,
      z.core = s.core ∧ z.nextId = s.nextId ∧ z.subs = updateRt s.subs i h ∧
        rtCheck { s with subs := updateRt s.subs j g } i =
          (rtCheck s i).map
            (fun w => { s with subs := updateRt (updateRt s.subs j g) i h, fanOut := w.fanOut }) := by
  have hfan : ({ s with subs := updateRt s.subs j g } : RtState).fanOut = s.fanOut := rfl
  have hrec : ({ s with subs := updateRt s.subs j g } : RtState) =
      RtState.mk s.core (updateRt s.subs j g) s.nextId s.fanOut := rfl
  rw [hrec]
  cases hf0 : s.fanOut with
  | none => rw [rtCheck_none_fanout hf0] at hz; simp at hz
  | some f =>
    cases hkind : f.kind with
    | delete name => rw [rtCheck_none_kind hf0 hkind] at hz; simp at hz
    | publish stream m exp =>
      cases hd : f.decided with
      | some d => rw [rtCheck_none_decided hf0 hkind hd] at hz; simp at hz
      | none =>
        cases hrem : f.remaining with
        | nil => rw [rtCheck_none_nil hf0 hkind hd hrem] at hz; simp at hz
        | cons k rest =>
          by_cases hki : k = i
          · rw [hki] at hrem
            cases hl : lookupRt s.subs i with
            | none => rw [rtCheck_none_lookup hf0 hkind hd hrem hl] at hz; simp at hz
            | some r =>
              cases hp : r.policy with
              | terminateOnLag n =>
                rw [rtCheck_hit hf0 hkind hd hrem hl hp] at hz
                injection hz with hc
                subst hc
                have hfanf : (RtState.mk s.core (updateRt s.subs j g) s.nextId s.fanOut).fanOut =
                    some f := by
                  show s.fanOut = some f
                  exact hf0
                have hlrec : lookupRt (updateRt s.subs j g) i = some r := by
                  rw [lookupRt_updateRt_ne _ _ _ _ hij]; exact hl
                refine ⟨fun x => x, ?_, ?_, ?_, ?_⟩
                · rfl
                · rfl
                · rw [updateRt_id]
                · rw [← hf0]
                  rw [rtCheck_hit hfanf hkind hd hrem hlrec hp,
                    rtCheck_hit hf0 hkind hd hrem hl hp]
                  simp only [Option.map_some, updateRt_id]
          · rw [rtCheck_none_guard hf0 hkind hd hrem hki] at hz; simp at hz

theorem rtCheck_frame_none (g : RtSubscriber → RtSubscriber) (s : RtState) (i j : SubId)
    (hij : i ≠ j) (hn : rtCheck s i = none) :
    rtCheck { s with subs := updateRt s.subs j g } i = none := by
  cases hf0 : s.fanOut with
  | none =>
    have hf : (RtState.mk s.core (updateRt s.subs j g) s.nextId none).fanOut = none := rfl
    rw [rtCheck_none_fanout hf]
  | some f =>
    have hf : (RtState.mk s.core (updateRt s.subs j g) s.nextId (some f)).fanOut = some f := rfl
    cases hkind : f.kind with
    | delete name => rw [rtCheck_none_kind hf hkind]
    | publish stream m exp =>
      cases hd : f.decided with
      | some d => rw [rtCheck_none_decided hf hkind hd]
      | none =>
        cases hrem : f.remaining with
        | nil => rw [rtCheck_none_nil hf hkind hd hrem]
        | cons k rest =>
          by_cases hki : k = i
          · rw [hki] at hrem
            cases hl : lookupRt s.subs i with
            | none =>
              have hlrec : lookupRt (updateRt s.subs j g) i = none := by
                rw [lookupRt_updateRt_ne _ _ _ _ hij]; exact hl
              rw [rtCheck_none_lookup hf hkind hd hrem hlrec]
            | some r =>
              cases hp : r.policy with
              | terminateOnLag n =>
                exact absurd (rtCheck_hit hf0 hkind hd hrem hl hp) (by rw [hn]; simp)
          · rw [rtCheck_none_guard hf hkind hd hrem hki]

/-! ## The `rtResolve` frames -/

theorem rtResolve_frame_dep (g : RtSubscriber → RtSubscriber) (s : RtState) (i j : SubId)
    (hij : i ≠ j) (z : RtState) (hz : rtResolve s i = some z) :
    ∃ h : RtSubscriber → RtSubscriber,
      z.core = s.core ∧ z.nextId = s.nextId ∧ z.subs = updateRt s.subs i h ∧
        rtResolve { s with subs := updateRt s.subs j g } i =
          (rtResolve s i).map
            (fun w => { s with subs := updateRt (updateRt s.subs j g) i h, fanOut := w.fanOut }) := by
  have hrec : ({ s with subs := updateRt s.subs j g } : RtState) =
      RtState.mk s.core (updateRt s.subs j g) s.nextId s.fanOut := rfl
  rw [hrec]
  cases hf0 : s.fanOut with
  | none => rw [rtResolve_none_fanout hf0] at hz; simp at hz
  | some f =>
    cases hkind : f.kind with
    | publish stream m exp =>
      cases hd : f.decided with
      | none => rw [rtResolve_none_decidedPublish hf0 hkind hd] at hz; simp at hz
      | some d =>
        cases d with
        | mk kk ov =>
          by_cases hki : kk = i
          · rw [hki] at hd
            cases hl0 : lookupRt s.subs i with
            | none => rw [rtResolve_none_lookup hf0 hkind hd hl0] at hz; simp at hz
            | some r =>
              have hfanf : (RtState.mk s.core (updateRt s.subs j g) s.nextId s.fanOut).fanOut =
                  some f := by
                show s.fanOut = some f
                exact hf0
              have hlrec : lookupRt (updateRt s.subs j g) i = some r := by
                rw [lookupRt_updateRt_ne _ _ _ _ hij]; exact hl0
              cases ov with
              | true =>
                rw [rtResolve_overflow_hit hf0 hkind hd hl0 rfl] at hz
                injection hz with hc
                subst hc
                rw [← hf0]
                rw [rtResolve_overflow_hit hfanf hkind hd hlrec rfl,
                  rtResolve_overflow_hit hf0 hkind hd hl0 rfl]
                refine ⟨fun _ => { r with registered := false, queue := r.queue.fail (.consumerLagged stream r.lastEnqueued) }, ?_, ?_, ?_, ?_⟩
                · rfl
                · rfl
                · rfl
                · simp only [Option.map_some]
              | false =>
                cases hq : r.queue.offer r.policy.capacity m with
                | mk q' res =>
                  cases hres : res with
                  | wouldSuspend =>
                    rw [rtResolve_admit_wouldSuspend hf0 hkind hd hl0 rfl hq hres] at hz
                    simp at hz
                  | refused =>
                    rw [rtResolve_admit_refused hf0 hkind hd hl0 rfl hq hres] at hz
                    rw [← hf0]
                    rw [rtResolve_admit_refused hf0 hkind hd hl0 rfl hq hres]
                    rw [rtResolve_admit_refused hfanf hkind hd hlrec rfl hq hres]
                    injection hz with hc
                    subst hc
                    refine ⟨fun _ => { r with queue := q', lastEnqueued := m.sequence },
                      ?_, ?_, ?_, ?_⟩
                    · rfl
                    · rfl
                    · rfl
                    · simp only [Option.map_some]
                  | accepted =>
                    rw [rtResolve_admit_accepted hf0 hkind hd hl0 rfl hq hres] at hz
                    rw [← hf0]
                    rw [rtResolve_admit_accepted hf0 hkind hd hl0 rfl hq hres]
                    rw [rtResolve_admit_accepted hfanf hkind hd hlrec rfl hq hres]
                    injection hz with hc
                    subst hc
                    refine ⟨fun _ => { r with queue := q', lastEnqueued := m.sequence },
                      ?_, ?_, ?_, ?_⟩
                    · rfl
                    · rfl
                    · rfl
                    · simp only [Option.map_some]
          · rw [rtResolve_none_guard hf0 hkind hd hki] at hz; simp at hz
    | delete name =>
      cases hd : f.decided with
      | some d => rw [rtResolve_none_decidedDelete hf0 hkind hd] at hz; simp at hz
      | none =>
        cases hrem : f.remaining with
        | nil => rw [rtResolve_none_nil hf0 hkind hd hrem] at hz; simp at hz
        | cons k rest =>
          by_cases hki : k = i
          · rw [hki] at hrem
            cases hl0 : lookupRt s.subs i with
            | none => rw [rtResolve_none_deleteLookup hf0 hkind hd hrem hl0] at hz; simp at hz
            | some r =>
              have hfanf : (RtState.mk s.core (updateRt s.subs j g) s.nextId s.fanOut).fanOut =
                  some f := by
                show s.fanOut = some f
                exact hf0
              have hlrec : lookupRt (updateRt s.subs j g) i = some r := by
                rw [lookupRt_updateRt_ne _ _ _ _ hij]; exact hl0
              rw [rtResolve_delete_hit hf0 hkind hd hrem hl0] at hz
              rw [← hf0]
              rw [rtResolve_delete_hit hf0 hkind hd hrem hl0]
              rw [rtResolve_delete_hit hfanf hkind hd hrem hlrec]
              injection hz with hc
              subst hc
              refine ⟨fun _ => { r with registered := false, queue := r.queue.fail (.streamNotFound name) }, ?_, ?_, ?_, ?_⟩
              · rfl
              · rfl
              · rfl
              · simp only [Option.map_some]
          · rw [rtResolve_none_deleteGuard hf0 hkind hd hrem hki] at hz; simp at hz

theorem rtResolve_frame_none (g : RtSubscriber → RtSubscriber) (s : RtState) (i j : SubId)
    (hij : i ≠ j) (hn : rtResolve s i = none) :
    rtResolve { s with subs := updateRt s.subs j g } i = none := by
  cases hf0 : s.fanOut with
  | none =>
    have hf : (RtState.mk s.core (updateRt s.subs j g) s.nextId none).fanOut = none := rfl
    rw [rtResolve_none_fanout hf]
  | some f =>
    have hf : (RtState.mk s.core (updateRt s.subs j g) s.nextId (some f)).fanOut = some f := rfl
    cases hkind : f.kind with
    | delete name =>
      cases hd : f.decided with
      | some d => rw [rtResolve_none_decidedDelete hf hkind hd]
      | none =>
        cases hrem : f.remaining with
        | nil => rw [rtResolve_none_nil hf hkind hd hrem]
        | cons k rest =>
          by_cases hki : k = i
          · rw [hki] at hrem
            by_cases hl0 : lookupRt s.subs i = none
            · have hlrec : lookupRt (updateRt s.subs j g) i = none := by
                rw [lookupRt_updateRt_ne _ _ _ _ hij]; exact hl0
              rw [rtResolve_none_deleteLookup hf hkind hd hrem hlrec]
            · have hlne : lookupRt s.subs i ≠ none := hl0
              cases hl : lookupRt s.subs i with
              | none => exact absurd hl hlne
              | some r =>
                exact absurd (rtResolve_delete_hit hf0 hkind hd hrem hl) (by rw [hn]; simp)
          · rw [rtResolve_none_deleteGuard hf hkind hd hrem hki]
    | publish stream m exp =>
      cases hd : f.decided with
      | none => rw [rtResolve_none_decidedPublish hf hkind hd]
      | some d =>
        cases d with
        | mk k ov =>
          by_cases hki : k = i
          · rw [hki] at hd
            by_cases hl0 : lookupRt s.subs i = none
            · have hlrec : lookupRt (updateRt s.subs j g) i = none := by
                rw [lookupRt_updateRt_ne _ _ _ _ hij]; exact hl0
              rw [rtResolve_none_lookup hf hkind hd hlrec]
            · have hlne : lookupRt s.subs i ≠ none := hl0
              cases hl : lookupRt s.subs i with
              | none => exact absurd hl hlne
              | some r =>
                cases ov with
                | true =>
                  exact absurd (rtResolve_overflow_hit hf0 hkind hd hl rfl) (by rw [hn]; simp)
                | false =>
                  cases hq : r.queue.offer r.policy.capacity m with
                  | mk q' res =>
                    cases hres : res with
                    | wouldSuspend =>
                      have hlrec : lookupRt (updateRt s.subs j g) i = some r := by
                        rw [lookupRt_updateRt_ne _ _ _ _ hij]; exact hl
                      rw [rtResolve_admit_wouldSuspend hf hkind hd hlrec rfl hq hres]
                    | refused =>
                      exact absurd
                        (rtResolve_admit_refused hf0 hkind hd hl rfl hq hres)
                        (by rw [hn]; simp)
                    | accepted =>
                      exact absurd
                        (rtResolve_admit_accepted hf0 hkind hd hl rfl hq hres)
                        (by rw [hn]; simp)
          · rw [rtResolve_none_guard hf hkind hd hki]

/-! ## The two commutations, assembled from the packages -/

/-- A consumer step of `i` and a consumer step of `j` (`i ≠ j`) commute, given
that each step is determined by its own subscriber entry. -/
theorem bindStep_pair_comm (X Y : RtState → SubId → Option RtState)
    (nilX : ∀ u : RtState, ∀ jj : SubId, lookupRt u.subs jj = none → X u jj = none)
    (hnX : ∀ u v : RtState, ∀ jj : SubId, lookupRt v.subs jj = lookupRt u.subs jj →
      X u jj = none → X v jj = none)
    (trX : ∀ u v : RtState, ∀ jj : SubId, ∀ w : RtState,
      lookupRt v.subs jj = lookupRt u.subs jj → X u jj = some w →
        ∃ r' : RtSubscriber, w = { u with subs := updateRt u.subs jj (fun _ => r') } ∧
          X v jj = some { v with subs := updateRt v.subs jj (fun _ => r') })
    (niY : ∀ u v : RtState, ∀ jj : SubId, lookupRt v.subs jj = lookupRt u.subs jj →
      Y u jj = none → Y v jj = none)
    (trY : ∀ u v : RtState, ∀ jj : SubId, ∀ w : RtState,
      lookupRt v.subs jj = lookupRt u.subs jj → Y u jj = some w →
        ∃ r' : RtSubscriber, w = { u with subs := updateRt u.subs jj (fun _ => r') } ∧
          Y v jj = some { v with subs := updateRt v.subs jj (fun _ => r') })
    (s : RtState) (i j : SubId) (hij : i ≠ j) :
    (X s i).bind (fun s' => Y s' j) = (Y s j).bind (fun s' => X s' i) := by
  cases h1 : X s i with
  | none =>
    cases h2 : Y s j with
    | none => rfl
    | some u =>
      obtain ⟨rwit, huform, -⟩ := trY s s j u rfl h2
      subst huform
      have hle : lookupRt s.subs i =
          lookupRt (updateRt s.subs j (fun x => rwit)) i :=
        (lookupRt_updateRt_ne _ _ _ _ hij).symm
      exact (hnX s (RtState.mk s.core (updateRt s.subs j (fun x => rwit)) s.nextId s.fanOut) i
        hle.symm h1).symm
  | some s₁ =>
    obtain ⟨rx, hs₁, -⟩ := trX s s i s₁ rfl h1
    cases h2 : Y s j with
    | none =>
      have hy : Y s₁ j = none :=
        niY s s₁ j (by rw [hs₁]; exact lookupRt_updateRt_ne _ _ _ _ (Ne.symm hij)) h2
      show Y s₁ j = none
      exact hy
    | some u =>
      obtain ⟨ry, huform, hyS₁⟩ :=
        trY s s₁ j u (by rw [hs₁]; exact lookupRt_updateRt_ne _ _ _ _ (Ne.symm hij)) h2
      obtain ⟨r₂, hs₁₂, hxu⟩ :=
        trX s u i s₁ (by rw [huform]; exact lookupRt_updateRt_ne _ _ _ _ hij) h1
      show Y s₁ j = X u i
      have e1 : lookupRt s₁.subs i = Option.map (fun _ => rx) (lookupRt s.subs i) := by
        rw [hs₁]; exact lookupRt_updateRt_self _ _ _
      have e2 : lookupRt s₁.subs i = Option.map (fun _ => r₂) (lookupRt s.subs i) := by
        rw [hs₁₂]; exact lookupRt_updateRt_self _ _ _
      have hrr : r₂ = rx := by
        cases hlj : lookupRt s.subs i with
        | none =>
          have hnone : X s i = none := nilX s i hlj
          rw [hnone] at h1
          simp at h1
        | some rr =>
          rw [hlj] at e1 e2
          simp only [Option.map_some] at e1 e2
          have hBE : some rx = some r₂ := e1.symm.trans e2
          injection hBE with h'
          exact h'.symm
      subst hrr
      rw [hyS₁, hxu, hs₁, huform]
      show (some { core := s.core,
                    subs := updateRt (updateRt s.subs i (fun _ => r₂)) j (fun _ => ry),
                    nextId := s.nextId, fanOut := s.fanOut } :
              Option RtState) =
            some { core := s.core,
                   subs := updateRt (updateRt s.subs j (fun _ => ry)) i (fun _ => r₂),
                   nextId := s.nextId, fanOut := s.fanOut }
      rw [updateRt_updateRt_comm hij]

/-- A consumer step of `j` and a publisher step of `i` (`i ≠ j`) commute, given
the consumer package and the publisher frames. -/
theorem bindStep_pub_comm (X : RtState → SubId → Option RtState)
    (nilX : ∀ u : RtState, ∀ jj : SubId, lookupRt u.subs jj = none → X u jj = none)
    (niX : ∀ u v : RtState, ∀ jj : SubId, lookupRt v.subs jj = lookupRt u.subs jj →
      X u jj = none → X v jj = none)
    (trX : ∀ u v : RtState, ∀ jj : SubId, ∀ w : RtState,
      lookupRt v.subs jj = lookupRt u.subs jj → X u jj = some w →
        ∃ r' : RtSubscriber, w = { u with subs := updateRt u.subs jj (fun _ => r') } ∧
          X v jj = some { v with subs := updateRt v.subs jj (fun _ => r') })
    (pub : RtState → SubId → Option RtState)
    (frNone : ∀ (g : RtSubscriber → RtSubscriber) (u : RtState) (ii jj : SubId), ii ≠ jj →
      pub u ii = none → pub { u with subs := updateRt u.subs jj g } ii = none)
    (frDep : ∀ (g : RtSubscriber → RtSubscriber) (u : RtState) (ii jj : SubId), ii ≠ jj →
      ∀ z : RtState, pub u ii = some z →
        ∃ h : RtSubscriber → RtSubscriber,
          z.core = u.core ∧ z.nextId = u.nextId ∧ z.subs = updateRt u.subs ii h ∧
            pub { u with subs := updateRt u.subs jj g } ii =
              (pub u ii).map
                (fun w => { u with subs := updateRt (updateRt u.subs jj g) ii h, fanOut := w.fanOut }))
    (s : RtState) (i j : SubId) (hij : i ≠ j) :
    (X s j).bind (fun s' => pub s' i) = (pub s i).bind (fun s' => X s' j) := by
  cases h2 : pub s i with
  | none =>
    cases h1 : X s j with
    | none => rfl
    | some s₁ =>
      obtain ⟨rx, hs₁, -⟩ := trX s s j s₁ rfl h1
      subst hs₁
      exact frNone (fun _ => rx) s i j hij h2
  | some u =>
    cases h1 : X s j with
    | none =>
      obtain ⟨h₀, -, -, hu3, -⟩ := frDep (fun x => x) s i j hij u h2
      have hle : lookupRt u.subs j = lookupRt s.subs j := by
        rw [hu3]
        exact lookupRt_updateRt_ne _ _ _ _ (Ne.symm hij)
      exact (niX s u j hle h1).symm
    | some s₁ =>
      obtain ⟨rx, hs₁, -⟩ := trX s s j s₁ rfl h1
      obtain ⟨h, hu1, hu2, hu3, frEq⟩ := frDep (fun _ => rx) s i j hij u h2
      have hlu : lookupRt u.subs j = lookupRt s.subs j := by
        rw [hu3]
        exact lookupRt_updateRt_ne _ _ _ _ (Ne.symm hij)
      obtain ⟨r₂, hs₁₂, hxu⟩ := trX s u j s₁ hlu h1
      have hleJ : lookupRt ({ s with subs := updateRt s.subs j (fun _ => rx) } : RtState).subs j =
          Option.map (fun _ => rx) (lookupRt s.subs j) := lookupRt_updateRt_self _ _ _
      have hleJ' : lookupRt ({ s with subs := updateRt s.subs j (fun _ => r₂) } : RtState).subs j =
          Option.map (fun _ => r₂) (lookupRt s.subs j) := lookupRt_updateRt_self _ _ _
      rw [← hs₁] at hleJ
      rw [← hs₁₂] at hleJ'
      have hrr : r₂ = rx := by
        cases hlj : lookupRt s.subs j with
        | none =>
          have hnone : X s j = none := nilX s j hlj
          rw [hnone] at h1
          simp at h1
        | some rr =>
          rw [hlj] at hleJ hleJ'
          simp only [Option.map_some] at hleJ hleJ'
          injection hleJ.symm.trans hleJ' with h'
          exact h'.symm
      subst hs₁
      rw [hrr] at hxu
      show pub { s with subs := updateRt s.subs j (fun _ => rx) } i = X u j
      rw [frEq]
      rw [h2]
      rw [hxu]
      rw [hu1, hu2, hu3, updateRt_updateRt_comm hij]
      simp only [Option.map_some]

/-! ## The frozen statements (snapshot r4, block `RtCommute.lean`) -/

/-- Two runtime steps taken in sequence. -/
def bindStep (s : RtState) (a b : RtLabel) : Option RtState :=
  (rtStep s a).bind (fun s' => rtStep s' b)

/-! ### The consumer and publisher packages, per label

A consumer label of `id` (`pull`/`wake`/`closeA`/`closeB`) is a step function that reads and
writes only the entry at `id`; a publisher label of `id` (`check`/`resolve`) is one that reads
`fanOut` and the entry at `id` and writes `fanOut` and that entry. The two records below package
exactly the hypotheses `bindStep_pair_comm` and `bindStep_pub_comm` consume, and the two
`*Fun` lemmas turn a label disjunction into the corresponding packaged function. -/

/-- A step function determined by, and writing only, the subscriber entry at its key. -/
structure ConsumerPkg (X : RtState → SubId → Option RtState) : Prop where
  nil : ∀ (u : RtState) (jj : SubId), lookupRt u.subs jj = none → X u jj = none
  ni : ∀ (u v : RtState) (jj : SubId), lookupRt v.subs jj = lookupRt u.subs jj →
    X u jj = none → X v jj = none
  tr : ∀ (u v : RtState) (jj : SubId) (w : RtState),
    lookupRt v.subs jj = lookupRt u.subs jj → X u jj = some w →
      ∃ r' : RtSubscriber, w = { u with subs := updateRt u.subs jj (fun _ => r') } ∧
        X v jj = some { v with subs := updateRt v.subs jj (fun _ => r') }

/-- A step function insensitive to a change of `subs` away from its key. -/
structure PubPkg (P : RtState → SubId → Option RtState) : Prop where
  frNone : ∀ (g : RtSubscriber → RtSubscriber) (u : RtState) (ii jj : SubId), ii ≠ jj →
    P u ii = none → P { u with subs := updateRt u.subs jj g } ii = none
  frDep : ∀ (g : RtSubscriber → RtSubscriber) (u : RtState) (ii jj : SubId), ii ≠ jj →
    ∀ z : RtState, P u ii = some z →
      ∃ h : RtSubscriber → RtSubscriber,
        z.core = u.core ∧ z.nextId = u.nextId ∧ z.subs = updateRt u.subs ii h ∧
          P { u with subs := updateRt u.subs jj g } ii =
            (P u ii).map
              (fun w => { u with subs := updateRt (updateRt u.subs jj g) ii h, fanOut := w.fanOut })

theorem consumerPkg_rtPull : ConsumerPkg rtPull :=
  ⟨fun _ _ h => rtPull_none_of_lookup_none h, fun _ _ _ h hn => rtPull_none_inval h hn,
    fun _ _ _ _ h hw => rtPull_transfer h hw⟩

theorem consumerPkg_rtWake : ConsumerPkg rtWake :=
  ⟨fun _ _ h => rtWake_none_of_lookup_none h, fun _ _ _ h hn => rtWake_none_inval h hn,
    fun _ _ _ _ h hw => rtWake_transfer h hw⟩

theorem consumerPkg_rtCloseA : ConsumerPkg rtCloseA :=
  ⟨fun _ _ h => rtCloseA_none_of_lookup_none h, fun _ _ _ h hn => rtCloseA_none_inval h hn,
    fun _ _ _ _ h hw => rtCloseA_transfer h hw⟩

theorem consumerPkg_rtCloseB : ConsumerPkg rtCloseB :=
  ⟨fun _ _ h => rtCloseB_none_of_lookup_none h, fun _ _ _ h hn => rtCloseB_none_inval h hn,
    fun _ _ _ _ h hw => rtCloseB_transfer h hw⟩

theorem pubPkg_rtCheck : PubPkg rtCheck :=
  ⟨fun g u ii jj hne hn => rtCheck_frame_none g u ii jj hne hn,
    fun g u ii jj hne z hz => rtCheck_frame_dep g u ii jj hne z hz⟩

theorem pubPkg_rtResolve : PubPkg rtResolve :=
  ⟨fun g u ii jj hne hn => rtResolve_frame_none g u ii jj hne hn,
    fun g u ii jj hne z hz => rtResolve_frame_dep g u ii jj hne z hz⟩

/-- Each of the four consumer labels of `id` is `rtStep · ·` for a packaged consumer function. -/
theorem consumerFun (c : RtLabel) (id : SubId)
    (hc : c = .pull id ∨ c = .wake id ∨ c = .closeA id ∨ c = .closeB id) :
    ∃ X : RtState → SubId → Option RtState, ConsumerPkg X ∧ ∀ u : RtState, rtStep u c = X u id := by
  rcases hc with h | h | h | h <;> subst h
  · exact ⟨rtPull, consumerPkg_rtPull, fun _ => rfl⟩
  · exact ⟨rtWake, consumerPkg_rtWake, fun _ => rfl⟩
  · exact ⟨rtCloseA, consumerPkg_rtCloseA, fun _ => rfl⟩
  · exact ⟨rtCloseB, consumerPkg_rtCloseB, fun _ => rfl⟩

/-- Each of the two publisher labels of `id` is `rtStep · ·` for a packaged publisher function. -/
theorem publisherFun (p : RtLabel) (id : SubId) (hp : p = .check id ∨ p = .resolve id) :
    ∃ P : RtState → SubId → Option RtState, PubPkg P ∧ ∀ u : RtState, rtStep u p = P u id := by
  rcases hp with h | h <;> subst h
  · exact ⟨rtCheck, pubPkg_rtCheck, fun _ => rfl⟩
  · exact ⟨rtResolve, pubPkg_rtResolve, fun _ => rfl⟩

/-- A consumer step of `j` and a publisher step of `i` commute when `i ≠ j`. The `RtInv`
hypothesis of the frozen statement is not used: the disjointness is unconditional. -/
theorem commute_consumer_publisher (s : RtState) (_hinv : RtInv s) (i j : SubId) (hij : i ≠ j)
    (c p : RtLabel) (hc : c = .pull j ∨ c = .wake j ∨ c = .closeA j ∨ c = .closeB j)
    (hp : p = .check i ∨ p = .resolve i) : bindStep s c p = bindStep s p c := by
  obtain ⟨X, pX, hX⟩ := consumerFun c j hc
  obtain ⟨P, pP, hP⟩ := publisherFun p i hp
  unfold bindStep
  simp only [hX, hP]
  exact bindStep_pub_comm X pX.nil pX.ni pX.tr P pP.frNone pP.frDep s i j hij

/-- Two consumer steps of distinct subscribers commute. The `RtInv` hypothesis of the frozen
statement is not used. -/
theorem commute_consumers (s : RtState) (_hinv : RtInv s) (i j : SubId) (hij : i ≠ j)
    (c c' : RtLabel) (hc : c = .pull i ∨ c = .wake i ∨ c = .closeA i ∨ c = .closeB i)
    (hc' : c' = .pull j ∨ c' = .wake j ∨ c' = .closeA j ∨ c' = .closeB j) :
    bindStep s c c' = bindStep s c' c := by
  obtain ⟨X, pX, hX⟩ := consumerFun c i hc
  obtain ⟨Y, pY, hY⟩ := consumerFun c' j hc'
  unfold bindStep
  simp only [hX, hY]
  exact bindStep_pair_comm X Y pX.nil pX.ni pX.tr pY.ni pY.tr s i j hij


end EffectNatsSubstrate
