import EffectNatsSubstrate.SubStatements

/-!
# SA5h — the history-extended model

The global form of T8′ (slice document §9.2): what a registered subscriber can
see is the prefix its registration materialised followed by exactly the
matching messages published since. Retained storage cannot state it (rollup,
pruning, and deletion forget messages a buffer still holds), so the statement
lives on a proof-only extension of the state — an Abadi–Lamport history
variable: `committed`, every successful publish in order, never pruned; and
`regs`, per registration, the history index at that moment and the `observed`
prefix. `applyH` is `apply` on `base` plus the two appends; `erase` drops the
ledger. AV1 (`applyH_erase`) and AV2 (`applyH_lift`, `reachableSub_lift`)
show the ledger constrains nothing; `visible_global` is the global T8′;
`entries_committed` is provenance. Nothing here is executed, traced, or
exported.
-/

namespace EffectNatsSubstrate

/-- What a registration recorded: the ledger length at that moment (live entries
start after it — an index, not a sequence head, because a re-created stream
restarts at sequence 1) and the `observed` prefix it materialised. -/
structure RegInfo where
  index : Nat
  initial : List Observed

structure SubStateH where
  base : SubState
  committed : List (StreamName × StoredMessage)
  regs : List (SubId × RegInfo)

def initialSubH : SubStateH := { base := initialSub, committed := [], regs := [] }

def erase (sH : SubStateH) : SubState := sH.base

def lookupReg : List (SubId × RegInfo) → SubId → Option RegInfo
  | [], _ => none
  | (i, r) :: rest, id => if i = id then some r else lookupReg rest id

/-- The stored message a successful publish label commits. -/
def labelMessage : Label → Option (StreamName × StoredMessage)
  | .op (.publish stream subject payload headers _ now) (.ok (.sequence seq)) =>
      some (stream, publishedMessage subject seq payload headers now)
  | _ => none

def committedAfter (sH : SubStateH) (l : Label) : List (StreamName × StoredMessage) :=
  match labelMessage l with
  | some e => sH.committed ++ [e]
  | none => sH.committed

def regsAfter (sH : SubStateH) (l : Label) : List (SubId × RegInfo) :=
  match l with
  | .register stream opts _ id (.ok .unit) =>
    match lookupStream sH.base.core stream with
    | some st =>
        sH.regs ++ [(id, { index := sH.committed.length, initial := replayObserved st.messages opts })]
    | none => sH.regs
  | _ => sH.regs

def applyH (sH : SubStateH) (l : Label) : Option SubStateH :=
  match apply sH.base l with
  | none => none
  | some base' => some { base := base', committed := committedAfter sH l, regs := regsAfter sH l }

def NextH (sH : SubStateH) (l : Label) (sH' : SubStateH) : Prop := applyH sH l = some sH'

inductive ReachableSubH : SubStateH → Prop
  | init : ReachableSubH initialSubH
  | step {sH sH' : SubStateH} {l : Label} : ReachableSubH sH → NextH sH l sH' → ReachableSubH sH'

/-- A ledger entry the subscriber would have been offered. -/
def liveKeep (sub : Subscriber) (e : StreamName × StoredMessage) : Bool :=
  e.1 == sub.stream && matchesAny sub.filters e.2.subject

def liveOf (committed : List (StreamName × StoredMessage)) (sub : Subscriber) (r : RegInfo) :
    List StoredMessage :=
  ((committed.drop r.index).filter (liveKeep sub)).map (·.2)

/-- The matching messages published since the subscriber registered. -/
def liveEntries (sH : SubStateH) (id : SubId) : List StoredMessage :=
  match lookupSub sH.base.subs id, lookupReg sH.regs id with
  | some sub, some r => liveOf sH.committed sub r
  | _, _ => []

/-! ## AV1 and AV2 — the ledger constrains nothing -/

theorem erase_initialSubH : erase initialSubH = initialSub := rfl

theorem applyH_erase (sH : SubStateH) (l : Label) :
    (applyH sH l).map erase = apply (erase sH) l := by
  unfold applyH erase
  cases apply sH.base l with
  | none => rfl
  | some base' => rfl

theorem applyH_lift {sH : SubStateH} {l : Label} {s' : SubState} (_h : ReachableSubH sH)
    (hstep : apply (erase sH) l = some s') :
    ∃ sH', applyH sH l = some sH' ∧ erase sH' = s' := by
  refine ⟨{ base := s', committed := committedAfter sH l, regs := regsAfter sH l }, ?_, rfl⟩
  have hstep' : apply sH.base l = some s' := hstep
  unfold applyH
  simp only [hstep']

theorem reachableSubH_erase {sH : SubStateH} (h : ReachableSubH sH) : ReachableSub (erase sH) := by
  induction h with
  | init => exact ReachableSub.init
  | @step sH sH' l _ hnext ih =>
    have hm := applyH_erase sH l
    rw [hnext] at hm
    exact ReachableSub.step ih hm.symm

theorem reachableSub_lift {s : SubState} (h : ReachableSub s) :
    ∃ sH, ReachableSubH sH ∧ erase sH = s :=
  reachableSub_all (P := fun s => ∃ sH, ReachableSubH sH ∧ erase sH = s)
    ⟨initialSubH, ReachableSubH.init, rfl⟩
    (fun _ _ ih hnext => by
      obtain ⟨sH, hr, rfl⟩ := ih
      obtain ⟨sH', hs, he⟩ := applyH_lift hr hnext
      exact ⟨sH', ReachableSubH.step hr hs, he⟩) h

/-! ## Ledger lookups and `liveOf` through an append -/

theorem lookupReg_append_fresh :
    ∀ {regs : List (SubId × RegInfo)} {id : SubId} {r : RegInfo},
      (∀ q ∈ regs, q.1 ≠ id) → lookupReg (regs ++ [(id, r)]) id = some r
  | [], _, _, _ => by simp [lookupReg]
  | (i, r₀) :: rest, id, r, hfresh => by
    have hi : i ≠ id := hfresh (i, r₀) List.mem_cons_self
    simp only [List.cons_append, lookupReg, if_neg hi]
    exact lookupReg_append_fresh (fun q hq => hfresh q (List.mem_cons_of_mem _ hq))

theorem lookupReg_append_of_some :
    ∀ {regs : List (SubId × RegInfo)} {id : SubId} {r : RegInfo} (l : List (SubId × RegInfo)),
      lookupReg regs id = some r → lookupReg (regs ++ l) id = some r
  | [], _, _, _, h => by cases h
  | (i, r₀) :: rest, id, r, l, h => by
    by_cases hi : i = id
    · subst hi
      simp only [lookupReg] at h
      cases h
      simp [lookupReg]
    · simp only [lookupReg, if_neg hi] at h
      simp only [List.cons_append, lookupReg, if_neg hi]
      exact lookupReg_append_of_some l h

theorem liveOf_append_of_neg {committed : List (StreamName × StoredMessage)} {sub : Subscriber}
    {r : RegInfo} {e : StreamName × StoredMessage} (hat : r.index ≤ committed.length)
    (hk : liveKeep sub e = false) : liveOf (committed ++ [e]) sub r = liveOf committed sub r := by
  unfold liveOf
  have hneg : ¬ (liveKeep sub e = true) := by simp [hk]
  rw [List.drop_append_of_le_length hat, List.filter_append,
    List.filter_cons_of_neg (p := liveKeep sub) (a := e) hneg, List.filter_nil, List.append_nil]

theorem liveOf_append_of_pos {committed : List (StreamName × StoredMessage)} {sub : Subscriber}
    {r : RegInfo} {e : StreamName × StoredMessage} (hat : r.index ≤ committed.length)
    (hk : liveKeep sub e = true) : liveOf (committed ++ [e]) sub r = liveOf committed sub r ++ [e.2] := by
  unfold liveOf
  rw [List.drop_append_of_le_length hat, List.filter_append,
    List.filter_cons_of_pos (p := liveKeep sub) (a := e) hk, List.filter_nil, List.map_append]
  rfl

theorem liveOf_at_length (committed : List (StreamName × StoredMessage)) (sub : Subscriber)
    (initial : List Observed) :
    liveOf committed sub { index := committed.length, initial := initial } = [] := by
  unfold liveOf
  rw [List.drop_length]
  rfl

/-! ## Core shapes the ledger needs -/

theorem lookupStream_removeStream_self : ∀ (s : JSState) (name : StreamName),
    lookupStream (removeStream s name) name = none
  | [], _ => rfl
  | (n, st) :: rest, name => by
    by_cases hn : n = name
    · simp only [removeStream, if_pos hn]
      exact lookupStream_removeStream_self rest name
    · simp only [removeStream, if_neg hn, lookupStream]
      exact lookupStream_removeStream_self rest name

theorem createStep_ok_shape {s s' : JSState} {raw : RawStreamConfig} {r : Ret}
    (h : createStep s raw = .ok (s', r)) :
    s' = s ∨ ∃ config, validate raw = .ok config ∧ lookupStream s config.name = none ∧
      s' = insertStream s config.name { config := config, messages := [], nextSequence := 1 } := by
  unfold createStep at h
  split at h
  · cases h
  · rename_i config hval
    split at h
    · split at h
      · cases h; exact Or.inl rfl
      · cases h
    · rename_i hlook
      cases h
      exact Or.inr ⟨config, hval, hlook, rfl⟩

theorem getStep_ok_eq {s s' : JSState} {name : StreamName} {r : Ret}
    (h : getStep s name = .ok (s', r)) : s' = s := by
  unfold getStep at h
  split at h
  · cases h; rfl
  · cases h

theorem lastMsgStep_ok_eq {s s' : JSState} {stream : StreamName} {subject : SubjectName} {r : Ret}
    (h : lastMsgStep s stream subject = .ok (s', r)) : s' = s := by
  unfold lastMsgStep at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

theorem mem_updateSub_eq :
    ∀ {subs : List (SubId × Subscriber)} {id : SubId} {f : Subscriber → Subscriber}
      {p : SubId × Subscriber},
      p ∈ updateSub subs id f → p ∈ subs ∨ (p.1 = id ∧ ∃ sub, (id, sub) ∈ subs ∧ p.2 = f sub)
  | [], _, _, _, h => by cases h
  | (i, sub) :: rest, id, f, p, h => by
    by_cases hi : i = id
    · subst hi
      simp only [updateSub] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨rfl, sub, List.mem_cons_self, rfl⟩
      · rcases mem_updateSub_eq h with h1 | ⟨hp1, sub', h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨hp1, sub', List.mem_cons_of_mem _ h1, h2⟩
    · simp only [updateSub, if_neg hi] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_updateSub_eq h with h1 | ⟨hp1, sub', h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨hp1, sub', List.mem_cons_of_mem _ h1, h2⟩

/-! ## The ledger invariant -/

/-- Every stored message is in the ledger; every ledger record is for an assigned id;
every subscriber has a record whose index is inside the ledger, satisfies the global
equation while registered, and sees only committed entries. -/
structure HistInv (sH : SubStateH) : Prop where
  coreCommitted : ∀ stream st, lookupStream sH.base.core stream = some st →
    ∀ m ∈ st.messages, (stream, m) ∈ sH.committed
  regsBelow : ∀ q ∈ sH.regs, q.1 < sH.base.nextId
  subs : ∀ p ∈ sH.base.subs, ∃ r, lookupReg sH.regs p.1 = some r ∧ r.index ≤ sH.committed.length ∧
    (p.2.registered = true →
      visible p.2 = r.initial ++ (liveOf sH.committed p.2 r).map Observed.entry) ∧
    (∀ m, Observed.entry m ∈ visible p.2 → (p.2.stream, m) ∈ sH.committed)

theorem histInv_of_same {sH : SubStateH} {base' : SubState} (hinv : HistInv sH)
    (hcore : ∀ stream st, lookupStream base'.core stream = some st →
      ∀ m ∈ st.messages, (stream, m) ∈ sH.committed)
    (hsubs : base'.subs = sH.base.subs) (hnext : base'.nextId = sH.base.nextId) :
    HistInv { base := base', committed := sH.committed, regs := sH.regs } := by
  refine ⟨hcore, ?_, ?_⟩
  · intro q hq
    show q.1 < base'.nextId
    rw [hnext]
    exact hinv.regsBelow q hq
  · intro p hp
    have hp' : p ∈ sH.base.subs := by
      rw [← hsubs]
      exact hp
    exact hinv.subs p hp'

theorem histInv_create {sH : SubStateH} {raw : RawStreamConfig} {core' : JSState} {r : Ret}
    (hinv : HistInv sH) (hstep : step sH.base.core (.createStream raw) = .ok (core', r)) :
    HistInv { base := afterOp deliverOne sH.base core' (.createStream raw) r,
              committed := committedAfter sH (.op (.createStream raw) (.ok r)),
              regs := regsAfter sH (.op (.createStream raw) (.ok r)) } := by
  have hc : createStep sH.base.core raw = .ok (core', r) := hstep
  show HistInv { base := { sH.base with core := core' }, committed := sH.committed, regs := sH.regs }
  refine histInv_of_same hinv ?_ rfl rfl
  intro stream st hl m hm
  rcases createStep_ok_shape hc with rfl | ⟨config, _, _, rfl⟩
  · exact hinv.coreCommitted stream st hl m hm
  · by_cases hn : stream = config.name
    · subst hn
      rw [lookup_insert] at hl
      cases hl
      cases hm
    · rw [lookupStream_insertStream_other _ _ _ _ (Ne.symm hn)] at hl
      exact hinv.coreCommitted stream st hl m hm

theorem histInv_get {sH : SubStateH} {name : StreamName} {core' : JSState} {r : Ret}
    (hinv : HistInv sH) (hstep : step sH.base.core (.getStream name) = .ok (core', r)) :
    HistInv { base := afterOp deliverOne sH.base core' (.getStream name) r,
              committed := committedAfter sH (.op (.getStream name) (.ok r)),
              regs := regsAfter sH (.op (.getStream name) (.ok r)) } := by
  have hg : getStep sH.base.core name = .ok (core', r) := hstep
  obtain rfl := getStep_ok_eq hg
  show HistInv { base := { sH.base with core := sH.base.core }, committed := sH.committed,
                 regs := sH.regs }
  exact histInv_of_same hinv hinv.coreCommitted rfl rfl

theorem histInv_last {sH : SubStateH} {stream : StreamName} {subject : SubjectName}
    {core' : JSState} {r : Ret}
    (hinv : HistInv sH)
    (hstep : step sH.base.core (.lastMessageForSubject stream subject) = .ok (core', r)) :
    HistInv { base := afterOp deliverOne sH.base core' (.lastMessageForSubject stream subject) r,
              committed := committedAfter sH (.op (.lastMessageForSubject stream subject) (.ok r)),
              regs := regsAfter sH (.op (.lastMessageForSubject stream subject) (.ok r)) } := by
  have hg : lastMsgStep sH.base.core stream subject = .ok (core', r) := hstep
  obtain rfl := lastMsgStep_ok_eq hg
  show HistInv { base := { sH.base with core := sH.base.core }, committed := sH.committed,
                 regs := sH.regs }
  exact histInv_of_same hinv hinv.coreCommitted rfl rfl

theorem histInv_delete {sH : SubStateH} {name : StreamName} {core' : JSState} {r : Ret}
    (hinv : HistInv sH) (hstep : step sH.base.core (.deleteStream name) = .ok (core', r)) :
    HistInv { base := afterOp deliverOne sH.base core' (.deleteStream name) r,
              committed := committedAfter sH (.op (.deleteStream name) (.ok r)),
              regs := regsAfter sH (.op (.deleteStream name) (.ok r)) } := by
  have hd : deleteStep sH.base.core name = .ok (core', r) := hstep
  obtain rfl := deleteStep_ok_eq hd
  show HistInv
    { base :=
        { sH.base with
            core := removeStream sH.base.core name
            subs := sH.base.subs.map (fun p => (p.1, endOne name p.2)) }
      committed := sH.committed
      regs := sH.regs }
  refine ⟨?_, hinv.regsBelow, ?_⟩
  · intro stream st hl m hm
    by_cases hn : stream = name
    · subst hn
      rw [lookupStream_removeStream_self] at hl
      cases hl
    · rw [lookupStream_removeStream_other _ _ _ hn] at hl
      exact hinv.coreCommitted stream st hl m hm
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨r, hr, hat, heq, hent⟩ := hinv.subs q hq
    refine ⟨r, hr, hat, ?_, ?_⟩
    · intro hreg
      cases hc : (q.2.stream == name && q.2.registered) with
      | true =>
        exfalso
        have hfalse : (endOne name q.2).registered = false := by
          unfold endOne
          rw [if_pos hc]
        rw [hfalse] at hreg
        cases hreg
      | false =>
        rw [endOne_skip hc] at hreg ⊢
        exact heq hreg
    · intro m hm
      cases hc : (q.2.stream == name && q.2.registered) with
      | true =>
        have hv : visible (endOne name q.2) = visible q.2 := by
          unfold endOne
          rw [if_pos hc]
          rfl
        have hs : (endOne name q.2).stream = q.2.stream := by
          unfold endOne
          rw [if_pos hc]
        rw [hv] at hm
        rw [hs]
        exact hent m hm
      | false =>
        rw [endOne_skip hc] at hm ⊢
        exact hent m hm

theorem liveKeep_admit (sub : Subscriber) (m : StoredMessage) :
    liveKeep { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence } = liveKeep sub := rfl

theorem liveOf_admit (committed : List (StreamName × StoredMessage)) (sub : Subscriber)
    (m : StoredMessage) (r : RegInfo) :
    liveOf committed { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence } r
      = liveOf committed sub r := rfl

theorem visible_admit (sub : Subscriber) (m : StoredMessage) :
    visible { sub with pending := sub.pending ++ [m], lastEnqueued := m.sequence }
      = visible sub ++ [Observed.entry m] := by
  simp [visible, List.map_append, List.append_assoc]

theorem visible_drain (sub : Subscriber) :
    visible { sub with observed := sub.observed ++ sub.pending.map Observed.entry, pending := [] }
      = visible sub := by
  simp [visible]

theorem visible_drain_done (sub : Subscriber) (e : SubError) :
    visible { sub with observed := sub.observed ++ sub.pending.map Observed.entry, pending := [],
                       status := QueueStatus.done e }
      = visible sub := by
  simp [visible]

theorem histInv_publish {sH : SubStateH} {stream : StreamName} {subject : SubjectName}
    {payload : PayloadHash} {headers : List (String × String)} {x : Option StreamSeq} {now : Nat}
    {core' : JSState} {r : Ret} (hsinv : StateInv sH.base) (hinv : HistInv sH)
    (hstep : step sH.base.core (.publish stream subject payload headers x now) = .ok (core', r)) :
    HistInv { base := afterOp deliverOne sH.base core' (.publish stream subject payload headers x now) r,
              committed := committedAfter sH (.op (.publish stream subject payload headers x now) (.ok r)),
              regs := regsAfter sH (.op (.publish stream subject payload headers x now) (.ok r)) } := by
  have hpub : publishStep sH.base.core stream subject payload headers x now = .ok (core', r) := hstep
  obtain ⟨st, hl, hceq, hr⟩ := publishStep_ok_eq hpub
  subst hr
  subst hceq
  simp only [afterOp, committedAfter, labelMessage, regsAfter]
  refine ⟨?_, hinv.regsBelow, ?_⟩
  · intro stream' st' hl' m hm
    by_cases hn : stream' = stream
    · subst hn
      rw [lookupStream_updateStream_self _ _ _ _ hl] at hl'
      cases hl'
      simp only [applyPublish] at hm
      have hsub := (pruneSubject_sublist
        (publishBase st subject (isRollup headers) ++ [newMessage st subject payload headers now])
        subject st.config.maxMessagesPerSubject).subset hm
      rcases List.mem_append.mp hsub with hold | hnew
      · exact List.mem_append.mpr
          (Or.inl (hinv.coreCommitted stream' st hl m ((publishBase_sublist st subject _).subset hold)))
      · rw [List.mem_singleton.mp hnew]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    · rw [lookupStream_updateStream_other _ _ _ _ hn] at hl'
      exact List.mem_append.mpr (Or.inl (hinv.coreCommitted stream' st' hl' m hm))
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨r, hr, hat, heq, hent⟩ := hinv.subs q hq
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · show r.index ≤ (sH.committed ++ [_]).length
      rw [List.length_append]
      exact Nat.le_trans hat (Nat.le_add_right _ _)
    · intro hreg
      dsimp only
      cases hc : (q.2.stream == stream && q.2.registered && matchesAny q.2.filters
          (publishedMessage subject st.nextSequence payload headers now).subject) with
      | false =>
        rw [deliverOne_skip hc] at hreg ⊢
        have hk : liveKeep q.2 (stream, publishedMessage subject st.nextSequence payload headers now)
            = false := by
          unfold liveKeep
          by_cases hs : q.2.stream = stream
          · have hmatch : matchesAny q.2.filters subject = false := by
              have hc2 := hc
              rw [hs, hreg] at hc2
              simpa using hc2
            rw [hs]
            simp [hmatch]
          · have hs' : stream ≠ q.2.stream := fun h => hs h.symm
            simp [hs']
        rw [liveOf_append_of_neg hat hk]
        exact heq hreg
      | true =>
        have hc' := hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc'
        obtain ⟨⟨hstream, hreg0⟩, hmatch⟩ := hc'
        have ho : q.2.status = .opened := (hsinv q hq).registeredOpen hreg0
        cases hpol : q.2.policy with
        | terminateOnLag n =>
          by_cases hfull : n ≤ q.2.pending.length
          · rw [deliverOne_overflow hc hpol hfull] at hreg
            cases hreg
          · rw [deliverOne_admit hc hpol (Nat.lt_of_not_le hfull) ho] at hreg ⊢
            have hk : liveKeep q.2 (stream, publishedMessage subject st.nextSequence payload headers now)
                = true := by
              unfold liveKeep
              simp [hstream, hmatch]
            rw [visible_admit, heq hreg0, liveOf_admit, liveOf_append_of_pos hat hk,
              List.map_append, List.append_assoc]
            rfl
    · intro m hm
      dsimp only
      cases hc : (q.2.stream == stream && q.2.registered && matchesAny q.2.filters
          (publishedMessage subject st.nextSequence payload headers now).subject) with
      | false =>
        rw [deliverOne_skip hc] at hm ⊢
        exact List.mem_append.mpr (Or.inl (hent m hm))
      | true =>
        have hc' := hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc'
        obtain ⟨⟨hstream, hreg0⟩, _⟩ := hc'
        have ho : q.2.status = .opened := (hsinv q hq).registeredOpen hreg0
        cases hpol : q.2.policy with
        | terminateOnLag n =>
          by_cases hfull : n ≤ q.2.pending.length
          · rw [deliverOne_overflow hc hpol hfull] at hm ⊢
            have hm' : Observed.entry m ∈ visible q.2 := hm
            exact List.mem_append.mpr (Or.inl (hent m hm'))
          · rw [deliverOne_admit hc hpol (Nat.lt_of_not_le hfull) ho] at hm ⊢
            rw [visible_admit] at hm
            rcases List.mem_append.mp hm with hold | hnew
            · exact List.mem_append.mpr (Or.inl (hent m hold))
            · cases List.mem_singleton.mp hnew
              show (q.2.stream, _) ∈ sH.committed ++ [(stream, _)]
              rw [hstream]
              exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

theorem histInv_op {sH : SubStateH} {o : Op} {e : Expect} {base' : SubState}
    (hsinv : StateInv sH.base) (hinv : HistInv sH)
    (hx : apply sH.base (.op o e) = some base') :
    HistInv { base := base', committed := committedAfter sH (.op o e),
              regs := regsAfter sH (.op o e) } := by
  cases e with
  | ok r =>
    obtain ⟨core', hstep, rfl⟩ := applyOp_ok_eq hx
    cases o with
    | publish stream subject payload headers x now => exact histInv_publish hsinv hinv hstep
    | deleteStream name => exact histInv_delete hinv hstep
    | createStream raw => exact histInv_create hinv hstep
    | getStream name => exact histInv_get hinv hstep
    | lastMessageForSubject stream subject => exact histInv_last hinv hstep
  | error err =>
    have h' : applyOp deliverOne sH.base o (.error err) = some base' := hx
    unfold applyOp at h'
    cases hstep : step sH.base.core o with
    | ok p =>
      obtain ⟨core', r₀⟩ := p
      rw [hstep] at h'
      simp at h'
    | error err₀ =>
      rw [hstep] at h'
      simp only at h'
      split at h'
      · cases h'
        cases o <;> exact hinv
      · cases h'

theorem histInv_register {sH : SubStateH} {stream : StreamName} {opts : ConsumeOptions}
    {l₀ : StreamSeq} {id : SubId} {e : Expect} {base' : SubState} (hinv : HistInv sH)
    (hx : apply sH.base (.register stream opts l₀ id e) = some base') :
    HistInv { base := base', committed := committedAfter sH (.register stream opts l₀ id e),
              regs := regsAfter sH (.register stream opts l₀ id e) } := by
  have h' : applyRegister sH.base stream opts l₀ id e = some base' := hx
  obtain ⟨hid, _⟩ := applyRegister_enabled h'
  unfold applyRegister at h'
  split at h'
  · cases h'
  · cases hl : lookupStream sH.base.core stream with
    | none =>
      rw [hl] at h'
      cases e with
      | ok r => simp at h'
      | error err =>
        split at h'
        · split at h'
          · cases h'
            exact hinv
          · cases h'
        all_goals first | cases h' | contradiction | (rename_i hc; cases hc)
    | some st =>
      rw [hl] at h'
      cases e with
      | error err => simp at h'
      | ok r =>
        cases r with
        | config c => simp at h'
        | sequence n => simp at h'
        | message m => simp at h'
        | unit =>
          simp only at h'
          split at h'
          · cases h'
            simp only [committedAfter, labelMessage, regsAfter, hl]
            refine ⟨?_, ?_, ?_⟩
            · intro stream' st' hl' m hm
              exact hinv.coreCommitted stream' st' hl' m hm
            · intro q hq
              have hq' : q ∈ sH.regs ++ [(id, ({ index := sH.committed.length, initial := replayObserved st.messages opts } : RegInfo))] := hq
              rcases List.mem_append.mp hq' with hold | hnew
              · show q.1 < id + 1
                have := hinv.regsBelow q hold
                rw [← hid] at this
                exact Nat.lt_succ_of_lt this
              · rw [List.mem_singleton.mp hnew]
                exact Nat.lt_succ_self id
            · intro p hp
              have hp' : p ∈ sH.base.subs ++ [(id, newSubscriber stream opts l₀ st.messages)] := hp
              rcases List.mem_append.mp hp' with hold | hnew
              · obtain ⟨r, hr, hat, heq, hent⟩ := hinv.subs p hold
                exact ⟨r, lookupReg_append_of_some _ hr, hat, heq, hent⟩
              · rw [List.mem_singleton.mp hnew]
                refine ⟨{ index := sH.committed.length, initial := replayObserved st.messages opts },
                  ?_, Nat.le_refl _, ?_, ?_⟩
                · apply lookupReg_append_fresh
                  intro q hq
                  rw [hid]
                  exact Nat.ne_of_lt (hinv.regsBelow q hq)
                · intro _
                  show replayObserved st.messages opts ++ [] =
                    replayObserved st.messages opts ++ (liveOf sH.committed _ _).map Observed.entry
                  simp only [liveOf_at_length, List.map_nil]
                · intro m hm
                  have hm' : Observed.entry m ∈
                      (selectReplay st.messages opts).map Observed.entry ++ [Observed.caughtUp] := by
                    have hm'' : Observed.entry m ∈
                        visible (newSubscriber stream opts l₀ st.messages) := hm
                    simpa [visible, newSubscriber, replayObserved] using hm''
                  rcases List.mem_append.mp hm' with hin | hcu
                  · obtain ⟨m₀, hm₀, hmeq⟩ := List.mem_map.mp hin
                    have hmm : m = m₀ := (Observed.entry.inj hmeq).symm
                    rw [hmm]
                    exact hinv.coreCommitted stream st hl m₀ (selectReplay_mem hm₀).1
                  · rw [List.mem_singleton] at hcu
                    cases hcu
          · cases h'

theorem histInv_pull {sH : SubStateH} {id : SubId} {base' : SubState} (hsinv : StateInv sH.base)
    (hinv : HistInv sH) (hx : apply sH.base (.pull id) = some base') :
    HistInv { base := base', committed := committedAfter sH (.pull id),
              regs := regsAfter sH (.pull id) } := by
  have h' : applyPull pullStep sH.base id = some base' := hx
  unfold applyPull at h'
  split at h'
  · cases h'
  · rename_i sub hsub
    split at h'
    · cases h'
    · rename_i sub' hpull
      cases h'
      refine ⟨hinv.coreCommitted, hinv.regsBelow, ?_⟩
      intro p hp
      have hp' : p ∈ updateSub sH.base.subs id (fun _ => sub') := hp
      rcases mem_updateSub_eq hp' with hold | ⟨hpid, _, _, hp2⟩
      · exact hinv.subs p hold
      · obtain ⟨r, hr, hat, heq, hent⟩ := hinv.subs (id, sub) (mem_of_lookupSub hsub)
        have hsubinv : SubInv sH.base sub := hsinv (id, sub) (mem_of_lookupSub hsub)
        rw [hpid, hp2]
        refine ⟨r, hr, hat, ?_, ?_⟩
        · intro hreg
          unfold pullStep at hpull
          split at hpull
          · cases hpull
          · rename_i e hst
            cases hpull
            have hreg' : sub.registered = true := hreg
            have ho := hsubinv.registeredOpen hreg'
            rw [hst] at ho
            cases ho
          · split at hpull
            · cases hpull
            · cases hpull
              have hreg' : sub.registered = true := hreg
              rw [visible_drain]
              exact heq hreg'
          · rename_i e hst
            split at hpull
            · cases hpull
            · cases hpull
              have hreg' : sub.registered = true := hreg
              have ho := hsubinv.registeredOpen hreg'
              rw [hst] at ho
              cases ho
        · intro m hm
          unfold pullStep at hpull
          split at hpull
          · cases hpull
          · rename_i e hst
            cases hpull
            have hm' : Observed.entry m ∈ (sub.observed ++ [Observed.failed e]) ++
                sub.pending.map Observed.entry := hm
            rcases List.mem_append.mp hm' with hobs | hpend
            · rcases List.mem_append.mp hobs with hobs' | hf
              · exact hent m (List.mem_append.mpr (Or.inl hobs'))
              · rw [List.mem_singleton] at hf
                cases hf
            · exact hent m (List.mem_append.mpr (Or.inr hpend))
          · split at hpull
            · cases hpull
            · cases hpull
              rw [visible_drain] at hm
              exact hent m hm
          · rename_i e hst
            split at hpull
            · cases hpull
            · cases hpull
              rw [visible_drain_done] at hm
              exact hent m hm

theorem histInv_unsubscribe {sH : SubStateH} {id : SubId} {base' : SubState}
    (hinv : HistInv sH) (hx : apply sH.base (.unsubscribe id) = some base') :
    HistInv { base := base', committed := committedAfter sH (.unsubscribe id),
              regs := regsAfter sH (.unsubscribe id) } := by
  have h' : applyUnsubscribe sH.base id = some base' := hx
  unfold applyUnsubscribe at h'
  split at h'
  · cases h'
  · rename_i sub hsub
    split at h'
    · cases h'
    · cases h'
      refine ⟨hinv.coreCommitted, hinv.regsBelow, ?_⟩
      intro p hp
      have hp' : p ∈ updateSub sH.base.subs id
          (fun sub => { sub with registered := false, pending := [], status := .shutDown }) := hp
      rcases mem_updateSub_eq hp' with hold | ⟨hpid, sub₀, h₀, hp2⟩
      · exact hinv.subs p hold
      · obtain ⟨r, hr, hat, _, hent⟩ := hinv.subs (id, sub₀) h₀
        rw [hpid, hp2]
        refine ⟨r, hr, hat, ?_, ?_⟩
        · intro hreg
          cases hreg
        · intro m hm
          have hm' : Observed.entry m ∈ sub₀.observed ++ ([] : List StoredMessage).map Observed.entry :=
            hm
          simp only [List.map_nil, List.append_nil] at hm'
          exact hent m (List.mem_append.mpr (Or.inl hm'))

theorem histInv_step {sH sH' : SubStateH} {l : Label} (hreach : ReachableSubH sH)
    (hinv : HistInv sH) (h : applyH sH l = some sH') : HistInv sH' := by
  have hsinv : StateInv sH.base := stateInv_reachable (reachableSubH_erase hreach)
  unfold applyH at h
  cases hx : apply sH.base l with
  | none =>
    rw [hx] at h
    cases h
  | some base' =>
    rw [hx] at h
    simp only at h
    cases h
    cases l with
    | op o e => exact histInv_op hsinv hinv hx
    | register stream opts l₀ id e => exact histInv_register hinv hx
    | pull id => exact histInv_pull hsinv hinv hx
    | unsubscribe id => exact histInv_unsubscribe hinv hx

theorem histInv_reachable {sH : SubStateH} (h : ReachableSubH sH) : HistInv sH := by
  induction h with
  | init =>
    refine ⟨?_, (fun _ hq => nomatch hq), (fun _ hp => nomatch hp)⟩
    intro stream st hl
    cases hl
  | step hr hnext ih => exact histInv_step hr ih hnext

/-! ## SA5h -/

/-- The global T8′: while registered, what a subscriber can see is the prefix its registration
materialised followed by exactly the matching messages published since. -/
theorem visible_global {sH : SubStateH} (h : ReachableSubH sH) :
    ∀ p ∈ sH.base.subs, ∀ r, lookupReg sH.regs p.1 = some r → p.2.registered = true →
      visible p.2 = r.initial ++ (liveEntries sH p.1).map Observed.entry := by
  intro p hp r hr hreg
  obtain ⟨r', hr', _, heq, _⟩ := (histInv_reachable h).subs p hp
  rw [hr] at hr'
  cases hr'
  have hshape := subShape_reachable (reachableSubH_erase h)
  have hlook : lookupSub sH.base.subs p.1 = some p.2 := lookupSub_of_mem_pairwise hshape.1 hp
  unfold liveEntries
  rw [hlook, hr]
  exact heq hreg

/-- Provenance: every entry a subscriber ever sees was a successful publish. -/
theorem entries_committed {sH : SubStateH} (h : ReachableSubH sH) :
    ∀ p ∈ sH.base.subs, ∀ m, Observed.entry m ∈ visible p.2 → (p.2.stream, m) ∈ sH.committed :=
  fun p hp m hm =>
    let ⟨_, _, _, _, hent⟩ := (histInv_reachable h).subs p hp
    hent m hm

end EffectNatsSubstrate
