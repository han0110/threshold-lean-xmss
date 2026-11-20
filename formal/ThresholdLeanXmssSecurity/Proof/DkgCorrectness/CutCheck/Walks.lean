import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Joint
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Records.Keys
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Parts

/-!
# The walks of one operator through the head of a batch

`preGhost` is the recorded prefix of one ceremony up to the check of batch `k`, with its result as
its record. `preGhost_eq` states that its program is the plain program of the PRSS setup, the
batches before `k` and the head of batch `k` (`plainHead`).

`HeadReach` states that the program reaches the last round of each reshare of the head at a fixed
depth, with the message of the reshare as its outbox and the output of the reshare in each result.
`headReach` proves it from the timed prefixes (`reachH_preGhost`) and from the waits of one reshare
(`reachH_reshare`, `reachH_reshareCollector`, `reachH_recLayers`).

`HeadDraws` states that the reads of `PRG` on each path hold the draws of each reshare at a fixed
label, and the output at each position with no filler. `headDraws` proves it from the reads of one
reshare (`holds_rerand_reads`, `holds_mult_reads`) and of the AND layers (`holds_recLayers_reads`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace CutBudget

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The circuits of batch `k` of `jobs` under `parameter`. -/
def batchCircuits (parameter : PublicParameter) (jobs : List Job) (k : ℕ) : List Circuit :=
  ((chunks settings.batchSize jobs).getD k []).map (circuits parameter ·.kind)


/-- The recorded prefix with its result as its record. -/
def preGhost (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    OracleComp (PartySpec C E RealSpec) (Option (Joint.PreOut C) × Option (Joint.PreOut C)) :=
  (fun x => (x.1, x.1)) <$> Joint.pre1 K circuits settings k i c

/-- The rounds before the head of batch `k`, namely the PRSS setup and the batches before `k`. -/
def headStart (parameter : PublicParameter) (jobs : List Job) (k : ℕ) : ℕ :=
  setupRounds + (((chunks settings.batchSize jobs).take k).map fun batch =>
    CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum

/-- The label at the start of the head of batch `k`. -/
def headLabel (parameter : PublicParameter) (jobs : List Job) (start : ℕ) (k : ℕ) : ℕ :=
  start + (((chunks settings.batchSize jobs).take k).map (jobLabel circuits parameter)).sum

/-- The wait of the round of a peer reshare of `count` positions at operator `i`, with a relation
`rel` between each result of the rest and the output of the reshare on its inbox. -/
def PeerWaitG {γ : Type} (i : C.Party) (count : ℕ) (rel : γ → Shares C Bit → Prop)
    (_ : List (Query C × HashOutput)) (outbox : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) γ) : Prop :=
  ∃ (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit),
    outbox = reshareOut K (localContext i) bitCodec r Zs v count ∧
    ∀ inbox, ∀ x ∈ support (resume inbox), rel x (reshareZ K (localContext i) bitCodec r Zs v count inbox)


/-- The wait of the second round of a collector reshare of `count` positions at operator `i`, with a
relation `rel` between each result of the rest and the output of the reshare on the forwards. -/
def CollectorWaitG {γ : Type} (i : C.Party) (count : ℕ) (rel : γ → Shares C Bit → Prop)
    (_ : List (Query C × HashOutput)) (outbox : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) γ) : Prop :=
  ∃ (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit) (inbox : Mail C E),
    outbox = colOut2 K i r Zs v count inbox ∧
    ∀ forward, ∀ x ∈ support (resume forward), rel x (colZ K i r Zs v count inbox forward)


/-- The wait of the last round of a reshare in `mode`, with a relation `rel` between each result of the
rest and the output of the reshare. -/
def ReshareWaitG {γ : Type} : ReshareMode → C.Party → ℕ → (γ → Shares C Bit → Prop) → List (Query C × HashOutput) →
    Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop
  | .peer => PeerWaitG K
  | .collector => CollectorWaitG K


/-- The relation between a result of `preGhost` with a head and the value `out` of that head. -/
def HeadRel (out : BatchStart C → Shares C Bit) (x : Option (Joint.PreOut C) × Option (Joint.PreOut C))
    (z : Shares C Bit) : Prop :=
  ∀ p : Joint.PreOut C, x.2 = some p → out p.1.2.2.1 = z

/-- The reshare rounds of the head of batch `k` at an operator with keys. On each path that does not
abort, the program reaches the last round of the reshare of each AND layer and of `Rerand`, at the
round after `headStart`, the earlier layers and the earlier rounds of the layer, with the message
of the reshare as its outbox and the output of the reshare in the head of each result. -/
def HeadReach : Prop :=
  ∀ (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C), c.keys i = some keys →
    k < (chunks settings.batchSize c.jobs).length →
    (∀ l < depth (batchCircuits circuits settings keys.parameter c.jobs k),
      CachedOpening.ReachH (fun x => x.2 = none)
        (ReshareWaitG K settings.mode i (gatesAt (batchCircuits circuits settings keys.parameter c.jobs k) l).length
          (HeadRel fun b => b.zs l))
        (headStart circuits settings keys.parameter c.jobs k + l * settings.mode.rounds + (settings.mode.rounds - 1))
        [] (preGhost K circuits settings k i c)) ∧
    CachedOpening.ReachH (fun x => x.2 = none)
      (PeerWaitG K i (outputsOf (batchCircuits circuits settings keys.parameter c.jobs k)).length
        (HeadRel fun b => b.v'))
      (headStart circuits settings keys.parameter c.jobs k +
        depth (batchCircuits circuits settings keys.parameter c.jobs k) * settings.mode.rounds)
      [] (preGhost K circuits settings k i c)

/-- The reads of a reshare of `count` positions at the label `ρ` with the PRSS keys `prss` in the
reads `hist`. Each held term has a read at each position, and the output `z` is the read at each
position with no filler. -/
def ReshareReads (hist : List (PrgInput C × Bit)) (i : C.Party) (prss : PrssKeys C) (mode : ReshareMode)
    (ρ count : ℕ) (z : Shares C Bit) : Prop :=
  ∀ T, i ∈ C.holders T → ∀ g < count, (∃ bit, ((.term T, prss.term T, ρ, 0, g), bit) ∈ hist) ∧
    (filler K mode T g = none → ((.term T, prss.term T, ρ, 0, g), z T g) ∈ hist)

/-- The draws of the head of batch `k` at an operator with keys. On each path, a result with a head
has the reads of each AND layer at the label of the head start plus the layer, and the reads of
`Rerand` after the layers. -/
def HeadDraws : Prop :=
  ∀ (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C), c.keys i = some keys →
    k < (chunks settings.batchSize c.jobs).length →
    RerandCells.Holds (fun hist x => ∀ p : Joint.PreOut C, x.2 = some p →
      (∀ l < depth (batchCircuits circuits settings keys.parameter c.jobs k),
        ReshareReads K hist i p.1.2.2.1.ctx.prss settings.mode
          (headLabel circuits settings keys.parameter c.jobs c.counters.1 k + l)
          (gatesAt (batchCircuits circuits settings keys.parameter c.jobs k) l).length (p.1.2.2.1.zs l)) ∧
      ReshareReads K hist i p.1.2.2.1.ctx.prss .peer
        (headLabel circuits settings keys.parameter c.jobs c.counters.1 k +
          depth (batchCircuits circuits settings keys.parameter c.jobs k))
        (outputsOf (batchCircuits circuits settings keys.parameter c.jobs k)).length p.1.2.2.1.v')
      [] (preGhost K circuits settings k i c)

/-! ## The plain program of the recorded prefix -/

/-- The head of a batch with no record, the code of `recHead`. -/
def plainHead (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (BatchStart C × ℕ) := do
  let (label, k) ← get
  let cs := jobs.map (circuits parameter ·.kind)
  let B := realRunBuildingBlocks (G := RealSpec) K ctx settings.mode
  let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
  let (zs, s1) ← StateT.lift ((recLayers K B cs inputs (depth cs)).run ⟨fun _ => [], label, k⟩)
  let (v', s2) ← StateT.lift ((B.rerand (outputShares K cs
    (layerPrefix K B.mode cs inputs zs (depth cs)).1) (outputsOf cs).length).run s1)
  pure (⟨B.mode, jobs, parameter, cs, inputs, zs, v', ctx, s2⟩, k)

omit [Fintype E] [DecidableEq E] in
theorem dropRecS_recHead (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    dropRecS (recHead K circuits settings ctx parameter jobs) = plainHead K circuits settings ctx parameter jobs := by
  unfold recHead plainHead
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_get, dropRecS_liftS]

/-- The self-recorded prefix at an operator with keys is the plain program of the prefix, namely the
PRSS setup, the batches before `k` and the head of batch `k`, with its result as its record. -/
theorem preGhost_eq (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hkeys : c.keys i = some keys) :
    preGhost K circuits settings k i c = (fun o => (o, o)) <$> (((StateT.lift (prssSetup i) :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) (PrssKeys C)) >>= fun prss =>
        ((chunks settings.batchSize c.jobs).take k).mapM
          (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter) >>= fun outs =>
        plainHead K circuits settings ⟨i, keys, prss⟩ keys.parameter ((chunks settings.batchSize c.jobs).getD k []) >>=
          fun h => pure (prss, outs, h)).run c.counters).run := by
  have hdrop : (dropRecS (recPrefix K circuits settings k i keys c.jobs)) = ((StateT.lift (prssSetup i) :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) (PrssKeys C)) >>= fun prss =>
        ((chunks settings.batchSize c.jobs).take k).mapM
          (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter) >>= fun outs =>
        plainHead K circuits settings ⟨i, keys, prss⟩ keys.parameter ((chunks settings.batchSize c.jobs).getD k []) >>=
          fun h => pure (prss, outs, h)) := by
    unfold recPrefix
    simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_liftS, monadHom_list_mapM, dropRecS_recHead]
    refine bind_congr fun prss => ?_
    congr 1
    exact congrArg (fun f => List.mapM f _) (funext fun b => dropRecS_recBatch K circuits settings _ _ b)
  rw [← hdrop]
  simp only [preGhost, Joint.pre1, hkeys]
  change _ = (fun o => (o, o)) <$> (Prod.fst <$> ((recPrefix K circuits settings k i keys c.jobs).run c.counters).run.run)
  rw [Functor.map_map]

/-- Real batches take the sum of their exact rounds. -/
theorem runTimed_mapM_realBatch (ctx : Context C) (parameter : PublicParameter) :
    ∀ l : List (List Job), RunTimed ((l.map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum)
      (l.mapM (realBatch K circuits settings.mode ctx parameter))
  | [] => by simpa using runTimed_pure (σ := ℕ × ℕ) (C := C) (E := E) (G := RealSpec) ([] : List (Option (List (List Bit))))
  | b :: l => by
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (CheckTiming.runTimed_realBatch_exact K circuits settings.mode ctx parameter b).bind fun a =>
      ((runTimed_mapM_realBatch ctx parameter l).bind (n := 0) fun as => runTimed_pure _).of_eq (Nat.add_zero _)

/-! ## The reads of `PRG` -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A program and its continuation keep a leaf property that each abort has, when the continuation
keeps it from each result of the program. -/
theorem holds_partyBind_support {α β : Type} {P : List (PrgInput C × Bit) → Option β → Prop}
    {hist : List (PrgInput C × Bit)} (p : PartyM C E RealSpec α) (q : α → PartyM C E RealSpec β)
    (hnone : ∀ h, P h none) (hq : ∀ a, some a ∈ support p.run → ∀ h, hist ⊆ h → RerandCells.Holds P h (q a).run) :
    RerandCells.Holds P hist (p >>= q).run := by
  rw [OptionT.run_bind, Option.elimM]
  refine RerandCells.holds_bind (Q := fun h o => o ∈ support p.run ∧ hist ⊆ h)
    (RerandCells.holds_of_support p.run hist fun x hx h hsub => ⟨hx, hsub⟩) fun h o ho => ?_
  rcases o with _ | a
  · exact RerandCells.Holds.pure h _ (hnone h)
  · exact hq a ho.1 h ho.2

omit [Fintype E] [DecidableEq E] in
theorem filler_peer_none {T : C.Term} {g : ℕ} (h : filler K .peer T g = none) : T ∉ filledTerms K := by
  intro hT
  obtain ⟨j, -, hj⟩ := Finset.mem_map.1 hT
  simp only [filler] at h
  rw [List.find?_eq_none] at h
  exact h j (List.mem_finRange j) (decide_eq_true hj)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A program with a leaf property and a continuation that keeps a property from each leaf with a
result, when each abort has the property. -/
theorem holds_partyBind {α β : Type} {P : List (PrgInput C × Bit) → Option β → Prop}
    {Q : List (PrgInput C × Bit) → Option α → Prop} {hist : List (PrgInput C × Bit)} (p : PartyM C E RealSpec α)
    (q : α → PartyM C E RealSpec β) (hp : RerandCells.Holds Q hist p.run) (hnone : ∀ h, P h none)
    (hq : ∀ h a, Q h (some a) → RerandCells.Holds P h (q a).run) :
    RerandCells.Holds P hist (p >>= q).run := by
  rw [OptionT.run_bind, Option.elimM]
  refine RerandCells.holds_bind hp fun h o ho => ?_
  rcases o with _ | a
  · exact RerandCells.Holds.pure h _ (hnone h)
  · exact hq h a ho

omit [Fintype E] [DecidableEq E] in
theorem ReshareReads.mono {hist hist' : List (PrgInput C × Bit)} {i : C.Party} {prss : PrssKeys C} {mode : ReshareMode}
    {ρ count : ℕ} {z : Shares C Bit} (h : ReshareReads K hist i prss mode ρ count z) (hsub : hist ⊆ hist') :
    ReshareReads K hist' i prss mode ρ count z := fun T hT g hg =>
  ⟨(h T hT g hg).1.imp fun _ hb => hsub hb, fun hf => hsub ((h T hT g hg).2 hf)⟩

omit [Fintype E] [DecidableEq E] in
/-- The reads of `Rerand`. Each held term has a read at each position at the label of the start of
`Rerand`, and the output at each position with no filler is that read. -/
theorem holds_rerand_reads (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit) (n : ℕ) (st : RunState C)
    (hist : List (PrgInput C × Bit)) :
    RerandCells.Holds (fun h o => ∀ a, o = some a → ReshareReads K h ctx.self ctx.prss .peer st.label n a.1) hist
      (((realRunBuildingBlocks (G := RealSpec) K ctx mode).rerand v n).run st).run := by
  simp only [realRunBuildingBlocks, prssRandomness, freshLabel, StateT.run_bind, StateT.run_modifyGet,
    StateT.run_lift, pure_bind, bind_assoc, oracleStep, localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM]
  refine RerandCells.holds_termDraws_bind ctx.self ctx.prss.term st.label 0 n C.terms hist _ fun rs h hsub hcells => ?_
  simp only [Option.elim]
  refine RerandCells.holds_of_support _ h fun o ho h' hsub' a hoa T hself g hg => ?_
  have hm : C.terms.idxOf T < C.terms.length := List.idxOf_lt_length_of_mem (mem_terms T)
  have hc := hcells _ hm
  simp only [List.getElem_idxOf] at hc
  refine ⟨⟨_, hsub' (hc hself g hg)⟩, fun hf => ?_⟩
  rw [mem_support_bind_iff] at ho
  obtain ⟨Z, -, ho⟩ := ho
  rw [RerandCells.reshare_unfilled K ctx _ _ n _ o ho a hoa T (filler_peer_none K hf) hself g hg]
  exact hsub' (hc hself g hg)

omit [Fintype E] [DecidableEq E] in
/-- The output of a collector reshare at a held term that is not `T*` of its gate is the randomness of
that term. -/
theorem reshareCollector_unfilled (ctx : Context C) (rnd : PrssOutput C Bit) (w : ℕ → Bit) (n : ℕ) (s : RunState C) :
    ∀ o ∈ support ((reshareCollector (G := RealSpec) K ctx rnd w n).run s).run, ∀ a, o = some a →
      ∀ T, ctx.self ∈ C.holders T → ∀ g < n, T ≠ (K.collector g).1 → a.1 T g = rnd.1 T g := by
  intro o ho a hoa T hself g hg hT
  subst hoa
  unfold reshareCollector at ho
  simp only [StateT.run_bind, StateT.run_lift, record, StateT.run_modify, StateT.run_pure, OptionT.run_bind,
    Option.elimM, bind_assoc, pure_bind] at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨o₁, -, ho⟩ := ho
  rcases o₁ with _ | inbox
  · simp at ho
  simp only [Option.elim] at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨o₂, -, ho⟩ := ho
  rcases o₂ with _ | forward
  · simp at ho
  · simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at ho
    subst ho
    simp [hself, hT, Nat.not_le.2 hg]

omit [Fintype E] [DecidableEq E] in
/-- The reads of the reshare of one AND layer. Each held term has a read at each position at the label
of the start of the layer, and the output at each position with no filler is that read. -/
theorem holds_mult_reads (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit) (n : ℕ) (st : RunState C)
    (hist : List (PrgInput C × Bit)) :
    RerandCells.Holds (fun h o => ∀ a, o = some a → ReshareReads K h ctx.self ctx.prss mode st.label n a.1) hist
      (((realRunBuildingBlocks (G := RealSpec) K ctx mode).mult x y n).run st).run := by
  simp only [realRunBuildingBlocks, prssRandomness, freshLabel, StateT.run_bind, StateT.run_modifyGet,
    StateT.run_lift, pure_bind, bind_assoc, oracleStep, localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM]
  refine RerandCells.holds_termDraws_bind ctx.self ctx.prss.term st.label 0 n C.terms hist _ fun rs h hsub hcells => ?_
  simp only [Option.elim]
  refine RerandCells.holds_of_support _ h fun o ho h' hsub' a hoa T hself g hg => ?_
  have hm : C.terms.idxOf T < C.terms.length := List.idxOf_lt_length_of_mem (mem_terms T)
  have hc := hcells _ hm
  simp only [List.getElem_idxOf] at hc
  refine ⟨⟨_, hsub' (hc hself g hg)⟩, fun hf => ?_⟩
  rw [mem_support_bind_iff] at ho
  obtain ⟨Z, -, ho⟩ := ho
  cases mode with
  | peer =>
    simp only [reshareWith] at ho
    rw [RerandCells.reshare_unfilled K ctx (Prod.mk (fun T => rs.getD (C.terms.idxOf T) fun _ => 0)
      (fun j => Z.getD j.val fun _ => 0)) _ n _ o ho a hoa T (filler_peer_none K hf) hself g hg]
    exact hsub' (hc hself g hg)
  | collector =>
    simp only [reshareWith] at ho
    have hstar : T ≠ (K.collector g).1 := by
      intro he
      simp [filler, he] at hf
    rw [reshareCollector_unfilled K ctx (Prod.mk (fun T => rs.getD (C.terms.idxOf T) fun _ => 0)
      (fun j => Z.getD j.val fun _ => 0)) _ n _ o ho a hoa T hself g hg hstar]
    exact hsub' (hc hself g hg)

omit [Fintype E] [DecidableEq E] in
/-- The reads of the AND layers. The layers add one label each, and each layer has the reads of its
reshare at its label. -/
theorem holds_recLayers_reads (ctx : Context C) (mode : ReshareMode) (cs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    ∀ (n : ℕ) (s : RunState C) (hist : List (PrgInput C × Bit)),
      RerandCells.Holds (fun h o => ∀ a : (ℕ → Shares C Bit) × RunState C, o = some a → a.2.label = s.label + n ∧
        ∀ l < n, ReshareReads K h ctx.self ctx.prss mode (s.label + l) (gatesAt cs l).length (a.1 l)) hist
      ((recLayers K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs n).run s).run
  | 0, s, hist => by
    simp only [recLayers, List.range_zero, List.foldlM_nil, StateT.run_pure, OptionT.run_pure]
    exact RerandCells.Holds.pure hist _ fun a ha => by
      cases ha
      exact ⟨rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
  | n + 1, s, hist => by
    unfold recLayers
    rw [List.range_succ, List.foldlM_append, ← recLayers, StateT.run_bind]
    refine holds_partyBind _ _ (RerandCells.holds_grow (holds_recLayers_reads ctx mode cs inputs n s hist))
      (fun h a ha => by cases ha) fun h a ha => ?_
    obtain ⟨hsub₀, hrest⟩ := ha
    obtain ⟨hlabel, hprev⟩ := hrest a rfl
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, StateT.run_map, OptionT.run_map]
    rw [map_eq_bind_pure_comp]
    refine RerandCells.holds_bind (RerandCells.holds_grow (RerandCells.holds_support
      (holds_mult_reads K ctx mode _ _ _ a.2 h))) fun h' o ho => ?_
    refine RerandCells.Holds.pure h' _ fun b hb => ?_
    rcases o with _ | z
    · cases hb
    obtain ⟨hsub, hmem, hz⟩ := ho
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    have hz2 := mult_support K ctx mode _ _ _ a.2 z hmem
    refine ⟨by rw [hz2]; simp only [afterReply]; omega, fun l hl => ?_⟩
    dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt hl)]
      exact (hprev l hl).mono K hsub
    · rw [Function.update_self, ← hlabel]
      exact hz z rfl

omit [Fintype E] [DecidableEq E] in
/-- The reads of the plain head of a batch from the counters `(L, kk)`. The AND layer `l` has the
reads of its reshare at the label `L + l`, and `Rerand` at the label `L` plus the depth. -/
theorem plainHead_reads (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (L kk : ℕ)
    (hist : List (PrgInput C × Bit)) :
    RerandCells.Holds (fun h o => ∀ d : (BatchStart C × ℕ) × (ℕ × ℕ), o = some d → d.1.1.ctx = ctx ∧
        (∀ l < depth (jobs.map (circuits parameter ·.kind)),
          ReshareReads K h ctx.self ctx.prss settings.mode (L + l)
            (gatesAt (jobs.map (circuits parameter ·.kind)) l).length (d.1.1.zs l)) ∧
        ReshareReads K h ctx.self ctx.prss .peer (L + depth (jobs.map (circuits parameter ·.kind)))
          (outputsOf (jobs.map (circuits parameter ·.kind))).length d.1.1.v') hist
      ((plainHead K circuits settings ctx parameter jobs).run (L, kk)).run := by
  simp only [plainHead, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
  refine holds_partyBind_support _ _ (fun h d hd => by cases hd) fun a _ h _ => ?_
  refine holds_partyBind (Q := fun h o => ∀ a₁ : ((ℕ → Shares C Bit) × RunState C) × (ℕ × ℕ), o = some a₁ →
      a₁.1.2.label = L + depth (jobs.map (circuits parameter ·.kind)) ∧
      ∀ l < depth (jobs.map (circuits parameter ·.kind)),
        ReshareReads K h ctx.self ctx.prss settings.mode (L + l)
          (gatesAt (jobs.map (circuits parameter ·.kind)) l).length (a₁.1.1 l)) _ _ ?_
    (fun h d hd => by cases hd) fun h₁ a₁ ha₁ => ?_
  · refine holds_partyBind _ _ (holds_recLayers_reads K ctx settings.mode _ a.1 _ ⟨fun _ => [], L, kk⟩ h)
      (fun h b hb => by cases hb) fun h b hb => ?_
    simp only [OptionT.run_pure]
    exact RerandCells.Holds.pure h _ fun b' hb' => by
      cases hb'
      exact hb b rfl
  · obtain ⟨hlabel, hlayers⟩ := ha₁ a₁ rfl
    refine holds_partyBind (Q := fun h o => ∀ a₂ : (Shares C Bit × RunState C) × (ℕ × ℕ), o = some a₂ → h₁ ⊆ h ∧
        ReshareReads K h ctx.self ctx.prss .peer (L + depth (jobs.map (circuits parameter ·.kind)))
          (outputsOf (jobs.map (circuits parameter ·.kind))).length a₂.1.1) _ _ ?_
      (fun h d hd => by cases hd) fun h₂ a₂ ha₂ => ?_
    · refine holds_partyBind _ _ (RerandCells.holds_grow (holds_rerand_reads K ctx settings.mode _ _ a₁.1.2 h₁))
        (fun h b hb => by cases hb) fun h b hb => ?_
      simp only [OptionT.run_pure]
      refine RerandCells.Holds.pure h _ fun a' ha' => ?_
      cases ha'
      exact ⟨hb.1, by rw [← hlabel]; exact hb.2 b rfl⟩
    · obtain ⟨hsub, hre⟩ := ha₂ a₂ rfl
      simp only [StateT.run_pure, OptionT.run_pure]
      refine RerandCells.Holds.pure h₂ _ fun d hd => ?_
      cases hd
      exact ⟨rfl, fun l hl => (hlayers l hl).mono K hsub, hre⟩

/-- `HeadDraws` holds. -/
theorem headDraws : HeadDraws K circuits settings := by
  intro k i σ c keys hkeys hk
  rw [preGhost_eq K circuits settings k i c keys hkeys, map_eq_bind_pure_comp]
  refine RerandCells.holds_bind (Q := fun hist o => ∀ p : Joint.PreOut C, o = some p →
      (∀ l < depth (batchCircuits circuits settings keys.parameter c.jobs k),
        ReshareReads K hist i p.1.2.2.1.ctx.prss settings.mode
          (headLabel circuits settings keys.parameter c.jobs c.counters.1 k + l)
          (gatesAt (batchCircuits circuits settings keys.parameter c.jobs k) l).length (p.1.2.2.1.zs l)) ∧
      ReshareReads K hist i p.1.2.2.1.ctx.prss .peer
        (headLabel circuits settings keys.parameter c.jobs c.counters.1 k +
          depth (batchCircuits circuits settings keys.parameter c.jobs k))
        (outputsOf (batchCircuits circuits settings keys.parameter c.jobs k)).length p.1.2.2.1.v') ?_
    fun h o ho => RerandCells.Holds.pure h _ fun p hp => ho p hp
  rw [StateT.run_bind]
  refine holds_partyBind_support _ _ (fun h p hp => by cases hp) fun a ha h _ => ?_
  have ha2 : a.2 = c.counters := lift_counters _ _ _ ha
  rw [StateT.run_bind]
  refine holds_partyBind_support _ _ (fun h p hp => by cases hp) fun b hb h' _ => ?_
  have hb2 := mapM_realBatch_counters K circuits settings ⟨i, keys, a.1⟩ keys.parameter _ a.2 b hb
  rcases b with ⟨outs, L, kk⟩
  rw [StateT.run_bind]
  refine holds_partyBind _ _ (plainHead_reads K circuits settings _ _ _ L kk h') (fun h p hp => by cases hp)
    fun h d hd => ?_
  simp only [StateT.run_pure, OptionT.run_pure]
  refine RerandCells.Holds.pure h _ fun p hp => ?_
  cases hp
  obtain ⟨hctx, hlayers, hre⟩ := hd d rfl
  simp only [Prod.mk.injEq] at hb2
  rw [hctx]
  unfold headLabel batchCircuits
  rw [← ha2, ← hb2.1]
  exact ⟨hlayers, hre⟩

/-! ## The waits of the reshares -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An exchange is a wait of depth `0`. The rest aborts on an abort frame. -/
theorem reachH_exchange {α γ : Type} {P : γ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    (hist : List (Query C × HashOutput)) (out : Mail C E) (h : Mail C E → PartyM C E RealSpec α)
    (g : Option α → OracleComp (PartySpec C E RealSpec) γ)
    (hQ : Q hist out fun inbox => if C.parties.any (fun c => Msg.isAbort (inbox c)) then g none
      else (h inbox).run >>= g) :
    CachedOpening.ReachH P Q 0 hist ((exchange out >>= h).run >>= g) := by
  have he : (exchange (C := C) (G := RealSpec) out >>= h).run >>= g =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= fun inbox =>
        if C.parties.any (fun c => Msg.isAbort (inbox c)) then g none else (h inbox).run >>= g := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind, Option.elimM]
    refine bind_congr fun inbox => ?_
    by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
    · simp only [Option.elim, hab, ↓reduceIte, OptionT.run_failure, pure_bind]
    · simp only [Option.elim, hab, Bool.false_eq_true, ↓reduceIte, OptionT.run_pure, pure_bind]
  rw [he]
  exact CachedOpening.ReachH.here hist out _ hQ

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An exchange is one round before a wait of depth `n` of the rest. -/
theorem reachH_exchange_round {α γ : Type} {P : γ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    (n : ℕ) (hist : List (Query C × HashOutput)) (out : Mail C E) (h : Mail C E → PartyM C E RealSpec α)
    (g : Option α → OracleComp (PartySpec C E RealSpec) γ) (hgnone : ∃ y, g none = pure y ∧ P y)
    (hrest : ∀ inbox, CachedOpening.ReachH P Q n hist ((h inbox).run >>= g)) :
    CachedOpening.ReachH P Q (n + 1) hist ((exchange out >>= h).run >>= g) := by
  have he : (exchange (C := C) (G := RealSpec) out >>= h).run >>= g =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= fun inbox =>
        if C.parties.any (fun c => Msg.isAbort (inbox c)) then g none else (h inbox).run >>= g := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind, Option.elimM]
    refine bind_congr fun inbox => ?_
    by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
    · simp only [Option.elim, hab, ↓reduceIte, OptionT.run_failure, pure_bind]
    · simp only [Option.elim, hab, Bool.false_eq_true, ↓reduceIte, OptionT.run_pure, pure_bind]
  rw [he]
  refine CachedOpening.ReachH.round n hist out _ fun inbox => ?_
  change CachedOpening.ReachH P Q n hist
    (if C.parties.any (fun c => Msg.isAbort (inbox c)) then g none else (h inbox).run >>= g)
  by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
  · obtain ⟨y, hy, hPy⟩ := hgnone
    simp only [hab, ↓reduceIte, hy]
    exact CachedOpening.ReachH.early n hist y hPy
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    exact hrest inbox

omit [Fintype E] [DecidableEq E] in
/-- A peer reshare waits at its round, and each result with an output on an inbox has the output
`reshareZ` on that inbox. -/
theorem reachH_reshare {γ : Type} {P : γ → Prop} (ctx : Context C) (rnd : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ)
    (s : RunState C) (rel : γ → Shares C Bit → Prop) (g : Option (Shares C Bit × RunState C) →
      OracleComp (PartySpec C E RealSpec) γ)
    (hnone : ∀ inbox, ∀ y ∈ support (g none), rel y (reshareZ K (localContext ctx.self) bitCodec rnd.1 rnd.2 v count inbox))
    (hsome : ∀ inbox s', ∀ y ∈ support (g (some (reshareZ K (localContext ctx.self) bitCodec rnd.1 rnd.2 v count inbox, s'))),
      rel y (reshareZ K (localContext ctx.self) bitCodec rnd.1 rnd.2 v count inbox))
    (hist : List (Query C × HashOutput)) :
    CachedOpening.ReachH P (PeerWaitG K ctx.self count rel) 0 hist
      (((reshare K ctx bitCodec rnd v count).run s).run >>= g) := by
  obtain ⟨r, Z⟩ := rnd
  simp only [reshare, StateT.run_bind, StateT.run_lift, bind_assoc]
  refine reachH_exchange hist _ _ g ⟨r, Z, v, ?_, fun inbox x hx => ?_⟩
  · funext j
    rfl
  · by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
    · simp only [hab, ↓reduceIte] at hx
      exact hnone inbox x hx
    · simp only [hab, Bool.false_eq_true, ↓reduceIte, record, StateT.run_modify, StateT.run_pure, pure_bind,
        OptionT.run_pure] at hx
      exact hsome inbox _ x hx

omit [Fintype E] [DecidableEq E] in
/-- A collector reshare waits at its second round one round after its start, and each result with an
output on the forwards has the output `colZ`. -/
theorem reachH_reshareCollector {γ : Type} {P : γ → Prop} (ctx : Context C) (rnd : PrssOutput C Bit) (v : ℕ → Bit)
    (count : ℕ) (s : RunState C) (rel : γ → Shares C Bit → Prop)
    (g : Option (Shares C Bit × RunState C) → OracleComp (PartySpec C E RealSpec) γ)
    (hgnone : ∃ y, g none = pure y ∧ P y)
    (hnone : ∀ z, ∀ y ∈ support (g none), rel y z)
    (hsome : ∀ z s', ∀ y ∈ support (g (some (z, s'))), rel y z)
    (hist : List (Query C × HashOutput)) :
    CachedOpening.ReachH P (CollectorWaitG K ctx.self count rel) 1 hist
      (((reshareCollector K ctx rnd v count).run s).run >>= g) := by
  obtain ⟨r, Z⟩ := rnd
  simp only [reshareCollector, StateT.run_bind, StateT.run_lift, bind_assoc]
  refine reachH_exchange_round 0 hist _ _ g hgnone fun inbox => ?_
  simp only [pure_bind]
  refine reachH_exchange hist _ _ g ⟨r, Z, v, inbox, ?_, fun forward x hx => ?_⟩
  · funext h
    rfl
  · by_cases hab : C.parties.any (fun c => Msg.isAbort (forward c))
    · simp only [hab, ↓reduceIte] at hx
      exact hnone _ x hx
    · simp only [hab, Bool.false_eq_true, ↓reduceIte, record, StateT.run_modify, StateT.run_pure, pure_bind,
        OptionT.run_pure] at hx
      exact hsome _ _ x hx

omit [Fintype E] [DecidableEq E] in
/-- The reshare of one AND layer waits at its last round, and each result with an output has the
output of the reshare. -/
theorem reachH_mult {γ : Type} {P : γ → Prop} (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ)
    (s : RunState C) (rel : γ → Shares C Bit → Prop)
    (g : Option (Shares C Bit × RunState C) → OracleComp (PartySpec C E RealSpec) γ)
    (hgnone : ∃ y, g none = pure y ∧ P y)
    (hnone : ∀ z, ∀ y ∈ support (g none), rel y z)
    (hsome : ∀ z s', ∀ y ∈ support (g (some (z, s'))), rel y z)
    (hist : List (Query C × HashOutput)) :
    CachedOpening.ReachH P (ReshareWaitG K mode ctx.self count rel) (mode.rounds - 1) hist
      ((((realRunBuildingBlocks (G := RealSpec) K ctx mode).mult x y count).run s).run >>= g) := by
  simp only [realRunBuildingBlocks, StateT.run_bind]
  rw [show mode.rounds - 1 = 0 + (mode.rounds - 1) by omega]
  refine EchoRound.reachH_partyBind (runTimed_prssRandomness ctx _ 0 _ _) hgnone (fun hist q _ => ?_) hist
  cases mode with
  | peer =>
    exact reachH_reshare K ctx q.1 _ _ q.2 rel g (fun inbox y hy => hnone _ y hy)
      (fun inbox s' y hy => hsome _ s' y hy) hist
  | collector =>
    exact reachH_reshareCollector K ctx q.1 _ _ q.2 rel g hgnone hnone hsome hist

omit [Fintype E] [DecidableEq E] in
/-- The AND layers wait at the last round of layer `l`, after the rounds of the layers before it, and
each result has the output of that reshare at index `l`. -/
theorem reachH_recLayers {γ : Type} {P : γ → Prop} (ctx : Context C) (mode : ReshareMode) (cs : List Circuit)
    (inputs : List (C.Term → List Bit)) (l : ℕ) (rel : γ → Shares C Bit → Prop) :
    ∀ (n : ℕ), l < n → ∀ (s : RunState C) (g : Option ((ℕ → Shares C Bit) × RunState C) →
        OracleComp (PartySpec C E RealSpec) γ),
      (∃ y, g none = pure y ∧ P y) → (∀ z, ∀ y ∈ support (g none), rel y z) →
      (∀ a : (ℕ → Shares C Bit) × RunState C, ∀ y ∈ support (g (some a)), rel y (a.1 l)) →
      ∀ hist : List (Query C × HashOutput),
      CachedOpening.ReachH P (ReshareWaitG K mode ctx.self (gatesAt cs l).length rel)
        (l * mode.rounds + (mode.rounds - 1)) hist
        (((recLayers K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs n).run s).run >>= g)
  | 0, hl, _, _, _, _, _, _ => absurd hl (Nat.not_lt_zero l)
  | n + 1, hl, s, g, hgnone, hnone, hsome, hist => by
    unfold recLayers
    rw [List.range_succ, List.foldlM_append, ← recLayers, StateT.run_bind]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | rfl
    · rw [OptionT.run_bind, Option.elimM, bind_assoc]
      obtain ⟨y₀, hy₀, hP₀⟩ := hgnone
      refine reachH_recLayers ctx mode cs inputs l rel n hl' s _ ⟨y₀, by simp [hy₀], hP₀⟩
        (fun z y hy => ?_) (fun a y hy => ?_) hist
      · simp only [Option.elim, pure_bind] at hy
        exact hnone z y hy
      · simp only [Option.elim] at hy
        rw [StateT.run_map, OptionT.run_map, bind_map_left, mem_support_bind_iff] at hy
        obtain ⟨o, -, hy⟩ := hy
        rcases o with _ | b
        · exact hnone _ y hy
        · have h := hsome _ y hy
          simpa only [Option.map_some, Function.update_of_ne (Nat.ne_of_lt hl')] using h
    · refine EchoRound.reachH_partyBind (RecordedOpening.runTimed_recLayers K ctx mode cs inputs l s) hgnone
        (fun hist a _ => ?_) hist
      rw [StateT.run_map, OptionT.run_map, bind_map_left]
      refine reachH_mult K ctx mode _ _ _ a.2 rel _ ?_ (fun z y hy => ?_) (fun z s' y hy => ?_) hist
      · simpa only [Option.map_none] using hgnone
      · simp only [Option.map_none] at hy
        exact hnone z y hy
      · have h := hsome _ y hy
        simpa only [Option.map_some, Function.update_self] using h

omit [Fintype E] [DecidableEq E] in
/-- The plain head of a batch from the counters `(L, kk)` waits at the round of `Rerand` after its
AND layers, and each result with a head has the output of `Rerand` as `v'`. -/
theorem reachH_plainHead {γ : Type} {P : γ → Prop} (ctx : Context C) (parameter : PublicParameter) (jobs : List Job)
    (L kk : ℕ) (rel : γ → Shares C Bit → Prop)
    (g : Option ((BatchStart C × ℕ) × (ℕ × ℕ)) → OracleComp (PartySpec C E RealSpec) γ)
    (hgnone : ∃ y, g none = pure y ∧ P y) (hnone : ∀ z, ∀ y ∈ support (g none), rel y z)
    (hsome : ∀ d, ∀ y ∈ support (g (some d)), rel y d.1.1.v') (hist : List (Query C × HashOutput)) :
    CachedOpening.ReachH P (PeerWaitG K ctx.self (outputsOf (jobs.map (circuits parameter ·.kind))).length rel)
      (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds) hist
      (((plainHead K circuits settings ctx parameter jobs).run (L, kk)).run >>= g) := by
  simp only [plainHead, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
  rw [show depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds =
    0 + (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 0) by omega]
  refine EchoRound.reachH_partyBind ((timed_inputShares ctx jobs).bind fun _ => timed_pure _) hgnone
    (fun hist a _ => ?_) hist
  refine EchoRound.reachH_partyBind
    ((RecordedOpening.runTimed_recLayers K ctx settings.mode _ _ _ _).bind (n := 0) fun _ => timed_pure _) hgnone
    (fun hist a₁ _ => ?_) hist
  simp only [realRunBuildingBlocks, StateT.run_bind, bind_assoc]
  rw [show (0 : ℕ) = 0 + 0 from rfl]
  refine EchoRound.reachH_partyBind (runTimed_prssRandomness ctx _ 0 _ _) hgnone (fun hist q _ => ?_) hist
  rw [OptionT.run_bind, Option.elimM, bind_assoc]
  refine reachH_reshare K ctx q.1 _ _ q.2 rel _ (fun inbox y hy => ?_) (fun inbox s' y hy => ?_) hist
  · simp only [Option.elim, pure_bind] at hy
    exact hnone _ y hy
  · simp only [Option.elim, OptionT.run_pure, StateT.run_pure, pure_bind] at hy
    exact hsome _ y hy

omit [Fintype E] [DecidableEq E] in
/-- The plain head of a batch from the counters `(L, kk)` waits at the last round of AND layer `l`,
and each result with a head has the output of that reshare at index `l` of `zs`. -/
theorem reachH_plainHead_layer {γ : Type} {P : γ → Prop} (ctx : Context C) (parameter : PublicParameter)
    (jobs : List Job) (L kk : ℕ) (l : ℕ) (hl : l < depth (jobs.map (circuits parameter ·.kind)))
    (rel : γ → Shares C Bit → Prop)
    (g : Option ((BatchStart C × ℕ) × (ℕ × ℕ)) → OracleComp (PartySpec C E RealSpec) γ)
    (hgnone : ∃ y, g none = pure y ∧ P y) (hnone : ∀ z, ∀ y ∈ support (g none), rel y z)
    (hsome : ∀ d, ∀ y ∈ support (g (some d)), rel y (d.1.1.zs l)) (hist : List (Query C × HashOutput)) :
    CachedOpening.ReachH P (ReshareWaitG K settings.mode ctx.self (gatesAt (jobs.map (circuits parameter ·.kind)) l).length rel)
      (l * settings.mode.rounds + (settings.mode.rounds - 1)) hist
      (((plainHead K circuits settings ctx parameter jobs).run (L, kk)).run >>= g) := by
  simp only [plainHead, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
  rw [show l * settings.mode.rounds + (settings.mode.rounds - 1) =
    0 + (l * settings.mode.rounds + (settings.mode.rounds - 1)) by omega]
  refine EchoRound.reachH_partyBind ((timed_inputShares ctx jobs).bind fun _ => timed_pure _) hgnone
    (fun hist a _ => ?_) hist
  rw [bind_assoc, OptionT.run_bind, Option.elimM, bind_assoc]
  obtain ⟨y₀, hy₀, hP₀⟩ := hgnone
  refine reachH_recLayers K ctx settings.mode _ _ l rel _ hl _ _ ⟨y₀, by simp [hy₀], hP₀⟩
    (fun z y hy => ?_) (fun b y hy => ?_) hist
  · simp only [Option.elim, pure_bind] at hy
    exact hnone z y hy
  · simp only [Option.elim, OptionT.run_bind, pure_bind, Option.elimM, bind_assoc] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨o, -, hy⟩ := hy
    rcases o with _ | q
    · simp only [pure_bind] at hy
      exact hnone _ y hy
    · simp only [StateT.run_pure, OptionT.run_pure, pure_bind] at hy
      exact hsome _ y hy

/-- The self-recorded prefix reaches a wait at the depth `headStart + n` when the plain head of batch
`k` reaches it at the depth `n` for each continuation that keeps the relation `rel` with the value
`out` of the head. -/
theorem reachH_preGhost (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hkeys : c.keys i = some keys) (out : BatchStart C → Shares C Bit)
    (W : (Option (Joint.PreOut C) × Option (Joint.PreOut C) → Shares C Bit → Prop) → List (Query C × HashOutput) →
      Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) (Option (Joint.PreOut C) × Option (Joint.PreOut C))) →
        Prop)
    (n : ℕ)
    (hhead : ∀ (prss : PrssKeys C) (L kk : ℕ)
      (rel : Option (Joint.PreOut C) × Option (Joint.PreOut C) → Shares C Bit → Prop)
      (g : Option ((BatchStart C × ℕ) × (ℕ × ℕ)) →
        OracleComp (PartySpec C E RealSpec) (Option (Joint.PreOut C) × Option (Joint.PreOut C))),
      (∃ y, g none = pure y ∧ y.2 = none) → (∀ z, ∀ y ∈ support (g none), rel y z) →
      (∀ d, ∀ y ∈ support (g (some d)), rel y (out d.1.1)) → ∀ hist,
      CachedOpening.ReachH (fun x => x.2 = none) (W rel) n hist
        (((plainHead K circuits settings ⟨i, keys, prss⟩ keys.parameter
          ((chunks settings.batchSize c.jobs).getD k [])).run (L, kk)).run >>= g)) :
    CachedOpening.ReachH (fun x => x.2 = none) (W (HeadRel out))
      (headStart circuits settings keys.parameter c.jobs k + n) [] (preGhost K circuits settings k i c) := by
  rw [preGhost_eq K circuits settings k i c keys hkeys, map_eq_bind_pure_comp, StateT.run_bind]
  unfold headStart
  rw [Nat.add_assoc]
  refine EchoRound.reachH_partyBind (RunTimed.lift (timed_prssSetup i) c.counters) ?_ (fun hist a _ => ?_) []
  · exact ⟨(none, none), rfl, rfl⟩
  rw [StateT.run_bind]
  refine EchoRound.reachH_partyBind (runTimed_mapM_realBatch K circuits settings _ _ _ a.2) ?_
    (fun hist b _ => ?_) hist
  · exact ⟨(none, none), rfl, rfl⟩
  obtain ⟨outs, L, kk⟩ := b
  show CachedOpening.ReachH _ _ _ hist (((plainHead K circuits settings ⟨i, keys, a.1⟩ keys.parameter
    ((chunks settings.batchSize c.jobs).getD k []) >>= fun h => pure (a.1, outs, h)).run (L, kk)).run >>= _)
  rw [StateT.run_bind, OptionT.run_bind, Option.elimM, bind_assoc]
  refine hhead a.1 L kk (HeadRel out) _ ?_ (fun z y hy p hp => ?_) (fun d y hy p hp => ?_) hist
  · exact ⟨(none, none), by simp, rfl⟩
  · simp only [Option.elim, pure_bind, Function.comp_apply, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    cases hp
  · simp only [Option.elim, StateT.run_pure, OptionT.run_pure, pure_bind, Function.comp_apply, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    cases hp
    rfl

/-- `HeadReach` holds. -/
theorem headReach : HeadReach K circuits settings := by
  intro k i σ c keys hkeys hk
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [Nat.add_assoc]
    exact reachH_preGhost K circuits settings k i c keys hkeys (fun b => b.zs l)
      (ReshareWaitG K settings.mode i _) _ fun prss L kk rel g hg hn hs hist =>
        reachH_plainHead_layer K circuits settings ⟨i, keys, prss⟩ keys.parameter _ L kk l hl rel g hg hn hs hist
  · exact reachH_preGhost K circuits settings k i c keys hkeys (fun b => b.v') (PeerWaitG K i _) _
      fun prss L kk rel g hg hn hs hist =>
        reachH_plainHead K circuits settings ⟨i, keys, prss⟩ keys.parameter _ L kk rel g hg hn hs hist

end CutBudget

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.headReach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.headReach

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.headDraws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.headDraws
