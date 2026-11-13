import ThresholdLeanXmssSecurity.Proof.TreeTwinDrawReplay

/-!
# Batch replay at the final actual cache

Peer and collector batch entries retain the answers for the same PRSS masks
that define their suspended steps. Sequential batches carry those answers to
the final shared cache; next-peer resumptions export mask coherence there.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open ThresholdLeanXmssSecurity.TreeTwinDrawReplay
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinBatchReplay
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

def ReshareEntryRelAt (D : C.Coalition) (cache : HashCache C × HiddenCache C) (mode : ReshareMode) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : Context C) (idx count : ℕ) (v₁ v₂ : ℕ → Bit)
    (st₁ st₂ : RunState C)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (x y : Step C E RealSpec TreeOutput) : Prop :=
  match mode with
  | .peer => TreeSimPeerRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y
  | .collector => TreeSimCollectorEntryRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y

theorem ReshareEntryRelAt_rel {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {mode : ReshareMode} {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C}
    {idx count : ℕ} {v₁ v₂ : ℕ → Bit} {st₁ st₂ : RunState C}
    {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput}
    {x y : Step C E RealSpec TreeOutput}
    (h : ReshareEntryRelAt prims K D cache mode δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y) :
    TreeStagesReshareEntryRel K mode δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y := by
  cases mode with
  | peer => exact TreeSimPeerRelAt_rel prims K h
  | collector => exact TreeSimCollectorEntryRelAt_rel prims K h

theorem ReshareEntryRelAt_mono {D : C.Coalition} {cache cache' : HashCache C × HiddenCache C}
    {mode : ReshareMode} {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C}
    {idx count : ℕ} {v₁ v₂ : ℕ → Bit} {st₁ st₂ : RunState C}
    {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput}
    {x y : Step C E RealSpec TreeOutput}
    (hash : cache.1 ≤ cache'.1) (hidden : cache.2 ≤ cache'.2)
    (h : ReshareEntryRelAt prims K D cache mode δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y) :
    ReshareEntryRelAt prims K D cache' mode δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y := by
  cases mode with
  | peer => exact TreeSimPeerRelAt_mono prims K hash hidden h
  | collector => exact TreeSimCollectorEntryRelAt_mono prims K hash hidden h

-- Port of TreeSimStages.treeStages_reshare_entry.
theorem reshare_entry_at (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (mode : ReshareMode) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C) (label : st₁.label = st₂.label)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (advance
        ((treeStagesReshareProgram K ctx₁ mode idx count v₁ st₁ k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (free (advance
        ((treeStagesReshareProgram K ctx₂ mode idx count v₂ st₂ k₂).run)))).run b)
      (fun u z => ReshareEntryRelAt prims K D u.2.1 mode δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  cases mode with
  | peer =>
    exact peer_start_mixed_at prims K D δ visible ctx₁ ctx₂ self keys idx count
      v₁ v₂ st₁ st₂ label k₁ k₂ a b related
  | collector =>
    exact collector_entry_mixed_at prims K D δ visible ctx₁ ctx₂ self keys idx count
      v₁ v₂ st₁ st₂ label k₁ k₂ a b related

-- Port of TreeSimStages.treeStages_batch_entry with the strengthened reshare post.
theorem batch_entry_at (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (mode : ReshareMode) (jobs : List Job) (idx count : ℕ) (base : HashCache C)
    (covered₁ : TreeStagesPrfCovered base ctx₁.keys.seed jobs)
    (covered₂ : TreeStagesPrfCovered base ctx₂.keys.seed jobs)
    (value₁ value₂ : List (C.Term → List Bit) → ℕ → Bit)
    (st₁ st₂ : RunState C) (label : st₁.label = st₂.label)
    (k₁ k₂ : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (base_le : base ≤ a.1.1) :
    let inputs₁ := jobs.map (treeStagesCachedInputs base ctx₁)
    let inputs₂ := jobs.map (treeStagesCachedInputs base ctx₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((treeStagesBatchProgram K ctx₁ mode jobs idx count value₁ st₁ k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((treeStagesBatchProgram K ctx₂ mode jobs idx count value₂ st₂ k₂).run)))).run b)
      (fun u z => ReshareEntryRelAt prims K D u.2.1 mode δ ctx₁ ctx₂ idx count (value₁ inputs₁) (value₂ inputs₂)
        st₁ st₂ (k₁ inputs₁) (k₂ inputs₂) u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  have base_le₂ : base ≤ b.1 := by rw [← related.1]; exact base_le
  have replay₁ := treeStages_inputQueries_replay prims D ctx₁ jobs a.1
    (treeStages_prfCovered_mono base_le _ _ covered₁)
  have replay₂ := treeStages_inputQueries_replay prims D ctx₂ jobs b
    (treeStages_prfCovered_mono base_le₂ _ _ covered₂)
  rw [← treeStages_cachedInputs_mono base_le ctx₁ jobs covered₁] at replay₁
  rw [← treeStages_cachedInputs_mono base_le₂ ctx₂ jobs covered₂] at replay₂
  unfold treeStagesBatchProgram
  simp only [inputShares_fun, mapM_oracleStep, worldRoles, advance_oracleStep_bind,
    free_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeStages_readOnly_pair prims D _ _ a b _ _ replay₁ replay₂)
  intro u z hu
  rw [hu.1, hu.2.1]
  have rel : TreeSimStreamRel δ u.2 z.2 := by
    simpa only [TreeSimStreamRel, hu.2.2.1, hu.2.2.2] using related
  apply relTriple_post_mono (treeSim_relTriple_support (reshare_entry_at prims K D δ visible mode
    ctx₁ ctx₂ self keys idx count _ _ st₁ st₂ label _ _ u.2 z.2 rel))
  intro x y hxy
  have grows : base ≤ u.2.1.1 := by rw [hu.2.2.1]; exact base_le
  exact ⟨hxy.1.1, hxy.1.2, grows.trans (treeSim_logged_grows prims D _ u.2 x hxy.2.1)⟩

def BatchRelAt (D : C.Coalition) (cache : HashCache C × HiddenCache C) {base : HashCache C} (d : TreeStagesBatchData C E base)
    (δ : HiddenAddress C → Bit) (x y : Step C E RealSpec TreeOutput) : Prop :=
  let inputs₁ := d.jobs.map (treeStagesCachedInputs base d.ctx₁)
  let inputs₂ := d.jobs.map (treeStagesCachedInputs base d.ctx₂)
  ReshareEntryRelAt prims K D cache d.mode δ d.ctx₁ d.ctx₂ d.idx d.count (d.value₁ inputs₁) (d.value₂ inputs₂)
    d.st₁ d.st₂ (d.k₁ inputs₁) (d.k₂ inputs₂) x y

theorem BatchRelAt_rel {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {base : HashCache C} {d : TreeStagesBatchData C E base} {δ : HiddenAddress C → Bit}
    {x y : Step C E RealSpec TreeOutput} (h : BatchRelAt prims K D cache d δ x y) :
    d.rel K δ x y := ReshareEntryRelAt_rel prims K h

theorem BatchRelAt_mono {D : C.Coalition} {cache cache' : HashCache C × HiddenCache C}
    {base : HashCache C} {d : TreeStagesBatchData C E base} {δ : HiddenAddress C → Bit}
    {x y : Step C E RealSpec TreeOutput}
    (hash : cache.1 ≤ cache'.1) (hidden : cache.2 ≤ cache'.2)
    (h : BatchRelAt prims K D cache d δ x y) : BatchRelAt prims K D cache' d δ x y :=
  ReshareEntryRelAt_mono prims K hash hidden h

-- Specialization of batch_entry_at to the original batch data.
theorem batchData_entry_at {base : HashCache C} (d : TreeStagesBatchData C E base)
    (D : C.Coalition) (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (d.real K).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance (d.ideal K).run))).run b)
      (fun u z => BatchRelAt prims K D u.2.1 d δ u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) :=
  batch_entry_at prims K D δ visible d.ctx₁ d.ctx₂ d.self d.keys d.mode d.jobs d.idx d.count
    base d.covered₁ d.covered₂ d.value₁ d.value₂ d.st₁ d.st₂ d.label d.k₁ d.k₂ a b related grows

-- Port of TreeSimStages.treeStages_batch_start using stable sequential replay.
theorem batch_start_at (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => (d i).real K))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => (d i).ideal K))).run b)
      (fun u z => (∀ i, if i ∈ D.1 then u.1 i = .done none ∧ z.1 i = .done none
          else BatchRelAt prims K D u.2.1 (d i) δ (u.1 i) (z.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  simp only [startSteps, simulateQ_sequenceFin]
  apply sequenceFin_rel_stable _ _ (fun a b => TreeSimStreamRel δ a b ∧ base ≤ a.1.1)
    (fun i u z s => if i ∈ D.1 then u = .done none ∧ z = .done none
      else BatchRelAt prims K D s.1 (d i) δ u z)
  · intro i u z s j t h ht
    by_cases hi : i ∈ D.1
    · simpa only [if_pos hi] using h
    · simp only [if_neg hi] at h ⊢
      have grows := logged_caches_grow prims D _ s t ht
      exact BatchRelAt_mono prims K grows.1 grows.2 h
  · intro i a b h
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨rfl, rfl⟩, h⟩
    · simp only [if_neg hi, worldRoles]
      exact batchData_entry_at prims K (d i) D δ visible a b h.1 h.2
  · exact ⟨related, grows⟩

-- Pure adaptor of the batch vector used at TreeSimStages:8530/9218.
theorem batch_peer_resume_at (cache : HashCache C × HiddenCache C) (D : C.Coalition)
    (base : HashCache C) (d : C.Party → TreeStagesBatchData C E base)
    (δ : HiddenAddress C → Bit) (count : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .peer)
    (index : ∀ i, i ∉ D.1 → (d i).idx = 0)
    (size : ∀ i, i ∉ D.1 → (d i).count = count)
    (x y : C.Party → Step C E RealSpec TreeOutput)
    (h : ∀ i, if i ∈ D.1 then x i = .done none ∧ y i = .done none
      else BatchRelAt prims K D cache (d i) δ (x i) (y i)) :
    TreeStagesPeerResumeRelAt prims K cache D (fun _ => true) δ
      (fun i => (d i).ctx₁) (fun i => (d i).ctx₂) 0 count
      (fun i => (d i).value₁ (d i).input₁) (fun i => (d i).value₂ (d i).input₂)
      (fun i => (d i).st₁) (fun i => (d i).st₂)
      (fun i => (d i).k₁ (d i).input₁) (fun i => (d i).k₂ (d i).input₂) x y := by
  intro i
  by_cases hi : i ∈ D.1
  · simpa only [if_pos hi] using h i
  · simpa only [if_neg hi, Bool.true_eq, if_true, BatchRelAt, mode i hi,
      ReshareEntryRelAt, index i hi, size i hi, TreeStagesBatchData.input₁,
      TreeStagesBatchData.input₂] using h i

-- Port of TreeSimStages.treeStages_batch_collector_start retaining each answer.
theorem batch_collector_start_at (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (T₀ : C.Term) (ρ idx count : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .collector)
    (index : ∀ i, i ∉ D.1 → (d i).idx = idx)
    (size : ∀ i, i ∉ D.1 → (d i).count = count)
    (self₁ : ∀ i, i ∉ D.1 → (d i).ctx₁.self = i)
    (self₂ : ∀ i, i ∉ D.1 → (d i).ctx₂.self = i)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count
      ((fun i => (d i).value₁ (d i).input₁) - (fun i => (d i).value₂ (d i).input₂)) x = 0) :
    let v₁ := fun i => (d i).value₁ (d i).input₁
    let v₂ := fun i => (d i).value₂ (d i).input₂
    let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => (d i).real K))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => (d i).ideal K))).run b)
      (fun u z => (∃ rnd₁ rnd₂ : C.Party → PrssOutput C Bit,
        (∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
          (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i) ∧
        u.1 = treeSimCollectorWaiting K D count rnd₁ v₁ (fun i => (d i).st₁) (fun i => (d i).k₁ (d i).input₁) ∧
        z.1 = treeSimCollectorWaiting K D count rnd₂ v₂ (fun i => (d i).st₂) (fun i => (d i).k₂ (d i).input₂) ∧
        (∀ i, i ∉ D.1 → DrawAnswered prims D u.2.1 (d i).ctx₁ ρ idx count (rnd₁ i))) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  intro v₁ v₂ δ
  have visible' : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  apply relTriple_post_mono (batch_start_at prims K D base d δ visible' a b
    ⟨related.1, treeSim_hiddenRel_extend past _ related.2 fresh⟩ grows)
  intro u z h
  have witnesses : ∀ i, ∃ r₁ r₂ : PrssOutput C Bit,
      (i ∉ D.1 → r₂ = r₁ + frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
        (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i) ∧
      u.1 i = (if i ∈ D.1 then .done none else treeSimCollectorStep K (localContext i) r₁
        (v₁ i) count (d i).st₁ ((d i).k₁ (d i).input₁)) ∧
      z.1 i = (if i ∈ D.1 then .done none else treeSimCollectorStep K (localContext i) r₂
        (v₂ i) count (d i).st₂ ((d i).k₂ (d i).input₂)) ∧
      (i ∉ D.1 → DrawAnswered prims D u.2.1 (d i).ctx₁ ρ idx count r₁) := by
    intro i
    have hiRel := h.1 i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi] at hiRel ⊢
      exact ⟨0, 0, fun hn => (hn hi).elim, hiRel.1, hiRel.2, fun hn => (hn hi).elim⟩
    · simp only [if_neg hi, BatchRelAt, mode i hi, ReshareEntryRelAt] at hiRel
      obtain ⟨r₁, r₂, hm₁, hm₂, hu, hz, answered⟩ := hiRel
      have shift : treeSimPrssShift δ (d i).ctx₁ (d i).st₁.label (d i).idx (d i).count =
          frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
            (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i := by
        rw [label i hi, index i hi, size i hi]
        dsimp only [δ]
        rw [treeSim_prssShift_add, treeSim_prssShift_zero past (d i).ctx₁ ρ idx count block, zero_add]
        unfold treeSimCollectorShift
        rw [treeSim_prssShift_block D (d i).ctx₁ (by simpa [self₁ i hi] using hi), self₁ i hi]
      rw [shift] at hm₁ hm₂
      refine ⟨r₁, r₂, fun _ => Prod.ext hm₁ hm₂, ?_, ?_, ?_⟩
      · simpa only [if_neg hi, treeSimCollectorStep, localContext, self₁ i hi, size i hi, v₁, TreeStagesBatchData.input₁] using hu
      · simpa only [if_neg hi, treeSimCollectorStep, localContext, self₂ i hi, size i hi, v₂, TreeStagesBatchData.input₂] using hz
      · intro _
        simpa only [label i hi, index i hi, size i hi] using answered
  choose rnd₁ rnd₂ masks realStep idealStep answered using witnesses
  exact ⟨⟨rnd₁, rnd₂, masks, funext realStep, funext idealStep, answered⟩, h.2⟩

-- Port of TreeSimStages.TreeStagesPeerNext.coupling with the same mask witnesses.
theorem peerNext_coupling_at (D : C.Coalition)
    (past : HiddenAddress C → Bit) (initial : HiddenCache C) (k₁ k₂ out₁ out₂)
    (n : TreeStagesPeerNext K D past initial k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (related : TreeSimStreamRel past a b)
    (ha : a.1.2 = initial) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeSimStreamRel (n.δ K) u.2 z.2 ∧
        TreeSimFutureEmpty (n.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (n.ρ + 1) z.2.2 ∧
        TreeSimFutureZero (n.ρ + 1) (n.δ K) ∧
        ∃ rnd₁ rnd₂, ∃ _masks : n.Masks K rnd₁ rnd₂,
          u.1 = treeSimPeerPartial K D n.ctx₁ n.live n.count rnd₁ n.v₁ n.st₁ n.next₁ ∧
          z.1 = treeSimPeerPartial K D n.ctx₂ n.live n.count rnd₂ n.v₂ n.st₂ n.next₂ ∧
          TreeTwinHolderKeys.DrawCoherent prims D (fun i => n.live i = true)
            u.2.1 n.ctx₁ n.ρ n.count rnd₁) := by
  have visible : ∀ x, ¬ Hidden D x.1.1 → n.δ K x = 0 := by
    intro x hx
    simp only [TreeStagesPeerNext.δ, Pi.add_apply, n.visible x hx, treeSimPeerShift,
      treeSim_blockShift_visible D n.ρ 0 n.count _ _ x hx, add_zero]
  have fresh : ∀ x, (a.1.2 x).isSome →
      treeSimPeerShift K D n.T₀ n.pivotParty n.ρ 0 n.count (n.v₁ - n.v₂) 0 x = 0 := by
    rw [ha]
    exact treeSim_futureEmpty_block D n.ρ 0 n.count _ _ initial n.futureEmpty
  apply relTriple_post_mono (treeSim_relTriple_support (peer_resume_entry_at prims K D (n.δ K) visible
    n.live n.ctx₁ n.ctx₂ (fun i hi => (n.self₁ i hi).trans (n.self₂ i hi).symm) n.keys 0 n.count
    n.v₁ n.v₂ n.st₁ n.st₂ (fun i hi => (n.lab₁ i hi).trans (n.lab₂ i hi).symm)
    k₁ k₂ n.next₁ n.next₂ out₁ out₂ n.x₁ n.x₂ n.shape₁ n.shape₂ n.program₁ n.program₂ a b
    ⟨related.1, treeSim_hiddenRel_extend past _ related.2 fresh⟩))
  intro u z h
  have frame₁ := treeStages_peer_resume_logged_frame prims K D n.ctx₁ n.ρ 0 n.count n.v₁ n.st₁
    k₁ n.next₁ out₁ n.x₁ n.live (fun i hi _ => n.lab₁ i hi) n.shape₁ n.program₁ a u h.2.1
  have frame₂ := treeStages_peer_resume_frame prims K D n.ctx₂ n.ρ 0 n.count n.v₂ n.st₂
    k₂ n.next₂ out₂ n.x₂ n.live (fun i hi _ => n.lab₂ i hi) n.shape₂ n.program₂ b z h.2.2
  have empty : TreeSimFutureEmpty n.ρ a.1.2 := by simpa only [ha] using n.futureEmpty
  obtain ⟨rnd₁, rnd₂, masks, realSteps, idealSteps, coherent⟩ :=
    peer_resume_masks_at prims K D u.2.1 n.ρ n.live (n.δ K)
    n.ctx₁ n.ctx₂ n.count n.v₁ n.v₂ n.st₁ n.st₂ n.next₁ n.next₂ u.1 z.1 n.self₁ (fun i hi _ => n.lab₁ i hi) h.1.1
  exact ⟨h.1.2, treeSim_futureEmpty_after empty frame₁,
    treeSim_futureEmpty_after (treeSim_futureEmpty_related empty related.2) frame₂,
    treeSim_futureZero_extend D n.ρ 0 n.count _ _ past n.futureZero,
    rnd₁, rnd₂, masks, realSteps, idealSteps, coherent⟩

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.ReshareEntryRelAt_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReshareEntryRelAt_rel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.ReshareEntryRelAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReshareEntryRelAt_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.reshare_entry_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reshare_entry_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.batch_entry_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_entry_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.BatchRelAt_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchRelAt_rel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.BatchRelAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchRelAt_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.batchData_entry_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchData_entry_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.batch_start_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_start_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.batch_peer_resume_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_peer_resume_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.batch_collector_start_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_collector_start_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBatchReplay.peerNext_coupling_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms peerNext_coupling_at

end ThresholdLeanXmssSecurity.TreeTwinBatchReplay
