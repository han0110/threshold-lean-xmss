import ThresholdLeanXmssSecurity.Proof.TreeTwinValueCarry

/-! # Layer schedule bookkeeping

Batch code, positions, counts and aligned share lists pass through actual layer
records. Peer exits preserve the saved data relation using their product shift.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinLayerBook
open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinValueCarry
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

section Batch
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
  (D : C.Coalition) (parameter : PublicParameter) (openings : List (List (List Bit)))

theorem batchLink_tags (code : TreeTwinCode C E) (st st' : C.Party → RunState C)
    (link : BatchLink K circuits settings top tree D parameter openings code st)
    (tag : ∀ i, i ∉ D.1 → (st' i).tag = (st i).tag) :
    BatchLink K circuits settings top tree D parameter openings code st' := by
  obtain ⟨site, prior, circs, tags, rest⟩ := link
  exact ⟨site, prior, circs, fun i hi => ⟨(tag i hi).trans (tags i hi).1, (tags i hi).2⟩, rest⟩

theorem batchLink_modes (code : TreeTwinCode C E) (st : C.Party → RunState C)
    (link : BatchLink K circuits settings top tree D parameter openings code st) :
    ∀ i, (code.2.2.2.1 i).mode = (code.2.2.1 i).mode := by
  obtain ⟨site, prior, circs, tags, real, ideal, rest⟩ := link
  intro i
  exact (congrArg (fun f : C.Party → RunGadgets C E RealSpec => (f i).mode) ideal).trans
    (congrArg (fun f : C.Party → RunGadgets C E RealSpec => (f i).mode) real).symm

theorem count₁_of_rerand (c : Caller K circuits settings top tree D parameter openings)
    (count : ∀ i, i ∉ D.1 → ((c.rest.p₁ i).2.map (·.count)).sum +
      (outputsOf c.rest.circs).length = tupleCount c.rest.circs) :
    ∀ i, i ∉ D.1 → c.count₁ K circuits settings top tree D parameter openings i =
      tupleCount c.rest.circs := by
  intro i hi
  simpa [Caller.count₁, Caller.checkData, TreeStagesRerandTail.checkCoinData,
    hi, treeStagesRerandTuples] using count i hi
end Batch

theorem tailCode_last (D : C.Coalition) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (h : s.rest = []) :
    treeTwinTailCode K D (s.last K D d h) = treeTwinScheduleCode K D s := rfl

theorem position_succ (circuits : Circuits) (settings : Settings) (tree : Tree)
    (D : C.Coalition) (parameter : PublicParameter) (circs : List Circuit) (layer : ℕ)
    (st st' : C.Party → RunState C)
    (pos : Position circuits settings tree D parameter circs layer st)
    (tag : ∀ i, i ∉ D.1 → (st' i).tag = (st i).tag)
    (lab : ∀ i, i ∉ D.1 → (st' i).label = (st i).label + 1)
    (bound : layer + 1 ≤ depth circs) :
    Position circuits settings tree D parameter circs (layer + 1) st' := by
  apply position_shift circuits settings tree D parameter circs layer 1 st st' pos tag lab
  intro jobs eq
  subst circs
  change layer + 1 ≤ depth (runCircuits circuits parameter jobs) + 1 + _
  omega

theorem position_rerandCoin (circuits : Circuits) (settings : Settings) (tree : Tree)
    (D : C.Coalition) (parameter : PublicParameter) (circs : List Circuit)
    (st st' : C.Party → RunState C)
    (pos : Position circuits settings tree D parameter circs (depth circs) st)
    (tag : ∀ i, i ∉ D.1 → (st' i).tag = (st i).tag)
    (lab : ∀ i, i ∉ D.1 → (st' i).label = (st i).label + 1) :
    Position circuits settings tree D parameter circs (depth circs + 1) st' := by
  apply position_shift circuits settings tree D parameter circs (depth circs) 1 st st' pos tag lab
  intro jobs eq
  subst circs
  change depth (runCircuits circuits parameter jobs) + 1 ≤
    depth (runCircuits circuits parameter jobs) + 1 + _
  omega

theorem range_drop_next (n layer next : ℕ) (rest : List ℕ)
    (eq : (List.range n).drop layer = layer :: next :: rest) :
    (List.range n).drop next = next :: rest ∧ layer + 1 < n := by
  have successor := range_drop_succ n layer next rest eq
  have len := congrArg List.length eq
  simp only [List.length_drop, List.length_range, List.length_cons] at len
  constructor
  · rw [successor, ← List.drop_drop, eq]
    simp only [List.drop_succ_cons, List.drop_zero, successor]
  · omega

theorem countSum_cons (D : C.Coalition) (circs : List Circuit) (layer : ℕ)
    (rest : List ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (mode : C.Party → ReshareMode) (z : C.Party → Shares C Bit)
    (count : ∀ i, i ∉ D.1 → ((p i).2.map (·.count)).sum +
      ((layer :: rest).map (fun l => (gatesAt circs l).length)).sum +
      (outputsOf circs).length = tupleCount circs) :
    ∀ i, i ∉ D.1 →
      (((treeTwinLayerShares K circs layer (mode i) (p i) (z i)).2).map (·.count)).sum +
      (rest.map (fun l => (gatesAt circs l).length)).sum +
      (outputsOf circs).length = tupleCount circs := by
  intro i hi
  simpa [treeTwinLayerShares, Nat.add_assoc] using count i hi

theorem countSum_nil (D : C.Coalition) (circs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C))
    (mode : C.Party → ReshareMode) (z : C.Party → Shares C Bit)
    (count : ∀ i, i ∉ D.1 → ((p i).2.map (·.count)).sum +
      ([layer].map (fun l => (gatesAt circs l).length)).sum +
      (outputsOf circs).length = tupleCount circs) :
    ∀ i, i ∉ D.1 →
      (((treeTwinLayerShares K circs layer (mode i) (p i) (z i)).2).map (·.count)).sum +
      (outputsOf circs).length = tupleCount circs := by
  simpa using countSum_cons K D circs layer [] p mode z count

theorem nonzero_of_count (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (circs : List Circuit) (p₁ p₂ : C.Party → MainInput C × List (Tuple C))
    (count : ∀ i, i ∉ D.1 → ((p₁ i).2.map (·.count)).sum +
      (outputsOf circs).length = tupleCount circs)
    (data : TreeTwinRunData K D ctx₁ ctx₂ p₁ p₂) (nonzero : tupleCount circs ≠ 0) :
    (∀ i, i ∉ D.1 → ((p₁ i).2.map (·.count)).sum + (outputsOf circs).length ≠ 0) ∧
    (∀ i, i ∉ D.1 → ((p₂ i).2.map (·.count)).sum + (outputsOf circs).length ≠ 0) := by
  constructor
  · intro i hi
    rw [count i hi]
    exact nonzero
  · intro i hi
    rw [(treeTwinRunData_counts_modes K D ctx₁ ctx₂ p₁ p₂ data i hi).1, count i hi]
    exact nonzero

theorem rerandCoinNext_tagLabel (D : C.Coalition) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (verify₁ : ∀ i, i ∉ D.1 → (tail.gadgets₁ i).verify =
      check K (d.ctx₁ i) (realCheckGadgets K (d.ctx₁ i)))
    (verify₂ : ∀ i, i ∉ D.1 → (tail.gadgets₂ i).verify =
      check K (d.ctx₂ i) (realCheckGadgets K (d.ctx₂ i)))
    (nonzero₁ : ∀ i, i ∉ D.1 →
      ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 →
      ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (sent : C.Party → Mail C E) :
    let n := tail.coinNext K D d keys verify₁ verify₂ nonzero₁ nonzero₂ sent
    ∀ i, ((n.st₁ i).tag = (d.st₁ i).tag ∧ (n.st₁ i).label = (d.st₁ i).label + 1) ∧
      ((n.st₂ i).tag = (d.st₂ i).tag ∧ (n.st₂ i).label = (d.st₂ i).label + 1) := by
  dsimp only
  intro i
  constructor
  · constructor
    · change ((treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i).getD
        (0, nextLabel (d.st₁ i))).2.tag = (d.st₁ i).tag
      unfold treeSimPeerOutputs treeSimPeerReturn
      split_ifs <;> rfl
    · exact treeStages_peer_recorded_label K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i
  · constructor
    · change ((treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i).getD
        (0, nextLabel (d.st₂ i))).2.tag = (d.st₂ i).tag
      unfold treeSimPeerOutputs treeSimPeerReturn
      split_ifs <;> rfl
    · exact treeStages_peer_recorded_label K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i

/-- Honest parties have equal numbers of saved wire blocks and tuples. -/
def SharesAligned (D : C.Coalition) (p : C.Party → MainInput C × List (Tuple C)) : Prop :=
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (p i).1.length = (p j).1.length) ∧
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (p i).2.length = (p j).2.length)

theorem sharesAligned_cachedInputs (D : C.Coalition) (base : HashCache C)
    (ctx : C.Party → Context C) (jobs : List Job) :
    SharesAligned D (fun i => (jobs.map (treeStagesCachedInputs base (ctx i)), [])) := by
  constructor <;> intro i j hi hj <;> simp

theorem sharesAligned_layerShares (D : C.Coalition) (circs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C))
    (mode : C.Party → ReshareMode) (z : C.Party → Shares C Bit) (aligned : SharesAligned D p) :
    SharesAligned D (fun i => treeTwinLayerShares K circs layer (mode i) (p i) (z i)) := by
  constructor
  · intro i j hi hj
    simpa only [treeTwinLayerShares, treeTwin_appendLayer_length] using aligned.1 i j hi hj
  · intro i j hi hj
    simp only [treeTwinLayerShares, List.length_append, List.length_cons, List.length_nil,
      aligned.2 i j hi hj]

theorem tuplesAligned_of_layerCounts (D : C.Coalition) (circs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (counts : LayerCounts D circs layer p) :
    ∀ i j, i ∉ D.1 → j ∉ D.1 → (p i).2.length = (p j).2.length := by
  intro i j hi hj
  have eq := (counts i hi).trans (counts j hj).symm
  simpa only [List.length_map] using congrArg List.length eq

theorem treeTwinRunData_peerExit (D : C.Coalition) (d : TreeSimPeerData K D)
    (circs : List Circuit) (layer : ℕ) (p₁ p₂ : C.Party → MainInput C × List (Tuple C))
    (data : TreeTwinRunData K D d.ctx₁ d.ctx₂ p₁ p₂)
    (count : d.count = (gatesAt circs layer).length)
    (v₁ : ∀ i, i ∉ D.1 → d.v₁ i =
      mulRep K (d.ctx₁ i) (layerX K circs layer (p₁ i).1) (layerY K circs layer (p₁ i).1))
    (v₂ : ∀ i, i ∉ D.1 → d.v₂ i =
      mulRep K (d.ctx₂ i) (layerX K circs layer (p₂ i).1) (layerY K circs layer (p₂ i).1))
    (mode₁ mode₂ : C.Party → ReshareMode) (modes : ∀ i, i ∉ D.1 → mode₂ i = mode₁ i)
    (aligned : SharesAligned D p₁) (x₁ x₂ : C.Party → Shares C Bit × RunState C)
    (exits : ∀ i, i ∉ D.1 → TreeSimPeerExitRel K D d i (x₁ i) (x₂ i)) :
    TreeTwinRunData K D d.ctx₁ d.ctx₂
      (fun i => treeTwinLayerShares K circs layer (mode₁ i) (p₁ i) (x₁ i).1)
      (fun i => treeTwinLayerShares K circs layer (mode₂ i) (p₂ i) (x₂ i).1) := by
  refine treeTwinRunData_layer K D d.ctx₁ d.ctx₂ circs layer _ _ p₁ p₂ _ _ data
    aligned.1 aligned.2 modes fun i hi => ?_
  rw [(exits i hi).1, count]
  congr 1
  funext g
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Pi.sub_apply, Pi.sub_apply, v₁ j (Finset.mem_filter.1 hj).2, v₂ j (Finset.mem_filter.1 hj).2]

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.batchLink_tags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchLink_tags

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.batchLink_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchLink_modes

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.count₁_of_rerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count₁_of_rerand

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.tailCode_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tailCode_last

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.position_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms position_succ

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.position_rerandCoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms position_rerandCoin

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.range_drop_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms range_drop_next

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.countSum_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countSum_cons

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.countSum_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countSum_nil

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.nonzero_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonzero_of_count

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.rerandCoinNext_tagLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rerandCoinNext_tagLabel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.sharesAligned_cachedInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sharesAligned_cachedInputs

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.sharesAligned_layerShares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sharesAligned_layerShares

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.tuplesAligned_of_layerCounts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tuplesAligned_of_layerCounts

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLayerBook.treeTwinRunData_peerExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinRunData_peerExit

end ThresholdLeanXmssSecurity.TreeTwinLayerBook
