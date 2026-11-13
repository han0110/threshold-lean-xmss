import ThresholdLeanXmssSecurity.Proof.TreeTwinLayerBook
import ThresholdLeanXmssSecurity.Proof.TreeTwinHiddenLayer

/-! # Layer bookkeeping for hidden-term saved data

Saved tuple counts transfer between the two runs. Peer exits preserve
hidden-term wire and x/y shifts with the original single-pivot product shift.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinHiddenLayerBook
open TreeTwinHiddenData TreeTwinLayerBook
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

-- Port of TreeTwinLayerBook.nonzero_of_count (118), with hidden-term saved data.
theorem nonzero_of_count (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (circs : List Circuit) (p₁ p₂ : C.Party → MainInput C × List (Tuple C))
    (count : ∀ i, i ∉ D.1 → ((p₁ i).2.map (·.count)).sum +
      (outputsOf circs).length = tupleCount circs)
    (data : HiddenRunData K D ctx₁ ctx₂ p₁ p₂) (nonzero : tupleCount circs ≠ 0) :
    (∀ i, i ∉ D.1 → ((p₁ i).2.map (·.count)).sum + (outputsOf circs).length ≠ 0) ∧
    (∀ i, i ∉ D.1 → ((p₂ i).2.map (·.count)).sum + (outputsOf circs).length ≠ 0) := by
  constructor
  · intro i hi
    rw [count i hi]
    exact nonzero
  · intro i hi
    rw [(TreeTwinHiddenLayer.counts_modes K D ctx₁ ctx₂ p₁ p₂ data i hi).1, count i hi]
    exact nonzero

-- Port of TreeTwinLayerBook.treeTwinRunData_peerExit (190), with the same exits and witnesses.
theorem treeTwinRunData_peerExit (D : C.Coalition) (d : TreeSimPeerData K D)
    (circs : List Circuit) (layer : ℕ) (p₁ p₂ : C.Party → MainInput C × List (Tuple C))
    (data : HiddenRunData K D d.ctx₁ d.ctx₂ p₁ p₂)
    (count : d.count = (gatesAt circs layer).length)
    (v₁ : ∀ i, i ∉ D.1 → d.v₁ i =
      mulRep K (d.ctx₁ i) (layerX K circs layer (p₁ i).1) (layerY K circs layer (p₁ i).1))
    (v₂ : ∀ i, i ∉ D.1 → d.v₂ i =
      mulRep K (d.ctx₂ i) (layerX K circs layer (p₂ i).1) (layerY K circs layer (p₂ i).1))
    (mode₁ mode₂ : C.Party → ReshareMode) (modes : ∀ i, i ∉ D.1 → mode₂ i = mode₁ i)
    (aligned : SharesAligned D p₁) (x₁ x₂ : C.Party → Shares C Bit × RunState C)
    (exits : ∀ i, i ∉ D.1 → TreeSimPeerExitRel K D d i (x₁ i) (x₂ i)) :
    HiddenRunData K D d.ctx₁ d.ctx₂
      (fun i => treeTwinLayerShares K circs layer (mode₁ i) (p₁ i) (x₁ i).1)
      (fun i => treeTwinLayerShares K circs layer (mode₂ i) (p₂ i) (x₂ i).1) := by
  refine TreeTwinHiddenLayer.runData_layer K D d.ctx₁ d.ctx₂ circs layer _ _ p₁ p₂ _ _ data
    aligned.1 aligned.2 modes fun i hi => ?_
  rw [(exits i hi).1, count]
  congr 1
  funext g
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Pi.sub_apply, Pi.sub_apply, v₁ j (Finset.mem_filter.1 hj).2, v₂ j (Finset.mem_filter.1 hj).2]

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenLayerBook.nonzero_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonzero_of_count

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenLayerBook.treeTwinRunData_peerExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinRunData_peerExit

end ThresholdLeanXmssSecurity.TreeTwinHiddenLayerBook
