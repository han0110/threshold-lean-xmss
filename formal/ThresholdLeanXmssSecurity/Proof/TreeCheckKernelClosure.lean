import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelChecked
import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCovered
import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgSigningFresh

/-! # The check-kernel coupling

`checkKernelCoupling` proves the original `CheckKernelCoupling`. It applies the composed gadget
coupling `coupled_check` at the actual checkpoint, takes the hidden-cache freshness from
`walkCheckpoint_futureEmpty_live`, rewrites the hybrid fuel with `hybrid_rounds`, and turns the
real-program coupling into the kernel coupling with `kernel_of_realRun`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeCheckKernelClosure

open TreeCheckKernelCoupling TreeCheckWalkRecipe TreeCheckWalkCoupling

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

set_option linter.constructorNameAsVariable false in
theorem checkKernelCoupling (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) : CheckKernelCoupling prims K circuits settings := by
  have H16 := TreeCheckKernelChecked.coupled_check prims K circuits settings
  have P2 := TreeCheckPrgSigningFresh.walkCheckpoint_futureEmpty_live prims K circuits settings
  have H1 := TreeCheckKernelCovered.kernel_of_realRun prims K circuits settings
  have R := hybrid_rounds prims K circuits settings
  unfold AtWalk at H16 P2 H1 R
  unfold CheckKernelCoupling AtWalk
  intro hb top tree D A x z Z q dealt bounded small j p setup c o pre live facts
  have h16 := by
    with_reducible exact (H16 hb top tree D A x z Z q dealt bounded small j p setup c o pre live facts)
  have fresh := by
    with_reducible exact (P2 hb top tree D A x z Z q dealt bounded small j p setup c o pre live)
  have rounds := by
    with_reducible exact (R hb top tree D A x z Z q dealt bounded small j p setup c o)
  dsimp only at h16
  unfold Coupled at h16
  have coupled := by
    exact (h16 o.1.1 o.2.1.1 o.2.1.2 le_rfl fresh)
  have k := by
    with_reducible exact (H1 hb top tree D A x z Z q dealt bounded small j p setup c o pre)
  intro b
  apply k
  unfold hybRun at coupled
  unfold hybridKernel
  rw [rounds]
  exact coupled

end ThresholdLeanXmssSecurity.TreeCheckKernelClosure

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelClosure.checkKernelCoupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelClosure.checkKernelCoupling
