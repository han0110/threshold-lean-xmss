import ThresholdLeanXmssSecurity.Proof.TreeRawSaltSteps
import ThresholdLeanXmssSecurity.Proof.TreeRawSaltCertificates

/-!
# The raw-salt estimate for the actual ceremony

The boundary compiler preserves the actual source computation, including abort
prefixes. Its global private and charged budgets give the original opaque
normalization, finite-table representation and quantitative salt-guess bound.
-/

open LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeRawSaltFinal

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem ceremonyOpaqueNormalization :
    TreeRawSaltRepresentationProof.CeremonyOpaqueNormalization prims K circuits settings :=
  TreeRawSaltNormalizeProof.ceremonyOpaqueNormalization_of_compiler prims K circuits settings
    (TreeRawSaltStepsProof.boundaryCompilerSteps prims)
    (TreeRawSaltCertificatesProof.ceremonyCompilerCertificates prims K circuits settings)

theorem ceremonyRepresentation : TreeRawSaltCeremonyRepresentation prims K circuits settings :=
  TreeRawSaltRepresentationProof.ceremonyRepresentation_of_opaque prims K circuits settings
    (ceremonyOpaqueNormalization prims K circuits settings)

theorem treeSimHashRawSaltEstimate : TreeSimHashRawSaltEstimate prims K circuits settings :=
  treeSimHashRawSaltEstimate_of_representation prims K circuits settings
    (ceremonyRepresentation prims K circuits settings)

end ThresholdLeanXmssSecurity.TreeRawSaltFinal

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFinal.ceremonyOpaqueNormalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltFinal.ceremonyOpaqueNormalization

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFinal.ceremonyRepresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltFinal.ceremonyRepresentation

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFinal.treeSimHashRawSaltEstimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltFinal.treeSimHashRawSaltEstimate
