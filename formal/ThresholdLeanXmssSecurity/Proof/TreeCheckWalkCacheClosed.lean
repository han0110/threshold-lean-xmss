import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCacheSigning

/-! # Cache certificates for every live checkpoint of the fixed walk -/

open LeanXmss ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity.TreeCheckWalkCacheClosed

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- First-run and signing checkpoints have the original cache certificate. -/
theorem walkCheckpointCache (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    TreeCheckWalkTransport.WalkCheckpointCache prims K circuits settings := by
  exact TreeCheckWalkCache.walkCheckpointCache_of_signing prims K circuits settings
    (TreeCheckWalkCacheSigning.walkCheckpointCacheSigning prims K circuits settings)

end ThresholdLeanXmssSecurity.TreeCheckWalkCacheClosed

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCacheClosed.walkCheckpointCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCacheClosed.walkCheckpointCache
