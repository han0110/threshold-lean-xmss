import ThresholdLeanXmssSecurity.Proof.SigningCompilerShare

/-!
# The signing compiler's eager fiber table

The lazy and eager share interpreters have the same full outcome law before
bad, and the same first-bad tag and kind. Only the lucky bit is erased.
The target function is arbitrary. The laws specialize the frozen-state
coupling and implementation erasure laws of `SigningShareLazy`.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningCompilerShare.Table

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof

variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev FrozenState (C : Committee) :=
  SigningShareLazy.ShareState C.Term CPoint (SigningShareLazy.FrozenBad Bool)

def eagerHandler (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp) :=
  SigningShareLazy.unifImpl (ShareState C) +
    SigningShareLazy.eagerImpl (Tag := Bool) C.terms τ g

@[simp] theorem erase_init :
    SigningShareLazy.erase (SigningShareLazy.init : ShareState C) =
      (SigningShareLazy.init : FrozenState C) := rfl

end ThresholdLeanXmssSecurity.SigningCompilerShare.Table
