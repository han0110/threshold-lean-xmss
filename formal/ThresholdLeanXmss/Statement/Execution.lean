import ThresholdLeanXmss.Statement.RandomOracle
import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# The execution on the network

Read this file second. `realExecution` runs a protocol on the network with an adversary that plays a
static coalition, as in GS20, Section 3.1. The games of the setup run the seed generation with it.
`noCoalition` and `honestAdversary` give the honest run.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The real execution of a protocol in the hybrid model of `Fh`, on the inputs `x` and the auxiliary
input `z`. -/
def realExecution {I O Ih Oh Lh Rh : Type} (D : C.Coalition) (A : Adversary C E I Lh Rh)
    (Fh : Functionality C Ih Oh Lh Rh) (fuel : ℕ) (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (x : C.Party → I) (z : Aux) : OracleComp (WorldSpec C) (A.State × (C.Party → Option O)) := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  executePhase worldRoles D A Fh fuel state fun i => program i (x i)

def noCoalition : C.Coalition := ⟨∅, by simp⟩

/-- The adversary of an honest run. It controls no operator and replies `reply` to each leak. -/
def honestAdversary {I L R : Type} (reply : L → R) : Adversary C E I L R :=
  ⟨Unit, fun _ _ => pure (), fun _ _ => pure ((), fun _ _ => none), fun _ l => pure ((), reply l)⟩

end ThresholdLeanXmss
