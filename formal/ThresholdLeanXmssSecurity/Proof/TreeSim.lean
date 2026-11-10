import ThresholdLeanXmssSecurity.Proof.TreeSecurity
import ThresholdLeanXmssSecurity.Proof.Coupling
import ThresholdLeanXmssSecurity.Proof.CheckSplit

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

-- The simulation stages below will replace this initial explicit obligation.
theorem treeSimulationHop
    (simulation : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSimulationHop prims K circuits settings (keySplit C) := simulation

end ThresholdLeanXmssSecurity
