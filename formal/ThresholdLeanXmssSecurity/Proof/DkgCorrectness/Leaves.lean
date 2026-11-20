import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndTable

/-!
# The leaves of the proof of `dkgCorrectness`

Two structures name the statements that the landing `dkgCorrectness_of_leaves` takes. Each one
is a list of hypotheses by group, with no instance. `CeremonyParts` holds the parts of the lemma of
one ceremony, and `UsedHitParts` the parts of the hop on the used keys. A statement with a proof in the library is no field.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The parts of `CeremonyBad` (`ceremonyBad_of_parts`) and of `ProvenanceTreeRun`
(`provenanceTreeRun_of_parts`). -/
structure CeremonyParts : Prop where
  /-- A joint start of a check with a positive count fits the budget of the game. -/
  budget : ∀ prims, CeremonyBudget prims K circuits settings runLimit
  /-- The tuples of a joint start of a check have `TupleInputs` when the PRSS keys agree. -/
  tupleInputs : ∀ prims, CeremonyTupleInputs prims K circuits settings

/-- The parts of `UsedHitHop` at the error `setupHybridError` (`UsedHit.usedHitHop_of_reductions`). -/
structure UsedHitParts : Prop where
  /-- Each part of the reduction of a top slot has its cost in the class `prssSetup`. -/
  topCost : ∀ prims, UsedHit.TopSlotPartCosts K circuits settings runLimit prims
  /-- The reduction of a top slot with the real challenger has the law of hybrid `j`. -/
  topReal : ∀ prims, UsedHit.TopLawReal K circuits settings runLimit prims
  /-- The reduction of a top slot with fresh hidden keys has the law of hybrid `j + 1`. -/
  topFresh : ∀ prims, UsedHit.TopLawFresh K circuits settings runLimit prims
  /-- Each part of the reduction of a bottom slot has its cost in the class `prssSetup`. -/
  bottomCost : ∀ prims, UsedHit.BottomSlotPartCosts K circuits settings runLimit prims
  /-- The reduction of a bottom slot with the real challenger has the law of its hybrid. -/
  bottomReal : ∀ prims, UsedHit.BottomLawReal K circuits settings runLimit prims
  /-- The reduction of a bottom slot with fresh hidden keys has the law of the next hybrid. -/
  bottomFresh : ∀ prims, UsedHit.BottomLawFresh K circuits settings runLimit prims
  /-- The end points of the fixed and of the old numbering have one probability. -/
  endPoints : ∀ prims, UsedHit.EndPointsAgree K circuits settings runLimit prims
  /-- The hybrid with fresh keys in each slot has the law of the game with a uniform table. -/
  eager : ∀ prims, UsedHit.EagerDraw K circuits settings runLimit prims
  /-- Each key of the private table at the end of the game with a table is an entry of the table. -/
  keyProvenance : ∀ prims, UsedHit.KeyProvenance K circuits settings runLimit prims
  /-- The game with a renamed table is the game with the hidden keys of the honest calls renamed. -/
  keyParametric : UsedHit.KeyParametric K circuits settings runLimit
  /-- The public cache has at most `q` stream cells of the adversary and one for each honest known key. -/
  cellsCount : ∀ prims, UsedHit.CellsCount K circuits settings runLimit prims

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end
