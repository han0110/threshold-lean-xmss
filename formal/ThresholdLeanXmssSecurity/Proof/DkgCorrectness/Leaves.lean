import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndTable

/-!
# The leaves of the proof of `dkgCorrectness`

Four structures name the statements that the landing `dkgCorrectness_of_leaves` takes. Each one is
a list of hypotheses by group, with no instance. `CeremonyParts` holds the parts of the lemma of one
ceremony, `SupportParts` the part of the support lemma of one ceremony, `CutStatements` the lock step
of one ceremony that gives the covers of a run of a tree, and `UsedHitParts` the parts of the hop on
the used keys. A statement with a proof in the library is no field.
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
  /-- Wrong opened outputs of an honest operator have a wrong recorded batch. -/
  monitor : ∀ prims, CeremonyMonitor prims K circuits settings
  /-- A wrong recorded batch has a bad check, or an honest operator did not record its start. -/
  batch : ∀ prims, CeremonyBatch prims K circuits settings
  /-- An honest operator that did not record the start of a check leaves no honest output. -/
  abort : ∀ prims, CeremonyAbort prims K circuits settings
  /-- An honest operator holds one old key under a hidden name with probability at most `2^-256`. -/
  fresh : ∀ prims, FreshOne prims K circuits settings
  /-- The honest operators record the same modes, circuits, labels and tags at the checks. -/
  sync : ∀ prims, CeremonySync prims K circuits settings
  /-- The streams are fresh at the label of a joint start of a check. -/
  interval : ∀ prims, CeremonyInterval prims K circuits settings
  /-- A bad recorded check is at most as likely as a bad check of the cut ceremony. -/
  coupling : ∀ prims, CeremonyCoupling prims K circuits settings
  /-- At a joint start of a check the honest PRSS keys agree, or two echo hashes collide. -/
  keysAgree : ∀ prims, CeremonyKeysAgree prims K circuits settings
  /-- A joint start of a check with a positive count fits the budget of the game. -/
  budget : ∀ prims, CeremonyBudget prims K circuits settings runLimit
  /-- No honest operator ends a ceremony in a phase with fewer rounds than the ceremony has. -/
  short : ∀ prims, ShortFuel prims K circuits settings
  /-- The tuples of a joint start of a check have `TupleInputs` when the PRSS keys agree. -/
  tupleInputs : ∀ prims, CeremonyTupleInputs prims K circuits settings

/-- The parts of `CeremonySupport` (`ceremonySupport_of_parts`), which gives `CutState`
(`cutState_of_supports`). -/
structure SupportParts : Prop where
  /-- With no global event at the end, two honest results have the same opened outputs. -/
  outputsAgree : ∀ prims, CeremonyOutputsAgree prims K circuits settings

/-- The statement of a run of a tree that gives `TopCover` and `RestCover` (`topCover_of_started`,
`restCover_of_started`). -/
structure CutStatements : Prop where
  /-- Each honest operator records the start of each check of a ceremony that an honest operator ends. -/
  started : ∀ prims, CeremonyStarted prims K circuits settings

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
