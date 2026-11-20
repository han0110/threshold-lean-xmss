import Sketch.DealerAbort
import Sketch.SeedGenHop
import Sketch.BottomRuns

/-!
# `DkgCompleteness` from one premise

The honest run of the real setup gives an output to each operator, except with probability
`dkgAbortError`, and its outputs are at distance at most `dkgCompletenessError` from the outputs of
the dealer. The proof joins the four hops of `Completeness.lean`. It has one premise,
`RealTreeAbortOrCorrect`, which says that each operator of an honest tree run ends with no output or
with the output of the ceremony.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- `DkgCompleteness` from `RealTreeAbortOrCorrect`. -/
theorem dkgCompleteness_of_abortOrCorrect
    (correct : ∀ prims, RealTreeAbortOrCorrect K circuits settings prims)
    (batch : 0 < settings.batchSize) (runs : 0 < runLimit)
    (prims : Primitives) (compute : CircuitsCompute circuits prims.Th) (b : Fin (2 ^ layerHeight)) :
    (Pr{let r ← runWorld prims (honestDkg K circuits settings runLimit b)}[∃ i,
        (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none]).toReal ≤
        dkgAbortError (E := E) circuits settings C b ∧
      letI : MeasurableSpace (SetupOutputs C) := ⊤
      measureTVDist (Prod.fst <$> runWorld prims (honestDkg K circuits settings runLimit b))
          (Prod.fst <$> runWorld prims (dealerDkg b)) ≤
        dkgCompletenessError (E := E) circuits settings C b :=
  dkgCompleteness_of_hops K circuits settings runLimit (topRunsHop K circuits settings runLimit)
    (bottomRunsHop_of_abortOrCorrect K circuits settings runLimit correct) seedGenHop dealerAbort
    batch runs prims compute b

/-- info: 'ThresholdLeanXmss.Sketch.dkgCompleteness_of_abortOrCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dkgCompleteness_of_abortOrCorrect

end ThresholdLeanXmss.Sketch
