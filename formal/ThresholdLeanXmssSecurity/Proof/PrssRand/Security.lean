import ThresholdLeanXmssSecurity.Proof.PrssRand.Bound
import ThresholdLeanXmssSecurity.Proof.PrssRand.Streams
import ThresholdLeanXmssSecurity.Proof.PrssRand.KeyHop

/-!
# The PRSS streams from dealt keys, the proof

`prssRandSecurity` proves `PrssRandStatement` from three lemmas, with the simulator `prssRandSim`.

1. `prssRand_queryBound` counts the calls of the ideal run.
2. `prssRand_keyHop` bounds the stream-key event of `keyWorld_coupling` on the real run.
3. `prssRand_streamHop` states that the real run with random hidden streams is the ideal run.

`abs_sub_le_of_hops` joins the two hops at the PRF reduction `prgReduction`. The PRF step follows
the PRSS of CDI05, Section 4.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-- The streams of dealt PRSS keys securely compute the calls of the adapted `Frand`, with selective
abort, in the `F_prssKeys`-hybrid model. -/
theorem prssRandSecurity [SampleableType E] (prims : Primitives) (K : Constants C E) :
    PrssRandStatement prims K := by
  intro label calls D A
  refine ⟨prssRandSim K label calls D A, fun x z Z q hq =>
    ⟨prssRand_queryBound K label calls D A x z Z prims q hq, ?_⟩⟩
  have h := abs_sub_le_of_hops prims D (prssRandReal K label calls D A x z Z)
    (prssRandIdeal K label calls D A x z Z) (prssRandHashError C q) 0
    (by
      unfold reductionReal
      rw [prfRealExp_prgReduction]
      exact (keyWorld_coupling prims D _).trans (prssRand_keyHop K label calls D A x z Z prims q hq))
    (by
      unfold reductionIdeal
      rw [prfIdealExp_prgReduction, prssRand_streamHop]
      simp)
  simpa [prssRandReal, prssRandIdeal] using h

end ThresholdLeanXmssSecurity
