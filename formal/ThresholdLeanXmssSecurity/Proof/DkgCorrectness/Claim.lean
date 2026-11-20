import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RunsUnion

/-!
# The field `dkgCorrectness` from the leaves of the route

`dkgCorrectness_of_leaves` gives the field `dkgCorrectness` of `Theorems`,
`CircuitsCompute circuits prims.Th → DkgCorrectness prims K circuits settings runLimit`. Its premises
are the readiness hop, the four collision hops and the hop on the used keys of the game, and the
statements of the route on one run of a tree. `flagFirstHop`, `seedsHop` and `runsUnionHop` give the
three other hops of the game. The error of `UsedHitHop` is `setupHybridError`, and with it
`part1Error` is `dkgCorrectnessError`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [DecidableEq E] in
/-- The field `dkgCorrectness` from the open hops of the game and the statements of the route. -/
theorem dkgCorrectness_of_leaves
    (ready : ∀ prims, ReadyHopL prims K circuits settings runLimit)
    (echo : ∀ prims, CollisionHopW prims K circuits settings runLimit EchoDomain (echoError runLimit C))
    (usedHitHop : ∀ prims, UsedHitHop prims K circuits settings runLimit (setupHybridError runLimit C))
    (reuse : ∀ prims, CollisionHopW prims K circuits settings runLimit DeriveDomain (reuseError runLimit C))
    (copy : ∀ prims, CollisionHopW prims K circuits settings runLimit CopyDomain (copyError settings runLimit C))
    (split : ∀ prims, CollisionHopW prims K circuits settings runLimit SplitHashDomain (splitError settings runLimit C))
    (bad : ∀ prims, CeremonyBad prims K circuits settings runLimit)
    (top : ∀ prims, TopCover prims K circuits settings)
    (fuel : HeadFuel circuits settings)
    (head : ∀ prims, HeadCover prims K circuits settings)
    (cut : ∀ prims, CutState prims K circuits settings)
    (dead : ∀ prims, CutDead prims K circuits settings)
    (mono : ∀ prims, CutMonotone prims K circuits settings)
    (rest : ∀ prims, RestCover prims K circuits settings) :
    CircuitsCompute circuits prims.Th → ThresholdLeanXmss.DkgCorrectness prims K circuits settings runLimit := by
  intro compute batch runs D A q bounded
  exact part1L_of_route K circuits settings runLimit (setupHybridError runLimit C)
    (fun prims => flagFirstHop prims K circuits settings runLimit)
    (fun prims => seedsHop prims K circuits settings runLimit)
    (fun prims => RunsUnion.runsUnionHop prims K circuits settings runLimit)
    ready echo usedHitHop reuse copy split bad top fuel head cut dead mono rest batch runs prims compute D A q bounded

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.dkgCorrectness_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.dkgCorrectness_of_leaves
