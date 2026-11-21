import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomPause
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomSplit
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.SeedAgree

/-!
# The laws of a bottom slot

`bottomLawReal` and `bottomLawFresh` prove `BottomLawReal` and `BottomLawFresh` with the head split
`bottomHeadSplit` and the parameter of the seed generation in `jointKeyWorld`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

variable {C : Committee} {E : Type} [Field E] [Fintype E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (prims : Primitives)

omit [Field E] [Fintype E] [Algebra Bit E] in
/-- Two honest operators that end the seed generation in `jointKeyWorld` with an output hold the same
parameter. -/
theorem seedParameterAgreeJoint (D : C.Coalition) : SeedParameterAgreeJoint (E := E) prims D :=
  fun net st w y hy i j Ki Kj hi hj hKi hKj =>
    seedParameterAgree_any (jointKeyWorld prims D false) D net st w y hy i j Ki Kj hi hj hKi hKj

theorem bottomLawReal : BottomLawReal K circuits settings runLimit prims :=
  bottomLawReal_of_split K circuits settings runLimit prims (bottomHeadSplit K circuits settings prims)
    (seedParameterAgreeJoint prims)

theorem bottomLawFresh : BottomLawFresh K circuits settings runLimit prims :=
  bottomLawFresh_of_split K circuits settings runLimit prims (bottomHeadSplit K circuits settings prims)
    (seedParameterAgreeJoint prims)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawReal

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawFresh
