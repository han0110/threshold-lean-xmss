import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.PhaseSplitQ
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.JointSetup
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomCut
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomCosts

/-!
# The split of a bottom run at the end of its head

`bottomHeadSplit` proves `BottomHeadSplit`. The program of each operator is the head and then the tail
(`slotProgram_bottom_cut`). Each honest head takes the rounds of the first ceremony under the common
parameter (`timed_headWith`). The first free work of each tail is the start of its PRSS setup, private
coins and setup hash calls (`advance_headWith_tail`), and these calls commute with each free call of
`jointKeyWorld` (`jointKeyWorld_setupCommute`). So `executePhase_bind_worldQ` splits the phase.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives)

/-- `BottomHeadSplit`. -/
theorem bottomHeadSplit : BottomHeadSplit K circuits settings prims := by
  intro D net st fresh operators b w parameter hpar
  have hF := headRounds_add_le circuits settings parameter b
  have hfuel : CheckTiming.firstRounds circuits settings parameter (.bottom b) +
      (treeFuel circuits settings - CheckTiming.firstRounds circuits settings parameter (.bottom b)) =
      treeFuel circuits settings := by omega
  have key := executePhase_bind_worldQ (impl := jointKeyWorld prims D false) (Q := SetupLocal) D net noFunctionality
    (fun t t' ht => jointKeyWorld_setupCommute prims D t t' ht)
    (CheckTiming.firstRounds circuits settings parameter (.bottom b))
    (treeFuel circuits settings - CheckTiming.firstRounds circuits settings parameter (.bottom b)) st
    (fun i => headWith K circuits settings D (fresh 0) i (operators i) b)
    (fun i => tailWith K circuits settings D (fresh 1) i (operators i) b)
    (fun i x => advance_headWith_tail i (operators i) _)
    (fun i hi => timed_headWith K circuits settings parameter D (fresh 0) i (operators i) b (hpar i hi))
  rw [hfuel] at key
  have hprog : (fun i => slotProgram K circuits settings D fresh i (operators i) (.bottom b)) =
      fun i => headWith K circuits settings D (fresh 0) i (operators i) b >>=
        tailWith K circuits settings D (fresh 1) i (operators i) b :=
    funext fun i => slotProgram_bottom_cut K circuits settings D fresh i (operators i) b
  rw [hprog]
  exact key w

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomHeadSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomHeadSplit
