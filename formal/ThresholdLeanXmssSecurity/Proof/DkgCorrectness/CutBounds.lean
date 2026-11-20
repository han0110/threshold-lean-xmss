import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Route
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Setup

/-!
# Two small facts of the cut of a bottom tree

* `cutMonotone` proves `CutMonotone`. The rest of a bottom tree is a run in `streamWorld`, so the
  hash cache only grows, and each collision of `GlobalEvent` stays.
* `headFuel` proves `HeadFuel`. The first ceremony of a bottom tree is a part of the two ceremonies
  that `bottomRounds_le` bounds by `treeFuel`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A global event stays in a larger hash cache. -/
theorem globalEvent_mono {w w' : StreamState C} (hle : w.1 ≤ w'.1) (h : GlobalEvent w) :
    GlobalEvent w' := by
  rcases h with h | h | h | h
  · exact Or.inl (SetupAgree.domainCollision_mono hle h)
  · exact Or.inr (Or.inl (SetupAgree.domainCollision_mono hle h))
  · exact Or.inr (Or.inr (Or.inl (SetupAgree.domainCollision_mono hle h)))
  · exact Or.inr (Or.inr (Or.inr (SetupAgree.domainCollision_mono hle h)))

omit [Fintype E] [DecidableEq E] in
/-- A global event at the cut stays to the end of the run. -/
theorem cutMonotone (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) :
    CutMonotone prims K circuits settings := by
  intro D net b s st heads m w hw y hy
  exact globalEvent_mono (streamWorld_run_mono prims D _ w y hy) hw

/-- The head of a bottom tree has the rounds of its first ceremony within the fuel of a run. -/
theorem headFuel (circuits : Circuits) (settings : Settings) : HeadFuel circuits settings := by
  intro parameter b
  have h := bottomRounds_le circuits settings parameter b (fun _ => digit 0)
  rw [CheckTiming.firstRounds, CheckTiming.firstJobs,
    ← CheckTiming.batchesRounds_eq circuits settings parameter (bottomJobs b)]
  unfold Fuel.batchesRounds treeFuel
  omega

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutMonotone

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.headFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.headFuel
