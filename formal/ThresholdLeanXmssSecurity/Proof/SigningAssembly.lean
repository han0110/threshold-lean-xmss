import ThresholdLeanXmssSecurity.Proof.SigningGuardedFlag
import ThresholdLeanXmssSecurity.Proof.SigningFlatEager
import ThresholdLeanXmssSecurity.Proof.SigningLane2Bridge

/-!
# The rows of the signing core

This module defines the rows of the bad events of the signing core on `jointRun`.

* `jointRun` holds the result, the opening candidates, the final lazy cache and the call log.
  `jointRun_logged` and `jointRun_verify` give `loggedRun`, `verifyRun` and `exposedRun` exactly.
* `probEvent_core_eq_win` gives the win without the flag of the signing core as `Win` on `jointRun`.
* `win_cover` splits a win into a charged output event or one of the four rows `InputHitRow`,
  `LazyPartnerRow`, `TopRow` and `AbsentRow`.

`SigningLinkPaidProof.win_cover_released` and the module `SigningTopRows` use these rows.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningAssemblyProof

open HashSig LeanXmss ThresholdLeanXmss SigningUnchargedLoggedProof SigningFlatEagerProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-! ## The rows on the joint run -/

/-- The win without the flag. -/
def Win (w : JointOutcome C) : Prop :=
  w.1.1.1 = (true, false)

/-- The charged output events on the final lazy cache. -/
def Charged (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  SigningGuessProof.ChargedOutput prims x (w.1.1, w.2.1)

/-- The input-side row. A candidate carried a hidden value before its release, on the partial
chain target. -/
def InputHitRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧
    SigningOpeningProof.HiddenInputHit x (SigningGuardedFlagProof.partialChainTarget prims x (w.1, w.2.1))
      (w.1, w.2.1)

/-- The bottom partner row on the final lazy cache, before the split. -/
def LazyPartnerRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧ SigningPartnerLinkProof.BottomPartnerCase prims x (w.1.1, w.2.1)

/-- The row of the top partner that no successful bottom tree resolves. -/
def TopRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧ SigningGuessProof.TopPartner prims x (w.1.1, w.2.1) ∧
    ¬∃ key, SigningGuessProof.ResolvedTopPartner x key w.2.1.1

/-- The row of a chain start at the forged key with an absent PRF entry. -/
def AbsentRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧ SigningGuardedFlagProof.ForgedStartAbsent x (w.1, w.2.1)

/-- The three rows of the uncharged lane on the joint run. -/
def UnchargedRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  InputHitRow prims x w ∨ TopRow prims x w ∨ AbsentRow prims x w

/-! ## The cover of the win on the joint run -/

set_option maxRecDepth 100000 in
/-- A win is a charged output event or one of the four rows of the lazy cover. -/
theorem win_cover (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hwin : Win w) :
    Charged prims x w ∨ InputHitRow prims x w ∨ LazyPartnerRow prims x w ∨ TopRow prims x w ∨
      AbsentRow prims x w := by
  by_cases hc : Charged prims x w
  · exact Or.inl hc
  have ho := mem_exposedRun_of_joint prims A x w hw
  obtain ⟨top, state, forgery, hm, hbad⟩ :=
    SigningCacheProof.signing_run_badEvent_closed prims A x (w.1.1, w.2.1) ho hwin
  rcases hbad with hhit | hguess | hbottom | htop
  · exact (hc (Or.inl ⟨hwin, top, state, forgery, hm, hhit⟩)).elim
  · by_cases habsent : SigningGuardedFlagProof.ForgedStartAbsent x (w.1, w.2.1)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, hc, habsent⟩)))
    · exact Or.inr (Or.inl ⟨hwin, hc, SigningGuardedFlagProof.hiddenInputHit_partial prims x (w.1, w.2.1)
        (SigningGuessLinkProof.guess_hiddenInputHit prims A x (w.1, w.2.1)
          (mem_verifyRun_of_joint prims A x w hw) top state forgery hm hguess) habsent⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hwin, hc, top, state, forgery, hm, hbottom⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hc, ⟨top, state, forgery, hm, htop⟩,
      fun h => hc (Or.inr (Or.inr h))⟩)))

/-- The win without the flag of the signing core is the win of the joint run. -/
theorem probEvent_core_eq_win (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr{let r ← runSigningWorld prims (SigningCoreProof.flaggedAfter A x)}[r.1.2 = false ∧ r.1.1 = true] =
      Pr{let z ← jointRun prims A x}[Win z] := by
  rw [SigningDescentProof.runSigningWorld_flaggedAfter, ← SigningCostProof.loggedRun_forget,
    ← jointRun_logged, Functor.map_map, Functor.map_map, prEvent_map]
  refine prEvent_congr_of_support _ _ _ fun w _ => ?_
  simp only [Win]
  constructor
  · intro h
    exact Prod.ext h.2 h.1
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩

end SigningAssemblyProof

end ThresholdLeanXmssSecurity
