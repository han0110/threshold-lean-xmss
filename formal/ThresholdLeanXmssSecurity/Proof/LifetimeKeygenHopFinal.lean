import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenPrograms
import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenCapQuiet
import ThresholdLeanXmssSecurity.Proof.LifetimeEmulatedBudget

/-!
# The lifetime keygen hop

The all-answer lifetime budget supplies keygen cap quietness and the real
continuation bound. Together with chronological role equality and the
program-free tail, these give the original keygen hop with one D18 error
`keygenHashError C ((setupRounds + 2) * Q)`.

The pinned and current leanVM sources have no threshold lifetime keygen hop.
This assembly uses the local component and lifetime interfaces.
-/

open LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeKeygenHopFinal

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The original lifetime budget pays for the single keygen hop. -/
theorem lifetimeKeygenHop_of_hasLifetimeQueryBound (Q : ℕ)
    (hQ : HasLifetimeQueryBound K settings attempts circuitsOf D A Q) :
    LifetimeHybridOrder.LifetimeKeygenHop K settings attempts aes circuitsOf D A Q := by
  have hcap := LifetimeKeygenCapQuiet.keygenCapQuiet K settings attempts D A Q aes circuitsOf hQ
  apply LifetimeKeygenHopProof.lifetimeKeygenHop_of_programs
    K settings attempts aes circuitsOf D A Q
  · intro values
    exact LifetimeKeygenPrograms.chronologicalRoles
      K settings attempts (circuitsOf (thOf values)) D A
  · intro values
    exact LifetimeKeygenPrograms.tailProgramFree
      K settings attempts (circuitsOf (thOf values)) D A
  · exact hcap
  · intro values
    exact LifetimeKeygenHopProof.realTailBound_of_sourceBound
      K settings attempts D A ⟨thOf values, aes⟩ (circuitsOf (thOf values)) Q
      (hcap values)
      (LifetimeEmulatedBudget.sourceBound_of_hasLifetimeQueryBound
        K settings attempts circuitsOf D A Q hQ values)

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopFinal.lifetimeKeygenHop_of_hasLifetimeQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeKeygenHop_of_hasLifetimeQueryBound

end ThresholdLeanXmssSecurity.LifetimeKeygenHopFinal
