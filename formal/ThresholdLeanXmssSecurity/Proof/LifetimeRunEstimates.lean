import ThresholdLeanXmssSecurity.Proof.LifetimeTailBudget
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# Collision and hit estimates at a selected lifetime run

The actual boundary is covered by failed key separation, a cached setup hit,
and the lazy tail flag. The tail uses the original lifetime query allowance.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeRunEstimates

open LifetimeRunBoundary LifetimeSetupBridge LifetimeTailDriver LifetimeTailBridge
open LifetimeTailBudget LifetimeTailFlagBound LifetimePrfTransportProof LifetimeHybridOrder

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The sum of the separation, cached-hit and exact-Q tail estimates. -/
def runCost (C : Committee) (Q : ℕ) : ℕ :=
  (Q + C.n ^ 2) * prssKeyCount C + (C.n ^ 2 * termCount C ^ 2 + C.n ^ 4) + revealPairs C +
    2 * (Q + C.n ^ 2) * prssKeyCount C + (3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E) (prims : Primitives)

/-- S3 at the actual lifetime boundary, with the unchanged exact-Q numerator. -/
theorem tail_flag_le_of_hybrid (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q) :
    Pr[fun y => KeysApart D (rowsAt y.1.1) ∧ y.2.2.2 = true |
      LifetimeTailFlag.lazyRunBoundary K circuits settings attempts D n A prims] ≤
      ((3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (lazyRunBoundary_le K circuits settings attempts D n prims A (fun _ => default) []).trans ?_
  exact flagBoundG prims K circuits settings D (boundaryAdv K circuits settings attempts D n A)
    (lifeDriver K circuits settings attempts D n seedOf) (fun _ => default) []
    (lifeDriver_lawful K circuits settings attempts D n seedOf) Q
    (driver_bound_of_hybrid K circuits settings attempts D n A Q hQ _ _)

/-- The collision and hit estimates cover the actual joint boundary bad event. -/
theorem boundary_bad_le_of_hybrid (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q) :
    Pr[fun y => y.2.2.bad = true | runBoundary K circuits settings attempts D n A prims] ≤
      (runCost C Q : ℝ≥0∞) / 2 ^ 256 := by
  have h := (LifetimeTailFlag.bad_le_setup_add_flag K circuits settings attempts D n A prims).trans
    (add_le_add (add_le_add
      (setup_keysApart_le_of_hybrid K circuits settings attempts D n A prims Q hQ)
      (setup_keyHit_le_of_hybrid K circuits settings attempts D n A prims Q hQ))
      (tail_flag_le_of_hybrid K circuits settings attempts D n A prims Q hQ))
  convert h using 1 <;> try rfl
  simp only [runCost, Fintype.card_prod, Committee.Party, Fintype.card_fin,
    keygenFinish_card_term, prssKeyCount, termCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ← ENNReal.add_div]
  congr 1
  ring

/-- The original real-world lifetime budget implies the exact selected tail bound. -/
theorem tail_flag_le (circuitsOf : (HashInput → HashOutput) → Circuits) (aes : Aes) (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (values : MpcDomain → HashOutput) :
    Pr[fun y => KeysApart D (rowsAt y.1.1) ∧ y.2.2.2 = true |
      LifetimeTailFlag.lazyRunBoundary K (circuitsOf (thOf values)) settings attempts D n A
        ⟨thOf values, aes⟩] ≤
      ((3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  tail_flag_le_of_hybrid K (circuitsOf (thOf values)) settings attempts D n A ⟨thOf values, aes⟩ Q
    (LifetimeRealBad.hybridBudget_of_real K (circuitsOf (thOf values)) settings attempts D A Q n (hQ values))

/-- The original source premise covers the complete selected boundary. -/
theorem boundary_bad_le (circuitsOf : (HashInput → HashOutput) → Circuits) (aes : Aes) (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (values : MpcDomain → HashOutput) :
    Pr[fun y => y.2.2.bad = true |
      runBoundary K (circuitsOf (thOf values)) settings attempts D n A ⟨thOf values, aes⟩] ≤
      (runCost C Q : ℝ≥0∞) / 2 ^ 256 :=
  boundary_bad_le_of_hybrid K (circuitsOf (thOf values)) settings attempts D n A ⟨thOf values, aes⟩ Q
    (LifetimeRealBad.hybridBudget_of_real K (circuitsOf (thOf values)) settings attempts D A Q n (hQ values))

/-- The same bound for the original reduction's stream-key bad event. -/
theorem reduction_bad_le (circuitsOf : (HashInput → HashOutput) → Circuits) (aes : Aes) (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (values : MpcDomain → HashOutput) :
    probBad_streamKey ⟨thOf values, aes⟩ D (reductionGame K settings attempts circuitsOf D A values n) ≤
      (runCost C Q : ℝ) / 2 ^ 256 := by
  rw [probBad_reductionGame_eq]
  have h := ENNReal.toReal_mono (by finiteness)
    (boundary_bad_le K settings attempts D n A circuitsOf aes Q hQ values)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using h

end ThresholdLeanXmssSecurity.LifetimeRunEstimates

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunEstimates.tail_flag_le_of_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRunEstimates.tail_flag_le_of_hybrid

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunEstimates.boundary_bad_le_of_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRunEstimates.boundary_bad_le_of_hybrid

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunEstimates.tail_flag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRunEstimates.tail_flag_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunEstimates.boundary_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRunEstimates.boundary_bad_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunEstimates.reduction_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRunEstimates.reduction_bad_le
