import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SeedHit
import ThresholdLeanXmssSecurity.Proof.SigningOwnForger
import ThresholdLeanXmssSecurity.Proof.SigningOwnGateBlock
import ThresholdLeanXmssSecurity.Proof.SigningOwnVerify

/-! # The stages of the signing claim with the budget of the forger alone

- `DistinctFlagOwn` and `HiddenCoreOwnAt` are the two stages of `SigningOwnBudgetStatement`
  (`ThresholdLeanXmss/Statement.lean`), as `DistinctFlagBound` and `HiddenCoreAt` are for the claim
  with the budget of every party.
- `chargedSlack` and `SigningOwnVerify.capSlack` are the slacks of the two lanes of the second stage.
  `slack_split` states that their sum is two times `signingSlack`.
-/

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SigningOwnClaim

open SigningOwnForger SigningOwnGateBlock SigningOwnVerify

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The slack of the charged lane in units of `2^-128`. One unit for each top key and the calls of
the verification. -/
def chargedSlack : ℕ := 2 ^ 16 + 384

theorem slack_split : chargedSlack + capSlack = 2 * signingSlack := by
  norm_num [chargedSlack, capSlack, signingSlack]

/-- For distinct keys, the own calls of the forger hit each hidden key with weight at most `q` over
all its values. It is `DistinctFlagBound` of `Proof/SeedHit.lean` with the own budget, and without
the calls of the dealer. -/
def DistinctFlagOwn (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningOwnBound A q →
    Pr{let z ← flaggedRun prims A}[¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true] ≤
      ((Fintype.card (KeySlot C) * q : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- `HiddenCoreAt` of `Proof/SigningCore.lean` with the own budget. -/
def HiddenCoreOwnAt (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C), x ∈ support (keyGen3 (C := C)) →
    ¬KeyCollision x.2.1 x.2.2 → HasSigningOwnBound A q → q + signingSlack < 2 ^ 127 →
    Pr{let r ← runSigningWorld prims (flaggedAfter A x)}[r.1.2 = false ∧ r.1.1 = true] ≤
      ENNReal.ofReal (signingHashError (q + signingSlack))

end SigningOwnClaim

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnClaim.slack_split' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnClaim.slack_split
