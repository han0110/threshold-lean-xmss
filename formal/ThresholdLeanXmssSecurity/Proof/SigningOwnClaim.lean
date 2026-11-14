import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SeedHit
import ThresholdLeanXmssSecurity.Proof.SigningOwnForger
import ThresholdLeanXmssSecurity.Proof.SigningOwnGateBlock
import ThresholdLeanXmssSecurity.Proof.SigningOwnVerify

/-! # The signing claim with the budget of the forger alone

- `SigningOwnBudgetStatement` is the signing claim whose budget counts the own calls of the forger to
  `H` and to the PRG and its round-2 requests (`SigningOwnForger.SigningOwnCounted`). The calls of
  the honest operators are not in the budget. The fixed slack `signingSlack` pays the security loss
  from them. It does not bound their number.
- `DistinctFlagOwn` and `HiddenCoreOwnAt` are the two stages of the claim, as `DistinctFlagBound`
  and `HiddenCoreAt` are for the claim with the budget of every party.
- `chargedSlack` and `SigningOwnVerify.capSlack` are the slacks of the two lanes of the second stage.
-/

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SigningOwnClaim

open SigningOwnForger SigningOwnGateBlock SigningOwnVerify

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The signing is strongly unforgeable with adaptive corruption (PRAWNS, Definition 3.2), in the
random-oracle model, with the budget of the forger alone. The game and the advantage are those of
`SigningSecurityStatement`.

* `q` bounds the own calls of the forger to `H` and to `PRG` and its round-2 requests, on every path
  of its program and for every answer. A rejected round-2 request counts too. The calls of the
  dealer, of the honest operators and of the verification do not count.
* `signingSlack` is a fixed part of the bound. It pays the security loss from the calls that do not
  count. It does not bound the number of those calls.
* The claim has the coordination assumption of `SigningSecurityStatement`, `breaksOneMessagePerKey`.
  Honest operators sign at most one message for each key over all quorums.
* For a fixed `q`, this budget and the budget of `SigningSecurityStatement` give different classes
  of forgers. A forger with a small count on the support of the game can have a large count on
  every path. So this claim does not replace `SigningSecurityStatement`. -/
def SigningOwnBudgetStatement (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningOwnBound A q →
    tsigAdvantage prims A ≤ signingHashError (q + signingSlack) + seedHitError C q + seedCollisionError C

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
    Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true | flaggedRun prims A] ≤
      ((Fintype.card (KeySlot C) * q : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- `HiddenCoreAt` of `Proof/SigningCore.lean` with the own budget. -/
def HiddenCoreOwnAt (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C), x ∈ support (keyGen3 (C := C)) →
    ¬KeyCollision x.2.1 x.2.2 → HasSigningOwnBound A q → q + signingSlack < 2 ^ 127 →
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true | runSigningWorld prims (flaggedAfter A x)] ≤
      ENNReal.ofReal (signingHashError (q + signingSlack))

end SigningOwnClaim

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnClaim.slack_split' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnClaim.slack_split
