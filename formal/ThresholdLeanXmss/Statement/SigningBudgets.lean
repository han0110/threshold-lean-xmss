import ThresholdLeanXmss.Statement.Signing

/-!
# The budgets of the signing proofs

The forms of the signing claim that the proofs use. No field of `Theorems` is in this file, and
`Theorems.lean` does not import it.

* `SigningOwnBudgetStatement` is `ThresholdLeanXmssStronglyUnforgeable` with the count as a predicate
  (`IsQueryBoundP` of VCVio). `SigningOwnBudget.signingOwnBudget` proves it, and
  `SigningStronglyUnforgeable.stronglyUnforgeable_iff` proves that the two are equivalent.
* `SigningSecurityStatement` is the same game with the budget of every party, as leanXMSS has it at
  the revision `1acdff19` of leanVM. `signingSecurityClosed`
  (`Proof/SigningCompilerO1Coupling.lean`) proves it, with a proof of its own.
* For a fixed `q`, the two budgets give different classes of forgers. A forger with a small count on
  the support of the game can have a large count on every path. So neither claim replaces the other.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The bound `q / 2^127` for `q` calls. Each call costs two units of `2^-128`. One unit
pays a call whose output hits an honest output at its tweak. The other pays a call that meets a
hidden honest input, namely a chain value below an opened position or `ρ_e` before round 1, or the
output of a digest that a later search selects. -/
def signingHashError (q : ℕ) : ℝ := q / 2 ^ 127

/-! ## The budget of every party -/

/-- Every execution makes at most `q` calls of `H` and `PRG`, by every party, cache hits included.
The key generation, the signers, the forger and the verification all
count. The signing oracles build each bottom tree once, at the first request that needs it, and
that build counts. When at least `t` operators can sign the forged message, the win test builds its
tree again, and that build counts too. -/
def HasSigningQueryBound {α : Type} (oa : OracleComp (WorldSpec C) α) (q : ℕ) : Prop :=
  ∀ r ∈ support (runSigningWorld prims oa), r.2 ≤ q

/-- The signing is strongly unforgeable with adaptive corruption (PRAWNS, Definition 3.2), in the
random-oracle model, with the budget of every party. `q` bounds the calls of `H` and `PRG` by every
party in the signing world, and the bound has no slack. The game, the terms of the hidden keys and
the coordination assumption are those of `StronglyUnforgeable`. -/
def SigningSecurityStatement (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q →
    tsigAdvantage prims A ≤ signingHashError q + seedHitError C q + seedCollisionError C

/-! ## The budget of the forger alone -/

/-- The queries that `adversaryCost` counts, as a predicate. -/
def SigningOwnCounted : (LocalSpec C + TsigSpec C).Domain → Prop
  | .inl (.inr _) => True
  | .inr (.round2 ..) => True
  | _ => False

/-- The forger makes at most `q` own calls of `H` and `PRG` and round-2 requests together, on every
path of its program and for every answer. A rejected round-2 request counts too. -/
def HasSigningOwnBound (A : TsigAdversary C) (q : ℕ) : Prop :=
  ∀ pk top, IsQueryBoundP (A pk top) SigningOwnCounted q

/-- The slack of `SigningOwnBudgetStatement`, in calls. It is equal to `securitySlack`. -/
def signingSlack : ℕ := 2 ^ 15 + 384

/-- `ThresholdLeanXmssStronglyUnforgeable` with the budget `HasSigningOwnBound` and the bound
`signingHashError (q + signingSlack)`. -/
def SigningOwnBudgetStatement (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningOwnBound A q →
    tsigAdvantage prims A ≤ signingHashError (q + signingSlack) + seedHitError C q + seedCollisionError C

end ThresholdLeanXmss
