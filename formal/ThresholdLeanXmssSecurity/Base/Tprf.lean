import ThresholdLeanXmssSecurity.Base.Dkg

/-!
# The threshold PRF

The game of the threshold PRF of PRAWNS and its two claims, correctness and adaptive security.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The game `G^tprf` of PRAWNS, Figure 1, with `KeyGen'` of PRAWNS, Section 5.1. -/
def tprfGame (A : TprfAdversary C) (b : Bool) : OracleComp (WorldSpec C) Bool := do
  let (_, seeds, keys) ← free (liftComp (prawnsKeyGen (C := C)) _)
  let forward : QueryImpl (LocalSpec C) (StateT (TprfState C) (OracleComp (WorldSpec C))) :=
    fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  (simulateQ (forward + tprfOracles keys seeds b) A : StateT (TprfState C) (OracleComp (WorldSpec C)) Bool).run'
    ⟨∅, fun _ _ => ∅, ∅, fun _ => none⟩

/-- `Adv^tprf`, PRAWNS, Definition 2.2. -/
def tprfAdvantage (A : TprfAdversary C) : ℝ :=
  |accepts prims (tprfGame A false) - accepts prims (tprfGame A true)|

/-- The error of Theorem 5.1 with `F(k, x) = H16(k ‖ x)` in the random-oracle model, for `q`
counted calls. PRAWNS bounds it by `2 C(n, t - 1) ε_F`, which gives `2 C(n, t - 1) q / 2^256`. The
masks add `n² q / 2^256` for the guess of a hidden pair key. Honest calls are free, so two of the
`C(n, t - 1) + n²` keys may also collide. -/
def tprfError (C : Committee) (q : ℕ) : ℝ :=
  ((2 * C.n.choose (C.t - 1) + C.n ^ 2) * q + (C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 : ℕ) / 2 ^ 256

/-- `Combine'` of the parts of every quorum gives `F(msk, x)` (PRAWNS, Definition 2.1). -/
def TprfCorrectnessStatement (C : Committee) : Prop :=
  ∀ (J : C.Quorum) (x : Point) (ec : Message), ∀ r ∈ support (runWorld prims (tprfCorrectnessRun J x ec)), r.1 = true

/-- The threshold PRF is adaptively secure (PRAWNS, Definition 2.2 and Theorem 5.1). -/
def TprfSecurityStatement (C : Committee) : Prop :=
  ∀ (A : TprfAdversary C) (q : ℕ),
    IsQueryBoundP A (fun t => Sum.elim Counted (fun _ => False) t) q →
    tprfAdvantage prims A ≤ tprfError C q

end ThresholdLeanXmss
