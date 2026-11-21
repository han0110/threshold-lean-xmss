import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Events

/-!
# The statement of the part of the first hit under an emulated seed

`HitPart event bound` bounds the event `event` in the game with the keys of the dealer and no emulated
run. `HitSeed` is the part of a counted call that asks a PRF cell under an emulated seed of a hidden
term, with the bound `hitSeedError`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-- A counted call asks a PRF cell under the seed that an emulated operator holds for a term with no
corrupt holder. -/
def HitSeedOf (D : C.Coalition) (r : DealtOut C × LogState C) : Prop :=
  ∃ q ∈ r.2.2, ∃ (i : C.Party) (keys : Keys C) (T : C.Term) (x : Point), i ∉ D.1 ∧ r.1.2.2.2.2 i = some keys ∧
    i ∈ C.holders T ∧ ¬ KnownTo D.1 T ∧ q = .prf (keys.seed T) x

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The bound `bound q` of the event `event` in the game with the keys of the dealer and no emulated
run. -/
def HitPart (event : C.Coalition → DealtOut C × LogState C → Prop) (bound : ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    dealtProb prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (event D) ≤ bound q

/-- The bound of a counted call under an emulated seed of a hidden term. -/
def hitSeedError (C : Committee) (q : ℕ) : ℝ := ((2 * q * (C.n * termCount C) : ℕ) : ℝ) / 2 ^ 256

/-- The part of a counted call under an emulated seed of a hidden term. -/
def HitSeed : Prop := HitPart prims K circuits settings runLimit HitSeedOf (hitSeedError C)

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
