import ThresholdLeanXmssSecurity.Proof.SigningCache
import ThresholdLeanXmssSecurity.Proof.HiddenCore
import XmssSecurity.Proof.AdaptiveFreshTarget

/-!
# The costs of the signing core

This module holds the common terms of the cost lanes of `HiddenCoreAt` (`Proof/SigningCore.lean`,
step 5 of the signing plan in the module docstring of `ThresholdLeanXmssSecurity.lean`).

* `Outcome` and `finalOf` read an outcome of `exposedRun`.
* `HitLaneBound` says that a win with a hit costs one unit for each call. The output of a fresh call
  is a uniform truncation that equals a fixed honest output with probability `2^-128`.
  `hitLaneBoundClosed` in `SigningHitProof` proves it.
* The logged run records each call with its answer and forgets to `exposedRun` (`loggedRun_forget`).
* The budget of `gameAfter` bounds the count of `exposedRun` (`exposedRun_count_le`).
* Two units for each call give `signingHashError q` (`signingHashError_eq`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningCostProof

open SigningDescentProof SigningCacheProof

variable {C : Committee} (prims : Primitives)

/-- An outcome of `exposedRun`. -/
abbrev Outcome (C : Committee) :=
  ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × HashCache C × ℕ

/-- The final state of an outcome of `exposedRun`. -/
def finalOf (x : SigningSecurityProof.Keys3 C) (r : Outcome C) (top : TopTree) (state : TsigState C)
    (forgery : Forgery) : FinalState C :=
  ⟨x, top, state, forgery, r.2.1, false⟩

/-- A win without the flag that ends in a hit on the final cache. -/
def WinHit (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  r.1.1 = (true, false) ∧ ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := finalOf x r top state forgery
    Hit z.cache z.keys.1 z.key (z.honestKey prims)

/-! ## The lane interfaces -/

/-- The hit lane (step 5 of the plan). A win with a hit costs `2^-128` for each call. -/
def HitLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C), x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    Pr{let z ← exposedRun prims A x}[WinHit prims x z] ≤ (q : ℝ≥0∞) / 2 ^ 128

/-! ## The logged run -/

/-- The oracles of the signing world with the count and the log of each call with its answer. -/
def loggedImpl : QueryImpl (WorldSpec C) (StateT ((HashCache C × ℕ) × QueryLog (WorldSpec C)) ProbComp) :=
  fun t => StateT.mk fun p => (fun z => (z.1, (z.2, p.2.logQuery t z.1))) <$> (countImpl prims t).run p.1

/-- `exposedRun` with the log of each call. -/
def loggedRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × (HashCache C × ℕ) ×
      QueryLog (WorldSpec C)) :=
  (simulateQ (loggedImpl prims) (finalRun A x)).run (((∅ : HashCache C), 0), [])

/-- The logged run forgets its log, as `SigningCoreProof.simulateQ_run_forget`. -/
theorem loggedRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, z.2.1)) <$> loggedRun prims A x = exposedRun prims A x :=
  SigningCoreProof.simulateQ_run_forget _ _ (fun t s b => by simp [loggedImpl, Functor.map_map]) _ _ _

/-! ## The glue -/

set_option maxRecDepth 100000 in
/-- The budget of `gameAfter` bounds the count of `exposedRun`. -/
theorem exposedRun_count_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    ∀ r ∈ support (exposedRun prims A x), r.2.2 ≤ q := by
  intro r hr
  refine hq (r.1.1.1, r.2.2) ?_
  rw [← SigningCoreProof.flaggedAfter_forget, SigningCoreProof.runSigningWorld_map,
    runSigningWorld_flaggedAfter, Functor.map_map, support_map]
  exact ⟨r, hr, rfl⟩

/-- Two units for each call give `signingHashError q`. -/
theorem signingHashError_eq (q : ℕ) :
    ENNReal.ofReal (signingHashError q) = (q : ℝ≥0∞) / 2 ^ 128 + (q : ℝ≥0∞) / 2 ^ 128 := by
  unfold signingHashError
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
  have h : (q : ℝ≥0∞) / 2 ^ 128 = (q / 2 ^ 127) / 2 := by
    simp [div_eq_mul_inv, mul_assoc, ← ENNReal.mul_inv, pow_succ]
  rw [h, ENNReal.add_halves]

end SigningCostProof

end ThresholdLeanXmssSecurity
