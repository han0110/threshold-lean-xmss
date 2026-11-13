import ThresholdLeanXmssSecurity.Proof.SigningCache
import ThresholdLeanXmssSecurity.Proof.HiddenCore
import XmssSecurity.Proof.AdaptiveFreshTarget

/-!
# The costs of the signing core

`HiddenCoreAt` of `Proof/SigningCore.lean` (steps 5 and 6 of the signing plan in
the module docstring of `ThresholdLeanXmssSecurity.lean`) and the full signing claim
`signingSecurityComplete`.

The component lemmas:

* A win without the flag ends in a bad event on the final cache of `exposedRun` (`win_le_bad`, from
  `signing_run_badEvent_closed`).
* The budget of `gameAfter` bounds the count of `exposedRun` (`exposedRun_count_le`).
* Two units for each call give `signingHashError q` (`signingHashError_eq`).
* A fresh call of `H` truncates to a fixed digest with probability `2^-128`, on both copies
  (`free_fresh_truncate_le`, `counted_fresh_truncate_le`).
* The logged run records each call with its answer and forgets to `exposedRun` (`loggedRun_forget`).

The hypotheses of `hiddenCoreAt`:

* `HitLaneBound`: a win with a hit costs one unit for each call. The output of a fresh call is a
  uniform truncation that equals a fixed honest output with probability `2^-128`.
* `GuessPartnerLaneBound`: a win with a guess or a partner costs one unit for each call. A guess
  queries a hidden chain value at a chain call, and a partner meets the selected codeword output at
  a digest call. The two call types are disjoint.

The calls of `KeyGen` count in `q` and are never bad, so they pay the lower-order terms of leanVM
(`firstLaneSlack`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

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

/-- A win without the flag that ends in a guess or a partner on the final cache. -/
def WinGuessPartner (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  r.1.1 = (true, false) ∧ ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := finalOf x r top state forgery
    Guess z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
        (XmssSecurity.Bridge.toModelSig z.forgery.signature) ∨
      Partner z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
        (XmssSecurity.Bridge.toModelSig z.forgery.signature)

/-! ## The lane interfaces -/

/-- The hit lane (step 5 of the plan). A win with a hit costs `2^-128` for each call. -/
def HitLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C), x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    Pr[WinHit prims x | exposedRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128

/-- The guess and partner lane (step 5 of the plan). A win with a guess or a partner costs
`2^-128` for each call. -/
def GuessPartnerLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C), x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    Pr[WinGuessPartner prims x | exposedRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128

/-! ## The unit of a call -/

/-- A fresh call of `H` truncates to a fixed digest with probability `2^-128`, as
`XmssSecurity.Rom.uniform_truncate_probability`. -/
theorem fresh_truncate_le (q : Query C) (s : HashCache C) (hs : s q = none) (d : Digest) :
    Pr[fun p => truncateHash p.1 = d | ((Query C →ₒ HashOutput).randomOracle q).run s] ≤
      ((2 ^ XmssSecurity.digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs, probEvent_map]
  exact (XmssSecurity.Rom.uniform_truncate_probability d).le

/-- A fresh call of `H` on the free copy of the signing world costs `2^-128` for a fixed digest. -/
theorem free_fresh_truncate_le (q : Query C) (s : HashCache C × ℕ) (hs : s.1 q = none) (d : Digest) :
    Pr[fun z => truncateHash z.1 = d | (countImpl prims (.inr (.inr (.inl q)))).run s] ≤
      ((2 ^ XmssSecurity.digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  simp only [countImpl, SeedHitProof.withCount, StateT.run_mk]
  rw [probEvent_map]
  exact fresh_truncate_le q s.1 hs d

/-- A fresh call of `H` on the counted copy of the signing world costs `2^-128` for a fixed digest. -/
theorem counted_fresh_truncate_le (q : Query C) (s : HashCache C × ℕ) (hs : s.1 q = none) (d : Digest) :
    Pr[fun z => truncateHash z.1 = d | (countImpl prims (.inl (.inl (.inr (.inl q))))).run s] ≤
      ((2 ^ XmssSecurity.digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  simp only [countImpl, SeedHitProof.withCount, StateT.run_mk]
  rw [probEvent_map]
  exact fresh_truncate_le q s.1 hs d

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
/-- A win without the flag ends in a bad event on the final cache, by `signing_run_badEvent_closed`. -/
theorem win_le_bad (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true | runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] ≤
      Pr[WinHit prims x | exposedRun prims A x] + Pr[WinGuessPartner prims x | exposedRun prims A x] := by
  rw [runSigningWorld_flaggedAfter, probEvent_map]
  refine le_trans (probEvent_mono fun r hr hwin => ?_) (probEvent_or_le _ _ _)
  have hwin' : r.1.1 = (true, false) := Prod.ext hwin.2 hwin.1
  obtain ⟨top, state, forgery, hsome, hbad⟩ := signing_run_badEvent_closed prims A x r hr hwin'
  rcases hbad with h | h
  · exact Or.inl ⟨hwin', top, state, forgery, hsome, h⟩
  · exact Or.inr ⟨hwin', top, state, forgery, hsome, h⟩

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

open SigningCostProof in
/-- `HiddenCoreAt` from the two open lanes. -/
theorem hiddenCoreAt (prims : Primitives) (C : Committee) (hitLane : HitLaneBound prims C)
    (guessPartnerLane : GuessPartnerLaneBound prims C) : SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hc hq hsmall
  rw [signingHashError_eq]
  exact le_trans (win_le_bad prims A x)
    (add_le_add (hitLane A q x hx hc hq hsmall) (guessPartnerLane A q x hx hc hq hsmall))

open SigningCostProof in
/-- `SigningSecurityStatement` from the two open lanes. -/
theorem signingSecurityComplete (prims : Primitives) (C : Committee) (hitLane : HitLaneBound prims C)
    (guessPartnerLane : GuessPartnerLaneBound prims C) : SigningSecurityStatement prims C :=
  signingSecurityFull prims C (hiddenCoreAt prims C hitLane guessPartnerLane)

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.signingSecurityComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.signingSecurityComplete
