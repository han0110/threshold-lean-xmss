import ThresholdLeanXmssSecurity.Proof.SigningCost
import XmssSecurity.Scan.Frame

/-!
# The hit lane of the signing core

`HitLaneBound` of `Proof/SigningCost.lean` (step 5 of the signing plan of `formal/PROOF.md`).

Proved stages.

* A win with a hit on `exposedRun` is the same event on `loggedRun` (`winHit_logged`).
* A potential on the state of `loggedRun` bounds the lane by `q / 2^128` (`hitLane_of_potential`).
  The potential starts at `0`, rises by at most `2^-128` for each counted call and reaches `1` at
  each win with a hit. The per-call sum is `XmssSecurity.expectedFinal_le`, and the count of
  `exposedRun_count_le` pays it (`count_ge_expectedCost`).
* The potential needs no step for a programming query. After such a query the run uses the
  potential `0` (`guarded`, `guarded_step`).

Open stages, the hypotheses of `hitLaneBound`.

* `HitPotential`: such a potential exists for each run.
* `NoProgramQuery`: `finalRun` asks no programming query.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningHitLaneProof

open SigningDescentProof SigningCacheProof SigningCostProof

variable {C : Committee} (prims : Primitives)

/-- The state of `loggedRun`. -/
abbrev LoggedState (C : Committee) := (HashCache C × ℕ) × QueryLog (WorldSpec C)

/-- The initial state of `loggedRun`. -/
def loggedInit : LoggedState C := (((∅ : HashCache C), 0), [])

/-- A query of the programming oracle. `finalRun` never asks it. -/
def IsProgram : (WorldSpec C).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- A log that holds a query of the programming oracle. -/
def Programmed (log : QueryLog (WorldSpec C)) : Prop := ∃ entry ∈ log, IsProgram entry.1

/-- A potential for the hit lane. It starts at `0`, rises by at most `2^-128` for each counted call
other than a programming query, and reaches `1` at each win with a hit. -/
def IsHitPotential (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (Inv : LoggedState C → Prop)
    (f : LoggedState C → ℝ≥0∞) : Prop :=
  Inv loggedInit ∧ f loggedInit = 0 ∧
    (∀ t s, Inv s → ¬IsProgram t → ∀ r ∈ support ((loggedImpl prims t).run s), Inv r.2) ∧
    (∀ t s, Inv s → ¬Programmed s.2 → ¬IsProgram t → ∑' r, Pr[= r | (loggedImpl prims t).run s] * f r.2 ≤
      f s + (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹) ∧
    ∀ z ∈ support (loggedRun prims A x), WinHit prims x (z.1, z.2.1) → 1 ≤ f z.2

/-- The first open stage of the hit lane. Each run with distinct keys and a bounded count has a
potential. -/
def HitPotential (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C), x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    ∃ Inv f, IsHitPotential prims A x Inv f

/-- The second open stage of the hit lane. `finalRun` asks no programming query, because the forger
and the honest operators use only the local oracles. -/
def NoProgramQuery (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C), ∀ z ∈ support (loggedRun prims A x), ¬Programmed z.2.2

/-- A win with a hit on `exposedRun` is the same event on `loggedRun`. -/
theorem winHit_logged (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[WinHit prims x | exposedRun prims A x] = Pr[fun z => WinHit prims x (z.1, z.2.1) | loggedRun prims A x] := by
  rw [← loggedRun_forget, probEvent_map]
  rfl

/-- A call of `loggedImpl` adds its cost to the count. -/
theorem loggedImpl_count (t : (WorldSpec C).Domain) (s : LoggedState C)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((loggedImpl prims t).run s)) :
    r.2.1.2 = s.1.2 + SeedHitProof.signCost t := by
  simp only [loggedImpl, countImpl, SeedHitProof.withCount, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, ⟨w, -, rfl⟩, rfl⟩ := hr
  rfl

/-- A call of `loggedImpl` appends itself to the log. -/
theorem loggedImpl_log (t : (WorldSpec C).Domain) (s : LoggedState C)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((loggedImpl prims t).run s)) :
    r.2.2 = s.2.logQuery t r.1 := by
  simp only [loggedImpl, countImpl, SeedHitProof.withCount, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, ⟨w, -, rfl⟩, rfl⟩ := hr
  rfl

theorem programmed_logQuery (log : QueryLog (WorldSpec C)) (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) :
    Programmed (log.logQuery t u) ↔ Programmed log ∨ IsProgram t := by
  simp [Programmed, QueryLog.logQuery, QueryLog.singleton, or_and_right, exists_or]

/-- The potential that is `0` after a programming query. -/
def guarded (f : LoggedState C → ℝ≥0∞) (s : LoggedState C) : ℝ≥0∞ :=
  open Classical in if Programmed s.2 then 0 else f s

/-- A guarded potential pays every call. -/
theorem guarded_step (Inv : LoggedState C → Prop) (f : LoggedState C → ℝ≥0∞)
    (hstep : ∀ t s, Inv s → ¬Programmed s.2 → ¬IsProgram t → ∑' r, Pr[= r | (loggedImpl prims t).run s] * f r.2 ≤
      f s + (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : ¬Programmed s.2 → Inv s) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] * guarded f r.2 ≤
      guarded f s + (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  classical
  by_cases hbad : Programmed s.2 ∨ IsProgram t
  · refine le_trans (le_of_eq (tsum_probOutput_mul_of_const_on_support _ (c := 0) (fun r hr => ?_) (by simp)))
      zero_le
    rw [guarded, if_pos (by rw [loggedImpl_log prims t s r hr, programmed_logQuery]; exact hbad)]
  · push Not at hbad
    rw [guarded, if_neg hbad.1]
    refine le_trans (ENNReal.tsum_le_tsum fun r => ?_) (hstep t s (hs hbad.1) hbad.1 hbad.2)
    gcongr
    unfold guarded
    split_ifs
    · exact zero_le
    · exact le_rfl

/-- The count of `loggedRun` pays the cost of its calls. -/
theorem count_ge_expectedCost {α : Type} (c : ℝ≥0∞) (oa : OracleComp (WorldSpec C) α) (s : LoggedState C) :
    (s.1.2 : ℝ≥0∞) * c +
        XmssSecurity.expectedSimulatedCost (loggedImpl prims) (fun t _ => (SeedHitProof.signCost t : ℝ≥0∞) * c) oa s ≤
      XmssSecurity.expectedFinal (loggedImpl prims) (fun s => (s.1.2 : ℝ≥0∞) * c) oa s := by
  refine XmssSecurity.expectedFinal_ge (loggedImpl prims) (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) _ _
    (fun t s _ => ?_) oa s trivial
  rw [tsum_probOutput_mul_of_const_on_support _ (c := ((s.1.2 + SeedHitProof.signCost t : ℕ) : ℝ≥0∞) * c)
    (fun r hr => by rw [loggedImpl_count prims t s r hr]) (by simp)]
  push_cast
  rw [add_mul]

set_option maxRecDepth 100000 in
/-- A hit potential bounds the hit lane by the count. -/
theorem hitLane_of_potential (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hcount : ∀ z ∈ support (loggedRun prims A x), z.2.1.2 ≤ q)
    (hprogram : ∀ z ∈ support (loggedRun prims A x), ¬Programmed z.2.2) (Inv : LoggedState C → Prop)
    (f : LoggedState C → ℝ≥0∞) (hf : IsHitPotential prims A x Inv f) :
    Pr[WinHit prims x | exposedRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  classical
  obtain ⟨hinit, hzero, hinv, hstep, hwin⟩ := hf
  let c : ℝ≥0∞ := (2 ^ 128 : ℝ≥0∞)⁻¹
  have hrun : loggedRun prims A x = (simulateQ (loggedImpl prims) (finalRun A x)).run loggedInit := rfl
  rw [winHit_logged, hrun]
  rw [hrun] at hwin hcount hprogram
  have hguardedInit : guarded f loggedInit = 0 := by
    rw [guarded, if_neg (by simp [loggedInit, Programmed]), hzero]
  calc Pr[fun z => WinHit prims x (z.1, z.2.1) | (simulateQ (loggedImpl prims) (finalRun A x)).run loggedInit]
      ≤ XmssSecurity.expectedFinal (loggedImpl prims) (guarded f) (finalRun A x) loggedInit := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun z => ?_
        split_ifs with hz
        · by_cases hs : z ∈ support ((simulateQ (loggedImpl prims) (finalRun A x)).run loggedInit)
          · calc _ = Pr[= z | (simulateQ (loggedImpl prims) (finalRun A x)).run loggedInit] * 1 := (mul_one _).symm
              _ ≤ _ := by
                gcongr
                rw [guarded, if_neg (hprogram z hs)]
                exact hwin z hs hz
          · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul]
        · exact zero_le
    _ ≤ guarded f loggedInit + XmssSecurity.expectedSimulatedCost (loggedImpl prims)
          (fun t _ => (SeedHitProof.signCost t : ℝ≥0∞) * c) (finalRun A x) loggedInit := by
        refine XmssSecurity.expectedFinal_le (loggedImpl prims) (Inv := fun s => ¬Programmed s.2 → Inv s)
          (fun t s hs r hr hr' => ?_) (guarded f) _ (fun t s hs => guarded_step prims Inv f hstep t s hs) _ _
          (fun _ => hinit)
        rw [loggedImpl_log prims t s r hr, programmed_logQuery] at hr'
        push Not at hr'
        exact hinv t s (hs hr'.1) hr'.2 r hr
    _ ≤ XmssSecurity.expectedFinal (loggedImpl prims) (fun s => (s.1.2 : ℝ≥0∞) * c) (finalRun A x) loggedInit := by
        rw [hguardedInit, zero_add]
        simpa [loggedInit] using count_ge_expectedCost prims c (finalRun A x) loggedInit
    _ ≤ (q : ℝ≥0∞) * c := by
        unfold XmssSecurity.expectedFinal
        calc _ ≤ ∑' z, Pr[= z | (simulateQ (loggedImpl prims) (finalRun A x)).run loggedInit] * ((q : ℝ≥0∞) * c) := by
              refine ENNReal.tsum_le_tsum fun z => ?_
              by_cases hs : z ∈ support ((simulateQ (loggedImpl prims) (finalRun A x)).run loggedInit)
              · show _ * ((z.2.1.2 : ℝ≥0∞) * c) ≤ _
                gcongr
                exact_mod_cast hcount z hs
              · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
          _ ≤ (q : ℝ≥0∞) * c := by
              rw [ENNReal.tsum_mul_right]
              calc _ ≤ 1 * ((q : ℝ≥0∞) * c) := by gcongr; exact tsum_probOutput_le_one
                _ = _ := one_mul _
    _ = (q : ℝ≥0∞) / 2 ^ 128 := (div_eq_mul_inv _ _).symm

end SigningHitLaneProof

open SigningHitLaneProof SigningCostProof in
set_option maxRecDepth 100000 in
/-- `HitLaneBound` from the open stages `HitPotential` and `NoProgramQuery`. -/
theorem hitLaneBound (prims : Primitives) (C : Committee) (hitPotential : HitPotential prims C)
    (noProgramQuery : NoProgramQuery prims C) : HitLaneBound prims C := by
  intro A q x hx hc hq hsmall
  obtain ⟨Inv, f, hf⟩ := hitPotential A q x hx hc hq hsmall
  refine hitLane_of_potential prims A q x (fun z hz => ?_) (noProgramQuery A x) Inv f hf
  refine exposedRun_count_le prims A x q hq (z.1, z.2.1) ?_
  rw [← loggedRun_forget, support_map]
  exact ⟨z, hz, rfl⟩

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.hitLaneBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.hitLaneBound
