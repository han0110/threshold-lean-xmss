import ThresholdLeanXmssSecurity.Proof.SigningGuessProof

/-!
# The uncharged lane of the signing core

`SigningGuessProof.UnchargedLaneBound` reduces to one
fixed-cap first-lane monitor of leanVM, `XmssSecurity.FirstLaneOracleSimulation`.

The monitor obligation `UnchargedWorldMonitor` asks for one monitor computation
for each adversary and each key. It has three component hypotheses.

* The uncharged win of the signing run is dominated by an event of the monitor run.
* The monitor run makes at most `q` hazard queries.
* Each such event is a monitor hit.

The encoding queries of the monitor take a leaf index of `Fin 2 ^ 32`. The bottom keys fill
this range, so a top partner cannot use a separate encoding leaf. It needs a probe or a
reveal on an extra index, or a different monitor.

A per-call charge of `2^-128` times the expected call count cannot bound this lane.
`trueOpening_charge_gap` shows the gap for a stopped scan for the true opening `ρ_e`.
After the scan, a birthday search over first digest trials gives a bottom partner,
which is an uncharged win.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningUnchargedProof

variable {C : Committee}

/-- A monitor computation with a hazard cap `q` and a detected event bounds the
uncharged lane by one fixed-cap unit. -/
theorem uncharged_le_of_world (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (q : ℕ) {Index Result : Type} [Fintype Index]
    [DecidableEq Index] (monitor : OracleComp (XmssSecurity.FirstLaneOracleSimulation.World Index) Result)
    (event : Result → Prop)
    (hcouple : Pr[SigningGuessProof.UnchargedWin prims x | SigningDescentProof.exposedRun prims A x] ≤
      Pr[fun r => event r.2.1 | XmssSecurity.FirstLaneOracleSimulation.eagerExperiment monitor])
    (hbound : monitor.IsQueryBoundP XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q)
    (hdetect : ∀ r ∈ support (XmssSecurity.FirstLaneOracleSimulation.eagerExperiment monitor),
      event r.2.1 → XmssSecurity.FirstLaneOracleSimulation.CombinedHit r.1 r.2.2) :
    Pr[SigningGuessProof.UnchargedWin prims x | SigningDescentProof.exposedRun prims A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  refine hcouple.trans ((probEvent_mono hdetect).trans ?_)
  rw [XmssSecurity.FirstLaneOracleSimulation.combinedHit_probability_eq_structuralExperiment
    q monitor hbound]
  simpa only [XmssSecurity.digestBits, Nat.cast_pow, Nat.cast_ofNat] using
    XmssSecurity.FirstLaneOracleSimulation.structuralExperiment_empty_true_probability_le
      q monitor

/-- The open monitor obligation. Each adversary and each key of `KeyGen'`
within the budget has one first-lane monitor computation. -/
def UnchargedWorldMonitor (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    ∃ (Index Result : Type) (_ : Fintype Index) (_ : DecidableEq Index)
      (monitor : OracleComp (XmssSecurity.FirstLaneOracleSimulation.World Index) Result)
      (event : Result → Prop),
      Pr[SigningGuessProof.UnchargedWin prims x | SigningDescentProof.exposedRun prims A x] ≤
        Pr[fun r => event r.2.1 | XmssSecurity.FirstLaneOracleSimulation.eagerExperiment monitor] ∧
      monitor.IsQueryBoundP XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q ∧
      ∀ r ∈ support (XmssSecurity.FirstLaneOracleSimulation.eagerExperiment monitor),
        event r.2.1 → XmssSecurity.FirstLaneOracleSimulation.CombinedHit r.1 r.2.2

/-- The residual lane from the monitor obligation. -/
theorem unchargedLaneBound_of_world (prims : Primitives) (C : Committee)
    (hmonitor : UnchargedWorldMonitor prims C) : SigningGuessProof.UnchargedLaneBound prims C := by
  intro A q x hx hkeys hq hsmall
  obtain ⟨Index, Result, _, _, monitor, event, hcouple, hbound, hdetect⟩ :=
    hmonitor A q x hx hkeys hq hsmall
  exact uncharged_le_of_world prims A x q monitor event hcouple hbound hdetect

/-- The hidden core from the monitor obligation. -/
theorem hiddenCoreAt_of_world (prims : Primitives) (C : Committee)
    (hmonitor : UnchargedWorldMonitor prims C) : SigningCoreProof.HiddenCoreAt prims C :=
  SigningGuessProof.hiddenCoreAt_of_uncharged prims C (unchargedLaneBound_of_world prims C hmonitor)

/-- A commitment scan that stops at its first match finds the true opening at
trial `k` with probability `(1 - 1/N)^k / N`. This exceeds the per-call charge
`1/N` of its expected length by an exact positive gap. -/
theorem trueOpening_charge_gap (N : ℝ) (hN : N ≠ 0) (M : ℕ) :
    (∑ k ∈ Finset.range M, (1 - 1 / N) ^ k / N) -
        1 / N * (∑ k ∈ Finset.range M, SigningGuessProof.openingSurvival N k) =
      (∑ k ∈ Finset.range M, (k : ℝ) * (1 - 1 / N) ^ k) / N ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold SigningGuessProof.openingSurvival
  field_simp
  ring

/-- Two stopped trials already show the gap at `N = 2^128`. -/
theorem trueOpening_two :
    1 / (2 ^ 128 : ℝ) * (∑ k ∈ Finset.range 2, SigningGuessProof.openingSurvival (2 ^ 128) k) <
      ∑ k ∈ Finset.range 2, (1 - 1 / (2 ^ 128 : ℝ)) ^ k / 2 ^ 128 := by
  norm_num [SigningGuessProof.openingSurvival, Finset.sum_range_succ]

end SigningUnchargedProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningUnchargedProof.hiddenCoreAt_of_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningUnchargedProof.hiddenCoreAt_of_world
