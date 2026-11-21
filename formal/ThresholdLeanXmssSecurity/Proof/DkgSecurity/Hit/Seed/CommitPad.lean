import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Close

/-!
# The pad of the commitments between honest operators

In the seed generation an honest operator `i` asks the cell `commit .seedGen i j r` on the free copy
and sends the answer to `j`. An honest receiver `j` asks the same cell again and compares the two
answers. No other step reads the answer. So the answer of a free call of such a cell with two honest
operators goes into one equality test only.

`prEvent_le_of_shiftMean` is the mean over a shift, the common step on the world of the two hit
parts.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

attribute [local instance] Classical.propDecidable

/-! ## The mean over a shift -/

/-- A probability `p` that is at most the probability of `δ ∈ named` in one run for each `δ`, with at
most `N` named values at the end of each run, is at most `N` over the number of the values. The bound
is a mean over the run and over `δ`. -/
theorem prEvent_le_of_shiftMean {V Y : Type} [Fintype V] [SampleableType V] (p : ℝ≥0∞) (run : ProbComp Y)
    (named : Y → Finset V) (N : ℕ) (step : ∀ δ, p ≤ Pr{let y ← run}[δ ∈ named y])
    (count : ∀ y ∈ support run, (named y).card ≤ N) : p ≤ (N : ℝ≥0∞) / (Fintype.card V : ℝ≥0∞) := by
  have h₁ : p ≤ wp ($ᵗ V) (fun δ => wp run (fun y => if δ ∈ named y then 1 else 0)) := by
    calc p = wp ($ᵗ V) (fun _ => p) := (wp_const _ p).symm
      _ ≤ _ := wp_mono _ fun δ => (step δ).trans_eq (prEvent_eq_wp_indicator _ _)
  refine h₁.trans ?_
  rw [DkgSecurityProof.wp_swap]
  refine (wp_mono_of_support run fun y hy => ?_).trans_eq (wp_const run _)
  rw [← prEvent_eq_wp_indicator, SampleableType.prEvent_uniformSample]
  refine ENNReal.div_le_div_right ?_ _
  have hc : (Finset.univ.filter fun δ => δ ∈ named y).card ≤ N := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact count y hy
  exact_mod_cast hc

variable {C : Committee}

/-! ## The pad -/

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.prEvent_le_of_shiftMean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.prEvent_le_of_shiftMean

