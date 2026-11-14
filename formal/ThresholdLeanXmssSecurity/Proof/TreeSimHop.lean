import ThresholdLeanXmssSecurity.Proof.TreeSim
import ThresholdLeanXmssSecurity.Proof.TreeSecurity
import ThresholdLeanXmssSecurity.Proof.CheckLast

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-!
# The assembly of the simulation hop

This module gives `TreeSimulationHop` with the split `keySplit C` from the couplings of `TreeSim` and
from the bounds of the two bad events of a trace.

* `TreeSimHashBound` is the bound of the hash event. `treeSim_hashBudget` shows that this bound is at
  most `treeHashError - keySplit`.
* `treeSim_large` gives the hop for `q ≥ 2^128`, where the budget is at least one.
* `treeSimulationHop` gives the hop from `TreeSimStages` and from the two event bounds.
  `treeSimulationHop_of_trace` is the same assembly for a trace with a given coupling.
* `treeSimulationHopClosed` gives the hop from `TreeSimStagesGoal`, `TreeSimHashBoundGoal` and
  `TreeSimCheckBoundGoal`.
* `treeSim_checkSlice` shows that `treeSimShift` keeps the relation `SplitSliceRel` of the check.

These declarations use `TreeSecurity`, `CheckSecurity` and `CheckLast`, and `TreeSim` does not import
these modules.
-/

/-- Common translations of the hidden pivot preserve the check's split-slice
relation, even when the known copies are inconsistent across honest operators. -/
theorem treeSim_checkSlice [SampleableType E] (D : C.Coalition)
    {xsR ysR xsD ysD : C.Party → Shares C E}
    (h : SplitSliceRel D xsR ysR xsD ysD) (δx δy : ℕ → E) :
    SplitSliceRel D (fun i => treeSimShift D (xsR i) δx)
      (fun i => treeSimShift D (ysR i) δy) xsD ysD := by
  constructor
  · intro i hi T hT hiT
    simpa only [treeSimShift_known D _ δx T hT, treeSimShift_known D _ δy T hT]
      using h.1 i hi T hT hiT
  · intro T hT i j hi hj hiT hjT
    obtain ⟨hx, hy, hxd, hyd⟩ := h.2 T hT i j hi hj hiT hjT
    refine ⟨?_, ?_, hxd, hyd⟩
    · funext g
      simp only [treeSimShift, hx]
    · funext g
      simp only [treeSimShift, hy]

/-- One birthday bound for the union of hash failures. The `2 m` PRSS-key
points have already been paid by `keySplit`; no per-gadget hash budgets are added. -/
def TreeSimHashBound (trace : TreeSimTrace C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    Pr[fun r => r.2.1 = true | trace top tree D A x z Z].toReal ≤
      (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) / 2 ^ 256

/-- The hash union fits exactly in the remaining budget of the simulation hop. -/
theorem treeSim_hashBudget (tree : Tree) (q : ℕ) :
    (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) / 2 ^ 256 ≤
      treeHashError circuits settings C tree q - keySplit C q := by
  have h := keySplit_add_rest_le circuits settings (C := C) tree q
  linarith

/-- At `q ≥ 2^128` the unused hash budget alone is at least one. -/
theorem treeSim_largeHashBudget (tree : Tree) (q : ℕ) (hq : 2 ^ 128 ≤ q) :
    1 ≤ treeHashError circuits settings C tree q - keySplit C q := by
  apply le_trans _ (treeSim_hashBudget circuits settings tree q)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 256)).mpr
  have hq' : (2 : ℝ) ^ 128 ≤ (q : ℝ) := by exact_mod_cast hq
  have hnat : q ≤ q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) := Nat.le_add_right _ _
  have hcast : (q : ℝ) ≤ (q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) : ℕ) := by
    exact_mod_cast hnat
  simp only [one_mul, Nat.cast_pow]
  calc
    (2 : ℝ) ^ 256 = ((2 : ℝ) ^ 128) ^ 2 := by ring
    _ ≤ (q : ℝ) ^ 2 := by gcongr
    _ ≤ (↑(q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) : ℝ) ^ 2 := by gcongr

/-- The large-query case of the exact requested simulation hop is unconditional. -/
theorem treeSim_large (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hq : 2 ^ 128 ≤ q) :
    |(Pr[= true | (simulateQ (streamWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run' (∅, ∅)]).toReal -
      accepts prims (treeIdealGame K circuits settings top tree D A x z Z)| ≤
      treeCheckError (E := E) circuits settings tree q +
        (treeHashError circuits settings C tree q - keySplit C q) := by
  have hc : 0 ≤ treeCheckError (E := E) circuits settings tree q := by
    letI : Inhabited E := ⟨0⟩
    letI : SampleableType E := SampleableType.ofFintype E
    unfold treeCheckError
    exact mul_nonneg (Nat.cast_nonneg _) (checkErrorOf_nonneg K _ _ _)
  have hh := treeSim_largeHashBudget (C := C) circuits settings tree q hq
  have unit : ∀ {α : Type} (oa : ProbComp α) (P : α → Prop),
      0 ≤ Pr[P | oa].toReal ∧ Pr[P | oa].toReal ≤ 1 := by
    intro α oa P
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact probEvent_le_one)⟩
  rw [accepts_eq_worldRun]
  have hl := unit ((simulateQ (streamWorld prims D)
    (treeRealGame K circuits settings top tree D A x z Z)).run' (∅, ∅)) (fun b => b = true)
  have hr := unit (worldRun prims (treeIdealGame K circuits settings top tree D A x z Z))
    (fun r => r.1 = true)
  simp only [probEvent_eq_eq_probOutput] at hl
  rw [abs_le]
  constructor <;> linarith

/-- Conditional assembly, with the actual target unchanged. The four named
hypotheses above are still open; the local mask lemmas do not discharge them. -/
theorem treeSimulationHop_of_trace (trace : TreeSimTrace C E)
    (marginal : TreeSimMarginal prims K circuits settings trace)
    (coupling : TreeSimCoupling prims K circuits settings trace)
    (hashBound : TreeSimHashBound circuits settings trace)
    (checkBound : TreeSimCheckBound circuits settings trace) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  intro hb top tree D A x z Z q hx hq
  by_cases hsmall : q < 2 ^ 128
  · have hm := congrArg (fun d => d true) (marginal top tree D A x z Z)
    have hm' : Pr[fun r => r.1 = true | trace top tree D A x z Z] =
        Pr[= true | (simulateQ (streamWorld prims D)
          (treeRealGame K circuits settings top tree D A x z Z)).run' (∅, ∅)] := by
      simpa only [← probOutput_def, probOutput_map] using hm
    rw [← hm', accepts_eq_worldRun]
    have hc := treeSim_badUnion (trace top tree D A x z Z)
      (worldRun prims (treeIdealGame K circuits settings top tree D A x z Z))
      (fun r => r.2.1 = true) (fun r => r.2.2 = true) (fun r => r.1 = true)
      (fun r => r.1 = true) (coupling hb top tree D A x z Z q hx hq hsmall)
    have hh := (hashBound hb top tree D A x z Z q hx hq hsmall).trans
      (treeSim_hashBudget circuits settings tree q)
    have hcheck := checkBound hb top tree D A x z Z q hx hq hsmall
    linarith
  · exact treeSim_large prims K circuits settings top tree D A x z Z q (Nat.le_of_not_gt hsmall)

/-- The requested hop with exact experiment normalization, ghost padding,
complete PRSS prefix coupling and trace erasure. The post-setup stage invariant
and the two event bounds remain open; no experiment-normalization premise remains. -/
theorem treeSimulationHop (events : TreeSimEvents C E)
    (stages : TreeSimStages prims K circuits settings events)
    (hashBound : TreeSimHashBound circuits settings (treeSimTrace prims K circuits settings events))
    (checkBound : TreeSimCheckBound circuits settings (treeSimTrace prims K circuits settings events)) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  have coupling := treeSim_ghost_coupling prims K circuits settings events
    (treeSim_ceremony_coupling prims K circuits settings events
      (treeSim_stages_coupling prims K circuits settings events stages))
  intro hb top tree D A x z Z q hx hq
  by_cases hsmall : q < 2 ^ 128
  · obtain ⟨parameter, seeds, pairs, hx⟩ := hx
    have heq : x = dealtKeys parameter seeds pairs := funext hx
    subst x
    have hm := congrArg (fun d => d true)
      (treeSim_trace_marginal prims K circuits settings events top tree D A
        (dealtKeys parameter seeds pairs) z Z)
    have hm' : Pr[fun r => r.1 = true | treeSimTrace prims K circuits settings events top tree D A
        (dealtKeys parameter seeds pairs) z Z] =
        Pr[= true | (simulateQ (streamWorld prims D)
          (treeRealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z)).run' (∅, ∅)] := by
      simpa only [← probOutput_def, probOutput_map] using hm
    have hi := congrArg (fun p => Pr[= true | p])
      (treeSim_streamIdeal_eq prims K circuits settings top tree D A parameter seeds pairs z Z)
    simp only [probOutput_map] at hi
    rw [← hm', accepts_eq_worldRun, hi]
    have hc := treeSim_badUnion _ _ (fun r : Bool × Bool × Bool => r.2.1 = true) (fun r => r.2.2 = true)
      (fun r => r.1 = true) (fun b => b = true)
      (coupling hb top tree D A parameter seeds pairs z Z q hq hsmall)
    have dealt : DealtInputs D (dealtKeys parameter seeds pairs) := ⟨parameter, seeds, pairs, fun _ => rfl⟩
    have hh := (hashBound hb top tree D A _ z Z q dealt hq hsmall).trans
      (treeSim_hashBudget circuits settings tree q)
    have hcheck := checkBound hb top tree D A _ z Z q dealt hq hsmall
    simpa only [probEvent_eq_eq_probOutput, add_comm] using hc.trans (add_le_add hh hcheck)
  · exact treeSim_large prims K circuits settings top tree D A x z Z q (Nat.le_of_not_gt hsmall)

/-- Parallel task 2: bound the fixed collision/salt-guess union. This task does
not assume the stages or the check bound. Count distinct region points, not all
PRF/Th calls, and retain the shared dealer cache. -/
def TreeSimHashBoundGoal : Prop :=
  TreeSimHashBound circuits settings
    (treeSimTrace prims K circuits settings (treeSimEvents prims K circuits settings))

/-- Assembly of the three fixed, independent tasks. The name denotes closure
of the interface, not a claim that its three premises have been proved. -/
theorem treeSimulationHopClosed
    (stages : TreeSimStagesGoal prims K circuits settings)
    (hashBound : TreeSimHashBoundGoal prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact treeSimulationHop prims K circuits settings (treeSimEvents prims K circuits settings)
    stages hashBound checkBound

/-- info: 'ThresholdLeanXmssSecurity.treeSim_checkSlice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_checkSlice

/-- info: 'ThresholdLeanXmssSecurity.treeSim_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_large

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimulationHop

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHopClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimulationHopClosed

end ThresholdLeanXmssSecurity
