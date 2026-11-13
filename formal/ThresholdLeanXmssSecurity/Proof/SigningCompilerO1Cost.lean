import ThresholdLeanXmssSecurity.Proof.SigningCompilerCoupling
import ThresholdLeanXmssSecurity.Proof.SigningLaneHybridCapO1

/-! # Exact costs of threshold-guarded completion

Completion, suffix release, digit recording, key sweeps and corruption consume
zero counted source queries. The O1 state lens preserves the exact source count
for the unchanged deferred alphabet.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningCompilerO1CostProof

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningLaneHybridCapO1Proof

variable {C : Committee}
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem sourceCost_sourceBottomCompletion (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep) :
    SourceCost (sourceBottomCompletion P seeds e l pos) 0 := by
  unfold sourceBottomCompletion
  refine (sourceCost_sourceReveal _).bind (m := 0) _ fun value => ?_
  dsimp only
  split
  · refine (SourceCost.pure (C := C) (0 : Digest)).bind (m := 0) _ fun offset => ?_
    change Digest at offset
    exact (SourceCost.lift _ 0 (exact_completePrf seeds _ (value ^^^ offset))).bind
      (m := 0) _ fun _ => SourceCost.modify _
  · refine (sourceCost_deferredQuery_uncounted (C := C) _ id).bind (m := 0) _ fun offset => ?_
    change Digest at offset
    exact (SourceCost.lift _ 0 (exact_completePrf seeds _ (value ^^^ offset))).bind
      (m := 0) _ fun _ => SourceCost.modify _

theorem sourceCost_sourceReleaseBottomSuffix (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    SourceCost (sourceReleaseBottomSuffix P seeds e l start) 0 := by
  rw [sourceReleaseBottomSuffix_eq]
  refine (SourceCost.mapM_zero _ _
    (fun pos _ => sourceCost_sourceBottomCompletion P seeds e l pos)).bind (m := 0) _ fun _ => ?_
  exact (SourceCost.mapM_zero _ _ (fun pos _ => sourceCost_sourcePlant P (.bottom e l pos))).bind
    (m := 0) _ fun _ => SourceCost.pure ()

/-- Exact source count over every O1 state, with the unchanged counted predicate. -/
def SourceCostO1 {α : Type} (oa : SourceMO1 C α) (n : ℕ) : Prop :=
  ∀ st, XmssSecurity.ExactPredicateQueryCount sourceCounted (oa.run st) n

theorem SourceCostO1.pure {α : Type} (a : α) : SourceCostO1 (C := C) (pure a) 0 := by
  intro st
  exact .pure (a, st)

theorem SourceCostO1.bind {α β : Type} {oa : SourceMO1 C α} {n m : ℕ}
    (h : SourceCostO1 oa n) (f : α → SourceMO1 C β) (hf : ∀ a, SourceCostO1 (f a) m) :
    SourceCostO1 (oa >>= f) (n + m) := by
  intro st
  rw [StateT.run_bind]
  exact XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind (h st) _ m
    (fun a => hf a.1 a.2)

theorem SourceCostO1.get : SourceCostO1 (get : SourceMO1 C (SourceStateO1 C)) 0 := by
  intro st
  exact .pure (st, st)

theorem SourceCostO1.modify (f : SourceStateO1 C → SourceStateO1 C) :
    SourceCostO1 (modify f : SourceMO1 C Unit) 0 := by
  intro st
  exact .pure ((), f st)

theorem SourceCostO1.mapM_zero {α β : Type} (xs : List α) (f : α → SourceMO1 C β)
    (hf : ∀ a ∈ xs, SourceCostO1 (f a) 0) : SourceCostO1 (xs.mapM f) 0 := by
  induction xs with
  | nil => exact SourceCostO1.pure []
  | cons a xs ih =>
      rw [List.mapM_cons]
      refine (hf a (List.mem_cons_self ..)).bind (m := 0) _ fun b => ?_
      exact (ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))).bind (m := 0) _
        (fun bs => SourceCostO1.pure (b :: bs))

theorem sourceCostO1_liftBase {α : Type} {oa : SourceM C α} {n : ℕ}
    (h : SourceCost oa n) : SourceCostO1 (liftBase oa) n := by
  intro st
  change XmssSecurity.ExactPredicateQueryCount sourceCounted
    ((fun r => (r.1, { st with base := r.2 })) <$> oa.run st.base) n
  rw [map_eq_bind_pure_comp]
  simpa only [Nat.add_zero, Function.comp_def] using
    (XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind (h st.base) _ 0
      (fun r => XmssSecurity.ExactPredicateQueryCount.pure (r.1, { st with base := r.2 })))

theorem sourceCostO1_recordStart (e : KeyIndex) (l : ChainIndex) (pos : Digit) :
    SourceCostO1 (recordStart (C := C) e l pos) 0 :=
  SourceCostO1.modify _

theorem sourceCostO1_sourceReleaseCovered (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceCostO1 (sourceReleaseCovered P seeds e l) 0 := by
  unfold sourceReleaseCovered
  refine SourceCostO1.get.bind (m := 0) _ fun st => ?_
  cases firstStart (st.starts e l) with
  | none => exact SourceCostO1.pure ()
  | some start => exact sourceCostO1_liftBase (sourceCost_sourceReleaseBottomSuffix P seeds e l start)

theorem sourceCostO1_sourceReleaseKey (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceCostO1 (sourceReleaseKey P seeds e) 0 := by
  unfold sourceReleaseKey
  exact (SourceCostO1.mapM_zero _ _ (fun l _ => sourceCostO1_sourceReleaseCovered P seeds e l)).bind
    (m := 0) _ fun _ => SourceCostO1.pure ()

theorem sourceCostO1_corrupt (prims : Primitives) (x : Keys3 C) (top : TopTree) (i : C.Party) :
    SourceCostO1 (sourceTsigO1 prims x top (.corrupt i)) 0 := by
  unfold sourceTsigO1
  refine SourceCostO1.get.bind (m := 0) _ fun st => ?_
  dsimp only
  split
  · exact SourceCostO1.pure none
  · refine (SourceCostO1.modify _).bind (m := 0) _ fun _ => ?_
    exact (SourceCostO1.mapM_zero _ _ (fun e _ => sourceCostO1_sourceReleaseKey x.1 x.2.1 e)).bind
      (m := 0) _ fun _ => SourceCostO1.pure _

end ThresholdLeanXmssSecurity.SigningCompilerO1CostProof

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCost_sourceBottomCompletion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCost_sourceBottomCompletion

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCost_sourceReleaseBottomSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCost_sourceReleaseBottomSuffix

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_liftBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_recordStart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_recordStart

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_sourceReleaseCovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_sourceReleaseCovered

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_sourceReleaseKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_sourceReleaseKey

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_corrupt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1CostProof.sourceCostO1_corrupt
