import ThresholdLeanXmssSecurity.Proof.LifetimePrecomputeSwap
import ThresholdLeanXmssSecurity.Proof.Dealer

/-! # Search failure in the complete lifetime dealer table

Each bottom-tree coordinate has the marginal of its own build after the top build.
The unconditional union over all bottom trees bounds the original precompute flag.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeForgerSearch
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
variable {C : Committee}

/-- Discarded local computations do not change the next observed dealer output. -/
theorem ro_ghost (prims : Primitives) {α β : Type}
    (p : OracleComp (RoSpec C) α) (q : OracleComp (RoSpec C) β) (s : HashCache C) :
    𝒟[Prod.fst <$> roRun prims (p >>= fun _ => q) s] =
      𝒟[Prod.fst <$> roRun prims q s] := by
  have h := sameRun_swap prims (liftComp p (LocalSpec C)) (liftComp q (LocalSpec C))
    (fun _ b => pure b) s
  simp only [simulateQ_bind, StateT.run_bind,
    localRun_liftComp, simulateQ_pure, StateT.run_pure] at h
  have he := congrArg (fun d : SPMF (β × HashCache C) => Prod.fst <$> d) h
  simp only [← evalDist_map, map_bind, map_pure] at he
  simp only [roRun_bind, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
  refine he.trans ?_
  apply evalDist_bind_congr
  intro r hr
  exact SwapPort.evalDist_bind_ignore _ _

/-- A selected list coordinate has the marginal of its own oracle computation. -/
theorem ro_mapM_getD (prims : Primitives) {α β : Type} (f : α → OracleComp (RoSpec C) β)
    (xs : List α) (n : ℕ) (hn : n < xs.length) (fallback : β) (s : HashCache C) :
    𝒟[(fun r => r.1.getD n fallback) <$> roRun prims (xs.mapM f) s] =
      𝒟[Prod.fst <$> roRun prims (f xs[n]) s] := by
  induction xs generalizing n s with
  | nil => simp at hn
  | cons a xs ih =>
    cases n with
    | zero =>
      simp only [List.mapM_cons, roRun_bind, map_bind, List.getElem_cons_zero]
      apply evalDist_bind_congr
      intro r hr
      simp only [roRun_pure, map_pure, List.getD_cons_zero]
      exact SwapPort.evalDist_bind_ignore _ _
    | succ n =>
      have hn' : n < xs.length := by simpa using hn
      simp only [List.mapM_cons, roRun_bind, map_bind, List.getElem_cons_succ]
      calc
        _ = 𝒟[roRun prims (f a) s >>= fun r =>
          Prod.fst <$> roRun prims (f xs[n]) r.2] := by
          apply evalDist_bind_congr
          intro r hr
          simp only [roRun_pure, map_pure, List.getD_cons_succ,
            bind_pure_comp]
          exact ih n hn' r.2
        _ = _ := by
          simpa only [roRun_bind, map_bind] using ro_ghost prims (f a) (f xs[n]) s

open LifetimeForgerReplay

/-- A table coordinate has the top-plus-one-bottom marginal. -/
theorem table_coordinate (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) :
    𝒟[(fun r => r.1 (.bottom b)) <$>
      roRun prims (dealerTables circuits settings parameter seeds) ∅] =
    𝒟[Prod.fst <$> roRun prims (do
      let top ← dealerCeremony circuits settings parameter seeds emptyTop .top
      dealerCeremony circuits settings parameter seeds
        ((TreeOutput.topTree top.1).getD emptyTop) (.bottom b)) ∅] := by
  simp only [dealerTables, roRun_bind, map_bind]
  apply evalDist_bind_congr
  intro r hr
  simp only [roRun_pure, map_pure, bind_pure_comp]
  have h := ro_mapM_getD prims
    (fun b => dealerCeremony circuits settings parameter seeds
      ((TreeOutput.topTree r.1.1).getD emptyTop) (.bottom b))
    (List.finRange (2 ^ layerHeight)) b.val (by rw [List.length_finRange]; exact b.isLt) default r.2
  have hi : (List.finRange (2 ^ layerHeight))[b.val]'(by rw [List.length_finRange]; exact b.isLt) = b := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  simpa only [hi] using h

/-- A bottom coordinate fails at most as often as the reference success experiment. -/
theorem table_coordinate_fail (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) :
    Pr[fun r => (r.1 (.bottom b)).1 = none |
      roRun prims (dealerTables circuits settings parameter seeds) ∅] ≤
        (1 - codewordP) ^ randomizerAttemptLimit := by
  have hm := table_coordinate prims circuits settings parameter seeds b
  have hp := congrArg (fun d : SPMF (Option TreeOutput × List (List (List Bit))) =>
    d.run.toOuterMeasure (some '' {x | x.1 = none})) hm
  change Pr[fun x => x.1 = none | (fun r => r.1 (.bottom b)) <$>
    roRun prims (dealerTables circuits settings parameter seeds) ∅] =
    Pr[fun x => x.1 = none | Prod.fst <$> roRun prims (do
      let top ← dealerCeremony circuits settings parameter seeds emptyTop .top
      dealerCeremony circuits settings parameter seeds
        ((TreeOutput.topTree top.1).getD emptyTop) (.bottom b)) ∅] at hp
  simp only [probEvent_map, Function.comp_def] at hp
  rw [hp]
  have hb : Pr[fun r => r.1.1 = none | roRun prims (do
      let top ← dealerCeremony circuits settings parameter seeds emptyTop .top
      dealerCeremony circuits settings parameter seeds
        ((TreeOutput.topTree top.1).getD emptyTop) (.bottom b)) ∅] ≤
    Pr[fun r => r.1 = none | roRun prims (do
      let top ← dealerCeremony circuits settings parameter seeds emptyTop .top
      let some t := TreeOutput.topTree top.1 | pure none
      Prod.fst <$> dealerCeremony circuits settings parameter seeds t (.bottom b)) ∅] := by
    simp only [roRun_bind]
    simp only [probEvent_bind_eq_tsum]
    apply ENNReal.tsum_le_tsum
    intro r
    apply mul_le_mul_right 
    cases ht : TreeOutput.topTree r.1.1 with
    | none => simp only [Option.getD_none, roRun_pure, probEvent_pure]; exact probEvent_le_one
    | some t => simp only [Option.getD_some, roRun_map, probEvent_map, Function.comp_def, le_refl]
  exact hb.trans (by
    erw [roRun_dealerSuccess prims circuits settings hc hsize]
    exact refSuccess_fail prims parameter seeds b)

/-- The unconditional union charges one reference failure bound per bottom tree. -/
theorem table_search_fail (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    Pr[fun r => searchFails r.1 = true |
      roRun prims (dealerTables circuits settings parameter seeds) ∅] ≤
        (2 ^ layerHeight : ℝ≥0∞) * (1 - codewordP) ^ randomizerAttemptLimit := by
  calc
    _ ≤ Pr[fun r => ∃ b ∈ (Finset.univ : Finset (Fin (2 ^ layerHeight))),
      (r.1 (.bottom b)).1 = none |
      roRun prims (dealerTables circuits settings parameter seeds) ∅] := by
        apply probEvent_mono
        intro r hr h
        simp only [searchFails, List.any_eq_true, Option.isNone_iff_eq_none] at h
        obtain ⟨b, hb, hfail⟩ := h
        exact ⟨b, Finset.mem_univ _, hfail⟩
    _ ≤ ∑ b : Fin (2 ^ layerHeight), Pr[fun r => (r.1 (.bottom b)).1 = none |
      roRun prims (dealerTables circuits settings parameter seeds) ∅] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _b : Fin (2 ^ layerHeight), (1 - codewordP) ^ randomizerAttemptLimit :=
        Finset.sum_le_sum fun b _ => table_coordinate_fail prims circuits settings hc hsize parameter seeds b
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

private def output {α : Type} (p : EmulationM C α) : OracleComp (WorldSpec C) α :=
  (fun r => r.1.1) <$> (p.run ∅).run

private theorem output_lift_bind {α β : Type} (p : OracleComp (WorldSpec C) α)
    (f : α → EmulationM C β) :
    output (StateT.lift (liftM p) >>= f) = p >>= fun a => output (f a) := by
  simp only [output, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    WriterT.run_bind, WriterT.run_liftM, bind_map_left, map_bind, Functor.map_map]

private theorem output_map {α β : Type} (f : α → β) (p : EmulationM C α) :
    f <$> output p = output (f <$> p) := by
  simp only [output, StateT.run_map, WriterT.run_map, Functor.map_map]

section Original
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (attempts : ℕ) (D : C.Coalition) (A : LifetimeAdversary C E)

omit [Fintype E] [DecidableEq E] in
/-- Erasing the real lifetime counter preserves both precompute outputs. -/
theorem precompute_output :
    precomputeRun prims K circuits settings attempts D A =
      (simulateQ (worldAnswer prims) (precomputeGame K circuits settings attempts D A)).run' ∅ := by
  simp only [precomputeRun, bind_pure_comp]
  exact fst_map_run_withAddCost _ _ _ _

omit [Fintype E] [DecidableEq E] in
/-- The first output of the original run observes only its sampled dealer table. -/
theorem precompute_flag :
    𝒟[Prod.fst <$> precomputeRun prims K circuits settings attempts D A] =
      𝒟[prawnsKeyGen (C := C) >>= fun d =>
        (fun r => searchFails r.1) <$>
          roRun prims (dealerTables circuits settings d.1 (honestSeeds D d.2.2)) ∅] := by
  rw [precompute_output]
  have hmap {α β : Type} (f : α → β) (p : OracleComp (WorldSpec C) α) :
      f <$> (simulateQ (worldAnswer prims) p).run' (∅ : HashCache C) =
        (simulateQ (worldAnswer prims) (f <$> p)).run' ∅ := by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [hmap]
  unfold precomputeGame
  change 𝒟[(simulateQ (worldAnswer prims) (Prod.fst <$> output _)).run' ∅] = _
  rw [output_map]
  simp only [map_bind, map_pure]
  rw [output_lift_bind]
  simp only [simulateQ_bind, simulateQ_world_sample, StateT.run'_eq,
    StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
  apply evalDist_bind_congr
  intro d hd
  change 𝒟[Prod.fst <$> (simulateQ (worldAnswer prims)
    (output (StateT.lift (liftM (free (liftComp
      (dealerTables circuits settings d.1 (honestSeeds D d.2.2)) (LocalSpec C)))) >>= _))).run ∅] = _
  rw [output_lift_bind]
  simp only [simulateQ_bind, StateT.run_bind, map_bind, simulateQ_free, localRun_liftComp]
  apply evalDist_bind_congr
  intro r hr
  rw [output_lift_bind]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  -- Both following computations are lossless and their output is unobserved.
  simp only [← output_map, simulateQ_map, StateT.run_map, Functor.map_map,
    Function.comp_def]
  calc
    _ = 𝒟[(simulateQ (worldAnswer prims) (idealExecution (fun p => p) D
      (LifetimeSlots.dealtKeygen d) (keygenSimulator D A.keygen) (fun _ => ()) [])).run r.2 >>=
        fun _ => pure (searchFails r.1)] := by
      apply evalDist_bind_congr
      intro st hst
      simp only [map_eq_bind_pure_comp]
      exact SwapPort.evalDist_bind_ignore _ _
    _ = _ := SwapPort.evalDist_bind_ignore _ _

omit [Fintype E] [DecidableEq E] in
/-- The exact original search obligation, with one failure allowance per bottom tree. -/
theorem precomputeSearch : PrecomputeSearch prims K circuits settings attempts D A := by
  intro hc hsize
  have hflag := precompute_flag prims K circuits settings attempts D A
  have he := congrArg (fun d : SPMF Bool => d.run.toOuterMeasure (some '' {b | b = true})) hflag
  change Pr[fun b => b = true | Prod.fst <$> precomputeRun prims K circuits settings attempts D A] =
    Pr[fun b => b = true | prawnsKeyGen (C := C) >>= fun d =>
      (fun r => searchFails r.1) <$>
        roRun prims (dealerTables circuits settings d.1 (honestSeeds D d.2.2)) ∅] at he
  simp only [probEvent_map, Function.comp_def] at he
  rw [he]
  have hb : Pr[fun b => b = true | prawnsKeyGen (C := C) >>= fun d =>
      (fun r => searchFails r.1) <$>
        roRun prims (dealerTables circuits settings d.1 (honestSeeds D d.2.2)) ∅] ≤
      (2 ^ layerHeight : ℝ≥0∞) * (1 - codewordP) ^ randomizerAttemptLimit := by
    apply probEvent_bind_le_of_forall_le
    intro d hd
    simp only [probEvent_map, Function.comp_def]
    exact table_search_fail prims circuits settings hc hsize _ _
  have hfin : (2 ^ layerHeight : ℝ≥0∞) * (1 - codewordP) ^ randomizerAttemptLimit ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self))
  have hreal := ENNReal.toReal_mono hfin hb
  rw [ENNReal.toReal_mul, toReal_failure, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hreal
  exact hreal

end Original
end ThresholdLeanXmssSecurity.LifetimeForgerSearch

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.ro_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.ro_ghost

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.ro_mapM_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.ro_mapM_getD

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.table_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.table_coordinate

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.table_coordinate_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.table_coordinate_fail

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.table_search_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.table_search_fail

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.precompute_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.precompute_output

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.precompute_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.precompute_flag

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSearch.precomputeSearch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSearch.precomputeSearch
