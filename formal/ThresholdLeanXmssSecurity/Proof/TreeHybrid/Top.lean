import ThresholdLeanXmssSecurity.Proof.TreeHybrid.Simulator

/-!
# The top tree in the hybrid model

The top tree has one ceremony and one local step, the build of the tree from the chain ends.

* `top_cut_acc` cuts the real run at the end of the ceremony (`ceremony_cut`). Each operator with an
  output then builds its tree (`executePhase_localOnly`).
* `hybridCommon_swap` changes the opened outputs to the outputs of the dealer.
* `top_ideal_acc` moves the build of the dealer to the time of its use (`sameRun_swap`, `obsEq_hash`).
* `top_distance` is the distance of the real run and the ideal run.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The budget of an adversary does not depend on the output type of its distinguisher. -/
theorem isQueryBounded_const {I L R O O' : Type} {A : Adversary C E I L R} {Z : Distinguisher C A.State O}
    {fuel q : ℕ} (hq : IsQueryBounded A Z fuel q) :
    IsQueryBounded A (fun _ => pure true : Distinguisher C A.State O') fuel q := by
  obtain ⟨start, step, final, h, hs, hr, ha, -⟩ := hq
  exact ⟨start, step, final, h, hs, hr, ha, fun _ => isQueryBoundP_pure _ _ _⟩

section Top

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (A : CeremonyAdversary C E)
  {x : C.Party → Keys C} {parameter : PublicParameter} {seeds : C.Term → HashOutput}
  {pairKeys : C.Pair → HashOutput}

/-- The real run of the top tree is the common run of its ceremony and then the local build at each
operator with an output. -/
theorem top_cut_acc (hsize : 0 < settings.batchSize) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (z : Aux) (top : TopTree)
    (Z : Distinguisher C A.State TreeOutput) (extra : ℕ) :
    acc prims (treeRealLocal K circuits settings D A x z top .top
        (hybridRounds circuits parameter (chunks settings.batchSize topJobs) + extra) >>= Z) =
      acc prims (hybridCommon K circuits settings topJobs D A x z parameter seeds >>= fun r =>
        localFinish D (topBuild parameter) r.2.1 r.2.2 >>= Z) := by
  have hprog : (fun i => newTreeHybrid K circuits settings i (x i) top .top) = fun i =>
      (some ([] : List (List Bit))).elim failure fun _ => newTreeHybrid K circuits settings i (x i) top .top := by
    funext i
    rw [Option.elim_some]
  have hcore := mainRealHybridCore_of prims K (mainEngineReal prims K) (mainRealSim prims K)
  refine acc_obsEq prims ?_
  unfold treeRealLocal hybridCommon
  simp only [bind_assoc]
  refine ObsEq.bind_right _ fun st => ?_
  rw [hprog, executePhase_batchAdversary]
  simp only [newTreeHybrid_top]
  refine ((ceremony_cut prims K circuits settings.mode D (batchAdversary A) hcore hx _ (fun _ => some []) st
    extra _).bind_left Z).trans (ObsEq.of_eq ?_)
  rw [chunks_flatten _ hsize]
  have key : ∀ r : A.State × (C.Party → Option (List (List Bit))),
      executePhase localRoles D (batchAdversary A) (mainFunctionalities K settings.mode) extra r.1
        (fun i => (r.2 i).elim failure fun o =>
          oracleStep (topBuild (x i).parameter o) >>= fun res => res.elim failure pure) =
        localFinish D (topBuild parameter) r.1 r.2 := by
    intro r
    refine (executePhase_congr D (batchAdversary A) _ extra r.1 _
      (fun i => oracleStep ((r.2 i).elim (pure none) (topBuild parameter)) >>= fun res => res.elim failure pure)
      fun i _ => ?_).trans ((executePhase_localOnly D (batchAdversary A) _ extra r.1 _).trans ?_)
    · have hp : (x i).parameter = parameter := by rw [hx i]; rfl
      rw [hp]
      cases r.2 i with
      | none => rw [Option.elim_none, Option.elim_none, oracleStep_pure, pure_bind, Option.elim_none]
      | some o => rw [Option.elim_some, Option.elim_some]
    · unfold localFinish
      rfl
  exact (bind_assoc _ _ _).trans (bind_congr fun o => (bind_assoc _ _ _).trans (bind_congr fun r => by
    rw [pure_bind]
    exact congrArg (· >>= Z) (key r)))

/-- The batches of the dealer give the outputs of all jobs. -/
theorem evalBatches_flatten (bs : List (List Job)) :
    List.flatten <$> evalBatches (C := C) circuits parameter seeds bs =
      bs.flatten.mapM (evalJob circuits parameter seeds) := by
  induction bs with
  | nil => simp [evalBatches]
  | cons b bs ih =>
    rw [List.flatten_cons, List.mapM_append, ← ih]
    simp [evalBatches, List.mapM_cons, map_bind]

/-- With the outputs of the dealer at each operator with an output, the run is the ideal run. -/
theorem top_ideal_acc (hsize : 0 < settings.batchSize) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (z : Aux) (top : TopTree) (Z : Distinguisher C A.State TreeOutput) :
    acc prims (hybridCommon K circuits settings topJobs D A x z parameter seeds >>= fun r =>
        localFinish D (topBuild parameter) (ceremonyIdealOut D r).1 (ceremonyIdealOut D r).2 >>= Z) =
      acc prims (treeIdealLocal K circuits settings D A x z parameter seeds top .top >>= Z) := by
  refine acc_obsEq prims ?_
  unfold hybridCommon treeIdealLocal
  rw [dealerCeremony_top circuits settings parameter seeds hsize top]
  simp only [bind_assoc, liftComp_bind, liftComp_pure, pure_bind]
  refine ObsEq.bind_right _ fun st => ?_
  have hM : topJobs.mapM (evalJob circuits parameter seeds) =
      List.flatten <$> evalBatches (C := C) circuits parameter seeds (chunks settings.batchSize topJobs) := by
    rw [evalBatches_flatten, chunks_flatten _ hsize]
  rw [hM, liftComp_map, bind_map_left]
  refine ObsEq.bind_right _ fun l => ?_
  unfold treeSimRun
  simp only [bind_assoc, pure_bind, Finset.mem_filter, Finset.mem_univ, true_and]
  generalize simBatches K circuits settings.mode D (batchAdversary A) parameter (knownSeed (corruptInputs D x))
    (chunks settings.batchSize topJobs) l.flatten (fun _ => some []) st = S
  refine ObsEq.trans ?_ (sameRun_swap prims (liftComp (topBuild parameter l.flatten) (LocalSpec C)) S
    (fun res r => Z (r.1, fun i => if i ∉ D.1 ∧ (r.2 i).isSome = true then res else none))).symm.obsEq
  refine ObsEq.bind_right _ fun r => ?_
  unfold localFinish ceremonyIdealOut
  simp only [bind_assoc, pure_bind]
  refine obsEq_hash prims _ _ _ _ fun h _ => ObsEq.of_eq ?_
  rw [valueAt_sequenceFin]
  refine congrArg (fun outs => Z (r.1, outs)) (funext fun i => ?_)
  by_cases hi : i ∈ D.1
  · rw [ite_eq_left hi, ite_eq_right (fun h => h.1 hi), D_pure]
  · by_cases hs : (r.2 i).isSome = true
    · rw [ite_eq_right hi, ite_eq_left ⟨hi, hs⟩, ite_eq_left ⟨hi, hs⟩, Option.elim_some]
    · rw [ite_eq_right hi, ite_eq_right (fun h => hs h.2), ite_eq_right (fun h => hs h.2), Option.elim_none, D_pure]

/-- The distance of the real run and the ideal run of the top tree. -/
theorem top_distance (hsize : 0 < settings.batchSize) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (z : Aux) (top : TopTree) (Z : Distinguisher C A.State TreeOutput) (fuel q : ℕ)
    (hfuel : TreeFuel circuits settings .top fuel) (hq : IsQueryBounded A Z fuel q) :
    |accepts prims (distinguish (realExecution D A (mainFunctionalities K settings.mode) fuel
        (fun i keys => newTreeHybrid K circuits settings i keys top .top) x z) Z) -
      accepts prims (distinguish (idealExecution worldRoles.adversary D (Ftree circuits settings top .top)
        (treeHybridSimulator K circuits settings D A .top) x z) Z)| ≤ treeHybridError settings C .top q := by
  have hR : hybridRounds circuits parameter (chunks settings.batchSize topJobs) ≤ fuel := hfuel parameter
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hR
  have h1 := top_cut_acc prims K circuits settings D A hsize hx z top Z extra
  rw [← hextra] at h1
  have h2 := hybridCommon_swap prims K circuits settings topJobs D A hsize x z parameter seeds
    (fun _ => pure true) fuel q hR (isQueryBounded_const hq)
    (fun p => localFinish D (topBuild parameter) p.1 p.2 >>= Z)
  have h3 := top_ideal_acc prims K circuits settings D A hsize hx z top Z
  rw [tree_real_acc, tree_ideal_acc prims K circuits settings D A hx z top .top Z, h1, ← h3]
  exact h2

end Top

end ThresholdLeanXmssSecurity
