import ThresholdLeanXmssSecurity.Proof.TreeHybrid.Program

/-!
# The simulator of a tree in the hybrid model

The simulator of a tree runs the simulator of the batches for each ceremony of the tree (GS20,
Theorem 2). `F_tree` leaks the openings of each batch of each ceremony.

* For a bottom tree it computes the codeword of the root from the openings of the first ceremony,
  with counted calls. It runs the signature ceremony only if every honest operator has an output of
  the first ceremony and the search finds a codeword.
* The receivers are the operators with an output of the last ceremony.
* `treeRealLocal` and `treeIdealLocal` are the real run and the ideal run as local computations.
  `tree_real_acc` and `tree_ideal_acc` give their accept probabilities.
* `tree_queryBound` is the count of the calls of the ideal run.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The last local step of a tree. Each honest operator with a value computes its tree from it. -/
def localFinish {σ : Type} (D : C.Coalition) (check : List (List Bit) → OracleComp (RoSpec C) (Option TreeOutput))
    (st : σ) (values : C.Party → Option (List (List Bit))) :
    OracleComp (LocalSpec C) (σ × (C.Party → Option TreeOutput)) :=
  liftComp (OverPermutation.sequenceFin fun i =>
    if i ∈ D.1 then pure none else (values i).elim (pure none) check) (LocalSpec C) >>= fun outs => pure (st, outs)

section Simulator

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (A : CeremonyAdversary C E)

/-- The simulator of the ceremonies of a tree on the openings of `F_tree`. It gives the state of the
adversary and the receivers. -/
def treeSimRun (tree : Tree) (st : A.State) (keys : C.Party → Option (Keys C))
    (l : PublicParameter × List (List (List Bit))) : OracleComp (LocalSpec C) (A.State × Finset C.Party) :=
  match tree with
  | .top =>
    simBatches K circuits settings.mode D (batchAdversary A) l.1 (knownSeed keys)
      (chunks settings.batchSize topJobs) l.2.flatten (fun _ => some []) st >>= fun r =>
    pure (r.1, Finset.univ.filter fun i => (r.2 i).isSome)
  | .bottom b =>
    simBatches K circuits settings.mode D (batchAdversary A) l.1 (knownSeed keys)
      (chunks settings.batchSize (bottomJobs b))
      (l.2.take (chunks settings.batchSize (bottomJobs b)).length).flatten (fun _ => some []) st >>= fun r₁ =>
    if ∀ i, i ∉ D.1 → (r₁.2 i).isSome then
      liftComp (bottomSearch (C := C) l.1 b (l.2.take (chunks settings.batchSize (bottomJobs b)).length).flatten)
        (LocalSpec C) >>= fun w =>
      match w.2 with
      | none => pure (r₁.1, ∅)
      | some re =>
        simBatches K circuits settings.mode D (batchAdversary A) l.1 (knownSeed keys)
          (chunks settings.batchSize (signJobs b re.2))
          (l.2.drop (chunks settings.batchSize (bottomJobs b)).length).flatten
          (fun i => (r₁.2 i).map fun _ => []) r₁.1 >>= fun r₂ =>
        pure (r₂.1, Finset.univ.filter fun i => (r₂.2 i).isSome)
    else pure (r₁.1, ∅)

/-- The simulator of a tree (GS20, Theorem 2). Its state holds the keys of the corrupt operators. -/
def treeHybridSimulator (tree : Tree) :
    Simulator (C := C) (LocalSpec C) (Keys C) (PublicParameter × List (List (List Bit))) (Finset C.Party)
      A.State where
  State := A.State × (C.Party → Option (Keys C))
  start keys z := do
    let st ← A.start keys z
    pure (st, keys)
  answer s l := do
    let r ← treeSimRun K circuits settings D A tree s.1 s.2 l
    pure ((r.1, s.2), r.2)
  output s := pure s.1

/-- The real run of a tree as a local computation. -/
def treeRealLocal (x : C.Party → Keys C) (z : Aux) (top : TopTree) (tree : Tree) (fuel : ℕ) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option TreeOutput)) :=
  A.start (corruptInputs D x) z >>= fun st =>
    executePhase localRoles D A (mainFunctionalities K settings.mode) fuel st
      (fun i => newTreeHybrid K circuits settings i (x i) top tree)

/-- The ideal run of a tree as a local computation. The dealer computes the tree and its log, the
simulator runs, and each receiver gets the tree of the dealer. -/
def treeIdealLocal (x : C.Party → Keys C) (z : Aux) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (tree : Tree) : OracleComp (LocalSpec C) (A.State × (C.Party → Option TreeOutput)) :=
  A.start (corruptInputs D x) z >>= fun st =>
  liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C) >>= fun d =>
  treeSimRun K circuits settings D A tree st (corruptInputs D x) (parameter, d.2) >>= fun r =>
  pure (r.1, fun i => if i ∉ D.1 ∧ i ∈ r.2 then d.1 else none)

/-- The real run accepts as its local form. -/
theorem tree_real_acc (x : C.Party → Keys C) (z : Aux) (top : TopTree) (tree : Tree) (fuel : ℕ)
    (Z : Distinguisher C A.State TreeOutput) :
    accepts prims (distinguish (realExecution D A (mainFunctionalities K settings.mode) fuel
        (fun i keys => newTreeHybrid K circuits settings i keys top tree) x z) Z) =
      acc prims (treeRealLocal K circuits settings D A x z top tree fuel >>= Z) := by
  unfold acc
  rw [main_accepts_eq_local prims _ (treeRealLocal K circuits settings D A x z top tree fuel >>= Z) (by
      unfold distinguish realExecution treeRealLocal
      simp only [simulateQ_bind, bind_assoc, main_simulateQ_executePhase, main_mapRoles_world,
        main_simulateQ_adversary]),
    main_accepts_eq_local prims _ (treeRealLocal K circuits settings D A x z top tree fuel >>= Z)
      (main_simulateQ_adversary prims _)]

/-- A handler that runs each local call on the free copy runs a computation of `H` on the free copy. -/
private theorem simulateQ_stateT_free_ro {σ L R α : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ (t : (LocalSpec C).Domain) st,
      (impl (.inl t)).run st = (fun a => (a, st)) <$> free (OracleComp.lift (OracleSpec.query t)))
    (p : OracleComp (RoSpec C) α) (st : σ) :
    (simulateQ impl (liftComp p (LocalSpec C + (L →ₒ R)))).run st =
      (fun a => (a, st)) <$> free (liftComp p (LocalSpec C)) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    have hq : simulateQ impl (liftComp (liftM (OracleSpec.query t) : OracleComp (RoSpec C) _)
        (LocalSpec C + (L →ₒ R))) = impl (.inl (.inr t)) := by
      rw [liftComp_def, simulateQ_query]
      simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
      erw [simulateQ_query]
      rcases t with q | x <;> exact id_map _
    rw [hq]
    erw [himpl (.inr t) st]
    simp only [bind_map_left, ih, liftComp_bind, free_bind, map_bind]
    rfl

/-- The ideal run of `F_tree` with a simulator. The functionality computes the tree on the free copy,
and the simulator runs on the counted copy. -/
private theorem idealExecution_Ftree {σ : Type} (top : TopTree) (tree : Tree)
    (S : Simulator (C := C) (LocalSpec C) (Keys C) (PublicParameter × List (List (List Bit))) (Finset C.Party) σ)
    (x : C.Party → Keys C) (z : Aux) :
    idealExecution worldRoles.adversary D (Ftree circuits settings top tree) S x z = (do
      let st ← worldRoles.adversary (S.start (corruptInputs D x) z)
      let d ← free (liftComp (dealerCeremony circuits settings
        (firstInput fun i => if i ∈ D.1 then none else some (x i)).parameter
        (knownSeed fun i => if i ∈ D.1 then none else some (x i)) top tree) (LocalSpec C))
      let a ← worldRoles.adversary (S.answer st
        ((firstInput fun i => if i ∈ D.1 then none else some (x i)).parameter, d.2))
      let out ← worldRoles.adversary (S.output a.1)
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ a.2 then d.1 else none)) := by
  unfold idealExecution Ftree
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine bind_congr fun st => ?_
  rw [simulateQ_stateT_free_ro _ (by intros; rfl)]
  simp only [bind_map_left]
  refine bind_congr fun d => ?_
  have hleak {σ' L R : Type} (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ' (OracleComp (WorldSpec C))))
      (l : L) : simulateQ impl (leak (C := C) (R := R) l) = impl (.inr l) := by
    unfold leak
    exact (simulateQ_query _ _).trans (id_map _)
  rw [hleak]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  change ((worldRoles.adversary (S.answer st _) >>= fun p => pure (p.2, p.1)) >>= fun p =>
    worldRoles.adversary (S.output p.2) >>= fun out =>
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ p.1 then d.1 else none)) = _
  simp only [bind_assoc, pure_bind]

/-- The ideal run with `treeHybridSimulator` accepts as its local form, on dealt keys. -/
theorem tree_ideal_acc {x : C.Party → Keys C} {parameter : PublicParameter} {seeds : C.Term → HashOutput}
    {pairKeys : C.Pair → HashOutput} (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (z : Aux)
    (top : TopTree) (tree : Tree) (Z : Distinguisher C A.State TreeOutput) :
    accepts prims (distinguish (idealExecution worldRoles.adversary D (Ftree circuits settings top tree)
        (treeHybridSimulator K circuits settings D A tree) x z) Z) =
      acc prims (treeIdealLocal K circuits settings D A x z parameter seeds top tree >>= Z) := by
  obtain ⟨hparam, hseed⟩ := fceremony_dealt D hx
  unfold acc
  refine (main_accepts_eq_local prims _
    (treeIdealLocal K circuits settings D A x z parameter seeds top tree >>= Z) ?_).trans
    (main_accepts_eq_local prims _ (treeIdealLocal K circuits settings D A x z parameter seeds top tree >>= Z)
      (main_simulateQ_adversary prims _)).symm
  unfold distinguish
  rw [idealExecution_Ftree, hparam, hseed]
  unfold treeIdealLocal treeHybridSimulator
  simp [simulateQ_bind, main_simulateQ_adversary, worldAnswer, simulateQ_free, bind_assoc]

/-- The steps of the ceremonies of a tree fit in the fuel of the claim, for each parameter and each
codeword. -/
def TreeFuel (tree : Tree) (fuel : ℕ) : Prop :=
  match tree with
  | .top => ∀ parameter, hybridRounds circuits parameter (chunks settings.batchSize topJobs) ≤ fuel
  | .bottom b => ∀ parameter encoding,
      hybridRounds circuits parameter (chunks settings.batchSize (bottomJobs b)) +
        hybridRounds circuits parameter (chunks settings.batchSize (signJobs b encoding)) ≤ fuel

theorem treeFuel_claim (tree : Tree) :
    TreeFuel circuits settings tree (ceremonyBatches settings * maxBatch circuits settings mainRounds) := by
  cases tree with
  | top => exact fun parameter => hybridRounds_le_fuel circuits settings 0 (fun _ => digit 0) topJobs (by simp) parameter
  | bottom b =>
    intro parameter encoding
    unfold hybridRounds
    rw [← List.sum_append, ← List.map_append]
    refine (sum_map_le_length_mul _ _ _ fun batch hb => measure_le_maxBatch circuits settings mainRounds parameter
      b encoding batch ?_).trans (Nat.mul_le_mul_right _ ?_)
    · rcases List.mem_append.1 hb with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [List.length_append, length_chunks_signJobs settings b b encoding (fun _ => digit 0)]
      exact treeBatches_le_ceremonyBatches settings (.bottom b)

private theorem signJobs_points (b : Fin (2 ^ layerHeight)) (encoding : Encoding) :
    ((signJobs b encoding).map (·.points.length)).sum = chainCount := by
  simp [signJobs, Function.comp_def]

/-- One run of the simulator of a tree costs the steps of the adversary and the overhead of the claim. -/
private theorem treeSimRun_bound (hsize : 0 < settings.batchSize) (tree : Tree) (step fuel : ℕ)
    (hanswer : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (hround : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (hfuel : TreeFuel circuits settings tree fuel) (st : A.State) (keys : C.Party → Option (Keys C))
    (l : PublicParameter × List (List (List Bit))) :
    IsQueryBoundP (treeSimRun K circuits settings D A tree st keys l) Counted
      (fuel * step + treeHybridOverhead settings C tree) := by
  have hsim := simBatches_bound K circuits settings.mode D (batchAdversary A) l.1 (knownSeed keys) step
    hanswer hround
  cases tree with
  | top =>
    have h := hsim (chunks settings.batchSize topJobs) l.2.flatten (fun _ => some []) st
    rw [chunks_flatten _ hsize] at h
    refine (isQueryBoundP_bind h fun r _ => isQueryBoundP_pure Counted _ 0).mono ?_
    have := Nat.mul_le_mul_right step (hfuel l.1)
    simp only [treeHybridOverhead]
    omega
  | bottom b =>
    have hR₁ := Nat.mul_le_mul_right step (Nat.le_of_add_right_le (hfuel l.1 fun _ => digit 0))
    have h₁ := hsim (chunks settings.batchSize (bottomJobs b))
      (l.2.take (chunks settings.batchSize (bottomJobs b)).length).flatten (fun _ => some []) st
    rw [chunks_flatten _ hsize] at h₁
    unfold treeSimRun
    refine (isQueryBoundP_bind h₁ (m := (fuel - hybridRounds circuits l.1 (chunks settings.batchSize (bottomJobs b))) *
      step + (chunks settings.batchSize (signJobs b fun _ => digit 0)).length * termHashes C + chainCount * termCount C +
      (2 ^ (layerHeight + 1) + randomizerAttemptLimit)) fun r₁ _ => ?_).mono ?_
    · split_ifs
      · refine (isQueryBoundP_bind (bottomSearch_calls l.1 b _) fun w _ => ?_).mono (Nat.add_comm _ _).le
        split
        · exact (isQueryBoundP_pure Counted _ 0).mono (Nat.zero_le _)
        · rename_i re _
          have h₂ := hsim (chunks settings.batchSize (signJobs b re.2))
            (l.2.drop (chunks settings.batchSize (bottomJobs b)).length).flatten (fun i => (r₁.2 i).map fun _ => []) r₁.1
          rw [chunks_flatten _ hsize, signJobs_points, length_chunks_signJobs settings b b re.2 (fun _ => digit 0)] at h₂
          refine (isQueryBoundP_bind h₂ fun r _ => isQueryBoundP_pure Counted _ 0).mono ?_
          have := Nat.mul_le_mul_right step (Nat.le_sub_of_add_le' (hfuel l.1 re.2))
          omega
      · exact (isQueryBoundP_pure Counted _ 0).mono (Nat.zero_le _)
    · rw [Nat.sub_mul]
      simp only [treeHybridOverhead, treeBatches, Nat.add_mul]
      omega

/-- The ideal run makes at most `q + treeHybridOverhead` counted calls. -/
theorem tree_queryBound (hsize : 0 < settings.batchSize) (x : C.Party → Keys C) (z : Aux) (top : TopTree)
    (tree : Tree) (Z : Distinguisher C A.State TreeOutput) (fuel q : ℕ)
    (hfuel : TreeFuel circuits settings tree fuel) (hq : IsQueryBounded A Z fuel q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution worldRoles.adversary D
        (Ftree circuits settings top tree) (treeHybridSimulator K circuits settings D A tree) x z) Z))
      (q + treeHybridOverhead settings C tree) := by
  obtain ⟨start, step, final, hsum, hstart, hround, hanswer, hZ⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  simp only [bind_assoc]
  have hs : CostLe prims (worldRoles.adversary
      ((treeHybridSimulator K circuits settings D A tree).start (corruptInputs D x) z)) start :=
    CostLe.of_counted prims _ start
      ((isQueryBoundP_bind (hstart _ _) fun st _ => isQueryBoundP_pure Counted _ 0).mono (Nat.add_zero _).le)
  have ha : ∀ s l, CostLe prims (worldRoles.adversary ((treeHybridSimulator K circuits settings D A tree).answer s l))
      (fuel * step + treeHybridOverhead settings C tree) := fun s l => CostLe.of_counted prims _ _
    ((isQueryBoundP_bind (treeSimRun_bound K circuits settings D A hsize tree step fuel hanswer hround hfuel s.1 s.2 l)
      fun r _ => isQueryBoundP_pure Counted _ 0).mono (Nat.add_zero _).le)
  refine CostLe.mono prims (CostLe.bind prims hs
    (m := 0 + ((fuel * step + treeHybridOverhead settings C tree + 0) + (0 + (0 + (0 + final))))) fun st => ?_) ?_
  · unfold Ftree
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine (costLe_liftComp_ro prims _ _ st).bind prims fun p => ?_
    refine (costLe_simulateQ_leak prims _ _ _ ?hl).bind prims fun r => ?_
    case hl => exact (ha _ _).bind prims fun _ => CostLe.pure prims _
    refine (CostLe.pure prims _).bind prims fun out => ?_
    refine (CostLe.of_counted prims _ 0 (isQueryBoundP_pure Counted _ 0)).bind prims fun o => ?_
    refine (CostLe.pure prims _).bind prims fun r' => ?_
    exact CostLe.of_counted prims _ _ (hZ _)
  · omega

end Simulator

end ThresholdLeanXmssSecurity
