import ThresholdLeanXmssSecurity.Proof.TreeHybrid.Tools

/-!
# The programs of a tree in the hybrid model

The program of an operator and the program of the dealer of `F_tree`, as their ceremonies with the
local steps between them.

* `topBuild`, `bottomSearch` and `bottomCheck` are the local steps of `ceremonyOutput`, as computations
  of `H`. The operators and the dealer run the same steps.
* `newTreeHybrid_top` and `newTreeHybrid_bottom` write the program of an operator as its ceremonies and
  these steps.
* `dealerCeremony_top` and `dealerCeremony_bottom` write the dealer with its log in the same form.
  `dealerBatches_run` is the log of the batches of one ceremony.
* `bottomSearch_calls` counts the calls of the codeword of a root.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The local steps -/

/-- The top tree from the outputs of its ceremony. -/
def topBuild (parameter : PublicParameter) (o : List (List Bit)) : OracleComp (RoSpec C) (Option TreeOutput) :=
  tweakable (do
    let root ← merkleNode parameter topLayer (topChainEnd o) layerHeight 0
    pure (some (.top ⟨topChainEnd o, root⟩)))

/-- The root of a bottom tree of height `H` and the codeword of the root within `L` trials. -/
def searchAt (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) (H L : ℕ) :
    OracleComp (RoSpec C) (Digest × Option (Randomizer × Encoding)) :=
  tweakable (do
    let root ← merkleNode parameter bottomLayer (fun e l => (bCpk b o e l).2.2) H b.val
    let base ← truncateHash <$> Verification.oracleHashWithHash
      (randomizerInput parameter topLayer (topKey b) (bRho b o) (littleEndianBytes 16 root))
    let g ← grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base L 0
    pure (root, g))

/-- The root of bottom tree `b` and the codeword of the root, from the outputs of the first ceremony.
The codeword is `none` if the randomizer search fails. -/
def bottomSearch (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) :
    OracleComp (RoSpec C) (Digest × Option (Randomizer × Encoding)) :=
  searchAt parameter b o layerHeight randomizerAttemptLimit

/-- The bottom tree with its top signature from the chain values `values`, or `none` if the signature
does not lead to the root of the top tree. -/
def bottomCheck (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight)) (o : List (List Bit))
    (root : Digest) (randomness : Randomizer) (values : List (List Bit)) :
    OracleComp (RoSpec C) (Option TreeOutput) :=
  tweakable (do
    let path ← merklePath parameter topLayer top.chainEnd (topKey b)
    let signature : LayerSignature := ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩
    let topRoot ← Verification.layerRootWithHash parameter topLayer (topKey b) (littleEndianBytes 16 root) signature
    pure (if topRoot ≠ some top.root then none
      else some (.bottom ⟨bCpk b o, bCommitment b o, root, signature⟩)))

/-- The codeword of a root costs one call for each node of the tree, one call for the start of the
search and one call for each trial, in each domain `p`. -/
theorem searchAt_calls (p : (LocalSpec C).Domain → Prop) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) (H L : ℕ) :
    IsQueryBoundP (liftComp (searchAt (C := C) parameter b o H L) (LocalSpec C)) p (2 ^ (H + 1) + L) := by
  refine IsQueryBoundP.liftComp_subSpec (p := fun t => p (.inr t)) (fun t => Iff.rfl) ?_
  refine tweakable_calls _ _ _ ?_
  have hbase : ∀ input : HashInput, IsQueryBoundP
      (truncateHash <$> (Verification.oracleHashWithHash input : OracleComp HashSpec HashOutput))
      (fun _ => True) 1 := by
    intro input
    rw [isQueryBoundP_map_iff]
    unfold Verification.oracleHashWithHash
    exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  refine (isQueryBoundP_bind (merkleNode_calls parameter _ _ H b.val) fun root _ =>
    isQueryBoundP_bind (hbase _) fun base _ =>
      isQueryBoundP_bind (grind_calls parameter _ _ _ base L 0) fun g _ =>
        isQueryBoundP_pure _ (root, g) 0).mono ?_
  have := Nat.one_le_two_pow (n := H + 1)
  omega

attribute [local irreducible] searchAt in
/-- The codeword of the root of a bottom tree costs at most `2 ^ (layerHeight + 1)` calls and the trials
of the search. `searchAt` stays folded here, because Lean cannot unfold a tree of height 16. -/
theorem bottomSearch_calls (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) :
    IsQueryBoundP (liftComp (bottomSearch (C := C) parameter b o) (LocalSpec C)) Counted
      (2 ^ (layerHeight + 1) + randomizerAttemptLimit) := by
  unfold bottomSearch
  exact searchAt_calls Counted parameter b o layerHeight randomizerAttemptLimit

attribute [irreducible] searchAt

private theorem searchAt_bind {β : Type} (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (o : List (List Bit)) (H L : ℕ)
    (k : Digest × Option (Randomizer × Encoding) → OracleComp (RoSpec C) β) :
    searchAt parameter b o H L >>= k =
      tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b o e l).2.2) H b.val) >>= fun root =>
        tweakable (truncateHash <$> Verification.oracleHashWithHash
          (randomizerInput parameter topLayer (topKey b) (bRho b o) (littleEndianBytes 16 root))) >>= fun base =>
          tweakable (grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base L 0) >>= fun g =>
            k (root, g) := by
  unfold searchAt
  simp only [tweakable, simulateQ_bind, simulateQ_pure, simulateQ_map, bind_assoc, pure_bind]

private theorem bottomCheck_bind {β : Type} (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) (root : Digest) (randomness : Randomizer)
    (values : List (List Bit)) (k : Option TreeOutput → OracleComp (RoSpec C) β) :
    bottomCheck parameter top b o root randomness values >>= k =
      tweakable (merklePath parameter topLayer top.chainEnd (topKey b)) >>= fun path =>
        tweakable (Verification.layerRootWithHash parameter topLayer (topKey b) (littleEndianBytes 16 root)
          ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩) >>= fun topRoot =>
          k (if topRoot ≠ some top.root then none
            else some (.bottom ⟨bCpk b o, bCommitment b o, root,
              ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩)) := by
  unfold bottomCheck
  simp only [tweakable, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]

/-! ## The program of an operator -/

section Operator

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The signature ceremony of bottom tree `b` and the check of the signature, from the codeword `w`. -/
def bottomSign (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight)) (o : List (List Bit))
    (w : Digest × Option (Randomizer × Encoding)) : PartyM C E (MainSpec C) TreeOutput :=
  match w.2 with
  | none => failure
  | some re =>
    hybridBatches K circuits settings.mode i keys (chunks settings.batchSize (signJobs b re.2)) >>= fun values =>
      oracleStep (bottomCheck keys.parameter top b o w.1 re.1 values) >>= fun res => res.elim failure pure

/-- The steps of an operator after the first ceremony of bottom tree `b`. -/
def bottomTail (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) :
    PartyM C E (MainSpec C) TreeOutput :=
  oracleStep (bottomSearch keys.parameter b o) >>= bottomSign K circuits settings i keys top b o

private theorem mapM_run_next {σ β : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (body : List Job → StateT σ M (Option β)) (f : List Job → M β) (next : σ → σ)
    (h : ∀ b s, (body b).run s = (fun o => (some o, next s)) <$> f b) :
    ∀ (L : List (List Job)) (s : σ),
      (L.mapM body).run s = (fun os => (os.map some, next^[L.length] s)) <$> L.mapM f
  | [], s => by simp
  | b :: L, s => by
    simp [List.mapM_cons, StateT.run_bind, h, mapM_run_next body f next h L, Function.iterate_succ_apply]

private theorem hybridBatches_flatten (i : C.Party) (keys : Keys C) :
    ∀ L : List (List Job),
      hybridBatches K circuits settings.mode i keys L =
        List.flatten <$> L.mapM (hybridBatch K circuits settings.mode i keys)
  | [] => by simp [hybridBatches]
  | b :: L => by simp [hybridBatches, List.mapM_cons, hybridBatches_flatten i keys L]

/-- One hybrid ceremony gives the outputs of its batches, from every start of the counters. -/
private theorem ceremonyHybridRun_run (i : C.Party) (keys : Keys C) (jobs : List Job) (s : ℕ × ℕ) :
    ∃ s', (ceremonyHybridRun K circuits settings i keys jobs).run s =
      (fun o => (some o, s')) <$> hybridBatches K circuits settings.mode i keys (chunks settings.batchSize jobs) := by
  refine ⟨(fun c : ℕ × ℕ => (c.1, c.2 + 1))^[(chunks settings.batchSize jobs).length] s, ?_⟩
  unfold ceremonyHybridRun batched
  simp only [StateT.run_bind, StateT.run_pure]
  rw [mapM_run_next _ (hybridBatch K circuits settings.mode i keys) (fun c => (c.1, c.2 + 1)) ?_,
    hybridBatches_flatten]
  · simp [foldlM_some_append]
  intro b s
  simp [hybridBatch, StateT.run_bind, StateT.run_lift, runJobs_hybrid_run, batchInputQuery, hybridContext]
  rw [show (inputShares (E := E) (G := MainSpec C) _ : Job → _) = fun job => oracleStep (inputQuery _ job) from
    funext (inputShares_eq _), mapM_oracleStep]

omit [Field E] [Algebra Bit E] in
private theorem stateLift_bind_run {α β γ : Type} (x : PartyM C E (MainSpec C) α)
    (f : α → StateT (ℕ × ℕ) (PartyM C E (MainSpec C)) β) (s : ℕ × ℕ) (g : β × (ℕ × ℕ) → PartyM C E (MainSpec C) γ) :
    (StateT.lift x >>= f).run s >>= g = x >>= fun a => (f a).run s >>= g := by
  simp [StateT.run_bind, StateT.run_lift]

private theorem oracleStep_searchAt_bind {β : Type} (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (o : List (List Bit)) (H L : ℕ) (k : Digest × Option (Randomizer × Encoding) → PartyM C E (MainSpec C) β) :
    oracleStep (searchAt parameter b o H L) >>= k =
      oracleStep (tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b o e l).2.2) H b.val)) >>= fun root =>
        oracleStep (tweakable (truncateHash <$> Verification.oracleHashWithHash
          (randomizerInput parameter topLayer (topKey b) (bRho b o) (littleEndianBytes 16 root)))) >>= fun base =>
          oracleStep (tweakable (grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base L 0)) >>= fun g =>
            k (root, g) := by
  rw [← bind_pure (searchAt parameter b o H L), searchAt_bind]
  simp only [oracleStep_bind, oracleStep_pure, bind_assoc, pure_bind]

private theorem oracleStep_bottomCheck_bind {β : Type} (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) (root : Digest) (randomness : Randomizer)
    (values : List (List Bit)) (k : Option TreeOutput → PartyM C E (MainSpec C) β) :
    oracleStep (bottomCheck parameter top b o root randomness values) >>= k =
      oracleStep (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))) >>= fun path =>
        oracleStep (tweakable (Verification.layerRootWithHash parameter topLayer (topKey b) (littleEndianBytes 16 root)
          ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) >>= fun topRoot =>
          k (if topRoot ≠ some top.root then none
            else some (.bottom ⟨bCpk b o, bCommitment b o, root,
              ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩)) := by
  rw [← bind_pure (bottomCheck parameter top b o root randomness values), bottomCheck_bind]
  simp only [oracleStep_bind, oracleStep_pure, bind_assoc, pure_bind]

/-- The program of the top tree is its ceremony and the local build. -/
theorem newTreeHybrid_top (i : C.Party) (keys : Keys C) (top : TopTree) :
    newTreeHybrid K circuits settings i keys top .top =
      hybridBatches K circuits settings.mode i keys (chunks settings.batchSize topJobs) >>= fun o =>
        oracleStep (topBuild keys.parameter o) >>= fun res => res.elim failure pure := by
  unfold newTreeHybrid
  rw [ceremonyOutput, StateT.run'_eq, StateT.run_bind]
  obtain ⟨s', hs'⟩ := ceremonyHybridRun_run K circuits settings i keys topJobs (0, 0)
  rw [hs', map_bind, bind_map_left, bind_assoc]
  refine bind_congr fun o => ?_
  dsimp only
  rw [StateT.run_bind, StateT.run_lift]
  simp only [bind_assoc, pure_bind, map_bind, StateT.run_pure, map_pure]
  rw [show topBuild keys.parameter o = tweakable (merkleNode keys.parameter topLayer (topChainEnd o) layerHeight 0)
      >>= fun root => pure (some (.top ⟨topChainEnd o, root⟩)) by
    simp only [topBuild, tweakable, simulateQ_bind, simulateQ_pure], oracleStep_bind, bind_assoc]
  simp only [oracleStep_pure, pure_bind, Option.elim]
  unfold topChainEnd
  rfl

/-- The program of a bottom tree is its first ceremony and then `bottomTail`. -/
theorem newTreeHybrid_bottom (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    newTreeHybrid K circuits settings i keys top (.bottom b) =
      hybridBatches K circuits settings.mode i keys (chunks settings.batchSize (bottomJobs b)) >>=
        bottomTail K circuits settings i keys top b := by
  unfold newTreeHybrid
  rw [ceremonyOutput, StateT.run'_eq, StateT.run_bind]
  obtain ⟨s', hs'⟩ := ceremonyHybridRun_run K circuits settings i keys (bottomJobs b) (0, 0)
  rw [hs', map_bind, bind_map_left, bind_assoc]
  refine bind_congr fun o => ?_
  dsimp only
  unfold bottomTail bottomSearch
  rw [bind_map_left, stateLift_bind_run, oracleStep_searchAt_bind]
  unfold bCpk bottomKeys
  dsimp only
  refine bind_congr fun root => ?_
  rw [stateLift_bind_run]
  unfold bRho bottomKeys
  refine bind_congr fun base => ?_
  rw [stateLift_bind_run]
  refine bind_congr fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩
  · simp only [StateT.run_pure, pure_bind]
    unfold bottomSign
    rfl
  dsimp only
  rw [StateT.run_bind, bind_assoc]
  obtain ⟨s'', hs''⟩ := ceremonyHybridRun_run K circuits settings i keys (signJobs b encoding) s'
  rw [hs'', bind_map_left]
  unfold bottomSign
  dsimp only
  refine bind_congr fun values => ?_
  rw [stateLift_bind_run, oracleStep_bottomCheck_bind]
  refine bind_congr fun path => ?_
  rw [stateLift_bind_run]
  refine bind_congr fun topRoot => ?_
  split_ifs <;> simp only [StateT.run_pure, pure_bind, Option.elim]
  unfold bCpk bCommitment bottomKeys
  rfl

/-- The first step of the signature ceremony is a call, and it aborts when the functionality gives no
output. A failed search is an abort. The signature ceremony has a batch, because the batch size is
not zero. -/
theorem bottomSign_call (hsize : 0 < settings.batchSize) (i : C.Party) (keys : Keys C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (o : List (List Bit)) (w : Digest × Option (Randomizer × Encoding)) :
    ∀ step ∈ support (advance (bottomSign K circuits settings i keys top b o w).run),
      step = .done none ∨
        ∃ input resume, step = .call input resume ∧ advance (resume none) = pure (.done none) := by
  intro step hs
  unfold bottomSign at hs
  rcases w with ⟨root, _ | re⟩
  · rw [advance_run_failure, support_pure, Set.mem_singleton_iff] at hs
    exact Or.inl hs
  have hcount : 0 < chainCount := by decide
  obtain ⟨batch, rest, hc⟩ := List.exists_cons_of_ne_nil
    (show chunks settings.batchSize (signJobs b re.2) ≠ [] by
      simp only [chunks, signJobs, ne_eq, List.map_eq_nil_iff, List.range_eq_nil, List.length_map,
        List.length_finRange]
      exact Nat.ne_of_gt (Nat.div_pos (by omega) hsize))
  dsimp only at hs
  rw [hc] at hs
  simp only [hybridBatches, hybridBatch, bind_assoc, pure_bind] at hs
  rw [advance_oracleStep_bind, mem_support_bind_iff] at hs
  obtain ⟨v, -, hs⟩ := hs
  rw [advance_bind, mainProtocol_eq, advance_progAt, pure_bind] at hs
  obtain ⟨input, resume, hcall, hnone⟩ := stages_callStep_none K settings.mode
    (batch.map (circuits keys.parameter ·.kind)) i
    (List.range (depth (batch.map (circuits keys.parameter ·.kind)))) (v, [])
  rw [hcall] at hs
  simp only [continueStep, support_pure, Set.mem_singleton_iff] at hs
  refine Or.inr ⟨input, _, hs, ?_⟩
  rw [advance_bind]
  change advance (resume none) >>= _ = _
  rw [hnone, pure_bind]
  rfl

end Operator

/-! ## The dealer -/

section Dealer

variable (circuits : Circuits) (settings : Settings) (parameter : PublicParameter) (seeds : C.Term → HashOutput)

/-- The outputs of the jobs of each batch in the clear. -/
def evalBatches (bs : List (List Job)) : OracleComp (RoSpec C) (List (List (List Bit))) :=
  bs.mapM fun batch => batch.mapM (evalJob circuits parameter seeds)

/-- The batches of the dealer give the outputs of each batch, and the log holds the same lists. -/
theorem dealerBatches_run : ∀ L : List (List Job),
    (L.mapM (fun jobs => (do
        let outputs ← liftM (jobs.mapM (evalJob circuits parameter seeds))
        tell [outputs]
        pure (some outputs) :
          WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) (Option (List (List Bit)))))).run =
      evalBatches circuits parameter seeds L >>= fun l => pure (l.map some, l)
  | [] => rfl
  | jobs :: L => by
    rw [List.mapM_cons]
    simp only [WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell, WriterT.run_pure,
      dealerBatches_run L, evalBatches, List.mapM_cons, bind_assoc, pure_bind, map_bind, map_pure,
      bind_map_left, List.map_cons]
    refine bind_congr fun a => bind_congr fun l => ?_
    simp

/-- A ceremony of the dealer and the steps after it. -/
private theorem dealerBatched_bind {α : Type} (jobs : List Job)
    (f : Option (List (List Bit)) → WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) α) :
    (batched settings.batchSize (fun jobs => (do
        let outputs ← liftM (jobs.mapM (evalJob circuits parameter seeds))
        tell [outputs]
        pure (some outputs) :
          WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) (Option (List (List Bit))))) jobs >>= f).run =
      evalBatches circuits parameter seeds (chunks settings.batchSize jobs) >>= fun l =>
        (fun p => (p.1, l ++ p.2)) <$> (f (some l.flatten)).run := by
  simp only [batched, WriterT.run_bind, dealerBatches_run, bind_assoc, pure_bind]
  refine bind_congr fun l => ?_
  rw [foldlM_some_append, List.nil_append]

private theorem map_run_liftM_bind {α β γ : Type} (x : OracleComp (RoSpec C) α)
    (f : α → WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β) (g : β × List (List (List Bit)) → γ) :
    g <$> ((liftM x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) α) >>= f).run =
      x >>= fun a => g <$> (f a).run := by
  simp [WriterT.run_bind, WriterT.run_liftM, bind_map_left, map_bind]

/-- The dealer of the top tree, with its log. -/
theorem dealerCeremony_top (hsize : 0 < settings.batchSize) (top : TopTree) :
    dealerCeremony circuits settings parameter seeds top .top =
      evalBatches circuits parameter seeds (chunks settings.batchSize topJobs) >>= fun l =>
        topBuild parameter l.flatten >>= fun res => pure (res, l) := by
  unfold dealerCeremony
  rw [ceremonyOutput, dealerBatched_bind]
  refine bind_congr fun l => ?_
  dsimp only
  rw [WriterT.run_bind, WriterT.run_liftM]
  simp only [WriterT.run_pure, bind_map_left, map_bind, map_pure]
  rw [show topBuild parameter l.flatten =
      tweakable (merkleNode parameter topLayer (topChainEnd l.flatten) layerHeight 0) >>= fun root => pure (some (.top ⟨topChainEnd l.flatten, root⟩)) by
    simp only [topBuild, tweakable, simulateQ_bind, simulateQ_pure], bind_assoc]
  simp only [pure_bind, List.empty_eq, List.append_nil]
  unfold topChainEnd
  rfl

/-- The dealer of a bottom tree, with its log. The log holds the batches of the signature ceremony only
if the search finds a codeword. -/
theorem dealerCeremony_bottom (hsize : 0 < settings.batchSize) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    dealerCeremony circuits settings parameter seeds top (.bottom b) =
      evalBatches circuits parameter seeds (chunks settings.batchSize (bottomJobs b)) >>= fun l₁ =>
        bottomSearch parameter b l₁.flatten >>= fun w =>
          match w.2 with
          | none => pure (none, l₁)
          | some re =>
            evalBatches circuits parameter seeds (chunks settings.batchSize (signJobs b re.2)) >>= fun l₂ =>
              bottomCheck parameter top b l₁.flatten w.1 re.1 l₂.flatten >>= fun res => pure (res, l₁ ++ l₂) := by
  unfold dealerCeremony
  rw [ceremonyOutput, dealerBatched_bind]
  refine bind_congr fun l => ?_
  dsimp only
  rw [bottomSearch, searchAt_bind, map_run_liftM_bind]
  unfold bCpk bottomKeys
  dsimp only
  refine bind_congr fun root => ?_
  rw [map_run_liftM_bind]
  unfold bRho bottomKeys
  refine bind_congr fun base => ?_
  rw [map_run_liftM_bind]
  refine bind_congr fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩
  · simp only [WriterT.run_pure, map_pure, List.empty_eq, List.append_nil]
  dsimp only
  rw [dealerBatched_bind, map_bind]
  refine bind_congr fun l₂ => ?_
  rw [Functor.map_map]
  dsimp only
  rw [bottomCheck_bind, map_run_liftM_bind]
  refine bind_congr fun path => ?_
  rw [map_run_liftM_bind]
  refine bind_congr fun topRoot => ?_
  split_ifs <;> simp only [WriterT.run_pure, map_pure, List.empty_eq, List.append_nil]
  unfold bCpk bCommitment bottomKeys
  rfl

end Dealer

end ThresholdLeanXmssSecurity
