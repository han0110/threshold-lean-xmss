import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.Hops
import ThresholdLeanXmssSecurity.Proof.SeedGen
import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.Signing

/-!
# The keys of the seed generation and the abort of the dealer

`seedGenHop` proves `SeedGenHop`. The honest seed generation gives the keys from fresh derivations of
`H`. The trees of the dealer read only cells of `Th` and of the PRF, so the cells of the derivations
do not change them. With distinct derivation inputs, the derivations are uniform and give the keys of
`prawnsKeyGen`. Two equal derivation inputs have probability at most `derivedKeyCollision C`.

`dealerAbort` proves `DealerAbort`. The top tree of `referenceTree` never fails, so the dealer gives
no bottom tree only when the randomizer search of bottom tree `b` fails.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCompletenessProof

section SeedGenHop

attribute [local instance] Classical.propDecidable

/-! ## The cells of the trees -/

section TreeCells

variable {C : Committee}

/-- An input of `H` that a tree of the dealer reads, namely an input of `Th` or of the PRF. -/
abbrev TreeCell := HashInput ⊕ (HashOutput × Point)

/-- The input of `H` of a tree cell. -/
def treeQuery : TreeCell → Query C
  | .inl x => .hash x
  | .inr p => .prf p.1 p.2

/-- The oracle of the tree cells. -/
abbrev TreeSpec := TreeCell →ₒ HashOutput

/-- A tree cell as one query of `H`. -/
def treeImpl : QueryImpl TreeSpec (OracleComp (RoSpec C)) := fun t => hashQuery (treeQuery t)

/-- A computation of leanVM on the tree cells. -/
def treeHash {α : Type} (oa : OracleComp HashSpec α) : OracleComp TreeSpec α :=
  simulateQ (fun input => OracleComp.lift (OracleSpec.query (spec := TreeSpec) (.inl input))) oa

/-- `F` on the tree cells. -/
def treeValue (seeds : C.Term → HashOutput) (p : Point) : OracleComp TreeSpec Digest := do
  let values ← C.terms.mapM fun T => truncateHash <$> OracleComp.lift
    (OracleSpec.query (spec := TreeSpec) (.inr (seeds T, p)))
  pure (values.foldl (· ^^^ ·) 0)

theorem treeImpl_treeHash {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ (treeImpl (C := C)) (treeHash oa) = tweakable oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [treeHash, tweakable]
  | query_bind input k ih =>
    simp only [treeHash, tweakable, simulateQ_bind, simulateQ_spec_query]
    congr 1
    funext answer
    exact ih answer

theorem treeImpl_treeValue (seeds : C.Term → HashOutput) (p : Point) :
    simulateQ (treeImpl (C := C)) (treeValue seeds p) = prfValue seeds p := by
  simp only [treeValue, prfValue, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_map, simulateQ_spec_query, simulateQ_pure, prf]
  rfl

theorem treeImpl_referenceTree (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree)
    (tree : Tree) :
    simulateQ (treeImpl (C := C)) (referenceTree treeHash (treeValue seeds) P top tree) =
      referenceTree tweakable (prfValue seeds) P top tree := by
  let hom : OracleComp TreeSpec →ᵐ OracleComp (RoSpec C) := simulateQ' treeImpl
  have h := SeedHitProof.hom_referenceTree hom treeHash (treeValue seeds) P top tree
  change simulateQ (treeImpl (C := C)) _ = referenceTree (fun oa => simulateQ (treeImpl (C := C)) (treeHash oa))
    (fun p => simulateQ (treeImpl (C := C)) (treeValue seeds p)) P top tree at h
  simpa only [treeImpl_treeHash, treeImpl_treeValue] using h

/-- The tree cells of a cache. -/
def treePart (s : HashCache C) : HashCache C :=
  QueryCache.ofFn fun q => if ∃ t, q = treeQuery t then s q else none

theorem treePart_apply (s : HashCache C) (q : Query C) :
    treePart s q = if ∃ t, q = treeQuery t then s q else none := rfl

variable (prims : Primitives)

theorem treePart_step (t : TreeCell) (s : HashCache C) :
    Prod.map id treePart <$> ((roImpl prims ∘ₛ treeImpl) t).run s =
      ((roImpl prims ∘ₛ treeImpl) t).run (treePart s) := by
  have e : (roImpl prims ∘ₛ treeImpl (C := C)) t = hashAnswer prims (treeQuery t) :=
    (simulateQ_query _ _).trans (id_map _)
  rw [e]
  have ht : ∃ t', treeQuery (C := C) t = treeQuery t' := ⟨t, rfl⟩
  by_cases hfix : IsFixed (treeQuery (C := C) t)
  · obtain ⟨input, hq, hm⟩ := hfix
    rw [hq, hashAnswer_of_isFixed prims hm]
    simp
  · rw [hashAnswer_of_not_isFixed prims hfix, OracleSpec.randomOracle]
    have hpart : treePart s (treeQuery t) = s (treeQuery t) := by simp only [treePart_apply, ht, ↓reduceIte]
    rcases hs : s (treeQuery t) with _ | u
    · rw [QueryImpl.withCaching_run_none _ hs, QueryImpl.withCaching_run_none _ (hpart.trans hs),
        Functor.map_map]
      congr 1
      funext u
      simp only [Prod.map, id]
      congr 1
      ext1 q
      by_cases hq : q = treeQuery t
      · subst hq
        simp only [treePart_apply, ht, ↓reduceIte, QueryCache.cacheQuery_self]
      · rw [treePart_apply, QueryCache.cacheQuery_of_ne _ _ hq, QueryCache.cacheQuery_of_ne _ _ hq,
          treePart_apply]
    · rw [QueryImpl.withCaching_run_some _ hs, QueryImpl.withCaching_run_some _ (hpart.trans hs)]
      simp

/-- A computation on the tree cells reads only the tree cells of the cache. -/
theorem run'_treePart {α : Type} (oa : OracleComp TreeSpec α) (s : HashCache C) :
    (simulateQ (roImpl prims) (simulateQ treeImpl oa)).run' s =
      (simulateQ (roImpl prims) (simulateQ treeImpl oa)).run' (treePart s) := by
  rw [← QueryImpl.simulateQ_compose]
  exact run'_simulateQ_eq_of_query_map_eq _ _ treePart (treePart_step prims) oa s

theorem treePart_cacheQuery (s : HashCache C) (q : Query C) (u : HashOutput) (hq : ∀ t, q ≠ treeQuery t) :
    treePart (s.cacheQuery q u) = treePart s := by
  ext1 q'
  by_cases e : q' = q
  · subst e
    have hn : ¬ ∃ t, q' = treeQuery t := fun ⟨t, e⟩ => hq t e
    simp only [treePart_apply, hn, ↓reduceIte]
  · rw [treePart_apply, treePart_apply, QueryCache.cacheQuery_of_ne _ _ e]

/-- `evalDist_fresh_mapM` with a continuation on the tree cells. -/
theorem evalDist_fresh_mapM_bind {β : Type} (qs : List (Query C)) :
    ∀ (k : List HashOutput → OracleComp TreeSpec β) (s : HashCache C), qs.Nodup → (∀ q ∈ qs, s q = none) →
      (∀ q ∈ qs, ¬ IsFixed q) → (∀ q ∈ qs, ∀ t, q ≠ treeQuery t) →
      (simulateQ (roImpl prims) (qs.mapM hashQuery >>= fun v => simulateQ treeImpl (k v))).run' s =ᵈ
        ((qs.mapM fun _ => $ᵗ HashOutput) >>= fun v =>
          (simulateQ (roImpl prims) (simulateQ treeImpl (k v))).run' s) := by
  induction qs with
  | nil => intro k s _ _ _ _; simp
  | cons q qs ih =>
    intro k s hnd hfresh hfix htree
    rw [List.nodup_cons] at hnd
    have hq : simulateQ (roImpl prims) (hashQuery q) = hashAnswer prims q :=
      (simulateQ_query _ _).trans (id_map _)
    have hne : ∀ q' ∈ qs, q' ≠ q := fun q' hq' e => hnd.1 (e ▸ hq')
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    rw [simulateQ_bind, hq, StateT.run'_eq, StateT.run_bind,
      hashAnswer_of_not_isFixed prims (hfix q (List.mem_cons_self ..)), OracleSpec.randomOracle,
      QueryImpl.withCaching_run_none _ (hfresh q (List.mem_cons_self ..)), bind_map_left, map_bind]
    refine EvalDistEq.bind_right _ fun u => ?_
    have h := ih (fun v => k (u :: v)) (s.cacheQuery q u) hnd.2 (fun q' hq' => by
        rw [QueryCache.cacheQuery_of_ne _ _ (hne q' hq')]
        exact hfresh q' (List.mem_cons_of_mem _ hq'))
      (fun q' hq' => hfix q' (List.mem_cons_of_mem _ hq')) (fun q' hq' => htree q' (List.mem_cons_of_mem _ hq'))
    have hframe : ∀ v, (simulateQ (roImpl prims) (simulateQ treeImpl (k (u :: v)))).run' (s.cacheQuery q u) =
        (simulateQ (roImpl prims) (simulateQ treeImpl (k (u :: v)))).run' s := fun v => by
      rw [run'_treePart prims _ (s.cacheQuery q u), run'_treePart prims _ s,
        treePart_cacheQuery s q u (htree q (List.mem_cons_self ..))]
    simp only [hframe] at h
    rw [StateT.run'_eq] at h
    exact h

end TreeCells

/-! ## The seed generation before a continuation -/

section SeedGenBind

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The keys of every operator from the values of the derivations. -/
def valueKeys (values : List HashOutput) : C.Party → Option (Keys C) := fun i => some (keysFromValues values i)

/-- The honest seed generation before a continuation `K` gives the keys from the derivations to `K`.
It is `evalDist_seedGen_derivations` with a continuation. -/
theorem evalDist_seedGen_bind {α : Type} (K : (C.Party → Option (Keys C)) → OracleComp (LocalSpec C) α) :
    (simulateQ (localAnswer prims) (honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds >>= K)).run' ∅ =ᵈ
      (simulateQ (localAnswer prims) (OverPermutation.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>=
        fun parts => seedGenDerivations parts >>= fun values => K (valueKeys values))).run' ∅ := by
  refine (((sameRun_seedGen (E := E) prims).bind fun keys => SameRun.refl prims (K keys)).run'_eq).trans ?_
  rw [bind_assoc]
  refine (evalDist_run'_bind_congr prims _ (fun parts => seedGenRest (E := E) parts >>= K)
    (fun parts => seedGenDerivations parts >>= fun _ => seedGenRest (E := E) parts >>= K) ∅
    fun p _ => (evalDist_run'_prepend prims (seedGenDerivations p.1) _ _).symm).trans ?_
  refine evalDist_run'_bind_congr prims _ _ _ ∅ fun p hp => ?_
  refine evalDist_run'_bind_congr prims (seedGenDerivations p.1) _ _ p.2 fun q hq => ?_
  have hp0 := (localRun_support _ ∅ p hp).2.1 noMpc_empty
  obtain ⟨_, hq0, hqv⟩ := localRun_support _ p.2 q hq
  have hout : ∀ z ∈ support ((simulateQ (localAnswer prims) (seedGenRest (E := E) p.1)).run q.2),
      z.1 = valueKeys q.1 := by
    intro z hz
    obtain ⟨hle, hz0, hzv⟩ := localRun_support _ q.2 z hz
    have hagree := agrees_hashOf prims (hz0 (hq0 hp0))
    have hk := hzv _ (good_hashOf prims z.2) hagree
    have hv := hqv _ (good_hashOf prims z.2) (hagree.mono hle)
    rw [simulateQ_fixedLocal_seedGenRest, support_pure, Set.mem_singleton_iff] at hk
    rw [simulateQ_fixedLocal_seedGenDerivations, support_pure, Set.mem_singleton_iff] at hv
    rw [hk, hv]
    funext i
    rw [valueKeys, keysFromValues_map]
  refine (evalDist_run'_bind_congr prims _ K (fun _ => K (valueKeys q.1)) q.2
    fun z hz => by rw [hout z hz]).trans ?_
  exact evalDist_run'_prepend prims _ _ _

end SeedGenBind

/-! ## The two games on the local oracles -/

section Games

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (b : Fin (2 ^ layerHeight))

/-- `free` of `liftComp`, as a monad map. -/
def freeHom : OracleComp (RoSpec C) →ᵐ OracleComp (WorldSpec C) where
  toFun _ oa := free (liftComp oa _)
  toFun_pure' _ := rfl
  toFun_bind' _ _ := by simp only [liftComp_bind, free_bind]

/-- The trees of `referenceDkg` on the tree cells, from the keys of the seed generation. -/
def gameTrees (keys : C.Party → Option (Keys C)) : OracleComp TreeSpec (SetupOutputs C) := do
  let top ← if ∀ i, (keys i).isSome then
      (TreeOutput.topTree <$> referenceTree treeHash (treeValue (gameSeeds noCoalition keys))
        (gameParameter noCoalition keys) emptyTop .top)
    else pure none
  let bottom ← match top with
    | some top =>
      (bottomOf <$> referenceTree treeHash (treeValue (gameSeeds noCoalition keys))
        (gameParameter noCoalition keys) top (.bottom b))
    | none => pure none
  pure fun i => (keys i, top, bottom)

/-- The trees of `dealerDkg` on the tree cells, from the result of `prawnsKeyGen`. -/
def dealerTrees (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) :
    OracleComp TreeSpec (SetupOutputs C) := do
  let output ← referenceTree treeHash (treeValue r.2.1) r.1 emptyTop .top
  match output with
  | some (.top top) => do
      let bottom ← bottomOf <$> referenceTree treeHash (treeValue r.2.1) r.1 top (.bottom b)
      pure fun i => (some (r.2.2 i), some top, bottom)
  | _ => pure fun _ => (none, none, none)

theorem freeHom_tree {α : Type} (oa : OracleComp TreeSpec α) :
    freeHom (simulateQ treeImpl oa) = free (liftComp (simulateQ (treeImpl (C := C)) oa) (LocalSpec C)) := rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem freeHom_referenceTree (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree) (tree : Tree) :
    free (liftComp (referenceTree tweakable (prfValue seeds) P top tree) (LocalSpec C)) =
      referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) (LocalSpec C)))
        (fun x => free (liftComp (prfValue seeds x) (LocalSpec C))) P top tree :=
  SeedHitProof.hom_referenceTree freeHom tweakable (prfValue seeds) P top tree

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem dealtWith_bottom (P : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → OracleComp (WorldSpec C) Digest) :
    (dealtWith (fun oa => free (liftComp oa (LocalSpec C))) P keys top value).bottom b =
      bottomOf <$> referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) (LocalSpec C))) value P top (.bottom b) := by
  simp only [dealtWith]
  congr 1

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem referenceDkg_eq :
    referenceDkg (E := E) b = free (honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
      honestRounds noFunctionality (fun l => l.elim) setupRounds >>= fun keys =>
        liftComp (simulateQ (treeImpl (C := C)) (gameTrees b keys)) (LocalSpec C)) := by
  unfold referenceDkg honestNet
  rw [free_bind, realExecution_honest]
  erw [bind_map_left]
  refine bind_congr fun keys => ?_
  change (do
    let top ← dealtTop keys
    let bottom ← dealtBottom keys b top
    pure fun i => (keys i, top, bottom)) = _
  unfold gameTrees dealtTop dealtBottom
  by_cases hall : ∀ i, (keys i).isSome
  · simp only [hall, implies_true, ↓reduceIte, simulateQ_bind, simulateQ_map, treeImpl_referenceTree,
      liftComp_bind, liftComp_map, bind_map_left, free]
    refine bind_congr fun o => ?_
    cases TreeOutput.topTree o <;> simp [treeImpl_referenceTree]
  · simp [hall]

private theorem dealerDkg_eq_trees :
    dealerDkg (C := C) b = free (liftComp prawnsKeyGen _ >>= fun r =>
      liftComp (simulateQ (treeImpl (C := C)) (dealerTrees b r)) (LocalSpec C)) := by
  unfold dealerDkg dealerKeyGen dealerKeyGenWith
  rw [free_bind]
  simp only [bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with ⟨P, seeds, keys⟩
  dsimp only
  rw [← freeHom_referenceTree]
  unfold dealerTrees
  simp only [simulateQ_bind, liftComp_bind, free_bind, treeImpl_referenceTree]
  refine bind_congr fun o => ?_
  rcases o with _ | (top | tree)
  · simp
  · simp only [pure_bind, dealtWith_bottom, ← freeHom_referenceTree]
    simp only [simulateQ_map, treeImpl_referenceTree, liftComp_map, free, bind_pure_comp]
    rfl
  · simp

end Games

/-! ## The keys of the dealer -/

section Dealt

variable {C : Committee} (prims : Primitives) (b : Fin (2 ^ layerHeight))

/-- The trees of the game on the dealt keys have the distribution of the trees of the dealer. -/
def GameTreesDealt : Prop :=
  ∀ (P : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput),
    (simulateQ (roImpl prims) (simulateQ (treeImpl (C := C))
        (gameTrees b fun i => some (dealtKeys P seeds pairKeys i)))).run' ∅ =ᵈ
      (simulateQ (roImpl prims) (simulateQ (treeImpl (C := C))
        (dealerTrees b (P, seeds, dealtKeys P seeds pairKeys)))).run' ∅

theorem gameTreesDealt : GameTreesDealt (C := C) prims b := by
  intro P seeds pairKeys
  unfold gameTrees dealerTrees
  simp only [Option.isSome_some, implies_true, ↓reduceIte, gameSeeds_dealt, gameParameter_dealt,
    simulateQ_bind, treeImpl_referenceTree, bind_map_left]
  rw [← simulateQ_bind, ← simulateQ_bind, StateT.run'_eq, StateT.run'_eq]
  change Prod.fst <$> roRun prims _ ∅ =ᵈ Prod.fst <$> roRun prims _ ∅
  rw [← localRun_liftComp, ← localRun_liftComp, ← StateT.run'_eq, ← StateT.run'_eq, liftComp_bind, liftComp_bind]
  generalize hA : referenceTree tweakable (prfValue seeds) P emptyTop .top = A
  refine evalDist_run'_bind_congr prims _ _ _ ∅ fun p hp => ?_
  obtain ⟨-, -, h, -, -, hd⟩ := localRun_D_one prims A ∅ noMpc_empty p hp
  obtain ⟨top, htop, -, -⟩ := D_refTop (prims := prims) (h := h) P seeds emptyTop
  rw [hA] at htop
  rw [hd.trans htop]
  exact EvalDistEq.rfl

/-- `prawnsKeyGen` before a continuation, with its three samples. -/
theorem prawnsKeyGen_bind {α : Type} (f : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) → ProbComp α) :
    prawnsKeyGen >>= f = ($ᵗ PublicParameter >>= fun P => $ᵗ (C.Term → HashOutput) >>= fun seeds =>
      $ᵗ (C.Pair → HashOutput) >>= fun pairKeys => f (P, seeds, dealtKeys P seeds pairKeys)) := by
  simp only [prawnsKeyGen, bind_assoc, pure_bind]

/-- The trees of the game on the keys of the derivations of `parts`. -/
def realBranch (parts : C.Party → Parts C) : ProbComp (SetupOutputs C) :=
  (simulateQ (roImpl prims) ((seedGenInputs parts).mapM hashQuery >>= fun values =>
    simulateQ treeImpl (gameTrees b (valueKeys (C := C) values)))).run' ∅

/-- `prawnsKeyGen` and the trees of the dealer. -/
def dealerBranch : ProbComp (SetupOutputs C) :=
  prawnsKeyGen >>= fun r => (simulateQ (roImpl prims) (simulateQ (treeImpl (C := C)) (dealerTrees b r))).run' ∅

/-- With distinct derivation inputs, the game trees on the derived keys are the dealer. -/
theorem realBranch_eq (parts : C.Party → Parts C) (hnd : (seedGenInputs parts).Nodup) :
    realBranch prims b parts =ᵈ dealerBranch prims b := by
  have hfix : ∀ q ∈ seedGenInputs parts, ¬ IsFixed q := fun q hq => by
    simp only [seedGenInputs, List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | ⟨T, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rintro ⟨_, h, _⟩ <;> cases h
  have htree : ∀ q ∈ seedGenInputs parts, ∀ t, q ≠ treeQuery t := fun q hq t => by
    simp only [seedGenInputs, List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | ⟨T, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rcases t with _ | _ <;> intro h <;> cases h
  set X := fun keys : C.Party → Option (Keys C) =>
    (simulateQ (roImpl prims) (simulateQ (treeImpl (C := C)) (gameTrees b keys))).run' ∅ with hX
  have step1 : realBranch prims b parts =ᵈ
      ((seedGenInputs parts).mapM (fun _ => $ᵗ HashOutput) >>= fun values => X (valueKeys values)) :=
    evalDist_fresh_mapM_bind prims _ (fun values => gameTrees b (valueKeys values)) ∅ hnd
      (fun _ _ => rfl) hfix htree
  have step2 : ((seedGenInputs parts).mapM (fun _ => $ᵗ HashOutput) >>= fun values => X (valueKeys values)) =ᵈ
      (prawnsKeyGen >>= fun r => X (fun i => some (r.2.2 i))) := by
    refine (EvalDistEq.of_eq (bind_map_left valueKeys _ X).symm).trans ?_
    exact ((evalDist_keysFromValues parts).bind_left X).trans (EvalDistEq.of_eq (bind_map_left _ _ X))
  have step3 : (prawnsKeyGen >>= fun r => X (fun i => some (r.2.2 i))) =ᵈ dealerBranch prims b := by
    unfold dealerBranch
    rw [prawnsKeyGen_bind, prawnsKeyGen_bind]
    exact EvalDistEq.bind_right _ fun P => EvalDistEq.bind_right _ fun seeds =>
      EvalDistEq.bind_right _ fun pairKeys => gameTreesDealt prims b P seeds pairKeys
  exact step1.trans (step2.trans step3)

end Dealt

/-! ## The hop -/

section Hop

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives)
  (b : Fin (2 ^ layerHeight))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `referenceDkg` on the local oracles samples the parts and then runs `realBranch`. -/
private theorem referenceDkg_branch :
    Prod.fst <$> runWorld prims (referenceDkg (E := E) b) =ᵈ
      (OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C)) >>= realBranch prims b) := by
  rw [referenceDkg_eq]
  refine (EvalDistEq.of_eq ((fst_map_runWorld prims _).trans (by rw [simulateQ_free]))).trans
    ((evalDist_seedGen_bind (E := E) prims _).trans ?_)
  rw [← liftComp_sequenceFin, run'_localAnswer_liftComp_bind]
  refine EvalDistEq.of_eq (bind_congr fun parts => ?_)
  rw [seedGenDerivations, ← liftComp_bind, simulateQ_localAnswer_liftComp]
  rfl

/-- `dealerDkg` on the local oracles is `dealerBranch`. -/
theorem dealerDkg_local : Prod.fst <$> runWorld prims (dealerDkg (C := C) b) = dealerBranch prims b := by
  rw [dealerDkg_eq_trees]
  refine (fst_map_runWorld prims _).trans ?_
  rw [simulateQ_free, run'_localAnswer_liftComp_bind]
  refine bind_congr fun r => ?_
  rw [simulateQ_localAnswer_liftComp]
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `SeedGenHop` holds. -/
theorem seedGenHop : SeedGenHop (C := C) (E := E) := by
  intro prims b
  let : MeasurableSpace (SetupOutputs C) := ⊤
  have hreal := referenceDkg_branch (C := C) (E := E) prims b
  have hideal : Prod.fst <$> runWorld prims (dealerDkg (C := C) b) =ᵈ
      (OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C)) >>= fun _ => dealerBranch prims b) :=
    (EvalDistEq.of_eq (dealerDkg_local prims b)).trans (OracleComp.EvalDistEq.bind_const _ _).symm
  have hbound := probEvent_seedGen_collision (C := C)
  rw [Fintype.card_bitVec] at hbound
  calc measureTVDist _ _ = measureTVDist
        (OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C)) >>= realBranch prims b)
        (OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C)) >>= fun _ => dealerBranch prims b) := by
        unfold measureTVDist
        rw [hreal.evalDist_eq, hideal.evalDist_eq]
    _ ≤ (Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          ¬ (seedGenInputs parts).Nodup]).toReal :=
        measureTVDist_bind_left_le_prEvent_of_evalDistEq _ _ _ _
          fun parts hnd => realBranch_eq prims b parts (not_not.mp hnd)
    _ ≤ ((((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ≥0∞) *
          ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by simp)) hbound
    _ = ((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]
        norm_num
    _ ≤ derivedKeyCollision C := by
        unfold derivedKeyCollision termCount
        gcongr
        · rw [card_term]
        · exact card_pair_le C

end Hop

end SeedGenHop

section DealerAbort

variable {C : Committee}

/-- `dealerDkg` on the random oracles, for the parameter, the seeds and the keys of `prawnsKeyGen`. -/
def dealerRo (parameter : PublicParameter) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C)
    (b : Fin (2 ^ layerHeight)) : OracleComp (RoSpec C) (SetupOutputs C) := do
  let some (.top top) ← referenceTree tweakable (prfValue seeds) parameter emptyTop .top
    | pure fun _ => (none, none, none)
  let output ← referenceTree tweakable (prfValue seeds) parameter top (.bottom b)
  pure fun i => (some (keys i), some top, (fun | some (.bottom tree) => some tree | _ => none) output)

/-- `dealerDkg` samples by `prawnsKeyGen` and then runs `dealerRo` on the free copy. -/
theorem dealerDkg_eq (b : Fin (2 ^ layerHeight)) :
    dealerDkg (C := C) b = free (liftComp prawnsKeyGen _) >>= fun x => φ (dealerRo x.1 x.2.1 x.2.2 b) := by
  unfold dealerDkg dealerKeyGen dealerKeyGenWith
  rw [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨parameter, seeds, keys⟩
  simp only [dealerRo, referenceTree_φ, bind_assoc, φ_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp [φ_pure]
  swap
  · simp [φ_pure]
  simp only [pure_bind, dealtWith, referenceTree_φ, φ_bind, bind_map_left, φ_pure]
  refine bind_congr fun output => ?_
  rcases output with _ | (_ | _) <;> rfl

/-- The outputs of `dealerDkg` in the world are the outputs of `dealerRo` from the empty cache. -/
theorem fst_runWorld_dealerDkg (prims : Primitives) (b : Fin (2 ^ layerHeight)) :
    Prod.fst <$> runWorld prims (dealerDkg (C := C) b) =
      prawnsKeyGen >>= fun x => Prod.fst <$> roRun prims (dealerRo x.1 x.2.1 x.2.2 b) ∅ := by
  rw [dealerDkg_eq, runWorld, simulateQ_bind]
  simp only [WriterT.run_bind, StateT.run'_eq, StateT.run_bind, world_sample_run]
  have hw : ∀ x : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C),
      (WriterT.run (simulateQ (world prims) (φ (dealerRo x.1 x.2.1 x.2.2 b)))).run ∅ =
        (fun p => ((p.1, (1 : Multiplicative ℕ)), p.2)) <$> roRun prims (dealerRo x.1 x.2.1 x.2.2 b) ∅ :=
    fun x => world_lift_run prims _ ∅
  simp only [StateT.run_map, bind_map_left, hw, map_bind, Functor.map_map]
  erw [map_bind]
  refine bind_congr (m := ProbComp) fun x => ?_
  exact Functor.map_map _ _ _

/-- `dealerRo` gives `none` to an operator only when the randomizer search of bottom tree `b` fails. -/
theorem dealerRo_fail (prims : Primitives) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (keys : C.Party → Keys C) (b : Fin (2 ^ layerHeight)) :
    Pr{let z ← roRun prims (dealerRo parameter seeds keys b) ∅}[∃ i,
        (z.1 i).1 = none ∨ (z.1 i).2.1 = none ∨ (z.1 i).2.2 = none] ≤
      (1 - codewordP) ^ randomizerAttemptLimit := by
  unfold dealerRo
  refine step prims _ _ _ ∅ _ noMpc_empty fun r1 s1 hle1 hn1 hd1 hp1 => ?_
  have hm1 := hp1 IsMsg (Pres_refTop prims IsMsg (fun _ h => h) seeds parameter emptyTop) (noB_empty _)
  obtain ⟨h0, hg0, ha0⟩ := exists_good prims s1 hn1
  obtain ⟨top, htop, -, -⟩ := D_refTop (prims := prims) (h := h0) parameter seeds emptyTop
  have hr1 : r1 = some (.top top) := (hd1 h0 hg0 ha0).trans htop
  have htopf : ∀ h, Good prims h → Agrees h s1 → TopFacts prims h seeds parameter top := by
    intro h hg ha
    obtain ⟨top', htop', hc', hr'⟩ := D_refTop (prims := prims) (h := h) parameter seeds emptyTop
    have : some (TreeOutput.top top') = some (.top top) := htop'.symm.trans ((hd1 h hg ha).symm.trans hr1)
    cases this
    exact ⟨hc', hr'⟩
  subst hr1
  dsimp only
  refine (step_add prims _ _ _ (fun r => r = none) s1 0 hn1
    fun r2 s2 hr2 hle2 hn2 hd2 hp2 => ?_).trans
    (by rw [add_zero]; exact refBottom_fail prims seeds parameter top b s1 hn1 hm1 htopf)
  obtain ⟨h0, hg0, ha0⟩ := exists_good prims s2 hn2
  obtain ⟨hc0, hrt0⟩ := htopf h0 hg0 (ha0.mono hle2)
  rcases D_refBottom (prims := prims) (h := h0) parameter seeds top hc0 hrt0 b with hb | ⟨tree, hb, -⟩
  · exact absurd ((hd2 h0 hg0 ha0).trans hb) hr2
  have hr2' : r2 = some (.bottom tree) := (hd2 h0 hg0 ha0).trans hb
  subst hr2'
  rw [roRun_pure]
  simp

/-- `DealerAbort` holds. The top tree never fails, and bottom tree `b` fails with probability at most
`searchFailure`. -/
theorem dealerAbort : DealerAbort (C := C) := by
  intro prims b
  have hfin : (1 - codewordP) ^ randomizerAttemptLimit ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  rw [← toReal_failure]
  refine ENNReal.toReal_mono hfin ?_
  have h1 : Pr{let r ← runWorld prims (dealerDkg (C := C) b)}[∃ i,
        (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none] =
      Pr{let r ← Prod.fst <$> runWorld prims (dealerDkg (C := C) b)}[∃ i,
        (r i).1 = none ∨ (r i).2.1 = none ∨ (r i).2.2 = none] := by
    rw [prEvent_map]
  rw [h1, fst_runWorld_dealerDkg]
  refine pr_bind_le fun x _ => ?_
  rw [prEvent_map]
  exact dealerRo_fail prims _ _ _ b

end DealerAbort

/-- info: 'ThresholdLeanXmssSecurity.DkgCompletenessProof.seedGenHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedGenHop

/-- info: 'ThresholdLeanXmssSecurity.DkgCompletenessProof.dealerAbort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerAbort

end ThresholdLeanXmssSecurity.DkgCompletenessProof
