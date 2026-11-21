import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Dealer
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Forger
import ThresholdLeanXmssSecurity.Proof.SeedGenGames
import ThresholdLeanXmssSecurity.Proof.Pilot.StreamTables
import ThresholdLeanXmssSecurity.Proof.BuildingBlocks
import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.SeedGen

/-!
# The dealer moves to the start of `dealtGame`

`dealerFirstGame` is `dealtGame` with each run emulated, where the keys of the dealer are sampled
first and the top tree of the dealer is computed right after them. `dealtGame` computes that top
tree at the start of its first emulated run. `dealerFirst_eq` shows that the two games have the same
law, by lazy sampling (`worldRun_safe_swap`) and a replay of the top tree.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## No programming query outside the setup domains -/

theorem noOuter_free {α : Type} (oa : OracleComp (LocalSpec C) α) : AllQueriesSatisfy (free oa) NoOuterProgram :=
  AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) oa)
    fun t _ => (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inr t) _).2 trivial

theorem noOuter_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    AllQueriesSatisfy (worldRoles.adversary oa) NoOuterProgram := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [worldRoles, counted]
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp [worldRoles, counted]
    rw [e, adversary_query]
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inl t)) _).2 trivial) ih

theorem worldRoles_adversary_eq {α : Type} (oa : OracleComp (LocalSpec C) α) :
    worldRoles.adversary oa =
      simulateQ (fun t => worldRoles.adversary (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [worldRoles, counted]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map, ← ih]
    change counted (liftComp (liftM (OracleSpec.query t) >>= k) (SimulatorSpec C)) = _
    rw [liftComp_bind, counted_bind]
    rfl

theorem free_eq {α : Type} (oa : OracleComp (LocalSpec C) α) :
    free oa = simulateQ (fun t => free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map, ← ih, free_bind]

/-- The handler of `worldRoles` on the two copies of the local oracles. -/
def worldSplit : QueryImpl (LocalSpec C + LocalSpec C) (OracleComp (WorldSpec C)) := fun t =>
  match t with
  | .inl t => worldRoles.adversary (OracleComp.lift (OracleSpec.query t))
  | .inr t => free (OracleComp.lift (OracleSpec.query t))

theorem worldRoles_eq : worldRoles (C := C) = mapRoles worldSplit splitRoles := by
  unfold mapRoles splitRoles
  rcases h : (worldRoles (C := C)) with ⟨adv, hon⟩
  congr 1 <;> funext β oa
  · rw [← show worldRoles.adversary oa = adv oa by rw [h]]
    rw [worldRoles_adversary_eq]
    exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by simp [worldSplit]) oa).symm
  · rw [← show worldRoles.honest oa = hon oa by rw [h]]
    change free oa = _
    rw [free_eq]
    exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by simp [worldSplit]) oa).symm

theorem noOuter_worldSplit {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) :
    AllQueriesSatisfy (simulateQ worldSplit p) NoOuterProgram := by
  refine AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) p)
    fun t _ => ?_
  rcases t with t | t
  · exact noOuter_adversary _
  · exact noOuter_free _

section Network

variable {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

theorem noOuter_startSteps (program : C.Party → PartyM C E (CallSpec I O) α) :
    AllQueriesSatisfy (startSteps worldRoles D program) NoOuterProgram := by
  rw [worldRoles_eq, ← simulateQ_startSteps]
  exact noOuter_worldSplit _

theorem noOuter_stepRound (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    AllQueriesSatisfy (stepRound worldRoles D A F state steps) NoOuterProgram := by
  rw [worldRoles_eq, ← simulateQ_stepRound_mapRoles]
  exact noOuter_worldSplit _

theorem noOuter_executeRounds (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    AllQueriesSatisfy (executeRounds worldRoles D A F fuel state steps) NoOuterProgram := by
  rw [worldRoles_eq, ← simulateQ_executeRounds_mapRoles]
  exact noOuter_worldSplit _

end Network

theorem noOuter_of_map {α β : Type} (f : α → β) {oa : OracleComp (WorldSpec C) α}
    (h : AllQueriesSatisfy (f <$> oa) NoOuterProgram) : AllQueriesSatisfy oa NoOuterProgram :=
  (allQueriesSatisfy_def _ _).2 ((isQueryBound_map_iff _ _ _ _ _).1 h)

theorem noOuter_observedStepRound (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    {α : Type} (steps : C.Party → Step C E RealSpec α) :
    AllQueriesSatisfy (stepRound observedRoles D A noFunctionality state steps).run NoOuterProgram := by
  refine noOuter_of_map Prod.fst ?_
  change AllQueriesSatisfy (seedGenEraseLog _) _
  rw [seedGenEraseLog_stepRound]
  exact noOuter_stepRound D A _ state steps

theorem noOuter_observedExecuteRounds (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ)
    (state : A.State) {α : Type} (steps : C.Party → Step C E RealSpec α) :
    AllQueriesSatisfy (executeRounds observedRoles D A noFunctionality fuel state steps).run NoOuterProgram := by
  refine noOuter_of_map Prod.fst ?_
  change AllQueriesSatisfy (seedGenEraseLog _) _
  rw [seedGenEraseLog_executeRounds]
  exact noOuter_executeRounds D A _ fuel state steps

theorem noOuter_observe {α : Type} (oa : OracleComp (LocalSpec C) α) :
    AllQueriesSatisfy (observe oa) NoOuterProgram := by
  refine noOuter_of_map Prod.fst ?_
  rw [fst_observe]
  exact noOuter_adversary oa

/-! ## The replay of a computation of `H` and `PRG` -/

/-- A computation of `H` and `PRG` on the free copy, in the world with no count. -/
theorem baseAnswer_freeLift (prims : Primitives) {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (baseAnswer prims) (free (liftComp oa (LocalSpec C))) =
      simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, free_bind, simulateQ_bind, simulateQ_bind, ← funext ih]
    congr 1

/-- A free computation of `H` outside the setup domains, run two times, is one run. -/
theorem worldRun_freeLift_dup (prims : Primitives) (D : C.Coalition) {α β : Type} (oa : OracleComp (RoSpec C) α)
    (hsafe : AllQueriesSatisfy (free (liftComp oa (LocalSpec C))) WorldSafe) (k : α → OracleComp (WorldSpec C) β) :
    WorldRun (streamWorld prims D) (do let _ ← free (liftComp oa (LocalSpec C)); free (liftComp oa (LocalSpec C)) >>= k)
      (free (liftComp oa (LocalSpec C)) >>= k) := by
  rintro ⟨c, h⟩
  simp only [simulateQ_bind, StateT.run_bind]
  rw [streamWorld_safe hsafe, baseAnswer_freeLift, bind_map_left, bind_map_left]
  refine OracleComp.EvalDistEq.bind_congr_of_support
    ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) oa).run c) fun z hz => ?_
  rw [streamWorld_safe hsafe, baseAnswer_freeLift,
    replay_simulateQ (grows_roAnswer prims) (replays_roAnswer prims) oa c z hz z.2 le_rfl]
  simp

/-! ## The games -/

/-- `worldSeedGen` after the start of `A` and the keys of the dealer. -/
def seedGenTail (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (early : CallLog C)
    (parameter : PublicParameter) (dealt : C.Party → Keys C) [Field E] [Algebra Bit E] :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) := do
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let ((state, steps, sent), calls) ← (stepRound observedRoles D net noFunctionality state steps).run
  let log := early ++ calls
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let view := fun (i j : C.Party) =>
    if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
  let high ← free (liftComp ($ᵗ HashOutput) _)
  let _ ← program (.derive .seedGen .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
    (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      program (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
        (view (firstHonest (C.holders T)) k).term T)) ((dealt j).seed T)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]) ((dealt j).pairKey i)
    else pure true
  let ((state, keys), _) ← (executeRounds observedRoles D net noFunctionality (setupRounds - 1) state steps).run
  pure (state, keys)

variable [Field E] [Algebra Bit E]

theorem worldSeedGen_eq (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    worldSeedGen D net = (do
      let (state, early) ← observe (net.start (corruptInputs D fun _ => ()) [])
      let (parameter, seeds, dealt) ← free (liftComp (prawnsKeyGen (C := C)) _)
      let (state, keys) ← seedGenTail D net state early parameter dealt
      pure (state, parameter, seeds, dealt, keys)) := by
  simp only [worldSeedGen, seedGenTail, bind_assoc, pure_bind]
  rfl

theorem noOuter_program {q : Query C} (hq : isSetupQuery q = true) (value : HashOutput) :
    AllQueriesSatisfy (program q value) NoOuterProgram :=
  AllQueriesSatisfy.simulateQ (P := fun t => ∀ x, t = .inr x → isSetupQuery x.1 = true)
    ((allQueriesSatisfy_query_iff (spec := SimulatorSpec C) (.inr (q, value)) _).2
      fun x hx => by cases hx; exact hq)
    fun t ht => by
      rcases t with t | x
      · exact (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inl t)) _).2 trivial
      · exact (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inr x)) _).2 (ht x rfl)

theorem noOuter_seedGenTail (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) :
    AllQueriesSatisfy (seedGenTail D net state early parameter dealt) NoOuterProgram := by
  unfold seedGenTail
  refine allQueriesSatisfy_bind (noOuter_free _) fun parts => ?_
  refine allQueriesSatisfy_bind (noOuter_startSteps D _) fun steps => ?_
  refine allQueriesSatisfy_bind (noOuter_observedStepRound D net state steps) fun r => ?_
  obtain ⟨⟨state', steps', sent⟩, calls⟩ := r
  refine allQueriesSatisfy_bind (noOuter_free _) fun high => ?_
  refine allQueriesSatisfy_bind (noOuter_program rfl _) fun _ => ?_
  refine allQueriesSatisfy_bind (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun T => ?_) _) fun _ => ?_
  · split
    · exact noOuter_program rfl _
    · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun j => DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun i => ?_) _) _) fun _ => ?_
  · split
    · exact noOuter_program rfl _
    · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (noOuter_observedExecuteRounds D net _ _ _) fun r => ?_
  exact allQueriesSatisfy_pure _ _

/-- `realLift` as a monad map. -/
def realLiftHom (σ : Type) : OracleComp (RoSpec C) →ᵐ RealM C σ where
  toFun _ oa := realLift oa
  toFun_pure' a := by ext; simp [realLift]
  toFun_bind' _ _ := by ext; simp [realLift, free_bind]

/-- The top tree of the dealer on the free copy. -/
@[irreducible] def dealerTop (parameter : PublicParameter) (seeds : C.Term → HashOutput) : OracleComp (WorldSpec C) (Option TreeOutput) :=
  free (liftComp (referenceTree (fun oa => tweakable oa) (prfValue seeds) parameter emptyTop .top) (LocalSpec C))

theorem worldDealer_run {σ : Type} (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (s : RealState C σ) :
    (worldDealer (σ := σ) parameter seeds dealt).run s =
      (fun output => (dealtWith (m := RealM C σ) realLift parameter dealt ((TreeOutput.topTree output).getD emptyTop)
        (fun x => realLift (prfValue seeds x)), s)) <$> dealerTop parameter seeds := by
  unfold worldDealer dealerTop
  dsimp only
  have e := SeedHitProof.hom_referenceTree (realLiftHom (C := C) σ) (fun oa => tweakable oa) (prfValue seeds)
    parameter emptyTop .top
  change _ = referenceTree (m := RealM C σ) (fun oa => realLift (tweakable oa)) (fun x => realLift (prfValue seeds x))
    parameter emptyTop .top at e
  rw [← e]
  simp [realLiftHom, realLift, StateT.run_lift]

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (runLimit : ℕ)

/-- With a positive run limit and each run emulated, the rest of `dealtGame` starts with the top
tree of the dealer. -/
theorem secRest_start (hrun : 0 < runLimit) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (state : A.net.State) :
    ∃ k : Option TreeOutput → OracleComp (WorldSpec C) Bool,
      (secRest K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A parameter seeds dealt emu).run'
        (startState D state fun i => (emu i).map fun _ => dealt i) = dealerTop parameter seeds >>= k := by
  obtain ⟨n, rfl⟩ : ∃ n, runLimit = n + 1 := ⟨runLimit - 1, by omega⟩
  obtain ⟨i, hi⟩ := exists_honest D
  have hmay : mayRun (n + 1) D (startState D state fun i => (emu i).map fun _ => dealt i) .top :=
    ⟨by simp [startState], i, hi, rfl⟩
  have hlt : (startState D state fun i => (emu i).map fun _ => dealt i).runs .top < n + 1 := by
    simp [startState]
  simp only [secRest, secRuns, StateT.run'_eq, StateT.run_bind, StateT.run_get, pure_bind, hmay, ite_true,
    secRun, hlt, worldDealer_run, bind_map_left, bind_assoc, map_bind]
  exact ⟨_, rfl⟩

theorem dealerTop_safe (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    AllQueriesSatisfy (dealerTop parameter seeds) WorldSafe := by
  unfold dealerTop
  rw [DkgCompletenessProof.freeHom_referenceTree]
  generalize Tree.top = tree
  exact referenceTree_safe freeLift_safe (fun x => freeLift_safe _ (prfValue_safe seeds x)) _ _ _

/-- The top tree of the dealer, run two times, is one run. -/
theorem worldRun_dealerTop_dup (prims : Primitives) (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) {β : Type} (k : Option TreeOutput → OracleComp (WorldSpec C) β) :
    WorldRun (streamWorld prims D) (do let _ ← dealerTop parameter seeds; dealerTop parameter seeds >>= k)
      (dealerTop parameter seeds >>= k) := by
  have h := dealerTop_safe parameter seeds
  unfold dealerTop at h ⊢
  generalize Tree.top = tree at h ⊢
  exact worldRun_freeLift_dup prims D _ h k

/-- The keys of the honest operators in `dealtGame`. -/
def keysOf (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) : C.Party → Option (Keys C) :=
  fun i => (emu i).map fun _ => dealt i

/-- The rest of `dealtGame` after the start of `A` and the keys of the dealer. -/
def dealtTail (D : C.Coalition) (A : DkgTsigAdversary C E) (o : A.net.State × CallLog C)
    (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) : OracleComp (WorldSpec C) Bool :=
  seedGenTail D A.net o.1 o.2 r.1 r.2.2 >>= fun te =>
    (secRest K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A r.1 r.2.1 r.2.2 te.2).run'
      (startState D te.1 (keysOf r.2.2 te.2))

/-- `dealtGame` with each run emulated, with the keys and the top tree of the dealer first. -/
def dealerFirstGame (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool := do
  let r ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
  let _ ← dealerTop r.1 r.2.1
  let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
  dealtTail K circuits settings runLimit D A o r

theorem dealtGame_eq (D : C.Coalition) (A : DkgTsigAdversary C E) :
    dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A = (do
      let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
      let r ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      dealtTail K circuits settings runLimit D A o r) := by
  simp only [dealtGame, dealtRun, worldSeedGen_eq, dealtTail, map_bind, bind_assoc, pure_bind, map_pure,
    bind_pure]
  rfl

variable (prims : Primitives)

theorem noOuter_observeTail (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) :
    AllQueriesSatisfy (do
      let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
      seedGenTail D A.net o.1 o.2 parameter dealt) NoOuterProgram :=
  allQueriesSatisfy_bind (noOuter_observe _) fun o => noOuter_seedGenTail D A.net o.1 o.2 parameter dealt

/-- The move of the dealer to the start, for a positive run limit. -/
theorem dealerFirst_worldRun (hrun : 0 < runLimit) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    WorldRun (streamWorld prims D) (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A)
      (dealerFirstGame K circuits settings runLimit D A) := by
  rw [dealtGame_eq]
  refine WorldRun.trans (fun s => (worldRun_safe_swap prims D (sample_safe _)
    (noOuter_observe (A.net.start (corruptInputs D fun _ => ()) [])) _ s).symm) ?_
  refine WorldRun.bind_right _ _ fun r => ?_
  obtain ⟨parameter, seeds, dealt⟩ := r
  have hY := noOuter_observeTail D A parameter dealt
  have hT : AllQueriesSatisfy (dealerTop (C := C) parameter seeds) WorldSafe := dealerTop_safe parameter seeds
  have hk : ∀ te : A.net.State × (C.Party → Option (Keys C)), ∃ k : Option TreeOutput → OracleComp (WorldSpec C) Bool,
      (secRest K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A parameter seeds dealt te.2).run'
        (startState D te.1 (keysOf dealt te.2)) = dealerTop parameter seeds >>= k :=
    fun te => secRest_start K circuits settings runLimit hrun D A parameter seeds dealt te.2 te.1
  choose k hk using hk
  have eL : (do
      let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
      dealtTail K circuits settings runLimit D A o (parameter, seeds, dealt)) =
      (do
        let te ← (do
          let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
          seedGenTail D A.net o.1 o.2 parameter dealt)
        let a ← dealerTop parameter seeds
        k te a) := by
    simp only [dealtTail, hk, bind_assoc]
  show WorldRun _ _ (do
      let _ ← dealerTop parameter seeds
      let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
      dealtTail K circuits settings runLimit D A o (parameter, seeds, dealt))
  rw [eL]
  have hswap := worldRun_safe_swap prims D hT hY (fun a te => k te a)
  exact WorldRun.trans (fun s => (hswap s).symm)
    (WorldRun.trans (fun s => (worldRun_dealerTop_dup prims D parameter seeds _ s).symm)
      (WorldRun.bind_right _ _ fun _ => hswap))

/-- `dealtGame` with each run emulated and `dealerFirstGame` win with the same probability, for a
positive run limit. -/
theorem dealerFirst_eq (hrun : 0 < runLimit) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) =
      streamAccepts prims D (dealerFirstGame K circuits settings runLimit D A) := by
  unfold streamAccepts
  rw [((dealerFirst_worldRun K circuits settings runLimit prims hrun D A) (∅, ∅)).prEvent_eq]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dealerFirst_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dealerFirst_eq
