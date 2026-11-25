import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Start

/-!
# The proof of `SharedEnd`

An emulated recorded program with its record dropped is `emulatedProgram` with the shifted building
blocks (`dropRec_passTree_shifted`). Then each piece of the rest of `sharedDealt` erases to the piece
of `dealtRun`, in each mode.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The emulated recorded program with its record dropped -/

omit [Fintype E] [DecidableEq E] in
theorem dropRecS_passRun_shifted (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    dropRecS (passRun K circuits settings (shiftedShares circuits D parameter seeds openings) i keys jobs) =
      ceremonyRun K circuits settings (shiftedBuildingBlocks K circuits settings D parameter seeds openings) i keys
        jobs := by
  unfold passRun ceremonyRun
  rw [MonadHom.mmap_bind, dropRecS_liftS]
  simp only [monadHom_batched]
  refine bind_congr fun prss => ?_
  congr 1
  funext js
  unfold passBatch passCheckOpen shiftedShares
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_get, dropRecS_set, dropRecS_liftS, dropRecS_record,
    pure_bind]
  refine StateT.ext fun st => ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    StateT.run_pure]
  refine bind_congr fun inputs => ?_
  rw [runJobs_eq, StateT.run_bind, foldlM_layerBody_eq, StateT.run_map, bind_map_left, bind_assoc]
  refine bind_congr fun r => ?_
  simp only [tailBody, StateT.run_bind, bind_assoc]
  refine bind_congr fun x => ?_
  refine bind_congr fun y => ?_
  have hopen : ∀ (ctx : Context C) (v : Shares C Bit) (count : ℕ), openRep (G := RealSpec) K ctx v count =
      oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (v T)))) >>= fun digests =>
        exchange (repOutbox (E := E) K ctx.self v count digests) >>= fun inbox => repRest K ctx.self v count inbox := by
    intro ctx v count
    change openRep K (localContext ctx.self) v count = _
    rw [openRep_eq]
    rfl
  simp only [shiftedBuildingBlocks, StateT.run_bind, StateT.run_lift, hopen, bind_assoc, pure_bind, StateT.run_pure]

omit [Fintype E] [DecidableEq E] in
/-- The bottom branch with a given randomizer only composes its hash computations and its batch
interface. -/
theorem monadHom_bottomOutputWith {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (h : m →ᵐ n) (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (parameter : PublicParameter)
    (run : List Job → m (Option (List (List Bit)))) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (randomizer : Randomizer) :
    h (bottomOutputWith lift parameter run top b randomizer) =
      bottomOutputWith (fun oa => h (lift oa)) parameter (fun js => h (run js)) top b randomizer := by
  simp only [bottomOutputWith, MonadHom.mmap_bind]
  congr 1
  funext out
  cases out with
  | none => exact h.toFun_pure' _
  | some outputs =>
    simp only [MonadHom.mmap_bind]
    congr 1
    funext root
    congr 1
    funext digest
    cases Codeword.decode digest with
    | none => exact h.toFun_pure' _
    | some encoding =>
      simp only [MonadHom.mmap_bind]
      congr 1
      funext values
      cases values with
      | none => exact h.toFun_pure' _
      | some vals =>
        simp only [MonadHom.mmap_bind]
        congr 1
        funext path
        congr 1
        funext topRoot
        split <;> exact h.toFun_pure' _

omit [Fintype E] [DecidableEq E] in
/-- An emulated recorded program with its record dropped is `emulatedProgram` with the shifted
building blocks. -/
theorem dropRec_passTree_shifted (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (randomizer : Randomizer) (i : C.Party) (operator : OperatorState C)
    (tree : Tree) :
    dropRec (passTree K circuits settings (shiftedShares circuits D parameter seeds openings) (some randomizer) i
        operator tree) =
      emulatedProgram K circuits settings (shiftedBuildingBlocks K circuits settings D parameter seeds openings)
        randomizer i operator tree := by
  cases tree with
  | top =>
    unfold passTree emulatedProgram newTreeWith
    rcases operator.keys with _ | keys
    · exact dropRec_failure
    · rw [MonadHom.mmap_bind, dropRec_run', monadHom_ceremonyOutput]
      simp only [dropRecS_liftS, dropRecS_passRun_shifted]
      refine bind_congr fun o => ?_
      rcases o with _ | output
      · exact dropRec_failure
      · exact MonadHom.mmap_pure _ _
  | bottom b =>
    unfold passTree emulatedProgram newBottomWith
    rcases operator.keys with _ | keys <;> rcases operator.top with _ | top
    · exact dropRec_failure
    · exact dropRec_failure
    · exact dropRec_failure
    · rw [MonadHom.mmap_bind, dropRec_run', monadHom_bottomOutputWith]
      simp only [dropRecS_liftS, dropRecS_passRun_shifted]
      refine bind_congr fun o => ?_
      rcases o with _ | output
      · exact dropRec_failure
      · exact MonadHom.mmap_pure _ _


/-! ## The pieces of the games with the keys of the dealer -/

section Pieces

variable {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (view : W → StreamState C)
  (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation of the world keeps the state of the game, so a step after it starts from the same
states. -/
theorem erasedAt_lift_bind {σ α β : Type} (X : OracleComp (WorldSpec C) α)
    (f : α → StateT (RealState C σ) (StateT W ProbComp) β) (g : α → RealM C σ β) (s₁ s₂ : RealState C σ)
    (h : ∀ a, eraseOut <$> (f a).run s₁ = eraseOut <$> simulateQ impl ((g a).run s₂)) :
    eraseOut <$> (StateT.lift (simulateQ impl X) >>= f).run s₁ =
      eraseOut <$> simulateQ impl ((StateT.lift X >>= g).run s₂) := by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind, simulateQ_bind]
  exact bind_congr h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem run_get_bind {S α : Type} {n : Type → Type} [Monad n] [LawfulMonad n] (F : S → StateT S n α) (s : S) :
    (get >>= F).run s = (F s).run s := by
  simp

/-- The dealer of the world as a dealer on the computations of the world. -/
def worldDealt₀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (top : TopTree) : Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith (fun oa => free (liftComp oa _)) parameter dealt top fun x => free (liftComp (prfValue seeds x) _)

omit [Fintype E] [DecidableEq E] in
/-- An emulated recorded run erases to `worldEmulatedRun`, from two states that differ only in the
flag. -/
theorem erasedAt_emulatedRun (net : Adversary C E Unit PEmpty PEmpty) (emu : C.Party → Option (Keys C))
    (openings : List (List (List Bit))) (randomizer : Randomizer) (tree : Tree) (s₁ s₂ : RealState C net.State)
    (hs : eraseFlag s₁ = eraseFlag s₂) :
    eraseOut <$> (sharedRunWith K circuits settings impl view D net (fun i =>
        passTree K circuits settings (shiftedShares circuits D (gameParameter D emu) (gameSeeds D emu) openings)
          (some randomizer) i ⟨emu i, (s₁.operators i).top, (s₁.operators i).bottom⟩ tree) tree).run s₁ =
      eraseOut <$> simulateQ impl ((worldEmulatedRun K circuits settings D net emu openings randomizer tree).run s₂) := by
  unfold sharedRunWith worldEmulatedRun
  rw [run_get_bind, run_get_bind]
  obtain ⟨a₁, o₁, r₁, c₁, f₁⟩ := s₁
  obtain ⟨a₂, o₂, r₂, c₂, f₂⟩ := s₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := fields_of_eraseFlag hs
  refine (?_ : FlagErases impl _ _) _ _ hs
  refine flagErases_read_bind _ fun before => ?_
  have hp : (fun i => emulatedProgram K circuits settings
      (shiftedBuildingBlocks K circuits settings D (gameParameter D emu) (gameSeeds D emu) openings) randomizer i
        ⟨emu i, (o₁ i).top, (o₁ i).bottom⟩ tree) =
      fun i => dropRecord (passTree K circuits settings
        (shiftedShares circuits D (gameParameter D emu) (gameSeeds D emu) openings) (some randomizer) i
          ⟨emu i, (o₁ i).top, (o₁ i).bottom⟩ tree).run.run :=
    funext fun i => (dropRec_passTree_shifted K circuits settings D _ _ _ randomizer i _ tree).symm
  dsimp only
  rw [hp]
  unfold inWorld
  refine flagErases_phase D net noFunctionality ([] : Record C E) _ _ _ fun r => ?_
  rcases r with ⟨state, steps⟩
  refine flagErases_read_bind _ fun after => ?_
  refine (flagErases_lift _).bind fun v => ?_
  exact flagErases_set _ _ rfl

omit [Fintype E] [DecidableEq E] in
/-- A recorded run erases to `secRun`, in each mode. -/
theorem flagErases_sharedRun (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    FlagErases impl (sharedRun K circuits settings impl view m D net parameter seeds dealt emu tree)
      (secRun K circuits settings m D net parameter seeds dealt emu tree) := by
  have plain := flagErases_sharedRun_real K circuits settings impl view D net parameter seeds dealt emu tree
  unfold sharedRun secRun
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  have hr : s₁.runs = s₂.runs := (fields_of_eraseFlag hs).2.2.1
  by_cases h : s₁.runs tree < m.emulated tree
  · rw [ite_eq_left h, ite_eq_left (hr ▸ h)]
    unfold sharedDealer worldDealer
    simp only [bind_assoc, pure_bind]
    have e₁ : referenceTree (fun oa => sharedLift (σ := net.State) impl (tweakable oa))
        (fun x => sharedLift (σ := net.State) impl (prfValue seeds x)) parameter emptyTop .top = worldHom impl net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (worldHom impl net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    have e₂ : referenceTree (fun oa => realLift (σ := net.State) (tweakable oa)) (fun x => realLift (prfValue seeds x))
        parameter emptyTop .top = realHom net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (realHom net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    rw [e₁, e₂]
    refine erasedAt_lift_bind impl _ _ _ s₁ s₂ fun out => ?_
    have d₁ : dealtWith (sharedLift (σ := net.State) impl) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => sharedLift (σ := net.State) impl (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (worldHom impl net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (worldHom impl net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    have d₂ : dealtWith (realLift (σ := net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₁, d₂]
    cases tree with
    | top => exact erasedAt_emulatedRun K circuits settings impl view D net emu _ 0 .top s₁ s₂ hs
    | bottom b =>
      unfold dealerTree
      simp only [bind_assoc]
      refine erasedAt_lift_bind impl _ _ _ s₁ s₂ fun o => ?_
      cases o with
      | none =>
        simp only [pure_bind]
        exact flagErases_pure () s₁ s₂ hs
      | some bottom =>
        simp only [bind_assoc, pure_bind]
        refine erasedAt_lift_bind impl _ _ _ s₁ s₂ fun ρ => ?_
        exact erasedAt_emulatedRun K circuits settings impl view D net emu _ _ (.bottom b) s₁ s₂ hs
  · rw [ite_eq_right h, ite_eq_right (hr ▸ h)]
    have hp := plain s₁ s₂ hs
    unfold sharedRun at hp
    rw [run_get_bind, ite_eq_right (by simp [Mode.real])] at hp
    exact hp

omit [Fintype E] [DecidableEq E] in
theorem flagErases_sharedRuns (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, FlagErases impl
      (sharedRuns K circuits settings runLimit impl view m D net parameter seeds dealt emu tree count)
      (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count)
  | 0 => flagErases_pure ()
  | count + 1 => by
    have run := flagErases_sharedRun K circuits settings impl view D m net parameter seeds dealt emu tree
    have rest := flagErases_sharedRuns m net parameter seeds dealt emu tree count
    unfold sharedRuns secRuns
    refine flagErases_get_bind fun s₁ s₂ hs => ?_
    have hm : mayRun runLimit D s₁ tree ↔ mayRun runLimit D s₂ tree := by
      obtain ⟨-, ho, hr, hc⟩ := fields_of_eraseFlag hs
      cases tree <;> simp only [mayRun, ho, hr, hc]
    by_cases h : mayRun runLimit D s₁ tree
    · rw [ite_eq_left h, ite_eq_left (hm.1 h)]
      exact (run.bind fun _ => rest) s₁ s₂ hs
    · rw [ite_eq_right h, ite_eq_right (mt hm.2 h)]
      exact flagErases_pure () s₁ s₂ hs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The signing oracles of a dealer on the computations of the world. -/
theorem flagErasesT_tsig {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C) :
    FlagErasesT (impl := impl)
      (tsigOracles (sharedLift (σ := σ) impl) (SeedHitProof.Dealt.hmap (worldHom impl σ) d) q)
      (tsigOracles realLift (SeedHitProof.Dealt.hmap (realHom σ) d) q) := fun st =>
  (flagErases_lift _).of_eq (SeedHitProof.hom_tsigOracles (worldHom impl σ) (fun oa => free (liftComp oa _)) d q st)
    (SeedHitProof.hom_tsigOracles (realHom σ) (fun oa => free (liftComp oa _)) d q st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagErasesT_get_bind {σ α : Type}
    {f : RealState C σ → StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp)) α}
    {g : RealState C σ → StateT (TsigState C) (RealM C σ) α}
    (h : ∀ s₁ s₂, eraseFlag s₁ = eraseFlag s₂ → FlagErasesT (impl := impl) (f s₁) (g s₂)) :
    FlagErasesT (impl := impl) (StateT.lift get >>= f) (StateT.lift get >>= g) := by
  intro st
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  exact flagErases_get_bind fun s₁ s₂ hs => h s₁ s₂ hs st s₁ s₂ hs

omit [Fintype E] [DecidableEq E] in
theorem flagErasesT_dealerOracles (m : Mode) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C) :
    FlagErasesT (impl := impl)
      (sharedDealerOracles K circuits settings runLimit impl view m D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (worldHom impl A.net.State) d) q)
      (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (realHom A.net.State) d) q) := by
  unfold secOracles sharedDealerOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact flagErasesT_pure _
  · dsimp only
    unfold secTreeRequest
    refine FlagErasesT.bind (flagErasesT_tsig impl d _) fun answer => ?_
    have tail : FlagErasesT (impl := impl)
        (StateT.lift get >>= fun s : RealState C A.net.State => match heldBottom D s.operators b, answer with
          | some tree, some (_, ρ) => pure (some (tree, ρ))
          | _, _ => pure none)
        (StateT.lift get >>= fun s : RealState C A.net.State => match heldBottom D s.operators b, answer with
          | some tree, some (_, ρ) => pure (some (tree, ρ))
          | _, _ => pure none) := by
      refine flagErasesT_get_bind impl fun s₁ s₂ hs => ?_
      rw [(fields_of_eraseFlag hs).2.1]
      split <;> exact flagErasesT_pure _
    by_cases hc : m.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      exact FlagErasesT.bind (flagErasesT_lift (flagErases_sharedRuns K circuits settings runLimit impl view D m A.net
        parameter seeds dealt emu _ 1)) fun _ => tail
    · simp only [hc, ↓reduceIte]
      exact tail
  all_goals
    dsimp only
    unfold secSignRequest
    refine FlagErasesT.bind (flagErasesT_lift (flagErases_modify _ fun _ => rfl)) fun _ => ?_
    refine flagErasesT_get_bind impl fun s₁ s₂ hs => ?_
    rw [(fields_of_eraseFlag hs).2.1]
    cases (s₂.operators i).keys <;> cases (s₂.operators i).top <;> cases (s₂.operators i).bottom (treeOf e) <;>
      first | exact flagErasesT_tsig impl d _ | exact flagErasesT_pure _

/-- The oracles of `forge` in `sharedSigning` with no `own`, with the dealer `dealer`. -/
def sharedDealerForge (m : Mode) (A : DkgTsigAdversary C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (dealer : Dealt C (StateT (RealState C A.net.State) (StateT W ProbComp))) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State))
      (StateT (TsigState C) (StateT (RealState C A.net.State) (StateT W ProbComp))) :=
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (SharedM C ProbComp W A.net.State)) :=
    fun t => StateT.lift (inWorld impl (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (SharedM C ProbComp W A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : SharedM C ProbComp W A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  HAdd.hAdd forger (HAdd.hAdd
    (sharedDealerOracles K circuits settings runLimit impl view m D A.net parameter seeds dealt emu dealer) cell)

/-- The oracles of `forge` in `secSigning`, with the dealer `dealer`. -/
def secForge (m : Mode) (A : DkgTsigAdversary C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (dealer : Dealt C (RealM C A.net.State)) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) (StateT (TsigState C) (RealM C A.net.State)) :=
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  HAdd.hAdd forger (HAdd.hAdd (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu dealer) cell)

omit [Fintype E] [DecidableEq E] in
theorem flagErasesT_dealerForge (m : Mode) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (d : Dealt C (OracleComp (WorldSpec C))) (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) :
    FlagErasesT (impl := impl)
      (sharedDealerForge K circuits settings runLimit impl view D m A parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (worldHom impl A.net.State) d) t)
      (secForge K circuits settings runLimit D m A parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (realHom A.net.State) d) t) := by
  rcases t with t | q | q
  · exact flagErasesT_lift (flagErases_lift _)
  · exact flagErasesT_dealerOracles K circuits settings runLimit impl view D m A parameter seeds dealt emu d q
  · rcases q with _ | state
    · exact flagErasesT_lift (flagErases_mapGet impl (·.adversary) fun _ => rfl)
    · exact flagErasesT_lift (flagErases_modify _ fun _ => rfl)

omit [Fintype E] [DecidableEq E] in
theorem flagErases_dealerSigning (m : Mode) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) :
    FlagErases impl (sharedSigning K circuits settings runLimit impl view false m D A parameter seeds dealt emu)
      (secSigning K circuits settings runLimit m D A parameter seeds dealt emu) := by
  unfold sharedSigning secSigning
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  rw [(fields_of_eraseFlag hs).2.1]
  cases topHolder D s₂.operators with
  | none => exact flagErases_pure _ s₁ s₂ hs
  | some kt =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold sharedDealer worldDealer
    simp only [bind_assoc, pure_bind]
    have e₁ : referenceTree (fun oa => sharedLift (σ := A.net.State) impl (tweakable oa))
        (fun x => sharedLift (σ := A.net.State) impl (prfValue seeds x)) parameter emptyTop .top =
        worldHom impl A.net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (worldHom impl A.net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    have e₂ : referenceTree (fun oa => realLift (σ := A.net.State) (tweakable oa)) (fun x => realLift (prfValue seeds x))
        parameter emptyTop .top = realHom A.net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (realHom A.net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    rw [e₁, e₂]
    refine erasedAt_lift_bind impl _ _ _ s₁ s₂ fun out => ?_
    have d₁ : dealtWith (sharedLift (σ := A.net.State) impl) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => sharedLift (σ := A.net.State) impl (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (worldHom impl A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (worldHom impl A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    have d₂ : dealtWith (realLift (σ := A.net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₁, d₂]
    refine (?_ : FlagErases impl _ _) s₁ s₂ hs
    have sim := flagErasesT_simulateQ _ _
      (flagErasesT_dealerForge K circuits settings runLimit impl view D m A parameter seeds dealt emu
        (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)))
      (A.forge ⟨((TreeOutput.topTree out).getD emptyTop).root, parameter⟩ ((TreeOutput.topTree out).getD emptyTop))
    refine (sim _).bind fun p => ?_
    rcases p with ⟨forgery, st⟩
    exact (flagErases_lift _).of_eq
      (hom_forgeryWins (worldHom impl A.net.State) (fun oa => free (liftComp oa _))
        (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) st forgery)
      (hom_forgeryWins (realHom A.net.State) (fun oa => free (liftComp oa _))
        (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) st forgery)

end Pieces

/-! ## The hop -/

omit [Fintype E] [DecidableEq E] in
theorem sharedDealt_fst (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    (fun r => r.1.1) <$> sharedDealt prims K circuits settings runLimit m D A =
      simulateQ (loggedWorld prims D) (dealtGame K circuits settings runLimit m D A) := by
  unfold sharedDealt dealtGame dealtRun sharedRest secRest
  simp only [map_bind, simulateQ_bind, simulateQ_map]
  refine bind_congr fun x => ?_
  rcases x with ⟨state, parameter, seeds, dealt, emu⟩
  simp only [inWorld, StateT.run'_eq, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, pure_bind,
    bind_assoc, simulateQ_bind, simulateQ_map, map_bind]
  refine bind_congr fun v => ?_
  have h := ((flagErases_sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst D m A.net
    parameter seeds dealt (committed v.2 emu) .top runLimit).bind
    fun _ => flagErases_dealerSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst D m A
      parameter seeds dealt (committed v.2 emu)).fst
    (votedStart D (startState D state fun i => (emu i).map fun _ => dealt i) v.1 v.2)
  simp only [StateT.run_bind, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
    simulateQ_pure] at h ⊢
  exact h

omit [Fintype E] [DecidableEq E] in
/-- The proof of `SharedEnd`. -/
theorem sharedEnd : ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    dealtProb prims K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A (fun r => r.1.1.1 = true) =
      streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) := by
  intro D A
  generalize (⟨true, fun _ => runLimit⟩ : Mode) = mo
  unfold dealtProb streamAccepts
  congr 1
  have e1 : Pr{let r ← (sharedDealt prims K circuits settings runLimit mo D A).run ((∅, ∅), [])}[r.1.1.1 = true] =
      Pr{let r ← (simulateQ (loggedWorld prims D) (dealtGame K circuits settings runLimit mo D A)).run ((∅, ∅), [])}[
        r.1 = true] := by
    rw [← sharedDealt_fst, StateT.run_map, prEvent_map]
  have e2 : Pr{let r ← (simulateQ (streamWorld prims D) (dealtGame K circuits settings runLimit mo D A)).run (∅, ∅)}[
        r.1 = true] =
      Pr{let r ← (simulateQ (loggedWorld prims D) (dealtGame K circuits settings runLimit mo D A)).run ((∅, ∅), [])}[
        r.1 = true] := by
    rw [loggedWorld_eq, ← withLog_run (streamWorld prims D) countedCells _ (∅, ∅) [], prEvent_map]
  rw [e1, e2]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedEnd
