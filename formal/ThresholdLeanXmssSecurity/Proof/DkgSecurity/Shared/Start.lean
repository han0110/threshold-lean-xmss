import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Hops
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Erasure

/-!
# The proof of `SharedStart`

The real game with the shared event, `sharedReal true`, is `dkgTsigGame` with recorded runs, with the
log of the counted calls and with a flag. `dropRec_passTree_plain` states that a real recorded program
with its record dropped is `treeProgram`. Then each piece of the rest of the shared game erases to the
piece of `dkgTsigRun noMonitor` (`FlagErases`), and the log goes away by `withLog_run`.
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

/-! ## The real recorded program with its record dropped -/

omit [Fintype E] [DecidableEq E] in
theorem dropRecS_passBatch_plain (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    dropRecS (passBatch K circuits settings plainShares ctx parameter jobs) =
      realBatch K circuits settings.mode ctx parameter jobs := by
  unfold passBatch passCheckOpen plainShares
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_get, dropRecS_set, dropRecS_liftS, dropRecS_record,
    pure_bind]
  refine StateT.ext fun st => ?_
  rw [realBatch_run]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    StateT.run_pure]
  refine bind_congr fun inputs => ?_
  rw [runJobs_eq, StateT.run_bind, foldlM_layerBody_eq, StateT.run_map, bind_map_left, bind_assoc]
  refine bind_congr fun r => ?_
  simp only [tailBody, StateT.run_bind, bind_assoc]
  refine bind_congr fun x => ?_
  refine bind_congr fun y => ?_
  have hopen : ∀ (v : Shares C Bit) (count : ℕ), openRep (G := RealSpec) K ctx v count =
      oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (v T)))) >>= fun digests =>
        exchange (repOutbox (E := E) K ctx.self v count digests) >>= fun inbox => repRest K ctx.self v count inbox := by
    intro v count
    change openRep K (localContext ctx.self) v count = _
    rw [openRep_eq]
    rfl
  change _ = StateT.run (StateT.lift (openRep (G := RealSpec) K ctx x.1 _)) y.2 >>= _
  rw [StateT.run_lift, hopen]
  simp only [bind_assoc, pure_bind, StateT.run_pure]

omit [Fintype E] [DecidableEq E] in
theorem dropRecS_passRun_plain (i : C.Party) (keys : Keys C) (jobs : List Job) :
    dropRecS (passRun K circuits settings plainShares i keys jobs) =
      ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs := by
  unfold passRun
  rw [MonadHom.mmap_bind, dropRecS_liftS]
  simp only [monadHom_batched, dropRecS_passBatch_plain]
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem dropRec_failure {α : Type} : dropRec (failure : RecM C E α) = failure :=
  OptionT.ext (by
    change dropLog.toFun _ (pure none) = pure none
    exact dropLog.toFun_pure' _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem dropRec_run' {S α : Type} (x : StateT S (RecM C E) α) (s : S) :
    dropRec (x.run' s) = (dropRecS x).run' s := by
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, MonadHom.mmap_bind]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- A real recorded program with its record dropped is `treeProgram`. -/
theorem dropRec_passTree_plain (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    dropRec (passTree K circuits settings plainShares none i operator tree) =
      treeProgram K circuits settings i operator tree := by
  have hcer : ∀ (keys : Keys C) (top : TopTree) (t : Tree),
      dropRec ((ceremonyOutput (m := StateT (ℕ × ℕ) (RecM C E))
        (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
        (passRun K circuits settings plainShares i keys) top t).run' (0, 0)) =
      (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
        (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys)
        top t).run' (0, 0) := by
    intro keys top t
    rw [dropRec_run', monadHom_ceremonyOutput]
    simp only [dropRecS_liftS, dropRecS_passRun_plain]
  cases tree with
  | top =>
    unfold passTree treeProgram newTree
    rcases operator.keys with _ | keys
    · exact dropRec_failure
    · rw [MonadHom.mmap_bind, hcer]
      refine bind_congr fun o => ?_
      rcases o with _ | output
      · exact dropRec_failure
      · exact MonadHom.mmap_pure _ _
  | bottom b =>
    unfold passTree treeProgram newTree
    rcases operator.keys with _ | keys <;> rcases operator.top with _ | top
    · exact dropRec_failure
    · exact dropRec_failure
    · exact dropRec_failure
    · rw [MonadHom.mmap_bind, hcer]
      refine bind_congr fun o => ?_
      rcases o with _ | output
      · exact dropRec_failure
      · exact MonadHom.mmap_pure _ _

/-! ## The pieces of the real game -/

section Pieces

variable {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (view : W → StreamState C)
  (D : C.Coalition)

omit [Fintype E] [DecidableEq E] in
theorem treeProgram_eq_drop (operators : C.Party → OperatorState C) (tree : Tree) :
    (fun i => treeProgram K circuits settings i (operators i) tree) =
      fun i => dropRecord (passTree K circuits settings plainShares none i (operators i) tree).run.run :=
  funext fun i => (dropRec_passTree_plain K circuits settings i (operators i) tree).symm

omit [Fintype E] [DecidableEq E] in
/-- A real recorded run erases to `treeRun` with no monitor. -/
theorem flagErases_sharedRun_real (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    FlagErases impl (sharedRun K circuits settings impl view Mode.real D net parameter seeds dealt emu tree)
      (treeRun K circuits settings noMonitor D net tree) := by
  unfold sharedRun treeRun
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  have hnot : ¬ s₁.runs tree < Mode.real.emulated tree := by simp [Mode.real]
  rw [ite_eq_right hnot]
  unfold sharedRunWith
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  obtain ⟨a₁, o₁, r₁, c₁, f₁⟩ := s₁
  obtain ⟨a₂, o₂, r₂, c₂, f₂⟩ := s₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := fields_of_eraseFlag hs
  refine (?_ : FlagErases impl _ _) _ _ hs
  refine flagErases_read_bind _ fun before => ?_
  dsimp only
  rw [treeProgram_eq_drop]
  unfold inWorld
  refine flagErases_phase D net noFunctionality ([] : Record C E) _ _ _ fun r => ?_
  rcases r with ⟨state, steps⟩
  refine flagErases_read_bind _ fun after => ?_
  have hm : ∀ (keys : C.Party → Option (Keys C)) (outputs : C.Party → Option TreeOutput),
      (StateT.lift (noMonitor keys tree outputs) : RealM C net.State Bool) = pure false := fun _ _ =>
    StateT.ext fun s => by simp [noMonitor, StateT.run_lift]
  simp only [hm, pure_bind]
  exact flagErases_set _ _ rfl

omit [Fintype E] [DecidableEq E] in
theorem flagErases_sharedRuns_real (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, FlagErases impl
      (sharedRuns K circuits settings runLimit impl view Mode.real D net parameter seeds dealt emu tree count)
      (treeRuns K circuits settings runLimit noMonitor D net tree count)
  | 0 => flagErases_pure ()
  | count + 1 => by
    have run := flagErases_sharedRun_real K circuits settings impl view D net parameter seeds dealt emu tree
    have rest := flagErases_sharedRuns_real net parameter seeds dealt emu tree count
    unfold sharedRuns treeRuns
    refine flagErases_get_bind fun s₁ s₂ hs => ?_
    have hm : mayRun runLimit D s₁ tree ↔ mayRun runLimit D s₂ tree := by
      obtain ⟨-, ho, hr, hc⟩ := fields_of_eraseFlag hs
      cases tree <;> simp only [mayRun, ho, hr, hc]
    by_cases h : mayRun runLimit D s₁ tree
    · rw [ite_eq_left h, ite_eq_left (hm.1 h)]
      exact (run.bind fun _ => rest) s₁ s₂ hs
    · rw [ite_eq_right h, ite_eq_right (mt hm.2 h)]
      exact flagErases_pure () s₁ s₂ hs

/-- The computations of the world on the state of the game over the state of `impl`. -/
def worldHom (σ : Type) : OracleComp (WorldSpec C) →ᵐ StateT (RealState C σ) (StateT W ProbComp) where
  toFun _ oa := StateT.lift (simulateQ impl oa)
  toFun_pure' a := by ext; simp
  toFun_bind' _ _ := by ext; simp

omit [Fintype E] [DecidableEq E] in
/-- The end of a request of a bottom tree reads the outputs of the operators only. -/
theorem flagErases_heldAnswer {σ : Type} (b : Fin (2 ^ layerHeight)) :
    FlagErases impl
      (get >>= fun s : RealState C σ => match heldBottom D s.operators b with
        | some tree => do
          let v ← (sharedLift impl (prfValue (gameSeeds D fun i => (s.operators i).keys)
            (.randomizer topLayer (topKey b))) : StateT (RealState C σ) (StateT W ProbComp) Digest)
          pure (some (tree, v))
        | none => pure none)
      (get >>= fun s : RealState C σ => match heldBottom D s.operators b with
        | some tree => do
          let v ← gameValue D s.operators (.randomizer topLayer (topKey b))
          pure (some (tree, v))
        | none => pure none) := by
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  rw [(fields_of_eraseFlag hs).2.1]
  refine (?_ : FlagErases impl _ _) s₁ s₂ hs
  split
  · exact (flagErases_lift _).bind fun _ => flagErases_pure _
  · exact flagErases_pure _

omit [Fintype E] [DecidableEq E] in
theorem flagErasesT_sign {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    FlagErasesT (impl := impl)
      (do
        StateT.lift (modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true })
        let s ← StateT.lift get
        operatorAnswer (sharedLift impl)
          (fun x => sharedLift impl (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) (s.operators i) e q :
        StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp)) (TsigSpec C q))
      (signRequest D (σ := σ) i e q) := by
  unfold signRequest
  refine FlagErasesT.bind (flagErasesT_lift (flagErases_modify _ fun _ => rfl)) fun _ => ?_
  intro st
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  rw [(fields_of_eraseFlag hs).2.1]
  refine (?_ : FlagErases impl _ _) s₁ s₂ hs
  exact (flagErases_lift _).of_eq
    (hom_operatorAnswer (worldHom impl σ) (fun oa => free (liftComp oa _))
      (fun x => free (liftComp (prfValue (gameSeeds D fun j => (s₂.operators j).keys) x) _)) (s₂.operators i) e q st)
    (hom_operatorAnswer (realHom σ) (fun oa => free (liftComp oa _))
      (fun x => free (liftComp (prfValue (gameSeeds D fun j => (s₂.operators j).keys) x) _)) (s₂.operators i) e q st)

omit [Fintype E] [DecidableEq E] in
theorem flagErasesT_ownOracles (net_A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (q : TsigQuery C) :
    FlagErasesT (impl := impl)
      (sharedOwnOracles K circuits settings runLimit impl view Mode.real D net_A.net parameter seeds dealt emu q)
      (realOracles K circuits settings runLimit noMonitor D net_A q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact flagErasesT_pure _
  · exact flagErasesT_lift ((flagErases_sharedRuns_real K circuits settings runLimit impl view D net_A.net
      parameter seeds dealt emu _ 1).bind fun _ => flagErases_heldAnswer impl D b)
  · exact flagErasesT_sign impl D i e _
  · exact flagErasesT_sign impl D i e _

omit [Fintype E] [DecidableEq E] in
theorem flagErases_mapGet {σ α : Type} (f : RealState C σ → α) (hf : ∀ s, f (eraseFlag s) = f s) :
    FlagErases impl (f <$> (get : StateT (RealState C σ) (StateT W ProbComp) _)) (f <$> (get : RealM C σ _)) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  simp only [Function.comp_apply]
  rw [← hf s₁, hs, hf s₂]
  exact flagErases_pure _ s₁ s₂ hs

omit [Fintype E] [DecidableEq E] in
/-- The win test of the real game reads the outputs of the operators only. -/
theorem flagErases_winTest {σ : Type} (parameter : PublicParameter) (top : TopTree) (st : TsigState C)
    (forgery : Forgery) :
    FlagErases impl
      (get >>= fun s : RealState C σ =>
        forgeryWins (sharedLift impl)
          { dealtWith (m := StateT (RealState C σ) (StateT W ProbComp)) (sharedLift impl) parameter
              (fun i => ((s.operators i).keys).getD noKeys) top
              (fun x => sharedLift impl (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) with
            bottom := fun b => pure (heldBottom D s.operators b) } st forgery)
      (get >>= fun s : RealState C σ => forgeryWins realLift (canonicalDealt D s.operators parameter top) st forgery) := by
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  rw [(fields_of_eraseFlag hs).2.1]
  refine (?_ : FlagErases impl _ _) s₁ s₂ hs
  have hdealt : SeedHitProof.Dealt.hmap (worldHom impl σ) (worldDealt D s₂.operators parameter top) =
      { dealtWith (m := StateT (RealState C σ) (StateT W ProbComp)) (sharedLift impl) parameter
          (fun i => ((s₂.operators i).keys).getD noKeys) top
          (fun x => sharedLift impl (prfValue (gameSeeds D fun i => (s₂.operators i).keys) x)) with
        bottom := fun b => pure (heldBottom D s₂.operators b) } := by
    unfold SeedHitProof.Dealt.hmap worldDealt
    congr 1
  have hw := hom_forgeryWins (worldHom impl σ) (fun oa => free (liftComp oa _))
    (worldDealt D s₂.operators parameter top) st forgery
  rw [hdealt] at hw
  exact (flagErases_lift _).of_eq hw (forgeryWins_canonicalDealt D s₂.operators parameter top st forgery).symm

/-- The oracles of `forge` in `sharedSigning` with `own`, in the real mode. -/
def sharedForgeOracles (A : DkgTsigAdversary C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State))
      (StateT (TsigState C) (StateT (RealState C A.net.State) (StateT W ProbComp))) :=
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (SharedM C ProbComp W A.net.State)) :=
    fun t => StateT.lift (inWorld impl (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (SharedM C ProbComp W A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : SharedM C ProbComp W A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  HAdd.hAdd forger (HAdd.hAdd
    (sharedOwnOracles K circuits settings runLimit impl view Mode.real D A.net parameter seeds dealt emu) cell)

omit [Fintype E] [DecidableEq E] in
theorem flagErasesT_forgeOracles (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) :
    FlagErasesT (impl := impl) (sharedForgeOracles K circuits settings runLimit impl view D A parameter seeds dealt emu t)
      (realForgeOracles K circuits settings runLimit D noMonitor A t) := by
  rcases t with t | q | q
  · exact flagErasesT_lift (flagErases_lift _)
  · exact flagErasesT_ownOracles K circuits settings runLimit impl view D A parameter seeds dealt emu q
  · rcases q with _ | state
    · exact flagErasesT_lift (flagErases_mapGet impl (·.adversary) fun _ => rfl)
    · exact flagErasesT_lift (flagErases_modify _ fun _ => rfl)

omit [Fintype E] [DecidableEq E] in
theorem flagErases_signing (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) :
    FlagErases impl (sharedSigning K circuits settings runLimit impl view true Mode.real D A parameter seeds dealt emu)
      (dkgSigning K circuits settings runLimit noMonitor D A) := by
  have sim := fun pk top => flagErasesT_simulateQ _ _
    (flagErasesT_forgeOracles K circuits settings runLimit impl view D A parameter seeds dealt emu) (A.forge pk top)
  unfold sharedSigning dkgSigning
  refine flagErases_get_bind fun s₁ s₂ hs => ?_
  rw [(fields_of_eraseFlag hs).2.1]
  refine (?_ : FlagErases impl _ _) s₁ s₂ hs
  cases topHolder D s₂.operators with
  | none => exact flagErases_pure _
  | some kt =>
    rcases kt with ⟨keys, top⟩
    simp only [↓reduceIte]
    exact (sim ⟨top.root, keys.parameter⟩ top _).bind fun p => by
      rcases p with ⟨forgery, st⟩
      exact flagErases_winTest impl D keys.parameter top st forgery

end Pieces

/-! ## The hop -/

/-- `loggedWorld` is `streamWorld` with the log of the counted cells. -/
theorem loggedWorld_eq (D : C.Coalition) : loggedWorld prims D = withLog (streamWorld prims D) countedCells := rfl

omit [Fintype E] [DecidableEq E] in
theorem sharedReal_fst (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Prod.fst <$> sharedReal prims K circuits settings runLimit true D A =
      simulateQ (loggedWorld prims D) (dkgTsigGame K circuits settings runLimit D A) := by
  unfold sharedReal dkgTsigGame dkgTsigRun sharedRestOf sharedRest
  simp only [map_bind, simulateQ_bind, simulateQ_map]
  refine bind_congr fun x => ?_
  rcases x with ⟨state, keys⟩
  have h := ((flagErases_sharedRuns_real K circuits settings runLimit (loggedWorld prims D) Prod.fst D A.net
    (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none) .top runLimit).bind
    fun _ => flagErases_signing K circuits settings runLimit (loggedWorld prims D) Prod.fst D A
      (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)).fst
    (startState D state keys)
  simp only [StateT.run_bind, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
    simulateQ_pure] at h ⊢
  exact h

omit [Fintype E] [DecidableEq E] in
/-- The proof of `SharedStart`. -/
theorem sharedStart : ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (dkgTsigGame K circuits settings runLimit D A) =
      realProb prims K circuits settings runLimit true D A fun r => r.1 = true := by
  intro D A
  unfold realProb streamAccepts
  congr 1
  have e1 : Pr{let r ← (sharedReal prims K circuits settings runLimit true D A).run ((∅, ∅), [])}[r.1.1 = true] =
      Pr{let r ← (simulateQ (loggedWorld prims D) (dkgTsigGame K circuits settings runLimit D A)).run ((∅, ∅), [])}[
        r.1 = true] := by
    rw [← sharedReal_fst, StateT.run_map, prEvent_map]
  have e2 : Pr{let r ← (simulateQ (streamWorld prims D) (dkgTsigGame K circuits settings runLimit D A)).run (∅, ∅)}[
        r.1 = true] =
      Pr{let r ← (simulateQ (loggedWorld prims D) (dkgTsigGame K circuits settings runLimit D A)).run ((∅, ∅), [])}[
        r.1 = true] := by
    rw [loggedWorld_eq, ← withLog_run (streamWorld prims D) countedCells _ (∅, ∅) [], prEvent_map]
  rw [e2, ← e1]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedStart
