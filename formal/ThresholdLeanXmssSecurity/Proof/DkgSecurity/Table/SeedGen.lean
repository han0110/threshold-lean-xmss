import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.ShapeEnd

/-!
# `SeedGenShape`

`LogRel y x` states that a computation `y` of the forger in the world is the observed computation `x`
with the setup calls of its log appended to the log of the forger, and with no change of the state
of the signing game. The roles of the forger are the observed roles in this sense, so the network
of the seed generation is too. `seedGenShape` proves `SeedGenShape` from it, and `tableHop` proves the
hop `TableHop`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- `y` is `x` with the setup calls of the log of `x` appended to the log of the forger. -/
def LogRel {α : Type} (y : WorldM C α) (x : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) : Prop :=
  ∀ log st, (y.run log).run st = (fun r => ((r.1, log ++ r.2.filter fun e => isSetupQuery e.1), st)) <$> x.run

theorem LogRel.pure {α : Type} (a : α) :
    LogRel (Pure.pure a : WorldM C α) (Pure.pure a) := by
  intro log st
  change _ = _ <$> (Pure.pure (a, []) : OracleComp (WorldSpec C) _)
  simp

theorem LogRel.bind {α β : Type} {y : WorldM C α} {x : WriterT (CallLog C) (OracleComp (WorldSpec C)) α}
    {g : α → WorldM C β} {f : α → WriterT (CallLog C) (OracleComp (WorldSpec C)) β}
    (h : LogRel y x) (hk : ∀ a, LogRel (g a) (f a)) : LogRel (y >>= g) (x >>= f) := by
  intro log st
  rw [StateT.run_bind, StateT.run_bind, h log st, bind_map_left]
  simp only [WriterT.run_bind, map_bind, Functor.map_map, List.filter_append]
  refine bind_congr fun r => ?_
  rw [hk r.1]
  simp [List.append_assoc]

theorem LogRel.adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    LogRel (forgerWorldRoles.adversary oa) (observedRoles.adversary oa) := fun log st =>
  worldAdversaryCall_run oa log st

theorem LogRel.honest {α : Type} (oa : OracleComp (LocalSpec C) α) :
    LogRel (forgerWorldRoles.honest oa) (observedRoles.honest oa) := by
  intro log st
  change ((simulateQ worldHonestCall oa).run log).run st = _
  rw [worldHonestCall_run]
  simp [observedRoles, WriterT.run_liftM, Functor.map_map]

theorem LogRel.sequenceFin {α : Type} : ∀ {n : ℕ} {g : Fin n → WorldM C α}
    {f : Fin n → WriterT (CallLog C) (OracleComp (WorldSpec C)) α}, (∀ i, LogRel (g i) (f i)) →
    LogRel (OverPermutation.sequenceFin g) (OverPermutation.sequenceFin f)
  | 0, _, _, _ => by
    simp only [OverPermutation.sequenceFin]
    exact LogRel.pure _
  | n + 1, _, _, h => by
    simp only [OverPermutation.sequenceFin]
    exact (h 0).bind fun _ => (LogRel.sequenceFin fun i => h i.succ).bind fun _ => LogRel.pure _

section Network

variable {E α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)

theorem logRel_stepRound (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    LogRel (stepRound forgerWorldRoles D A noFunctionality state steps)
      (stepRound observedRoles D A noFunctionality state steps) := by
  unfold stepRound
  rw [ite_eq_right (by simp [callInput_real]), ite_eq_right (by simp [callInput_real])]
  refine (LogRel.adversary _).bind fun r => ?_
  obtain ⟨state', sent⟩ := r
  refine (LogRel.sequenceFin fun j => ?_).bind fun _ => LogRel.pure _
  split <;> (try split) <;> first | exact LogRel.pure _ | exact LogRel.honest _

theorem logRel_executeRounds :
    ∀ fuel (state : A.State) (steps : C.Party → Step C E RealSpec α),
      LogRel (executeRounds forgerWorldRoles D A noFunctionality fuel state steps)
        (executeRounds observedRoles D A noFunctionality fuel state steps)
  | 0, state, steps => by
    simp only [executeRounds]
    exact LogRel.pure _
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · exact LogRel.pure _
    · exact (logRel_stepRound D A state steps).bind fun r => logRel_executeRounds fuel r.1 r.2.1

end Network

/-! ## Computations of the forger with no call of `A` -/

theorem lifted_sequenceFin {α : Type} : ∀ {n : ℕ} {g : Fin n → WorldM C α} {f : Fin n → OracleComp (WorldSpec C) α},
    (∀ i log st, ((g i).run log).run st = (fun a => ((a, log), st)) <$> f i) →
    ∀ log st, ((OverPermutation.sequenceFin g).run log).run st =
      (fun a => ((a, log), st)) <$> OverPermutation.sequenceFin f
  | 0, _, _, _, log, st => by simp [OverPermutation.sequenceFin]
  | n + 1, _, _, h, log, st => by
    simp only [OverPermutation.sequenceFin, StateT.run_bind, h 0, bind_map_left, map_bind,
      lifted_sequenceFin (fun i => h i.succ), StateT.run_pure, map_pure]

theorem startSteps_run {E α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (log : CallLog C) (st : TsigState C) :
    ((startSteps forgerWorldRoles D program).run log).run st =
      (fun a => ((a, log), st)) <$> startSteps worldRoles D program := by
  unfold startSteps
  refine lifted_sequenceFin (fun i log st => ?_) log st
  split
  · simp
  · exact worldHonestCall_run _ log st

theorem worldWrite_run (q : Query C) (value : HashOutput) (log : CallLog C) (st : TsigState C) :
    ((worldWrite q value).run log).run st = (fun _ => (((), log), st)) <$> program q value := by
  simp [worldWrite, toWorld, StateT.run_lift]

theorem forIn_bind_run {γ β δ : Type} (l : List γ) (f : γ → PUnit → WorldM C (ForInStep PUnit))
    (c : γ → OracleComp (WorldSpec C) β)
    (hc : ∀ a log st, ((f a PUnit.unit).run log).run st = (fun _ => ((ForInStep.yield PUnit.unit, log), st)) <$> c a)
    (log : CallLog C) (st : TsigState C) (K : (PUnit × CallLog C) × TsigState C → OracleComp (WorldSpec C) δ) :
    (((forIn l PUnit.unit f).run log).run st >>= K) = (l.mapM c >>= fun _ => K ((PUnit.unit, log), st)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.forIn_cons, StateT.run_bind, hc, bind_map_left, bind_assoc, List.mapM_cons]
    refine bind_congr fun _ => ?_
    simpa using ih

theorem extractReveal_filter_append {E : Type} (phase : Phase) (a b : CallLog C)
    (sent : C.Party → C.Party → Option (Msg E)) (j i : C.Party) :
    extractReveal phase (List.filter (fun e => isSetupQuery e.1) a ++ List.filter (fun e => isSetupQuery e.1) b) sent j i =
      extractReveal phase (a ++ b) sent j i := by
  rw [← List.filter_append, extractReveal_filter]

/-! ## The seed generation -/

section SeedGen

variable {E : Type} [Field E] [Algebra Bit E] (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

theorem fwAdversary_run {α : Type} (oa : OracleComp (LocalSpec C) α) (log : CallLog C) (st : TsigState C) :
    ((forgerWorldRoles.adversary oa).run log).run st =
      (fun r => ((r.1, log ++ r.2.filter fun e => isSetupQuery e.1), st)) <$> observe oa :=
  worldAdversaryCall_run oa log st

theorem fwHonest_run {α : Type} (oa : OracleComp (LocalSpec C) α) (log : CallLog C) (st : TsigState C) :
    ((forgerWorldRoles.honest oa).run log).run st = (fun a => ((a, log), st)) <$> free oa :=
  worldHonestCall_run oa log st

omit [Field E] [Algebra Bit E] in
theorem fwStepRound_run {α : Type} (state : net.State) (steps : C.Party → Step C E RealSpec α) (log : CallLog C)
    (st : TsigState C) :
    ((stepRound forgerWorldRoles D net noFunctionality state steps).run log).run st =
      (fun r => ((r.1, log ++ r.2.filter fun e => isSetupQuery e.1), st)) <$>
        (stepRound observedRoles D net noFunctionality state steps).run :=
  logRel_stepRound D net state steps log st

omit [Field E] [Algebra Bit E] in
theorem fwExecuteRounds_run {α : Type} (fuel : ℕ) (state : net.State) (steps : C.Party → Step C E RealSpec α)
    (log : CallLog C) (st : TsigState C) :
    ((executeRounds forgerWorldRoles D net noFunctionality fuel state steps).run log).run st =
      (fun r => ((r.1, log ++ r.2.filter fun e => isSetupQuery e.1), st)) <$>
        (executeRounds observedRoles D net noFunctionality fuel state steps).run :=
  logRel_executeRounds D net fuel state steps log st

theorem seedGenShape : SeedGenShape (E := E) D := by
  intro net parameter k st
  unfold seedGenWorld seedGenTail
  simp only [StateT.run_bind, fwAdversary_run, fwHonest_run, startSteps_run, fwStepRound_run, bind_map_left,
    map_bind, StateT.run_get, pure_bind]
  simp only [List.nil_append, extractReveal_filter_append]
  refine bind_congr fun o => bind_congr fun parts => bind_congr fun steps => bind_congr fun r => bind_congr
    fun high => ?_
  rw [worldWrite_run, bind_map_left]
  refine bind_congr fun _ => ?_
  dsimp only
  refine Eq.trans (forIn_bind_run (β := Bool) _ _ ?cT ?hT _ _ _) ?mainT
  case mainT =>
    refine bind_congr (m := OracleComp (WorldSpec C)) fun _ => ?_
    dsimp only
    refine Eq.trans (forIn_bind_run (β := List Bool) _ _ ?cP ?hP _ _ _) ?mainP
    case mainP =>
      refine bind_congr (m := OracleComp (WorldSpec C)) fun _ => ?_
      dsimp only
      rw [fwExecuteRounds_run]
      simp [Functor.map_map]
    case hP =>
      intro j log st
      rw [StateT.run_bind, StateT.run_bind]
      rw [forIn_bind_run (β := Bool) _ _ _ (fun i log st => ?_) log st]
      · simp only [map_eq_bind_pure_comp]
        rfl
      · by_cases h : j ∈ D.1 ∧ i ∉ D.1
        · simp [StateT.run_bind, worldWrite_run, h, map_eq_bind_pure_comp]
        · simp [h]
  case hT =>
    intro T log st
    split
    · rename_i j heq
      have hj : j ∈ D.1 := by
        have := List.find?_some heq
        simp only [decide_eq_true_eq] at this
        exact this.1
      rw [heq]
      simp [StateT.run_bind, worldWrite_run, hj, map_eq_bind_pure_comp]
    · rename_i heq
      rw [heq]
      simp

end SeedGen

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.seedGenShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.seedGenShape

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The hop `TableHop`. `dealtGame` with each run emulated wins at most as often as the forger
`dkgReduction` wins `tsigGame`. -/
theorem tableHop (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (runLimit : ℕ) :
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
      streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) ≤
        accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A)) :=
  tableHop_of_structureStage prims K circuits settings runLimit
    (structureStage_of_stages K circuits settings runLimit prims (bottomStage K circuits settings runLimit prims)
      (shapeStage_of_seedGenShape K circuits settings runLimit prims fun D => seedGenShape D))

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop
