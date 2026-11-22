import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Records.Keys
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Cover
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.End

/-!
# The fuel of a recorded run of a tree

`passDone` proves `PassDone`. Both real forms of the opened sharing make no round
(`timed_realOpened`), so one ceremony with the record of a pass takes the rounds of the ceremony
(`timedLog_passRun`), and `treeFuel` covers the program of each operator in a run of a tree, for each
randomizer (`within_passTree`). So each honest operator ends the run.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening ThresholdLeanXmssSecurity.DkgCorrectnessProof.LiveRounds

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Fuel

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- The check and the opening of a start with the record of a pass take the check rounds and one
round, for an opened sharing with no round. An abort keeps at most one opening, and a result has one
start and one opening. -/
theorem timedLog_passCheckOpen (opened : Opened C E) (hopen : ∀ b k, Timed 0 (opened b k).run) (b : BatchStart C)
    (k : ℕ) (st : ℕ × ℕ) :
    TimedLog (Stop 1) (Full 1 1) (checkLabels (tupleCount b.circuits) + 1)
      ((passCheckOpen K opened b k).run st).run.run := by
  have hcheck := runTimed_realCheck (G := RealSpec) K b.ctx (batchTuples K b.mode b.circuits b.inputs b.zs b.v')
    b.state
  rw [sum_batchTuples] at hcheck
  rw [show checkLabels (tupleCount b.circuits) + 1 = checkLabels (tupleCount b.circuits) + (0 + (0 + (1 + 0))) by
    omega]
  simp only [passCheckOpen, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk,
    StateT.run_set, StateT.run_pure]
  refine timedLog_record_bind (a := 1) (s := 0) (o := 1) _ ?_ (by simp [openingsOf]) rfl rfl
  refine timedLog_lift_bind (timed_pair hcheck st) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  refine timedLog_record_bind (a := 0) (s := 0) (o := 0) _ ?_ le_rfl rfl rfl
  refine timedLog_lift_bind (timed_pair (hopen b k) _) ⟨rfl, by simp [openingsOf]⟩ fun p₀ => ?_
  refine timedLog_lift_bind (timed_pair (timed_oracleStep _) _) ⟨rfl, by simp [openingsOf]⟩ fun p₁ => ?_
  refine timedLog_lift_bind (timed_pair (timed_exchange _) _) ⟨rfl, by simp [openingsOf]⟩ fun p₂ => ?_
  rw [← Nat.add_zero 0]
  refine timedLog_lift_bind (timed_pair (timed_repRest K _ _ _ _) _) ⟨rfl, by simp [openingsOf]⟩ fun p₃ => ?_
  refine timedLog_record_bind (a := 0) (s := 0) (o := 0) _ ?_ le_rfl rfl rfl
  rw [run_recPure]
  exact TimedLog.done _ ⟨rfl, rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- A batch with the record of a pass takes `exactBatchRounds`, for an opened sharing with no round. -/
theorem timedLog_passBatch (opened : Opened C E) (hopen : ∀ b k, Timed 0 (opened b k).run) (ctx : Context C)
    (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ) :
    TimedLog (Stop 1) (Full 1 1) (CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)))
      ((passBatch K circuits settings opened ctx parameter jobs).run st).run.run := by
  obtain ⟨label, k⟩ := st
  simp only [passBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, RecM.liftS, StateT.run_mk]
  have harith : CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)) =
      0 + (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds +
        (1 + (checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1))) := by
    unfold CheckTiming.exactBatchRounds checkLabels
    split_ifs <;> omega
  rw [harith]
  refine timedLog_lift_bind (timed_pair (timed_inputShares ctx jobs) _) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  refine timedLog_lift_bind (timed_pair (runTimed_recLayers K ctx settings.mode _ _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₁ => ?_
  refine timedLog_lift_bind (timed_pair (runTimed_realRerand K ctx settings.mode _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₂ => ?_
  exact timedLog_passCheckOpen K opened hopen ⟨(realRunBuildingBlocks K ctx settings.mode).mode, jobs, parameter,
    jobs.map (circuits parameter ·.kind), p.1, p₁.1.1, p₂.1.1, ctx, p₂.1.2⟩ k p₂.2

omit [Fintype E] [DecidableEq E] in
/-- Batches with the record of a pass take the sum of their rounds, for an opened sharing with no
round. -/
theorem timedLog_passBatches (opened : Opened C E) (hopen : ∀ b k, Timed 0 (opened b k).run) (ctx : Context C)
    (parameter : PublicParameter) :
    ∀ (js : List (List Job)) (st : ℕ × ℕ),
      TimedLog (Stop js.length) (Full js.length js.length)
        ((js.map fun batch => CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum)
        ((js.mapM (passBatch K circuits settings opened ctx parameter)).run st).run.run
  | [], st => by
    simp only [List.mapM_nil, StateT.run_pure, run_recPure, List.map_nil, List.sum_nil, List.length_nil]
    exact TimedLog.done _ ⟨rfl, rfl, rfl⟩
  | jobs :: js, st => by
    rw [List.mapM_cons, StateT.run_bind, List.map_cons, List.sum_cons, List.length_cons]
    refine timedLog_recBind (a₂ := js.length) (s₂ := js.length) (o₂ := js.length)
      (timedLog_passBatch K circuits settings opened hopen ctx parameter jobs st) (fun c => ?_)
      (by omega) (by omega) (by omega) (by omega)
    rw [StateT.run_bind, ← Nat.add_zero (List.sum _)]
    refine timedLog_recBind (a₂ := 0) (s₂ := 0) (o₂ := 0) (n := 0)
      (timedLog_passBatches opened hopen ctx parameter js c.2) (fun q => ?_) (le_refl _) (by omega) (by omega)
      (by omega)
    rw [StateT.run_pure, run_recPure]
    exact TimedLog.done _ ⟨rfl, rfl, rfl⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A timed recorded program with its record dropped takes at most its rounds. -/
theorem within_of_timedLog {β : Type} {A B : Option β × Record C E → Prop} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option β × Record C E)} (h : TimedLog A B n p) :
    Fuel.Within n (Prod.fst <$> p) := by
  induction h with
  | stop n x _ => exact Fuel.Within.ret n x.1
  | done x _ => exact Fuel.Within.ret 0 x.1
  | queryLocal n q k _ ih => exact Fuel.Within.queryLocal n q _ ih
  | round n out k _ ih => exact Fuel.Within.round n out _ ih

omit [Fintype E] [DecidableEq E] in
/-- One ceremony with the record of a pass takes the rounds of the ceremony, for an opened sharing
with no round. An abort keeps at most one opening for each batch, and a result has one start and
one opening for each batch. -/
theorem timedLog_passRun (opened : Opened C E) (hopen : ∀ b k, Timed 0 (opened b k).run) (j : C.Party)
    (keys : Keys C) (jobs : List Job) (st : ℕ × ℕ) :
    TimedLog (Stop (chunks settings.batchSize jobs).length)
      (Full (chunks settings.batchSize jobs).length (chunks settings.batchSize jobs).length)
      (CheckTiming.ceremonyRounds circuits settings keys.parameter jobs)
      ((passRun K circuits settings opened j keys jobs).run st).run.run := by
  simp only [passRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
  unfold CheckTiming.ceremonyRounds
  refine timedLog_lift_bind (timed_pair (timed_prssSetup j) st) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  simp only [batched, StateT.run_bind]
  rw [← Nat.add_zero (List.sum _)]
  refine timedLog_recBind (a₂ := 0) (s₂ := 0) (o₂ := 0)
    (timedLog_passBatches K circuits settings opened hopen ⟨j, keys, p.1⟩ keys.parameter _ p.2) (fun q => ?_) le_rfl
    (by omega) (by omega) (by omega)
  rw [StateT.run_pure, run_recPure]
  exact TimedLog.done _ ⟨rfl, rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
theorem runWithin_passRun (opened : Opened C E) (hopen : ∀ b k, Timed 0 (opened b k).run) (j : C.Party)
    (keys : Keys C) (jobs : List Job) :
    Fuel.RunWithin (CheckTiming.ceremonyRounds circuits settings keys.parameter jobs)
      (dropRecS (passRun K circuits settings opened j keys jobs)) := fun st =>
  within_of_timedLog (timedLog_passRun K circuits settings opened hopen j keys jobs st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The ceremonies of a bottom tree from a given randomizer take at most the rounds of the first run
and the most rounds of the second run over all encodings. -/
theorem runWithin_bottomOutputWith
    (lift : ∀ {β : Type}, OracleComp HashSpec β → StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), Fuel.RunWithin 0 (lift oa)) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (b : Fin (2 ^ layerHeight))
    (a c : ℕ) (hfirst : Fuel.RunWithin a (run (bottomJobs b)))
    (hsecond : ∀ encoding, Fuel.RunWithin c (run (signJobs b encoding))) (top : TopTree) (randomizer : Randomizer) :
    Fuel.RunWithin (a + c) (bottomOutputWith lift parameter run top b randomizer) := by
  refine Fuel.RunWithin.bind hfirst fun o => ?_
  rcases o with _ | outputs
  · exact (Fuel.runWithin_pure _).mono (Nat.zero_le _)
  refine (Fuel.RunWithin.bind (hlift _) fun root => ?_).mono (Nat.zero_add c).le
  refine (Fuel.RunWithin.bind (hlift _) fun digest => ?_).mono (Nat.zero_add c).le
  rcases Codeword.decode digest with _ | encoding
  · exact (Fuel.runWithin_pure _).mono (Nat.zero_le _)
  refine (Fuel.RunWithin.bind (n := 0) (hsecond encoding) fun o' => ?_).mono (by omega)
  rcases o' with _ | values
  · exact Fuel.runWithin_pure _
  refine Fuel.RunWithin.bind (m := 0) (n := 0) (hlift _) fun path => ?_
  refine Fuel.RunWithin.bind (m := 0) (n := 0) (hlift _) fun topRoot => ?_
  split <;> exact Fuel.runWithin_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem within_run'_bind {x : StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option TreeOutput)} {a n : ℕ}
    (hx : Fuel.RunWithin a x) (k : Option TreeOutput → PartyM C E RealSpec TreeOutput)
    (hk : ∀ o, Fuel.Within 0 (k o).run) (hle : a ≤ n) : Fuel.Within n (x.run' (0, 0) >>= k).run := by
  have h : Fuel.Within a (x.run' (0, 0)).run := by
    rw [StateT.run'_eq, map_eq_bind_pure_comp, ← Nat.add_zero a]
    exact (hx (0, 0)).bind fun p => Fuel.Within.ret 0 (some p.1)
  exact ((Fuel.Within.bind h hk).mono (by omega))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem within_dropRec_failure : Fuel.Within 0 (dropRec (failure : RecM C E TreeOutput)).run := by
  rw [dropRec_failure]
  exact Fuel.Within.ret 0 none

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem within_dropRec_pure (output : TreeOutput) :
    Fuel.Within 0 (dropRec (pure output : RecM C E TreeOutput)).run := by
  rw [MonadHom.mmap_pure]
  exact Fuel.Within.ret 0 (some output)

omit [Fintype E] [DecidableEq E] in
/-- The program of an operator in a run of a tree with the record of a pass takes at most `treeFuel`
rounds, for each randomizer and an opened sharing with no round. -/
theorem within_passTree (opened : Opened C E) (hopen : ∀ b k, Timed 0 (opened b k).run)
    (randomizer : Option Randomizer) (j : C.Party) (operator : OperatorState C) (tree : Tree) :
    Fuel.Within (treeFuel circuits settings)
      (Prod.fst <$> (passTree K circuits settings opened randomizer j operator tree).run.run) := by
  have hlift : ∀ {β : Type} (oa : OracleComp HashSpec β),
      Fuel.RunWithin 0 (StateT.lift (oracleStep (tweakable oa)) : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) :=
    fun oa => Fuel.RunWithin.of_runTimed (RunTimed.lift (timed_oracleStep _))
  change Fuel.Within _ (dropRec (passTree K circuits settings opened randomizer j operator tree)).run
  cases tree with
  | top =>
    unfold passTree
    rcases hk : operator.keys with _ | keys
    · rw [dropRec_failure]
      exact Fuel.Within.ret _ none
    rw [MonadHom.mmap_bind, dropRec_run', monadHom_ceremonyOutput]
    simp only [dropRecS_liftS]
    refine within_run'_bind ?_ _ (fun o => by
      rcases o with _ | output
      · exact within_dropRec_failure
      · exact within_dropRec_pure output) (topFuel circuits settings keys.parameter)
    exact Fuel.runWithin_ceremonyOutput_top (fun oa => StateT.lift (oracleStep (tweakable oa))) (fun oa => hlift oa)
      keys.parameter (fun js => dropRecS.toFun _ (passRun K circuits settings opened j keys js)) _
      (runWithin_passRun K circuits settings opened hopen j keys topJobs) emptyTop
  | bottom b =>
    unfold passTree
    rcases hk : operator.keys with _ | keys
    · rw [dropRec_failure]
      exact Fuel.Within.ret _ none
    rcases ht : operator.top with _ | top
    · rw [dropRec_failure]
      exact Fuel.Within.ret _ none
    have hfuel := bottomFuel circuits settings keys.parameter b fun _ => digit 0
    have hsecond : ∀ encoding, Fuel.RunWithin (treeFuel circuits settings -
        CheckTiming.ceremonyRounds circuits settings keys.parameter (bottomJobs b))
        (dropRecS (passRun K circuits settings opened j keys (signJobs b encoding))) := fun encoding =>
      (runWithin_passRun K circuits settings opened hopen j keys _).mono (by
        have := bottomFuel circuits settings keys.parameter b encoding
        omega)
    rcases randomizer with _ | r
    · rw [MonadHom.mmap_bind, dropRec_run', monadHom_ceremonyOutput]
      simp only [dropRecS_liftS]
      refine within_run'_bind (a := CheckTiming.ceremonyRounds circuits settings keys.parameter (bottomJobs b) +
        (treeFuel circuits settings - CheckTiming.ceremonyRounds circuits settings keys.parameter (bottomJobs b)))
        ?_ _ (fun o => by
      rcases o with _ | output
      · exact within_dropRec_failure
      · exact within_dropRec_pure output) ?_
      exact Fuel.runWithin_ceremonyOutput_bottom (fun oa => StateT.lift (oracleStep (tweakable oa))) (fun oa => hlift oa)
        keys.parameter (fun js => dropRecS.toFun _ (passRun K circuits settings opened j keys js)) b _ _
        (runWithin_passRun K circuits settings opened hopen j keys (bottomJobs b)) hsecond top
      omega
    · rw [MonadHom.mmap_bind, dropRec_run', monadHom_bottomOutputWith]
      simp only [dropRecS_liftS]
      refine within_run'_bind (a := CheckTiming.ceremonyRounds circuits settings keys.parameter (bottomJobs b) +
        (treeFuel circuits settings - CheckTiming.ceremonyRounds circuits settings keys.parameter (bottomJobs b)))
        ?_ _ (fun o => by
      rcases o with _ | output
      · exact within_dropRec_failure
      · exact within_dropRec_pure output) ?_
      exact runWithin_bottomOutputWith (fun oa => StateT.lift (oracleStep (tweakable oa))) (fun oa => hlift oa)
        keys.parameter (fun js => dropRecS.toFun _ (passRun K circuits settings opened j keys js)) b _ _
        (runWithin_passRun K circuits settings opened hopen j keys (bottomJobs b)) hsecond top r
      omega

end Fuel

section Real

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The opened sharing of a real run or of an emulated run. -/
def RealOpened (D : C.Coalition) (opened : Opened C E) : Prop :=
  opened = plainShares ∨ ∃ (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))), opened = shiftedShares circuits D parameter seeds openings

/-- The fuel bound. In a recorded run of a tree with a real form of the opened sharing, from
consistent honest keys, each honest operator is done at the end. -/
def PassDone : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (opened : Opened C E)
    (randomizer : Option Randomizer) (operators : C.Party → OperatorState C) (tree : Tree) (state : net.State)
    (world : StreamState C), RealOpened circuits D opened → seedsDiffer D (fun i => (operators i).keys) = false →
    ∀ r ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        ([] : Record C E) (treeFuel circuits settings) state fun i =>
          (passTree K circuits settings opened randomizer i (operators i) tree).run.run)).run world),
      ∀ i, i ∉ D.1 → (r.1.2 i).isDone

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Both real forms of the opened sharing make no round. -/
theorem timed_realOpened (D : C.Coalition) (opened : Opened C E) (h : RealOpened circuits D opened) :
    ∀ b k, Timed 0 (opened b k).run := by
  rcases h with rfl | ⟨parameter, seeds, openings, rfl⟩
  · exact fun b _ => timed_pure b.v'
  · exact fun b k => Timed.oracleStep_bind 0 _ _ fun _ => timed_pure _

omit [Fintype E] [DecidableEq E] in
/-- `PassDone`. Both real forms of the opened sharing make no round, so `treeFuel` covers each honest
program (`within_passTree`). -/
theorem passDone : PassDone prims K circuits settings := by
  intro D net opened randomizer operators tree state world hreal _ r hr
  exact Fuel.executePhaseR_done D net noFunctionality ([] : Record C E) _ _ le_rfl state _
    (fun i _ => within_passTree K circuits settings opened (timed_realOpened circuits D opened hreal) randomizer i
      (operators i) tree) r.1 (mem_support_phase prims D _ world r hr)

end Real

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passDone
