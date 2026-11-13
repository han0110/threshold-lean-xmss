import ThresholdLeanXmssSecurity.Proof.LifetimePrecomputeSwap
import ThresholdLeanXmssSecurity.Proof.LifetimeSlotQuiet
import ThresholdLeanXmssSecurity.Proof.LifetimeTableReplay

/-!
# Precomputing the final lifetime dealer table

Private dealing samples move before the keygen simulator. A separated dealer-table
prefix is then observationally inert for the complete keygen and signing continuation.
The supported table replays the original final-world tail with its full physical state.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeForgerPrecompute

open LifetimeHybridOrder LifetimeSlots LifetimeSlotTransport

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

variable {C : Committee} {E : Type}

/-- A fixed dealing keeps exactly the ideal functionality's receiver selection. -/
theorem idealExecution_dealtKeygen {σ : Type} (D : C.Coalition)
    (S : Simulator (C := C) (WorldSpec C) Unit
      (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) σ)
    (d : LifetimeBridge.Dealing C) (x : C.Party → Unit) (z : Aux) :
    idealExecution (fun oa => oa) D (dealtKeygen d) S x z = (do
      let st ← S.start (corruptInputs D x) z
      let (st, receivers) ← S.answer st (d.1, fun i => if i ∈ D.1 then some (d.2.2 i) else none)
      let out ← S.output st
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ receivers then some (d.2.2 i) else none)) := by
  unfold idealExecution dealtKeygen
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro st
  have hleak {σ' L R : Type}
      (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ' (OracleComp (WorldSpec C))))
      (l : L) : simulateQ impl (leak (C := C) (R := R) l) = impl (.inr l) := by
    unfold leak
    exact (simulateQ_query _ _).trans (id_map _)
  rw [hleak]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  change ((S.answer st (d.1, fun i => if i ∈ D.1 then some (d.2.2 i) else none) >>=
    fun p => pure (p.2, p.1)) >>= fun p => S.output p.2 >>= fun out =>
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ p.1 then some (d.2.2 i) else none)) = _
  simp only [bind_assoc, pure_bind]

/-- A world-level prefix has no private-stream or writer effect when lifted into the emulation. -/
theorem emulationGame_lift_bind {α : Type} (p : OracleComp (WorldSpec C) α)
    (f : α → EmulationM C Bool) :
    emulationGame (StateT.lift (liftM p) >>= f) = p >>= fun a => emulationGame (f a) := by
  simp only [emulationGame, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    WriterT.run_bind, WriterT.run_liftM,
    bind_map_left, map_bind, Functor.map_map]

/-- The dealing may be sampled before the independent simulator start, including the final cache. -/
theorem keygen_sample_first {σ α : Type} (prims : Primitives) (D : C.Coalition)
    (S : Simulator (C := C) (WorldSpec C) Unit
      (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) σ)
    (x : C.Party → Unit) (z : Aux)
    (post : σ × (C.Party → Option (Keys C)) → OracleComp (WorldSpec C) α)
    (c : HashCache C) :
    𝒟[(simulateQ (worldAnswer prims) (idealExecution (fun p => p) D Fkeygen S x z >>= post)).run c] =
    𝒟[(simulateQ (worldAnswer prims) (do
      let d ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let r ← idealExecution (fun p => p) D (dealtKeygen d) S x z
      post r)).run c] := by
  rw [idealExecution_Fkeygen]
  simp only [idealExecution_dealtKeygen, bind_assoc]
  have hc := (commutes_private_stateT (prawnsKeyGen (C := C))
    (simulateQ (worldAnswer prims) (S.start (corruptInputs D x) z))).symm
  have he := hc.bind (fun st d => simulateQ (worldAnswer prims) (do
    let (st, receivers) ← S.answer st (d.1, fun i => if i ∈ D.1 then some (d.2.2 i) else none)
    let out ← S.output st
    post (out, fun i => if i ∉ D.1 ∧ i ∈ receivers then some (d.2.2 i) else none))) c
  simpa only [simulateQ_bind, simulateQ_pure, simulateQ_world_sample, bind_assoc, pure_bind] using he

/-- Mapping a Boolean observation commutes with erasing the emulation's private state. -/
theorem emulationGame_map {α : Type} (f : α → Bool) (p : EmulationM C α) :
    emulationGame (f <$> p) = f <$> ((fun r => r.1.1) <$> (p.run ∅).run) := by
  simp only [emulationGame, StateT.run_map, WriterT.run_map, Functor.map_map]

/-- World evaluation of an emulation is its full-state evaluator followed by output projection. -/
theorem emulationGame_eval (prims : Primitives) (p : EmulationM C Bool) (c : HashCache C) :
    (simulateQ (worldAnswer prims) (emulationGame p)).run' c =
      (evalEmulation prims p).run' (∅, c, []) := by
  simp only [emulationGame, StateT.run'_eq, evalEmulation, StateT.run_mk,
    simulateQ_map, StateT.run_map, Functor.map_map]

/-- World evaluation retains the chosen output projection. -/
theorem worldRun_map (prims : Primitives) {α β : Type} (f : α → β)
    (p : OracleComp (WorldSpec C) α) (c : HashCache C) :
    f <$> (simulateQ (worldAnswer prims) p).run' c =
      (simulateQ (worldAnswer prims) (f <$> p)).run' c := by
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

section Assembly

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The actual final-mode tail after the keygen output. -/
def worldTail (state : A.keygen.State) (outputs : C.Party → Option (Keys C)) :
    OracleComp (WorldSpec C) Bool :=
  emulationGame (slotRun K circuits settings attempts (worldEnv D circuits settings)
    (worldMode attempts (lifetimeRuns attempts) false) D A state outputs)

/-- Fixed-dealing keygen followed by the actual final-mode tail. -/
def dealtWorld (d : LifetimeBridge.Dealing C) : OracleComp (WorldSpec C) Bool := do
  let (state, outputs) ← idealExecution (fun p => p) D (dealtKeygen d)
    (keygenSimulator D A.keygen) (fun _ => ()) []
  worldTail K circuits settings attempts D A state outputs

/-- The actual dealer prefix, retained only in the hash cache for the original tail. -/
def worldPrecomputeGame : OracleComp (WorldSpec C) Bool := do
  let d ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
  let _ ← free (liftComp (LifetimeForgerReplay.dealerTables circuits settings d.1
    (honestSeeds D d.2.2)) (LocalSpec C))
  dealtWorld K circuits settings attempts D A d

/-- Every part of the fixed-dealing continuation excludes other-domain programming. -/
theorem dealtWorld_otherProgram (d : LifetimeBridge.Dealing C) :
    IsQueryBoundP (dealtWorld K circuits settings attempts D A d) LifetimeJointLink.OtherProgram 0 := by
  apply LifetimeKeygenPrograms.qb0_bind'
  · exact LifetimeSlotQuiet.dealtKeygen_otherProgram D A.keygen d (fun _ => ()) []
  · rintro ⟨state, outputs⟩
    apply LifetimeSlotQuiet.otherProgram_of_quiet
    apply LifetimeKeygenPrograms.emulationGame_quiet
    exact LifetimeSlotQuiet.slotRun_quiet K circuits settings attempts D A _ state outputs

omit [Fintype E] [DecidableEq E] in
/-- The generic final slot game is the keygen program followed by its unchanged tail. -/
theorem genericSlotGame_split :
    genericSlotGame K circuits settings attempts D A (lifetimeRuns attempts) false =
      idealExecution (fun p => p) D Fkeygen (keygenSimulator D A.keygen) (fun _ => ()) [] >>=
        fun r => worldTail K circuits settings attempts D A r.1 r.2 := by
  exact emulationGame_lift_bind _ _

/-- Sampling first and inserting the separated table prefix preserves the final slot output law. -/
theorem slot_eq_worldPrecompute (prims : Primitives) :
    𝒟[(simulateQ (worldAnswer prims)
      (slotGame K settings attempts D A (lifetimeRuns attempts) false circuits)).run' ∅] =
    𝒟[(simulateQ (worldAnswer prims)
      (worldPrecomputeGame K circuits settings attempts D A)).run' ∅] := by
  rw [slotGame_eq_generic, genericSlotGame_split]
  have ha := keygen_sample_first prims D (keygenSimulator D A.keygen) (fun _ => ()) []
    (fun r => worldTail K circuits settings attempts D A r.1 r.2) ∅
  have hp := congrArg (fun d : SPMF (Bool × HashCache C) => Prod.fst <$> d) ha
  simp only [← evalDist_map, ← StateT.run'_eq] at hp
  refine hp.trans ?_
  simp only [worldPrecomputeGame, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply evalDist_bind_congr
  intro r hr
  have hg := LifetimePrecomputeSwap.evalDist_world_ghost prims
    (free (liftComp (LifetimeForgerReplay.dealerTables circuits settings r.1.1
      (honestSeeds D r.1.2.2)) (LocalSpec C)))
    (dealtWorld K circuits settings attempts D A r.1)
    (LifetimePrecomputeSwap.free_dealerTables_dealerQuery circuits settings _ _)
    (dealtWorld_otherProgram K circuits settings attempts D A r.1) r.2
  simpa only [dealtWorld, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] using hg.symm

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Every supported fixed-dealing keygen output has the functionality's receiver form. -/
theorem dealtKeygen_output (d : LifetimeBridge.Dealing C)
    (r : A.keygen.State × (C.Party → Option (Keys C)))
    (hr : r ∈ support (idealExecution (fun p => p) D (dealtKeygen d)
      (keygenSimulator D A.keygen) (fun _ => ()) [])) :
    ∃ receivers : Finset C.Party,
      r.2 = fun i => if i ∉ D.1 ∧ i ∈ receivers then some (d.2.2 i) else none := by
  rw [idealExecution_dealtKeygen] at hr
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨st, _, answer, _, out, _, rfl⟩ := hr
  exact ⟨answer.2, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The original and table tails agree after every supported surviving keygen delivery. -/
theorem slotRun_replay (prims : Primitives) (d : LifetimeBridge.Dealing C)
    (hd : d ∈ support (prawnsKeyGen (C := C)))
    (tables : Tree → Option TreeOutput × List (List (List Bit))) (c : HashCache C)
    (ht : LifetimeTableReplay.TableRuns prims circuits settings d.1
      (honestSeeds D d.2.2) tables c)
    (state : A.keygen.State) (outputs : C.Party → Option (Keys C))
    (hout : ∃ receivers : Finset C.Party,
      outputs = fun i => if i ∉ D.1 ∧ i ∈ receivers then some (d.2.2 i) else none)
    (w : WorldState C) (hw : c ≤ w.2.1) :
    (evalEmulation prims (slotRun K circuits settings attempts (worldEnv D circuits settings)
      (worldMode attempts (lifetimeRuns attempts) false) D A state outputs)).run' w =
    (evalEmulation prims (slotRun K circuits settings attempts
      (LifetimeForgerReplay.tableEnv circuits settings D tables)
      (worldMode attempts (lifetimeRuns attempts) false) D A state outputs)).run' w := by
  rw [slotRun_tail, LifetimeTableReplay.slotRun_table_tail]
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => rfl
  | some h =>
    dsimp only
    by_cases ready : ∀ i, i ∉ D.1 → (outputs i).isSome
    · rw [if_neg (not_not_intro ready), if_neg (not_not_intro ready)]
      let keys := fun i => (outputs i).getD default
      have hk : ∀ i, i ∉ D.1 → keys i = d.2.2 i := by
        obtain ⟨receivers, ho⟩ := hout
        simpa only [keys, ho] using LifetimeTableReplay.dealtKeygen_keys D d receivers
          (by simpa only [ho] using ready)
      have honest : h ∉ D.1 := of_decide_eq_true (List.find?_some (p := fun i : C.Party => decide (i ∉ D.1)) hh)
      have hparam : (keys h).parameter = d.1 := by
        rw [hk h honest]
        exact LifetimeTableReplay.prawnsKeyGen_parameter d hd h
      have hseeds := LifetimeTableReplay.honestSeeds_congr D keys d.2.2 hk
      have he := LifetimeTableReplay.tail_replay K circuits settings attempts D keys h tables
        prims d.1 (honestSeeds D d.2.2) c hparam hseeds honest ht
        (tailProgram A state (keys h).parameter) (initialSlot D, w)
        (LifetimeTableReplay.tableInv_initial tables D c w hw)
      have hp := congrArg (fun p : ProbComp (Bool × Physical C E) => Prod.fst <$> p) he
      rw [rawKernel_run, LifetimeTableReplay.tableKernel_run, evalSlot_output, evalSlot_output] at hp
      exact hp
    · rw [if_pos ready, if_pos ready]

/-- Fixed-dealing keygen followed by the exact table environment of the precompute game. -/
def tableWorld (d : LifetimeBridge.Dealing C)
    (tables : Tree → Option TreeOutput × List (List (List Bit))) : OracleComp (WorldSpec C) Bool := do
  let (state, outputs) ← idealExecution (fun p => p) D (dealtKeygen d)
    (keygenSimulator D A.keygen) (fun _ => ()) []
  emulationGame (slotRun K circuits settings attempts
    (LifetimeForgerReplay.tableEnv circuits settings D tables)
    (worldMode attempts (lifetimeRuns attempts) false) D A state outputs)

omit [Fintype E] [DecidableEq E] in
/-- The second projection of the actual precompute game keeps the full dealer table and tail. -/
theorem precomputeGame_win :
    Prod.snd <$> LifetimeForgerReplay.precomputeGame K circuits settings attempts D A = (do
      let d ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let tables ← free (liftComp (LifetimeForgerReplay.dealerTables circuits settings d.1
        (honestSeeds D d.2.2)) (LocalSpec C))
      tableWorld K circuits settings attempts D A d tables) := by
  unfold LifetimeForgerReplay.precomputeGame
  rw [← emulationGame_map]
  simp only [map_bind, map_pure]
  rw [emulationGame_lift_bind]
  apply bind_congr
  intro d
  change emulationGame (StateT.lift (liftM
    (free (liftComp (LifetimeForgerReplay.dealerTables circuits settings d.1
      (honestSeeds D d.2.2)) (LocalSpec C)))) >>= _) = _
  rw [emulationGame_lift_bind]
  apply bind_congr
  intro tables
  rw [emulationGame_lift_bind]
  simp only [tableWorld, bind_pure]

omit [Fintype E] [DecidableEq E] in
/-- A supported table precomputation replays through the actual following keygen and tail. -/
theorem dealtWorld_replay (prims : Primitives) (d : LifetimeBridge.Dealing C)
    (hd : d ∈ support (prawnsKeyGen (C := C)))
    (tables : Tree → Option TreeOutput × List (List (List Bit))) (c : HashCache C)
    (ht : LifetimeTableReplay.TableRuns prims circuits settings d.1
      (honestSeeds D d.2.2) tables c) :
    (simulateQ (worldAnswer prims) (dealtWorld K circuits settings attempts D A d)).run' c =
      (simulateQ (worldAnswer prims) (tableWorld K circuits settings attempts D A d tables)).run' c := by
  simp only [dealtWorld, tableWorld, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply bind_congr_of_forall_mem_support
  intro r hr
  have hout : r.1 ∈ support (idealExecution (fun p => p) D (dealtKeygen d)
      (keygenSimulator D A.keygen) (fun _ => ()) []) := by
    apply support_simulateQ_run'_subset (worldAnswer prims) _ c
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  have hg := (grows_worldAnswer prims).simulateQ _ _ _ hr
  have he := slotRun_replay K circuits settings attempts D A prims d hd tables c ht
    r.1.1 r.1.2 (dealtKeygen_output D A d r.1 hout) (∅, r.2, []) hg
  change (simulateQ (worldAnswer prims) (emulationGame _)).run' r.2 =
    (simulateQ (worldAnswer prims) (emulationGame _)).run' r.2
  rw [emulationGame_eval, emulationGame_eval]
  exact he

omit [Fintype E] [DecidableEq E] in
/-- Table replay identifies the ghost-prefix world with the actual precompute game's win. -/
theorem worldPrecompute_eq_precompute (prims : Primitives) :
    𝒟[(simulateQ (worldAnswer prims)
      (worldPrecomputeGame K circuits settings attempts D A)).run' ∅] =
    𝒟[Prod.snd <$> (simulateQ (worldAnswer prims)
      (LifetimeForgerReplay.precomputeGame K circuits settings attempts D A)).run' ∅] := by
  rw [worldRun_map, precomputeGame_win]
  simp only [worldPrecomputeGame, simulateQ_bind, simulateQ_world_sample, StateT.run'_eq,
    StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
  apply evalDist_bind_congr
  intro d hd
  simp only [simulateQ_free, simulateQ_localAnswer_liftComp]
  apply evalDist_bind_congr
  intro r hr
  have ht := LifetimeTableReplay.tableRuns_of_support prims circuits settings d.1
    (honestSeeds D d.2.2) hr
  have he := dealtWorld_replay K circuits settings attempts D A prims d hd r.1 r.2 ht
  simpa only [StateT.run'_eq] using congrArg evalDist he

omit [Fintype E] [DecidableEq E] in
/-- Erasing the lifetime counter retains both actual precompute outputs. -/
theorem precomputeRun_output (prims : Primitives) :
    LifetimeForgerReplay.precomputeRun prims K circuits settings attempts D A =
      (simulateQ (worldAnswer prims)
        (LifetimeForgerReplay.precomputeGame K circuits settings attempts D A)).run' ∅ := by
  simp only [LifetimeForgerReplay.precomputeRun, bind_pure_comp]
  exact fst_map_run_withAddCost _ _ _ _

/-- The final slot world's win probability is the actual precompute game's win probability. -/
theorem finalPrecompute (prims : Primitives) :
    LifetimeForgerReplay.FinalPrecompute prims K circuits settings attempts D A := by
  intro _ _
  unfold LifetimeO3Bridge.slotProbability
  rw [LifetimeO3Bridge.probability_lifetimeRun, accepts_eq_probOutput, precomputeRun_output]
  have he := (slot_eq_worldPrecompute K circuits settings attempts D A prims).trans
    (worldPrecompute_eq_precompute K circuits settings attempts D A prims)
  have hp := probEvent_congr_evalDist he (fun b => b = true)
  rw [probEvent_map (mx := (simulateQ (worldAnswer prims)
    (LifetimeForgerReplay.precomputeGame K circuits settings attempts D A)).run' ∅)
    (f := Prod.snd)] at hp
  simpa only [Function.comp_def, probEvent_eq_eq_probOutput] using congrArg ENNReal.toReal hp

end Assembly

end ThresholdLeanXmssSecurity.LifetimeForgerPrecompute

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.idealExecution_dealtKeygen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.idealExecution_dealtKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.keygen_sample_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.keygen_sample_first

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.dealtWorld_otherProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.dealtWorld_otherProgram

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.slot_eq_worldPrecompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.slot_eq_worldPrecompute

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.slotRun_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.slotRun_replay

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.precomputeGame_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.precomputeGame_win

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.dealtWorld_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.dealtWorld_replay

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.worldPrecompute_eq_precompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.worldPrecompute_eq_precompute

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.precomputeRun_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.precomputeRun_output

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.finalPrecompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerPrecompute.finalPrecompute
