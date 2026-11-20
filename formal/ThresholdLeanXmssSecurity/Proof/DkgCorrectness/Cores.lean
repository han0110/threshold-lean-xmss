import ThresholdLeanXmssSecurity.Proof.BatchCheck.Programs
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Walk

/-!
# The rounds of a batch and of a ceremony, and the abort after a partial output

`runTimed_realBatch_exact` and `runTimed_ceremonyRun_exact` give the exact round count of a batch and
of a ceremony from the public data, on each path that ends with no abort. `treeProgram_bottom` cuts
the program of a bottom tree at its second PRSS setup, and `timed_bottomHead` gives the round count
of the part before the cut. After a partial abort, when
each honest operator is done or at the first step of a program that starts with a round, each honest
operator at such a step ends with no output (`executeRounds_cut_noOutput`).
`startsWithRound_verify_output` gives one such program. `tupleInputs_batchTuples` states that the
tuples of one batch satisfy `TupleInputs`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace Fuel

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The bound of the program of a tree -/

section Program

variable {C : Committee} {E : Type}

variable [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- The rounds of the batches of `jobs`. -/
def batchesRounds (parameter : PublicParameter) (jobs : List Job) : ℕ :=
  ((chunks settings.batchSize jobs).map (batchRounds circuits settings.mode parameter)).sum

/-- A real ceremony on any keys takes one PRSS setup and its batches. -/
theorem runTimed_ceremonyRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    RunTimed (setupRounds + batchesRounds circuits settings keys.parameter jobs)
      (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
        StateT (ℕ × ℕ) (PartyM C E RealSpec) _) := fun st => by
  have heq : (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run st =
      prssSetup i >>= fun prss => ((chunks settings.batchSize jobs).mapM (realBatch K circuits settings.mode
        ⟨i, keys, prss⟩ keys.parameter)).run st >>= fun p =>
          pure (p.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], p.2) := by
    simp only [ceremonyRun, batched, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure]
    rfl
  rw [heq, batchesRounds, ← Nat.add_zero (List.sum _)]
  exact (timed_prssSetup i).bind fun prss =>
    (runTimed_batches K circuits settings.mode _ keys.parameter _ st).bind fun p => timed_pure _

end Program

end Fuel

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace CheckTiming

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## One batch -/

/-- The rounds of one batch of the circuits `cs` in `mode`. Each AND layer takes one reshare, then
`Rerand` and `OpenRep` take one round each. A check with a tuple takes one coin, two rounds for each
halving step and four for the randomization. A check of no tuple takes no round. -/
def exactBatchRounds (mode : ReshareMode) (cs : List Circuit) : ℕ :=
  depth cs * mode.rounds + 2 + (if tupleCount cs = 0 then 0 else 2 * halvings (tupleCount cs) + 5)

section Ceremony

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem batchRounds_eq_exact (mode : ReshareMode) (parameter : PublicParameter) (jobs : List Job) :
    batchRounds circuits mode parameter jobs = exactBatchRounds mode (jobs.map (circuits parameter ·.kind)) := by
  unfold batchRounds batchCount checkLabels exactBatchRounds
  split_ifs <;> omega

/-- A real batch takes `exactBatchRounds` rounds from each start of the counters. -/
theorem runTimed_realBatch_exact (mode : ReshareMode) (ctx : Context C) (parameter : PublicParameter)
    (jobs : List Job) :
    RunTimed (exactBatchRounds mode (jobs.map (circuits parameter ·.kind)))
      (realBatch K circuits mode ctx parameter jobs) :=
  (runTimed_realBatch K circuits mode ctx parameter jobs).of_eq
    (batchRounds_eq_exact circuits mode parameter jobs)

/-- The rounds of a ceremony of `jobs` under `parameter`, one PRSS setup and its batches. -/
def ceremonyRounds (parameter : PublicParameter) (jobs : List Job) : ℕ :=
  setupRounds + ((chunks settings.batchSize jobs).map fun batch =>
    exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum

/-- The jobs of the first ceremony of a tree. -/
def firstJobs : Tree → List Job
  | .top => topJobs
  | .bottom b => bottomJobs b

/-- The rounds of the first ceremony of a tree under `parameter`. -/
def firstRounds (parameter : PublicParameter) (tree : Tree) : ℕ :=
  ceremonyRounds circuits settings parameter (firstJobs tree)

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem batchesRounds_eq (parameter : PublicParameter) (jobs : List Job) :
    setupRounds + Fuel.batchesRounds circuits settings parameter jobs = ceremonyRounds circuits settings parameter jobs := by
  unfold Fuel.batchesRounds ceremonyRounds
  congr 2
  exact List.map_congr_left fun batch _ => batchRounds_eq_exact circuits settings.mode parameter batch

/-- A real ceremony of `jobs` on the keys `keys` takes `ceremonyRounds` rounds under the parameter of
`keys`, from each start of the counters. -/
theorem runTimed_ceremonyRun_exact (i : C.Party) (keys : Keys C) (jobs : List Job) :
    RunTimed (ceremonyRounds circuits settings keys.parameter jobs)
      (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
        StateT (ℕ × ℕ) (PartyM C E RealSpec) _) :=
  (Fuel.runTimed_ceremonyRun K circuits settings i keys jobs).of_eq
    (batchesRounds_eq circuits settings keys.parameter jobs)

/-- The first ceremony of a tree takes `firstRounds` rounds under the parameter of the keys. -/
theorem runTimed_firstCeremony (i : C.Party) (keys : Keys C) (tree : Tree) :
    RunTimed (firstRounds circuits settings keys.parameter tree)
      (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys
        (firstJobs tree) : StateT (ℕ × ℕ) (PartyM C E RealSpec) _) :=
  runTimed_ceremonyRun_exact K circuits settings i keys (firstJobs tree)

end Ceremony

/-! ## The cut of a bottom tree at its second PRSS setup -/

section BottomCut

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The first ceremony of bottom tree `b` and the local randomizer search, on the counters. It gives
the outputs of the first ceremony, the root of the bottom tree, the randomizer and the encoding. -/
def firstPart (i : C.Party) (keys : Keys C) (b : Fin (2 ^ layerHeight)) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit) × Digest × Randomizer × Encoding)) := do
  let some outputs ← ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys
      (bottomJobs b) | pure none
  let root ← StateT.lift (oracleStep (tweakable
    (merkleNode keys.parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)))
  let base ← StateT.lift (oracleStep (tweakable (truncateHash <$> Verification.oracleHashWithHash
    (randomizerInput keys.parameter topLayer (topKey b) (bRho b outputs) (littleEndianBytes 16 root)))))
  let some (randomness, encoding) ← StateT.lift (oracleStep (tweakable
      (grind keys.parameter topLayer (topKey b) (littleEndianBytes 16 root) base randomizerAttemptLimit 0))) | pure none
  pure (some (outputs, root, randomness, encoding))

/-- The signature ceremony of bottom tree `b` at the encoding of `x` and the local end, on the
counters. -/
def secondPart (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option TreeOutput) := do
  let some values ← ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys
      (signJobs b x.2.2.2) | pure none
  let path ← StateT.lift (oracleStep (tweakable (merklePath keys.parameter topLayer top.chainEnd (topKey b))))
  let signature : LayerSignature := ⟨x.2.2.1, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← StateT.lift (oracleStep (tweakable
    (Verification.layerRootWithHash keys.parameter topLayer (topKey b) (littleEndianBytes 16 x.2.1) signature)))
  if topRoot ≠ some top.root then pure none else
  pure (some (.bottom ⟨bCpk b x.1, bCommitment b x.1, x.2.1, signature⟩))

omit [Fintype E] [DecidableEq E] in
theorem ceremonyOutput_bottom (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec)) (fun oa => StateT.lift (oracleStep (tweakable oa)))
        keys.parameter (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys)
        top (.bottom b) =
      firstPart K circuits settings i keys b >>= fun o => o.elim (pure none) (secondPart K circuits settings i keys top b) := by
  simp only [ceremonyOutput, firstPart, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with _ | outputs
  · simp only [pure_bind, Option.elim]
  · simp only [bind_assoc, bCpk, bRho, bottomKeys]
    refine bind_congr fun root => bind_congr fun base => bind_congr fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · simp only [pure_bind, Option.elim]
    · simp only [pure_bind, Option.elim, secondPart]
      rfl

/-- The first ceremony and the local search take the rounds of the first ceremony. The search makes
local calls only. -/
theorem runTimed_firstPart (i : C.Party) (keys : Keys C) (b : Fin (2 ^ layerHeight)) :
    RunTimed (firstRounds circuits settings keys.parameter (.bottom b)) (firstPart K circuits settings i keys b) := by
  unfold firstPart
  refine ((runTimed_firstCeremony K circuits settings i keys (.bottom b)).bind (n := 0) fun o => ?_).of_eq
    (Nat.add_zero _)
  rcases o with _ | outputs
  · exact runTimed_pure _
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun root => ?_
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun base => ?_
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩
  · exact runTimed_pure _
  · exact runTimed_pure _

/-- The program of operator `i` for bottom tree `b` up to its second PRSS setup. It is the first
ceremony and the local randomizer search. An operator without keys or without a top tree, or with
no encoding, aborts. -/
def bottomHead (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) :
    PartyM C E RealSpec ((List (List Bit) × Digest × Randomizer × Encoding) × (ℕ × ℕ)) :=
  match operator.keys, operator.top with
  | some keys, some _ => (firstPart K circuits settings i keys b).run (0, 0) >>= fun p =>
      p.1.elim failure fun x => pure (x, p.2)
  | _, _ => failure

/-- The program of operator `i` for bottom tree `b` from its second PRSS setup, after the result `r`
of `bottomHead`. -/
def bottomTail (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (r : (List (List Bit) × Digest × Randomizer × Encoding) × (ℕ × ℕ)) : PartyM C E RealSpec TreeOutput :=
  match operator.keys, operator.top with
  | some keys, some top => (secondPart K circuits settings i keys top b r.1).run r.2 >>= fun p =>
      p.1.elim failure pure
  | _, _ => failure

omit [Fintype E] [DecidableEq E] in
/-- The program of a bottom tree is `bottomHead` and then `bottomTail`. -/
theorem treeProgram_bottom (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) :
    treeProgram K circuits settings i operator (.bottom b) =
      bottomHead K circuits settings i operator b >>= bottomTail K circuits settings i operator b := by
  unfold treeProgram bottomHead bottomTail
  rcases operator.keys with _ | keys <;> rcases operator.top with _ | top <;> simp only [failure_bind]
  unfold newTree
  rw [ceremonyOutput_bottom]
  simp only [StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | x, st⟩
  · simp [Option.elim]
  · simp only [Option.elim, pure_bind, bind_map_left]
    refine bind_congr fun q => ?_
    rcases q with ⟨_ | out, st'⟩ <;> rfl

/-- The part before the second PRSS setup takes `firstRounds … (.bottom b)` rounds under the
parameter of the keys of the operator. -/
theorem timed_bottomHead (parameter : PublicParameter) (i : C.Party) (operator : OperatorState C)
    (b : Fin (2 ^ layerHeight)) (h : ∀ keys, operator.keys = some keys → keys.parameter = parameter) :
    Timed (firstRounds circuits settings parameter (.bottom b)) (bottomHead K circuits settings i operator b).run := by
  unfold bottomHead
  split
  · rename_i keys _ hk _
    rw [← h keys hk, ← Nat.add_zero (firstRounds circuits settings keys.parameter (.bottom b))]
    refine (runTimed_firstPart K circuits settings i keys b (0, 0)).bind fun p => ?_
    rcases p with ⟨_ | x, st⟩
    · exact timed_failure 0
    · exact timed_pure _
  · exact timed_failure _

end BottomCut

end CheckTiming

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The round after a partial abort -/

/-- A step that waits in a round and aborts on each inbox with an abort frame. -/
def RejectsAbort {ι α : Type} {G : OracleSpec ι} (step : Step C E G α) : Prop :=
  ∃ outbox resume, step = .wait outbox resume ∧
    ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advance (resume inbox) = pure (.done none)

section Round

variable {m : Type → Type} [Monad m] [LawfulMonad m] {I O L R Ia α : Type}

/-- The round after a partial abort. An honest operator is at `.done none`, and each other honest
operator is done or waits in a round that rejects an abort frame. The adversary sees the round, and
each operator then ends at its output. So each honest operator that waits ends with no output. -/
theorem stepRound_abort (Ro : Roles C m) (hpure : ∀ {β : Type} (x : β), Ro.honest (pure x) = pure x)
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (h : ∀ i ∉ D.1, (steps i).isDone ∨ RejectsAbort (steps i)) :
    stepRound Ro D A F st steps =
      (fun r => (r.1, fun j => Step.done (steps j).output, r.2)) <$>
        Ro.adversary (A.round st fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) := by
  obtain ⟨a, ha, hadone⟩ := hab
  have hnocall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, hi, hc⟩, -⟩
    rcases h i hi with hd | ⟨outbox, resume, hw, -⟩
    · cases hs : steps i <;> simp_all [Step.isDone, Step.callInput]
    · simp [hw, Step.callInput] at hc
  unfold stepRound
  rw [ite_eq_right hnocall, map_eq_bind_pure_comp]
  refine bind_congr fun ⟨state, sent⟩ => ?_
  dsimp only
  rw [stages_sequenceFin_eq_pure _ (fun j => Step.done (steps j).output) (fun j => ?_), pure_bind]
  · rfl
  rcases hs : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · rfl
  · by_cases hj : j ∈ D.1
    · simp [hj, Step.output]
    · simp only [hj, ite_false, Step.output]
      rcases h j hj with hd | ⟨outbox', resume', hw, hres⟩
      · simp [hs, Step.isDone] at hd
      · rw [hs] at hw
        cases hw
        rw [hres _ ⟨a, by simp [ha, hadone]⟩, hpure]
  · rfl

/-- The rest of the run after a partial abort, for each fuel. If each honest operator is done, the
run stops. Otherwise the adversary sees one round, and each operator ends at the output of its
step. -/
theorem executeRounds_abort (Ro : Roles C m) (hpure : ∀ {β : Type} (x : β), Ro.honest (pure x) = pure x)
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (h : ∀ i ∉ D.1, (steps i).isDone ∨ RejectsAbort (steps i)) :
    executeRounds Ro D A F (fuel + 1) st steps =
      if ∀ i ∉ D.1, (steps i).isDone then pure (st, fun j => (steps j).output) else
        (fun r => (r.1, fun j => (steps j).output)) <$>
          Ro.adversary (A.round st fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) := by
  rw [executeRounds]
  split_ifs with hdone
  · rfl
  rw [stepRound_abort Ro hpure D A F st steps hab h, map_eq_bind_pure_comp, bind_assoc,
    map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  rw [Function.comp_apply, pure_bind, Function.comp_apply]
  exact executeRounds_allDone D A F Ro fuel r.1 _ fun _ => trivial

/-- The honest roles of the real game keep `pure`. -/
theorem worldRoles_honest_pure {β : Type} (x : β) : (worldRoles (C := C)).honest (pure x) = pure x := by
  simp [worldRoles, free]

/-- The rest of the run after a partial abort in the real game, under each handler of `WorldSpec`
with a state and for each fuel. Each operator ends at the output of its step at the cut, so each
honest operator that waits ends with no output. -/
theorem executeRounds_abort_support {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (h : ∀ i ∉ D.1, (steps i).isDone ∨ RejectsAbort (steps i)) (s : σ)
    (z : (A.State × (C.Party → Option α)) × σ)
    (hz : z ∈ support ((simulateQ impl (executeRounds worldRoles D A F fuel st steps)).run s)) :
    z.1.2 = fun j => (steps j).output := by
  cases fuel with
  | zero =>
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | succ fuel =>
    rw [executeRounds_abort worldRoles (fun x => worldRoles_honest_pure x) D A F fuel st steps hab h] at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    · simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      rfl

end Round

/-! ## Programs that reach a round -/

section Programs

variable {ι : Type} {G : OracleSpec ι}

/-- The local work of the program stops at an abort or at a round. After the round, the program aborts
at once if the inbox holds an abort frame. -/
def StartsWithRound {α : Type} (p : PartyM C E G α) : Prop :=
  ∀ step ∈ support (advance p.run), step = .done none ∨
    ∃ outbox resume, step = .wait outbox resume ∧
      ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advance (resume inbox) = pure (.done none)

/-- A round with `exchange` aborts on an abort frame, so it starts each continuation. -/
theorem startsWithRound_exchange_bind {α : Type} (outbox : Mail C E) (f : Mail C E → PartyM C E G α) :
    StartsWithRound (exchange outbox >>= f) := by
  intro step hs
  rw [advance_exchange_bind, support_pure, Set.mem_singleton_iff] at hs
  subst hs
  refine Or.inr ⟨outbox, _, rfl, fun inbox ⟨k, hk⟩ => ?_⟩
  have hany : (C.parties.any fun j => Msg.isAbort (inbox j)) = true :=
    List.any_eq_true.2 ⟨k, List.mem_finRange k, by simp [hk, Msg.isAbort]⟩
  simp only [exchangeResume, hany, ite_true, advance_pure]

/-- Local work before the round keeps the property. -/
theorem startsWithRound_oracleStep_bind {α β : Type} (oa : OracleComp (RoSpec C) β)
    (f : β → PartyM C E G α) (h : ∀ b, StartsWithRound (f b)) :
    StartsWithRound (oracleStep oa >>= f) := by
  intro step hs
  rw [advance_oracleStep_bind, mem_support_bind_iff] at hs
  obtain ⟨b, -, hb⟩ := hs
  exact h b step hb

/-- Any continuation after the program keeps the property. -/
theorem startsWithRound_bind {α β : Type} (p : PartyM C E G α) (k : α → PartyM C E G β)
    (h : StartsWithRound p) : StartsWithRound (p >>= k) := by
  intro step hs
  rw [advance_bind, mem_support_bind_iff] at hs
  obtain ⟨s, hs, hstep⟩ := hs
  rcases h s hs with rfl | ⟨outbox, resume, rfl, hres⟩
  · simp only [continueStep, support_pure, Set.mem_singleton_iff] at hstep
    exact Or.inl hstep
  · simp only [continueStep, support_pure, Set.mem_singleton_iff] at hstep
    refine Or.inr ⟨outbox, _, hstep, fun inbox hk => ?_⟩
    rw [advance_bind]
    change advance (resume inbox) >>= continueStep k = _
    rw [hres inbox hk, pure_bind]
    rfl

/-- Any continuation after a program on the run state keeps the property. -/
theorem startsWithRound_run_bind {α β : Type} (p : RunM C E G α) (k : α → RunM C E G β) (st : RunState C)
    (h : StartsWithRound (p.run st)) : StartsWithRound ((p >>= k).run st) := by
  rw [StateT.run_bind]
  exact startsWithRound_bind _ _ h

/-- Each honest step of a cut whose programs start with a round is done or rejects an abort frame. -/
theorem isDone_or_rejectsAbort {α : Type} (p : PartyM C E G α) (h : StartsWithRound p)
    (step : Step C E G α) (hs : step ∈ support (advance p.run)) : step.isDone ∨ RejectsAbort step := by
  rcases h step hs with rfl | hw
  · exact Or.inl trivial
  · exact Or.inr hw

end Programs

/-! ## The forms of the opening and of the check -/

section Forms

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C) {ι : Type} {G : OracleSpec ι}

/-- `OpenSh` starts with its round. -/
theorem startsWithRound_openSh (v : ℕ → E) (count : ℕ) : StartsWithRound (openSh (G := G) K ctx v count) :=
  startsWithRound_exchange_bind _ _

/-- `OpenRep` makes local hash calls and then sends its round. -/
theorem startsWithRound_openRep (v : Shares C Bit) (count : ℕ) :
    StartsWithRound (openRep (G := G) K ctx v count) :=
  startsWithRound_oracleStep_bind _ _ fun _ => startsWithRound_exchange_bind _ _

/-- The coin key of the real check draws its PRSS outputs and then sends the round of `OpenSh`. -/
theorem startsWithRound_coinKey (st : RunState C) :
    StartsWithRound ((coinKey (G := G) K (realCheckBuildingBlocks K ctx)).run st) := by
  unfold coinKey
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  refine startsWithRound_run_bind _ _ _ ?_
  change StartsWithRound ((prssRandomness ctx (elementCodec K) 1 2 >>= fun r => coinWith K ctx r 2).run st)
  rw [prssRandomness_run]
  refine startsWithRound_oracleStep_bind _ _ fun o => ?_
  unfold coinWith
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  exact startsWithRound_bind _ _ (startsWithRound_openSh K ctx _ _)

/-- The check of a batch with a positive count starts with the round of its first coin. -/
theorem startsWithRound_check (tuples : List (Tuple C)) (hcount : (tuples.map (·.count)).sum ≠ 0)
    (st : RunState C) :
    StartsWithRound ((check (G := G) K ctx (realCheckBuildingBlocks K ctx) tuples).run st) := by
  unfold check
  dsimp only
  rw [ite_eq_right hcount]
  exact startsWithRound_run_bind _ _ _ (startsWithRound_coinKey K ctx st)

/-- With the count 0 the check makes no round, and the batch goes on to the round of `OpenRep`. -/
theorem startsWithRound_verify_output_zero {β : Type} (mode : ReshareMode) (tuples : List (Tuple C))
    (hcount : (tuples.map (·.count)).sum = 0) (v : Shares C Bit) (count : ℕ) (k : (ℕ → Bit) → RunM C E G β)
    (st : RunState C) :
    StartsWithRound (((realRunBuildingBlocks K ctx mode).verify tuples >>= fun _ =>
      (realRunBuildingBlocks K ctx mode).output v count >>= k).run st) := by
  rw [StateT.run_bind]
  change StartsWithRound ((check K ctx (realCheckBuildingBlocks K ctx) tuples).run st >>= _)
  have hzero : (check (G := G) K ctx (realCheckBuildingBlocks K ctx) tuples).run st = pure ((), st) := by
    unfold check
    dsimp only
    rw [ite_eq_left hcount]
    rfl
  rw [hzero, pure_bind]
  rw [StateT.run_bind]
  change StartsWithRound ((StateT.lift (openRep K ctx v count)).run st >>= _)
  rw [StateT.run_lift, bind_assoc]
  exact startsWithRound_bind _ _ (startsWithRound_openRep K ctx v count)

/-- The check and the opening of a batch start with a round for each count. With a positive count
the round is the first coin of the check, and with the count 0 it is the round of `OpenRep`. -/
theorem startsWithRound_verify_output {β : Type} (mode : ReshareMode) (tuples : List (Tuple C))
    (v : Shares C Bit) (count : ℕ) (k : (ℕ → Bit) → RunM C E G β) (st : RunState C) :
    StartsWithRound (((realRunBuildingBlocks K ctx mode).verify tuples >>= fun _ =>
      (realRunBuildingBlocks K ctx mode).output v count >>= k).run st) := by
  by_cases hcount : (tuples.map (·.count)).sum = 0
  · exact startsWithRound_verify_output_zero K ctx mode tuples hcount v count k st
  · exact startsWithRound_run_bind _ _ _ (startsWithRound_check K ctx tuples hcount st)

end Forms

/-! ## The cut -/

section Cut

variable {I O L R Ia α : Type}

/-- No honest output after a partial abort, under each handler of `WorldSpec` with a state. At the
cut, an honest operator is at `.done none`, and each other honest operator is done or is at a step
of a program that starts with a round. Then each honest operator at such a step ends with no
output. The programs are, for example, `startsWithRound_openRep`, `startsWithRound_check` and
`startsWithRound_verify_output` with any continuation (`startsWithRound_bind`). -/
theorem executeRounds_cut_noOutput {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) (prog : C.Party → PartyM C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (hcut : ∀ i ∉ D.1, (steps i).isDone ∨
      (StartsWithRound (prog i) ∧ steps i ∈ support (advance (prog i).run)))
    (s : σ) (z : (A.State × (C.Party → Option α)) × σ)
    (hz : z ∈ support ((simulateQ impl (executeRounds worldRoles D A F fuel st steps)).run s))
    (i : C.Party) (hlive : steps i ∈ support (advance (prog i).run))
    (hprog : StartsWithRound (prog i)) : z.1.2 i = none := by
  have h : ∀ j ∉ D.1, (steps j).isDone ∨ RejectsAbort (steps j) := fun j hj =>
    (hcut j hj).elim Or.inl fun hp => isDone_or_rejectsAbort _ hp.1 _ hp.2
  rw [executeRounds_abort_support impl D A F fuel st steps hab h s z hz]
  rcases hprog _ hlive with hs | ⟨outbox, resume, hs, -⟩ <;> simp [hs, Step.output]

end Cut

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.KnownTupleInputs

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The bits `r` are a free draw of `count` bits of the stream `(name, key, ρ, idx)` on the support
of `streamWorld` from some state, and the world `w` is above the end state of the draw. -/
def Drawn (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) (w : HashCache C × HiddenCache C)
    (r : ℕ → Bit) : Prop :=
  ∃ s z, z ∈ support ((simulateQ (streamWorld prims D) (freeBits name key ρ idx count)).run s) ∧
    z.2.1 ≤ w.1 ∧ z.2.2 ≤ w.2 ∧ ∀ g < count, r g = z.1 g

/-- Two draws of one stream below one world give the same bits. -/
theorem drawn_agree {name : KeyName C} {key : HashOutput} {ρ idx count : ℕ} {w : HashCache C × HiddenCache C}
    {r r' : ℕ → Bit} (h : Drawn prims D name key ρ idx count w r) (h' : Drawn prims D name key ρ idx count w r') :
    ∀ g < count, r g = r' g := by
  have cell : ∀ {r : ℕ → Bit}, Drawn prims D name key ρ idx count w r → ∀ g < count,
      StreamCell prims D (name, key, ρ, idx, g) w (r g) := by
    rintro r ⟨s, z, hz, h1, h2, hr⟩ g hg
    rw [freeBits_eq, simulateQ_map, StateT.run_map, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hc := readAll_cells prims D _ s y hy
    have hlen := hc.length_eq
    simp only [List.length_map, List.length_range] at hlen
    have hg' : g < y.1.length := hlen ▸ hg
    have h := hc.get (by simpa using hg) hg'
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at h
    rw [hr g hg]
    dsimp only at h1 h2 ⊢
    rw [List.getD_eq_getElem _ _ hg']
    exact h.mono prims D h1 h2
  intro g hg
  exact (cell h g hg).unique prims D (cell h' g hg)

section Reshare

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The bits of each held term at each honest operator are a free draw of the stream of its PRSS
key of that term, at the label `ρ` and the index `0`, below the world `w`. -/
def TermsDrawn (prss : C.Party → PrssKeys C) (ρ count : ℕ) (w : HashCache C × HiddenCache C)
    (r : C.Party → Shares C Bit) : Prop :=
  ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → Drawn prims D (.term T) ((prss i).term T) ρ 0 count w (r i T)

/-- A peer reshare of `count` bits at the honest operators with the outputs `z`. The randomness is
drawn from the streams, each honest operator receives the message of each other honest operator as
sent, and the output is `reshareZ` of the inbox. -/
def PeerRun (prss : C.Party → PrssKeys C) (ρ count : ℕ) (w : HashCache C × HiddenCache C)
    (z : C.Party → Shares C Bit) : Prop :=
  ∃ (r : C.Party → Shares C Bit) (Zs : C.Party → C.Party → ℕ → Bit) (v : C.Party → ℕ → Bit)
    (inbox : C.Party → Mail C E),
    TermsDrawn prims D prss ρ count w r ∧
    (∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i →
      inbox i j = reshareOut K (localContext j) bitCodec (r j) (Zs j) (v j) count i) ∧
    ∀ i, i ∉ D.1 → z i = reshareZ K (localContext i) bitCodec (r i) (Zs i) (v i) count (inbox i)

/-- A collector reshare of `count` bits at the honest operators with the outputs `z`. The randomness
is drawn from the streams, each honest operator receives the message of the second round of each
other honest operator as sent, and the output is `colZ` of the two inboxes. The first round needs no
premise, as a collector forwards one sum to each holder for any inbox. -/
def CollectorRun (prss : C.Party → PrssKeys C) (ρ count : ℕ) (w : HashCache C × HiddenCache C)
    (z : C.Party → Shares C Bit) : Prop :=
  ∃ (r : C.Party → Shares C Bit) (Zs : C.Party → C.Party → ℕ → Bit) (v : C.Party → ℕ → Bit)
    (inbox forward : C.Party → Mail C E),
    TermsDrawn prims D prss ρ count w r ∧
    (∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → forward i j = colOut2 K j (r j) (Zs j) (v j) count (inbox j) i) ∧
    ∀ i, i ∉ D.1 → z i = colZ K i (r i) (Zs i) (v i) count (inbox i) (forward i)

/-- A reshare in `mode`. -/
def ReshareRun : ReshareMode → (C.Party → PrssKeys C) → ℕ → ℕ → HashCache C × HiddenCache C →
    (C.Party → Shares C Bit) → Prop
  | .peer => PeerRun prims D K
  | .collector => CollectorRun prims D K

/-- The honest holders of `T` agree at the positions of `T` below `count` that a corrupt operator
fills. -/
def CorruptAgree (mode : ReshareMode) (count : ℕ) (z : C.Party → Shares C Bit) (T : C.Term) : Prop :=
  ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 → ∀ g < count,
    (∃ f ∈ D.1, filler K mode T g = some f) → z i T g = z j T g

/-- The bits of a term with no filler agree at two honest holders with agreeing keys. -/
theorem termsDrawn_agree {prss : C.Party → PrssKeys C} (hkeys : PrssKeysAgree D prss) {ρ count : ℕ}
    {w : HashCache C × HiddenCache C} {r : C.Party → Shares C Bit} (hr : TermsDrawn prims D prss ρ count w r)
    {T : C.Term} {i j : C.Party} (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) (hi : i ∉ D.1)
    (hj : j ∉ D.1) : ∀ g < count, r i T g = r j T g := by
  have h := hr j hj T hjT
  rw [← hkeys.1 T i j hi hj hiT hjT] at h
  exact drawn_agree prims D (hr i hi T hiT) h

/-- Each honest holder of a term with an
honest filler `f` holds the value `u_f` of `f`. -/
theorem peer_value {r : C.Party → Shares C Bit} {Zs : C.Party → C.Party → ℕ → Bit} {v : C.Party → ℕ → Bit}
    {inbox : C.Party → Mail C E} {count : ℕ}
    (hmail : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i →
      inbox i j = reshareOut K (localContext j) bitCodec (r j) (Zs j) (v j) count i)
    {T : C.Term} {f : C.Party} (hf : K.filled f = T) (hfD : f ∉ D.1) {i : C.Party} (hi : i ∉ D.1)
    (hiT : i ∈ C.holders T) {g : ℕ} (hg : g < count) :
    reshareZ K (localContext i) bitCodec (r i) (Zs i) (v i) count (inbox i) T g =
      reshareU K (localContext f) (r f) (Zs f) (v f) g := by
  have hfill : T ∈ filledTerms K := Finset.mem_map.2 ⟨f, Finset.mem_univ _, hf⟩
  have hsum : ∀ F : C.Party → Bit, ∑ j ∈ Finset.univ.filter (K.filled · = T), F j = F f := fun F =>
    Finset.sum_eq_single_of_mem f (by simp [hf]) fun j hj hjf =>
      absurd (K.filled.injective ((Finset.mem_filter.1 hj).2.trans hf.symm)) hjf
  simp only [reshareZ, localContext, hiT, not_true_eq_false, false_or, not_le.2 hg, hfill, ↓reduceIte, hsum]
  by_cases hif : f = i
  · subst hif
    simp
  · simp only [hif, ↓reduceIte, bitCodec]
    rw [hmail i f hi hfD hif]
    simp only [reshareOut, localContext, Ne.symm hif, hf, hiT, ne_eq, not_false_eq_true, and_self,
      ↓reduceIte, bitCodec, Msg.bitAt, vector]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg]
    rfl

/-- The honest holders of a term agree on the output of a peer reshare when they agree at the
positions with a corrupt filler. -/
theorem peer_agree {prss : C.Party → PrssKeys C} (hkeys : PrssKeysAgree D prss) {ρ count : ℕ}
    {w : HashCache C × HiddenCache C} {z : C.Party → Shares C Bit} (h : PeerRun prims D K prss ρ count w z)
    {T : C.Term} (hcorrupt : CorruptAgree D K .peer count z T) :
    ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 → z i T = z j T := by
  obtain ⟨r, Zs, v, inbox, hr, hmail, hz⟩ := h
  intro i hiT j hjT hi hj
  funext g
  by_cases hg : g < count
  · by_cases hc : ∃ f ∈ D.1, filler K .peer T g = some f
    · exact hcorrupt i hiT j hjT hi hj g hg hc
    rw [hz i hi, hz j hj]
    by_cases hfill : T ∈ filledTerms K
    · obtain ⟨f, -, hf⟩ := Finset.mem_map.1 hfill
      have hfD : f ∉ D.1 := fun hfD => hc ((filler_peer_corrupt K D T g).2 ⟨f, hfD, hf⟩)
      rw [peer_value D K hmail hf hfD hi hiT hg, peer_value D K hmail hf hfD hj hjT hg]
    · simp only [reshareZ, localContext, hiT, hjT, not_true_eq_false, false_or, not_le.2 hg, hfill,
        ↓reduceIte]
      exact termsDrawn_agree prims D hkeys hr hiT hjT hi hj g hg
  · rw [hz i hi, hz j hj]
    simp [reshareZ, not_lt.1 hg]

/-- Each honest holder of `T*` of a gate with an honest collector `κ` holds the sum of `κ`. -/
theorem collector_value {r : C.Party → Shares C Bit} {Zs : C.Party → C.Party → ℕ → Bit}
    {v : C.Party → ℕ → Bit} {inbox forward : C.Party → Mail C E} {count : ℕ}
    (hforward : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i →
      forward i j = colOut2 K j (r j) (Zs j) (v j) count (inbox j) i)
    {g : ℕ} (hg : g < count) (hκ : (K.collector g).2 ∉ D.1) {i : C.Party} (hi : i ∉ D.1)
    (hiT : i ∈ C.holders (K.collector g).1) :
    colZ K i (r i) (Zs i) (v i) count (inbox i) (forward i) (K.collector g).1 g =
      colSum K (K.collector g).2 (r (K.collector g).2) (Zs (K.collector g).2) (v (K.collector g).2) count
        (inbox (K.collector g).2) g := by
  simp only [colZ, hiT, not_true_eq_false, false_or, not_le.2 hg, ↓reduceIte]
  by_cases hiκ : (K.collector g).2 = i
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hiκ), hiκ]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hiκ), hforward i _ hi hκ hiκ]
    have hmem : g ∈ forwardedTo K count (K.collector g).2 i := by
      simp [forwardedTo, collectedBy, hg, hiT]
    simp only [colOut2, Ne.symm hiκ, ne_eq, not_false_eq_true, ↓reduceIte, Msg.bitAt]
    exact getD_map_idxOf hmem _

/-- The honest holders of a term agree on the output of a collector reshare when they agree at the
positions with a corrupt collector. -/
theorem collector_agree {prss : C.Party → PrssKeys C} (hkeys : PrssKeysAgree D prss) {ρ count : ℕ}
    {w : HashCache C × HiddenCache C} {z : C.Party → Shares C Bit} (h : CollectorRun prims D K prss ρ count w z)
    {T : C.Term} (hcorrupt : CorruptAgree D K .collector count z T) :
    ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 → z i T = z j T := by
  obtain ⟨r, Zs, v, inbox, forward, hr, hforward, hz⟩ := h
  intro i hiT j hjT hi hj
  funext g
  by_cases hg : g < count
  · by_cases hc : ∃ f ∈ D.1, filler K .collector T g = some f
    · exact hcorrupt i hiT j hjT hi hj g hg hc
    rw [hz i hi, hz j hj]
    by_cases hstar : T = (K.collector g).1
    · subst hstar
      have hκ : (K.collector g).2 ∉ D.1 := fun hκ => hc ((filler_collector_corrupt K D _ g).2 ⟨rfl, hκ⟩)
      rw [collector_value D K hforward hg hκ hi hiT, collector_value D K hforward hg hκ hj hjT]
    · simp only [colZ, hiT, hjT, not_true_eq_false, false_or, not_le.2 hg, hstar, ↓reduceIte]
      exact termsDrawn_agree prims D hkeys hr hiT hjT hi hj g hg
  · rw [hz i hi, hz j hj]
    simp [colZ, not_lt.1 hg]

/-- The honest holders of a term agree on the output of a reshare in each mode when they agree at
the positions with a corrupt filler. -/
theorem reshare_agree {prss : C.Party → PrssKeys C} (hkeys : PrssKeysAgree D prss) (mode : ReshareMode)
    {ρ count : ℕ} {w : HashCache C × HiddenCache C} {z : C.Party → Shares C Bit}
    (h : ReshareRun prims D K mode prss ρ count w z) {T : C.Term} (hcorrupt : CorruptAgree D K mode count z T) :
    ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 → z i T = z j T := by
  cases mode with
  | peer => exact peer_agree prims D K hkeys h hcorrupt
  | collector => exact collector_agree prims D K hkeys h hcorrupt

end Reshare

section Batch

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

omit [Field E] [Algebra Bit E] in
/-- Two equal vectors agree at each position below their length. -/
theorem vector_apply_eq {R : Type} {count : ℕ} {f f' : ℕ → R} (h : vector count f = vector count f') :
    ∀ g < count, f g = f' g := by
  intro g hg
  have h' := congrArg (·[g]?) h
  simpa [vector, List.getElem?_range hg] using h'

omit [Field E] [Algebra Bit E] in
/-- Two lists of tuples with the same counts and the same values at `T` have the same copies at
`T`. -/
theorem copies_eq (T : C.Term) {a b : List (Tuple C)} (hcount : a.map (·.count) = b.map (·.count))
    (hval : ∀ m : ℕ, (a[m]?).map (fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)) =
      (b[m]?).map fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)) :
    (a.map fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) =
      b.map fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T)) := by
  apply List.ext_getElem?
  intro m
  have hc := congrArg (·[m]?) hcount
  have hv := hval m
  simp only [List.getElem?_map] at hc ⊢
  rcases ha : a[m]? with _ | τ <;> rcases hb : b[m]? with _ | σ <;> simp_all

/-- The honest operators have input sharings of one length, and the honest holders of each term
agree on the sharing of each job at it. -/
def InputsAgree (inputs : C.Party → List (C.Term → List Bit)) : Prop :=
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (inputs i).length = (inputs j).length) ∧
    ∀ k, Consistent D fun i T => ((inputs i).getD k fun _ => []) T

/-- The agreement of the products of the first `d` layers at `T` gives the agreement of the traces
at `T`. -/
theorem agreeAt_layerPrefix_of_lt (mode : ReshareMode) (jobs : List Circuit) (T : C.Term)
    (I I' : List (C.Term → List Bit)) (zs zs' : ℕ → Shares C Bit) (hI : I.length = I'.length)
    (hIT : ∀ k, (I.getD k fun _ => []) T = (I'.getD k fun _ => []) T) :
    ∀ d, (∀ l < d, zs l T = zs' l T) →
      AgreeAt T (layerPrefix K mode jobs I zs d) (layerPrefix K mode jobs I' zs' d) := by
  intro d
  induction d with
  | zero => exact fun _ => ⟨hI, hIT, rfl, fun _ => rfl⟩
  | succ d ih =>
    intro hz
    rw [layerPrefix_succ, layerPrefix_succ]
    exact agreeAt_layerStep K mode jobs T zs zs' _ _ d (ih fun l hl => hz l (by omega)) (hz d (by omega))

/-- `TupleInputs` for the tuples of one batch. The honest operators run one job list `jobs` in one
mode from one label `L`, and they agree on the PRSS keys and on the input sharings. Each AND layer
and `Rerand` is a reshare with the randomness drawn from the streams below one world `w` and the
honest messages delivered as sent. -/
theorem tupleInputs_batchTuples {prss : C.Party → PrssKeys C} (hkeys : PrssKeysAgree D prss)
    (mode : ReshareMode) (jobs : List Circuit) (L : ℕ) (w : HashCache C × HiddenCache C)
    (inputs : C.Party → List (C.Term → List Bit)) (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit)
    (hinputs : InputsAgree D inputs) (hlayers : ∀ l < depth jobs,
      ReshareRun prims D K mode prss (L + l) (gatesAt jobs l).length w fun i => zs i l)
    (hrerand : ReshareRun prims D K .peer prss (L + depth jobs) (outputsOf jobs).length w v') :
    TupleInputs K (headCounts jobs) D fun i => batchTuples K mode jobs (inputs i) (zs i) (v' i) := by
  have hshape := fun i => batchTuples_shape K mode jobs (inputs i) (zs i) (v' i)
  have hcounts : ∀ i, (batchTuples K mode jobs (inputs i) (zs i) (v' i)).map (·.count) = headCounts jobs :=
    fun i => by simpa [List.map_map, headCounts, Function.comp_def] using congrArg (List.map Prod.fst) (hshape i)
  refine ⟨fun i _ => hcounts i, fun i j _ _ => ?_, fun T hant => ?_⟩
  · have hi := congrArg (List.map Prod.snd) (hshape i)
    have hj := congrArg (List.map Prod.snd) (hshape j)
    simp only [List.map_map] at hi hj
    exact hi.trans hj.symm
  intro i hiT j hjT hi hj
  have hcor : ∀ l < depth jobs, CorruptAgree D K mode (gatesAt jobs l).length (fun i => zs i l) T := by
    intro l hl a haT b hbT ha hb g hg hc
    have h := congrArg (·[l]?) (hant a haT b hbT ha hb)
    simp only [List.getElem?_map, batchTuples_layer K mode jobs _ _ _ l hl, Option.map_some,
      Option.some.injEq] at h
    simpa [hc] using vector_apply_eq h g hg
  have hcorv : CorruptAgree D K .peer (outputsOf jobs).length v' T := by
    intro a haT b hbT ha hb g hg hc
    have h := congrArg (·[depth jobs]?) (hant a haT b hbT ha hb)
    simp only [List.getElem?_map, batchTuples_output, Option.map_some, Option.some.injEq] at h
    simpa [hc] using vector_apply_eq h g hg
  have hz : ∀ l < depth jobs, zs i l T = zs j l T := fun l hl =>
    reshare_agree prims D K hkeys mode (hlayers l hl) (hcor l hl) i hiT j hjT hi hj
  have hv : v' i T = v' j T := reshare_agree prims D K hkeys .peer hrerand hcorv i hiT j hjT hi hj
  have hagree := agreeAt_layerPrefix_of_lt K mode jobs T (inputs i) (inputs j) (zs i) (zs j)
    (hinputs.1 i j hi hj) (fun k => hinputs.2 k T i hiT j hjT hi hj) (depth jobs) hz
  exact copies_eq T ((hcounts i).trans (hcounts j).symm)
    (batchTuples_agreeAt K mode jobs T _ _ _ _ _ _ hagree hv)

end Batch

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.KnownTupleInputs

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CheckTiming.runTimed_realBatch_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CheckTiming.runTimed_realBatch_exact

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CheckTiming.runTimed_ceremonyRun_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CheckTiming.runTimed_ceremonyRun_exact

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.executeRounds_cut_noOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.executeRounds_cut_noOutput

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.startsWithRound_verify_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.startsWithRound_verify_output

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.KnownTupleInputs.tupleInputs_batchTuples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.KnownTupleInputs.tupleInputs_batchTuples
