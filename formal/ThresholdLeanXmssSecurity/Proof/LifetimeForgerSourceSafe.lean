import ThresholdLeanXmssSecurity.Proof.LifetimeForgerSourceParts

/-! # Programming confinement of the concrete lifetime forger source

The source programs only keygen derivation points. Emulated party steps and
the lifetime tail preserve this property for arbitrary adversary programs.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe
open LifetimeForgerSourceParts LifetimeForgerMerge LifetimeJointLink
open LifetimeKeygenPrograms LifetimeSlotQuiet LifetimeIdealBad LifetimeKeygenHopProof
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

def Safe {α : Type} (p : OracleComp (ReplaySpec C) α) : Prop :=
  IsQueryBoundP p OtherReplayProgram 0

theorem inWorld_safe {α : Type} (p : OracleComp (WorldSpec C) α)
    (hp : IsQueryBoundP p OtherProgram 0) : Safe (inWorld p) := by
  apply ThresholdLeanXmssSecurity.qb0_simulateQ _ (fun t ht => ?_) p hp
  exact (isQueryBoundP_query_iff _ _ _).2 fun h => (ht h).elim

theorem safe_pure {α : Type} (a : α) : Safe (pure a : OracleComp (ReplaySpec C) α) :=
  isQueryBoundP_pure _ _ _

theorem safe_bind {α β : Type} {p : OracleComp (ReplaySpec C) α}
    {f : α → OracleComp (ReplaySpec C) β} (hp : Safe p) (hf : ∀ a, Safe (f a)) :
    Safe (p >>= f) := qb0_bind' hp hf

theorem safe_map {α β : Type} (f : α → β) {p : OracleComp (ReplaySpec C) α}
    (hp : Safe p) : Safe (f <$> p) := (isQueryBoundP_map_iff _ _ _).2 hp

def SafeState {σ α : Type} (p : StateT σ (OracleComp (ReplaySpec C)) α) : Prop :=
  ∀ s, Safe (p.run s)

theorem safeState_pure {σ α : Type} (a : α) :
    SafeState (pure a : StateT σ (OracleComp (ReplaySpec C)) α) := fun _ => safe_pure _

theorem safeState_bind {σ α β : Type} {p : StateT σ (OracleComp (ReplaySpec C)) α}
    {f : α → StateT σ (OracleComp (ReplaySpec C)) β}
    (hp : SafeState p) (hf : ∀ a, SafeState (f a)) : SafeState (p >>= f) :=
  fun s => safe_bind (hp s) fun r => hf r.1 r.2

theorem safeState_lift {σ α : Type} {p : OracleComp (ReplaySpec C) α} (hp : Safe p) :
    SafeState (StateT.lift p : StateT σ (OracleComp (ReplaySpec C)) α) := by
  intro s
  exact safe_map _ hp

theorem safeState_sequenceFin {σ α : Type} : ∀ {n : ℕ}
    (p : Fin n → StateT σ (OracleComp (ReplaySpec C)) α),
    (∀ i, SafeState (p i)) → SafeState (Concrete.sequenceFin p)
  | 0, _, _ => safeState_pure _
  | _ + 1, p, hp => safeState_bind (hp 0) fun _ =>
      safeState_bind (safeState_sequenceFin (fun i => p i.succ) (fun i => hp i.succ))
        fun _ => safeState_pure _

theorem replay_honest_safe (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    SafeState ((replayRoles D).honest p) := by
  intro own
  apply inWorld_safe
  exact otherProgram_of_quiet _ ((isQueryBoundP_map_iff _ _ _).2 (honest_quiet D p own))

theorem world_adversary_safe {α : Type} (p : OracleComp (LocalSpec C) α) :
    Safe (inWorld (worldRoles.adversary p)) :=
  inWorld_safe _ (otherProgram_of_quiet _ (counted_quiet p))

-- Ports of SlotQuiet.startSteps_own_quiet and stepRound_own_quiet.
theorem startSteps_safe {α : Type} (D : C.Coalition)
    (p : C.Party → PartyM C E RealSpec α) : SafeState (startSteps (replayRoles D) D p) := by
  apply safeState_sequenceFin
  intro i
  split
  · exact safeState_pure _
  · exact replay_honest_safe D _

theorem stepRound_safe {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    SafeState (stepRound (replayRoles D) D A noFunctionality state steps) := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  refine safeState_bind (safeState_lift (world_adversary_safe _)) fun r =>
    safeState_bind ?_ fun _ => safeState_pure _
  apply safeState_sequenceFin
  intro j
  cases steps j with
  | done out => exact safeState_pure _
  | wait out resume =>
    dsimp only
    split
    · exact safeState_pure _
    · exact replay_honest_safe D _
  | call input _ => exact input.elim

theorem signing_query_safe (q : TsigQuery C) :
    Safe (OracleComp.lift (OracleSpec.query (spec := ReplaySpec C) (.inr q))) :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)

theorem forgerOracles_safe (D : C.Coalition) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) (top : TopTree) (h : C.Party)
    (q : (LifetimeSpec C E).Domain) :
    SafeState (forgerOracles K circuits settings attempts D parameter corrupt top h q) := by
  intro s
  cases q with
  | sign q =>
    cases q <;>
      simp only [forgerOracles, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_pure]
    all_goals try split_ifs
    all_goals first
      | exact safe_pure _
      | exact safe_map _ (signing_query_safe _)
  | publicKey => exact safe_pure _
  | start tree =>
    cases tree <;>
      simp only [forgerOracles, StateT.run_bind, StateT.run_get, pure_bind]
    all_goals split
    all_goals first
      | exact safe_pure _
      | (simp only [StateT.run_lift, StateT.run_bind, bind_assoc, StateT.run_set,
            StateT.run_pure, pure_bind]
         first
         | exact safe_bind (startSteps_safe D _ _) fun _ => safe_pure _
         | (refine safe_bind (signing_query_safe _) fun r => ?_
            exact safe_bind (startSteps_safe D _ _) fun _ => safe_pure _))
  | round sent =>
    simp only [forgerOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · split
      · simp only [StateT.run_lift, StateT.run_bind, bind_assoc, StateT.run_set,
          StateT.run_pure, pure_bind]
        exact safe_bind (stepRound_safe D _ _ _ _) fun _ => safe_pure _
      · exact safe_pure _
    · exact safe_pure _

theorem corruptRequests_safe (D : C.Coalition) : Safe (corruptRequests D) := by
  apply zero_sequenceFin
  intro i
  split
  · exact signing_query_safe _
  · exact safe_pure _

theorem source_safe (D : C.Coalition) (A : LifetimeAdversary C E)
    (publicKey : PublicKey) (top : TopTree) :
    IsQueryBoundP (sourceReplay K circuits settings attempts D A publicKey top)
      OtherReplayProgram 0 := by
  unfold sourceReplay
  apply safe_bind (corruptRequests_safe D)
  intro corrupt
  refine safe_bind ?_ fun st => safe_bind ?_ fun result => safe_bind ?_ fun state => ?_
  · apply inWorld_safe
    exact qb0_bind' (otherProgram_of_quiet _ (observe_quiet _)) fun _ => isQueryBoundP_pure _ _ _
  · apply inWorld_safe
    rw [keygenSimulator_answer_emulation]
    exact (isQueryBoundP_map_iff _ _ _).2 (keygenEmulation_otherProgram D A.keygen st _ _)
  · exact inWorld_safe _ (isQueryBoundP_pure _ _ _)
  · rw [StateT.run'_eq]
    apply safe_map
    apply simulate_run_quiet
    intro t st
    rcases t with t | q
    · exact safeState_lift (world_adversary_safe _) st
    · exact forgerOracles_safe K circuits settings attempts D _ _ top _ q st

end ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.inWorld_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.inWorld_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safe_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safe_pure

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safe_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safe_bind

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safe_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safe_map

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_pure

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_bind

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_lift

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.safeState_sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.replay_honest_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.replay_honest_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.world_adversary_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.world_adversary_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.startSteps_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.startSteps_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.stepRound_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.stepRound_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.signing_query_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.signing_query_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.forgerOracles_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.forgerOracles_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.corruptRequests_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.corruptRequests_safe

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.source_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceSafe.source_safe
