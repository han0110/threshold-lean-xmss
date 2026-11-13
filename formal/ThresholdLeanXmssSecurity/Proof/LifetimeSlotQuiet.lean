import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenPrograms
import ThresholdLeanXmssSecurity.Proof.LifetimeSlots
import ThresholdLeanXmssSecurity.Proof.TreeCheckSeenCovered

/-!
# Programming freedom of lifetime slots

The slot tail makes no programming queries in shared, own and ideal modes.
The fixed-dealing keygen execution only programs keygen derivation points.
Both facts concern the actual programs, for arbitrary adversaries and states.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeSlotQuiet
open LifetimeKeygenPrograms LifetimeKeygenHopProof LifetimeJointLink
open LifetimeHybridOrder LifetimeSlots LifetimeEmulatedBudget

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Programming freedom from every state of an additional state layer. -/
def QuietState {σ α : Type} (x : StateT σ (EmulationM C) α) : Prop :=
  ∀ s, Quiet (x.run s)

theorem quiet_map {α β : Type} (f : α → β) {x : EmulationM C α} (hx : Quiet x) :
    Quiet (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact quiet_bind hx fun _ => quiet_pure _

theorem quietState_pure {σ α : Type} (a : α) :
    QuietState (pure a : StateT σ (EmulationM C) α) := fun _ => quiet_pure _

theorem quietState_bind {σ α β : Type} {x : StateT σ (EmulationM C) α}
    {f : α → StateT σ (EmulationM C) β} (hx : QuietState x)
    (hf : ∀ a, QuietState (f a)) : QuietState (x >>= f) := by
  intro s
  exact quiet_bind (hx s) fun r => hf r.1 r.2

theorem quietState_lift {σ α : Type} {x : EmulationM C α} (hx : Quiet x) :
    QuietState (StateT.lift x : StateT σ (EmulationM C) α) := by
  intro s
  exact quiet_bind hx fun _ => quiet_pure _

theorem quietState_sequenceFin {α : Type} {σ : Type} : ∀ {n : ℕ}
    (p : Fin n → StateT σ (EmulationM C) α), (∀ i, QuietState (p i)) →
      QuietState (Concrete.sequenceFin p)
  | 0, _, _ => quietState_pure _
  | _ + 1, p, hp => quietState_bind (hp 0) fun _ =>
      quietState_bind (quietState_sequenceFin (fun i => p i.succ) (fun i => hp i.succ))
        fun _ => quietState_pure _

theorem quietState_simulate {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ (EmulationM C))) (h : ∀ t, QuietState (impl t))
    (oa : OracleComp spec α) : QuietState (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact quietState_pure a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact quietState_bind (h t) ih

theorem own_honest_quiet (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    QuietState ((ownRoles D).honest p) := by
  intro own shared
  simp only [ownRoles, StateT.run_mk, StateT.run_lift, WriterT.run_bind']
  exact qb0_bind' (honest_quiet D p own) fun _ =>
    (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_pure _ _ _)

-- StateT port of LifetimeRunBoundary.startSteps_quietP.
theorem startSteps_own_quiet {α : Type} (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec α) :
    QuietState (startSteps (ownRoles D) D program) := by
  apply quietState_sequenceFin
  intro i
  split
  · exact quietState_pure _
  · exact own_honest_quiet D _

-- StateT port of LifetimeRunBoundary.stepRound_quietP.
theorem stepRound_own_quiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    QuietState (stepRound (ownRoles D) D A noFunctionality state steps) := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  refine quietState_bind (quietState_lift (adversary_quiet D _)) fun r =>
    quietState_bind ?_ fun _ => quietState_pure _
  apply quietState_sequenceFin
  intro j
  cases steps j with
  | done out => exact quietState_pure _
  | wait out resume =>
    dsimp only
    split
    · exact quietState_pure _
    · exact own_honest_quiet D _
  | call input _ => exact input.elim

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)

theorem lifetimeOracles_quiet (D : C.Coalition) (keys : C.Party → Keys C)
    (h : C.Party) (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E) :
    Quiet ((lifetimeOraclesWith K circuits settings attempts (fun _ => emulatedRoles D)
      (lifetimeHybridRoles D 0 0) D keys
      (fun x => (lifetimeHybridRoles D 0 0).honest
        (liftComp (prfValue (honestSeeds D keys) x) _)) h q).run st) := by
  rw [← hom_lifetimeOracles (H3 D) K circuits settings attempts
    (fun _ => emulRoles3) baseRoles3 _ _ (fun _ => rolesHom_emul D) (rolesHom_base D)
    D keys (fun x => freeCopy (liftComp (prfValue (honestSeeds D keys) x) _)) _
    (fun _ => impl3_freeCopy D _) h q st]
  exact simulate3_quiet D _

theorem finish_quiet (D : C.Coalition) (keys : C.Party → Keys C)
    (parameter : PublicParameter) (top : TopTree) (st : TsigState C) (forgery : Forgery) :
    Quiet (forgeryWins
      (fun p => (lifetimeHybridRoles D 0 0).honest (liftComp p _))
      (dealtWith (fun p => (lifetimeHybridRoles D 0 0).honest (liftComp p _))
        parameter keys top (fun x => (lifetimeHybridRoles D 0 0).honest
          (liftComp (prfValue (honestSeeds D keys) x) _))) st forgery) := by
  have eq := hom_forgeryWins (H3 D)
    (fun p => freeCopy (liftComp p _))
    (dealtWith (fun p => freeCopy (liftComp p _)) parameter keys top
      (fun x => freeCopy (liftComp (prfValue (honestSeeds D keys) x) _))) st forgery
  rw [hom_dealtWith (H3 D) _ _ (fun p => impl3_freeCopy D _) _ _ _ _ _
    (fun x => impl3_freeCopy D _)] at eq
  simp only [H3, impl3_freeCopy] at eq
  rw [← eq]
  exact simulate3_quiet D _

theorem slotOracles_quiet (D : C.Coalition) (mode : Slot attempts → RunMode)
    (keys : C.Party → Keys C) (h : C.Party) (q : (LifetimeSpec C E).Domain) :
    QuietState (slotOracles K circuits settings attempts (worldEnv D circuits settings)
      mode D keys (fun x => (lifetimeHybridRoles D 0 0).honest
        (liftComp (prfValue (honestSeeds D keys) x) _)) h q) := by
  intro s
  cases q with
  | sign q => exact quiet_map _ (lifetimeOracles_quiet K circuits settings attempts D keys h _ s.1)
  | publicKey => exact quiet_map _ (lifetimeOracles_quiet K circuits settings attempts D keys h _ s.1)
  | start tree =>
    simp only [slotOracles, worldEnv, StateT.run_mk]
    split
    · split
      · exact quiet_bind (startSteps_own_quiet D _ _) fun _ => quiet_pure _
      · refine quiet_bind (base_honest_quiet D _) fun r => ?_
        exact quiet_bind (startSteps_own_quiet D _ _) fun _ => quiet_pure _
      · exact quiet_map _ (lifetimeOracles_quiet K circuits settings attempts D keys h _ s.1)
    · exact quiet_map _ (lifetimeOracles_quiet K circuits settings attempts D keys h _ s.1)
  | round sent =>
    simp only [slotOracles, worldEnv, StateT.run_mk]
    split
    · exact quiet_bind (stepRound_own_quiet D _ _ _ _) fun _ => quiet_pure _
    · exact quiet_map _ (lifetimeOracles_quiet K circuits settings attempts D keys h _ s.1)

/-- No slot tail programs the world oracle, for any assignment of the three modes. -/
theorem slotRun_quiet (D : C.Coalition) (A : LifetimeAdversary C E)
    (mode : Slot attempts → RunMode) (state : A.keygen.State)
    (outputs : C.Party → Option (Keys C)) :
    Quiet (slotRun K circuits settings attempts (worldEnv D circuits settings)
      mode D A state outputs) := by
  unfold slotRun
  split
  · rename_i h _
    split
    · exact quiet_pure _
    · refine quiet_bind ?_ ?_
      · apply quietState_simulate
        intro t
        rcases t with t | q
        · exact quietState_lift (adversary_quiet D _)
        · exact slotOracles_quiet K circuits settings attempts D mode _ h q
      · rintro ⟨forgery, s⟩
        dsimp only
        split
        · exact quiet_pure _
        · split
          · exact finish_quiet D _ _ _ _ _
          · exact quiet_pure _
  · exact quiet_pure _

/-- The no-programming bound also excludes programming outside keygen derivation. -/
theorem otherProgram_of_quiet {α : Type} (p : OracleComp (WorldSpec C) α)
    (hp : IsQueryBoundP p Programming 0) : IsQueryBoundP p OtherProgram 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp ⊢
    have ht : ¬ Programming t := hp.1.resolve_right (by omega)
    have ho : ¬ OtherProgram t := by
      rcases t with (t | t) | t <;> simp_all [Programming, OtherProgram]
    refine ⟨Or.inl ho, fun u => ?_⟩
    simpa only [if_neg ho] using ih u (by simpa only [if_neg ht] using hp.2 u)

theorem observed_stepRound_quiet (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) :
    IsQueryBoundP ((stepRound observedRoles D A noFunctionality state steps).run) Programming 0 := by
  have h := TreeCheckSeenCovered.stepRound_quiet D A state steps
  rw [← keygenEraseLog_stepRound] at h
  exact (isQueryBoundP_map_iff _ _ _).1 h

theorem observed_executeRounds_quiet (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) :
    IsQueryBoundP ((executeRounds observedRoles D A noFunctionality fuel state steps).run)
      Programming 0 := by
  have h := TreeCheckSeenCovered.executeRounds_quiet D A fuel state steps
  rw [← keygenEraseLog_executeRounds] at h
  exact (isQueryBoundP_map_iff _ _ _).1 h

theorem keygenEmulation_otherProgram (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (st : SimulatorState C Unit A.State)
    (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C)) :
    IsQueryBoundP (keygenEmulation D A st parameter corrupt) OtherProgram 0 := by
  unfold keygenEmulation
  refine qb0_bind' (otherProgram_of_quiet _ (free_quiet _)) fun parts => ?_
  refine qb0_bind' (otherProgram_of_quiet _ (TreeCheckSeenCovered.startSteps_quiet D _)) fun steps => ?_
  refine qb0_bind' (otherProgram_of_quiet _ (observed_stepRound_quiet D A st.adversary steps)) fun r => ?_
  refine qb0_bind' (otherProgram_of_quiet _ (free_quiet _)) fun high => ?_
  refine qb0_bind' (keygenProgramBlock_safe D parts _ _ parameter corrupt high) fun _ => ?_
  exact qb0_bind' (otherProgram_of_quiet _ (observed_executeRounds_quiet D A _ _ _))
    fun _ => isQueryBoundP_pure _ _ _

/-- A fixed-dealing keygen simulator programs only keygen derivation points. -/
theorem dealtKeygen_otherProgram (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (d : LifetimeBridge.Dealing C) (x : C.Party → Unit) (z : Aux) :
    IsQueryBoundP (idealExecution (fun p => p) D (dealtKeygen d) (keygenSimulator D A) x z)
      OtherProgram 0 := by
  unfold idealExecution dealtKeygen
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine qb0_bind' ?_ fun st => ?_
  · exact qb0_bind' (otherProgram_of_quiet _ (observe_quiet _)) fun _ => isQueryBoundP_pure _ _ _
  · have hleak {σ L R : Type}
        (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
        (l : L) : simulateQ impl (leak (C := C) (R := R) l) = impl (.inr l) := by
      unfold leak
      exact (simulateQ_query _ _).trans (id_map _)
    rw [hleak]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    change IsQueryBoundP (((keygenSimulator D A).answer st
      (d.1, fun i => if i ∈ D.1 then some (d.2.2 i) else none) >>=
      fun p => pure (p.2, p.1)) >>= fun p =>
        (keygenSimulator D A).output p.2 >>= fun out =>
          pure (out, fun i => if i ∉ D.1 ∧ i ∈ p.1 then some (d.2.2 i) else none)) OtherProgram 0
    rw [keygenSimulator_answer_emulation]
    apply qb0_bind'
    · exact qb0_bind' ((isQueryBoundP_map_iff _ _ _).2
        (keygenEmulation_otherProgram D A st _ _)) fun _ => isQueryBoundP_pure _ _ _
    · intro p
      exact qb0_bind' (isQueryBoundP_pure _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.quiet_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quiet_map

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.quietState_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quietState_pure

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.quietState_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quietState_bind

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.quietState_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quietState_lift

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.quietState_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quietState_sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.quietState_simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quietState_simulate

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.own_honest_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms own_honest_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.startSteps_own_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms startSteps_own_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.stepRound_own_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepRound_own_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.lifetimeOracles_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeOracles_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.finish_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finish_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.slotOracles_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotOracles_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.slotRun_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotRun_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.otherProgram_of_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms otherProgram_of_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.observed_stepRound_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms observed_stepRound_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.observed_executeRounds_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms observed_executeRounds_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.keygenEmulation_otherProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenEmulation_otherProgram

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotQuiet.dealtKeygen_otherProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealtKeygen_otherProgram

end ThresholdLeanXmssSecurity.LifetimeSlotQuiet
