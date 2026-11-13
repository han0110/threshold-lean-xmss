import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenHopProof
import XmssSecurity.Proof.QueryBoundSupport
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The keygen cap is quiet

The lifetime query bound `HasLifetimeQueryBoundAll` holds for all answers of the oracles. Each
adversary segment that the real keygen prefix of `lifetimeGame` reaches is thus within `Q`
counted calls, and `cap_eq` leaves it unchanged.

The ideal keygen phase runs the same adversary segments. Its start is the real start. Its emulated
honest operators use parts from `sampleParts`, as `keygen` does, so each initial network state of
the ideal phase is in the support of the real one. The simulator runs one `stepRound` and then
`executeRounds (setupRounds - 1)`. The real phase does the same, because each honest operator
waits at the commit round. The programming block of the simulator changes only oracle answers,
and the support is over all answers.

Under `RealPrefixBound`, `phase_real_cap` and `phase_ideal_cap` state that the capped keygen phase
is the same program as the keygen phase. `realPrefixBound_of_lifetime` gets `RealPrefixBound` from
the lifetime budget. `keygenCapQuiet` gives `KeygenCapQuiet` for every `Th` of the form
`thOf values`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeKeygenCapQuiet

open LifetimeHybridOrder LifetimeJointLink LifetimeKeygenHopProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

theorem adversary_bind {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (k : α → OracleComp (LocalSpec C) β) :
    worldRoles.adversary (oa >>= k) = worldRoles.adversary oa >>= fun a => worldRoles.adversary (k a) := by
  simp only [worldRoles, counted, liftComp_bind]
  exact simulateQ_bind _ _ _

/-- A lifetime budget of the adversary role bounds the counted calls of the segment. -/
theorem counted_of_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP (worldRoles.adversary oa) LifetimeCounted n) : IsQueryBoundP oa Counted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [adversary_bind, adversary_query] at h
    rw [isQueryBoundP_query_bind_iff]
    have hc : Counted t → LifetimeCounted (C := C) (.inl (.inl t)) := by
      rcases t with t | t
      · intro ht
        exact ht.elim
      · intro _
        trivial
    have h1 : ¬ LifetimeCounted (C := C) (.inl (.inl t)) ∨ 0 < n := h.1
    have h2 : ∀ u, IsQueryBoundP (worldRoles.adversary (k u)) LifetimeCounted
        (if LifetimeCounted (C := C) (.inl (.inl t)) then n - 1 else n) := h.2
    refine ⟨?_, fun u => (ih u _ (h2 u)).mono ?_⟩
    · by_cases ht : Counted t
      · exact Or.inr (h1.resolve_left (not_not.mpr (hc ht)))
      · exact Or.inl ht
    · by_cases ht : Counted t
      · simp only [ht, hc ht, if_true, le_refl]
      · split_ifs <;> omega

theorem support_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    support (worldRoles.adversary oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [adversary_bind, adversary_query, support_bind, support_bind]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨u, _, hu⟩ => ⟨u, mem_support_query _ _, ih u ▸ hu⟩,
      fun ⟨u, _, hu⟩ => ⟨u, mem_support_query _ _, (ih u).symm ▸ hu⟩⟩

theorem support_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    support (free (C := C) oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e, support_bind, support_bind]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨u, _, hu⟩ => ⟨u, mem_support_query _ _, ih u ▸ hu⟩,
      fun ⟨u, _, hu⟩ => ⟨u, mem_support_query _ _, (ih u).symm ▸ hu⟩⟩

/-- The converse of `mem_support_sequenceFin_oc`. -/
theorem mem_support_sequenceFin_of {ι : Type} {spec : OracleSpec ι} {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α) (x : Fin n → α), (∀ i, x i ∈ support (f i)) →
      x ∈ support (Concrete.sequenceFin f)
  | 0, f, x, _ => by
    simp only [Concrete.sequenceFin, support_pure, Set.mem_singleton_iff]
    funext i
    exact i.elim0
  | n + 1, f, x, hx => by
    simp only [Concrete.sequenceFin, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff]
    refine ⟨x 0, hx 0, fun i => x i.succ,
      mem_support_sequenceFin_of (fun i : Fin n => f i.succ) _ (fun i => hx i.succ), ?_⟩
    funext i
    cases i using Fin.cases <;> rfl

section Rounds

variable (D : C.Coalition) (B : Adversary C E Unit PEmpty PEmpty) (Q : ℕ)

/-- A capped round equals the round when the round segment is within `Q`. -/
theorem stepRound_cap {m : Type → Type} [Monad m] (Ro : Roles C m) (state : B.State)
    (steps : C.Party → Step C E RealSpec (Keys C))
    (h : IsQueryBoundP (B.round state fun c i =>
      if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) Counted Q) :
    stepRound Ro D (capAdversary Q B) noFunctionality state steps =
      stepRound Ro D B noFunctionality state steps := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real]), if_neg (by simp [callInput_real])]
  change Ro.adversary (cap Q (B.round state _)) >>= _ = _
  rw [cap_eq _ _ h]
  rfl

/-- A bound on the real rounds from one network state bounds its next round segment and the
rounds from every next network state. -/
theorem round_bound (fuel : ℕ) (state : B.State) (steps : C.Party → Step C E RealSpec (Keys C))
    (hdone : ¬ ∀ i, i ∉ D.1 → (steps i).isDone)
    (h : IsQueryBoundP (executeRounds worldRoles D B noFunctionality (fuel + 1) state steps)
      LifetimeCounted Q) :
    IsQueryBoundP (B.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) Counted Q ∧
      ∀ r ∈ support (stepRound worldRoles D B noFunctionality state steps),
        IsQueryBoundP (executeRounds worldRoles D B noFunctionality fuel r.1 r.2.1) LifetimeCounted Q := by
  rw [executeRounds, if_neg hdone] at h
  refine ⟨?_, fun r hr => ?_⟩
  · have hs := OracleComp.IsQueryBoundP.of_bind_left h
    unfold stepRound at hs
    rw [if_neg (by simp [callInput_real])] at hs
    exact counted_of_adversary _ _ (OracleComp.IsQueryBoundP.of_bind_left hs)
  · have hr' := continuation_bound_of_support _ _ _ _ h r hr
    rcases r with ⟨s, st, sent⟩
    exact hr'

/-- The observed rounds of the capped adversary equal those of the adversary from each network
state whose real rounds are within `Q`. -/
theorem executeRounds_observed_cap : ∀ (fuel : ℕ) (state : B.State)
    (steps : C.Party → Step C E RealSpec (Keys C)),
    IsQueryBoundP (executeRounds worldRoles D B noFunctionality fuel state steps) LifetimeCounted Q →
    executeRounds observedRoles D (capAdversary Q B) noFunctionality fuel state steps =
      executeRounds observedRoles D B noFunctionality fuel state steps
  | 0, state, steps, _ => rfl
  | fuel + 1, state, steps, h => by
    by_cases hdone : ∀ i, i ∉ D.1 → (steps i).isDone
    · rw [executeRounds, executeRounds, if_pos hdone, if_pos hdone]
      rfl
    · obtain ⟨hround, hnext⟩ := round_bound D B Q fuel state steps hdone h
      rw [executeRounds, executeRounds, if_neg hdone, if_neg hdone,
        stepRound_cap D B Q observedRoles state steps hround]
      rw [WriterT.bind_def', WriterT.bind_def']
      congr 1
      apply bind_congr_of_forall_mem_support
      rintro ⟨⟨s, st, sent⟩, log⟩ hp
      have hw : (s, st, sent) ∈ support (stepRound worldRoles D B noFunctionality state steps) := by
        rw [← keygenEraseLog_stepRound, keygenEraseLog, support_map]
        exact ⟨_, hp, rfl⟩
      change Prod.map id (log ++ ·) <$>
          (executeRounds observedRoles D (capAdversary Q B) noFunctionality fuel s st).run = _
      rw [executeRounds_observed_cap fuel s st (hnext _ hw)]
      rfl

/-- The real rounds of the capped adversary equal those of the adversary from each network state
whose real rounds are within `Q`. -/
theorem executeRounds_world_cap (fuel : ℕ) (state : B.State)
    (steps : C.Party → Step C E RealSpec (Keys C))
    (h : IsQueryBoundP (executeRounds worldRoles D B noFunctionality fuel state steps)
      LifetimeCounted Q) :
    executeRounds worldRoles D (capAdversary Q B) noFunctionality fuel state steps =
      executeRounds worldRoles D B noFunctionality fuel state steps := by
  rw [← keygenEraseLog_executeRounds, ← keygenEraseLog_executeRounds]
  exact congrArg keygenEraseLog (executeRounds_observed_cap D B Q fuel state steps h)

end Rounds

section Phase

variable (D : C.Coalition) (B : Adversary C E Unit PEmpty PEmpty) (Q : ℕ)

/-- The start segment and the rounds from each start of the real keygen prefix are within `Q`. -/
def RealPrefixBound : Prop :=
  IsQueryBoundP (B.start (corruptInputs D fun _ => ()) []) Counted Q ∧
    ∀ state ∈ support (B.start (corruptInputs D fun _ => ()) []),
      ∀ steps ∈ support (startSteps worldRoles D fun i => (keygen i : PartyM C E RealSpec (Keys C))),
        IsQueryBoundP (executeRounds worldRoles D B noFunctionality setupRounds state steps)
          LifetimeCounted Q

/-- The capped real keygen phase is the real keygen phase. -/
theorem phase_real_cap (h : RealPrefixBound D B Q) :
    phase D (capAdversary Q B) false = phase D B false := by
  simp only [phase, Bool.false_eq_true, if_false, realExecution]
  change worldRoles.adversary (cap Q (B.start _ _)) >>= _ = _
  rw [cap_eq _ _ h.1]
  apply bind_congr_of_forall_mem_support
  intro state hstate
  rw [support_adversary] at hstate
  unfold executePhase
  apply bind_congr_of_forall_mem_support
  intro steps hsteps
  exact executeRounds_world_cap D B Q _ state steps (h.2 state hstate steps hsteps)

/-- Each initial network state of the emulated keygen is an initial network state of the real
keygen, and an honest operator in it waits. -/
theorem emulated_startSteps (parts : C.Party → Parts C)
    (hparts : parts ∈ support (free (C := C) (liftComp (Concrete.sequenceFin fun (_ : C.Party) =>
      (sampleParts : ProbComp (Parts C))) (LocalSpec C))))
    (steps : C.Party → Step C E RealSpec (Keys C))
    (hsteps : steps ∈ support (startSteps worldRoles D fun i =>
      (keygenWith i (parts i) : PartyM C E RealSpec (Keys C)))) :
    steps ∈ support (startSteps worldRoles D fun i => (keygen i : PartyM C E RealSpec (Keys C))) ∧
      ¬ ∀ i, i ∉ D.1 → (steps i).isDone := by
  rw [support_free, support_liftComp] at hparts
  have hpart := mem_support_sequenceFin _ parts hparts
  unfold startSteps at hsteps ⊢
  have hstep := mem_support_sequenceFin_oc _ steps hsteps
  refine ⟨mem_support_sequenceFin_of _ steps fun i => ?_, fun hd => ?_⟩
  · have hi := hstep i
    by_cases hD : i ∈ D.1
    · simpa only [hD, if_true] using hi
    · simp only [hD, if_false, worldRoles_honest, support_free] at hi ⊢
      rw [advance_keygen_sampling, mem_support_bind_iff]
      exact ⟨parts i, by rw [support_liftComp]; exact hpart i, hi⟩
  · obtain ⟨i, hi⟩ := keygen_exists_honest D
    have hs := hstep i
    simp only [hi, if_false, worldRoles_honest, support_free, advance_keygenWith,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hs
    obtain ⟨commitments, _, hc⟩ := hs
    have hd' := hd i hi
    rw [hc] at hd'
    exact hd'

/-- The emulation of the simulator with the capped adversary equals the emulation with the
adversary from each start whose real rounds are within `Q`. -/
theorem keygenEmulation_cap (st : SimulatorState C Unit B.State) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C))
    (h : ∀ steps ∈ support (startSteps worldRoles D fun i => (keygen i : PartyM C E RealSpec (Keys C))),
      IsQueryBoundP (executeRounds worldRoles D B noFunctionality setupRounds st.adversary steps)
        LifetimeCounted Q) :
    keygenEmulation D (capAdversary Q B) st parameter corrupt =
      keygenEmulation D B st parameter corrupt := by
  unfold keygenEmulation
  apply bind_congr_of_forall_mem_support
  intro parts hparts
  apply bind_congr_of_forall_mem_support
  intro steps hsteps
  obtain ⟨hreal, hdone⟩ := emulated_startSteps D parts hparts steps hsteps
  obtain ⟨hround, hnext⟩ := round_bound D B Q (setupRounds - 1) st.adversary steps hdone
    (h steps hreal)
  rw [stepRound_cap D B Q observedRoles st.adversary steps hround]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨s, st', sent⟩, log⟩ hp
  have hw : (s, st', sent) ∈ support (stepRound worldRoles D B noFunctionality st.adversary steps) := by
    rw [← keygenEraseLog_stepRound, keygenEraseLog, support_map]
    exact ⟨_, hp, rfl⟩
  change (do
      let high ← free (liftComp ($ᵗ HashOutput) _)
      keygenProgramBlock D parts (st.log ++ log) sent parameter corrupt high
      let ((state, keys), rest) ← (executeRounds observedRoles D (capAdversary Q B) noFunctionality
        (setupRounds - 1) s st').run
      pure ((⟨state, st.log ++ log ++ rest, st.corrupt⟩ : SimulatorState C Unit B.State), keys)) = _
  rw [executeRounds_observed_cap D B Q _ s st' (hnext _ hw)]
  rfl

/-- The adversary state of each simulator start is a start of the adversary. -/
theorem simulator_start_support (st : SimulatorState C Unit B.State)
    (hst : st ∈ support ((keygenSimulator D B).start (corruptInputs D fun _ => ()) [])) :
    st.adversary ∈ support (B.start (corruptInputs D fun _ => ()) []) := by
  have hst' : st ∈ support (observe (B.start (corruptInputs D fun _ => ()) []) >>= fun r =>
      (pure ⟨r.1, r.2, corruptInputs D fun _ => ()⟩ :
        OracleComp (WorldSpec C) (SimulatorState C Unit B.State))) := hst
  rw [mem_support_bind_iff] at hst'
  obtain ⟨r, hr, hs⟩ := hst'
  rw [support_pure, Set.mem_singleton_iff] at hs
  subst hs
  rw [← support_adversary, ← fst_observe, support_map]
  exact ⟨_, hr, rfl⟩

/-- The capped ideal keygen phase is the ideal keygen phase. -/
theorem phase_ideal_cap (h : RealPrefixBound D B Q) :
    phase D (capAdversary Q B) true = phase D B true := by
  simp only [phase, if_true]
  rw [idealExecution_Fkeygen, idealExecution_Fkeygen]
  have hstart : (keygenSimulator D (capAdversary Q B)).start (corruptInputs D fun _ => ()) [] =
      (keygenSimulator D B).start (corruptInputs D fun _ => ()) [] := by
    simp only [keygenSimulator, capAdversary]
    rw [cap_eq _ _ h.1]
  rw [hstart]
  apply bind_congr_of_forall_mem_support
  intro st hst
  have hadv := simulator_start_support D B st hst
  apply bind_congr
  rintro ⟨parameter, seeds, keys⟩
  simp only [keygenSimulator_answer_emulation]
  rw [keygenEmulation_cap D B Q st parameter _ (h.2 _ hadv)]
  rfl

end Phase

section Lifetime

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ)

/-- An all-answer budget of the real lifetime bounds its keygen prefix segment by segment. -/
theorem realPrefixBound_of_lifetime (circuits : Circuits)
    (h : IsQueryBoundP (lifetimeGame K circuits settings attempts D A) LifetimeCounted Q) :
    RealPrefixBound D A.keygen Q := by
  unfold lifetimeGame lifetimeGameWith at h
  refine ⟨counted_of_adversary _ _ (OracleComp.IsQueryBoundP.of_bind_left h), fun state hstate steps hsteps => ?_⟩
  have hphase := OracleComp.IsQueryBoundP.of_bind_left
    (continuation_bound_of_support _ _ _ _ h state (by rw [support_adversary]; exact hstate))
  unfold executePhase at hphase
  exact continuation_bound_of_support _ _ _ _ hphase steps hsteps

/-- Capping the keygen adversary is quiet in both keygen phases, for every `Th` of the lifetime. -/
theorem keygenCapQuiet (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
    (h : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (values : MpcDomain → HashOutput) :
    KeygenCapQuiet D A ⟨thOf values, aes⟩ Q := by
  have hb := realPrefixBound_of_lifetime K settings attempts D A Q _ (h values)
  intro ideal
  cases ideal
  · exact congrArg (fun p => (simulateQ (worldAnswer ⟨thOf values, aes⟩) p).run ∅)
      (phase_real_cap D A.keygen Q hb)
  · exact congrArg (fun p => (simulateQ (worldAnswer ⟨thOf values, aes⟩) p).run ∅)
      (phase_ideal_cap D A.keygen Q hb)

end Lifetime

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenCapQuiet.phase_real_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_real_cap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenCapQuiet.phase_ideal_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_ideal_cap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenCapQuiet.realPrefixBound_of_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realPrefixBound_of_lifetime

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenCapQuiet.keygenCapQuiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenCapQuiet

end ThresholdLeanXmssSecurity.LifetimeKeygenCapQuiet
