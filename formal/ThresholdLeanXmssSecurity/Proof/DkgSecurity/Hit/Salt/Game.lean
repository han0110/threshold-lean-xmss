import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Tree
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Count

/-!
# The free digest calls and the salt draws of the game with the keys of the dealer

* `worldSeedGen_quiet` states that the seed generation of the simulator makes no honest call of
  `TailLocal`. The honest operators run `seedGenWith`, which asks only cells of the class of the seed
  generation, and each other free call is a private sample.
* The rest of the game pays the honest calls of each run of a tree from the potential `runsLeft` of
  the runs that remain, in the cost calculus `RCost` and `RCostT` of `Hit/Count.lean`. The dealer,
  its signing oracles and the win test ask only `.hash` and `.prf`.
* `honest_dealtRun` bounds the honest calls of a predicate inside `TailLocal` in `dealtRun` with no
  emulated run by `runLimit` times the sum of the costs of one run of each tree. `digest_dealtRun` and
  `salt_dealtRun` are the two counts, each at `gameBatches * n * termCount C`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (PBound PState PartyP HonestP StepBoundP)
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets (ClassBound StateBound)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_mono noCall_query noCall_sequenceFin)
open PFunctor.FreeM (costWith cost costWith_mono costWith_le_cost_add)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

/-! ## The seed generation -/

section SeedGen

variable {C : Committee} {E : Type}

/-- A zero bound of a bind is a zero bound of the continuation at each result of the support. -/
theorem bound_zero_of_bind {ι α β : Type} {spec : OracleSpec ι} {P : ι → Prop} (oa : OracleComp spec α)
    (k : α → OracleComp spec β) (h : IsQueryBoundP (oa >>= k) P 0) : ∀ a ∈ support oa, IsQueryBoundP (k a) P 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro a' ha'
    simp only [support_pure, Set.mem_singleton_iff] at ha'
    subst ha'
    simpa using h
  | query_bind t f ih =>
    intro a ha
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    rw [mem_support_bind_iff] at ha
    obtain ⟨u, -, hu⟩ := ha
    have hn : ¬P t := h.1.resolve_right (by omega)
    exact ih u (by simpa [hn] using h.2 u) a hu

/-- A free call of a digest cell, which `HonestP TailLocal` counts. -/
def probe : OracleComp (WorldSpec C) Unit :=
  (liftM ((WorldSpec C).query (.inr (.inr (.inl (.digest [] 0))))) : OracleComp (WorldSpec C) _) >>= fun _ => pure ()

/-- A property of the results that each continuation with no honest call of `TailLocal` on it may
assume holds on the support. -/
theorem support_of_cont {α : Type} (oa : OracleComp (WorldSpec C) α) (Q : α → Prop)
    (h : ∀ k : α → OracleComp (WorldSpec C) Unit, (∀ a, Q a → IsQueryBoundP (k a) (HonestP TailLocal) 0) →
      IsQueryBoundP (oa >>= k) (HonestP TailLocal) 0) :
    ∀ a ∈ support oa, Q a := by
  intro a ha
  by_contra hq
  have hb := bound_zero_of_bind oa _ (h (fun a => if Q a then pure () else probe) fun a hqa => by
    simp only [hqa, ↓reduceIte]
    exact isQueryBoundP_pure _ _ _) a ha
  simp only [hq, ↓reduceIte, probe, isQueryBoundP_query_bind_iff] at hb
  have ht : HonestP (C := C) TailLocal (.inr (.inr (.inl (.digest [] 0)))) := ⟨[], 0, rfl⟩
  exact hb.1.resolve_right (lt_irrefl 0) ht

/-- The adversary role makes no honest call. -/
theorem quiet_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP (worldRoles.adversary oa) (HonestP (C := C) TailLocal) 0 :=
  SetupBudgets.honestP_adversary TailLocal oa

/-- A computation of the adversary makes no own call of the honest roles. -/
theorem quiet_round {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP oa (fun t => HonestP (C := C) TailLocal (.inl (.inl t))) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih => exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl not_false, fun u => by simpa using ih u⟩

/-- A vote round on inputs of the class `vote` makes no honest call of `TailLocal`. -/
theorem quiet_voteRound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (input : C.Party → Option (Query C)) (hin : ∀ j q, input j = some q → queryClass q = .vote) :
    IsQueryBoundP (voteRound worldRoles D net state input) (HonestP (C := C) TailLocal) 0 :=
  Vote.voteRound_isQueryBoundP D net state input _ 0 (fun _ _ => quiet_round _) fun j q hq h => by
    obtain ⟨salt, history, rfl⟩ := h
    exact absurd (hin j _ hq) (by simp [queryClass])

/-- A private sample on the free copy makes no call of `TailLocal`. -/
theorem quiet_free_prob {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (free (liftComp oa (LocalSpec C))) (HonestP (C := C) TailLocal) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simpa using ih u⟩

theorem quiet_observe {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP (observe oa) (HonestP (C := C) TailLocal) 0 := by
  have h := quiet_adversary oa
  rw [← fst_observe] at h
  exact (isQueryBoundP_map_iff _ _ _).1 h

theorem quiet_program (q : Query C) (value : HashOutput) :
    IsQueryBoundP (ThresholdLeanXmss.program q value) (HonestP (C := C) TailLocal) 0 := by
  unfold ThresholdLeanXmss.program counted
  erw [simulateQ_query]
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
  exact (noCall_iff _ _).1 (noCall_query _ _ (by simp [HonestP]))

/-- The start of honest programs with no call of `TailLocal` makes none and gives steps with none. -/
theorem startSteps_cont {α β : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ j, j ∉ D.1 → PBound TailLocal (program j) 0) (k : (C.Party → Step C E RealSpec α) → OracleComp (WorldSpec C) β)
    (hk : ∀ st, (∀ j, StepBoundP TailLocal (st j) 0) → IsQueryBoundP (k st) (HonestP TailLocal) 0) :
    IsQueryBoundP (startSteps worldRoles D program >>= k) (HonestP TailLocal) 0 := by
  unfold startSteps
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) =
      fun i => free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    funext i
    split_ifs
    · simp only [advance_pure, free_pure]
    · rfl
  change IsQueryBoundP ((OverPermutation.sequenceFin _) >>= _) _ _
  rw [he]
  refine (SetupBudgets.sequenceFin_free_advance_bindP TailLocal _ (fun _ => 0) ?_ k 0 ?_).mono (by simp)
  · intro j
    split_ifs with hj
    · exact isQueryBoundP_pure _ _ _
    · exact hp j hj
  · intro st b hb hs
    have hb0 : b = fun _ => 0 := funext fun i => Nat.le_zero.1 (hb i)
    subst hb0
    simpa using hk st hs

/-- One round on the real network from steps with no call of `TailLocal` makes none and gives such
steps. -/
theorem stepRound_cont {α β : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (h : ∀ j, StepBoundP TailLocal (steps j) 0)
    (k : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) → OracleComp (WorldSpec C) β)
    (hk : ∀ st, (∀ j, StepBoundP TailLocal (st.2.1 j) 0) → IsQueryBoundP (k st) (HonestP TailLocal) 0) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps >>= k) (HonestP TailLocal) 0 := by
  refine (SetupBudgets.stepRound_bind_boundP TailLocal D A state steps (fun _ => 0) h k 0 ?_).mono (by simp)
  intro st b hb hs
  have hb0 : b = fun _ => 0 := funext fun i => Nat.le_zero.1 (hb i)
  subst hb0
  simpa using hk st hs

theorem stepRound_observed_quiet {α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (h : ∀ j, StepBoundP TailLocal (steps j) 0) :
    IsQueryBoundP (stepRound observedRoles D A noFunctionality state steps).run (HonestP TailLocal) 0 ∧
      ∀ r ∈ support (stepRound observedRoles D A noFunctionality state steps).run,
        ∀ j, StepBoundP TailLocal (r.1.2.1 j) 0 := by
  have e := seedGenEraseLog_stepRound D A state steps
  unfold seedGenEraseLog at e
  constructor
  · have hb := stepRound_cont D A state steps h pure fun _ _ => isQueryBoundP_pure _ _ _
    rw [bind_pure, ← e] at hb
    exact (isQueryBoundP_map_iff _ _ _).1 hb
  · intro r hr
    have hs := support_of_cont (stepRound worldRoles D A noFunctionality state steps)
      (fun st => ∀ j, StepBoundP TailLocal (st.2.1 j) 0) fun k hk => stepRound_cont D A state steps h k hk
    refine hs r.1 ?_
    rw [← e, support_map]
    exact ⟨r, hr, rfl⟩

theorem executeRounds_observed_quiet {α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ)
    (state : A.State) (steps : C.Party → Step C E RealSpec α) (h : ∀ j, StepBoundP TailLocal (steps j) 0) :
    IsQueryBoundP (executeRounds observedRoles D A noFunctionality fuel state steps).run (HonestP TailLocal) 0 := by
  have hb := (SetupBudgets.executeRounds_boundP TailLocal D A fuel state steps (fun _ => 0) h).mono
    (le_of_eq (by simp) : ∑ _j : C.Party, (0 : ℕ) ≤ 0)
  rw [← seedGenEraseLog_executeRounds] at hb
  exact (isQueryBoundP_map_iff _ _ _).1 hb

theorem seedGenWith_quiet (i : C.Party) (own : Parts C) :
    PBound TailLocal (seedGenWith i own : PartyM C E RealSpec (Keys C)) 0 := by
  unfold seedGenWith
  exact PBound.of_classes
    (DigestBudgets.ClassBound.bind (n := 0) (m := 0) (DigestBudgets.commitRevealEcho_bound (phase := .seedGen)
      (by decide) _ _) fun _ => DigestBudgets.ClassBound.pure _)
    (DigestBudgets.ClassBound.bind (n := 0) (m := 0) (DigestBudgets.commitRevealEcho_bound (phase := .seedGen)
      (by decide) _ _) fun _ => DigestBudgets.ClassBound.pure _)

/-- The seed generation of the simulator makes no honest call of `TailLocal`. -/
theorem worldSeedGen_quiet (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    IsQueryBoundP (worldSeedGen D net) (HonestP TailLocal) 0 := by
  unfold worldSeedGen
  refine isQueryBoundP_bind (n := 0) (m := 0) (quiet_observe _) fun p _ => ?_
  obtain ⟨state, early⟩ := p
  refine isQueryBoundP_bind (n := 0) (m := 0) (quiet_free_prob _) fun x _ => ?_
  obtain ⟨parameter, seeds, dealt⟩ := x
  refine isQueryBoundP_bind (n := 0) (m := 0) (quiet_free_prob _) fun parts _ => ?_
  refine startSteps_cont D _ (fun j _ => seedGenWith_quiet j _) _ fun steps hsteps => ?_
  obtain ⟨hround, hsupp⟩ := stepRound_observed_quiet D net state steps hsteps
  refine isQueryBoundP_bind (n := 0) (m := 0) hround fun r hr => ?_
  obtain ⟨⟨state', steps', sent⟩, calls⟩ := r
  have hs' := hsupp _ hr
  refine isQueryBoundP_bind (n := 0) (m := 0) (quiet_free_prob _) fun high _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) (quiet_program _ _) fun _ _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) ((noCall_iff _ _).1 (noCall_mapM _ _ _ fun T => ?_)) fun _ _ => ?_
  · split
    · exact (noCall_iff _ _).2 (quiet_program _ _)
    · exact noCall_pure _ _
  refine isQueryBoundP_bind (n := 0) (m := 0) ((noCall_iff _ _).1 (noCall_mapM _ _ _ fun j =>
    noCall_mapM _ _ _ fun i => ?_)) fun _ _ => ?_
  · split
    · exact (noCall_iff _ _).2 (quiet_program _ _)
    · exact noCall_pure _ _
  exact isQueryBoundP_bind (n := 0) (m := 0) (executeRounds_observed_quiet D net _ state' steps' hs') fun _ _ =>
    isQueryBoundP_pure _ _ _

end SeedGen

variable {C : Committee}

/-! ## The dealer -/

section Dealer

variable {C : Committee}

open DigestBudgets (RoIn noCall_of_onlySign noCall_eval)

namespace Salt

/-- The signing oracles on the dealt keys `dealt` of `prfValue seeds` make no call of a class other than
`signing`. -/
theorem noCall_tsigOracles_dealt {c : HashClass} (hc : c ≠ .signing) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (q : (TsigSpec C).Domain) (t : TsigState C) :
    NoCall (RoIn c) ((tsigOracles (fun oa => oa)
      (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds)) q).run t) := by
  have hbottom : ∀ (b : Fin (2 ^ layerHeight)) (s : TsigState C),
      NoCall (RoIn c) ((bottomOnce (dealtWith (fun oa => oa) parameter dealt top
        (prfValue seeds)) b).run s) := by
    intro b s
    simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, StateT.run_modify,
        StateT.run_pure, pure_bind]
      refine noCall_bind _ (noCall_map _ _ (noCall_of_onlySign hc (GameCount.onlySign_referenceTree _ _ _ _)))
        fun _ => noCall_pure _ _
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind]
      exact noCall_pure _ _
  · simp only [tsigOracles, StateT.run_bind]
    refine noCall_bind _ (hbottom b t) fun ⟨o, st⟩ => ?_
    rcases o with _ | tree
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact noCall_bind _ (noCall_of_onlySign hc (GameCount.onlySign_prfValue _ _)) fun _ => noCall_pure _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind]
      exact noCall_bind _ (noCall_bind _ (noCall_eval hc _ _ _ _ _) fun _ => noCall_pure _ _) fun _ =>
        noCall_pure _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact noCall_pure _ _
    · simp only [StateT.run_bind]
      refine noCall_bind _ (hbottom _ t) fun ⟨o, st⟩ => ?_
      rcases o with _ | tree
      · exact noCall_pure _ _
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
        refine noCall_bind _ (noCall_eval hc _ _ _ _ _) fun own => ?_
        refine noCall_bind _ ?_ fun r => ?_
        · unfold signRound2With
          refine noCall_bind _ (noCall_of_onlySign hc ?_) fun r => ?_
          · unfold signCodeword
            exact GameCount.onlySign_tweakable _
          · rcases r with _ | ⟨_, encoding⟩
            · exact noCall_pure _ _
            · refine noCall_bind _ (noCall_sequenceFin _ _ fun l => ?_) fun _ => noCall_pure _ _
              split_ifs
              · exact noCall_map _ _ (noCall_eval hc _ _ _ _ _)
              · exact noCall_pure _ _
        · rcases r with ⟨_ | values, st'⟩
          · exact noCall_pure _ _
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
            exact noCall_pure _ _

end Salt

/-- A computation of `H` and `PRG` with no call of the classes `digest` and `stream` makes no call of
`TailCall`. -/
theorem noCall_tail_of_classes {α : Type} {oa : OracleComp (RoSpec C) α} (h₁ : NoCall (RoIn .digest) oa)
    (h₂ : NoCall (RoIn .stream) oa) : NoCall TailCall oa :=
  (noCall_iff _ _).2 (isQueryBoundP_zero_of_or (fun t ht => tail_classes (.inr t) ht)
    ((noCall_iff _ _).1 h₁) ((noCall_iff _ _).1 h₂))

/-- A computation of `H` and `PRG` with no call of `TailCall` makes no honest call of `TailLocal` on the
free copy. -/
theorem quiet_freeHom {α : Type} (oa : OracleComp (RoSpec C) α) (h : NoCall TailCall oa) :
    IsQueryBoundP (DkgCompletenessProof.freeHom oa) (HonestP (C := C) TailLocal) 0 := by
  change IsQueryBoundP (free (liftComp oa (LocalSpec C))) _ 0
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬TailCall t := h.1.resolve_right (by omega)
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inr t))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    have ht' : ¬HonestP (C := C) TailLocal (.inr (.inr t)) := ht
    rw [e, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ht', fun u => ?_⟩
    have hu := ih u (by simpa [ht] using h.2 u)
    simpa [ht'] using hu

variable (cW : (WorldSpec C).Domain → ℕ∞)
  (hfree : ∀ {α : Type} (oa : OracleComp (RoSpec C) α), NoCall TailCall oa →
    cost cW (DkgCompletenessProof.freeHom oa) ≤ 0)
include hfree

namespace Salt

/-- The top tree of the dealer costs nothing when free calls with no call of `TailCall` cost nothing. -/
theorem cost_dealerTree (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    cost cW (referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) _))
      (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) ≤ 0 := by
  have e : referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) (LocalSpec C)))
      (fun x => free (liftComp (prfValue seeds x) (LocalSpec C))) parameter emptyTop .top =
      DkgCompletenessProof.freeHom (referenceTree tweakable (prfValue seeds) parameter emptyTop .top) :=
    (SeedHitProof.hom_referenceTree DkgCompletenessProof.freeHom tweakable (prfValue seeds) parameter emptyTop
      .top).symm
  rw [e]
  exact hfree _ (noCall_tail_of_classes (noCall_of_onlySign (by decide) (GameCount.onlySign_referenceTree _ _ _ _))
    (noCall_of_onlySign (by decide) (GameCount.onlySign_referenceTree _ _ _ _)))

/-- The signing oracles of the dealer cost nothing when free calls with no call of `TailCall` cost nothing. -/
theorem cost_dealerOracles (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (top : TopTree) (q : (TsigSpec C).Domain) (st : TsigState C) :
    cost cW ((tsigOracles (fun oa => free (liftComp oa _)) (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0 := by
  have e := SeedHitProof.hom_tsigOracles DkgCompletenessProof.freeHom (fun oa => oa)
    (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds)) q st
  rw [hmap_freeHom_dealt] at e
  exact (le_of_eq (congrArg (cost cW) e.symm)).trans (hfree _ (noCall_tail_of_classes
    (noCall_tsigOracles_dealt (by decide) _ _ _ _ _ _) (noCall_tsigOracles_dealt (by decide) _ _ _ _ _ _)))

/-- The win test of the dealer costs nothing when free calls with no call of `TailCall` cost nothing. -/
theorem cost_dealerWins (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (top : TopTree) (st : TsigState C) (forgery : Forgery) :
    cost cW (forgeryWins (fun oa => free (liftComp oa _)) (worldDealt₀ parameter seeds dealt top) st forgery) ≤ 0 := by
  have e := hom_forgeryWins DkgCompletenessProof.freeHom (fun oa => oa)
    (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds)) st forgery
  rw [hmap_freeHom_dealt] at e
  exact (le_of_eq (congrArg (cost cW) e.symm)).trans
    (hfree _ (noCall_tail_of_classes (noCall_of_onlySign (by decide) (onlySign_forgeryWins_dealt _ _ _ _ _ _))
      (noCall_of_onlySign (by decide) (onlySign_forgeryWins_dealt _ _ _ _ _ _))))

end Salt

end Dealer


/-! ## The rest of the game with no emulated run -/

section Rest

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)
  (runCost : Tree → ℕ)

variable {p : (LocalSpec C).Domain → Prop} (hp : ∀ t, p t → TailLocal t)
  (htree : ∀ (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State),
    IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
      s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestP p) (runCost tree))

include hp in
theorem honestP_of_tail (t : (WorldSpec C).Domain) (h : HonestP p t) : HonestP TailLocal t := by
  rcases t with _ | t
  · exact h.elim
  · exact hp t h

include hp in
theorem cost_free_tail {α : Type} (oa : OracleComp (RoSpec C) α) (h : NoCall TailCall oa) :
    cost (callCharge (HonestP p)) (DkgCompletenessProof.freeHom oa) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2 (IsQueryBoundP.of_imp (honestP_of_tail hp) (quiet_freeHom oa h))

omit [Fintype E] [DecidableEq E] in
include hp htree in
/-- One real run of `tree` from a state with fewer than `runLimit` runs of `tree` costs its part of
the potential. -/
theorem cost_treeRun (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (hs : s.runs tree < runLimit) :
    costWith (callCharge (HonestP p)) ((treeRun K circuits settings noMonitor D net tree).run s)
      (fun z => runsLeft runLimit runCost z.2) ≤ runsLeft runLimit runCost s := by
  unfold treeRun
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  have hpot : ((runCost tree : ℕ) : ℕ∞) + ((FirstCounts.remaining runLimit runCost
      (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞) = runsLeft runLimit runCost s := by
    rw [runsLeft, ← FirstCounts.remaining_update runLimit _ s.runs tree hs, Nat.cast_add, add_comm]
  refine (?_ : RCost (callCharge (HonestP p)) _ (fun _ s' => runsLeft runLimit runCost s')
    fun _ => runsLeft runLimit runCost s) s
  refine RCost.bind (K := fun _ _ => ((FirstCounts.remaining runLimit runCost
      (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((RCost.lift ((cost_callCharge_le_iff _ _ _).2 (htree net tree s)) _).mono
      (fun _ _ => le_rfl) fun _ => hpot.le) fun r => ?_
  obtain ⟨state, outputs⟩ := r
  refine RCost.bind (K := fun _ _ => ((FirstCounts.remaining runLimit runCost
      (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((RCost.lift (cost_pure_le _ _ 0) _).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _)) fun bad => ?_
  refine RCost.bind (K := fun _ _ => ((FirstCounts.remaining runLimit runCost
      (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((RCost.lift ((cost_callCharge_le_iff _ _ 0).2 (IsQueryBoundP.of_imp (honestP_of_tail hp)
      (quiet_voteRound D net state _ fun _ _ => queryClass_map_treeVote))) _).mono (fun _ _ => le_rfl)
      fun _ => le_of_eq (zero_add _)) fun v => ?_
  exact (RCost.set _ _).mono (fun _ _ => le_rfl) fun _ => le_rfl

omit [Fintype E] [DecidableEq E] in
include hp htree in
theorem cost_secRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) (s : RealState C net.State) (hs : s.runs tree < runLimit) :
    costWith (callCharge (HonestP p)) ((secRun K circuits settings m D net parameter seeds dealt emu tree).run s)
      (fun z => runsLeft runLimit runCost z.2) ≤ runsLeft runLimit runCost s := by
  unfold secRun
  rw [StateT.run_bind, StateT.run_get, pure_bind, ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _)]
  exact cost_treeRun K circuits settings runLimit D runCost hp htree net tree s hs

omit [Fintype E] [DecidableEq E] in
include hp htree in
theorem rcost_secRuns (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, RCost (callCharge (HonestP p)) (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count)
      (fun _ s => runsLeft runLimit runCost s) (runsLeft runLimit runCost)
  | 0 => RCost.pure _ _
  | count + 1 => by
    have rest := rcost_secRuns m hm net parameter seeds dealt emu tree count
    unfold secRuns
    refine RCost.get_bind fun s => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h, StateT.run_bind, PFunctor.FreeM.costWith_bind']
      refine le_trans (costWith_mono _ fun z => ?_)
        (cost_secRun K circuits settings runLimit D runCost hp htree m hm net parameter seeds dealt emu tree s
          (FirstCounts.mayRun_lt runLimit h))
      exact rest z.2
    · rw [ite_eq_right h]
      exact le_rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The signing oracles of a dealer on the computations of the world. -/
theorem rcostT_tsig {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C)
    (htsig : ∀ st, cost (callCharge (HonestP p)) ((tsigOracles (fun oa => free (liftComp oa _)) d q).run st) ≤ 0)
    (Ψ : RealState C σ → ℕ∞) :
    RCostT (callCharge (HonestP p))
      (tsigOracles (realLift (σ := σ)) (SeedHitProof.Dealt.hmap (realHom σ) d) q)
      (fun _ s => Ψ s) (fun s => 0 + Ψ s) := fun st =>
  (RCost.lift (htsig st) Ψ).of_eq
    (SeedHitProof.hom_tsigOracles (realHom σ) (fun oa => free (liftComp oa _)) d q st)

omit [Fintype E] [DecidableEq E] in
include hp htree in
theorem rcostT_secOracles (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (top : TopTree) (q : TsigQuery C) :
    RCostT (callCharge (HonestP p))
      (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (realHom A.net.State) (worldDealt₀ parameter seeds dealt top)) q)
      (fun _ s => runsLeft runLimit runCost s) (fun s => 0 + runsLeft runLimit runCost s) := by
  have htsig : ∀ q st, cost (callCharge (HonestP p)) ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0 :=
    Salt.cost_dealerOracles _ (fun oa h => cost_free_tail hp oa h) parameter seeds dealt top
  unfold secOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact (RCostT.pure _ _).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm
  · dsimp only
    unfold secTreeRequest
    refine RCostT.bind (K := fun _ s => runsLeft runLimit runCost s)
      ((rcostT_tsig _ _ (htsig _) _).mono (fun _ _ => le_rfl) fun _ => le_rfl) fun answer => ?_
    have tail : RCostT (callCharge (HonestP p)) (StateT.lift get >>= fun s : RealState C A.net.State =>
        match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => pure (some (tree, ρ))
        | _, _ => pure none : StateT (TsigState C) (RealM C A.net.State) _)
        (fun _ s => runsLeft runLimit runCost s) (fun s => runsLeft runLimit runCost s) := by
      refine RCostT.get_bind fun s st => ?_
      split <;> exact le_rfl
    by_cases hc : m.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      exact RCostT.bind (RCostT.lift (rcost_secRuns K circuits settings runLimit D runCost hp htree m hm A.net
        parameter seeds dealt emu _ 1)) fun _ => tail
    · simp only [hc, ↓reduceIte]
      exact tail
  all_goals
    dsimp only
    unfold secSignRequest
    refine RCostT.bind (K := fun _ s => runsLeft runLimit runCost s)
      ((RCostT.lift (RCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm) fun _ => ?_
    refine RCostT.get_bind fun s st => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first
        | exact ((rcostT_tsig _ _ (htsig _) _) st s).trans (le_of_eq (zero_add _))
        | exact le_rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem cost_adversary_honest (t : (LocalSpec C).Domain) :
    cost (callCharge (HonestP p)) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2 (SetupBudgets.honestP_adversary p _)

omit [Fintype E] [DecidableEq E] in
include hp htree in
/-- The signing phase with the answers of the dealer costs the runs that remain. -/
theorem rcost_secSigning (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    RCost (callCharge (HonestP p)) (secSigning K circuits settings runLimit m D A parameter seeds dealt emu)
      (fun _ _ => 0) (fun s => 0 + runsLeft runLimit runCost s) := by
  unfold secSigning
  refine RCost.get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact zero_le
  | some kt =>
    simp only
    unfold worldDealer
    simp only [bind_assoc, pure_bind]
    have e₂ : referenceTree (fun oa => realLift (σ := A.net.State) (tweakable oa)) (fun x => realLift (prfValue seeds x))
        parameter emptyTop .top = realHom A.net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (realHom A.net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    rw [e₂]
    refine (?_ : RCost (callCharge (HonestP p)) _ (fun _ _ => 0) fun s => 0 + runsLeft runLimit runCost s) s
    refine RCost.bind (K := fun _ s => 0 + runsLeft runLimit runCost s)
      ((RCost.lift (Salt.cost_dealerTree _ (fun oa h => cost_free_tail hp oa h) _ _) _).mono (fun _ _ => le_rfl)
        fun _ => le_of_eq (zero_add _)) fun out => ?_
    have d₂ : dealtWith (realLift (σ := A.net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₂]
    refine RCost.bind (K := fun _ s => runsLeft runLimit runCost s)
      (((RCostT.simulateQ (c := callCharge (HonestP p)) _ (forgeCharge (fun _ => 0))
        (runsLeft runLimit runCost) (fun t => ?_) _) _).mono
        (fun _ _ => le_rfl) fun s => add_le_add (by rw [forgeCharge_zero]; exact cost_zero_le _) le_rfl) fun z => ?_
    · rcases t with t | q | q
      · exact (RCostT.lift (RCost.lift (cost_adversary_honest t) _)).mono (fun _ _ => le_rfl) fun _ => le_rfl
      · exact rcostT_secOracles K circuits settings runLimit D runCost hp htree m hm A parameter seeds dealt emu _ q
      · rcases q with _ | state
        · exact (RCostT.lift (RCost.map_get _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
        · exact (RCostT.lift (RCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
    · rcases z with ⟨forgery, st⟩
      exact ((RCost.lift (Salt.cost_dealerWins _ (fun oa h => cost_free_tail hp oa h) _ _ _ _ st forgery)
        fun _ => 0).of_eq (hom_forgeryWins (realHom A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)).mono
          (fun _ _ => le_rfl) fun _ => by simp

omit [Fintype E] [DecidableEq E] in
include hp htree in
theorem rcost_secRest (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    RCost (callCharge (HonestP p)) (secRest K circuits settings runLimit m D A parameter seeds dealt emu)
      (fun _ _ => 0) (fun s => 0 + runsLeft runLimit runCost s) := by
  unfold secRest
  refine RCost.get_bind fun s => ?_
  refine (RCost.bind (K := fun _ _ => 0 + runsLeft runLimit runCost s) (k := fun _ _ => (0 : ℕ∞))
    ((RCost.lift ((cost_callCharge_le_iff _ _ 0).2 (IsQueryBoundP.of_imp (honestP_of_tail hp)
      (quiet_voteRound D A.net s.adversary _ fun _ _ => queryClass_map_seedVote))) fun _ =>
        0 + runsLeft runLimit runCost s).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _))
    fun v => ?_) s
  obtain ⟨state, ok⟩ := v
  refine RCost.bind ((RCost.set _ (fun _ s => 0 + runsLeft runLimit runCost s)).mono
    (fun _ _ => le_rfl) fun _ => le_rfl) fun _ => ?_
  exact RCost.bind (K := fun _ s => 0 + runsLeft runLimit runCost s)
    ((rcost_secRuns K circuits settings runLimit D runCost hp htree m hm A.net parameter seeds dealt (committed ok emu)
      .top runLimit).frame 0 |>.mono (fun _ s => le_of_eq (add_comm _ _)) fun s => le_of_eq (add_comm _ _))
    fun _ => rcost_secSigning K circuits settings runLimit D runCost hp htree m hm A parameter seeds dealt
      (committed ok emu)

end Rest

/-! ## The game -/

section GameCount

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

omit [Fintype E] [DecidableEq E] in
/-- `dealtRun` with no emulated run makes at most `runLimit` times the sum of the costs of one run of
each tree of honest calls of a predicate inside `TailLocal`. -/
theorem honest_dealtRun {p : (LocalSpec C).Domain → Prop} (hp : ∀ t, p t → TailLocal t) (runCost : Tree → ℕ)
    (htree : ∀ (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State),
      IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
        s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestP p) (runCost tree))
    (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) :
    IsQueryBoundP (dealtRun K circuits settings runLimit m D A) (HonestP p)
      (runLimit * (runCost .top + ∑ b : Fin (2 ^ layerHeight), runCost (.bottom b))) := by
  rw [← cost_callCharge_le_iff]
  unfold dealtRun
  refine (cost_bind_le_add (n := 0) ((cost_callCharge_le_iff _ _ 0).2
    (IsQueryBoundP.of_imp (honestP_of_tail hp) (worldSeedGen_quiet D A.net)))
    (m := ((runLimit * (runCost .top + ∑ b : Fin (2 ^ layerHeight), runCost (.bottom b)) : ℕ) : ℕ∞))
    fun x => ?_).trans (le_of_eq (zero_add _))
  obtain ⟨state, parameter, seeds, dealt, emu⟩ := x
  refine (cost_bind_le_add (m := 0) ?_ fun _ => cost_pure_le _ _ _).trans (le_of_eq (add_zero _))
  rw [StateT.run'_eq, cost_map_eq]
  have h := rcost_secRest K circuits settings runLimit D runCost hp htree m hm A parameter seeds dealt emu
    (startState D state fun i => (emu i).map fun _ => dealt i)
  refine h.trans (le_of_eq ?_)
  change 0 + ((FirstCounts.remaining runLimit runCost (fun _ => 0) : ℕ) : ℕ∞) = _
  rw [zero_add, show FirstCounts.remaining runLimit runCost (fun _ => 0) =
    runLimit * (runCost .top + ∑ b : Fin (2 ^ layerHeight), runCost (.bottom b)) by
      simp only [FirstCounts.remaining, Nat.sub_zero, ← Finset.mul_sum]; ring]

omit [Fintype E] [DecidableEq E] in
/-- The game with the keys of the dealer and no emulated run makes at most
`gameBatches * n * termCount C` free calls of a digest cell, under all salts together. -/
theorem digest_dealtRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) :
    IsQueryBoundP (dealtRun K circuits settings runLimit m D A) (HonestP DigestCall)
      (gameBatches settings runLimit * C.n * termCount C) := by
  refine (honest_dealtRun K circuits settings runLimit D digestCall_tail _
    (fun net tree s => treeDigest K circuits settings D net tree s) m hm A).mono (le_of_eq ?_)
  unfold gameBatches
  simp only [← Finset.sum_mul]
  ring

omit [Fintype E] [DecidableEq E] in
/-- The game with the keys of the dealer and no emulated run makes at most
`gameBatches * n * termCount C` calls of `PRG` at the stream index 2 and the position 0 under the name of
a term, one for each draw of a salt. -/
theorem salt_dealtRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) :
    IsQueryBoundP (dealtRun K circuits settings runLimit m D A) (HonestP SaltDraw)
      (gameBatches settings runLimit * C.n * termCount C) := by
  refine (honest_dealtRun K circuits settings runLimit D saltDraw_tail _
    (fun net tree s => treeSalt K circuits settings D net tree s) m hm A).mono (le_of_eq ?_)
  unfold gameBatches
  simp only [← Finset.sum_mul]
  ring

end GameCount

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.worldSeedGen_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.worldSeedGen_quiet

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.digest_dealtRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.digest_dealtRun

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.salt_dealtRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.salt_dealtRun
