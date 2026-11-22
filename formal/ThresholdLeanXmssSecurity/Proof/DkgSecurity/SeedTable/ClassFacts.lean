import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.End
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Counts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.Birthday
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopCosts
import ThresholdLeanXmssSecurity.Proof.SigningStronglyUnforgeable

/-!
# The calls of the pieces of the shared rest

The pieces of the shared rest are a real run of a tree on the network, the dealer, its signing
oracles, the win test and a call of `forge`. This file bounds their calls of two predicates of the
world.

* `WorldProgramQuery` is a programming call. No piece makes one.
* `ClassCall` is a call of the class of the seed generation, on the counted copy or on the free
  copy. A real run makes at most `treeFuel * step` of them, all by the adversary, because the
  honest programs of a tree make none (`treeProgram_seedGen`). The dealer, its signing oracles and
  the win test make none.

`callCharge p` charges one for each call of `p`, and `cost_callCharge_le_iff` reads a bound on its
cost as `IsQueryBoundP`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open PFunctor.FreeM (costWith cost)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_sequenceFin)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## Counts as costs -/

section Charge

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- One for each call of `p`. -/
def callCharge (p : ι → Prop) (t : ι) : ℕ∞ := ((if p t then 1 else 0 : ℕ) : ℕ∞)

theorem cost_callCharge_le_iff (p : ι → Prop) {α : Type} (oa : OracleComp spec α) (n : ℕ) :
    cost (callCharge p) oa ≤ n ↔ IsQueryBoundP oa p n :=
  ((queryCostAtMost_iff_cost_le _ _ _).symm.trans
    (SigningStronglyUnforgeable.isQueryBoundP_iff_queryCostAtMost oa p n).symm)

theorem cost_map_eq (c : ι → ℕ∞) {α β : Type} (f : α → β) (oa : OracleComp spec α) :
    cost c (f <$> oa) = cost c oa :=
  PFunctor.FreeM.costWith_map' _ _ _

end Charge

/-! ## A real run of a tree -/

section Run

variable {E : Type} [Field E] [Algebra Bit E]

omit [Field E] [Algebra Bit E] in
/-- The record of a phase changes no cost. -/
theorem cost_executePhaseR (c : (WorldSpec C).Domain → ℕ∞) {I O L Rs Ia α ρ : Type} (D : C.Coalition)
    (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs) (blank : ρ) (fuel : ℕ) (st : A.State)
    (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) :
    cost c (executePhaseR worldRoles D A F blank fuel st program) =
      cost c (executePhase worldRoles D A F fuel st fun i => dropRecord (program i)) := by
  rw [executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D A F blank, cost_map_eq]

end Run

/-! ## The dealer -/

section Dealer

open DigestBudgets (RoIn noCall_of_onlySign noCall_eval)

/-- The signing oracles on the dealt keys `dealt` of `prfValue seeds` make no call of the class of
the seed generation. It is `noCall_tsigOracles` with the keys `dealt` of each operator in the place
of one key for all. -/
theorem noCall_tsigOracles_dealt (parameter : PublicParameter) (dealt : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (q : (TsigSpec C).Domain) (t : TsigState C) :
    NoCall (RoIn .seedGen) ((tsigOracles (fun oa => oa)
      (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds)) q).run t) := by
  have hc : HashClass.seedGen ≠ .signing := by decide
  have hbottom : ∀ (b : Fin (2 ^ layerHeight)) (s : TsigState C),
      NoCall (RoIn .seedGen) ((bottomOnce (dealtWith (fun oa => oa) parameter dealt top
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

/-- The win test on the dealt keys of `prfValue seeds` calls `H` only on `.hash` and `.prf`. It is
`onlySign_forgeryWins` with the bottom trees of the dealer in the place of the held bottom trees. -/
theorem onlySign_forgeryWins_dealt (parameter : PublicParameter) (dealt : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (st : TsigState C) (forgery : Forgery) :
    GameCount.OnlySign (forgeryWins (fun oa => oa) (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds))
      st forgery) := by
  unfold forgeryWins
  refine GameCount.onlySign_bind (GameCount.onlySign_tweakable _) fun verified => ?_
  dsimp only
  split_ifs
  · simp only [pure_bind]
    exact GameCount.onlySign_pure _
  refine GameCount.onlySign_bind ?_ fun _ => by simp only [pure_bind]; exact GameCount.onlySign_pure _
  unfold honestSignature
  refine GameCount.onlySign_bind (GameCount.onlySign_map _ (GameCount.onlySign_referenceTree _ _ _ _)) fun tree => ?_
  rcases tree with _ | tree
  · exact GameCount.onlySign_pure _
  refine GameCount.onlySign_bind (GameCount.onlySign_prfValue _ _) fun ρ => ?_
  refine GameCount.onlySign_bind (by unfold signCodeword; exact GameCount.onlySign_tweakable _) fun r => ?_
  rcases r with _ | ⟨randomness, encoding⟩
  · exact GameCount.onlySign_pure _
  refine GameCount.onlySign_bind (UsedHit.onlySign_sequenceFin _ fun l => ?_) fun _ =>
    GameCount.onlySign_bind (GameCount.onlySign_tweakable _) fun _ => GameCount.onlySign_pure _
  split
  · exact GameCount.onlySign_prfValue _ _
  · exact GameCount.onlySign_pure _
  · exact GameCount.onlySign_bind (GameCount.onlySign_prfValue _ _) fun _ => GameCount.onlySign_pure _

/-- The dealer of the world on the free copy is `freeHom` of the dealer on `H` and `PRG`. -/
theorem hmap_freeHom_dealt (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (top : TopTree) :
    SeedHitProof.Dealt.hmap DkgCompletenessProof.freeHom
      (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds)) = worldDealt₀ parameter seeds dealt top := by
  simp only [SeedHitProof.Dealt.hmap, worldDealt₀, dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]
  rfl

variable (cW : (WorldSpec C).Domain → ℕ∞)
  (hfree : ∀ {α : Type} (oa : OracleComp (RoSpec C) α), NoCall (RoIn .seedGen) oa →
    cost cW (DkgCompletenessProof.freeHom oa) ≤ 0)
include hfree

theorem cost_dealerTree (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    cost cW (referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) _))
      (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) ≤ 0 := by
  have e : referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) (LocalSpec C)))
      (fun x => free (liftComp (prfValue seeds x) (LocalSpec C))) parameter emptyTop .top =
      DkgCompletenessProof.freeHom (referenceTree tweakable (prfValue seeds) parameter emptyTop .top) :=
    (SeedHitProof.hom_referenceTree DkgCompletenessProof.freeHom tweakable (prfValue seeds) parameter emptyTop
      .top).symm
  rw [e]
  exact hfree _ (noCall_of_onlySign (by decide) (GameCount.onlySign_referenceTree _ _ _ _))

theorem cost_dealerOracles (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (top : TopTree) (q : (TsigSpec C).Domain) (st : TsigState C) :
    cost cW ((tsigOracles (fun oa => free (liftComp oa _)) (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0 := by
  have e := SeedHitProof.hom_tsigOracles DkgCompletenessProof.freeHom (fun oa => oa)
    (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds)) q st
  rw [hmap_freeHom_dealt] at e
  exact (le_of_eq (congrArg (cost cW) e.symm)).trans (hfree _ (noCall_tsigOracles_dealt _ _ _ _ _ _))

theorem cost_dealerWins (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (top : TopTree) (st : TsigState C) (forgery : Forgery) :
    cost cW (forgeryWins (fun oa => free (liftComp oa _)) (worldDealt₀ parameter seeds dealt top) st forgery) ≤ 0 := by
  have e := hom_forgeryWins DkgCompletenessProof.freeHom (fun oa => oa)
    (dealtWith (fun oa => oa) parameter dealt top (prfValue seeds)) st forgery
  rw [hmap_freeHom_dealt] at e
  exact (le_of_eq (congrArg (cost cW) e.symm)).trans
    (hfree _ (noCall_of_onlySign (by decide) (onlySign_forgeryWins_dealt _ _ _ _ _ _)))

end Dealer

/-! ## Programming calls -/

section Program

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

theorem cost_program_free {α : Type} (oa : OracleComp (RoSpec C) α) :
    cost (callCharge WorldProgramQuery) (DkgCompletenessProof.freeHom oa) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2 ((noCall_iff _ _).1 (Collision.noProgram_free _))

theorem cost_program_adversary (t : (LocalSpec C).Domain) :
    cost (callCharge WorldProgramQuery) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2 ((noCall_iff _ _).1 (Collision.noProgram_adversary _))

omit [Fintype E] [DecidableEq E] in
theorem cost_program_run (K : Constants C E) (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (s : RealState C net.State) (tree : Tree) :
    cost (callCharge WorldProgramQuery) (executePhaseR worldRoles D net noFunctionality ([] : Record C E)
      (treeFuel circuits settings) s.adversary fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) ≤ 0 := by
  rw [cost_executePhaseR]
  exact (cost_callCharge_le_iff _ _ 0).2 ((noCall_iff _ _).1 (Collision.noProgram_executePhase D net _ _ _))

end Program

/-! ## Calls of the class of the seed generation -/

section Class

/-- A call of the class of the seed generation, on the counted copy or on the free copy. -/
def ClassCall : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => InClass .seedGen t
  | .inl (.inr _) => False
  | .inr t => InClass .seedGen t

theorem cost_class_free {α : Type} (oa : OracleComp (RoSpec C) α) (h : NoCall (DigestBudgets.RoIn .seedGen) oa) :
    cost (callCharge ClassCall) (DkgCompletenessProof.freeHom oa) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2
    (DigestBudgets.free_liftComp_bound .seedGen ClassCall (fun _ => Iff.rfl) oa 0 ((noCall_iff _ _).1 h))

theorem cost_class_adversary (t : (LocalSpec C).Domain) :
    cost (callCharge ClassCall) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤
      callCharge (InClass .seedGen) t := by
  rw [ThresholdLeanXmssSecurity.adversary_query]
  exact (cost_query_le _).trans le_rfl

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

open DigestBudgets in
/-- The ceremonies of a tree at one operator make no call of the class of the seed generation. It is
`newTree_bound` for the class `seedGen`. -/
theorem newTree_seedGen (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    ClassBound .seedGen (newTree K circuits settings i keys top tree : PartyM C E RealSpec _) 0 := by
  have hrun := ceremonyOutput_bound settings (c := .seedGen) (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => lift_tweakable_bound (by decide) oa) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) _
    (fun jobs => ceremonyRun_bound K circuits settings (by decide) (by decide) (by decide) (by decide) i keys jobs)
    top tree (0, 0)
  have hzero : digestCost C .seedGen + copyCost C .seedGen = 0 := by simp [digestCost, copyCost]
  rw [hzero, Nat.mul_zero] at hrun
  unfold newTree
  refine (ClassBound.bind (m := 0) ?_ fun out => ?_).mono (Nat.add_zero _).le
  · unfold StateT.run'
    unfold ClassBound at hrun ⊢
    simp only [OptionT.run_map]
    exact (isQueryBoundP_map_iff _ _ _).2 hrun
  · rcases out with _ | output
    · exact ClassBound.failure
    · exact ClassBound.pure _

open DigestBudgets in
/-- The program of an operator in a run of a tree makes no call of the class of the seed generation. -/
theorem treeProgram_seedGen (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    ClassBound .seedGen (treeProgram K circuits settings i operator tree) 0 := by
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact ClassBound.failure
    · simp only [treeProgram, hk]
      exact newTree_seedGen K circuits settings _ _ _ _
  | bottom b =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact ClassBound.failure
    · simp only [treeProgram, hk]
      exact ClassBound.failure
    · simp only [treeProgram, hk, ht]
      exact ClassBound.failure
    · simp only [treeProgram, hk, ht]
      exact newTree_seedGen K circuits settings _ _ _ _

/-- A real run of a tree makes at most `treeFuel * step` calls of the class of the seed generation,
all of them by the adversary. -/
theorem cost_class_run (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (InClass .seedGen) step)
    (s : RealState C net.State) (tree : Tree) :
    cost (callCharge ClassCall) (executePhaseR worldRoles D net noFunctionality ([] : Record C E)
      (treeFuel circuits settings) s.adversary fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) ≤
      (treeFuel circuits settings * step : ℕ) := by
  rw [cost_executePhaseR, ← treeProgram_eq_drop K circuits settings s.operators tree, cost_callCharge_le_iff]
  have own := FirstCounts.ownAdds_executePhase .seedGen D net step hround (treeFuel circuits settings) s.adversary
    fun i => treeProgram K circuits settings i (s.operators i) tree
  have honest := DigestBudgets.executePhase_bound .seedGen D net (treeFuel circuits settings) s.adversary
    (fun i => treeProgram K circuits settings i (s.operators i) tree) (fun _ => 0)
    fun j _ => treeProgram_seedGen K circuits settings j _ tree
  simp only [Finset.sum_const_zero] at honest
  refine FirstCounts.isQueryBoundP_add (fun t ht => ?_) _ _ _ own honest
  rcases t with (t | t) | t
  · exact Or.inl ht
  · exact ht.elim
  · exact Or.inr ht

end Class

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.cost_class_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.cost_class_run

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.cost_dealerOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.cost_dealerOracles
