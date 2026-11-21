import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets

/-!
# The honest budgets of the echo hashes and of the derived keys of the PRSS setups

The network bound of `HonestBudgets.lean` holds for each predicate `p` on the local calls.
`treeHonestP` bounds the honest calls of `p` in one run of a tree by `n` times the calls of
one operator, when the calls of `p` are in the class `prssSetup`. The PRSS setup of one operator makes
at most `n` echo hashes and at most `termCount C + n` derivations.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace SetupBudgets

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_mono noCall_sequenceFin noCall_query)
open DigestBudgets (ClassBound StateBound)

attribute [local instance] Classical.propDecidable

/-! ## The PRSS setup of one operator -/

section Setup

variable {C : Committee} {E : Type} {p : (LocalSpec C).Domain → Prop}

/-- The PRSS setup of one operator makes the calls of `p` of its derivation and of its `n` echo
hashes, when its commitments make none. -/
theorem commitRevealEcho_pbound (hp : ∀ t, p t → InClass .prssSetup t) (i : C.Party) (own : Parts C) (a b : ℕ)
    (hcommit : ∀ j k l, ¬ p (.inr (.inl (.commit .prss j k l))))
    (hderive : ∀ view, IsQueryBoundP (deriveKeys .prss i view) (fun t => p (.inr t)) a)
    (hshared : ∀ l, IsQueryBoundP (hashQuery (C := C) (.sharedKeys .prss l)) (fun t => p (.inr t)) b) :
    PBound p (commitRevealEcho .prss i own : PartyM C E RealSpec _) (a + C.parties.length * b) := by
  have hc : ∀ j k l, IsQueryBoundP (hashQuery (C := C) (.commit .prss j k l)) (fun t => p (.inr t)) 0 :=
    fun j k l => (noCall_iff _ _).1 (noCall_query _ _ (hcommit j k l))
  have hzero : ∀ (l : List C.Party) (f : C.Party → Query C), (∀ j, ∃ x y z, f j = .commit .prss x y z) →
      IsQueryBoundP (l.mapM fun j => hashQuery (f j)) (fun t => p (.inr t)) 0 := fun l f hf => by
    simpa using queryBound_mapM _ _ 0 l fun j _ => by
      obtain ⟨x, y, z, e⟩ := hf j
      rw [e]
      exact hc x y z
  have hex : ∀ outbox : Mail C E, PBound p (exchange outbox : PartyM C E RealSpec _) 0 :=
    fun outbox => PBound.of_class hp (DigestBudgets.ClassBound.exchange outbox)
  have hreq : ∀ q : Prop, PBound p (require q : PartyM C E RealSpec Unit) 0 :=
    fun q => PBound.of_class hp (DigestBudgets.ClassBound.require q)
  unfold commitRevealEcho
  refine (PBound.bind (n := 0) (PBound.oracleStep (hzero _ _ fun j => ⟨_, _, _, rfl⟩)) fun _ =>
    PBound.bind (n := 0) (hex _) fun _ => PBound.bind (n := 0) (hex _) fun _ =>
    PBound.bind (n := 0) (PBound.oracleStep (hzero _ _ fun j => ⟨_, _, _, rfl⟩)) fun _ =>
    PBound.bind (n := 0) (hreq _) fun _ => PBound.bind (PBound.oracleStep (hderive _)) fun _ =>
    PBound.bind (PBound.oracleStep (queryBound_mapM _ _ b C.parties fun j _ => hshared _)) fun _ =>
    PBound.bind (n := 0) (hex _) fun _ => PBound.bind (n := 0) (hreq _) fun _ => PBound.pure _).mono (by omega)

/-- The PRSS setup of one operator, with its sampled parts. -/
theorem prssSetup_pbound (hp : ∀ t, p t → InClass .prssSetup t) (i : C.Party) (a b : ℕ)
    (hcommit : ∀ j k l, ¬ p (.inr (.inl (.commit .prss j k l))))
    (hderive : ∀ view, IsQueryBoundP (deriveKeys .prss i view) (fun t => p (.inr t)) a)
    (hshared : ∀ l, IsQueryBoundP (hashQuery (C := C) (.sharedKeys .prss l)) (fun t => p (.inr t)) b) :
    PBound p (prssSetup i : PartyM C E RealSpec _) (a + C.parties.length * b) := by
  unfold prssSetup prssSetupWith
  refine (PBound.bind (n := 0) (PBound.localStep ((DigestBudgets.liftComp_prob_bound .prssSetup _).of_imp hp))
    fun own => PBound.bind (m := 0) (commitRevealEcho_pbound hp i own a b hcommit hderive hshared)
      fun _ => PBound.pure _).mono (by omega)

/-- A derivation of the PRSS setup makes at most `termCount C + n` calls. -/
theorem deriveKeys_count (q : (RoSpec C).Domain → Prop) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys .prss i view) q (C.terms.length + C.parties.length) := by
  have h1 : ∀ x : Query C, IsQueryBoundP (hashQuery x) q 1 := fun x =>
    (hashQuery_queryBound x).of_imp fun _ _ => trivial
  unfold deriveKeys
  refine (isQueryBoundP_bind (n := 0) ?_ fun _ _ => isQueryBoundP_bind (queryBound_mapM q _ 1 _ fun T _ => ?_)
    fun _ _ => isQueryBoundP_bind (queryBound_mapM q _ 1 _ fun j _ => ?_)
      fun _ _ => isQueryBoundP_pure _ _ 0).mono (by simp)
  · exact isQueryBoundP_pure _ _ _
  · split_ifs
    · exact h1 _
    · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · split
    · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · exact h1 _

/-- A derivation of the PRSS setup makes no call of `p` when no derived key is a call of `p`. -/
theorem deriveKeys_zero (i : C.Party) (view : C.Party → Parts C)
    (hq : ∀ kind l, ¬ p (.inr (.inl (.derive .prss kind l)))) :
    IsQueryBoundP (deriveKeys .prss i view) (fun t => p (.inr t)) 0 := by
  rw [← noCall_iff]
  unfold deriveKeys
  refine noCall_bind _ (by exact noCall_pure _ _) fun _ => noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ =>
    noCall_bind _ (noCall_mapM _ _ _ fun j => ?_) fun _ => noCall_pure _ _
  · split_ifs
    · exact noCall_query _ _ (hq _ _)
    · exact noCall_pure _ _
  · split
    · exact noCall_pure _ _
    · exact noCall_query _ _ (hq _ _)

end Setup

/-! ## The runs of a tree -/

section Tree

open DigestBudgets

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) {p : (LocalSpec C).Domain → Prop}

omit [Field E] [Algebra Bit E] in
theorem PState.bind_le {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n m k : ℕ} (h : PState p prog n) (hf : ∀ a, PState p (f a) m)
    (hk : n + m ≤ k) : PState p (prog >>= f) k :=
  (PState.bind h hf).mono hk

/-- One ceremony makes the calls of `p` of its PRSS setup and none in its batches. -/
theorem ceremonyRun_pbound (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (i : C.Party) (keys : Keys C)
    (jobs : List Job) :
    PState p (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _) R := by
  unfold ceremonyRun
  refine PState.bind_le (PState.lift (hsetup i)) (fun prss => PState.of_class hp ?_) (Nat.add_zero R).le
  unfold batched
  dsimp only
  refine StateBound.bind_zero' ((StateBound.mapM _ (digestCost C .prssSetup + copyCost C .prssSetup)
    (fun batch => ?_) _).mono (by simp [digestCost, copyCost])) fun _ => StateBound.pure _
  refine StateBound.zero_bind StateBound.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine StateBound.zero_bind (StateBound.lift_zero ((ClassBound.mapM _ 0
    (fun job => inputShares_bound _ (by decide) job) _).mono (by simp))) fun inputs => ?_
  refine StateBound.bind_zero' (StateBound.lift (runJobs_bound K _ (by decide) (by decide) _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact StateBound.bind_zero (StateBound.set _) fun _ => StateBound.pure _

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree make the calls of `p` of `treeSetups tree` runs. -/
theorem ceremonyOutput_pbound (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), PState p (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (R : ℕ)
    (hrun : ∀ jobs, PState p (run jobs) R) (top : TopTree) (tree : Tree) :
    PState p (ceremonyOutput lift parameter run top tree) (treeSetups tree * R) := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine PState.bind_le (hrun topJobs) (m := 0) (fun out => ?_) (by simp [treeSetups])
    rcases out with _ | outputs
    · exact PState.pure _
    · exact PState.bind_le (hlift _) (fun _ => PState.pure _) le_rfl
  | bottom b =>
    unfold ceremonyOutput
    refine PState.bind_le (hrun (bottomJobs b)) (m := R) (fun out => ?_) (by simp [treeSetups]; omega)
    rcases out with _ | outputs
    · exact (PState.pure _).mono (Nat.zero_le _)
    refine PState.bind_le (hlift _) (m := R) (fun root => ?_) (by omega)
    refine PState.bind_le (hlift _) (m := R) (fun base => ?_) (by omega)
    refine PState.bind_le (hlift _) (m := R) (fun found => ?_) (by omega)
    rcases found with _ | ⟨randomness, encoding⟩
    · exact (PState.pure _).mono (Nat.zero_le _)
    refine PState.bind_le (hrun _) (m := 0) (fun out => ?_) (by omega)
    rcases out with _ | values
    · exact PState.pure _
    refine PState.bind_le (hlift _) (m := 0) (fun path => ?_) (by omega)
    refine PState.bind_le (hlift _) (m := 0) (fun topRoot => ?_) (by omega)
    split_ifs
    · exact PState.pure _
    · exact PState.pure _

/-- The ceremonies of a tree at one operator make the calls of `p` of `treeSetups tree` PRSS setups. -/
theorem newTree_pbound (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (i : C.Party) (keys : Keys C)
    (top : TopTree) (tree : Tree) :
    PBound p (newTree K circuits settings i keys top tree : PartyM C E RealSpec _) (treeSetups tree * R) := by
  have hrun := ceremonyOutput_pbound (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => PState.of_class hp (lift_tweakable_bound (by decide) oa)) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) R
    (fun jobs => ceremonyRun_pbound K circuits settings hp R hsetup i keys jobs) top tree (0, 0)
  unfold newTree
  refine (PBound.bind (m := 0) ?_ fun out => ?_).mono (Nat.add_zero _).le
  · unfold StateT.run'
    unfold PBound at hrun ⊢
    simp only [OptionT.run_map]
    exact (isQueryBoundP_map_iff _ _ _).2 hrun
  · rcases out with _ | output
    · exact isQueryBoundP_pure _ _ _
    · exact PBound.pure _

/-- The program of an operator in a run of a tree makes the calls of `p` of `treeSetups tree` PRSS
setups. -/
theorem treeProgram_pbound (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (i : C.Party) (operator : OperatorState C)
    (tree : Tree) : PBound p (treeProgram K circuits settings i operator tree) (treeSetups tree * R) := by
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact newTree_pbound K circuits settings hp R hsetup _ _ _ _
  | bottom b =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact newTree_pbound K circuits settings hp R hsetup _ _ _ _

/-- One run of a tree on the network makes at most `n * (treeSetups tree * R)` honest calls of `p`, when
the PRSS setup of each operator makes at most `R`. -/
theorem treeHonestP (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State) :
    IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
      fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestP p) (C.n * (treeSetups tree * R)) := by
  refine (executePhase_boundP p D net _ _ _ (fun _ => treeSetups tree * R)
    fun j _ => treeProgram_pbound K circuits settings hp R hsetup j _ tree).mono (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Tree

end SetupBudgets

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets.treeHonestP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets.treeHonestP
