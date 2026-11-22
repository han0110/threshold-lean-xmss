import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.ProgramParty

/-!
# The program of an operator in a run of a tree has check blocks

`PProv` and `PProvS` are `ProvWhole` on an operator program and on a program on a state. A program
with no local call of `TailLocal` has check blocks, so the blocks of `Tree.lean` with a zero bound give
each piece but one. The salt draws of a check and its digest calls form one check block
(`saltsDigests_prov`). The walk from `check` to `treeProgram` follows `check_whole` of `WholeTree.lean`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (PBound PState PartyP)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_mapM
  noCall_query)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

/-! ## The calculus of one operator -/

section Calculus

variable {C : Committee} {E : Type}

/-- An operator program with check blocks. -/
def PProv {α : Type} (prog : PartyM C E RealSpec α) : Prop := ProvWhole prog.run

/-- A program on a state with check blocks from each state. -/
def PProvS {σ α : Type} (prog : StateT σ (PartyM C E RealSpec) α) : Prop := ∀ s, PProv (prog.run s)

theorem PProv.pure {α : Type} (a : α) : PProv (pure a : PartyM C E RealSpec α) := ProvWhole.pure _

theorem PProv.bind {α β : Type} {prog : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} (h : PProv prog)
    (hf : ∀ a, PProv (f a)) : PProv (prog >>= f) := by
  unfold PProv at h hf ⊢
  simp only [OptionT.run_bind]
  refine ProvWhole.bind h fun o => ?_
  cases o with
  | none => exact ProvWhole.pure _
  | some a => exact hf a

theorem localTouch_tail (t : (LocalSpec C).Domain) (h : LocalTouch t) : TailLocal t := by
  rcases t with _ | q | x
  · exact h.elim
  · exact h
  · exact h.2

theorem PProv.of_tail {α : Type} {prog : PartyM C E RealSpec α} (h : PBound TailLocal prog 0) : PProv prog :=
  ProvWhole.of_noCall _ (PBound.of_tail localTouch_tail h)

theorem PProvS.of_tail {σ α : Type} {prog : StateT σ (PartyM C E RealSpec) α} (h : PState TailLocal prog 0) :
    PProvS prog := fun s => PProv.of_tail (h s)

theorem PProvS.pure {σ α : Type} (a : α) : PProvS (pure a : StateT σ (PartyM C E RealSpec) α) :=
  fun _ => PProv.pure _

theorem PProvS.bind {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} (h : PProvS prog) (hf : ∀ a, PProvS (f a)) :
    PProvS (prog >>= f) := fun s =>
  PProv.bind (h s) fun a => hf a.1 a.2

theorem PProvS.lift {σ α : Type} {prog : PartyM C E RealSpec α} (h : PProv prog) :
    PProvS (StateT.lift prog : StateT σ (PartyM C E RealSpec) α) := fun s => by
  change PProv (prog >>= fun a => Pure.pure (a, s))
  exact PProv.bind h fun _ => PProv.pure _

theorem PProvS.mapM {σ α β : Type} (f : α → StateT σ (PartyM C E RealSpec) β) (hf : ∀ a, PProvS (f a)) :
    ∀ xs : List α, PProvS (xs.mapM f)
  | [] => by simpa using PProvS.pure (σ := σ) (C := C) (E := E) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b => (PProvS.mapM f hf xs).bind fun bs => PProvS.pure (b :: bs)

theorem PProvS.foldlM {σ α γ : Type} (f : α → γ → StateT σ (PartyM C E RealSpec) α) (hf : ∀ a g, PProvS (f a g)) :
    ∀ (xs : List γ) (a : α), PProvS (xs.foldlM f a)
  | [], a => by simpa using PProvS.pure (σ := σ) (C := C) (E := E) a
  | g :: xs, a => by
    rw [List.foldlM_cons]
    exact (hf a g).bind fun a' => PProvS.foldlM f hf xs a'

end Calculus

/-! ## The check block -/

section Block

variable {C : Committee} {E : Type}

/-- The salt draws of a check and its digest calls, with a rest that does not read the salts, form one
check block. -/
theorem saltsDigests_prov {β : Type} (ctx : Context C) (rest : RunM C E RealSpec β) (hrest : PProvS rest) :
    PProvS (prssRandomness ctx (bitCodec (E := E)) 2 256 >>= fun salts => compareDigests ctx salts.1 >>= fun _ => rest) := by
  intro s
  unfold PProv
  simp only [prssRandomness, freshLabel, compareDigests, StateT.run_bind, StateT.run_modifyGet, StateT.run_lift,
    StateT.run_get, pure_bind, bind_assoc, oracleStep, localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM, Option.elim_some]
  have hpairs : NoCall (fun t => Touch (C := C) (.inr (.inr t))) (C.parties.mapM fun j =>
      if h : j = ctx.self then pure fun _ => 0
      else (bitCodec (C := C) (E := E)).draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) s.label 2 256) := by
    refine noCall_mapM _ _ _ fun j => ?_
    split
    · exact noCall_pure _ _
    · refine noCall_bind _ (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => ?_) fun _ => noCall_pure _ _
      obtain ⟨⟨T, hT⟩, -⟩ := h
      cases hT
  refine ProvWhole.block ctx.self ctx.prss.term s.label _ hpairs s.history _ fun z ds => ?_
  refine ProvWhole.bind (PProv.of_tail (PBound.of_classes (DigestBudgets.ClassBound.exchange _)
    (DigestBudgets.ClassBound.exchange _))) fun o => ?_
  cases o with
  | none => exact ProvWhole.pure _
  | some inbox =>
    refine ProvWhole.bind (PProv.of_tail (PBound.of_classes (DigestBudgets.ClassBound.require _)
      (DigestBudgets.ClassBound.require _))) fun o => ?_
    cases o with
    | none => exact ProvWhole.pure _
    | some u => exact hrest _

end Block

/-! ## The check and the runs -/

section Run

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The real check has check blocks. -/
theorem check_prov (ctx : Context C) (tuples : List (Tuple C)) :
    PProvS (check K ctx (realCheckBuildingBlocks K ctx) tuples : RunM C E RealSpec Unit) := by
  unfold check
  dsimp only
  split_ifs with hz
  · exact PProvS.pure _
  refine (PProvS.of_tail (coinKey_tail K ctx)).bind fun key => ?_
  refine (PProvS.of_tail (expand_tail K key _)).bind fun τ => ?_
  refine (PProvS.lift (PProv.of_tail (PBound.of_classes
    (DigestBudgets.ClassBound.require _) (DigestBudgets.ClassBound.require _)))).bind fun _ => ?_
  refine (PProvS.foldlM _ (fun v j => ?_) _ _).bind fun v => ?_
  · rcases v with ⟨xs, ys, D⟩
    exact (PProvS.of_tail (extendMult_tail K ctx _)).bind fun _ =>
      (PProvS.of_tail (challenge_tail K ctx)).bind fun _ => PProvS.pure _
  rcases v with ⟨xs, ys, D⟩
  refine (PProvS.foldlM _ (fun v j => ?_) _ _).bind fun v => ?_
  · rcases v with ⟨A, B, D⟩
    exact (PProvS.of_tail (extendMult_tail K ctx _)).bind fun _ =>
      (PProvS.of_tail (challenge_tail K ctx)).bind fun _ => PProvS.pure _
  rcases v with ⟨A, B, D⟩
  refine (PProvS.of_tail (prssRandomness_tail ctx _ _ _ (elementCodec_tail K _ _ (by decide)))).bind fun w => ?_
  refine (PProvS.of_tail (extendMult_tail K ctx _)).bind fun q => ?_
  refine saltsDigests_prov ctx _ ?_
  exact (PProvS.of_tail (challenge_tail K ctx)).bind fun _ =>
    (PProvS.lift (PProv.of_tail (PBound.of_classes
      (DigestBudgets.openSh_bound K ctx _ _) (DigestBudgets.openSh_bound K ctx _ _)))).bind fun _ =>
      PProvS.lift (PProv.of_tail (PBound.of_classes
        (DigestBudgets.ClassBound.require _) (DigestBudgets.ClassBound.require _)))

/-- A run of a batch has check blocks. -/
theorem runJobs_prov (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    PProvS (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) := by
  unfold runJobs
  refine (PProvS.foldlM _ (fun v layer => ?_) _ _).bind fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact (PProvS.of_tail (mult_tail K ctx mode _ _ _)).bind fun _ => PProvS.pure _
  rcases v with ⟨wires, tuples⟩
  refine (PProvS.of_tail (rerand_tail K ctx mode _ _)).bind fun v' => ?_
  refine (check_prov K ctx _).bind fun _ => ?_
  exact (PProvS.lift (PProv.of_tail (PBound.of_classes
    (DigestBudgets.openRep_bound K ctx _ _) (DigestBudgets.openRep_bound K ctx _ _)))).bind fun _ =>
    PProvS.pure _

end Run

/-! ## The runs of a tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- One ceremony has check blocks. -/
theorem ceremonyRun_prov (i : C.Party) (keys : Keys C) (jobs : List Job) :
    PProvS (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _) := by
  unfold ceremonyRun batched
  refine (PProvS.lift (PProv.of_tail (PBound.of_classes
    (DigestBudgets.prssSetup_bound (by decide) i) (DigestBudgets.prssSetup_bound (by decide) i)))).bind fun prss => ?_
  refine (PProvS.mapM _ (fun batch => ?_) _).bind fun _ => PProvS.pure _
  refine (PProvS.of_tail PState.get).bind fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine (PProvS.lift (PProv.of_tail (PBound.mapM_zero _ (fun job => PBound.of_classes
    (DigestBudgets.inputShares_bound _ (by decide) job) (DigestBudgets.inputShares_bound _ (by decide) job)) _))).bind
    fun inputs => ?_
  refine (PProvS.lift (runJobs_prov K _ _ _ _ _)).bind fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact (PProvS.of_tail (PState.set _)).bind fun _ => PProvS.pure _

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree have check blocks. -/
theorem ceremonyOutput_prov (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), PProvS (lift oa)) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))))
    (hrun : ∀ jobs, PProvS (run jobs)) (top : TopTree) (tree : Tree) :
    PProvS (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine (hrun topJobs).bind fun out => ?_
    rcases out with _ | outputs
    · exact PProvS.pure _
    · exact (hlift _).bind fun _ => PProvS.pure _
  | bottom b =>
    unfold ceremonyOutput
    refine (hrun (bottomJobs b)).bind fun out => ?_
    rcases out with _ | outputs
    · exact PProvS.pure _
    refine (hlift _).bind fun root => ?_
    refine (hlift _).bind fun base => ?_
    refine (hlift _).bind fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact PProvS.pure _
    refine (hrun _).bind fun out => ?_
    rcases out with _ | values
    · exact PProvS.pure _
    refine (hlift _).bind fun path => ?_
    refine (hlift _).bind fun topRoot => ?_
    split_ifs
    · exact PProvS.pure _
    · exact PProvS.pure _

/-- The ceremonies of a tree at one operator have check blocks. -/
theorem newTree_prov (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PProv (newTree K circuits settings i keys top tree : PartyM C E RealSpec _) := by
  have hrun := ceremonyOutput_prov (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => PProvS.of_tail (PState.of_classes (DigestBudgets.lift_tweakable_bound (by decide) oa)
      (DigestBudgets.lift_tweakable_bound (by decide) oa))) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys)
    (fun jobs => ceremonyRun_prov K circuits settings i keys jobs) top tree (0, 0)
  unfold newTree
  refine PProv.bind ?_ fun out => ?_
  · unfold StateT.run'
    rw [map_eq_bind_pure_comp]
    exact PProv.bind hrun fun _ => PProv.pure _
  · rcases out with _ | output
    · exact ProvWhole.pure _
    · exact PProv.pure _

/-- The program of each operator in a run of a tree has check blocks. -/
def TreeProv : Prop :=
  ∀ (i : C.Party) (operator : OperatorState C) (tree : Tree),
    ProvWhole (treeProgram K circuits settings i operator tree).run

/-- The program of each operator in a run of a tree has check blocks. -/
theorem treeProv : TreeProv (C := C) (E := E) K circuits settings := by
  intro i operator tree
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact ProvWhole.pure _
    · simp only [treeProgram, hk]
      exact newTree_prov K circuits settings _ _ _ _
  | bottom b' =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact ProvWhole.pure _
    · simp only [treeProgram, hk]
      exact ProvWhole.pure _
    · simp only [treeProgram, hk, ht]
      exact ProvWhole.pure _
    · simp only [treeProgram, hk, ht]
      exact newTree_prov K circuits settings _ _ _ _

end Tree


end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.treeProv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.treeProv
