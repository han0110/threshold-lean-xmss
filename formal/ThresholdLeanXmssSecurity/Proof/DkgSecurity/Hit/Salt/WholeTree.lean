import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.WholeGame
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.HiddenPlaces

/-!
# The program of an operator in a run of a tree has whole salt draws

`PWhole` and `PWholeS` are `SaltWhole` on an operator program and on a program on a state. A program
with no local call of `TailLocal` has whole salt draws, so the blocks of `Tree.lean` with a zero bound
give each piece but one. The draws of the salts `prssRandomness ctx bitCodec 2 256` are whole draws
of the held terms and pair draws with no call of `SaltDraw` (`randBits_whole`). The walk from `check`
to `treeProgram` follows `check_tail` to `treeProgram_tail`. `treeWhole` is `TreeWhole`.
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

/-- An operator program with whole salt draws. -/
def PWhole {α : Type} (prog : PartyM C E RealSpec α) : Prop := SaltWhole prog.run

/-- A program on a state with whole salt draws from each state. -/
def PWholeS {σ α : Type} (prog : StateT σ (PartyM C E RealSpec) α) : Prop := ∀ s, PWhole (prog.run s)

theorem PWhole.pure {α : Type} (a : α) : PWhole (pure a : PartyM C E RealSpec α) := SaltWhole.pure _

theorem PWhole.bind {α β : Type} {prog : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} (h : PWhole prog)
    (hf : ∀ a, PWhole (f a)) : PWhole (prog >>= f) := by
  unfold PWhole at h hf ⊢
  simp only [OptionT.run_bind]
  refine SaltWhole.bind h fun o => ?_
  cases o with
  | none => exact SaltWhole.pure _
  | some a => exact hf a

theorem PWhole.of_salt {α : Type} {prog : PartyM C E RealSpec α} (h : PBound SaltDraw prog 0) : PWhole prog :=
  SaltWhole.of_noCall _ h

theorem PWhole.of_tail {α : Type} {prog : PartyM C E RealSpec α} (h : PBound TailLocal prog 0) : PWhole prog :=
  PWhole.of_salt (PBound.of_tail saltDraw_tail h)

theorem PWholeS.of_salt {σ α : Type} {prog : StateT σ (PartyM C E RealSpec) α} (h : PState SaltDraw prog 0) :
    PWholeS prog := fun s => PWhole.of_salt (h s)

theorem PWholeS.of_tail {σ α : Type} {prog : StateT σ (PartyM C E RealSpec) α} (h : PState TailLocal prog 0) :
    PWholeS prog := fun s => PWhole.of_tail (h s)

theorem PWholeS.pure {σ α : Type} (a : α) : PWholeS (pure a : StateT σ (PartyM C E RealSpec) α) :=
  fun _ => PWhole.pure _

theorem PWholeS.bind {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} (h : PWholeS prog) (hf : ∀ a, PWholeS (f a)) :
    PWholeS (prog >>= f) := fun s =>
  PWhole.bind (h s) fun a => hf a.1 a.2

theorem PWholeS.lift {σ α : Type} {prog : PartyM C E RealSpec α} (h : PWhole prog) :
    PWholeS (StateT.lift prog : StateT σ (PartyM C E RealSpec) α) := fun s => by
  change PWhole (prog >>= fun a => Pure.pure (a, s))
  exact PWhole.bind h fun _ => PWhole.pure _

theorem PWholeS.mapM {σ α β : Type} (f : α → StateT σ (PartyM C E RealSpec) β) (hf : ∀ a, PWholeS (f a)) :
    ∀ xs : List α, PWholeS (xs.mapM f)
  | [] => by simpa using PWholeS.pure (σ := σ) (C := C) (E := E) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b => (PWholeS.mapM f hf xs).bind fun bs => PWholeS.pure (b :: bs)

theorem PWholeS.foldlM {σ α γ : Type} (f : α → γ → StateT σ (PartyM C E RealSpec) α) (hf : ∀ a g, PWholeS (f a g)) :
    ∀ (xs : List γ) (a : α), PWholeS (xs.foldlM f a)
  | [], a => by simpa using PWholeS.pure (σ := σ) (C := C) (E := E) a
  | g :: xs, a => by
    rw [List.foldlM_cons]
    exact (hf a g).bind fun a' => PWholeS.foldlM f hf xs a'

end Calculus

/-! ## The draws of the salts -/

section Draws

variable {C : Committee} {E : Type} {γ : Type}

/-- The draws of the held terms at the stream index 2 are whole draws of salts. -/
theorem saltWhole_termDraws_bind (self : C.Party) (keyOf : C.Term → HashOutput) (ρ : ℕ) :
    ∀ (l : List C.Term) (k : List (ℕ → Bit) → OracleComp (PartySpec C E RealSpec) γ), (∀ rs, SaltWhole (k rs)) →
      SaltWhole (liftComp (liftComp (l.mapM fun T => if self ∈ C.holders T then
          prgBits (.term T) (keyOf T) ρ 2 256 else pure fun _ => 0) (LocalSpec C)) (PartySpec C E RealSpec) >>= k)
  | [], k, hk => by simpa using hk []
  | T :: l, k, hk => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
    by_cases hT : self ∈ C.holders T
    · simp only [hT, ↓reduceIte]
      exact SaltWhole.draw T (keyOf T) ρ _ fun bits =>
        saltWhole_termDraws_bind self keyOf ρ l (fun rs => k (bits :: rs)) fun rs => hk _
    · simp only [hT, ↓reduceIte, liftComp_pure, pure_bind]
      exact saltWhole_termDraws_bind self keyOf ρ l (fun rs => k ((fun _ => 0) :: rs)) fun rs => hk _

variable [Field E] [Algebra Bit E]

omit [Field E] [Algebra Bit E] in
/-- The draws of the salts have whole salt draws. -/
theorem randBits_whole (ctx : Context C) :
    PWholeS (prssRandomness ctx (bitCodec (E := E)) 2 256 : RunM C E RealSpec _) := by
  unfold prssRandomness freshLabel
  refine (PWholeS.of_tail (PState.modifyGet _)).bind fun ρ => ?_
  refine (PWholeS.lift ?_).bind fun r => (PWholeS.lift (PWhole.of_salt ?_)).bind fun Z => PWholeS.pure _
  · unfold PWhole oracleStep localStep
    change SaltWhole (liftComp (liftComp _ (LocalSpec C)) (PartySpec C E RealSpec) >>= fun a => Pure.pure (some a))
    exact saltWhole_termDraws_bind ctx.self ctx.prss.term ρ C.terms _ fun _ => SaltWhole.pure _
  · refine SetupBudgets.PBound.oracleStep ((noCall_iff _ _).1 (noCall_mapM _ _ _ fun j => ?_))
    split
    · exact noCall_pure _ _
    · refine noCall_bind _ (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => ?_) fun _ => noCall_pure _ _
      obtain ⟨⟨T, hT⟩, -⟩ := h
      cases hT

end Draws

/-! ## The check and the runs -/

section Run

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The real check has whole salt draws. -/
theorem check_whole (ctx : Context C) (tuples : List (Tuple C)) :
    PWholeS (check K ctx (realCheckBuildingBlocks K ctx) tuples : RunM C E RealSpec Unit) := by
  unfold check
  dsimp only
  split_ifs with hz
  · exact PWholeS.pure _
  refine (PWholeS.of_tail (coinKey_tail K ctx)).bind fun key => ?_
  refine (PWholeS.of_tail (expand_tail K key _)).bind fun τ => ?_
  refine (PWholeS.lift (PWhole.of_tail (PBound.of_classes
    (DigestBudgets.ClassBound.require _) (DigestBudgets.ClassBound.require _)))).bind fun _ => ?_
  refine (PWholeS.foldlM _ (fun v j => ?_) _ _).bind fun v => ?_
  · rcases v with ⟨xs, ys, D⟩
    exact (PWholeS.of_tail (extendMult_tail K ctx _)).bind fun _ =>
      (PWholeS.of_tail (challenge_tail K ctx)).bind fun _ => PWholeS.pure _
  rcases v with ⟨xs, ys, D⟩
  refine (PWholeS.foldlM _ (fun v j => ?_) _ _).bind fun v => ?_
  · rcases v with ⟨A, B, D⟩
    exact (PWholeS.of_tail (extendMult_tail K ctx _)).bind fun _ =>
      (PWholeS.of_tail (challenge_tail K ctx)).bind fun _ => PWholeS.pure _
  rcases v with ⟨A, B, D⟩
  refine (PWholeS.of_tail (prssRandomness_tail ctx _ _ _ (elementCodec_tail K _ _ (by decide)))).bind fun w => ?_
  refine (PWholeS.of_tail (extendMult_tail K ctx _)).bind fun q => ?_
  refine (randBits_whole ctx).bind fun salts => ?_
  refine (PWholeS.of_salt (compareDigests_salt ctx _)).bind fun _ => ?_
  exact (PWholeS.of_tail (challenge_tail K ctx)).bind fun _ =>
    (PWholeS.lift (PWhole.of_tail (PBound.of_classes
      (DigestBudgets.openSh_bound K ctx _ _) (DigestBudgets.openSh_bound K ctx _ _)))).bind fun _ =>
      PWholeS.lift (PWhole.of_tail (PBound.of_classes
        (DigestBudgets.ClassBound.require _) (DigestBudgets.ClassBound.require _)))

/-- A run of a batch has whole salt draws. -/
theorem runJobs_whole (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    PWholeS (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) := by
  unfold runJobs
  refine (PWholeS.foldlM _ (fun v layer => ?_) _ _).bind fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact (PWholeS.of_tail (mult_tail K ctx mode _ _ _)).bind fun _ => PWholeS.pure _
  rcases v with ⟨wires, tuples⟩
  refine (PWholeS.of_tail (rerand_tail K ctx mode _ _)).bind fun v' => ?_
  refine (check_whole K ctx _).bind fun _ => ?_
  exact (PWholeS.lift (PWhole.of_tail (PBound.of_classes
    (DigestBudgets.openRep_bound K ctx _ _) (DigestBudgets.openRep_bound K ctx _ _)))).bind fun _ =>
    PWholeS.pure _

end Run

/-! ## The runs of a tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- One ceremony has whole salt draws. -/
theorem ceremonyRun_whole (i : C.Party) (keys : Keys C) (jobs : List Job) :
    PWholeS (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _) := by
  unfold ceremonyRun batched
  refine (PWholeS.lift (PWhole.of_tail (PBound.of_classes
    (DigestBudgets.prssSetup_bound (by decide) i) (DigestBudgets.prssSetup_bound (by decide) i)))).bind fun prss => ?_
  refine (PWholeS.mapM _ (fun batch => ?_) _).bind fun _ => PWholeS.pure _
  refine (PWholeS.of_tail PState.get).bind fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine (PWholeS.lift (PWhole.of_tail (PBound.mapM_zero _ (fun job => PBound.of_classes
    (DigestBudgets.inputShares_bound _ (by decide) job) (DigestBudgets.inputShares_bound _ (by decide) job)) _))).bind
    fun inputs => ?_
  refine (PWholeS.lift (runJobs_whole K _ _ _ _ _)).bind fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact (PWholeS.of_tail (PState.set _)).bind fun _ => PWholeS.pure _

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree have whole salt draws. -/
theorem ceremonyOutput_whole (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), PWholeS (lift oa)) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))))
    (hrun : ∀ jobs, PWholeS (run jobs)) (top : TopTree) (tree : Tree) :
    PWholeS (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine (hrun topJobs).bind fun out => ?_
    rcases out with _ | outputs
    · exact PWholeS.pure _
    · exact (hlift _).bind fun _ => PWholeS.pure _
  | bottom b =>
    unfold ceremonyOutput
    refine (hrun (bottomJobs b)).bind fun out => ?_
    rcases out with _ | outputs
    · exact PWholeS.pure _
    refine (hlift _).bind fun root => ?_
    refine (hlift _).bind fun base => ?_
    refine (hlift _).bind fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact PWholeS.pure _
    refine (hrun _).bind fun out => ?_
    rcases out with _ | values
    · exact PWholeS.pure _
    refine (hlift _).bind fun path => ?_
    refine (hlift _).bind fun topRoot => ?_
    split_ifs
    · exact PWholeS.pure _
    · exact PWholeS.pure _

/-- The ceremonies of a tree at one operator have whole salt draws. -/
theorem newTree_whole (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PWhole (newTree K circuits settings i keys top tree : PartyM C E RealSpec _) := by
  have hrun := ceremonyOutput_whole (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => PWholeS.of_tail (PState.of_classes (DigestBudgets.lift_tweakable_bound (by decide) oa)
      (DigestBudgets.lift_tweakable_bound (by decide) oa))) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys)
    (fun jobs => ceremonyRun_whole K circuits settings i keys jobs) top tree (0, 0)
  unfold newTree
  refine PWhole.bind ?_ fun out => ?_
  · unfold StateT.run'
    rw [map_eq_bind_pure_comp]
    exact PWhole.bind hrun fun _ => PWhole.pure _
  · rcases out with _ | output
    · exact SaltWhole.pure _
    · exact PWhole.pure _

/-- The program of each operator in a run of a tree has whole salt draws. -/
theorem treeWhole : TreeWhole (C := C) (E := E) K circuits settings := by
  intro i operator tree
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact SaltWhole.pure _
    · simp only [treeProgram, hk]
      exact newTree_whole K circuits settings _ _ _ _
  | bottom b' =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact SaltWhole.pure _
    · simp only [treeProgram, hk]
      exact SaltWhole.pure _
    · simp only [treeProgram, hk, ht]
      exact SaltWhole.pure _
    · simp only [treeProgram, hk, ht]
      exact newTree_whole K circuits settings _ _ _ _

end Tree

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.treeWhole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.treeWhole
