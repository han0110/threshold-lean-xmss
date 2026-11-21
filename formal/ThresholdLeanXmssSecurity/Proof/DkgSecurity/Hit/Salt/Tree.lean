import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets

/-!
# The free digest calls and the salt draws of one run of a tree

`TailCall` is a call of `H` on a digest cell or a call of `PRG` at the stream index 2. Only the last
part of a check makes such calls, namely `randBits 256` and `compareDigests`.

* `DigestCall` is a free call of a digest cell. `compareDigests` makes at most `C.terms.length` of
  them at one operator, one for each held term.
* `SaltDraw` is a call of `PRG` at the stream index 2 and the position 0 under the name of a term.
  `randBits 256` makes at most `C.terms.length` of them at one operator, one for each held term.

`treeTail` bounds the honest calls of a predicate inside `TailCall` of one run of a tree on the
network by `C.n` times the batches of the tree times the bound of one check. `treeDigest` and
`treeSalt` are the two cases, each with `treeBatches tree * (C.n * termCount C)`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (PBound PState PartyP HonestP)
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets (ClassBound StateBound)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_mono noCall_query)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

/-! ## The predicates -/

section Predicates

variable {C : Committee}

/-- A call of `H` on a digest cell or a call of `PRG` at the stream index 2. -/
def TailCall : (RoSpec C).Domain → Prop
  | .inl q => ∃ (salt : List Bit) (history : HashOutput), q = .digest salt history
  | .inr x => x.2.2.2.1 = 2

/-- A local call of `TailCall`. A private sample is no such call. -/
def TailLocal : (LocalSpec C).Domain → Prop
  | .inl _ => False
  | .inr t => TailCall t

/-- A call of a digest cell. -/
def DigestCall : (LocalSpec C).Domain → Prop
  | .inr (.inl q) => ∃ (salt : List Bit) (history : HashOutput), q = .digest salt history
  | _ => False

/-- A call of `PRG` at the stream index 2 and the position 0 under the name of a term. -/
def SaltDraw : (LocalSpec C).Domain → Prop
  | .inr (.inr x) => (∃ T : C.Term, x.1 = .term T) ∧ x.2.2.2.1 = 2 ∧ x.2.2.2.2 = 0
  | _ => False

theorem digestCall_tail (t : (LocalSpec C).Domain) (h : DigestCall t) : TailLocal t := by
  rcases t with _ | q | x
  · exact h.elim
  · exact h
  · exact h.elim

theorem saltDraw_tail (t : (LocalSpec C).Domain) (h : SaltDraw t) : TailLocal t := by
  rcases t with _ | q | x
  · exact h.elim
  · exact h.elim
  · exact h.2.1

theorem tail_classes (t : (LocalSpec C).Domain) (h : TailLocal t) : InClass .digest t ∨ InClass .stream t := by
  rcases t with _ | q | x
  · exact h.elim
  · obtain ⟨salt, history, rfl⟩ := h
    exact Or.inl rfl
  · exact Or.inr rfl

/-- Two zero bounds give the zero bound of a predicate inside their union. -/
theorem isQueryBoundP_zero_of_or {ι α : Type} {spec : OracleSpec ι} {P Q R : ι → Prop}
    (hR : ∀ t, R t → P t ∨ Q t) {oa : OracleComp spec α} (hP : IsQueryBoundP oa P 0) (hQ : IsQueryBoundP oa Q 0) :
    IsQueryBoundP oa R 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP hQ ⊢
    have hp : ¬P t := hP.1.resolve_right (by omega)
    have hq : ¬Q t := hQ.1.resolve_right (by omega)
    have hr : ¬R t := fun h => (hR t h).elim hp hq
    refine ⟨Or.inl hr, fun u => ?_⟩
    simpa [hr] using ih u (by simpa [hp] using hP.2 u) (by simpa [hq] using hQ.2 u)

end Predicates

/-! ## The calculus of one operator -/

section Calculus

variable {C : Committee} {E : Type} {p : (LocalSpec C).Domain → Prop}

theorem PState.zero_bind {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n : ℕ} (h : PState p prog 0) (hf : ∀ a, PState p (f a) n) :
    PState p (prog >>= f) n :=
  (SetupBudgets.PState.bind h hf).mono (Nat.zero_add _).le

theorem PState.bind_zero' {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n : ℕ} (h : PState p prog n) (hf : ∀ a, PState p (f a) 0) :
    PState p (prog >>= f) n :=
  (SetupBudgets.PState.bind h hf).mono (Nat.add_zero _).le

theorem PState.get {σ : Type} : PState p (get : StateT σ (PartyM C E RealSpec) σ) 0 :=
  fun _ => SetupBudgets.PBound.pure _

theorem PState.set {σ : Type} (s : σ) : PState p (set s : StateT σ (PartyM C E RealSpec) PUnit) 0 :=
  fun _ => SetupBudgets.PBound.pure _

theorem PState.modifyGet {σ α : Type} (f : σ → α × σ) :
    PState p (modifyGet f : StateT σ (PartyM C E RealSpec) α) 0 :=
  fun _ => SetupBudgets.PBound.pure _

theorem PState.mapM {σ α β : Type} (f : α → StateT σ (PartyM C E RealSpec) β) (n : ℕ)
    (hf : ∀ a, PState p (f a) n) : ∀ xs : List α, PState p (xs.mapM f) (xs.length * n)
  | [] => by simpa using SetupBudgets.PState.pure (p := p) (σ := σ) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      SetupBudgets.PState.bind (hf a) fun b => SetupBudgets.PState.bind (PState.mapM f n hf xs) fun bs =>
        SetupBudgets.PState.pure (p := p) (b :: bs)

theorem PBound.mapM_zero {α β : Type} (f : α → PartyM C E RealSpec β) (hf : ∀ a, PBound p (f a) 0) :
    ∀ xs : List α, PBound p (xs.mapM f) 0
  | [] => by simpa using SetupBudgets.PBound.pure (p := p) (C := C) (E := E) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    simpa using SetupBudgets.PBound.bind (hf a) fun b => SetupBudgets.PBound.bind (PBound.mapM_zero f hf xs)
      fun bs => SetupBudgets.PBound.pure (p := p) (C := C) (E := E) (b :: bs)

/-- A zero bound of `TailLocal` is a zero bound of each predicate inside it. -/
theorem PBound.of_tail (hp : ∀ t, p t → TailLocal t) {α : Type} {prog : PartyM C E RealSpec α}
    (h : PBound TailLocal prog 0) : PBound p prog 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with (t | _) | _
    · exact hp t ht
    · exact ht.elim
    · exact ht.elim) h

theorem PState.of_tail (hp : ∀ t, p t → TailLocal t) {σ α : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    (h : PState TailLocal prog 0) : PState p prog 0 :=
  fun s => PBound.of_tail hp (h s)

/-- The zero bounds of the classes `digest` and `stream` give the zero bound of `TailLocal`. -/
theorem PBound.of_classes {α : Type} {prog : PartyM C E RealSpec α} (h₁ : ClassBound .digest prog 0)
    (h₂ : ClassBound .stream prog 0) : PBound TailLocal prog 0 :=
  isQueryBoundP_zero_of_or (P := DigestBudgets.PartyIn .digest) (Q := DigestBudgets.PartyIn .stream)
    (fun t ht => by
      rcases t with (t | _) | _
      · exact tail_classes t ht
      · exact ht.elim
      · exact ht.elim) h₁ h₂

theorem PState.of_classes {σ α : Type} {prog : StateT σ (PartyM C E RealSpec) α} (h₁ : StateBound .digest prog 0)
    (h₂ : StateBound .stream prog 0) : PState TailLocal prog 0 :=
  fun s => PBound.of_classes (h₁ s) (h₂ s)

theorem PBound.oracleStep_tail {α : Type} {oa : OracleComp (RoSpec C) α} (h : NoCall TailCall oa) :
    PBound TailLocal (ThresholdLeanXmss.oracleStep oa : PartyM C E RealSpec α) 0 :=
  SetupBudgets.PBound.oracleStep ((noCall_iff _ _).1 h)

end Calculus

/-! ## The blocks with no call of `TailCall` -/

section Blocks

variable {C : Committee} {E : Type}

theorem noCall_prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) (hidx : idx ≠ 2) :
    NoCall TailCall (prgBits name key ρ idx count) := by
  unfold prgBits
  exact noCall_bind _ (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => hidx h) fun _ => noCall_pure _ _

theorem noCall_hashQuery_tail (q : Query C) (hq : ∀ salt history, q ≠ .digest salt history) :
    NoCall TailCall (hashQuery q) :=
  noCall_query _ _ fun ⟨salt, history, h⟩ => hq salt history h

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

omit [Field E] [Algebra Bit E] in
theorem prssRandomness_tail {R : Type} [Zero R] (codec : Codec C E R) (idx count : ℕ)
    (hdraw : ∀ name key ρ, NoCall TailCall (codec.draw name key ρ idx count)) :
    PState TailLocal (prssRandomness ctx codec idx count : RunM C E RealSpec _) 0 := by
  unfold prssRandomness freshLabel
  refine PState.zero_bind (PState.modifyGet _) fun ρ => ?_
  refine PState.zero_bind (SetupBudgets.PState.lift (PBound.oracleStep_tail
    (noCall_mapM _ _ _ fun T => ?_))) fun _ => ?_
  · split_ifs
    · exact hdraw _ _ _
    · exact noCall_pure _ _
  refine PState.zero_bind (SetupBudgets.PState.lift (PBound.oracleStep_tail
    (noCall_mapM _ _ _ fun j => ?_))) fun _ => SetupBudgets.PState.pure _
  split
  · exact noCall_pure _ _
  · exact hdraw _ _ _

theorem elementCodec_tail (idx count : ℕ) (hidx : idx ≠ 2) (name : KeyName C) (key : HashOutput) (ρ : ℕ) :
    NoCall TailCall ((elementCodec K).draw name key ρ idx count) :=
  noCall_bind _ (noCall_prgBits _ _ _ _ _ hidx) fun _ => noCall_pure _ _

omit [Field E] [Algebra Bit E] in
theorem bitCodec_tail (idx count : ℕ) (hidx : idx ≠ 2) (name : KeyName C) (key : HashOutput) (ρ : ℕ) :
    NoCall TailCall ((bitCodec (C := C) (E := E)).draw name key ρ idx count) :=
  noCall_prgBits _ _ _ _ _ hidx

theorem coin_tail (count : ℕ) :
    PState TailLocal ((realCheckBuildingBlocks K ctx).coin count : RunM C E RealSpec _) 0 := by
  unfold realCheckBuildingBlocks coinWith
  exact PState.zero_bind (prssRandomness_tail ctx _ _ _ (elementCodec_tail K _ _ (by decide))) fun _ =>
    PState.zero_bind (SetupBudgets.PState.lift (PBound.of_classes (DigestBudgets.openSh_bound K ctx _ _)
      (DigestBudgets.openSh_bound K ctx _ _))) fun _ => SetupBudgets.PState.pure _

theorem extendMult_tail (products : List (Product C E)) :
    PState TailLocal ((realCheckBuildingBlocks K ctx).extendMult products : RunM C E RealSpec _) 0 := by
  unfold realCheckBuildingBlocks
  exact PState.zero_bind (prssRandomness_tail ctx _ _ _ (elementCodec_tail K _ _ (by decide))) fun _ =>
    PState.of_classes (DigestBudgets.reshare_bound K ctx _ _ _ _) (DigestBudgets.reshare_bound K ctx _ _ _ _)

theorem coinKey_tail : PState TailLocal (coinKey K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) 0 := by
  unfold coinKey
  exact PState.zero_bind PState.get fun _ => PState.zero_bind (coin_tail K ctx 2) fun _ =>
    SetupBudgets.PState.lift (PBound.oracleStep_tail (noCall_hashQuery_tail _ fun _ _ h => by cases h))

theorem noCall_findChallenge_tail (key : HashOutput) :
    ∀ tries index, NoCall TailCall (findChallenge K key tries index) := by
  intro tries
  induction tries with
  | zero => intro index; exact noCall_pure _ _
  | succ tries ih =>
    intro index
    unfold findChallenge
    refine noCall_bind _ (noCall_hashQuery_tail _ fun _ _ h => by cases h) fun r => ?_
    dsimp only
    generalize Classical.propDecidable (elementOfHash K r ≠ 0 ∧ elementOfHash K r ≠ 1) = d
    rcases d with ⟨_ | _, _⟩
    · exact ih _
    · exact noCall_pure _ _

theorem challenge_tail : PState TailLocal (challenge K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) 0 := by
  unfold challenge
  refine PState.zero_bind (coinKey_tail K ctx) fun key => ?_
  refine PState.zero_bind (SetupBudgets.PState.lift (PBound.oracleStep_tail
    (noCall_findChallenge_tail K key _ _))) fun r => ?_
  split
  · exact SetupBudgets.PState.pure _
  · exact SetupBudgets.PState.lift (PBound.of_classes DigestBudgets.ClassBound.failure
      DigestBudgets.ClassBound.failure)

theorem expand_tail (key : HashOutput) (count : ℕ) :
    PState TailLocal (expand K key count : RunM C E RealSpec _) 0 := by
  unfold expand
  exact SetupBudgets.PState.lift (PBound.oracleStep_tail (noCall_mapM _ _ _ fun _ =>
    noCall_map _ _ (noCall_hashQuery_tail _ fun _ _ h => by cases h)))

theorem mult_tail (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) :
    PState TailLocal ((realRunBuildingBlocks K ctx mode).mult x y count : RunM C E RealSpec _) 0 := by
  unfold realRunBuildingBlocks reshareWith
  refine PState.zero_bind (prssRandomness_tail ctx _ _ _ (bitCodec_tail _ _ (by decide))) fun r => ?_
  cases mode
  · exact PState.of_classes (DigestBudgets.reshare_bound K ctx _ _ _ _) (DigestBudgets.reshare_bound K ctx _ _ _ _)
  · exact PState.of_classes (DigestBudgets.reshareCollector_bound K ctx _ _ _)
      (DigestBudgets.reshareCollector_bound K ctx _ _ _)

theorem rerand_tail (mode : ReshareMode) (v : Shares C Bit) (count : ℕ) :
    PState TailLocal ((realRunBuildingBlocks K ctx mode).rerand v count : RunM C E RealSpec _) 0 := by
  unfold realRunBuildingBlocks
  exact PState.zero_bind (prssRandomness_tail ctx _ _ _ (bitCodec_tail _ _ (by decide))) fun _ =>
    PState.of_classes (DigestBudgets.reshare_bound K ctx _ _ _ _) (DigestBudgets.reshare_bound K ctx _ _ _ _)

end Blocks

/-! ## The bound of one check and of one run -/

section Run

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)
  {p : (LocalSpec C).Domain → Prop} (hp : ∀ t, p t → TailLocal t) (a b : ℕ)
  (hsalt : ∀ ctx : Context C, PState p (prssRandomness ctx (bitCodec (E := E)) 2 256 : RunM C E RealSpec _) a)
  (hcmp : ∀ (ctx : Context C) (salts : Shares C Bit), PState p (compareDigests ctx salts : RunM C E RealSpec Unit) b)

include hp hsalt hcmp

/-- The real check makes the calls of `randBits 256` and of one comparison. -/
theorem check_tail (ctx : Context C) (tuples : List (Tuple C)) :
    PState p (check K ctx (realCheckBuildingBlocks K ctx) tuples : RunM C E RealSpec Unit) (a + b) := by
  unfold check
  dsimp only
  split_ifs with hz
  · exact (SetupBudgets.PState.pure _).mono (Nat.zero_le _)
  refine PState.zero_bind (PState.of_tail hp (coinKey_tail K ctx)) fun key => ?_
  refine PState.zero_bind (PState.of_tail hp (expand_tail K key _)) fun τ => ?_
  refine PState.zero_bind (SetupBudgets.PState.lift (PBound.of_tail hp (PBound.of_classes
    (DigestBudgets.ClassBound.require _) (DigestBudgets.ClassBound.require _)))) fun _ => ?_
  refine PState.zero_bind (SetupBudgets.PState.foldlM _ (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨xs, ys, D⟩
    exact SetupBudgets.PState.bind_zero (PState.of_tail hp (extendMult_tail K ctx _)) fun _ =>
      SetupBudgets.PState.bind_zero (PState.of_tail hp (challenge_tail K ctx)) fun _ => SetupBudgets.PState.pure _
  rcases v with ⟨xs, ys, D⟩
  refine PState.zero_bind (SetupBudgets.PState.foldlM _ (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨A, B, D⟩
    exact SetupBudgets.PState.bind_zero (PState.of_tail hp (extendMult_tail K ctx _)) fun _ =>
      SetupBudgets.PState.bind_zero (PState.of_tail hp (challenge_tail K ctx)) fun _ => SetupBudgets.PState.pure _
  rcases v with ⟨A, B, D⟩
  refine PState.zero_bind (PState.of_tail hp (prssRandomness_tail ctx _ _ _ (elementCodec_tail K _ _ (by decide))))
    fun w => ?_
  refine PState.zero_bind (PState.of_tail hp (extendMult_tail K ctx _)) fun q => ?_
  refine SetupBudgets.PState.bind (hsalt ctx) fun salts => ?_
  refine PState.bind_zero' (hcmp ctx _) fun _ => ?_
  exact SetupBudgets.PState.bind_zero (PState.of_tail hp (challenge_tail K ctx)) fun _ =>
    SetupBudgets.PState.bind_zero (SetupBudgets.PState.lift (PBound.of_tail hp (PBound.of_classes
      (DigestBudgets.openSh_bound K ctx _ _) (DigestBudgets.openSh_bound K ctx _ _)))) fun _ =>
      SetupBudgets.PState.lift (PBound.of_tail hp (PBound.of_classes
        (DigestBudgets.ClassBound.require _) (DigestBudgets.ClassBound.require _)))

/-- A run of a batch makes the calls of one check. -/
theorem runJobs_tail (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    PState p (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) (a + b) := by
  unfold runJobs
  refine PState.zero_bind (SetupBudgets.PState.foldlM _ (fun v layer => ?_) _ _) fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact SetupBudgets.PState.bind_zero (PState.of_tail hp (mult_tail K ctx mode _ _ _)) fun _ =>
      SetupBudgets.PState.pure _
  rcases v with ⟨wires, tuples⟩
  refine PState.zero_bind (PState.of_tail hp (rerand_tail K ctx mode _ _)) fun v' => ?_
  refine PState.bind_zero' (check_tail K hp a b hsalt hcmp ctx _) fun _ => ?_
  exact SetupBudgets.PState.bind_zero (SetupBudgets.PState.lift (PBound.of_tail hp (PBound.of_classes
    (DigestBudgets.openRep_bound K ctx _ _) (DigestBudgets.openRep_bound K ctx _ _)))) fun _ =>
    SetupBudgets.PState.pure _

end Run

/-! ## The runs of a tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) {p : (LocalSpec C).Domain → Prop} (hp : ∀ t, p t → TailLocal t) (a b : ℕ)
  (hsalt : ∀ ctx : Context C, PState p (prssRandomness ctx (bitCodec (E := E)) 2 256 : RunM C E RealSpec _) a)
  (hcmp : ∀ (ctx : Context C) (salts : Shares C Bit), PState p (compareDigests ctx salts : RunM C E RealSpec Unit) b)

include hp hsalt hcmp

/-- One ceremony makes the calls of its batches. -/
theorem ceremonyRun_tail (i : C.Party) (keys : Keys C) (jobs : List Job) :
    PState p (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _) ((chunks settings.batchSize jobs).length * (a + b)) := by
  unfold ceremonyRun batched
  refine PState.zero_bind (SetupBudgets.PState.lift (PBound.of_tail hp (PBound.of_classes
    (DigestBudgets.prssSetup_bound (by decide) i) (DigestBudgets.prssSetup_bound (by decide) i)))) fun prss => ?_
  refine PState.bind_zero' (PState.mapM _ _ (fun batch => ?_) _) fun _ => SetupBudgets.PState.pure _
  refine PState.zero_bind PState.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine PState.zero_bind (SetupBudgets.PState.lift (PBound.mapM_zero _ (fun job => PBound.of_tail hp
    (PBound.of_classes (DigestBudgets.inputShares_bound _ (by decide) job)
      (DigestBudgets.inputShares_bound _ (by decide) job))) _)) fun inputs => ?_
  refine PState.bind_zero' (SetupBudgets.PState.lift (runJobs_tail K hp a b hsalt hcmp _ _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact SetupBudgets.PState.bind_zero (PState.set _) fun _ => SetupBudgets.PState.pure _

omit [Field E] [Algebra Bit E] hp hsalt hcmp in
/-- The ceremonies of a tree make the calls of the batches of the tree. -/
theorem ceremonyOutput_tail (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), PState p (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (P : ℕ)
    (hrun : ∀ jobs, PState p (run jobs) ((chunks settings.batchSize jobs).length * P)) (top : TopTree)
    (tree : Tree) :
    PState p (ceremonyOutput lift parameter run top tree) (treeBatches settings tree * P) := by
  cases tree with
  | top =>
    rw [treeBatches.eq_1]
    unfold ceremonyOutput
    refine PState.bind_zero' (hrun topJobs) fun out => ?_
    rcases out with _ | outputs
    · exact SetupBudgets.PState.pure _
    · exact SetupBudgets.PState.bind_zero (hlift _) fun _ => SetupBudgets.PState.pure _
  | bottom b =>
    rw [treeBatches.eq_2, Nat.add_mul]
    unfold ceremonyOutput
    refine SetupBudgets.PState.bind (hrun (bottomJobs b)) fun out => ?_
    rcases out with _ | outputs
    · exact (SetupBudgets.PState.pure _).mono (Nat.zero_le _)
    refine PState.zero_bind (hlift _) fun root => ?_
    refine PState.zero_bind (hlift _) fun base => ?_
    refine PState.zero_bind (hlift _) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact (SetupBudgets.PState.pure _).mono (Nat.zero_le _)
    rw [← DigestBudgets.chunks_signJobs settings b encoding]
    refine PState.bind_zero' (hrun _) fun out => ?_
    rcases out with _ | values
    · exact SetupBudgets.PState.pure _
    refine SetupBudgets.PState.bind_zero (hlift _) fun path => ?_
    refine SetupBudgets.PState.bind_zero (hlift _) fun topRoot => ?_
    split_ifs
    · exact SetupBudgets.PState.pure _
    · exact SetupBudgets.PState.pure _

/-- The ceremonies of a tree at one operator make the calls of the batches of the tree. -/
theorem newTree_tail (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PBound p (newTree K circuits settings i keys top tree : PartyM C E RealSpec _) (treeBatches settings tree * (a + b)) := by
  have hrun := ceremonyOutput_tail settings (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => PState.of_tail hp (PState.of_classes (DigestBudgets.lift_tweakable_bound (by decide) oa)
      (DigestBudgets.lift_tweakable_bound (by decide) oa))) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) _
    (fun jobs => ceremonyRun_tail K circuits settings hp a b hsalt hcmp i keys jobs) top tree (0, 0)
  unfold newTree
  refine (SetupBudgets.PBound.bind (m := 0) ?_ fun out => ?_).mono (Nat.add_zero _).le
  · unfold StateT.run'
    unfold PBound at hrun ⊢
    simp only [OptionT.run_map]
    exact (isQueryBoundP_map_iff _ _ _).2 hrun
  · rcases out with _ | output
    · exact isQueryBoundP_pure _ _ _
    · exact SetupBudgets.PBound.pure _

/-- The program of an operator in a run of a tree makes the calls of the batches of the tree. -/
theorem treeProgram_tail (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    PBound p (treeProgram K circuits settings i operator tree) (treeBatches settings tree * (a + b)) := by
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact newTree_tail K circuits settings hp a b hsalt hcmp _ _ _ _
  | bottom b' =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact newTree_tail K circuits settings hp a b hsalt hcmp _ _ _ _

/-- One run of a tree on the network makes at most `C.n` times the bound of the batches of the tree of
honest calls of `p`. -/
theorem treeTail (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) :
    IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
      s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestP p)
      (C.n * (treeBatches settings tree * (a + b))) := by
  refine (SetupBudgets.executePhase_boundP p D net _ _ _ (fun _ => treeBatches settings tree * (a + b))
    fun j _ => treeProgram_tail K circuits settings hp a b hsalt hcmp j _ tree).mono (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Tree

/-! ## The two cases -/

section Cases

variable {C : Committee} {E : Type}

/-- `compareDigests` asks one digest cell for each held term. -/
theorem compareDigests_digest (ctx : Context C) (salts : Shares C Bit) :
    PState DigestCall (compareDigests ctx salts : RunM C E RealSpec Unit) C.terms.length := by
  unfold compareDigests
  refine PState.zero_bind PState.get fun st => ?_
  refine (SetupBudgets.PState.bind (m := 0) (SetupBudgets.PState.lift (SetupBudgets.PBound.oracleStep
    (queryBound_mapM (fun t => DigestCall (C := C) (.inr t)) _ 1 C.terms fun T _ => ?_))) fun _ => ?_).mono (by simp)
  · split_ifs
    · refine (isQueryBoundP_bind (n := 0) (m := 1) ((noCall_iff _ _).1 (noCall_query _ _ fun h => ?_)) fun _ _ =>
        (hashQuery_queryBound _).of_imp fun _ _ => trivial).mono (Nat.zero_add 1).le
      obtain ⟨_, _, h⟩ := h
      cases h
    · exact isQueryBoundP_pure _ _ _
  · exact SetupBudgets.PState.bind_zero (SetupBudgets.PState.lift (PBound.of_tail digestCall_tail
      (PBound.of_classes (DigestBudgets.ClassBound.exchange _) (DigestBudgets.ClassBound.exchange _)))) fun _ =>
      SetupBudgets.PState.lift (PBound.of_tail digestCall_tail (PBound.of_classes
        (DigestBudgets.ClassBound.require _) (DigestBudgets.ClassBound.require _)))

/-- `compareDigests` makes no call of `PRG`. -/
theorem compareDigests_salt (ctx : Context C) (salts : Shares C Bit) :
    PState SaltDraw (compareDigests ctx salts : RunM C E RealSpec Unit) 0 := by
  have h := SetupBudgets.PState.of_class (c := .stream) (fun (t : (LocalSpec C).Domain) (ht : SaltDraw t) => by
    rcases t with _ | _ | _
    · exact ht.elim
    · exact ht.elim
    · rfl) (DigestBudgets.compareDigests_bound (E := E) (c := .stream) ctx salts)
  simpa [DigestBudgets.digestCost] using h

/-- The draws of the salts call no digest cell. -/
theorem salts_digest (ctx : Context C) :
    PState DigestCall (prssRandomness ctx (bitCodec (E := E)) 2 256 : RunM C E RealSpec _) 0 :=
  SetupBudgets.PState.of_class (c := .digest) (fun t ht => by
    rcases t with _ | q | _
    · exact ht.elim
    · obtain ⟨_, _, rfl⟩ := ht
      rfl
    · exact ht.elim) (DigestBudgets.prssRandomness_bound ctx _ (DigestBudgets.noCall_bitCodec (by decide)) 2 256)

/-- A list of calls with at most one call of `SaltDraw` at each position 0 makes at most the count of
the positions 0 of such calls. -/
theorem mapM_salt (f : ℕ → OracleComp (RoSpec C) Bit)
    (hf : ∀ x, IsQueryBoundP (f x) (fun t => SaltDraw (C := C) (.inr t)) (if x = 0 then 1 else 0)) :
    ∀ xs : List ℕ, IsQueryBoundP (xs.mapM f) (fun t => SaltDraw (C := C) (.inr t)) (xs.count 0)
  | [] => isQueryBoundP_pure _ _ _
  | a :: xs => by
    rw [List.mapM_cons, List.count_cons]
    refine (isQueryBoundP_bind (hf a) fun _ _ => (isQueryBoundP_bind (m := 0) (mapM_salt f hf xs) fun _ _ =>
      isQueryBoundP_pure _ _ _)).mono ?_
    by_cases ha : a = 0 <;> simp [ha, Nat.add_comm]

/-- The bits of one salt have one cell at the position 0. -/
theorem prgBits_salt (T : C.Term) (key : HashOutput) (ρ : ℕ) :
    IsQueryBoundP (prgBits (.term T) key ρ 2 256) (fun t => SaltDraw (C := C) (.inr t)) 1 := by
  unfold prgBits
  refine (isQueryBoundP_bind (m := 0) ((mapM_salt _ (fun x => ?_) (List.range 256)).mono (le_of_eq ?_))
    fun _ _ => isQueryBoundP_pure _ _ _).mono (Nat.add_zero _).le
  · refine (isQueryBoundP_query_iff (fun t => SaltDraw (C := C) (.inr t)) _ _).2 fun h => ?_
    rw [ite_eq_left_iff.mpr fun hn => absurd h.2.2 hn]
    exact Nat.one_pos
  · exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 (by norm_num))

/-- The draws of the salts have one cell at the position 0 for each held term. -/
theorem salts_salt (ctx : Context C) :
    PState SaltDraw (prssRandomness ctx (bitCodec (E := E)) 2 256 : RunM C E RealSpec _) C.terms.length := by
  unfold prssRandomness freshLabel
  refine PState.zero_bind (PState.modifyGet _) fun ρ => ?_
  refine (SetupBudgets.PState.bind (m := 0) (SetupBudgets.PState.lift (SetupBudgets.PBound.oracleStep
    (queryBound_mapM (fun t => SaltDraw (C := C) (.inr t)) _ 1 C.terms fun T _ => ?_))) fun _ => ?_).mono (by simp)
  · split_ifs
    · exact prgBits_salt T _ _
    · exact isQueryBoundP_pure _ _ _
  refine PState.zero_bind (SetupBudgets.PState.lift (SetupBudgets.PBound.oracleStep
    ((noCall_iff _ _).1 (noCall_mapM _ _ _ fun j => ?_)))) fun _ => SetupBudgets.PState.pure _
  split
  · exact noCall_pure _ _
  · refine noCall_bind _ (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => ?_) fun _ => noCall_pure _ _
    obtain ⟨⟨T, hT⟩, -⟩ := h
    cases hT

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- One run of a tree on the network makes at most `treeBatches tree * (C.n * termCount C)` free calls of
a digest cell. -/
theorem treeDigest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) :
    IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
      s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestP DigestCall)
      (treeBatches settings tree * (C.n * termCount C)) := by
  refine (treeTail K circuits settings digestCall_tail 0 C.terms.length salts_digest compareDigests_digest D net tree
    s).mono (le_of_eq ?_)
  rw [check_terms_length, termCount, Committee.n]
  ring

/-- One run of a tree on the network makes at most `treeBatches tree * (C.n * termCount C)` calls of
`PRG` at the stream index 2 and the position 0 under the name of a term. -/
theorem treeSalt (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) :
    IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
      s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestP SaltDraw)
      (treeBatches settings tree * (C.n * termCount C)) := by
  refine (treeTail K circuits settings saltDraw_tail C.terms.length 0 salts_salt compareDigests_salt D net tree
    s).mono (le_of_eq ?_)
  rw [check_terms_length, termCount, Committee.n]
  ring

end Cases

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.treeDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.treeDigest

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.treeSalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.treeSalt
