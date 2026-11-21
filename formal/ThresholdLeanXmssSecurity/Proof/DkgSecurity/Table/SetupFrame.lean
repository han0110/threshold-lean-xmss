import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Games
import ThresholdLeanXmssSecurity.Proof.SeedHit
import ThresholdLeanXmssSecurity.Proof.SigningCore
import ThresholdLeanXmssSecurity.Proof.CheckSecurity
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Partition
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Partition

/-!
# The frame of the setup domains

* `dealerKeyGen_safe`, `tsigOracles_safe` and `forgeryWins_safe` show that the honest code of
  `tsigGame` makes no call in a setup domain and no programming query.
* `SeedPartition.merge isSetupQuery s p` is the cache with the setup cells from `p` and the other
  cells from `s`. `simulate_frame` shows that a computation with only `WorldSafe` queries reads and writes only
  the cells of `s`.
* `accepts_eq` gives `accepts` by the world with no count.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

variable {C : Committee}

/-! ## The setup domains -/

/-- A call of `H` in a setup domain, or a call of `PRG`. -/
def isSetupRo : (RoSpec C).Domain → Bool
  | .inl q => isSetupQuery q
  | .inr _ => true

/-- A query of the local oracles in a domain that only the setup uses. -/
def SetupOnly : (LocalSpec C).Domain → Prop
  | .inl _ => False
  | .inr x => isSetupRo x = true

/-- A query of the world that is no `SetupOnly` call on either copy and no programming query. -/
def WorldSafe : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => ¬ SetupOnly t
  | .inl (.inr _) => False
  | .inr t => ¬ SetupOnly t


/-! ## The honest code of the dealer game -/

/-- A call of `H` or `PRG` outside the setup domains. -/
def RoNoSetup (x : (RoSpec C).Domain) : Prop := isSetupRo x = false

theorem map_safe {ι : Type} {spec : OracleSpec ι} {α β : Type} {P : ι → Prop} (f : α → β)
    {oa : OracleComp spec α} (h : AllQueriesSatisfy oa P) : AllQueriesSatisfy (f <$> oa) P := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind h fun _ => allQueriesSatisfy_pure _ _

theorem free_safe {β : Type} {oa : OracleComp (RoSpec C) β} (h : AllQueriesSatisfy oa RoNoSetup) :
    AllQueriesSatisfy (free (liftComp oa (LocalSpec C))) WorldSafe := by
  refine AllQueriesSatisfy.simulateQ (P := fun t : (LocalSpec C).Domain => ¬ SetupOnly t)
    (AllQueriesSatisfy.simulateQ h fun t ht => ?_) fun t ht => ?_
  · rcases t with q | x
    · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inl q)) _).2
        (by simp [SetupOnly, RoNoSetup] at ht ⊢; exact ht)
    · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inr x)) _).2
        (by simp [SetupOnly, RoNoSetup] at ht ⊢; exact ht)
  · exact (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inr t) _).2 ht

theorem hashQuery_noSetup {q : Query C} (hq : isSetupQuery q = false) :
    AllQueriesSatisfy (ThresholdLeanXmss.hashQuery q) RoNoSetup :=
  (allQueriesSatisfy_query_iff (spec := RoSpec C) (.inl q) _).2 hq

theorem tweakable_safe {β : Type} (oa : OracleComp HashSpec β) :
    AllQueriesSatisfy (tweakable (C := C) oa) RoNoSetup :=
  AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) oa)
    fun _ _ => hashQuery_noSetup rfl

theorem prfValue_safe (seeds : C.Term → HashOutput) (x : Point) :
    AllQueriesSatisfy (prfValue seeds x) RoNoSetup := by
  unfold prfValue
  exact allQueriesSatisfy_bind (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun T => map_safe _ (hashQuery_noSetup rfl)) _)
    fun _ => allQueriesSatisfy_pure _ _

theorem eval_safe (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    AllQueriesSatisfy (eval keys i J x message) RoNoSetup := by
  unfold eval
  exact allQueriesSatisfy_bind (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun T => map_safe _ (hashQuery_noSetup rfl)) _) fun _ =>
    allQueriesSatisfy_bind (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun j => map_safe _ (hashQuery_noSetup rfl)) _) fun _ =>
      allQueriesSatisfy_pure _ _

/-- A lift of `H` and `PRG` into the world that keeps calls outside the setup domains safe. -/
def SafeLift (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β) : Prop :=
  ∀ {β : Type} (oa : OracleComp (RoSpec C) β), AllQueriesSatisfy oa RoNoSetup → AllQueriesSatisfy (lift oa) WorldSafe

theorem referenceJob_safe {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β}
    (hlift : SafeLift lift) {F : Point → OracleComp (WorldSpec C) Digest}
    (hF : ∀ x, AllQueriesSatisfy (F x) WorldSafe) (parameter : PublicParameter) (job : Job) :
    AllQueriesSatisfy (referenceJob (fun oa => lift (tweakable oa)) F parameter job) WorldSafe := by
  unfold referenceJob
  refine allQueriesSatisfy_bind (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ hF _) fun values => ?_
  split <;>
  repeat (first | exact allQueriesSatisfy_pure _ _ | exact hlift _ (tweakable_safe _) |
    exact map_safe _ (hlift _ (tweakable_safe _)) | refine allQueriesSatisfy_bind ?_ fun _ => ?_)

theorem ceremonyOutput_safe (lift : ∀ {α : Type}, OracleComp HashSpec α → OracleComp (WorldSpec C) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), AllQueriesSatisfy (lift oa) WorldSafe)
    (parameter : PublicParameter) (run : List Job → OracleComp (WorldSpec C) (Option (List (List Bit))))
    (hrun : ∀ jobs, AllQueriesSatisfy (run jobs) WorldSafe) (top : TopTree) (tree : Tree) :
    AllQueriesSatisfy (ceremonyOutput lift parameter run top tree) WorldSafe := by
  cases tree with
  | top =>
    refine allQueriesSatisfy_bind (hrun _) fun outputs => ?_
    rcases outputs with _ | outputs
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_bind (hlift _) fun _ => allQueriesSatisfy_pure _ _
  | bottom b =>
    refine allQueriesSatisfy_bind (hrun _) fun outputs => ?_
    rcases outputs with _ | outputs
    · exact allQueriesSatisfy_pure _ _
    refine allQueriesSatisfy_bind (hlift _) fun _ => ?_
    refine allQueriesSatisfy_bind (hlift _) fun _ => ?_
    refine allQueriesSatisfy_bind (hlift _) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact allQueriesSatisfy_pure _ _
    refine allQueriesSatisfy_bind (hrun _) fun values => ?_
    rcases values with _ | values
    · exact allQueriesSatisfy_pure _ _
    refine allQueriesSatisfy_bind (hlift _) fun _ => ?_
    refine allQueriesSatisfy_bind (hlift _) fun _ => ?_
    split <;> exact allQueriesSatisfy_pure _ _

theorem referenceTree_safe {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β}
    (hlift : SafeLift lift) {F : Point → OracleComp (WorldSpec C) Digest}
    (hF : ∀ x, AllQueriesSatisfy (F x) WorldSafe) (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    AllQueriesSatisfy (referenceTree (fun oa => lift (tweakable oa)) F parameter top tree) WorldSafe :=
  ceremonyOutput_safe _ (fun oa => hlift _ (tweakable_safe oa)) parameter _
    (fun jobs => map_safe _ (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (referenceJob_safe hlift hF parameter) jobs)) top tree

/-- A dealt key whose functions make only `WorldSafe` queries. -/
def SafeDealt (dealt : Dealt C (OracleComp (WorldSpec C))) : Prop :=
  (∀ x, AllQueriesSatisfy (dealt.value x) WorldSafe) ∧
    (∀ i J x message, AllQueriesSatisfy (dealt.part i J x message) WorldSafe) ∧
    ∀ b, AllQueriesSatisfy (dealt.bottom b) WorldSafe

theorem sequenceFin_safe {ι : Type} {spec : OracleSpec ι} {P : ι → Prop} {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α), (∀ i, AllQueriesSatisfy (f i) P) →
      AllQueriesSatisfy (OverPermutation.sequenceFin f) P
  | 0, _, _ => allQueriesSatisfy_pure _ _
  | _ + 1, _, h => allQueriesSatisfy_bind (h 0) fun _ =>
      allQueriesSatisfy_bind (sequenceFin_safe _ fun i => h i.succ) fun _ => allQueriesSatisfy_pure _ _

theorem sample_safe {β : Type} (pc : ProbComp β) :
    AllQueriesSatisfy (free (C := C) (liftComp pc (LocalSpec C))) WorldSafe := by
  refine AllQueriesSatisfy.simulateQ (P := fun t : (LocalSpec C).Domain => ¬ SetupOnly t)
    (AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) pc)
      fun t _ => ?_) fun t ht => ?_
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inl t) _).2 (by simp [SetupOnly])
  · exact (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inr t) _).2 ht

theorem dealtWith_safe {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β}
    (hlift : SafeLift lift) (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    {value : Point → OracleComp (WorldSpec C) Digest} (hvalue : ∀ x, AllQueriesSatisfy (value x) WorldSafe) :
    SafeDealt (dealtWith lift parameter keys top value) := by
  refine ⟨hvalue, fun i J x message => ?_, fun b => ?_⟩
  · exact hlift _ (eval_safe (keys i) i J x message)
  · unfold dealtWith
    dsimp only
    generalize Tree.bottom b = tree
    exact map_safe _ (referenceTree_safe hlift hvalue parameter top tree)

theorem freeLift_safe : SafeLift (C := C) fun oa => free (liftComp oa (LocalSpec C)) :=
  fun _ h => free_safe h

theorem dealerKeyGenWith_safe {sample : ∀ {β : Type}, ProbComp β → OracleComp (WorldSpec C) β}
    (hsample : ∀ {β : Type} (pc : ProbComp β), AllQueriesSatisfy (sample pc) WorldSafe)
    {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β} (hlift : SafeLift lift) :
    AllQueriesSatisfy (dealerKeyGenWith sample lift) WorldSafe := by
  unfold dealerKeyGenWith
  refine allQueriesSatisfy_bind (hsample _) fun keyGen => ?_
  simp only []
  generalize Tree.top = tree
  refine allQueriesSatisfy_bind (referenceTree_safe hlift (fun x => hlift _ (prfValue_safe keyGen.2.1 x)) _ _ tree)
    fun output => ?_
  split <;> exact allQueriesSatisfy_pure _ _

theorem dealerKeyGen_safe : AllQueriesSatisfy (dealerKeyGen (C := C)) WorldSafe :=
  dealerKeyGenWith_safe (fun pc => sample_safe pc) freeLift_safe

theorem lift_map_safe {ι : Type} {spec : OracleSpec ι} {P : ι → Prop} {σ α β : Type} (f : α → β)
    {x : OracleComp spec α} (h : AllQueriesSatisfy x P) (s : σ) :
    AllQueriesSatisfy ((f <$> (liftM x : StateT σ (OracleComp spec) α)).run s) P := by
  simp only [StateT.run_map, StateT.run_monadLift, monadLift_self]
  exact map_safe _ (allQueriesSatisfy_bind h fun _ => allQueriesSatisfy_pure _ _)

theorem signRound2With_safe {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β}
    (hlift : SafeLift lift) {part : Point → OracleComp (WorldSpec C) Digest}
    (hpart : ∀ x, AllQueriesSatisfy (part x) WorldSafe) (parameter : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    AllQueriesSatisfy (signRound2With lift part parameter J commitment e message parts) WorldSafe := by
  unfold signRound2With
  refine allQueriesSatisfy_bind (hlift _ (tweakable_safe _)) fun found => ?_
  rcases found with _ | ⟨_, encoding⟩
  · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (sequenceFin_safe _ fun l => ?_) fun _ => allQueriesSatisfy_pure _ _
  split
  · exact map_safe _ (hpart _)
  · exact allQueriesSatisfy_pure _ _

theorem bottomOnce_safe {dealt : Dealt C (OracleComp (WorldSpec C))} (hdealt : SafeDealt dealt)
    (b : Fin (2 ^ layerHeight)) (st : TsigState C) :
    AllQueriesSatisfy ((bottomOnce dealt b).run st) WorldSafe := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact allQueriesSatisfy_pure _ _
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, StateT.run_modify,
      StateT.run_pure]
    exact allQueriesSatisfy_bind (hdealt.2.2 b) fun _ => allQueriesSatisfy_pure _ _

theorem tsigOracles_safe {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β}
    (hlift : SafeLift lift) {dealt : Dealt C (OracleComp (WorldSpec C))} (hdealt : SafeDealt dealt)
    (q : TsigQuery C) (st : TsigState C) :
    AllQueriesSatisfy ((tsigOracles lift dealt q).run st) WorldSafe := by
  cases q with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact allQueriesSatisfy_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind]
      exact allQueriesSatisfy_pure _ _
  | tree b =>
    simp only [tsigOracles, StateT.run_bind]
    refine allQueriesSatisfy_bind (bottomOnce_safe hdealt b st) fun found => ?_
    rcases found with ⟨_ | tree, st'⟩
    · exact allQueriesSatisfy_pure _ _
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact allQueriesSatisfy_bind (hdealt.1 _) fun _ => allQueriesSatisfy_pure _ _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact allQueriesSatisfy_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind]
      exact lift_map_safe _ (hdealt.2.1 _ _ _ _) _
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact allQueriesSatisfy_pure _ _
    · rw [StateT.run_bind]
      refine allQueriesSatisfy_bind (bottomOnce_safe hdealt _ st) fun found => ?_
      rcases found with ⟨_ | tree, st'⟩
      · exact allQueriesSatisfy_pure _ _
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      refine allQueriesSatisfy_bind (hdealt.2.1 _ _ _ _) fun own => ?_
      refine allQueriesSatisfy_bind (signRound2With_safe hlift (fun x => hdealt.2.1 _ _ _ _) _ _ _ _ _ _)
        fun values => ?_
      rcases values with _ | values
      · exact allQueriesSatisfy_pure _ _
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        exact allQueriesSatisfy_pure _ _

theorem forgeryWins_safe {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β}
    (hlift : SafeLift lift) {dealt : Dealt C (OracleComp (WorldSpec C))} (hdealt : SafeDealt dealt)
    (st : TsigState C) (forgery : Forgery) :
    AllQueriesSatisfy (forgeryWins lift dealt st forgery) WorldSafe := by
  unfold forgeryWins
  refine allQueriesSatisfy_bind (hlift _ (tweakable_safe _)) fun _ => ?_
  dsimp only
  split
  · exact allQueriesSatisfy_bind (allQueriesSatisfy_pure _ _) fun _ => allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind ?_ fun _ => allQueriesSatisfy_bind (allQueriesSatisfy_pure _ _) fun _ =>
    allQueriesSatisfy_pure _ _
  unfold honestSignature
  refine allQueriesSatisfy_bind (hdealt.2.2 _) fun tree => ?_
  rcases tree with _ | tree
  · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (hdealt.1 _) fun _ => ?_
  refine allQueriesSatisfy_bind (hlift _ (tweakable_safe _)) fun found => ?_
  rcases found with _ | ⟨randomness, encoding⟩
  · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (sequenceFin_safe _ fun l => ?_) fun _ =>
    allQueriesSatisfy_bind (hlift _ (tweakable_safe _)) fun _ => allQueriesSatisfy_pure _ _
  split
  · exact hdealt.1 _
  · exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_bind (hdealt.1 _) fun _ => allQueriesSatisfy_pure _ _

/-! ## The win probability -/

/-- The world of `runWorld` without the count. -/
def baseAnswer (prims : Primitives) : QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp) :=
  localAnswer (C := C) prims + programAnswer (C := C) + localAnswer (C := C) prims

/-- A local query outside the setup domains reads and writes only the cells of `s`. -/
theorem localAnswer_frame (prims : Primitives) (t : (LocalSpec C).Domain) (ht : ¬ SetupOnly t)
    (s p : HashCache C) :
    (localAnswer prims t).run (SeedPartition.merge isSetupQuery s p) = (fun z => (z.1, SeedPartition.merge isSetupQuery z.2 p)) <$> (localAnswer prims t).run s := by
  rcases t with n | q | x
  · change (unifFwdImpl (Query C →ₒ HashOutput) n).run (SeedPartition.merge isSetupQuery s p) =
      (fun z => (z.1, SeedPartition.merge isSetupQuery z.2 p)) <$> (unifFwdImpl (Query C →ₒ HashOutput) n).run s
    simp [unifFwdImpl]
  · have hq : isSetupQuery q = false := by simpa [SetupOnly, isSetupRo] using ht
    exact DkgCorrectnessProof.UsedHit.hashAnswer_map prims q (SeedPartition.merge isSetupQuery · p) s (SeedPartition.merge_read_left _ hq s p)
      (SeedPartition.merge_write_left _ hq s p)
  · exact (ht (by simp [SetupOnly, isSetupRo])).elim

/-- A setup query reads and writes only the cells of `p`, as one step of the private table. -/
theorem localAnswer_setup (prims : Primitives) (x : (RoSpec C).Domain) (hx : isSetupRo x = true)
    (s p : HashCache C) :
    (localAnswer prims (.inr x)).run (SeedPartition.merge isSetupQuery s p) =
      (fun z => (z.1, SeedPartition.merge isSetupQuery s z.2)) <$> (privateStep prims.aes x).run p := by
  rcases x with q | y
  · have hq : isSetupQuery q = true := hx
    have e : hashAnswer prims q = (Query C →ₒ HashOutput).randomOracle q := by
      cases q <;> first | rfl | exact absurd hq (by simp [isSetupQuery])
    change (hashAnswer prims q).run (SeedPartition.merge isSetupQuery s p) = _ <$> ((Query C →ₒ HashOutput).randomOracle q).run p
    rw [DkgCorrectnessProof.UsedHit.hashAnswer_map prims q (SeedPartition.merge isSetupQuery s ·) p (SeedPartition.merge_read_right _ hq s p)
      (SeedPartition.merge_write_right _ hq s p), e]
    rfl
  · change (prgAnswer prims y).run (SeedPartition.merge isSetupQuery s p) = (fun z => (z.1, SeedPartition.merge isSetupQuery s z.2)) <$> (prgAnswer prims y).run p
    have hq : isSetupQuery (C := C) (.streamKey y.2.1) = true := rfl
    simp only [prgAnswer, StateT.run_bind,
      DkgCorrectnessProof.UsedHit.hashAnswer_map prims _ (SeedPartition.merge isSetupQuery s ·) p (SeedPartition.merge_read_right _ hq s p)
        (SeedPartition.merge_write_right _ hq s p),
      bind_map_left, map_bind, StateT.run_pure, map_pure]

theorem baseAnswer_frame (prims : Primitives) (t : (WorldSpec C).Domain) (ht : WorldSafe t) (s p : HashCache C) :
    (baseAnswer prims t).run (SeedPartition.merge isSetupQuery s p) = (fun z => (z.1, SeedPartition.merge isSetupQuery z.2 p)) <$> (baseAnswer prims t).run s := by
  rcases t with (t | x) | t
  · exact localAnswer_frame prims t ht s p
  · exact ht.elim
  · exact localAnswer_frame prims t ht s p

/-- A world computation with only `WorldSafe` queries reads and writes only the cells of `s`. -/
theorem simulate_frame (prims : Primitives) {α : Type} {oa : OracleComp (WorldSpec C) α}
    (h : AllQueriesSatisfy oa WorldSafe) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) oa).run (SeedPartition.merge isSetupQuery s p) =
      (fun z => (z.1, SeedPartition.merge isSetupQuery z.2 p)) <$> (simulateQ (baseAnswer prims) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self]
    rw [baseAnswer_frame prims t h.1 s p, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ (h.2 _) z.2

open ThresholdLeanXmssSecurity.SigningCoreProof in
theorem gameOracles_local (prims : Primitives) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C).Domain) (st : TsigState C) (c : HashCache C) :
    (simulateQ (baseAnswer prims) ((gameOracles dealt (.inl t)).run st)).run c =
      (fun z => ((z.1, st), z.2)) <$> (localAnswer prims t).run c := by
  have e : (gameOracles dealt (.inl t)).run st =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, st) := rfl
  rw [e, simulateQ_bind, ThresholdLeanXmssSecurity.SeedHitProof.simulateQ_adversary_query]
  simp only [simulateQ_pure, bind_pure_comp, StateT.run_map]
  rfl

open ThresholdLeanXmssSecurity.SigningCoreProof in
theorem gameOracles_liftComp (prims : Primitives) (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (pc : ProbComp α) (st : TsigState C) (c : HashCache C) :
    (simulateQ (baseAnswer prims)
        ((simulateQ (gameOracles dealt) (liftComp pc (LocalSpec C + TsigSpec C))).run st)).run c =
      (fun a => ((a, st), c)) <$> pc := by
  induction pc using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n k ih =>
    have e : liftComp (liftM (unifSpec.query n) : ProbComp _) (LocalSpec C + TsigSpec C) =
        (liftM ((LocalSpec C + TsigSpec C).query (.inl (.inl n))) : OracleComp _ _) := rfl
    rw [liftComp_bind, e, simulateQ_bind, simulateQ_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map, StateT.run_bind, simulateQ_bind]
    rw [gameOracles_local, bind_map_left]
    change ((unifFwdImpl (Query C →ₒ HashOutput) n).run c >>= _) = _
    simp [unifFwdImpl, ih]

theorem run'_bind (prims : Primitives) {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (f : α → OracleComp (WorldSpec C) β) (s : HashCache C) :
    (simulateQ (baseAnswer prims) (oa >>= f)).run' s =
      (simulateQ (baseAnswer prims) oa).run s >>= fun z => (simulateQ (baseAnswer prims) (f z.1)).run' z.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- Every output of `oa` satisfies `Q`. -/
def OutputsSatisfy {ι : Type} {spec : OracleSpec ι} {α : Type} (oa : OracleComp spec α) (Q : α → Prop) : Prop :=
  ∀ x ∈ support oa, Q x

theorem OutputsSatisfy.bind {ι : Type} {spec : OracleSpec ι} {α β : Type} {Q : β → Prop} (oa : OracleComp spec α)
    {f : α → OracleComp spec β} (h : ∀ a, OutputsSatisfy (f a) Q) : OutputsSatisfy (oa >>= f) Q := by
  intro y hy
  obtain ⟨a, -, hy⟩ := (mem_support_bind_iff _ _ _).1 hy
  exact h a y hy

/-- An output of the dealer is a safe dealt key. -/
def SafeOutput (output : Option (Dealt C (OracleComp (WorldSpec C)))) : Prop :=
  ∀ dealt, output = some dealt → SafeDealt dealt

theorem dealerKeyGenWith_support {sample : ∀ {β : Type}, ProbComp β → OracleComp (WorldSpec C) β}
    {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β} (hlift : SafeLift lift) :
    OutputsSatisfy (dealerKeyGenWith sample lift) SafeOutput := by
  unfold dealerKeyGenWith
  refine OutputsSatisfy.bind _ fun keyGen => ?_
  simp only []
  generalize Tree.top = tree
  refine OutputsSatisfy.bind _ fun output => ?_
  split
  · intro y hy dealt hdealt
    simp only [support_pure, Set.mem_singleton_iff] at hy
    rw [hy, Option.some.injEq] at hdealt
    rw [← hdealt]
    exact dealtWith_safe hlift _ _ _ fun x => hlift _ (prfValue_safe keyGen.2.1 x)
  · intro y hy dealt hdealt
    simp only [support_pure, Set.mem_singleton_iff] at hy
    rw [hy] at hdealt
    exact absurd hdealt (by simp)

theorem dealerKeyGen_support : OutputsSatisfy (dealerKeyGen (C := C)) SafeOutput :=
  dealerKeyGenWith_support freeLift_safe

open ThresholdLeanXmssSecurity.SigningCoreProof in
theorem game_eq (dealt : Dealt C (OracleComp (WorldSpec C))) (A : TsigAdversary C) :
    (·.1) <$> tsigGameWith worldRoles dealt A =
      (simulateQ (gameOracles dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run tsigInit >>=
        fun z => forgeryWins (fun oa => worldRoles.honest (liftComp oa _)) dealt z.2 z.1 := by
  unfold tsigGameWith
  simp only [map_bind, map_pure, bind_pure]
  rfl


theorem accepts_eq (prims : Primitives) (oa : OracleComp (WorldSpec C) Bool) :
    accepts prims oa = (Pr{let r ← (simulateQ (baseAnswer prims) oa).run' ∅}[r = true]).toReal := by
  have h : Prod.fst <$> (simulateQ (world prims) oa).run = simulateQ (baseAnswer prims) oa :=
    QueryImpl.fst_map_run_withCost _ _ _
  unfold accepts runWorld
  rw [← h, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map]
  simp only [prEvent_map]
  erw [prEvent_map]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.accepts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.accepts_eq
