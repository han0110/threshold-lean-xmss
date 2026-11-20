import ThresholdLeanXmssSecurity.Proof.SeedHit

/-!
# A forger that answers the setup domains from its own table

`SetupOnly` marks the calls of the local oracles in a domain that only the setup uses, namely `H` at
`.commit`, `.derive`, `.sharedKeys`, `.copy`, `.history`, `.digest`, `.streamKey`, `.coinKey` and
`.expand`, and each call of `PRG`.

* `dealerKeyGen_safe`, `tsigOracles_safe` and `forgeryWins_safe` show that the honest code of
  `tsigGame` makes no such call and no programming query.
* `privateTable aes B` runs the forger `B` and answers each `SetupOnly` call of `B` from a private
  lazy table, with `PRG` as AES under the table value of `.streamKey key`.
* `accepts_privateTable` shows that the wrapper has the win probability of `B` in `tsigGame`.
* `privateTable_cost` shows that the cost of the wrapper in `adversaryCost` is the cost of `B` with
  cost zero for each `SetupOnly` call.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmss.Sketch

variable {C : Committee}

/-! ## The setup domains -/

/-- An input of `H` in a domain that only the setup uses. -/
def isSetupQuery : Query C → Bool
  | .hash _ => false
  | .prf .. => false
  | .mask .. => false
  | _ => true

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

/-! ## The private table -/

/-- One step of the private table. `H` is a lazy random oracle, and `PRG` is AES under the first
128 bits of the table value of `.streamKey key`. -/
def privateStep (aes : Aes) : QueryImpl (RoSpec C) (StateT (HashCache C) ProbComp) :=
  (Query C →ₒ HashOutput).randomOracle + fun (x : PrgInput C) => do
    let derived ← (Query C →ₒ HashOutput).randomOracle (.streamKey x.2.1)
    pure (aes.eval (truncateHash derived) x.2.2)

/-- The handler of the wrapper. A setup call runs one step of the private table on private coins,
and each other call goes to the oracles of the game. -/
def privateImpl (aes : Aes) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT (HashCache C) (OracleComp (LocalSpec C + TsigSpec C))) := fun t =>
  match t with
  | .inl (.inr x) =>
      if isSetupRo x then StateT.mk fun table => liftComp ((privateStep aes x).run table) _
      else liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C + TsigSpec C) (.inl (.inr x))))
  | t => liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C + TsigSpec C) t))

/-- The forger `B` with a private lazy table for the setup domains, which starts empty. -/
def privateTable (aes : Aes) (B : TsigAdversary C) : TsigAdversary C := fun pk top =>
  (simulateQ (privateImpl aes) (B pk top)).run' ∅

/-- `adversaryCost` with cost zero for each `SetupOnly` call. -/
def setupFreeCost : (LocalSpec C + TsigSpec C).Domain → ℕ
  | .inl (.inr x) => if isSetupRo x then 0 else adversaryCost (.inl (.inr x))
  | t => adversaryCost t

/-! ## The cost of the wrapper -/

/-- A private sample of the forger costs nothing in `adversaryCost`. -/
theorem liftComp_cost_zero {α : Type} (pc : ProbComp α) :
    QueryCostAtMost (liftComp pc (LocalSpec C + TsigSpec C)) adversaryCost 0 := by
  induction pc using OracleComp.inductionOn with
  | pure x => exact isQueryBound_pure _ _ _ _
  | query_bind n k ih =>
    rw [liftComp_bind]
    have e : liftComp (liftM (unifSpec.query n) : ProbComp _) (LocalSpec C + TsigSpec C) =
        (liftM ((LocalSpec C + TsigSpec C).query (.inl (.inl n))) : OracleComp _ _) := rfl
    rw [e]
    unfold QueryCostAtMost at *
    rw [isQueryBound_query_bind_iff]
    exact ⟨le_rfl, ih⟩

theorem privateTable_cost (aes : Aes) (B : TsigAdversary C) (q : ℕ) (pk : PublicKey) (top : TopTree)
    (h : QueryCostAtMost (B pk top) setupFreeCost q) :
    QueryCostAtMost (privateTable aes B pk top) adversaryCost q := by
  unfold QueryCostAtMost privateTable
  rw [StateT.run'_eq, isQueryBound_map_iff]
  refine IsQueryBound.simulateQ_run_of_step (combine := (· + ·)) (mapBudget := id)
    (stepBudget := fun t _ => setupFreeCost t) h ?_ ?_ ?_ ∅
  · intro γ δ oa ob b₁ b₂ h₁ h₂
    refine isQueryBound_bind (· + ·) ?_ ?_ h₁ h₂
    · intro t b₁' b₂' b hb; omega
    · intro t b₁' b₂' b hb; omega
  · intro t b s hb
    rcases t with (n | x) | q
    · simp [privateImpl, setupFreeCost, isQueryBound_map_iff, isQueryBound_query_iff]
    · by_cases hx : isSetupRo x = true
      · simp only [privateImpl, hx, ite_true, StateT.run_mk, setupFreeCost]
        exact liftComp_cost_zero _
      · simp [privateImpl, hx, setupFreeCost, isQueryBound_map_iff, isQueryBound_query_iff, adversaryCost]
    · simp [privateImpl, setupFreeCost, isQueryBound_map_iff, isQueryBound_query_iff]
  · intro t b hb
    simp only [id]
    omega

/-! ## The honest code of the dealer game -/

/-- A call of `H` or `PRG` outside the setup domains. -/
def RoNoSetup (x : (RoSpec C).Domain) : Prop := isSetupRo x = false

-- Ported from `formal/Sketch/SeedGenEnd.lean` (`mapM_safe`).
theorem mapM_allQueries {ι : Type} {spec : OracleSpec ι} {α β : Type} (P : ι → Prop) (f : α → OracleComp spec β)
    (hf : ∀ a, AllQueriesSatisfy (f a) P) : ∀ l : List α, AllQueriesSatisfy (l.mapM f) P
  | [] => allQueriesSatisfy_pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (hf a) fun _ =>
      allQueriesSatisfy_bind (mapM_allQueries P f hf l) fun _ => allQueriesSatisfy_pure _ _

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
  exact allQueriesSatisfy_bind (mapM_allQueries _ _ (fun T => map_safe _ (hashQuery_noSetup rfl)) _)
    fun _ => allQueriesSatisfy_pure _ _

theorem eval_safe (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    AllQueriesSatisfy (eval keys i J x message) RoNoSetup := by
  unfold eval
  exact allQueriesSatisfy_bind (mapM_allQueries _ _ (fun T => map_safe _ (hashQuery_noSetup rfl)) _) fun _ =>
    allQueriesSatisfy_bind (mapM_allQueries _ _ (fun j => map_safe _ (hashQuery_noSetup rfl)) _) fun _ =>
      allQueriesSatisfy_pure _ _

/-- A lift of `H` and `PRG` into the world that keeps calls outside the setup domains safe. -/
def SafeLift (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β) : Prop :=
  ∀ {β : Type} (oa : OracleComp (RoSpec C) β), AllQueriesSatisfy oa RoNoSetup → AllQueriesSatisfy (lift oa) WorldSafe

theorem referenceJob_safe {lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β}
    (hlift : SafeLift lift) {F : Point → OracleComp (WorldSpec C) Digest}
    (hF : ∀ x, AllQueriesSatisfy (F x) WorldSafe) (parameter : PublicParameter) (job : Job) :
    AllQueriesSatisfy (referenceJob (fun oa => lift (tweakable oa)) F parameter job) WorldSafe := by
  unfold referenceJob
  refine allQueriesSatisfy_bind (mapM_allQueries _ _ hF _) fun values => ?_
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
    (fun jobs => map_safe _ (mapM_allQueries _ _ (referenceJob_safe hlift hF parameter) jobs)) top tree

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

/-- The cache with the setup cells from `p` and the other cells from `s`. -/
def merge (s p : HashCache C) : HashCache C := QueryCache.ofFn fun q => if isSetupQuery q then p q else s q

/-- One step of the lazy random oracle moves along a map of caches that keeps the cell of the query and
commutes with a write to that cell. -/
theorem randomOracle_frame (q : Query C) (f : HashCache C → HashCache C) (c : HashCache C)
    (hread : f c q = c q) (hwrite : ∀ v : HashOutput, f (c.cacheQuery q v) = (f c).cacheQuery q v) :
    ((Query C →ₒ HashOutput).randomOracle q).run (f c) =
      (fun z => (z.1, f z.2)) <$> ((Query C →ₒ HashOutput).randomOracle q).run c := by
  rw [randomOracle.run_eq, randomOracle.run_eq, hread]
  cases c q with
  | some u => simp
  | none => simp [hwrite]

theorem merge_read_left {q : Query C} (hq : isSetupQuery q = false) (s p : HashCache C) :
    merge s p q = s q := by
  simp [merge, hq]

theorem merge_read_right {q : Query C} (hq : isSetupQuery q = true) (s p : HashCache C) :
    merge s p q = p q := by
  simp [merge, hq]

theorem merge_write_left {q : Query C} (hq : isSetupQuery q = false) (s p : HashCache C) (v : HashOutput) :
    merge (s.cacheQuery q v) p = (merge s p).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases h : q' = q
  · subst h; simp [merge, hq]
  · by_cases h' : isSetupQuery q' <;> simp [merge, h', QueryCache.cacheQuery_of_ne, h]

theorem merge_write_right {q : Query C} (hq : isSetupQuery q = true) (s p : HashCache C) (v : HashOutput) :
    merge s (p.cacheQuery q v) = (merge s p).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases h : q' = q
  · subst h; simp [merge, hq]
  · by_cases h' : isSetupQuery q' <;> simp [merge, h', QueryCache.cacheQuery_of_ne, h]

theorem hashAnswer_frame (prims : Primitives) (q : Query C) (f : HashCache C → HashCache C) (c : HashCache C)
    (hread : f c q = c q) (hwrite : ∀ v : HashOutput, f (c.cacheQuery q v) = (f c).cacheQuery q v) :
    (hashAnswer prims q).run (f c) = (fun z => (z.1, f z.2)) <$> (hashAnswer prims q).run c := by
  cases q
  case hash input =>
    by_cases hm : MpcInput input
    · simp [hashAnswer, hm]
    · simp only [hashAnswer, hm, ite_false]
      exact randomOracle_frame _ f c hread hwrite
  all_goals exact randomOracle_frame _ f c hread hwrite

/-- A local query outside the setup domains reads and writes only the cells of `s`. -/
theorem localAnswer_frame (prims : Primitives) (t : (LocalSpec C).Domain) (ht : ¬ SetupOnly t)
    (s p : HashCache C) :
    (localAnswer prims t).run (merge s p) = (fun z => (z.1, merge z.2 p)) <$> (localAnswer prims t).run s := by
  rcases t with n | q | x
  · change (unifFwdImpl (Query C →ₒ HashOutput) n).run (merge s p) =
      (fun z => (z.1, merge z.2 p)) <$> (unifFwdImpl (Query C →ₒ HashOutput) n).run s
    simp [unifFwdImpl]
  · have hq : isSetupQuery q = false := by simpa [SetupOnly, isSetupRo] using ht
    exact hashAnswer_frame prims q (merge · p) s (merge_read_left hq s p) (merge_write_left hq s p)
  · exact (ht (by simp [SetupOnly, isSetupRo])).elim

/-- A setup query reads and writes only the cells of `p`, as one step of the private table. -/
theorem localAnswer_setup (prims : Primitives) (x : (RoSpec C).Domain) (hx : isSetupRo x = true)
    (s p : HashCache C) :
    (localAnswer prims (.inr x)).run (merge s p) =
      (fun z => (z.1, merge s z.2)) <$> (privateStep prims.aes x).run p := by
  rcases x with q | y
  · have hq : isSetupQuery q = true := hx
    have e : hashAnswer prims q = (Query C →ₒ HashOutput).randomOracle q := by
      cases q <;> first | rfl | exact absurd hq (by simp [isSetupQuery])
    change (hashAnswer prims q).run (merge s p) = _ <$> ((Query C →ₒ HashOutput).randomOracle q).run p
    rw [hashAnswer_frame prims q (merge s ·) p (merge_read_right hq s p) (merge_write_right hq s p), e]
    rfl
  · change (prgAnswer prims y).run (merge s p) = (fun z => (z.1, merge s z.2)) <$> (prgAnswer prims y).run p
    have hq : isSetupQuery (C := C) (.streamKey y.2.1) = true := rfl
    simp only [prgAnswer, StateT.run_bind,
      hashAnswer_frame prims _ (merge s ·) p (merge_read_right hq s p) (merge_write_right hq s p),
      bind_map_left, map_bind, StateT.run_pure, map_pure]

theorem baseAnswer_frame (prims : Primitives) (t : (WorldSpec C).Domain) (ht : WorldSafe t) (s p : HashCache C) :
    (baseAnswer prims t).run (merge s p) = (fun z => (z.1, merge z.2 p)) <$> (baseAnswer prims t).run s := by
  rcases t with (t | x) | t
  · exact localAnswer_frame prims t ht s p
  · exact ht.elim
  · exact localAnswer_frame prims t ht s p

/-- A world computation with only `WorldSafe` queries reads and writes only the cells of `s`. -/
theorem simulate_frame (prims : Primitives) {α : Type} {oa : OracleComp (WorldSpec C) α}
    (h : AllQueriesSatisfy oa WorldSafe) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) oa).run (merge s p) =
      (fun z => (z.1, merge z.2 p)) <$> (simulateQ (baseAnswer prims) oa).run s := by
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

open ThresholdLeanXmssSecurity.SigningCoreProof in
theorem gameOracles_local_safe (dealt : Dealt C (OracleComp (WorldSpec C))) (t : (LocalSpec C).Domain)
    (ht : ¬ SetupOnly t) (st : TsigState C) :
    AllQueriesSatisfy ((gameOracles dealt (.inl t)).run st) WorldSafe := by
  have e : (gameOracles dealt (.inl t)).run st =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, st) := rfl
  rw [e, ThresholdLeanXmssSecurity.adversary_query]
  exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inl t)) _).2 ht)
    fun _ => allQueriesSatisfy_pure _ _

open ThresholdLeanXmssSecurity.SigningCoreProof in
/-- A query that the wrapper forwards to the game. -/
theorem step_forward (prims : Primitives) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain)
    (hT : privateImpl prims.aes t = StateT.lift (OracleComp.lift (OracleSpec.query t)))
    (hsafe : ∀ st, AllQueriesSatisfy ((gameOracles dealt t).run st) WorldSafe)
    (st : TsigState C) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) ((gameOracles dealt t).run st)).run (merge s p) =
      (fun z => ((z.1.1.1, z.1.2), merge z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims) ((simulateQ (gameOracles dealt) ((privateImpl prims.aes t).run p)).run st)).run s := by
  rw [hT, simulate_frame prims (hsafe st) s p]
  simp only [StateT.run_lift, simulateQ_spec_query,
    bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]

open ThresholdLeanXmssSecurity.SigningCoreProof in
/-- One query of the forger in the two games. -/
theorem step_coupling (prims : Primitives) {dealt : Dealt C (OracleComp (WorldSpec C))} (hdealt : SafeDealt dealt)
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) ((gameOracles dealt t).run st)).run (merge s p) =
      (fun z => ((z.1.1.1, z.1.2), merge z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims) ((simulateQ (gameOracles dealt) ((privateImpl prims.aes t).run p)).run st)).run s := by
  rcases t with (n | x) | q
  · exact step_forward prims dealt _ rfl (fun st => gameOracles_local_safe dealt _ (by simp [SetupOnly]) st) st s p
  · by_cases hx : isSetupRo x = true
    · have e : (privateImpl prims.aes (.inl (.inr x))).run p =
          liftComp ((privateStep prims.aes x).run p) (LocalSpec C + TsigSpec C) := by
        simp [privateImpl, hx]
      rw [e, gameOracles_liftComp, gameOracles_local, localAnswer_setup prims x hx s p]
      simp [Functor.map_map]
    · exact step_forward prims dealt _ (by simp [privateImpl, hx]; rfl)
        (fun st => gameOracles_local_safe dealt _ (by simpa [SetupOnly] using hx) st) st s p
  · exact step_forward prims dealt (.inr q) rfl (fun st => tsigOracles_safe freeLift_safe hdealt q st) st s p

open ThresholdLeanXmssSecurity.SigningCoreProof in
/-- The run of the forger in the game equals the run of the wrapper, with the table merged into the cache. -/
theorem coupling (prims : Primitives) {dealt : Dealt C (OracleComp (WorldSpec C))} (hdealt : SafeDealt dealt)
    {α : Type} (b : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) ((simulateQ (gameOracles dealt) b).run st)).run (merge s p) =
      (fun z => ((z.1.1.1, z.1.2), merge z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims)
          ((simulateQ (gameOracles dealt) ((simulateQ (privateImpl prims.aes) b).run p)).run st)).run s := by
  induction b using OracleComp.inductionOn generalizing st s p with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rw [step_coupling prims hdealt t st s p, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ _ _ _

theorem merge_empty : merge (C := C) ∅ ∅ = ∅ := by
  refine QueryCache.ext fun q => ?_
  simp [merge]

/-- The output of a safe world computation does not depend on the setup cells. -/
theorem simulate_frame_run' (prims : Primitives) {α : Type} {oa : OracleComp (WorldSpec C) α}
    (h : AllQueriesSatisfy oa WorldSafe) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) oa).run' (merge s p) = (simulateQ (baseAnswer prims) oa).run' s := by
  rw [StateT.run'_eq, StateT.run'_eq, simulate_frame prims h s p, Functor.map_map]

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

open ThresholdLeanXmssSecurity.SigningCoreProof in
/-- The two games from one dealt key, with the private table merged into the cache. -/
theorem game_coupling (prims : Primitives) {dealt : Dealt C (OracleComp (WorldSpec C))} (hdealt : SafeDealt dealt)
    (B : TsigAdversary C) (s : HashCache C) :
    (simulateQ (baseAnswer prims) ((·.1) <$> tsigGameWith worldRoles dealt B)).run' (merge s ∅) =
      (simulateQ (baseAnswer prims) ((·.1) <$> tsigGameWith worldRoles dealt (privateTable prims.aes B))).run' s := by
  rw [game_eq, game_eq, run'_bind, run'_bind, coupling prims hdealt, bind_map_left]
  simp only [privateTable, StateT.run'_eq, simulateQ_map, StateT.run_map, bind_map_left]
  exact bind_congr fun z => simulate_frame_run' prims (forgeryWins_safe freeLift_safe hdealt _ _) _ _

theorem accepts_eq (prims : Primitives) (oa : OracleComp (WorldSpec C) Bool) :
    accepts prims oa = (Pr{let r ← (simulateQ (baseAnswer prims) oa).run' ∅}[r = true]).toReal := by
  have h : Prod.fst <$> (simulateQ (world prims) oa).run = simulateQ (baseAnswer prims) oa :=
    QueryImpl.fst_map_run_withCost _ _ _
  unfold accepts runWorld
  rw [← h, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map]
  simp only [prEvent_map]
  erw [prEvent_map]

theorem accepts_privateTable (prims : Primitives) (B : TsigAdversary C) :
    accepts prims (tsigGame (privateTable prims.aes B)) = accepts prims (tsigGame B) := by
  rw [accepts_eq, accepts_eq]
  refine congrArg ENNReal.toReal (EvalDistEq.prEvent_eq ?_ _)
  unfold tsigGame
  rw [run'_bind, run'_bind]
  conv_rhs => rw [← merge_empty, simulate_frame prims dealerKeyGen_safe ∅ ∅, bind_map_left]
  refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  obtain ⟨output, c⟩ := z
  have hmem : output ∈ support (dealerKeyGen (C := C)) := by
    refine support_simulateQ_run'_subset (baseAnswer prims) _ ∅ ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨_, hz, rfl⟩
  cases output with
  | none => exact EvalDistEq.rfl
  | some dealt =>
    have hdealt := dealerKeyGen_support _ hmem dealt rfl
    dsimp only
    rw [game_coupling prims hdealt B c]

/-- info: 'ThresholdLeanXmss.Sketch.accepts_privateTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepts_privateTable

/-- info: 'ThresholdLeanXmss.Sketch.privateTable_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms privateTable_cost

/-- info: 'ThresholdLeanXmss.Sketch.dealerKeyGen_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerKeyGen_safe

end ThresholdLeanXmss.Sketch
