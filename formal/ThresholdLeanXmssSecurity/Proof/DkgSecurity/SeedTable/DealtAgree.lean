import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.End
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.PhaseAbort
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Glue
import ThresholdLeanXmssSecurity.Proof.Signing

/-!
# The rest with the keys of the dealer on a result of `worldSeedGen`

`sharedDealtAgree_holds` states that on each result of `worldSeedGen`, the shared rest with real runs on
the keys of the dealer of each emulated operator with keys and the shared rest with the data of the
dealer give "win and no flag" with one probability.

* In the real mode a run reads no data of the dealer (`sharedRuns_real_params`). So both rests are
  the same runs of the top tree and then a signing phase with another dealer.
* The operators never change their keys (`keepsS_sharedRuns`).
* On a live result each honest operator has keys. Then the parameter and the seeds of the game are the
  ones of the dealer, and the two dealers differ only in the keys of the corrupt operators. A signing
  request reads the keys of the dealer only for an operator with keys (`sharedSigning_dealt_eq`).
* On a dead result an honest operator has no keys. Then no run of the top tree gives an honest
  output, and both signing phases give `false`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## A run in the real mode reads no data of the dealer -/

section Params

variable {M : Type → Type} [Monad M] {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W M))
  (view : W → StreamState C)

omit [Fintype E] [DecidableEq E] in
theorem sharedRun_real_params (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter parameter' : PublicParameter) (seeds seeds' : C.Term → HashOutput) (dealt dealt' : C.Party → Keys C)
    (emu emu' : C.Party → Option (Keys C)) (tree : Tree) :
    sharedRun K circuits settings impl view Mode.real D net parameter seeds dealt emu tree =
      sharedRun K circuits settings impl view Mode.real D net parameter' seeds' dealt' emu' tree := by
  unfold sharedRun
  refine bind_congr fun s => ?_
  have hnot : ¬ s.runs tree < Mode.real.emulated tree := by simp [Mode.real]
  rw [ite_eq_right hnot, ite_eq_right hnot]

omit [Fintype E] [DecidableEq E] in
theorem sharedRuns_real_params (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter parameter' : PublicParameter) (seeds seeds' : C.Term → HashOutput) (dealt dealt' : C.Party → Keys C)
    (emu emu' : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, sharedRuns K circuits settings runLimit impl view Mode.real D net parameter seeds dealt emu tree count =
      sharedRuns K circuits settings runLimit impl view Mode.real D net parameter' seeds' dealt' emu' tree count
  | 0 => rfl
  | count + 1 => by
    unfold sharedRuns
    rw [sharedRun_real_params K circuits settings impl view D net parameter parameter' seeds seeds' dealt dealt' emu
      emu' tree, sharedRuns_real_params D net parameter parameter' seeds seeds' dealt dealt' emu emu' tree count]

end Params

/-! ## Two dealers that differ only in the keys of some operators -/

section Dealers

variable {m : Type → Type} [Monad m] (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
  (parameter : PublicParameter) (top : TopTree) (value : Point → m Digest)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The win test reads no key of the dealer. -/
theorem forgeryWins_dealt_keys (keys keys' : C.Party → Keys C) (st : TsigState C) (forgery : Forgery) :
    forgeryWins lift (dealtWith lift parameter keys top value) st forgery =
      forgeryWins lift (dealtWith lift parameter keys' top value) st forgery := rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A request of a bottom tree reads no key of the dealer. -/
theorem tsigOracles_tree_keys (keys keys' : C.Party → Keys C) (b : Fin (2 ^ layerHeight)) :
    tsigOracles lift (dealtWith lift parameter keys top value) (.tree b) =
      tsigOracles lift (dealtWith lift parameter keys' top value) (.tree b) := rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A request of operator `i` reads the key of the dealer of `i` only. -/
theorem tsigOracles_round1_keys (keys keys' : C.Party → Keys C) (i : C.Party) (J : C.Quorum) (e : KeyIndex)
    (message : Message) (h : keys i = keys' i) :
    tsigOracles lift (dealtWith lift parameter keys top value) (.round1 i J e message) =
      tsigOracles lift (dealtWith lift parameter keys' top value) (.round1 i J e message) := by
  simp only [tsigOracles, dealtWith, h]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem bottomOnce_dealt_keys (keys keys' : C.Party → Keys C) (b : Fin (2 ^ layerHeight)) :
    bottomOnce (dealtWith lift parameter keys top value) b = bottomOnce (dealtWith lift parameter keys' top value) b :=
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem tsigOracles_round2_keys (keys keys' : C.Party → Keys C) (i : C.Party) (J : C.Quorum) (e : KeyIndex)
    (message : Message) (parts : C.Party → Digest) (h : keys i = keys' i) :
    tsigOracles lift (dealtWith lift parameter keys top value) (.round2 i J e message parts) =
      tsigOracles lift (dealtWith lift parameter keys' top value) (.round2 i J e message parts) := by
  simp only [tsigOracles]
  rw [bottomOnce_dealt_keys lift parameter top value keys keys']
  simp only [dealtWith, h]

end Dealers

/-! ## Invariants of the state of the game -/

section Keeps

variable {W σ : Type}

/-- Each run of `x` from a state with `I` ends in a state with `I`. -/
def KeepsS (I : RealState C σ → Prop) {α : Type} (x : SharedM C ProbComp W σ α) : Prop :=
  ∀ s w, I s → ∀ z ∈ support ((x.run s).run w), I z.1.2

/-- `KeepsS` from each state of the signing game. -/
def KeepsT (I : RealState C σ → Prop) {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp W σ) α) : Prop :=
  ∀ st, KeepsS I (x.run st)

variable {I : RealState C σ → Prop}

theorem KeepsS.bind {α β : Type} {x : SharedM C ProbComp W σ α} {f : α → SharedM C ProbComp W σ β}
    (hx : KeepsS I x) (hf : ∀ a, KeepsS I (f a)) : KeepsS I (x >>= f) := fun s w hs z hz => by
  rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  exact hf p.1.1 p.1.2 p.2 (hx s w hs p hp) z hz

theorem keepsS_pure {α : Type} (a : α) : KeepsS I (pure a : SharedM C ProbComp W σ α) := fun s w hs z hz => by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact hs

theorem keepsS_get_bind {α : Type} {f : RealState C σ → SharedM C ProbComp W σ α}
    (h : ∀ s, I s → KeepsS I (f s)) : KeepsS I (get >>= f) := fun s w hs z hz => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact h s hs s w hs z hz

theorem keepsS_set (t : RealState C σ) (ht : I t) : KeepsS I (set t : SharedM C ProbComp W σ PUnit) :=
  fun s w _ z hz => by
  rw [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact ht

theorem keepsS_modify (f : RealState C σ → RealState C σ) (hf : ∀ s, I s → I (f s)) :
    KeepsS I (modify f : SharedM C ProbComp W σ PUnit) := fun s w hs z hz => by
  rw [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact hf s hs

theorem keepsS_lift {α : Type} (x : StateT W ProbComp α) :
    KeepsS I (StateT.lift x : SharedM C ProbComp W σ α) := fun s w hs z hz => by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨p, -, rfl⟩ := hz
  exact hs

theorem keepsS_mapGet {α : Type} (f : RealState C σ → α) : KeepsS I (f <$> (get : SharedM C ProbComp W σ _)) := by
  rw [map_eq_bind_pure_comp]
  exact keepsS_get_bind fun _ _ => keepsS_pure _

theorem KeepsT.bind {α β : Type} {x : StateT (TsigState C) (SharedM C ProbComp W σ) α}
    {f : α → StateT (TsigState C) (SharedM C ProbComp W σ) β} (hx : KeepsT I x) (hf : ∀ a, KeepsT I (f a)) :
    KeepsT I (x >>= f) := fun st => by
  rw [StateT.run_bind]
  exact (hx st).bind fun p => hf p.1 p.2

theorem keepsT_pure {α : Type} (a : α) : KeepsT I (pure a : StateT (TsigState C) (SharedM C ProbComp W σ) α) :=
  fun _ => keepsS_pure _

theorem keepsT_lift {α : Type} {x : SharedM C ProbComp W σ α} (h : KeepsS I x) :
    KeepsT I (StateT.lift x : StateT (TsigState C) (SharedM C ProbComp W σ) α) := fun _ =>
  h.bind fun _ => keepsS_pure _

theorem keepsT_get_bind {α : Type} {f : RealState C σ → StateT (TsigState C) (SharedM C ProbComp W σ) α}
    (h : ∀ s, I s → KeepsT I (f s)) : KeepsT I (StateT.lift get >>= f) := fun st s w hs z hz => by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get] at hz
  exact h s hs st s w hs z hz

theorem KeepsS.of_eq {α : Type} {x x' : SharedM C ProbComp W σ α} (h : KeepsS I x) (e : x = x') : KeepsS I x' :=
  e ▸ h

/-- A computation of the world keeps the state of the game, and its result is in its support. -/
theorem keepsS_lift_bind {α β : Type} {x : StateT W ProbComp α} {f : α → SharedM C ProbComp W σ β}
    (h : ∀ a w w', (a, w') ∈ support (x.run w) → KeepsS I (f a)) : KeepsS I (StateT.lift x >>= f) :=
  fun s w hs z hz => by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  exact h a.1 w a.2 ha s a.2 hs z hz

end Keeps

/-! ## The operators keep their keys -/

section Runs

variable {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (view : W → StreamState C)

/-- The keys of the operators are `keys`. -/
def KeysAre {σ : Type} (keys : C.Party → Option (Keys C)) (s : RealState C σ) : Prop :=
  ∀ i, (s.operators i).keys = keys i

omit [Fintype E] [DecidableEq E] in
theorem keepsS_sharedRunWith (keys : C.Party → Option (Keys C)) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (program : C.Party → RecM C E TreeOutput) (tree : Tree) :
    KeepsS (KeysAre keys) (sharedRunWith K circuits settings impl view D net program tree) := by
  unfold sharedRunWith
  refine keepsS_get_bind fun s hs => ?_
  refine (keepsS_lift _).bind fun before => (keepsS_lift _).bind fun r => (keepsS_lift _).bind fun after => ?_
  refine (keepsS_lift _).bind fun v => keepsS_set _ fun i => ?_
  rw [← hs i]
  cases tree <;> rfl

omit [Fintype E] [DecidableEq E] in
theorem keepsS_sharedRuns (keys : C.Party → Option (Keys C)) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, KeepsS (KeysAre keys)
      (sharedRuns K circuits settings runLimit impl view Mode.real D net parameter seeds dealt emu tree count)
  | 0 => keepsS_pure _
  | count + 1 => by
    unfold sharedRuns
    refine keepsS_get_bind fun s _ => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h]
      refine KeepsS.bind ?_ fun _ => keepsS_sharedRuns keys D net parameter seeds dealt emu tree count
      unfold sharedRun
      refine keepsS_get_bind fun s' _ => ?_
      have hnot : ¬ s'.runs tree < Mode.real.emulated tree := by simp [Mode.real]
      rw [ite_eq_right hnot]
      exact keepsS_sharedRunWith K circuits settings impl view keys D net _ tree
    · rw [ite_eq_right h]
      exact keepsS_pure _

end Runs

/-! ## The live signing phase -/

section Live

variable {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (view : W → StreamState C)

/-- `x` and `y` agree from each state with `I`. -/
def EqOnT {σ α : Type} (I : RealState C σ → Prop) (x y : StateT (TsigState C) (SharedM C ProbComp W σ) α) : Prop :=
  ∀ st s w, I s → ((x.run st).run s).run w = ((y.run st).run s).run w

theorem eqOnT_simulateQ {σ : Type} {I : RealState C σ → Prop} {ι : Type} {spec : OracleSpec ι} {α : Type}
    (i₁ i₂ : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp W σ)))
    (heq : ∀ t, EqOnT I (i₁ t) (i₂ t)) (hk : ∀ t, KeepsT I (i₁ t)) (oa : OracleComp spec α) :
    EqOnT I (simulateQ i₁ oa) (simulateQ i₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st s w _; simp
  | query_bind t k ih =>
    intro st s w hs
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self,
      StateT.run_bind, id_eq]
    rw [bind_congr_of_forall_mem_support _ fun q hq => ih q.1.1.1 q.1.1.2 q.1.2 q.2 (hk t st s w hs q hq),
      heq t st s w hs]

omit [Fintype E] [DecidableEq E] in
theorem eqOnT_dealerOracles (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (keys : C.Party → Option (Keys C)) (dealt dealt' : C.Party → Keys C)
    (hdeal : ∀ i k, keys i = some k → dealt i = dealt' i) (emu emu' : C.Party → Option (Keys C)) (top : TopTree)
    (value : Point → SharedM C ProbComp W A.net.State Digest) (q : TsigQuery C) :
    EqOnT (KeysAre keys)
      (sharedDealerOracles K circuits settings runLimit impl view Mode.real D A.net parameter seeds dealt emu
        (dealtWith (sharedLift impl) parameter dealt top value) q)
      (sharedDealerOracles K circuits settings runLimit impl view Mode.real D A.net parameter seeds dealt' emu'
        (dealtWith (sharedLift impl) parameter dealt' top value) q) := by
  unfold sharedDealerOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · intro st s w _
    rfl
  · dsimp only
    rw [tsigOracles_tree_keys (sharedLift impl) parameter top value dealt dealt' b,
      sharedRuns_real_params K circuits settings runLimit impl view D A.net parameter parameter seeds seeds dealt
        dealt' emu emu' (.bottom b) 1]
    intro st s w _
    rfl
  all_goals
    dsimp only
    intro st s w hs
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_get, bind_assoc, pure_bind]
    rw [hs i]
    rcases hk : keys i with _ | k
    · rfl
    · first
        | rw [tsigOracles_round1_keys (sharedLift impl) parameter top value dealt dealt' i J e message
            (hdeal i k hk)]
        | rw [tsigOracles_round2_keys (sharedLift impl) parameter top value dealt dealt' i J e message parts
            (hdeal i k hk)]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The signing oracles of the dealer keep the state of the game. -/
theorem keepsT_tsig {σ : Type} (I : RealState C σ → Prop) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (top : TopTree) (q : TsigQuery C) :
    KeepsT I (tsigOracles (sharedLift (σ := σ) impl) (dealtWith (sharedLift impl) parameter dealt top
      fun x => sharedLift impl (prfValue seeds x)) q) := fun st => by
  have d := hmap_dealtWith_hom (worldHom impl σ) (fun oa => free (liftComp oa _)) parameter dealt top
    fun x => free (liftComp (prfValue seeds x) _)
  have e := SeedHitProof.hom_tsigOracles (worldHom impl σ) (fun oa => free (liftComp oa _))
    (dealtWith (fun oa => free (liftComp oa _)) parameter dealt top fun x => free (liftComp (prfValue seeds x) _)) q st
  rw [d] at e
  exact (keepsS_lift _).of_eq e

omit [Fintype E] [DecidableEq E] in
theorem keepsT_dealerOracles (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (top : TopTree) (q : TsigQuery C) :
    KeepsT (KeysAre keys)
      (sharedDealerOracles K circuits settings runLimit impl view Mode.real D A.net parameter seeds dealt emu
        (dealtWith (sharedLift impl) parameter dealt top fun x => sharedLift impl (prfValue seeds x)) q) := by
  unfold sharedDealerOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact keepsT_pure _
  · dsimp only
    refine (keepsT_tsig impl _ parameter seeds dealt top _).bind fun answer => ?_
    change Option (BottomTree × Digest) at answer
    simp only [show Mode.real.skip = false from rfl, true_or, ↓reduceIte]
    refine (keepsT_lift (keepsS_sharedRuns K circuits settings runLimit impl view keys D A.net parameter seeds dealt
      emu _ 1)).bind fun _ => keepsT_get_bind fun s _ => ?_
    rcases heldBottom D s.operators b with _ | tree <;> rcases answer with _ | ⟨_, ρ⟩ <;> exact keepsT_pure _
  all_goals
    dsimp only
    refine KeepsT.bind (keepsT_lift (keepsS_modify _ fun s hs => hs)) fun _ => keepsT_get_bind fun s _ => ?_
    split
    · exact keepsT_tsig impl _ parameter seeds dealt top _
    · exact keepsT_pure _

omit [Fintype E] [DecidableEq E] in
/-- On a state with the keys `keys`, the signing phase reads the keys of the dealer only at an operator
with keys. -/
theorem sharedSigning_dealt_eq (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (keys : C.Party → Option (Keys C)) (dealt dealt' : C.Party → Keys C)
    (hdeal : ∀ i k, keys i = some k → dealt i = dealt' i) (emu emu' : C.Party → Option (Keys C))
    (s : RealState C A.net.State) (hs : KeysAre keys s) (w : W) :
    ((sharedSigning K circuits settings runLimit impl view false Mode.real D A parameter seeds dealt emu).run s).run w =
      ((sharedSigning K circuits settings runLimit impl view false Mode.real D A parameter seeds dealt' emu').run s).run
        w := by
  unfold sharedSigning
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases topHolder D s.operators with
  | none => rfl
  | some kt =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold sharedDealer
    have e₁ : referenceTree (fun oa => sharedLift (σ := A.net.State) impl (tweakable oa))
        (fun x => sharedLift (σ := A.net.State) impl (prfValue seeds x)) parameter emptyTop .top =
        StateT.lift (simulateQ impl (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top)) :=
      (SeedHitProof.hom_referenceTree (worldHom impl A.net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    simp only [bind_assoc, pure_bind, StateT.run_bind]
    rw [e₁]
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    refine bind_congr fun p => ?_
    rcases p with ⟨out, w'⟩
    refine congrArg₂ (· >>= ·) ?_ (funext fun p => ?_)
    · refine eqOnT_simulateQ _ _ (fun t => ?_) (fun t => ?_) _ _ _ _ hs
      · rcases t with t | q | q
        · simp only [QueryImpl.add_apply_inl]
          intro st s w _
          rfl
        · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          exact eqOnT_dealerOracles K circuits settings runLimit impl view D A parameter seeds keys dealt dealt' hdeal
            emu emu' _ _ q
        · simp only [QueryImpl.add_apply_inr]
          rcases q with _ | state <;> intro st s w _ <;> rfl
      · rcases t with t | q | q
        · exact keepsT_lift (keepsS_lift _)
        · exact keepsT_dealerOracles K circuits settings runLimit impl view keys D A parameter seeds dealt emu _ q
        · rcases q with _ | state
          · exact keepsT_lift (keepsS_mapGet _)
          · exact keepsT_lift (keepsS_modify _ fun s hs => hs)
    · rw [forgeryWins_dealt_keys (sharedLift (σ := A.net.State) impl) parameter ((TreeOutput.topTree out).getD emptyTop)
        (fun x => sharedLift impl (prfValue seeds x)) dealt dealt']

end Live

/-! ## The dead runs of the top tree -/

section Dead

variable (prims : Primitives)

omit [Fintype E] [DecidableEq E] in
theorem startsWithRound_treeProgram_top (i : C.Party) {σ : Type} (s : RealState C σ) :
    StartsWithRound (treeProgram K circuits settings i (s.operators i) .top) := by
  rw [treeProgram_top]
  exact startsWithRound_bind _ _ (startsWithRound_ceremonyProgram K circuits settings i _)

omit [Fintype E] [DecidableEq E] in
/-- A real run of the top tree in `loggedWorld` in which an honest operator has no keys gives no honest
output. -/
theorem loggedRun_dead (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (s : RealState C net.State)
    (st : net.State) (i₀ : C.Party) (hi₀ : i₀ ∉ D.1) (hk : (s.operators i₀).keys = none) (w : LogState C) :
    ∀ r ∈ support ((simulateQ (loggedWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) (treeFuel circuits settings) st fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) .top).run.run)).run w),
    ∀ i, i ∉ D.1 → (r.1.2 i).output = none := by
  intro r hr
  have h1 : (r.1, r.2.1) ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) (treeFuel circuits settings) st fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) .top).run.run)).run w.1) := by
    rw [← withLog_run (streamWorld prims D) countedCells _ w.1 w.2, support_map]
    exact ⟨r, hr, rfl⟩
  have h2 : ((r.1.1, fun i => (r.1.2 i).output), r.2.1) ∈ support ((simulateQ (streamWorld prims D)
      (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) st fun i =>
        treeProgram K circuits settings i (s.operators i) .top)).run w.1) := by
    rw [treeProgram_eq_drop K circuits settings s.operators .top,
      executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D net noFunctionality
        ([] : Record C E), simulateQ_map, StateT.run_map, support_map]
    exact ⟨_, h1, rfl⟩
  exact phase_dead_noOutput prims D net _ st _ i₀ hi₀ (by simp [treeProgram, hk])
    (fun i _ => startsWithRound_treeProgram_top K circuits settings i s) w.1 _ h2

/-- The keys of the operators are `keys`, and no honest operator holds a top tree. -/
def NoTop {σ : Type} (D : C.Coalition) (keys : C.Party → Option (Keys C)) (s : RealState C σ) : Prop :=
  KeysAre keys s ∧ ∀ i, i ∉ D.1 → (s.operators i).top = none

omit [Fintype E] [DecidableEq E] in
theorem keepsS_sharedRuns_dead (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (keys : C.Party → Option (Keys C)) (hdead : ∃ i₀, i₀ ∉ D.1 ∧ keys i₀ = none) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) :
    ∀ count, KeepsS (NoTop D keys) (sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D
      net parameter seeds dealt emu .top count)
  | 0 => keepsS_pure _
  | count + 1 => by
    obtain ⟨i₀, hi₀, hk⟩ := hdead
    unfold sharedRuns
    refine keepsS_get_bind fun s _ => ?_
    by_cases h : mayRun runLimit D s .top
    · rw [ite_eq_left h]
      refine KeepsS.bind ?_ fun _ => keepsS_sharedRuns_dead D net keys ⟨i₀, hi₀, hk⟩ parameter seeds dealt emu count
      unfold sharedRun
      refine keepsS_get_bind fun s hs => ?_
      have hnot : ¬ s.runs .top < Mode.real.emulated .top := by simp [Mode.real]
      rw [ite_eq_right hnot]
      unfold sharedRunWith
      refine keepsS_get_bind fun s' hs' => ?_
      refine (keepsS_lift _).bind fun before => keepsS_lift_bind fun r w w' hr => ?_
      rcases r with ⟨state, steps⟩
      refine (keepsS_lift _).bind fun after => (keepsS_lift _).bind fun v => keepsS_set _ ⟨fun i => ?_, fun i hi => ?_⟩
      · rw [← hs'.1 i]
        rfl
      · have hno := loggedRun_dead K circuits settings prims D net s _ i₀ hi₀ ((hs.1 i₀).trans hk) w _ hr i hi
        simp [OperatorState.keep, committed, hs'.2 i hi, hno, TreeOutput.topTree]
    · rw [ite_eq_right h]
      exact keepsS_pure _

end Dead

/-! ## The two rests -/

section Agree

variable (prims : Primitives)

omit [Fintype E] [DecidableEq E] in
/-- The shared rest from the start with the keys `keys` in `loggedWorld` gives the same results with two
dealers that agree on the parameter, on the seeds and on the keys of each operator with keys, when
each honest operator has keys. -/
theorem sharedRest_dealt_eq (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : C.Party → Option (Keys C))
    (parameter parameter' : PublicParameter) (seeds seeds' : C.Term → HashOutput) (dealt dealt' : C.Party → Keys C)
    (emu emu' : C.Party → Option (Keys C))
    (hlive : (∀ i, i ∉ D.1 → keys i ≠ none) →
      parameter = parameter' ∧ seeds = seeds' ∧ ∀ i k, keys i = some k → dealt i = dealt' i)
    (state : A.net.State) (w : LogState C) :
    (sharedRest K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A parameter seeds dealt
      emu (startState D state keys)).run w =
      (sharedRest K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A parameter' seeds'
        dealt' emu' (startState D state keys)).run w := by
  unfold sharedRest
  simp only [inWorld, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, pure_bind, bind_assoc]
  refine bind_congr fun v => ?_
  obtain ⟨⟨state', ok⟩, w'⟩ := v
  have hlive' : (∀ i, i ∉ D.1 → committed ok keys i ≠ none) →
      parameter = parameter' ∧ seeds = seeds' ∧ ∀ i k, committed ok keys i = some k → dealt i = dealt' i := by
    cases ok
    · intro h
      obtain ⟨i, hi⟩ := exists_honest D
      exact absurd rfl (h i hi)
    · exact hlive
  dsimp only
  rw [sharedRuns_real_params K circuits settings runLimit (loggedWorld prims D) Prod.fst D A.net parameter parameter'
    seeds seeds' dealt dealt' (committed ok emu) (committed ok emu') .top runLimit]
  refine bind_congr_of_forall_mem_support _ fun p hp => ?_
  by_cases hl : ∀ i, i ∉ D.1 → committed ok keys i ≠ none
  · obtain ⟨rfl, rfl, hd⟩ := hlive' hl
    have hk : KeysAre (committed ok keys) p.1.2 := keepsS_sharedRuns K circuits settings runLimit
      (loggedWorld prims D) Prod.fst (committed ok keys) D A.net _ _ _ _ .top runLimit _ w' (fun i => rfl) p hp
    rw [sharedSigning_dealt_eq K circuits settings runLimit (loggedWorld prims D) Prod.fst D A parameter seeds
      (committed ok keys) dealt dealt' hd (committed ok emu) (committed ok emu') p.1.2 hk p.2]
  · push Not at hl
    obtain ⟨i₀, hi₀, hk₀⟩ := hl
    have hn : NoTop D (committed ok keys) p.1.2 := keepsS_sharedRuns_dead K circuits settings runLimit prims D A.net
      (committed ok keys) ⟨i₀, hi₀, hk₀⟩ _ _ _ _ runLimit _ w' ⟨fun i => rfl, fun i _ => rfl⟩ p hp
    have htop : topHolder D p.1.2.operators = none := by
      unfold topHolder
      rw [List.find?_eq_none.2 fun i _ => by by_cases hi : i ∈ D.1 <;> simp [hi, hn.2 i]]
    unfold sharedSigning
    simp only [StateT.run_bind, StateT.run_get, pure_bind, htop]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The keys of the dealer are `dealtKeys` on each result of `worldSeedGen`. -/
theorem worldSeedGen_dealt (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (r : net.State × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C)))
    (hr : r ∈ support (worldSeedGen D net)) : ∃ pairKeys, r.2.2.2.1 = dealtKeys r.2.1 r.2.2.1 pairKeys := by
  unfold worldSeedGen at hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨a, -, b, hb, parts, -, steps, -, c, -, high, -, -, -, -, -, -, -, d, -, rfl⟩ := hr
  have hb' : b ∈ support (prawnsKeyGen (C := C)) := by
    have h := support_simulateQ_subset _ _ hb
    rwa [support_liftComp] at h
  exact prawnsKeyGen_support b hb'

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- When each honest operator holds the keys of the dealer, the parameter and the seeds of the game are
the ones of the dealer. -/
theorem game_of_dealt (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (emu : C.Party → Option (Keys C))
    (hlive : ∀ i, i ∉ D.1 → ((emu i).map fun _ => dealtKeys parameter seeds pairKeys i) ≠ none) :
    gameParameter D (fun i => (emu i).map fun _ => dealtKeys parameter seeds pairKeys i) = parameter ∧
      gameSeeds D (fun i => (emu i).map fun _ => dealtKeys parameter seeds pairKeys i) = seeds := by
  constructor
  · unfold gameParameter
    split
    · rename_i i hi
      have h := List.find?_some hi
      simp only [decide_eq_true_eq] at h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h.2
      dsimp only
      rw [hk]
      simp only [Option.map_eq_some_iff] at hk
      obtain ⟨_, -, rfl⟩ := hk
      rfl
    · rename_i hnone
      obtain ⟨j, hj⟩ := exists_honest D
      rw [List.find?_eq_none] at hnone
      exact absurd (hnone j (by simp [Committee.parties])) (by simpa [hj, Option.isSome_iff_ne_none] using hlive j hj)
  · funext T
    unfold gameSeeds
    split
    · rename_i i hi
      have h := List.find?_some hi
      simp only [decide_eq_true_eq] at h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h.2.2
      dsimp only
      rw [hk]
      simp only [Option.map_eq_some_iff] at hk
      obtain ⟨_, -, rfl⟩ := hk
      simp [dealtKeys, h.1]
    · rename_i hnone
      obtain ⟨j, hjT, hj⟩ := exists_honest_holder D T
      rw [List.find?_eq_none] at hnone
      exact absurd (hnone j (by simp [Committee.parties]))
        (by simpa [hjT, hj, Option.isSome_iff_ne_none] using hlive j hj)

omit [Fintype E] [DecidableEq E] in
/-- The statement of `SharedDealtAgree` with its premise on the corrupt operators. -/
theorem sharedDealtAgree_holds (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ∀ z ∈ support ((simulateQ (loggedWorld prims D) (worldSeedGen D A.net)).run ((∅, ∅), [])),
      Pr{let r ← (sharedRestOf K circuits settings runLimit (loggedWorld prims D) Prod.fst false D A z.1.1
          fun i => (z.1.2.2.2.2 i).map fun _ => z.1.2.2.2.1 i).run' z.2}[Clean r] =
        Pr{let r ← (sharedRest K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A
          z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2
            (startState D z.1.1 fun i => (z.1.2.2.2.2 i).map fun _ => z.1.2.2.2.1 i)).run' z.2}[Clean r] := by
  intro z hz
  have hsupp : z.1 ∈ support (worldSeedGen D A.net) :=
    support_simulateQ_run'_subset (loggedWorld prims D) _ ((∅, ∅), []) (by
      rw [StateT.run'_eq, support_map]
      exact ⟨z, hz, rfl⟩)
  obtain ⟨pairKeys, hdealt⟩ := worldSeedGen_dealt D A.net z.1 hsupp
  unfold sharedRestOf
  rw [StateT.run'_eq, StateT.run'_eq, sharedRest_dealt_eq K circuits settings runLimit prims D A _ _ z.1.2.1 _
    z.1.2.2.1 _ z.1.2.2.2.1 _ z.1.2.2.2.2 (fun hl => ?_)]
  have hg := game_of_dealt D z.1.2.1 z.1.2.2.1 pairKeys z.1.2.2.2.2 (by rw [← hdealt]; exact hl)
  rw [← hdealt] at hg
  refine ⟨hg.1, hg.2, fun i k hk => ?_⟩
  show ((z.1.2.2.2.2 i).map fun _ => z.1.2.2.2.1 i).getD noKeys = z.1.2.2.2.1 i
  rcases h : z.1.2.2.2.2 i with _ | e
  · simp [h] at hk
  · rfl

end Agree

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedDealtAgree_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedDealtAgree_holds
