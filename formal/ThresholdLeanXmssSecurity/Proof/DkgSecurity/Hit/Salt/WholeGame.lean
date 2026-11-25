import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.WholeCore

/-!
# The invariant of the world along the game with the keys of the dealer

`KeepsS` and `KeepsT` are `KeepsQ` from each state of the game and of the signing game. The walk
`keeps_dealtRun` gives `KeepsQ` for `dealtRun` with no emulated run, from `CallKeeps`, `DrawKeeps` and
the hypothesis `TreeWhole` that the program of each operator in a run of a tree has whole salt draws.
The seed generation, the adversary, the dealer, its signing oracles and the win test make no honest
call of `SaltDraw`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (PartyP HonestP)
open PFunctor.FreeM (cost)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (Inv : W → Prop)

/-! ## The calculus on the states of the game -/

namespace Salt

section Calculus

/-- `KeepsQ` from each state of the game. -/
def KeepsS {σ α : Type} (m : RealM C σ α) : Prop := ∀ s, KeepsQ impl Inv (m.run s) fun _ => True

/-- `KeepsS` from each state of the signing game. -/
def KeepsT {σ α : Type} (m : StateT (TsigState C) (RealM C σ) α) : Prop := ∀ t, KeepsS impl Inv (m.run t)

variable {impl Inv} {σ : Type}

theorem keepsS_pure {α : Type} (a : α) : KeepsS impl Inv (pure a : RealM C σ α) := fun _ =>
  keepsQ_pure trivial

theorem KeepsS.bind {α β : Type} {m : RealM C σ α} {f : α → RealM C σ β} (h : KeepsS impl Inv m)
    (hf : ∀ a, KeepsS impl Inv (f a)) : KeepsS impl Inv (m >>= f) := fun s => by
  rw [StateT.run_bind]
  exact (h s).bind fun p _ => hf p.1 p.2

theorem keepsS_get_bind {α : Type} {f : RealState C σ → RealM C σ α} (h : ∀ s, KeepsQ impl Inv ((f s).run s) fun _ => True) :
    KeepsS impl Inv (get >>= f) := fun s => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact h s

theorem keepsS_set (t : RealState C σ) : KeepsS impl Inv (set t : RealM C σ PUnit) := fun _ => by
  rw [StateT.run_set]
  exact keepsQ_pure trivial

theorem keepsS_modify (f : RealState C σ → RealState C σ) : KeepsS impl Inv (modify f : RealM C σ PUnit) := fun _ => by
  rw [StateT.run_modify]
  exact keepsQ_pure trivial

theorem KeepsS.of_eq {α : Type} {m m' : RealM C σ α} (h : KeepsS impl Inv m) (e : m = m') : KeepsS impl Inv m' :=
  e ▸ h

theorem keepsS_lift {α : Type} {x : OracleComp (WorldSpec C) α} {Q : α → Prop} (h : KeepsQ impl Inv x Q) :
    KeepsS impl Inv (StateT.lift x : RealM C σ α) := fun _ => by
  rw [StateT.run_lift]
  exact h.bind fun _ _ => keepsQ_pure trivial

theorem keepsS_map_get {α : Type} (f : RealState C σ → α) : KeepsS impl Inv (f <$> (get : RealM C σ _)) := fun _ => by
  simp only [StateT.run_map, StateT.run_get, map_pure]
  exact keepsQ_pure trivial

theorem keepsT_pure {α : Type} (a : α) : KeepsT impl Inv (pure a : StateT (TsigState C) (RealM C σ) α) := fun _ =>
  keepsS_pure _

theorem KeepsT.bind {α β : Type} {m : StateT (TsigState C) (RealM C σ) α} {f : α → StateT (TsigState C) (RealM C σ) β}
    (h : KeepsT impl Inv m) (hf : ∀ a, KeepsT impl Inv (f a)) : KeepsT impl Inv (m >>= f) := fun t => by
  rw [StateT.run_bind]
  exact (h t).bind fun p => hf p.1 p.2

theorem keepsT_lift {α : Type} {m : RealM C σ α} (h : KeepsS impl Inv m) :
    KeepsT impl Inv (StateT.lift m : StateT (TsigState C) (RealM C σ) α) := fun _ => by
  rw [StateT.run_lift]
  exact h.bind fun _ => keepsS_pure _

theorem keepsT_get_bind {α : Type} {f : RealState C σ → StateT (TsigState C) (RealM C σ) α}
    (h : ∀ s, KeepsT impl Inv (f s)) : KeepsT impl Inv (StateT.lift get >>= f) :=
  KeepsT.bind (keepsT_lift (fun _ => by rw [StateT.run_get]; exact keepsQ_pure trivial)) h

/-- A program through a handler of the signing game whose calls keep `Inv` keeps `Inv`. -/
theorem KeepsT.simulateQ {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}
    (handler : QueryImpl spec' (StateT (TsigState C) (RealM C σ))) (h : ∀ t, KeepsT impl Inv (handler t))
    {α : Type} (oa : OracleComp spec' α) : KeepsT impl Inv (simulateQ handler oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using keepsT_pure (impl := impl) (Inv := Inv) (σ := σ) a
  | query_bind t f ih =>
    rw [simulateQ_query_bind]
    exact (h t).bind ih

end Calculus

end Salt

/-! ## The pieces with no honest call of `SaltDraw` -/

section Quiet

variable {impl Inv} (h₁ : CallKeeps impl Inv)
include h₁

/-- A world program with a zero cost of honest calls of `SaltDraw` keeps `Inv`. -/
theorem keepsQ_ofCost {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : cost (callCharge (HonestP SaltDraw)) oa ≤ 0) : KeepsQ impl Inv oa fun _ => True :=
  KeepsQ.of_noCall impl Inv h₁ _ ((cost_callCharge_le_iff _ _ 0).1 h)

omit h₁ in
theorem hfree_salt {α : Type} (oa : OracleComp (RoSpec C) α) (h : NoCall TailCall oa) :
    cost (callCharge (HonestP SaltDraw)) (DkgCompletenessProof.freeHom oa) ≤ 0 :=
  cost_free_tail saltDraw_tail oa h

end Quiet

/-! ## The rest of the game with no emulated run -/

section Rest

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

/-- The program of each operator in a run of a tree has whole salt draws. -/
def TreeWhole : Prop :=
  ∀ (i : C.Party) (operator : OperatorState C) (tree : Tree),
    SaltWhole (treeProgram K circuits settings i operator tree).run

variable {impl Inv} (h₁ : CallKeeps impl Inv) (h₂ : DrawKeeps impl Inv)
  (htree : TreeWhole (C := C) (E := E) K circuits settings)
include h₁ h₂ htree

omit [Fintype E] [DecidableEq E] in
theorem keepsS_treeRun (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    Salt.KeepsS impl Inv (treeRun K circuits settings noMonitor D net tree) := by
  unfold treeRun
  refine Salt.keepsS_get_bind fun s => ?_
  refine (Salt.KeepsS.bind (Salt.keepsS_lift (keepsQ_executePhase h₁ h₂ D net _ _ _ fun j _ => htree j _ tree))
    fun r => Salt.KeepsS.bind (Salt.keepsS_lift (Q := fun _ => True) ?_) fun bad =>
      Salt.KeepsS.bind (Salt.keepsS_lift (Q := fun _ => True) (KeepsQ.of_noCall impl Inv h₁ _
        (IsQueryBoundP.of_imp (honestP_of_tail saltDraw_tail)
          (quiet_voteRound D net _ _ fun _ _ => queryClass_map_treeVote)))) fun v => Salt.keepsS_set _) s
  simp only [noMonitor]
  exact keepsQ_pure trivial

omit [Fintype E] [DecidableEq E] in
theorem keepsS_secRuns (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, Salt.KeepsS impl Inv (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count)
  | 0 => Salt.keepsS_pure _
  | count + 1 => by
    have rest := keepsS_secRuns m hm net parameter seeds dealt emu tree count
    unfold secRuns
    refine Salt.keepsS_get_bind fun s => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h]
      refine (Salt.KeepsS.bind ?_ fun _ => rest) s
      unfold secRun
      refine Salt.keepsS_get_bind fun s' => ?_
      rw [ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _)]
      exact keepsS_treeRun K circuits settings D h₁ h₂ htree net tree s'
    · rw [ite_eq_right h]
      exact keepsQ_pure trivial

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] h₂ htree in
theorem Salt.keepsT_tsig {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C)
    (htsig : ∀ st, cost (callCharge (HonestP SaltDraw)) ((tsigOracles (fun oa => free (liftComp oa _)) d q).run st) ≤ 0) :
    Salt.KeepsT impl Inv (tsigOracles (realLift (σ := σ)) (SeedHitProof.Dealt.hmap (realHom σ) d) q) := fun st =>
  (Salt.keepsS_lift (keepsQ_ofCost h₁ _ (htsig st))).of_eq
    (SeedHitProof.hom_tsigOracles (realHom σ) (fun oa => free (liftComp oa _)) d q st)

omit [Fintype E] [DecidableEq E] in
theorem keepsT_secOracles (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (top : TopTree) (q : TsigQuery C) :
    Salt.KeepsT impl Inv (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu
      (SeedHitProof.Dealt.hmap (realHom A.net.State) (worldDealt₀ parameter seeds dealt top)) q) := by
  have htsig : ∀ q st, cost (callCharge (HonestP SaltDraw)) ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0 :=
    Salt.cost_dealerOracles _ (fun oa h => hfree_salt oa h) parameter seeds dealt top
  unfold secOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact Salt.keepsT_pure _
  · dsimp only
    unfold secTreeRequest
    refine (Salt.keepsT_tsig h₁ _ _ (htsig _)).bind fun answer => ?_
    by_cases hc : m.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      refine (Salt.keepsT_lift (keepsS_secRuns K circuits settings runLimit D h₁ h₂ htree m hm A.net
        parameter seeds dealt emu _ 1)).bind fun _ => Salt.keepsT_get_bind fun s => ?_
      split <;> exact Salt.keepsT_pure _
    · simp only [hc, ↓reduceIte]
      refine Salt.keepsT_get_bind fun s => ?_
      split <;> exact Salt.keepsT_pure _
  all_goals
    dsimp only
    unfold secSignRequest
    refine (Salt.keepsT_lift (Salt.keepsS_modify _)).bind fun _ => Salt.keepsT_get_bind fun s => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first
        | exact Salt.keepsT_tsig h₁ _ _ (htsig _)
        | exact Salt.keepsT_pure _

omit [Fintype E] [DecidableEq E] in
theorem keepsS_secSigning (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    Salt.KeepsS impl Inv (secSigning K circuits settings runLimit m D A parameter seeds dealt emu) := by
  unfold secSigning
  refine Salt.keepsS_get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact keepsQ_pure trivial
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
    refine (Salt.KeepsS.bind (Salt.keepsS_lift (keepsQ_ofCost h₁ _ (Salt.cost_dealerTree _ (fun oa h => hfree_salt oa h) _ _)))
      fun out => ?_) s
    have d₂ : dealtWith (realLift (σ := A.net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₂]
    refine Salt.KeepsS.bind (fun s => Salt.KeepsT.simulateQ _ (fun t => ?_) _ _ s) fun z => ?_
    · rcases t with t | q | q
      · exact Salt.keepsT_lift (Salt.keepsS_lift (keepsQ_adversary h₁ _))
      · exact keepsT_secOracles K circuits settings runLimit D h₁ h₂ htree m hm A parameter seeds dealt emu _ q
      · rcases q with _ | state
        · exact Salt.keepsT_lift (Salt.keepsS_map_get _)
        · exact Salt.keepsT_lift (Salt.keepsS_modify _)
    · rcases z with ⟨forgery, st⟩
      exact (Salt.keepsS_lift (keepsQ_ofCost h₁ _ (Salt.cost_dealerWins _ (fun oa h => hfree_salt oa h) _ _ _ _ st
        forgery))).of_eq (hom_forgeryWins (realHom A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)

omit [Fintype E] [DecidableEq E] in
/-- `dealtRun` with no emulated run keeps `Inv`. -/
theorem keeps_dealtRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) :
    KeepsQ impl Inv (dealtRun K circuits settings runLimit m D A) fun _ => True := by
  unfold dealtRun
  refine (KeepsQ.of_noCall impl Inv h₁ _ (IsQueryBoundP.of_imp (honestP_of_tail saltDraw_tail)
    (worldSeedGen_quiet D A.net))).bind fun x _ => ?_
  obtain ⟨state, parameter, seeds, dealt, emu⟩ := x
  refine KeepsQ.bind (P := fun _ => True) ?_ fun _ _ => keepsQ_pure trivial
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  refine KeepsQ.bind (P := fun _ => True) ?_ fun _ _ => keepsQ_pure trivial
  unfold secRest
  refine (Salt.keepsS_get_bind fun s => ?_) _
  refine (Salt.KeepsS.bind (Salt.keepsS_lift (Q := fun _ => True) (KeepsQ.of_noCall impl Inv h₁ _
    (IsQueryBoundP.of_imp (honestP_of_tail saltDraw_tail)
      (quiet_voteRound D A.net s.adversary _ fun _ _ => queryClass_map_seedVote)))) fun v => ?_) s
  obtain ⟨state', ok⟩ := v
  exact Salt.KeepsS.bind (Salt.keepsS_set _) fun _ => Salt.KeepsS.bind (keepsS_secRuns K circuits settings runLimit D
    h₁ h₂ htree m hm A.net parameter seeds dealt (committed ok emu) .top runLimit) fun _ => keepsS_secSigning K
      circuits settings runLimit D h₁ h₂ htree m hm A parameter seeds dealt (committed ok emu)

end Rest

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.keeps_dealtRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.keeps_dealtRun
