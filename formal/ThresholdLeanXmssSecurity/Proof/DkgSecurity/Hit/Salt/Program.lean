import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.ProgramTree

/-!
# The program fact `SaltProv`

`ProvS` and `ProvT` are `Prov []` from each state of the game and of the signing game. The seed
generation, the adversary, the dealer, its signing oracles and the win test make no call of `Touch`,
and each run of a tree is a phase whose honest programs have check blocks (`treeProv`). So `dealtRun`
with no emulated run has `Prov []` (`prov_dealtRun`), and `saltProv` is `SaltProv`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (HonestP)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)
open PFunctor.FreeM (cost)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} (D : C.Coalition) (δ : Fin 256 → Bit)

/-! ## The calculus on the states of the game -/

section Calculus

/-- `Prov []` from each state of the game. -/
def ProvS {σ α : Type} (m : RealM C σ α) : Prop := ∀ s, Prov D δ [] (m.run s)

/-- `ProvS` from each state of the signing game. -/
def ProvT {σ α : Type} (m : StateT (TsigState C) (RealM C σ) α) : Prop := ∀ t, ProvS D δ (m.run t)

variable {D δ} {σ : Type}

theorem provS_pure {α : Type} (a : α) : ProvS D δ (pure a : RealM C σ α) := fun _ => prov_pure _ _

theorem ProvS.bind {α β : Type} {m : RealM C σ α} {f : α → RealM C σ β} (h : ProvS D δ m)
    (hf : ∀ a, ProvS D δ (f a)) : ProvS D δ (m >>= f) := fun s => by
  rw [StateT.run_bind]
  exact (h s).bind fun p => hf p.1 p.2

theorem provS_get_bind {α : Type} {f : RealState C σ → RealM C σ α} (h : ∀ s, Prov D δ [] ((f s).run s)) :
    ProvS D δ (get >>= f) := fun s => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact h s

theorem provS_set (t : RealState C σ) : ProvS D δ (set t : RealM C σ PUnit) := fun _ => by
  rw [StateT.run_set]
  exact prov_pure _ _

theorem provS_modify (f : RealState C σ → RealState C σ) : ProvS D δ (modify f : RealM C σ PUnit) := fun _ => by
  rw [StateT.run_modify]
  exact prov_pure _ _

theorem ProvS.of_eq {α : Type} {m m' : RealM C σ α} (h : ProvS D δ m) (e : m = m') : ProvS D δ m' := e ▸ h

theorem provS_lift {α : Type} {x : OracleComp (WorldSpec C) α} (h : Prov D δ [] x) :
    ProvS D δ (StateT.lift x : RealM C σ α) := fun _ => by
  rw [StateT.run_lift]
  exact h.bind fun _ => prov_pure _ _

theorem provS_map_get {α : Type} (f : RealState C σ → α) : ProvS D δ (f <$> (get : RealM C σ _)) := fun _ => by
  simp only [StateT.run_map, StateT.run_get, map_pure]
  exact prov_pure _ _

theorem provT_pure {α : Type} (a : α) : ProvT D δ (pure a : StateT (TsigState C) (RealM C σ) α) := fun _ =>
  provS_pure _

theorem ProvT.bind {α β : Type} {m : StateT (TsigState C) (RealM C σ) α} {f : α → StateT (TsigState C) (RealM C σ) β}
    (h : ProvT D δ m) (hf : ∀ a, ProvT D δ (f a)) : ProvT D δ (m >>= f) := fun t => by
  rw [StateT.run_bind]
  exact (h t).bind fun p => hf p.1 p.2

theorem provT_lift {α : Type} {m : RealM C σ α} (h : ProvS D δ m) :
    ProvT D δ (StateT.lift m : StateT (TsigState C) (RealM C σ) α) := fun _ => by
  rw [StateT.run_lift]
  exact h.bind fun _ => provS_pure _

theorem provT_get_bind {α : Type} {f : RealState C σ → StateT (TsigState C) (RealM C σ) α}
    (h : ∀ s, ProvT D δ (f s)) : ProvT D δ (StateT.lift get >>= f) :=
  ProvT.bind (provT_lift (fun _ => by rw [StateT.run_get]; exact prov_pure _ _)) h

theorem ProvT.simulateQ {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}
    (handler : QueryImpl spec' (StateT (TsigState C) (RealM C σ))) (h : ∀ t, ProvT D δ (handler t))
    {α : Type} (oa : OracleComp spec' α) : ProvT D δ (simulateQ handler oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using provT_pure (D := D) (δ := δ) (σ := σ) a
  | query_bind t f ih =>
    rw [simulateQ_query_bind]
    exact (h t).bind ih

end Calculus

/-! ## The pieces with no call of `Touch` -/

theorem touch_tail (t : (WorldSpec C).Domain) (h : Touch t) : HonestP TailLocal t := by
  rcases t with _ | (_ | q | x)
  · exact h.elim
  · exact h.elim
  · exact h
  · exact h.2

theorem prov_ofCost {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : cost (callCharge (HonestP TailLocal)) oa ≤ 0) : Prov D δ [] oa :=
  prov_of_noTouch D δ [] oa ((noCall_iff _ _).2 (IsQueryBoundP.of_imp touch_tail ((cost_callCharge_le_iff _ _ 0).1 h)))

theorem hfree_tail {α : Type} (oa : OracleComp (RoSpec C) α) (h : NoCall TailCall oa) :
    cost (callCharge (HonestP TailLocal)) (DkgCompletenessProof.freeHom oa) ≤ 0 :=
  cost_free_tail (p := TailLocal) (fun _ h => h) oa h

/-! ## The rest of the game with no emulated run -/

section Rest

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
theorem provS_treeRun (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ProvS D δ (treeRun K circuits settings noMonitor D net tree) := by
  unfold treeRun
  refine provS_get_bind fun s => ?_
  refine (ProvS.bind (provS_lift (prov_executePhase D δ net _ _ _ fun j _ => treeProv K circuits settings j _ tree))
    fun r => ProvS.bind (provS_lift ?_) fun bad => provS_set _) s
  simp only [noMonitor]
  exact prov_pure _ _

omit [Fintype E] [DecidableEq E] in
theorem provS_secRuns (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, ProvS D δ (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count)
  | 0 => provS_pure _
  | count + 1 => by
    have rest := provS_secRuns m hm net parameter seeds dealt emu tree count
    unfold secRuns
    refine provS_get_bind fun s => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h]
      refine (ProvS.bind ?_ fun _ => rest) s
      unfold secRun
      refine provS_get_bind fun s' => ?_
      rw [ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _)]
      exact provS_treeRun D δ K circuits settings net tree s'
    · rw [ite_eq_right h]
      exact prov_pure _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem provT_tsig {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C)
    (htsig : ∀ st, cost (callCharge (HonestP TailLocal)) ((tsigOracles (fun oa => free (liftComp oa _)) d q).run st) ≤ 0) :
    ProvT D δ (tsigOracles (realLift (σ := σ)) (SeedHitProof.Dealt.hmap (realHom σ) d) q) := fun st =>
  (provS_lift (prov_ofCost D δ _ (htsig st))).of_eq
    (SeedHitProof.hom_tsigOracles (realHom σ) (fun oa => free (liftComp oa _)) d q st)

omit [Fintype E] [DecidableEq E] in
theorem provT_secOracles (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (top : TopTree) (q : TsigQuery C) :
    ProvT D δ (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu
      (SeedHitProof.Dealt.hmap (realHom A.net.State) (worldDealt₀ parameter seeds dealt top)) q) := by
  have htsig : ∀ q st, cost (callCharge (HonestP TailLocal)) ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0 :=
    Salt.cost_dealerOracles _ (fun oa h => hfree_tail oa h) parameter seeds dealt top
  unfold secOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact provT_pure _
  · dsimp only
    unfold secTreeRequest
    refine (provT_tsig D δ _ _ (htsig _)).bind fun answer => ?_
    by_cases hc : m.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      refine (provT_lift (provS_secRuns D δ K circuits settings runLimit m hm A.net
        parameter seeds dealt emu _ 1)).bind fun _ => provT_get_bind fun s => ?_
      split <;> exact provT_pure _
    · simp only [hc, ↓reduceIte]
      refine provT_get_bind fun s => ?_
      split <;> exact provT_pure _
  all_goals
    dsimp only
    unfold secSignRequest
    refine (provT_lift (provS_modify _)).bind fun _ => provT_get_bind fun s => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first
        | exact provT_tsig D δ _ _ (htsig _)
        | exact provT_pure _

omit [Fintype E] [DecidableEq E] in
theorem provS_secSigning (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    ProvS D δ (secSigning K circuits settings runLimit m D A parameter seeds dealt emu) := by
  unfold secSigning
  refine provS_get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact prov_pure _ _
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
    refine (ProvS.bind (provS_lift (prov_ofCost D δ _ (Salt.cost_dealerTree _ (fun oa h => hfree_tail oa h) _ _)))
      fun out => ?_) s
    have d₂ : dealtWith (realLift (σ := A.net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₂]
    refine ProvS.bind (fun s => ProvT.simulateQ _ (fun t => ?_) _ _ s) fun z => ?_
    · rcases t with t | q | q
      · exact provT_lift (provS_lift (prov_of_noTouch D δ [] _ (noTouch_adversary _)))
      · exact provT_secOracles D δ K circuits settings runLimit m hm A parameter seeds dealt emu _ q
      · rcases q with _ | state
        · exact provT_lift (provS_map_get _)
        · exact provT_lift (provS_modify _)
    · rcases z with ⟨forgery, st⟩
      exact (provS_lift (prov_ofCost D δ _ (Salt.cost_dealerWins _ (fun oa h => hfree_tail oa h) _ _ _ _ st
        forgery))).of_eq (hom_forgeryWins (realHom A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)

omit [Fintype E] [DecidableEq E] in
/-- `dealtRun` with no emulated run has `Prov []`. -/
theorem prov_dealtRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) :
    Prov D δ [] (dealtRun K circuits settings runLimit m D A) := by
  unfold dealtRun
  refine (prov_of_noTouch D δ [] _ ((noCall_iff _ _).2 (IsQueryBoundP.of_imp touch_tail
    (worldSeedGen_quiet D A.net)))).bind fun x => ?_
  obtain ⟨state, parameter, seeds, dealt, emu⟩ := x
  refine Prov.bind ?_ fun _ => prov_pure _ _
  rw [StateT.run'_eq]
  exact Prov.map _ ((ProvS.bind (provS_secRuns D δ K circuits settings runLimit m hm A.net parameter seeds dealt
    emu .top runLimit) fun _ => provS_secSigning D δ K circuits settings runLimit m hm A parameter seeds dealt emu) _)

variable (prims : Primitives) in
omit [Fintype E] [DecidableEq E] in
/-- The game program with the shifted salt reads is the game program with the rewritten digest
calls. -/
theorem saltProv : SaltProv K circuits settings runLimit := by
  intro D A δ
  have h := prov_dealtRun D δ K circuits settings runLimit ⟨true, fun _ => 0⟩ (fun _ => rfl) A
  unfold Prov at h
  rw [StateT.run'_eq, h, Functor.map_map]
  simp

end Rest

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.saltProv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.saltProv
