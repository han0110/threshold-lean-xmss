import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Provenance
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Count

/-!
# The calls of the game that can make a digest cell

`callCell t` is the digest cell that the call `t` asks or programs, namely the cell of a counted call
of `H`, of a free call of `H` or of a programming call. `ProgDigest` is a programming call on a digest
cell. `dealtRun` with no emulated run makes no such call (`noProgDigest_dealtRun`). The seed generation
programs only `.derive` cells, and the rest of the game makes no programming call. So the game makes at
most `q + gameBatches * n * termCount C` calls with a digest cell (`charged_dealtRun`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (HonestP)
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit (NoProg NoProgT noProgT_simulateQ)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_mapM
  noCall_mono)
open PFunctor.FreeM (cost)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The digest cell that a call asks or programs. -/
def callCell : (WorldSpec C).Domain → Option (List Bit × HashOutput)
  | .inl (.inl (.inr (.inl (.digest salt history)))) => some (salt, history)
  | .inl (.inr (.digest salt history, _)) => some (salt, history)
  | .inr (.inr (.inl (.digest salt history))) => some (salt, history)
  | _ => none

/-- A call with a digest cell. -/
def Charged (t : (WorldSpec C).Domain) : Prop := callCell t ≠ none

/-- A programming call on a digest cell. -/
def ProgDigest : (WorldSpec C).Domain → Prop
  | .inl (.inr (.digest _ _, _)) => True
  | _ => False

theorem charged_cases (t : (WorldSpec C).Domain) (h : Charged t) :
    (Logged t ∨ HonestP DigestCall t) ∨ ProgDigest t := by
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  all_goals try exact absurd rfl h
  · exact Or.inl (Or.inl trivial)
  · cases q <;> first | exact absurd rfl h | exact Or.inr trivial
  · cases q <;> first | exact absurd rfl h | exact Or.inl (Or.inr ⟨_, _, rfl⟩)

/-! ## No programming call on a digest cell -/

section Game

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

theorem noProgram_ofCost {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : cost (callCharge WorldProgramQuery) oa ≤ 0) : NoCall WorldProgramQuery oa :=
  (noCall_iff _ _).2 ((cost_callCharge_le_iff _ _ 0).1 h)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProg_of_eq {σ α : Type} {m m' : RealM C σ α} (h : NoProg m) (e : m = m') : NoProg m' := e ▸ h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgT_pure {σ α : Type} (a : α) : NoProgT (pure a : StateT (TsigState C) (RealM C σ) α) :=
  fun _ => UsedHit.NoProg.pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgT_bind {σ α β : Type} {m : StateT (TsigState C) (RealM C σ) α}
    {f : α → StateT (TsigState C) (RealM C σ) β} (h : NoProgT m) (hf : ∀ a, NoProgT (f a)) : NoProgT (m >>= f) :=
  fun t => by
    rw [StateT.run_bind]
    exact (h t).bind fun p => hf p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgT_get_bind {σ α : Type} {f : RealState C σ → StateT (TsigState C) (RealM C σ) α}
    (h : ∀ s, NoProgT (f s)) : NoProgT (StateT.lift get >>= f) :=
  noProgT_bind (UsedHit.NoProgT.lift UsedHit.NoProg.get) h

omit [Fintype E] [DecidableEq E] in
theorem noProg_secRuns (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, NoProg (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count)
  | 0 => UsedHit.NoProg.pure _
  | count + 1 => by
    unfold secRuns
    refine UsedHit.NoProg.get.bind fun s => ?_
    split_ifs
    · refine UsedHit.NoProg.bind ?_ fun _ => noProg_secRuns m hm net parameter seeds dealt emu tree count
      unfold secRun
      refine UsedHit.NoProg.get.bind fun s' => ?_
      rw [ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _)]
      exact noProg_treeRun K circuits settings D net tree
    · exact UsedHit.NoProg.pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgT_tsig {σ : Type} (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (top : TopTree) (q : TsigQuery C) :
    NoProgT (tsigOracles (realLift (σ := σ))
      (SeedHitProof.Dealt.hmap (realHom σ) (worldDealt₀ parameter seeds dealt top)) q) := fun st =>
  noProg_of_eq (UsedHit.NoProg.lift (noProgram_ofCost _ (DkgSecurityProof.cost_dealerOracles _
    (fun oa _ => cost_program_free oa) parameter seeds dealt top q st)))
    (SeedHitProof.hom_tsigOracles (realHom σ) (fun oa => free (liftComp oa _)) _ q st)

omit [Fintype E] [DecidableEq E] in
theorem noProgT_secOracles (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (top : TopTree) (q : TsigQuery C) :
    NoProgT (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu
      (SeedHitProof.Dealt.hmap (realHom A.net.State) (worldDealt₀ parameter seeds dealt top)) q) := by
  unfold secOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact noProgT_pure _
  · dsimp only
    unfold secTreeRequest
    refine noProgT_bind (noProgT_tsig _ _ _ _ _) fun answer => ?_
    by_cases hc : m.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      refine noProgT_bind (UsedHit.NoProgT.lift (noProg_secRuns K circuits settings runLimit D m hm A.net
        parameter seeds dealt emu _ 1)) fun _ => noProgT_get_bind fun s => ?_
      split <;> exact noProgT_pure _
    · simp only [hc, ↓reduceIte]
      refine noProgT_get_bind fun s => ?_
      split <;> exact noProgT_pure _
  all_goals
    dsimp only
    unfold secSignRequest
    refine noProgT_bind (UsedHit.NoProgT.lift (UsedHit.NoProg.modify _)) fun _ => noProgT_get_bind fun s => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first
        | exact noProgT_tsig _ _ _ _ _
        | exact noProgT_pure _

omit [Fintype E] [DecidableEq E] in
theorem noProg_secSigning (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    NoProg (secSigning K circuits settings runLimit m D A parameter seeds dealt emu) := by
  unfold secSigning
  refine UsedHit.NoProg.get.bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact UsedHit.NoProg.pure _
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
    refine UsedHit.NoProg.bind (UsedHit.NoProg.lift (noProgram_ofCost _ (DkgSecurityProof.cost_dealerTree _
      (fun oa _ => cost_program_free oa) _ _))) fun out => ?_
    have d₂ : dealtWith (realLift (σ := A.net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₂]
    refine UsedHit.NoProg.bind (fun s => noProgT_simulateQ _ (fun t => ?_) _ _ s) fun z => ?_
    · rcases t with t | q | q
      · exact UsedHit.NoProgT.lift (UsedHit.NoProg.lift (Collision.noProgram_adversary _))
      · exact noProgT_secOracles K circuits settings runLimit D m hm A parameter seeds dealt emu _ q
      · rcases q with _ | state
        · exact UsedHit.NoProgT.lift (fun _ => noCall_pure _ _)
        · exact UsedHit.NoProgT.lift (UsedHit.NoProg.modify _)
    · rcases z with ⟨forgery, st⟩
      exact noProg_of_eq (UsedHit.NoProg.lift (noProgram_ofCost _ (DkgSecurityProof.cost_dealerWins _
        (fun oa _ => cost_program_free oa) _ _ _ _ st forgery)))
        (hom_forgeryWins (realHom A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgDigest_program (q : Query C) (hq : ∀ salt history, q ≠ .digest salt history) (value : HashOutput) :
    NoCall ProgDigest (ThresholdLeanXmss.program q value) := by
  unfold ThresholdLeanXmss.program counted
  erw [simulateQ_query]
  rw [noCall_iff]
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
  refine (noCall_iff _ _).1 (SigningSelectionProof.noCall_query _ _ ?_)
  cases q <;> first | exact not_false | exact absurd rfl (hq _ _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem progDigest_program (t : (WorldSpec C).Domain) (h : ProgDigest t) : WorldProgramQuery t := by
  rcases t with ((_ | _ | _) | _) | _ <;> first | exact h.elim | trivial

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The seed generation of the simulator programs no digest cell. -/
theorem noProgDigest_worldSeedGen (net : Adversary C E Unit PEmpty PEmpty) :
    NoCall ProgDigest (worldSeedGen D net) := by
  have np : ∀ {α : Type} {oa : OracleComp (WorldSpec C) α}, NoCall WorldProgramQuery oa → NoCall ProgDigest oa :=
    fun h => noCall_mono _ progDigest_program h
  unfold worldSeedGen
  refine noCall_bind _ (np (noProgram_observe _)) fun p => ?_
  obtain ⟨state, early⟩ := p
  refine noCall_bind _ (np (Collision.noProgram_free _)) fun x => ?_
  obtain ⟨parameter, seeds, dealt⟩ := x
  refine noCall_bind _ (np (Collision.noProgram_free _)) fun parts => ?_
  refine noCall_bind _ (np (noProgram_startSteps D _)) fun steps => ?_
  refine noCall_bind _ (np (noProgram_stepRound_observed D net state steps)) fun r => ?_
  obtain ⟨⟨state', steps', sent⟩, calls⟩ := r
  refine noCall_bind _ (np (Collision.noProgram_free _)) fun high => ?_
  refine noCall_bind _ (noProgDigest_program _ (fun _ _ h => by cases h) _) fun _ => ?_
  refine noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ => ?_
  · split
    · exact noProgDigest_program _ (fun _ _ h => by cases h) _
    · exact noCall_pure _ _
  refine noCall_bind _ (noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_) fun _ => ?_
  · split
    · exact noProgDigest_program _ (fun _ _ h => by cases h) _
    · exact noCall_pure _ _
  exact noCall_bind _ (np (noProgram_executeRounds_observed D net _ state' steps')) fun _ => noCall_pure _ _

omit [Fintype E] [DecidableEq E] in
/-- With no emulated run, the rest of a game, with the vote of the seed generation, makes no
programming call. -/
theorem noProg_secRest (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    NoProg (secRest K circuits settings runLimit m D A parameter seeds dealt emu) := by
  unfold secRest
  refine UsedHit.NoProg.get.bind fun s => (UsedHit.NoProg.lift (Collision.noProgram_voteRound D A.net _ _)).bind
    fun v => ?_
  obtain ⟨state', ok⟩ := v
  exact (UsedHit.NoProg.set _).bind fun _ => UsedHit.NoProg.bind (noProg_secRuns K circuits settings runLimit D m hm
    A.net parameter seeds dealt (committed ok emu) .top runLimit) fun _ => noProg_secSigning K circuits settings
      runLimit D m hm A parameter seeds dealt (committed ok emu)

omit [Fintype E] [DecidableEq E] in
/-- `dealtRun` with no emulated run programs no digest cell. -/
theorem noProgDigest_dealtRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) :
    NoCall ProgDigest (dealtRun K circuits settings runLimit m D A) := by
  unfold dealtRun
  refine noCall_bind _ (noProgDigest_worldSeedGen D A.net) fun x => ?_
  obtain ⟨state, parameter, seeds, dealt, emu⟩ := x
  refine noCall_bind _ ?_ fun _ => noCall_pure _ _
  rw [StateT.run'_eq]
  refine SigningSelectionProof.noCall_map _ _ (noCall_mono _ progDigest_program ?_)
  exact noProg_secRest K circuits settings runLimit D m hm A parameter seeds dealt emu _

omit [Fintype E] [DecidableEq E] in
/-- `dealtRun` with no emulated run makes at most `q + gameBatches * n * termCount C` calls with a
digest cell for an adversary with the budget `q`. -/
theorem charged_dealtRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) :
    IsQueryBoundP (dealtRun K circuits settings runLimit m D A) Charged
      (q + gameBatches settings runLimit * C.n * termCount C) := by
  have h₁ := FirstCounts.isQueryBoundP_add (r := fun t => Logged t ∨ HonestP DigestCall t) (fun _ h => h) _ _ _
    (LoggedCount.logged_dealtRun K circuits settings runLimit D m hm A q bounded)
    (digest_dealtRun K circuits settings runLimit D m hm A)
  exact (FirstCounts.isQueryBoundP_add charged_cases _ _ _ h₁
    ((noCall_iff _ _).1 (noProgDigest_dealtRun K circuits settings runLimit D m hm A))).mono (by omega)

end Game

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.charged_dealtRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.charged_dealtRun
