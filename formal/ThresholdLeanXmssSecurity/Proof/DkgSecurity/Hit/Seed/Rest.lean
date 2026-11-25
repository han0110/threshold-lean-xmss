import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.ZipWith
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.UpToTouch
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.IdealCoupling

/-!
# The rest of the game asks no free cell of the seed generation

With no emulated run, the rest of the game `secRest` makes no free call of `H` in the class of the
seed generation (`noCall_secRest_seedGen`). These are the cells `commit .seedGen _ _ _`,
`derive .seedGen _ _` and `sharedKeys .seedGen _` (`seedGenCell_honestIn`). The walk is the walk of
`rcost_secRest` with the charge `callCharge (HonestIn .seedGen)` and no potential.

* A real run of a tree makes no such call (`treeProgram_seedGen`), and the adversary calls only the
  counted copy.
* The dealer, its signing oracles and the win test make none (`cost_dealerTree`,
  `cost_dealerOracles`, `cost_dealerWins`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_mono)
open PFunctor.FreeM (costWith cost costWith_mono)
open ThresholdLeanXmssSecurity.DkgSecurityProof (RCost RCostT)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- A free call of `H` at a cell of the seed generation, a commitment, a derive cell or a shared key
cell. -/
def SeedGenCell : (WorldSpec C).Domain → Prop := fun t =>
  ∃ q, t = .inr (.inr (.inl q)) ∧ isSeedGenQuery q = true

theorem seedGenCell_honestIn (t : (WorldSpec C).Domain) (h : SeedGenCell t) : HonestIn .seedGen t := by
  obtain ⟨q, rfl, hq⟩ := h
  cases q <;> first
    | (simp [isSeedGenQuery] at hq; done)
    | (revert hq; cases ‹Phase› <;> simp [isSeedGenQuery, HonestIn, InClass, queryClass, phaseClass])

theorem cost_seedGen_free {α : Type} (oa : OracleComp (RoSpec C) α)
    (h : NoCall (DigestBudgets.RoIn .seedGen) oa) :
    cost (callCharge (HonestIn (C := C) .seedGen)) (DkgCompletenessProof.freeHom oa) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2
    (DigestBudgets.free_liftComp_bound .seedGen _ (fun _ => Iff.rfl) oa 0 ((noCall_iff _ _).1 h))

theorem cost_seedGen_adversary (t : (LocalSpec C).Domain) :
    cost (callCharge (HonestIn (C := C) .seedGen)) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2 (DigestBudgets.honestIn_adversary .seedGen _)

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

omit [Fintype E] [DecidableEq E] in
theorem cost_treeRun_seedGen (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State) :
    costWith (callCharge (HonestIn .seedGen)) ((treeRun K circuits settings noMonitor D net tree).run s)
      (fun _ => 0) ≤ 0 := by
  unfold treeRun
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  have hrun : IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
      fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestIn .seedGen) 0 := by
    have h := DigestBudgets.executePhase_bound .seedGen D net (treeFuel circuits settings) s.adversary
      (fun i => treeProgram K circuits settings i (s.operators i) tree) (fun _ => 0)
      fun j _ => treeProgram_seedGen K circuits settings j _ tree
    simpa using h
  refine (?_ : RCost (callCharge (HonestIn .seedGen)) _ (fun _ _ => 0) fun _ => 0) s
  refine RCost.bind (K := fun _ _ => 0)
    ((RCost.lift ((cost_callCharge_le_iff _ _ _).2 hrun) _).mono (fun _ _ => le_rfl) fun _ => by simp) fun r => ?_
  obtain ⟨state, outputs⟩ := r
  refine RCost.bind (K := fun _ _ => 0)
    ((RCost.lift (cost_pure_le _ _ 0) _).mono (fun _ _ => le_rfl) fun _ => by simp) fun bad => ?_
  refine RCost.bind (K := fun _ _ => 0)
    ((RCost.lift ((cost_callCharge_le_iff _ _ _).2 (FirstCounts.voteRound_honestIn .seedGen (by decide) D net state _
      fun _ _ => queryClass_map_treeVote)) _).mono (fun _ _ => le_rfl) fun _ => by simp) fun v => ?_
  exact (RCost.set _ _).mono (fun _ _ => le_rfl) fun _ => le_rfl

omit [Fintype E] [DecidableEq E] in
theorem rcost_secRuns_seedGen (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, RCost (callCharge (HonestIn .seedGen))
      (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count) (fun _ _ => 0) fun _ => 0
  | 0 => RCost.pure _ _
  | count + 1 => by
    have rest := rcost_secRuns_seedGen m hm net parameter seeds dealt emu tree count
    unfold secRuns
    refine RCost.get_bind fun s => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h, StateT.run_bind, PFunctor.FreeM.costWith_bind']
      refine le_trans (costWith_mono _ fun p => rest p.2) ?_
      unfold secRun
      rw [StateT.run_bind, StateT.run_get, pure_bind, ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _)]
      exact cost_treeRun_seedGen K circuits settings D net tree s
    · rw [ite_eq_right h]
      exact le_rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rcostT_tsig_seedGen {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C)
    (htsig : ∀ st, cost (callCharge (HonestIn .seedGen)) ((tsigOracles (fun oa => free (liftComp oa _)) d q).run st) ≤ 0) :
    RCostT (callCharge (HonestIn .seedGen))
      (tsigOracles (realLift (σ := σ)) (SeedHitProof.Dealt.hmap (realHom σ) d) q)
      (fun _ _ => 0) (fun _ => 0 + 0) := fun st =>
  (RCost.lift (htsig st) fun _ => 0).of_eq
    (SeedHitProof.hom_tsigOracles (realHom σ) (fun oa => free (liftComp oa _)) d q st)

omit [Fintype E] [DecidableEq E] in
theorem rcostT_secOracles_seedGen (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (top : TopTree) (q : TsigQuery C) :
    RCostT (callCharge (HonestIn .seedGen))
      (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (realHom A.net.State) (worldDealt₀ parameter seeds dealt top)) q)
      (fun _ _ => 0) (fun _ => 0 + 0) := by
  have htsig : ∀ q st, cost (callCharge (HonestIn .seedGen)) ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0 :=
    cost_dealerOracles _ (fun oa h => cost_seedGen_free oa h) parameter seeds dealt top
  unfold secOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact (RCostT.pure _ _).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm
  · dsimp only
    unfold secTreeRequest
    refine RCostT.bind (K := fun _ _ => 0)
      ((rcostT_tsig_seedGen _ _ (htsig _)).mono (fun _ _ => le_rfl) fun _ => le_rfl) fun answer => ?_
    have tail : RCostT (callCharge (HonestIn .seedGen)) (StateT.lift get >>= fun s : RealState C A.net.State =>
        match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => pure (some (tree, ρ))
        | _, _ => pure none : StateT (TsigState C) (RealM C A.net.State) _)
        (fun _ _ => 0) (fun _ => 0) := by
      refine RCostT.get_bind fun s st => ?_
      split <;> exact le_rfl
    by_cases hc : m.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      exact RCostT.bind (RCostT.lift (rcost_secRuns_seedGen K circuits settings runLimit D m hm A.net
        parameter seeds dealt emu _ 1)) fun _ => tail
    · simp only [hc, ↓reduceIte]
      exact tail
  all_goals
    dsimp only
    unfold secSignRequest
    refine RCostT.bind (K := fun _ _ => 0)
      ((RCostT.lift (RCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm) fun _ => ?_
    refine RCostT.get_bind fun s st => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first
        | exact ((rcostT_tsig_seedGen _ _ (htsig _)) st s).trans (le_of_eq (zero_add _))
        | exact le_rfl

omit [Fintype E] [DecidableEq E] in
theorem rcost_secSigning_seedGen (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    RCost (callCharge (HonestIn .seedGen)) (secSigning K circuits settings runLimit m D A parameter seeds dealt emu)
      (fun _ _ => 0) (fun _ => 0) := by
  unfold secSigning
  refine RCost.get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact zero_le
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
    refine (?_ : RCost (callCharge (HonestIn .seedGen)) _ (fun _ _ => 0) fun _ => 0) s
    refine RCost.bind (K := fun _ _ => 0)
      ((RCost.lift (cost_dealerTree _ (fun oa h => cost_seedGen_free oa h) _ _) _).mono (fun _ _ => le_rfl)
        fun _ => le_of_eq (zero_add _)) fun out => ?_
    have d₂ : dealtWith (realLift (σ := A.net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₂]
    refine RCost.bind (K := fun _ _ => 0)
      (((RCostT.simulateQ (c := callCharge (HonestIn .seedGen)) _ (fun _ => 0) (fun _ => 0) (fun t => ?_) _) _).mono
        (fun _ _ => le_rfl) fun s => by simpa using cost_zero_le _) fun p => ?_
    · rcases t with t | q | q
      · exact RCostT.lift ((RCost.lift (cost_seedGen_adversary t) _).mono (fun _ _ => le_rfl) fun _ => le_rfl)
      · exact rcostT_secOracles_seedGen K circuits settings runLimit D m hm A parameter seeds dealt emu _ q
      · rcases q with _ | state
        · exact (RCostT.lift (RCost.map_get _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
        · exact (RCostT.lift (RCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
    · rcases p with ⟨forgery, st⟩
      exact ((RCost.lift (cost_dealerWins _ (fun oa h => cost_seedGen_free oa h) _ _ _ _ st forgery) fun _ => 0).of_eq
        (hom_forgeryWins (realHom A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)).mono
          (fun _ _ => le_rfl) fun _ => by simp

omit [Fintype E] [DecidableEq E] in
/-- With no emulated run, the rest of the game makes no free call in the class of the seed generation,
from each state. -/
theorem noCall_secRest_seedGen (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (st : RealState C A.net.State) :
    NoCall (HonestIn .seedGen) ((secRest K circuits settings runLimit m D A parameter seeds dealt emu).run' st) := by
  have h : RCost (callCharge (HonestIn .seedGen)) (secRest K circuits settings runLimit m D A parameter seeds dealt emu)
      (fun _ _ => 0) (fun _ => 0) := by
    unfold secRest
    refine RCost.get_bind fun s => ?_
    refine (RCost.bind (K := fun _ _ => 0) (k := fun _ _ => (0 : ℕ∞))
      ((RCost.lift ((cost_callCharge_le_iff _ _ _).2 (FirstCounts.voteRound_honestIn .seedGen (by decide) D A.net
        s.adversary (fun i => ((s.operators i).keys).map seedVote) fun _ _ => queryClass_map_seedVote))
          fun _ => 0).mono (Φ' := fun _ => (0 : ℕ∞)) (fun _ _ => le_rfl) fun _ => by simp)
      fun v => ?_) s
    obtain ⟨state, ok⟩ := v
    refine RCost.bind ((RCost.set _ (fun _ _ => 0)).mono (fun _ _ => le_rfl) fun _ => le_rfl) fun _ => ?_
    exact RCost.bind (K := fun _ _ => 0)
      (rcost_secRuns_seedGen K circuits settings runLimit D m hm A.net parameter seeds dealt (committed ok emu) .top
        runLimit)
      fun _ => rcost_secSigning_seedGen K circuits settings runLimit D m hm A parameter seeds dealt (committed ok emu)
  rw [noCall_iff, ← cost_callCharge_le_iff, StateT.run'_eq, cost_map_eq]
  have h0 := h st
  rw [show (fun p : Bool × RealState C A.net.State => (fun (_ : Bool) (_ : RealState C A.net.State) => (0 : ℕ∞)) p.1 p.2) =
    fun _ => 0 from rfl] at h0
  simpa [cost] using h0

omit [Fintype E] [DecidableEq E] in
/-- The rest of the game asks no free cell of the seed generation. -/
theorem noCall_secRest_seedGenCell (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (st : RealState C A.net.State) :
    NoCall SeedGenCell ((secRest K circuits settings runLimit m D A parameter seeds dealt emu).run' st) :=
  noCall_mono _ seedGenCell_honestIn (noCall_secRest_seedGen K circuits settings runLimit D m hm A parameter seeds
    dealt emu st)

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.noCall_secRest_seedGenCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.noCall_secRest_seedGenCell
