import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Glue
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.RestCost
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.ClassFacts
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.DealtAgree

/-!
# The calls of the program of the shared rest

Two instances of `cost_sharedProgram_le`.

* With the charge of a programming call, every piece costs nothing, so the program of the shared
  rest makes no programming call (`sharedProgramNoProgram`).
* With the charge of a call of the class of the seed generation, a real run costs `treeFuel * step`
  and `forge` costs at most its budget `forge` (`sharedProgramClassBound`).

Then `sharedSeedReal`, `sharedSeedIdeal` and `sharedSeedBound` are the hops `SharedSeedReal`,
`SharedSeedIdeal` and `SharedSeedBound`, with `SharedDealtAgree` from `sharedDealtAgree_holds`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open PFunctor.FreeM (costWith cost)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## Charges -/

theorem cost_zero_le {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (oa : OracleComp spec α) :
    cost (fun _ => (0 : ℕ∞)) oa ≤ 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact cost_pure_le _ _ _
  | query_bind t k ih =>
    rw [cost, costWith_query_bind, zero_add]
    exact iSup_le ih

theorem forgeCharge_zero {σ : Type} : forgeCharge (C := C) (σ := σ) (fun _ => 0) = fun _ => 0 := by
  funext t
  rcases t with t | t <;> rfl

theorem peekCharge_program : peekCharge (callCharge (WorldProgramQuery (C := C))) = callCharge PeekProgramQuery := by
  funext t
  rcases t with t | t
  · rfl
  · simp [peekCharge, callCharge, PeekProgramQuery]

theorem inClass_of_isSeedGenQuery (q : Query C) (h : isSeedGenQuery q = true) :
    InClass .seedGen (.inr (.inl q) : (LocalSpec C).Domain) := by
  cases q <;> (try cases ‹Phase›) <;> simp_all [isSeedGenQuery, InClass, queryClass, phaseClass]

theorem classCharge_le (t : (PeekSpec C).Domain) : classCharge t ≤ peekCharge (callCharge ClassCall) t := by
  rcases t with (((x | p) | x) | u)
  · rcases x with n | q | y
    · exact zero_le
    · by_cases h : isSeedGenQuery q = true
      · simp [classCharge, peekCharge, callCharge, ClassCall, h, inClass_of_isSeedGenQuery q h]
      · simp [classCharge, h]
    · exact zero_le
  · exact zero_le
  · rcases x with n | q | y
    · exact zero_le
    · by_cases h : isSeedGenQuery q = true
      · simp [classCharge, peekCharge, callCharge, ClassCall, h, inClass_of_isSeedGenQuery q h]
      · simp [classCharge, h]
    · exact zero_le
  · exact zero_le

theorem callCharge_inClass_le_ownCost (t : (LocalSpec C).Domain) :
    callCharge (InClass .seedGen) t ≤ (ownCost t : ℕ∞) := by
  rcases t with n | q | y
  · simp [callCharge, InClass]
  · unfold callCharge ownCost
    split_ifs <;> simp
  · simp [callCharge, InClass]

theorem forgeCharge_le_forgeCost {σ : Type} (t : (LocalSpec C + (TsigSpec C + StateSpec σ)).Domain) :
    forgeCharge (callCharge (InClass .seedGen)) t ≤ (forgeCost t : ℕ∞) := by
  rcases t with t | t
  · show ((if InClass .seedGen t then 1 else 0 : ℕ) : ℕ∞) ≤ (forgeCost (.inl t : (LocalSpec C + (TsigSpec C +
      StateSpec σ)).Domain) : ℕ∞)
    split_ifs with h
    · exact_mod_cast one_le_forgeCost (c := .seedGen) (t := (.inl t : (LocalSpec C + (TsigSpec C + StateSpec σ)).Domain)) h
    · simp
  · exact zero_le

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## No programming call -/

omit [Fintype E] [DecidableEq E] in
/-- The program of the shared rest makes no programming query. -/
theorem sharedProgramNoProgram : SharedProgramNoProgram K circuits settings runLimit := by
  intro D A state keys
  have h := cost_sharedProgram_le K circuits settings runLimit (callCharge WorldProgramQuery) (fun _ => 0) D A 0
    (fun state input _ => (cost_callCharge_le_iff _ _ 0).2
      ((SigningSelectionProof.noCall_iff _ _).1 (Collision.noProgram_voteRound D A.net state input)))
    (fun s tree => by simpa using cost_program_run K circuits settings D A.net s tree) (fun _ => 0)
    cost_program_adversary 0 (fun pk top => by rw [forgeCharge_zero]; exact cost_zero_le _)
    (cost_dealerTree _ fun oa _ => cost_program_free oa) (cost_dealerOracles _ fun oa _ => cost_program_free oa)
    (cost_dealerWins _ fun oa _ => cost_program_free oa) state keys
  have hrem : FirstCounts.remaining runLimit (fun _ => 0) (fun _ => 0) = 0 := by
    simp [FirstCounts.remaining]
  rw [peekCharge_program, hrem, Nat.cast_zero, add_zero, add_zero] at h
  have hb := (cost_callCharge_le_iff PeekProgramQuery _ 0).1 (by simpa using h)
  exact (isQueryBoundP_zero_iff _ _).1 ((isQueryBoundP_congr_pred fun _ => not_not).2 hb)

/-! ## The calls of the class of the seed generation -/

omit [Fintype E] [DecidableEq E] in
/-- The potential of the runs at the start and the vote of the seed generation are the bound of the
rounds after the seed generation. -/
theorem remaining_start (step : ℕ) :
    step + FirstCounts.remaining runLimit (fun _ => treeFuel circuits settings * step + step) (fun _ => 0) =
      (dkgTsigRounds circuits settings runLimit - setupRounds) * step := by
  simp only [FirstCounts.remaining, Nat.sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, dkgTsigRounds, Nat.add_sub_cancel_left]
  ring

omit [Fintype E] [DecidableEq E] in
/-- The calls of the class of the seed generation in the program of the shared rest are the calls of
the rounds of `A.net` after the seed generation and the calls of `A.forge`. -/
theorem sharedProgramClassBound : SharedProgramClassBound K circuits settings runLimit := by
  intro D A step forge hr hf state keys
  have hround : ∀ state sent, IsQueryBoundP (A.net.round state sent) (InClass .seedGen) step := fun state sent =>
    (cost_callCharge_le_iff _ _ _).1 ((PFunctor.FreeM.cost_mono callCharge_inClass_le_ownCost _).trans
      ((queryCostAtMost_iff_cost_le _ _ _).1 (hr state sent)))
  have hforge : ∀ pk top, cost (forgeCharge (callCharge (InClass .seedGen))) (A.forge pk top) ≤ (forge : ℕ∞) :=
    fun pk top => (PFunctor.FreeM.cost_mono forgeCharge_le_forgeCost _).trans
      ((queryCostAtMost_iff_cost_le _ _ _).1 (hf pk top))
  have hvote : ∀ state (input : C.Party → Option (Query C)), (∀ j q, input j = some q → queryClass q = .vote) →
      cost (callCharge ClassCall) (voteRound worldRoles D A.net state input) ≤ (step : ℕ∞) :=
    fun state input hin => (cost_callCharge_le_iff _ _ _).2 (Vote.voteRound_isQueryBoundP D A.net state input
      ClassCall step (fun state sent => hround state sent) fun j q hq => by
        have hc := hin j q hq
        simp only [ClassCall, InClass]
        split <;> simp_all)
  have h := cost_sharedProgram_le K circuits settings runLimit (callCharge ClassCall)
    (fun _ => treeFuel circuits settings * step + step) D A step hvote
    (fun s tree => by
      push_cast
      exact add_le_add (cost_class_run K circuits settings D A.net step hround s tree) le_rfl)
    (callCharge (InClass .seedGen))
    cost_class_adversary forge hforge (cost_dealerTree _ cost_class_free) (cost_dealerOracles _ cost_class_free)
    (cost_dealerWins _ cost_class_free) state keys
  rw [← remaining_start]
  refine (PFunctor.FreeM.cost_mono classCharge_le _).trans (h.trans (le_of_eq ?_))
  push_cast
  ring

/-! ## The hops -/

variable (prims : Primitives)

omit [Fintype E] [DecidableEq E] in
/-- The real end of the seed generation claim with the shared event. -/
theorem sharedSeedReal : SharedSeedReal prims K circuits settings runLimit :=
  sharedSeedReal_of_rest prims K circuits settings runLimit (sharedProgramNoProgram K circuits settings runLimit)
    (sharedRestTable prims K circuits settings runLimit) (sharedRestLogged prims K circuits settings runLimit)

omit [Fintype E] [DecidableEq E] in
/-- The budget of the table adversary with the distinguisher of the shared event. -/
theorem sharedSeedBound : SharedSeedBound prims K circuits settings runLimit :=
  sharedSeedBound_of_rest prims K circuits settings runLimit (sharedRestTable prims K circuits settings runLimit)
    (sharedProgramClassBound K circuits settings runLimit)

omit [Fintype E] [DecidableEq E] in
/-- The proof of `SharedDealtAgree`. -/
theorem sharedDealtAgree : SharedDealtAgree prims K circuits settings runLimit := fun D A =>
  sharedDealtAgree_holds K circuits settings runLimit prims D A

omit [Fintype E] [DecidableEq E] in
/-- The ideal end of the seed generation claim with the shared event. -/
theorem sharedSeedIdeal : SharedSeedIdeal prims K circuits settings runLimit :=
  sharedSeedIdeal_of_rest prims K circuits settings runLimit (sharedProgramNoProgram K circuits settings runLimit)
    (sharedRestTable prims K circuits settings runLimit) (sharedRestLogged prims K circuits settings runLimit)
    (sharedDealtAgree K circuits settings runLimit prims)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedReal

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedBound

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedIdeal
