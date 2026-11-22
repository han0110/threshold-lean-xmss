import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Bottom
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopCosts

/-!
# The cost of the reduction of a bottom slot

`forgeWalk_adds` bounds the walk of `forge` up to the request of the run of slot `j`. The potential is
the number of bottom runs that remain before that run. `resumeAfter_adds` bounds the game after the
run with the potential `remaining` of the runs that remain. `deadRun_adds` bounds a run with an
honest operator without keys or top tree by one PRSS setup. `bottomSlotPartCosts` proves
`BottomSlotPartCosts`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

open SetupBudgets DigestBudgets FirstCounts
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

/-! ## The bottom runs -/

section Runs

/-- The runs of all bottom trees. -/
def bottomRuns (runs : Tree → ℕ) : ℕ := ∑ b : Fin (2 ^ layerHeight), runs (.bottom b)

theorem fixedSlot_bottom_eq (runLimit : ℕ) (runs : Tree → ℕ) (b : Fin (2 ^ layerHeight)) :
    fixedSlot runLimit runs (.bottom b) = runLimit + 2 * bottomRuns runs := by
  simp only [fixedSlot, treeSetups, bottomRuns, Finset.mul_sum, Nat.mul_comm]

theorem bottomRuns_update (runs : Tree → ℕ) (b : Fin (2 ^ layerHeight)) :
    bottomRuns (Function.update runs (.bottom b) (runs (.bottom b) + 1)) = bottomRuns runs + 1 := by
  have h : ∀ b', Function.update runs (.bottom b) (runs (.bottom b) + 1) (.bottom b') =
      runs (.bottom b') + if b' = b then 1 else 0 := by
    intro b'
    by_cases hb : b' = b
    · subst hb
      simp
    · simp [hb]
  simp only [bottomRuns, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end Runs

/-! ## The calls of the class of one operator in a bottom run -/

section Operator

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem batchesWith_classBound (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (jobs : List Job) :
    StateBound .prssSetup (batchesWith K circuits settings i keys prss jobs) 0 := by
  unfold batchesWith
  refine StateBound.bind_zero' ((StateBound.mapM _ 0 (fun batch => ?_) _).mono (by simp)) fun _ => StateBound.pure _
  unfold realBatch
  refine StateBound.zero_bind StateBound.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine StateBound.zero_bind (StateBound.lift_zero ((ClassBound.mapM _ 0
    (fun job => inputShares_bound _ (by decide) job) _).mono (by simp))) fun inputs => ?_
  refine StateBound.bind_zero' (StateBound.lift ((runJobs_bound (c := .prssSetup) K _ (by decide) (by decide)
    _ _ _ _).mono (by simp [digestCost, copyCost]))) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact StateBound.bind_zero (StateBound.set _) fun _ => StateBound.pure _

theorem firstAfter_classBound (i : C.Party) (keys : Keys C) (b : Fin (2 ^ layerHeight)) (prss : PrssKeys C) :
    StateBound .prssSetup (firstAfter K circuits settings i keys b prss) 0 := by
  unfold firstAfter
  refine StateBound.zero_bind (batchesWith_classBound K circuits settings i keys prss _) fun o => ?_
  rcases o with _ | outputs
  · exact StateBound.pure _
  dsimp only
  generalize merkleNode keys.parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val = node
  refine StateBound.zero_bind (lift_tweakable_bound (by decide) node) fun root => ?_
  refine StateBound.zero_bind (lift_tweakable_bound (by decide) _) fun base => ?_
  refine StateBound.zero_bind (lift_tweakable_bound (by decide) _) fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩
  · exact StateBound.pure _
  · exact StateBound.pure _

theorem secondAfter_classBound (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (prss : PrssKeys C) :
    StateBound .prssSetup (secondAfter K circuits settings i keys top b x prss) 0 := by
  unfold secondAfter
  refine StateBound.zero_bind (batchesWith_classBound K circuits settings i keys prss _) fun o => ?_
  rcases o with _ | values
  · exact StateBound.pure _
  dsimp only
  refine StateBound.zero_bind (lift_tweakable_bound (by decide) _) fun path => ?_
  refine StateBound.zero_bind (lift_tweakable_bound (by decide) _) fun topRoot => ?_
  split_ifs
  · exact StateBound.pure _
  · exact StateBound.pure _

theorem inClass_imp (t : (LocalSpec C).Domain) (h : InClass (C := C) .prssSetup t) : InClass .prssSetup t := h

/-- The head of a bottom run makes the calls of the class of one PRSS setup. -/
theorem headWith_classBound (D : C.Coalition) (fresh : Option (FreshKeys C)) (i : C.Party)
    (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) :
    PBound (InClass (C := C) .prssSetup) (headWith K circuits settings D fresh i operator b)
      (4 * C.n + termCount C) := by
  unfold headWith
  split
  · refine (PBound.bind (prssSetup_classBound i) (m := 0) fun prss => ?_).mono (Nat.add_zero _).le
    refine (PBound.bind (m := 0) (PBound.of_class inClass_imp (firstAfter_classBound K circuits settings _ _ _ _ _))
      fun p => ?_).mono (Nat.zero_add _).le
    rcases p with ⟨_ | x, st⟩
    · exact isQueryBoundP_pure _ _ _
    · exact PBound.pure _
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

/-- The tail of a bottom run makes the calls of the class of one PRSS setup. -/
theorem bottomTail_classBound (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (r : (List (List Bit) × Digest × Randomizer × Encoding) × (ℕ × ℕ)) :
    PBound (InClass (C := C) .prssSetup) (CheckTiming.bottomTail K circuits settings i operator b r)
      (4 * C.n + termCount C) := by
  unfold CheckTiming.bottomTail
  split
  · refine (PBound.bind (m := 0) ?_ fun p => ?_).mono (Nat.add_zero _).le
    · unfold CheckTiming.secondPart
      refine PState.bind_le (ceremonyRun_pbound K circuits settings inClass_imp _ prssSetup_classBound i _ _)
        (m := 0) (fun o => ?_) (Nat.add_zero _).le _
      rcases o with _ | values
      · exact PState.pure _
      dsimp only
      refine PState.of_class inClass_imp ?_
      refine StateBound.zero_bind (lift_tweakable_bound (by decide) _) fun path => ?_
      refine StateBound.zero_bind (lift_tweakable_bound (by decide) _) fun topRoot => ?_
      split_ifs
      · exact StateBound.pure _
      · exact StateBound.pure _
    · rcases p with ⟨_ | out, st⟩
      · exact isQueryBoundP_pure _ _ _
      · exact PBound.pure _
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

/-- The rest of a bottom run after its first setup makes the calls of the class of one PRSS setup. -/
theorem afterFirstSetup_classBound (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (out : Option (Keys C)) :
    PBound (InClass (C := C) .prssSetup) (afterFirstSetup K circuits settings i operator b out)
      (4 * C.n + termCount C) := by
  unfold afterFirstSetup
  split
  · refine (PBound.bind (n := 0) (PBound.of_class inClass_imp (firstAfter_classBound K circuits settings _ _ _ _ _))
      fun p => ?_).mono (Nat.zero_add _).le
    rcases p with ⟨_ | x, st⟩
    · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · exact bottomTail_classBound K circuits settings i operator b _
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

/-- The rest of a bottom run after its second setup makes no call of the class. -/
theorem afterSecondSetup_classBound (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (head : Option HeadOut) (out : Option (Keys C)) :
    PBound (InClass (C := C) .prssSetup) (afterSecondSetup K circuits settings i operator b head out) 0 := by
  unfold afterSecondSetup
  split
  · refine (PBound.bind (n := 0) (PBound.of_class inClass_imp (secondAfter_classBound K circuits settings _ _ _ _ _ _ _))
      fun p => ?_).mono (Nat.zero_add _).le
    rcases p with ⟨_ | x, st⟩
    · exact isQueryBoundP_pure _ _ _
    · exact PBound.pure _
  · exact isQueryBoundP_pure _ _ _

end Operator

/-! ## The calls of the class in the parts of the game around a bottom slot -/

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The budget of the bottom runs that remain is the cost of the bottom runs that remain, when each
tree has at most `runLimit` runs. -/
theorem remaining_bottomCost_eq (step : ℕ) (runs : Tree → ℕ) (hle : ∀ t, runs t ≤ runLimit) :
    FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) runs =
      (runLimit * 2 ^ layerHeight - bottomRuns runs) * (treeFuel circuits settings * step + 2 * setupClassCalls C) := by
  unfold FirstCounts.remaining bottomRuns
  simp only [bottomCost, Nat.mul_zero, Nat.zero_add]
  rw [← Finset.sum_mul, Finset.sum_tsub_distrib _ fun b _ => hle _]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

/-- The program of an operator in a bottom run starts with its first PRSS setup, or fails at once
without keys or top tree. -/
theorem slotProgram_bottom_split (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) :
    ∃ k : PrssKeys C → PartyM C E RealSpec TreeOutput,
      slotProgram K circuits settings D fresh i operator (.bottom b) =
        (match operator.keys, operator.top with
          | some _, some _ => prssSetup i
          | _, _ => failure) >>= k := by
  rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
  · exact ⟨fun _ => failure, by simp only [slotProgram, hk, failure_bind]⟩
  · exact ⟨fun _ => failure, by simp only [slotProgram, hk, failure_bind]⟩
  · exact ⟨fun _ => failure, by simp only [slotProgram, hk, ht, failure_bind]⟩
  · simp only [slotProgram, hk, ht, slotTree, ceremonyOutput, slotCeremony, StateT.run'_eq, StateT.run_bind,
      StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_map, map_bind, bind_assoc, pure_bind]
    exact ⟨_, rfl⟩

/-- A run of `tree` whose phase is a phase of programs with at most `R` calls of the class each, for
each choice of fresh keys. -/
theorem fixedTreeRun_adds_of (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) (tree : Tree)
    (s : RealState C net.State) (R : ℕ)
    (hphase : ∀ fresh : ℕ → Option (FreshKeys C), ∃ prog : C.Party → PartyM C E RealSpec TreeOutput,
      (∀ i, PBound (InClass (C := C) .prssSetup) (prog i) R) ∧
      executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D fresh i (s.operators i) tree) =
        executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary prog) :
    IsQueryBoundP ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net tree).run s)
      (Adds .prssSetup) (treeFuel circuits settings * step + C.n * R) := by
  unfold fixedTreeRun
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc]
  refine (isQueryBoundP_bind (n := 0) (free_prob_adds _ _) fun fresh _ => ?_).mono (Nat.zero_add _).le
  obtain ⟨prog, hprog, e⟩ := hphase fun c => fresh.getD c none
  rw [e]
  refine (isQueryBoundP_bind (phase_adds D net step hround _ _ _ _ hprog) (m := 0) fun r _ => ?_).mono
    (Nat.add_zero _).le
  rw [← GameCount.bound_iff]
  refine GameCount.bound_mono (GameCount.bound_bind (n := 0) (m := 0)
    (wrongOutput_adds D (fun i => (s.operators i).keys) tree r.2) fun b => ?_) le_rfl
  rw [GameCount.bound_iff]
  exact isQueryBoundP_pure _ _ _

/-- A run of a bottom tree with an honest operator without keys or top tree makes the calls of the
class of one PRSS setup at each operator. The operators stop at the first round of the setup. -/
theorem deadRun_adds (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (hdead : ¬ AliveAtStart D s) :
    IsQueryBoundP ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net (.bottom b)).run s)
      (Adds .prssSetup) (treeFuel circuits settings * step + setupClassCalls C) := by
  obtain ⟨i₀, hi₀, hd₀⟩ : ∃ i, i ∉ D.1 ∧ ¬ ((s.operators i).keys.isSome ∧ (s.operators i).top.isSome) := by
    unfold AliveAtStart at hdead
    push Not at hdead
    obtain ⟨i, hi, h⟩ := hdead
    exact ⟨i, hi, fun h' => absurd (h h'.1) (by simp [h'.2])⟩
  let X : C.Party → PartyM C E RealSpec (PrssKeys C) := fun i =>
    match (s.operators i).keys, (s.operators i).top with
    | some _, some _ => prssSetup i
    | _, _ => failure
  have hX₀ : X i₀ = failure := by
    simp only [X]
    rcases hk : (s.operators i₀).keys with _ | keys <;> rcases ht : (s.operators i₀).top with _ | top
    all_goals first | rfl | simp [hk, ht] at hd₀
  refine fixedTreeRun_adds_of K circuits settings runLimit j D net step hround _ s (4 * C.n + termCount C)
    fun fresh => ⟨fun i => X i >>= fun _ => failure, fun i => ?_, ?_⟩
  · refine (PBound.bind (m := 0) ?_ fun _ => isQueryBoundP_pure _ _ _).mono (Nat.add_zero _).le
    simp only [X]
    split
    · exact prssSetup_classBound i
    · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · choose k hk using fun i => slotProgram_bottom_split K circuits settings D fresh i (s.operators i) b
    rw [executePhase_congr_honest D net _ _ _ _ fun i _ => hk i]
    refine executePhase_dead_congr D net _ _ X _ _ i₀ hi₀ hX₀ fun i _ => ?_
    simp only [X]
    split
    · exact startsWithRound_prssSetup i
    · exact startsWithRound_failure

/-- The rest of `forge` with the oracles of hybrid `j` from a state `s` makes at most its calls of the
class and the budget of the bottom runs that remain. -/
theorem signingImpl_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) (n : ℕ)
    (h : IsQueryBoundP oa (ForgeInClass .prssSetup) n) (st : TsigState C) (s : RealState C A.net.State) :
    IsQueryBoundP (((simulateQ (signingImpl K circuits settings runLimit j D A) oa).run st).run s) (Adds .prssSetup)
      (n * 1 + FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs) := by
  refine simulateQ_pot _ (ForgeInClass .prssSetup) (Adds .prssSetup)
    (fun s : RealState C A.net.State => FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step)
      s.runs) 1 ?_ oa n h st s
  intro t st s'
  rcases t with t | q | q
  · simp only [signingImpl, ForgeInClass]
    exact forger_step (FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step)) t st s'
  · simp only [signingImpl, ForgeInClass, ↓reduceIte]
    exact fixedOracles_step K circuits settings runLimit j D A step hround q st s'
  · simp only [signingImpl, ForgeInClass, ↓reduceIte]
    rcases q with _ | state
    · exact cellRead_step (FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step)) st s'
    · exact cellWrite_step (FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step))
        state st s'

/-- The game after the run of a pause, from the state `s` after the run, makes at most the calls of
the rest of `forge` and the budget of the bottom runs that remain. -/
theorem resumeAfter_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (p : BottomPause C A.net.State) (hnext : ∀ a, IsQueryBoundP (p.next a) (ForgeInClass .prssSetup) forge)
    (s : RealState C A.net.State) :
    IsQueryBoundP (resumeAfter K circuits settings runLimit j D A p s) (Adds .prssSetup)
      (forge + FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs) := by
  unfold resumeAfter
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  obtain ⟨hb, hs⟩ := requestRest_adds D p.b s
  refine (isQueryBoundP_bind (n := 0)
    (m := forge + FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs) hb
    fun r hr => ?_).mono (Nat.zero_add _).le
  obtain ⟨answer, s'⟩ := r
  obtain rfl : s' = s := hs _ hr
  refine (isQueryBoundP_bind (signingImpl_adds K circuits settings runLimit (j + 1) D A step hround _ forge (hnext answer)
    p.tsig s') (m := 0) fun q _ => ?_).mono (by omega)
  obtain ⟨⟨forgery, st⟩, s''⟩ := q
  exact isQueryBoundP_bind (n := 0) (m := 0) (forgeryWins_adds D _ _ _ _ _ _) fun _ _ => isQueryBoundP_pure _ _ _

/-- The head of a bottom run and one setup fit in the fuel of a run, for each parameter. -/
theorem headRounds_add_le (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) :
    CheckTiming.firstRounds circuits settings parameter (.bottom b) + setupRounds ≤ treeFuel circuits settings := by
  have h := bottomRounds_le circuits settings parameter b (fun _ => digit 0)
  rw [CheckTiming.firstRounds, CheckTiming.firstJobs, ← CheckTiming.batchesRounds_eq]
  unfold Fuel.batchesRounds treeFuel
  omega

/-- The pause makes, for the second setup, the calls of the first setup and the head of the run. -/
theorem pauseAt_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (p : BottomPause C A.net.State) :
    IsQueryBoundP (pauseAt K circuits settings runLimit j D A p) (Adds .prssSetup)
      (slotParity runLimit j * (treeFuel circuits settings * step + setupClassCalls C)) := by
  unfold pauseAt
  split_ifs with halive hc
  all_goals try exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · have h1 : slotParity runLimit j = 1 := by
      unfold slotParity at hc ⊢
      omega
    rw [h1, one_mul]
    refine (isQueryBoundP_bind (n := 0) (free_prob_adds _ _) fun fresh _ => ?_).mono (Nat.zero_add _).le
    refine (isQueryBoundP_bind (phase_adds D A.net step hround _ _ _ _ fun i =>
      headWith_classBound K circuits settings D _ i _ p.b) (m := 0) fun r _ => ?_).mono ?_
    · obtain ⟨adversary, heads⟩ := r
      dsimp only
      split_ifs
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_pure _ _ _
    · have := headRounds_add_le circuits settings (stateParameter D p.state) p.b
      have hle : headRounds circuits settings D p * step ≤ treeFuel circuits settings * step :=
        Nat.mul_le_mul_right _ (by unfold headRounds; omega)
      simp only [setupClassCalls]
      omega

/-- The game after the run of a pause from a state with one more run of the tree of the pause. -/
theorem resumeRun_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (p : BottomPause C A.net.State) (hp : PauseInRange runLimit forge j p) (s : RealState C A.net.State)
    (hs : s.runs = Function.update p.state.runs (.bottom p.b) (p.state.runs (.bottom p.b) + 1)) :
    IsQueryBoundP (resumeAfter K circuits settings runLimit j D A p s) (Adds .prssSetup)
      (forge + (runLimit * 2 ^ layerHeight - (bottomRuns p.state.runs + 1)) *
        (treeFuel circuits settings * step + 2 * setupClassCalls C)) := by
  obtain ⟨_, hle, hlt, hnext⟩ := hp
  refine (resumeAfter_adds K circuits settings runLimit j D A step forge hround p hnext s).mono (le_of_eq ?_)
  rw [remaining_bottomCost_eq circuits settings runLimit step _ fun t => ?_, hs, bottomRuns_update]
  rw [hs]
  by_cases ht : t = .bottom p.b
  · subst ht
    simp only [Function.update_self]
    omega
  · rw [Function.update_of_ne ht]
    exact hle t

/-- Under the guard the pause belongs to bottom run `(j - runLimit) / 2`. -/
theorem bottomRuns_of_pauseInRange {σ : Type} (forge j : ℕ) (p : BottomPause C σ)
    (hp : PauseInRange runLimit forge j p) : bottomRuns p.state.runs = (j - runLimit) / 2 := by
  have h := hp.1
  rw [fixedSlot_bottom_eq] at h
  unfold slotParity at h
  omega

/-- The arithmetic of the distinguisher of a bottom slot. -/
theorem bottomRest_arith (a x y forge N k k' c : ℕ) (hk : k = k') (ha : a ≤ x + y) :
    a + (forge + (N - (k + 1)) * c) ≤ forge + x + y + (N - k' - 1) * c := by
  subst hk
  rw [Nat.sub_sub]
  omega

/-- A phase of the run of a pause, the end of the run and the game after it. -/
theorem phaseRest_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (p : BottomPause C A.net.State) (hp : PauseInRange runLimit forge j p)
    (X : OracleComp (WorldSpec C) (A.net.State × (C.Party → Option TreeOutput))) (n : ℕ)
    (hX : IsQueryBoundP X (Adds .prssSetup) n) :
    IsQueryBoundP (X >>= fun r => finishRun D p r >>= fun s => resumeAfter K circuits settings runLimit j D A p s)
      (Adds .prssSetup)
      (n + (forge + (runLimit * 2 ^ layerHeight - (bottomRuns p.state.runs + 1)) *
          (treeFuel circuits settings * step + 2 * setupClassCalls C))) := by
  refine isQueryBoundP_bind hX fun r _ => ?_
  unfold finishRun
  rw [bind_assoc, ← GameCount.bound_iff]
  refine GameCount.bound_mono (GameCount.bound_bind (n := 0)
    (wrongOutput_adds D (fun i => (p.state.operators i).keys) (.bottom p.b) r.2) fun bad => ?_) (Nat.zero_add _).le
  rw [GameCount.bound_iff, pure_bind]
  exact resumeRun_adds K circuits settings runLimit j D A step forge hround p hp _ rfl

/-- A dead run of a pause in hybrid `h` and the game after it. -/
theorem deadRest_adds (h j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (p : BottomPause C A.net.State) (hp : PauseInRange runLimit forge j p) (hdead : ¬ AliveAtStart D p.state) :
    IsQueryBoundP ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net (.bottom p.b)).run p.state >>=
        fun x => resumeAfter K circuits settings runLimit j D A p x.2) (Adds .prssSetup)
      (treeFuel circuits settings * step + setupClassCalls C +
        (forge + (runLimit * 2 ^ layerHeight - (bottomRuns p.state.runs + 1)) *
          (treeFuel circuits settings * step + 2 * setupClassCalls C))) := by
  refine isQueryBoundP_bind (deadRun_adds K circuits settings runLimit h D A.net step hround p.b p.state hdead)
    fun r hr => ?_
  exact resumeRun_adds K circuits settings runLimit j D A step forge hround p hp r.2
    (fixedTreeRun_runs K circuits settings runLimit h D A.net _ p.state _ hr)

/-- The game after a bottom slot, under the guard. -/
theorem bottomRest_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (place : BottomPlace C A.net.State) (hg : PlaceGuard runLimit forge j D place)
    (out : C.Party → Option (Keys C)) :
    IsQueryBoundP (bottomRest K circuits settings runLimit j D A place out) (Adds .prssSetup)
      (forge + treeFuel circuits settings * step + setupClassCalls C +
        (runLimit * 2 ^ layerHeight - (j - runLimit) / 2 - 1) *
          (treeFuel circuits settings * step + 2 * setupClassCalls C)) := by
  cases place with
  | finished => exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  | dead p =>
    have hp : PauseInRange runLimit forge j p := hg.1
    have hdead : ¬ AliveAtStart D p.state := hg.2
    simp only [bottomRest]
    generalize j + 1 = J
    exact (deadRest_adds K circuits settings runLimit J j D A step forge hround p hp hdead).mono
      (bottomRest_arith _ _ _ _ _ _ _ _ (bottomRuns_of_pauseInRange runLimit forge j p hp) le_rfl)
  | live p adversary heads =>
    have hp : PauseInRange runLimit forge j p := hg
    simp only [bottomRest]
    split_ifs
    · refine (phaseRest_adds K circuits settings runLimit j D A step forge hround p hp _ _
        (phase_adds D A.net step hround _ _ _ _ fun i => afterFirstSetup_classBound K circuits settings i _ p.b _)).mono
        (bottomRest_arith _ _ _ _ _ _ _ _ (bottomRuns_of_pauseInRange runLimit forge j p hp) ?_)
      have : (treeFuel circuits settings - setupRounds) * step ≤ treeFuel circuits settings * step :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      simp only [setupClassCalls]
      omega
    · refine (phaseRest_adds K circuits settings runLimit j D A step forge hround p hp _ _
        (phase_adds D A.net step hround _ _ _ _ fun i =>
          afterSecondSetup_classBound K circuits settings i _ p.b _ _)).mono
        (bottomRest_arith _ _ _ _ _ _ _ _ (bottomRuns_of_pauseInRange runLimit forge j p hp) ?_)
      have : (treeFuel circuits settings - headRounds circuits settings D p - setupRounds) * step ≤
          treeFuel circuits settings * step :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  | skip p adversary heads =>
    have hp : PauseInRange runLimit forge j p := hg
    simp only [bottomRest]
    refine (phaseRest_adds K circuits settings runLimit j D A step forge hround p hp _ _
      (phase_adds D A.net step hround _ _ _ (4 * C.n + termCount C) fun i => ?_)).mono
      (bottomRest_arith _ _ _ _ _ _ _ _ (bottomRuns_of_pauseInRange runLimit forge j p hp) ?_)
    · rcases heads i with _ | x
      · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
      · exact bottomTail_classBound K circuits settings i _ p.b x
    · have : (treeFuel circuits settings - headRounds circuits settings D p) * step ≤
          treeFuel circuits settings * step :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      simp only [setupClassCalls]
      omega

/-- A step with a potential that is `0` at the runs `s.runs` and `2` elsewhere keeps the runs. -/
theorem keep_of_step {σ β : Type} (s : RealState C σ) (e : ℕ) (he : e ≤ 1)
    (X : OracleComp (WorldSpec C) ((β × TsigState C) × RealState C σ))
    (h : ∃ d, d ≤ (fun runs => if runs = s.runs then 0 else 2) s.runs + e ∧ IsQueryBoundP X (Adds .prssSetup) d ∧
      ∀ r ∈ support X, (fun runs => if runs = s.runs then 0 else 2) r.2.runs + d ≤
        (fun runs => if runs = s.runs then 0 else 2) s.runs + e) :
    IsQueryBoundP X (Adds .prssSetup) e ∧ ∀ r ∈ support X, r.2.runs = s.runs := by
  obtain ⟨d, hd, hb, hs⟩ := h
  simp only [ite_true, Nat.zero_add] at hd hs
  refine ⟨hb.mono hd, fun r hr => ?_⟩
  by_contra hne
  have := hs r hr
  simp only [hne, ite_false] at this
  omega

/-- A call of `forge` that is not a request of a tree, with the oracles of hybrid `j`, makes its call
of the class and keeps the runs. -/
theorem signingImpl_quiet (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) (ht : ∀ b, t ≠ .inr (.inl (.tree b)))
    (st : TsigState C) (s : RealState C A.net.State) :
    IsQueryBoundP (((signingImpl K circuits settings runLimit j D A t).run st).run s) (Adds .prssSetup)
        (if ForgeInClass .prssSetup t then 1 else 0) ∧
      ∀ r ∈ support (((signingImpl K circuits settings runLimit j D A t).run st).run s), r.2.runs = s.runs := by
  rcases t with t | q | q
  · simp only [signingImpl, ForgeInClass]
    exact keep_of_step s _ (by by_cases h : InClass (C := C) .prssSetup t <;> simp [h]) _
      (forger_step (fun runs => if runs = s.runs then 0 else 2) t st s)
  · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · simp only [signingImpl, ForgeInClass, ↓reduceIte]
      refine ⟨isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
      change r ∈ support (((pure (noAnswer (.corrupt i)) : StateT (TsigState C) (RealM C A.net.State) _).run st).run
        s) at hr
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
    · exact absurd rfl (ht b)
    · simp only [signingImpl, ForgeInClass, ↓reduceIte]
      exact signRequest_quiet D i e (.round1 i J e message) st s
    · simp only [signingImpl, ForgeInClass, ↓reduceIte]
      exact signRequest_quiet D i e (.round2 i J e message parts) st s
  · simp only [signingImpl, ForgeInClass, ↓reduceIte]
    rcases q with _ | state
    · exact keep_of_step s 0 (Nat.zero_le _) _ (cellRead_step (fun runs => if runs = s.runs then 0 else 2) st s)
    · exact keep_of_step s 0 (Nat.zero_le _) _ (cellWrite_step (fun runs => if runs = s.runs then 0 else 2) state st s)

/-- A request of bottom tree `b` before the run of slot `j` takes one bottom run from the budget of the
`k` bottom runs before that run. -/
theorem fixedTreeRequest_walk (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (k : ℕ) (hk : mayRun runLimit D s (.bottom b) → bottomRuns s.runs < k) :
    ∃ d, d ≤ (k - bottomRuns s.runs) * (treeFuel circuits settings * step + 2 * setupClassCalls C) ∧
      IsQueryBoundP ((fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s)
        (Adds .prssSetup) d ∧
      ∀ r ∈ support ((fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s),
        (bottomRuns s.runs ≤ k → bottomRuns r.2.runs ≤ k) ∧
        d + (k - bottomRuns r.2.runs) * (treeFuel circuits settings * step + 2 * setupClassCalls C) ≤
          (k - bottomRuns s.runs) * (treeFuel circuits settings * step + 2 * setupClassCalls C) := by
  unfold fixedTreeRequest
  rw [StateT.run_bind]
  by_cases hm : mayRun runLimit D s (.bottom b)
  · have hlt := hk hm
    refine ⟨treeFuel circuits settings * step + 2 * setupClassCalls C, ?_, ?_, ?_⟩
    · have e : k - bottomRuns s.runs = (k - (bottomRuns s.runs + 1)) + 1 := by omega
      rw [e, Nat.add_mul, one_mul]
      omega
    · have hrun := fixedTreeRun_adds K circuits settings runLimit j D net step hround (.bottom b) s
      simp only [treeSetups] at hrun
      simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte]
      rw [bind_assoc]
      refine (isQueryBoundP_bind hrun (m := 0) fun r _ => ?_).mono (by simp)
      simp only [StateT.run_pure, pure_bind]
      exact (requestRest_adds D b r.2).1
    · intro r hr
      simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte, bind_assoc,
        StateT.run_pure, mem_support_bind_iff] at hr
      obtain ⟨x, hx, hy⟩ := hr
      rw [(requestRest_adds D b x.2).2 r hy, fixedTreeRun_runs K circuits settings runLimit j D net _ s x hx,
        bottomRuns_update]
      refine ⟨fun _ => by omega, ?_⟩
      have e : k - bottomRuns s.runs = (k - (bottomRuns s.runs + 1)) + 1 := by omega
      rw [e, Nat.add_mul, one_mul]
      omega
  · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte, StateT.run_pure]
      exact (requestRest_adds D b s).1
    · intro r hr
      simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte, StateT.run_pure]
        at hr
      rw [(requestRest_adds D b s).2 r hr]
      exact ⟨id, by omega⟩

/-- A program of the game lifted to the signing state, and a continuation. -/
theorem lift_bind_bound {σ α β : Type} (x : RealM C σ α) (k : α → StateT (TsigState C) (RealM C σ) β)
    (st : TsigState C) (s : RealState C σ) (d m : ℕ) (hx : IsQueryBoundP (x.run s) (Adds .prssSetup) d)
    (hk : ∀ y ∈ support (x.run s), IsQueryBoundP (((k y.1).run st).run y.2) (Adds .prssSetup) m) :
    IsQueryBoundP (((StateT.lift x >>= k).run st).run s) (Adds .prssSetup) (d + m) := by
  rw [StateT.run_bind, StateT.run_bind, run_lift_tsig, bind_map_left]
  exact isQueryBoundP_bind hx hk

/-- The walk of `forge` up to the request of the run of slot `j`. The bottom runs before it are at most
`(j - runLimit) / 2`, and the pause adds the head of the run for the second setup. -/
theorem forgeWalk_adds (j : ℕ) (hj : runLimit ≤ j) (D : C.Coalition) (A : DkgTsigAdversary C E) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (keys : Keys C) (top : TopTree)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    ∀ n, IsQueryBoundP oa (ForgeInClass .prssSetup) n → ∀ (st : TsigState C) (s : RealState C A.net.State),
      bottomRuns s.runs ≤ (j - runLimit) / 2 →
      IsQueryBoundP (((forgeWalk K circuits settings runLimit j D A keys top oa).run st).run s) (Adds .prssSetup)
        (n + ((j - runLimit) / 2 - bottomRuns s.runs) * (treeFuel circuits settings * step + 2 * setupClassCalls C) +
          slotParity runLimit j * (treeFuel circuits settings * step + setupClassCalls C)) := by
  induction oa using OracleComp.inductionOn with
  | pure forgery =>
    intro n _ st s _
    change IsQueryBoundP (((forgeWalk K circuits settings runLimit j D A keys top (PFunctor.FreeM.pure forgery)).run
      st).run s) _ _
    simp only [forgeWalk, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_pure]
    exact (isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_bind (n := 0) (m := 0)
      (forgeryWins_adds D _ _ _ _ _ _) fun _ _ => isQueryBoundP_pure _ _ _) fun _ _ =>
        isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  | query_bind t next ih =>
    intro n hn st s hs
    rw [isQueryBoundP_query_bind_iff] at hn
    obtain ⟨hn0, hnext⟩ := hn
    change IsQueryBoundP (((forgeWalk K circuits settings runLimit j D A keys top
      (PFunctor.FreeM.liftBind t next)).run st).run s) _ _
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      have hQ : ¬ ForgeInClass (C := C) (σ := A.net.State) .prssSetup (.inr (.inl (.tree b))) := fun h => h
      simp only [hQ, ite_false] at hnext
      simp only [forgeWalk, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, pure_bind]
      split_ifs with hc
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_pure, bind_assoc]
        exact (isQueryBoundP_bind (pauseAt_adds K circuits settings runLimit j D A step hround _) (m := 0)
          fun _ _ => isQueryBoundP_pure _ _ _).mono (by omega)
      · have hk : mayRun runLimit D s (.bottom b) → bottomRuns s.runs < (j - runLimit) / 2 := by
          intro hm
          have hne : fixedSlot runLimit s.runs (.bottom b) + slotParity runLimit j ≠ j := fun h => hc ⟨hm, h⟩
          rw [fixedSlot_bottom_eq] at hne
          unfold slotParity at hne
          omega
        obtain ⟨d, hd, hb, hsupp⟩ := fixedTreeRequest_walk K circuits settings runLimit j D A.net step hround b s
          ((j - runLimit) / 2) hk
        refine (lift_bind_bound (α := (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Range
            (.inr (.inl (.tree b)))) (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D A.net b) _ st s
            d (n + ((j - runLimit) / 2 - bottomRuns s.runs) * (treeFuel circuits settings * step +
              2 * setupClassCalls C) - d + slotParity runLimit j * (treeFuel circuits settings * step +
              setupClassCalls C)) hb fun y hy => ?_).mono ?_
        · obtain ⟨hle, hcost⟩ := hsupp y hy
          exact (ih y.1 n (hnext y.1) st y.2 (hle hs)).mono (by omega)
        · omega
    · have hstep : IsQueryBoundP (((signingImpl K circuits settings runLimit j D A t >>= fun a =>
          forgeWalk K circuits settings runLimit j D A keys top (next a)).run st).run s) (Adds .prssSetup)
          (n + ((j - runLimit) / 2 - bottomRuns s.runs) * (treeFuel circuits settings * step + 2 * setupClassCalls C) +
            slotParity runLimit j * (treeFuel circuits settings * step + setupClassCalls C)) := by
        obtain ⟨hb, hkeep⟩ := signingImpl_quiet K circuits settings runLimit j D A t (fun b h => ht ⟨b, h⟩) st s
        rw [StateT.run_bind, StateT.run_bind]
        refine (isQueryBoundP_bind hb (m := (if ForgeInClass .prssSetup t then n - 1 else n) +
            ((j - runLimit) / 2 - bottomRuns s.runs) * (treeFuel circuits settings * step + 2 * setupClassCalls C) +
            slotParity runLimit j * (treeFuel circuits settings * step + setupClassCalls C)) fun r hr => ?_).mono ?_
        · have e := hkeep r hr
          refine (ih r.1.1 _ (hnext r.1.1) r.1.2 r.2 (e ▸ hs)).mono ?_
          rw [e]
        · by_cases hq : ForgeInClass (C := C) (σ := A.net.State) .prssSetup t
          · simp only [hq, ite_true, not_true_eq_false, false_or] at hn0 ⊢
            omega
          · simp only [hq, ite_false]
            omega
      rcases t with u | (q | q)
      · simpa only [forgeWalk] using hstep
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · simpa only [forgeWalk] using hstep
        · exact absurd ⟨b, rfl⟩ ht
        · simpa only [forgeWalk] using hstep
        · simpa only [forgeWalk] using hstep
      · simpa only [forgeWalk] using hstep

theorem bottomRuns_update_top (runs : Tree → ℕ) (v : ℕ) :
    bottomRuns (Function.update runs .top v) = bottomRuns runs := by
  unfold bottomRuns
  exact Finset.sum_congr rfl fun b _ => Function.update_of_ne (by simp) _ _

/-- The top runs keep the bottom runs. -/
theorem fixedTreeRuns_top_bottomRuns (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    ∀ (m : ℕ) (s : RealState C net.State),
      ∀ r ∈ support ((fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D net .top m).run s),
        bottomRuns r.2.runs = bottomRuns s.runs
  | 0, s, r, hr => by
    simp only [fixedTreeRuns, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | m + 1, s, r, hr => by
    simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split_ifs at hr
    · rw [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨x, hx, hr⟩ := hr
      rw [fixedTreeRuns_top_bottomRuns j D net m x.2 r hr,
        fixedTreeRun_runs K circuits settings runLimit j D net .top s x hx, bottomRuns_update_top]
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]

/-- The prefix of hybrid `j` up to bottom slot `j`. -/
theorem bottomPrefix_adds (j : ℕ) (hj : runLimit ≤ j) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (start step forge : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.net.start x z) (InClass .prssSetup) start)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) :
    IsQueryBoundP (bottomPrefix K circuits settings runLimit j D A) (Adds .prssSetup)
      ((start + setupRounds * step + 0) +
        (runLimit * (treeFuel circuits settings * step + setupClassCalls C) +
          (forge + ((j - runLimit) / 2 - 0) * (treeFuel circuits settings * step + 2 * setupClassCalls C) +
            slotParity runLimit j * (treeFuel circuits settings * step + setupClassCalls C)) + 0)) := by
  unfold bottomPrefix
  refine isQueryBoundP_bind ((GameCount.bound_iff _ _ _).1
    (seedBlock_bound .prssSetup D A.net start step 0 hstart hround (seedHonest (by decide)))) fun p _ => ?_
  obtain ⟨state, keys⟩ := p
  dsimp only
  refine isQueryBoundP_bind ?_ fun q _ => isQueryBoundP_pure _ _ _
  rw [StateT.run_bind]
  have hruns := fixedTreeRuns_adds K circuits settings runLimit j D A.net step hround .top runLimit
    (startState D state keys)
  simp only [treeSetups, one_mul] at hruns
  refine isQueryBoundP_bind hruns fun q hq => ?_
  have h0 : bottomRuns q.2.runs = 0 := by
    rw [fixedTreeRuns_top_bottomRuns K circuits settings runLimit j D A.net runLimit _ q hq]
    simp [bottomRuns, startState]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · rw [StateT.run'_eq, StateT.run_map, isQueryBoundP_map_iff]
    refine (forgeWalk_adds K circuits settings runLimit j hj D A step hround _ _ _ forge (hforge _ _)
      _ q.2 (by rw [h0]; exact Nat.zero_le _)).mono (le_of_eq ?_)
    rw [h0]

end Game

/-! ## The leaf -/

section Leaf

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (prims : Primitives)

/-- The arithmetic of the start of the reduction of a bottom slot. -/
theorem bottomStart_arith (j start step forge F h : ℕ) (hj : runLimit ≤ j) :
    (start + setupRounds * step + 0) + (runLimit * (F * step + h) +
      (forge + ((j - runLimit) / 2 - 0) * (F * step + 2 * h) + slotParity runLimit j * (F * step + h)) + 0) =
      start + (setupRounds + (runLimit + (j - runLimit) / 2 + slotParity runLimit j) * F) * step + forge + j * h := by
  obtain ⟨m, rfl⟩ : ∃ m, j = runLimit + m := ⟨j - runLimit, by omega⟩
  simp only [slotParity, Nat.add_sub_cancel_left, Nat.sub_zero, Nat.add_zero]
  obtain ⟨k, c, hc, rfl⟩ : ∃ k c, c < 2 ∧ m = 2 * k + c := ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
  have hdiv : (2 * k + c) / 2 = k := by omega
  have hmod : (2 * k + c) % 2 = c := by omega
  rw [hdiv, hmod]
  ring

/-- `BottomSlotPartCosts`. The start, each round and the distinguisher of the reduction of a bottom
slot stay within their budgets in the class `prssSetup`. -/
theorem bottomSlotPartCosts : BottomSlotPartCosts K circuits settings runLimit prims := by
  intro D A start step forge hs hr hf j hlo _
  refine ⟨fun x z => ?_, fun st sent => ?_, fun r => ?_⟩
  · simp only [bottomReduction]
    rw [isQueryBoundP_map_iff]
    refine slotHandler_bound prims D _ _ ((bottomPrefix_adds K circuits settings runLimit j hlo D A start step forge
      hs hr hf).mono (le_of_eq ?_)) _
    exact bottomStart_arith runLimit j start step forge _ _ hlo
  · rcases st with ⟨priv, place⟩
    cases place with
    | live p adversary heads =>
      simp only [bottomReduction]
      rw [isQueryBoundP_map_iff]
      exact slotHandler_bound prims D _ _ (adversary_adds _ _ (hr _ _)) _
    | finished => exact isQueryBoundP_pure _ _ _
    | dead p => exact isQueryBoundP_pure _ _ _
    | skip p adversary heads => exact isQueryBoundP_pure _ _ _
  · unfold bottomDistinguisher
    split_ifs with hg
    · rw [isQueryBoundP_map_iff]
      exact slotHandler_bound prims D _ _ (bottomRest_adds K circuits settings runLimit j D A step forge hr _ hg _) _
    · exact isQueryBoundP_pure _ _ _

end Leaf

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomSlotPartCosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomSlotPartCosts
