import ThresholdLeanXmssSecurity.Proof.Check

/-!
# The security of the check

`MultVerifyStatement` (GS20, Lemmas 8 to 11, and CGH+18) through `MultVerifyDistance` of
`Proof/Check.lean`.

Proved stages:

* The real and the ideal execution run on one shared cache, without the counted and the free copy
  (`accepts_real_eq_local`, `accepts_ideal_eq_local`). `simulateQ_executePhase_mapRoles` moves an oracle
  implementation through the network, and `mapRoles_world` erases the two copies.
* A check of no tuple bit returns at once, and `F_multVerify` accepts, so both runs are equal
  (`checkLocal_zero`).
* For `q ≥ 2 ^ 128` the bound is at least `1` (`one_le_checkHashError`).

Open stage: `CheckCoreDistance`, the two local runs for at least one tuple bit and `q < 2 ^ 128`.
Its plan:

1. Mask the outputs of the real run with the accept bit of `F_multVerify`. The runs differ only
   when an honest operator accepts wrong tuples.
2. Agreeing copies and wrong tuples: `delinearization_card_bound`, `sliceChallenge_soundness`,
   `halvingChallenge_soundness` and `finalChallenge_soundness`, with `q / |E|` for each coin key
   queried before its coin.
3. Disagreeing copies: two honest digests of a term differ unless two history or digest outputs
   collide.
4. Couple the run on `x` with the run on `canonicalDummyTuples`. Each call keeps the view
   (`executePhase_extend_shift`, `shamirPair_call_shift`), the salts hide the digests of the unknown
   terms (`saltDigestPhase_hide`), and the last opening matches by `finalMaskNetwork_sameRun`.
5. Steps 3 and 4 should share one collision event. With a separate birthday term for each, the
   terms of steps 2 to 4 exceed `checkHashError` when `C(n, t - 1) > R + 2` and `q` is large.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ## The network through one oracle implementation -/

section MapRoles

variable {C : Committee} {E : Type}

/-- Interpret both network roles through one oracle implementation. -/
def mapRoles {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec)) : Roles C m :=
  ⟨fun oa => simulateQ impl (roles.adversary oa), fun oa => simulateQ impl (roles.honest oa)⟩

/-- `simulateQ` commutes with the run of a stateful implementation. -/
theorem simulateQ_stateT_run {ι κ σ α : Type} {S : OracleSpec ι} {T : OracleSpec κ}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (φ : QueryImpl T m) (impl : QueryImpl S (StateT σ (OracleComp T))) (oa : OracleComp S α) (s : σ) :
    simulateQ φ ((simulateQ impl oa).run s) =
      (simulateQ (fun t => (StateT.mk fun s => simulateQ φ ((impl t).run s) : StateT σ m _)) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind, simulateQ_bind]
    show _ = (StateT.mk fun s => simulateQ φ ((impl t).run s)).run s >>= _
    refine bind_congr fun p => ?_
    exact ih _ _

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
  (φ : QueryImpl spec m) (Ro : Roles C (OracleComp spec))
  {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

theorem simulateQ_runFunctionality_mapRoles (st : A.State) (inputs : C.Party → Option I) :
    simulateQ φ (runFunctionality Ro D A F st inputs) =
      runFunctionality (mapRoles φ Ro) D A F st inputs := by
  unfold runFunctionality
  by_cases h : ∀ i ∉ D.1, (inputs i).isSome = true
  · rw [if_neg (not_not.mpr h), if_neg (not_not.mpr h)]
    simp only [simulateQ_pure, pure_bind, simulateQ_bind]
    rw [simulateQ_stateT_run]
    congr 1
    congr 1
    congr 1
    funext t
    rcases t with t | l
    · apply StateT.ext
      intro s
      change simulateQ φ ((StateT.lift (Ro.honest (OracleComp.lift (OracleSpec.query t)))).run s) =
        (StateT.lift (simulateQ φ (Ro.honest (OracleComp.lift (OracleSpec.query t))))).run s
      simp [StateT.run_lift]
    · apply StateT.ext
      intro s
      change simulateQ φ (Ro.adversary (A.answer s l) >>= fun d => pure (d.2, d.1)) =
        (simulateQ φ (Ro.adversary (A.answer s l)) >>= fun d => pure (d.2, d.1))
      simp
  · simp [h]

theorem simulateQ_stepRound_mapRoles (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    simulateQ φ (stepRound Ro D A F state steps) = stepRound (mapRoles φ Ro) D A F state steps := by
  unfold stepRound
  split_ifs
  · rw [simulateQ_bind, simulateQ_runFunctionality_mapRoles]
    refine bind_congr fun r => ?_
    rcases r with ⟨st, out⟩
    dsimp only
    rw [simulateQ_bind, simulateQ_sequenceFin]
    simp only [simulateQ_pure]
    congr 1
    congr 1
    funext j
    cases steps j with
    | done out => simp
    | wait outbox resume => simp
    | call input resume => by_cases hj : j ∈ D.1 <;> simp [hj, mapRoles]
  · rw [simulateQ_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨st, sent⟩
    dsimp only
    rw [simulateQ_bind, simulateQ_sequenceFin]
    simp only [simulateQ_pure]
    congr 1
    congr 1
    funext j
    cases steps j with
    | done out => simp
    | wait outbox resume => by_cases hj : j ∈ D.1 <;> simp [hj, mapRoles]
    | call input resume => simp

theorem simulateQ_executeRounds_mapRoles :
    ∀ fuel state (steps : C.Party → Step C E (CallSpec I O) α),
    simulateQ φ (executeRounds Ro D A F fuel state steps) =
      executeRounds (mapRoles φ Ro) D A F fuel state steps
  | 0, state, steps => by simp [executeRounds]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · simp
    · rw [simulateQ_bind, simulateQ_stepRound_mapRoles]
      refine bind_congr fun r => ?_
      exact simulateQ_executeRounds_mapRoles fuel r.1 r.2.1

theorem simulateQ_startSteps (program : C.Party → PartyM C E (CallSpec I O) α) :
    simulateQ φ (startSteps Ro D program) = startSteps (mapRoles φ Ro) D program := by
  unfold startSteps
  rw [simulateQ_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1 <;> simp [hi, mapRoles]

/-- An oracle implementation moves through a whole phase of the network. -/
theorem simulateQ_executePhase_mapRoles (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E (CallSpec I O) α) :
    simulateQ φ (executePhase Ro D A F fuel state program) =
      executePhase (mapRoles φ Ro) D A F fuel state program := by
  unfold executePhase
  rw [simulateQ_bind, simulateQ_startSteps]
  exact bind_congr fun steps => simulateQ_executeRounds_mapRoles φ Ro D A F fuel state steps

end MapRoles

/-! ## The local runs -/

section Local

variable {C : Committee}

/-- The counted and the free copy answer from one cache. -/
theorem mapRoles_world (prims : Primitives) :
    mapRoles (worldAnswer (C := C) prims) worldRoles = mapRoles (localAnswer prims) localRoles := by
  unfold mapRoles
  congr 1
  · funext β oa
    change simulateQ (worldAnswer prims) (counted (liftComp oa (SimulatorSpec C))) =
      simulateQ (localAnswer prims) oa
    rw [simulateQ_counted]
    unfold liftComp
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext t
    rcases t with t | (q | q) <;> exact (simulateQ_query _ _).trans (id_map _)
  · funext β oa
    exact simulateQ_free _ _ oa

theorem simulateQ_world_adversary' (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary oa) = simulateQ (localAnswer prims) oa :=
  congrArg (fun roles : Roles C (StateT (HashCache C) ProbComp) => roles.adversary oa) (mapRoles_world prims)

/-- The probability that a local game accepts from the empty cache. -/
def localAccepts (prims : Primitives) (oa : OracleComp (LocalSpec C) Bool) : ℝ :=
  (Pr[fun b => b = true | (simulateQ (localAnswer prims) oa).run' ∅]).toReal

lemma localAccepts_nonneg (prims : Primitives) (oa : OracleComp (LocalSpec C) Bool) :
    0 ≤ localAccepts prims oa :=
  ENNReal.toReal_nonneg

lemma localAccepts_le_one (prims : Primitives) (oa : OracleComp (LocalSpec C) Bool) :
    localAccepts prims oa ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact probEvent_le_one)

theorem accepts_eq_local (prims : Primitives) (oa : OracleComp (WorldSpec C) Bool)
    (ob : OracleComp (LocalSpec C) Bool)
    (h : simulateQ (worldAnswer prims) oa = simulateQ (localAnswer prims) ob) :
    accepts prims oa = localAccepts prims ob := by
  unfold accepts localAccepts
  congr 1
  rw [← h, ← fst_map_runWorld, probEvent_map]
  rfl

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The real run of the check on the shared cache. -/
def checkRealLocal (K : Constants C E) (fuel : ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) :
    OracleComp (LocalSpec C) Bool := do
  let st ← A.start (corruptInputs D x) z
  let r ← executePhase localRoles D A (checkFunctionalities K) fuel st fun i => checkProtocol K i (x i)
  Z r

/-- The ideal run of the check with `canonicalCheckSimulator` on the shared cache. -/
def checkIdealLocal (K : Constants C E) (fuel : ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) :
    OracleComp (LocalSpec C) Bool := do
  let st ← A.start (corruptInputs D x) z
  let l := multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))
  let r ← executePhase localRoles D A (checkFunctionalities K) fuel st
    fun i => checkProtocol K i (canonicalDummyTuples D l.1 l.2.1 i)
  Z (r.1, fun i => if i ∉ D.1 ∧ l.2.2 ∧ r.2 i = some () then some () else none)

theorem accepts_real_eq_local (prims : Primitives) (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux)
    (Z : Distinguisher C A.State Unit) :
    accepts prims (distinguish (realExecution D A (checkFunctionalities K) fuel (checkProtocol K) x z) Z) =
      localAccepts prims (checkRealLocal K fuel D A x z Z) := by
  apply accepts_eq_local
  unfold distinguish realExecution checkRealLocal
  simp only [simulateQ_bind, bind_assoc, simulateQ_executePhase_mapRoles, mapRoles_world, simulateQ_world_adversary']

theorem accepts_ideal_eq_local (prims : Primitives) (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux)
    (Z : Distinguisher C A.State Unit) :
    accepts prims (distinguish (idealExecution worldRoles.adversary D FmultVerify
        (canonicalCheckSimulator K fuel D A) x z) Z) =
      localAccepts prims (checkIdealLocal K fuel D A x z Z) := by
  apply accepts_eq_local
  rw [idealExecution_multVerify_local, distinguish_adversary, simulateQ_world_adversary']
  congr 1
  simp [idealMultVerifyLocal, canonicalCheckSimulator, checkIdealLocal, bind_assoc]

end Local

/-! ## No tuple bit -/

section Zero

variable {C : Committee} {E : Type}

/-- A run in which every honest program returns at once. -/
theorem executePhase_pure {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (a : α) :
    executePhase localRoles D A F fuel st (fun _ => (pure a : PartyM C E (CallSpec I O) α)) =
      pure (st, fun i => if i ∈ D.1 then none else some a) := by
  have hs : startSteps localRoles D (fun _ => (pure a : PartyM C E (CallSpec I O) α)) =
      pure (fun i => if i ∈ D.1 then Step.done none else Step.done (some a)) := by
    unfold startSteps
    simp only [localRoles, advance_run_pure]
    rw [← sequenceFin_pure]
    congr 1
    funext i
    split_ifs <;> rfl
  unfold executePhase
  rw [hs, pure_bind]
  have ho : (fun i => (if i ∈ D.1 then Step.done none else Step.done (some a) :
      Step C E (CallSpec I O) α).output) = fun i => if i ∈ D.1 then none else some a := by
    funext i
    split_ifs <;> rfl
  cases fuel with
  | zero => simp only [executeRounds, ho]
  | succ fuel =>
    rw [executeRounds, if_pos (fun i _ => by split_ifs; trivial), ho]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- A check of no tuple bit returns at once. -/
theorem checkProtocol_zero (K : Constants C E) (i : C.Party) (tuples : List (Tuple C))
    (h : (tuples.map (·.count)).sum = 0) : checkProtocol K i tuples = pure () := by
  unfold checkProtocol
  simp only [check, h, ↓reduceIte]
  rfl

/-- With no tuple bit, `F_multVerify` accepts. -/
theorem multVerifyLeak_accept_zero (counts : List ℕ) (D : C.Coalition) (x : C.Party → List (Tuple C))
    (hc : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) (hz : counts.sum = 0) :
    (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 = true := by
  obtain ⟨j, hj, hf⟩ := firstInput_honest D x
  have hcount : ∀ k, (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) k).count = 0 := by
    intro k
    simp only [tupleAt, hf]
    cases hk : (x j)[k]? with
    | none => rfl
    | some τ =>
      have hm : τ.count ∈ counts := by
        rw [← hc j hj]
        exact List.mem_map.mpr ⟨τ, List.mem_of_getElem? hk, rfl⟩
      simpa using List.sum_eq_zero_iff.mp hz _ hm
  simp only [multVerifyLeak, decide_eq_true_eq]
  constructor
  · intro k hk T i _ j' _ _ _ g hg
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk] at hg
    simp [hcount] at hg
  · intro τ hτ g hg
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hτ
    rw [hcount] at hg
    exact absurd hg (Nat.not_lt_zero _)

/-- With no tuple bit, the real and the ideal local run are equal. -/
theorem checkLocal_zero (K : Constants C E) (counts : List ℕ) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux)
    (Z : Distinguisher C A.State Unit) (hx : TupleInputs K counts D x) (hz : counts.sum = 0) :
    checkRealLocal K fuel D A x z Z = checkIdealLocal K fuel D A x z Z := by
  unfold checkRealLocal checkIdealLocal
  refine bind_congr fun st => ?_
  have hreal := executePhase_congr_honest D A (checkFunctionalities K) fuel st
    (fun i => checkProtocol K i (x i)) (fun _ => pure ())
    (fun i hi => checkProtocol_zero K i _ (by rw [hx.1 i hi, hz]))
  have hideal := executePhase_congr_honest D A (checkFunctionalities K) fuel st
    (fun i => checkProtocol K i (canonicalDummyTuples D
      (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).1
      (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1 i)) (fun _ => pure ())
    (fun i hi => checkProtocol_zero K i _ (by rw [canonicalDummyTuples_leak_counts K counts D x hx i hi, hz]))
  dsimp only
  rw [hreal, hideal, executePhase_pure, pure_bind, pure_bind,
    multVerifyLeak_accept_zero counts D x hx.1 hz]
  congr 2
  funext i
  by_cases hi : i ∈ D.1 <;> simp [hi]

end Zero

/-! ## Assembly -/

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

lemma checkErrorOf_nonneg (K : Constants C E) (d R q : ℕ) : 0 ≤ checkErrorOf (E := E) d R q := by
  have hc : (2 : ℝ) < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  unfold checkErrorOf
  have h1 : (0 : ℝ) < Fintype.card E - 2 := by linarith
  positivity

lemma checkHashError_nonneg (count q : ℕ) : 0 ≤ checkHashError C count q := by
  unfold checkHashError
  positivity

/-- For `q ≥ 2 ^ 128` the hash term alone is at least `1`. -/
lemma one_le_checkHashError (count q : ℕ) (hq : 2 ^ 128 ≤ q) : 1 ≤ checkHashError C count q := by
  unfold checkHashError
  rw [le_div_iff₀ (by positivity), one_mul]
  have h : 2 ^ 256 ≤ (q + termHashes C + halvings count + 2) ^ 2 :=
    calc 2 ^ 256 = (2 ^ 128) ^ 2 := by norm_num
      _ ≤ (q + termHashes C + halvings count + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact_mod_cast h

/-- The open stage: the real and the ideal local run of a check of at least one tuple bit, for a
budget below `2 ^ 128`. -/
def CheckCoreDistance (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) (q : ℕ),
    TupleInputs K counts D x → IsQueryBounded A Z (checkRounds counts.sum) q →
    counts.sum ≠ 0 → q < 2 ^ 128 →
    |localAccepts prims (checkRealLocal K (checkRounds counts.sum) D A x z Z) -
      localAccepts prims (checkIdealLocal K (checkRounds counts.sum) D A x z Z)| ≤
      checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q + checkHashError C counts.sum q

/-- `MultVerifyDistance` from the open stage `CheckCoreDistance`. -/
theorem multVerifyDistance (prims : Primitives) (K : Constants C E) (core : CheckCoreDistance prims K) :
    MultVerifyDistance prims K := by
  intro counts D A x z Z q hx hq
  rw [accepts_real_eq_local, accepts_ideal_eq_local]
  have hE := checkErrorOf_nonneg K (coins counts.sum) (halvings counts.sum) q
  have hH := checkHashError_nonneg (C := C) counts.sum q
  by_cases hz : counts.sum = 0
  · rw [checkLocal_zero K counts _ D A x z Z hx hz, sub_self, abs_zero]
    linarith
  by_cases hlarge : 2 ^ 128 ≤ q
  · have h1 := one_le_checkHashError (C := C) counts.sum q hlarge
    have hr0 := localAccepts_nonneg prims (checkRealLocal K (checkRounds counts.sum) D A x z Z)
    have hr1 := localAccepts_le_one prims (checkRealLocal K (checkRounds counts.sum) D A x z Z)
    have hi0 := localAccepts_nonneg prims (checkIdealLocal K (checkRounds counts.sum) D A x z Z)
    have hi1 := localAccepts_le_one prims (checkIdealLocal K (checkRounds counts.sum) D A x z Z)
    rw [abs_le]
    constructor <;> linarith
  · exact core counts D A x z Z q hx hq hz (Nat.lt_of_not_le hlarge)

/-- `MultVerifyStatement` from the open stage `CheckCoreDistance`. -/
theorem multVerifyStatementProof (prims : Primitives) (K : Constants C E) (core : CheckCoreDistance prims K) :
    MultVerifyStatement prims K :=
  multVerifyStatement_of_distance prims K (multVerifyDistance prims K core)

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.multVerifyDistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multVerifyDistance

/-- info: 'ThresholdLeanXmssSecurity.multVerifyStatementProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multVerifyStatementProof

end ThresholdLeanXmssSecurity
