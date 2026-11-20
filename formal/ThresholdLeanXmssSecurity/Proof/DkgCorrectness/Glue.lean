import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Route
import ThresholdLeanXmssSecurity.Proof.PhaseSplit

/-!
# The route with one cut, the glue

`runHopL_of_route` gives the bound of one run with `runError` from the statements of `Route.lean`,
from each start with `RunReadyL`. `part1L_of_route` gives `Part1With` with `part1Error` from it and
from the hops of the game over the readiness test.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The arithmetic of the ledger and of the error -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem le_foldl_max : ∀ (l : List ℕ) (init : ℕ), init ≤ l.foldl max init ∧ ∀ a ∈ l, a ≤ l.foldl max init
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left _ _) (le_foldl_max xs _).1, ?_⟩
    rintro a (rfl | ha)
    · exact le_trans (le_max_right _ _) (le_foldl_max xs _).1
    · exact (le_foldl_max xs _).2 a ha

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A batch of a job list of the protocol has at most the measure of `maxBatch`. -/
theorem measure_le_maxBatch (measure : List Circuit → ℕ) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (encoding : Encoding) (js : List Job)
    (hmem : js ∈ [topJobs, bottomJobs b, signJobs b encoding].flatMap (chunks settings.batchSize)) :
    measure (runCircuits circuits parameter js) ≤ maxBatch circuits settings measure := by
  have hfold := (le_foldl_max
    ((([topJobs, bottomJobs b, signJobs b encoding].flatMap (chunks settings.batchSize)).map
      fun jobs => measure (runCircuits circuits parameter jobs))) 0).2 _ (List.mem_map.2 ⟨js, hmem, rfl⟩)
  unfold maxBatch
  exact hfold.trans (Finset.le_sup (f := fun x : PublicParameter × Fin (2 ^ layerHeight) × Encoding =>
    (([topJobs, bottomJobs x.2.1, signJobs x.2.1 x.2.2].flatMap (chunks settings.batchSize)).map
      fun jobs => measure (runCircuits circuits x.1 jobs)).foldl max 0) (Finset.mem_univ (parameter, b, encoding)))

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- Each job list of the protocol is admissible. -/
theorem admissible_of_protocol (b : Fin (2 ^ layerHeight)) (encoding : Encoding) (jobs : List Job)
    (h : jobs = topJobs ∨ jobs = bottomJobs b ∨ jobs = signJobs b encoding) :
    AdmissibleJobs circuits settings jobs := by
  intro parameter js hjs
  have hmem : js ∈ [topJobs, bottomJobs b, signJobs b encoding].flatMap (chunks settings.batchSize) := by
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    rcases h with h | h | h
    · exact ⟨_, Or.inl rfl, h ▸ hjs⟩
    · exact ⟨_, Or.inr (Or.inl rfl), h ▸ hjs⟩
    · exact ⟨_, Or.inr (Or.inr rfl), h ▸ hjs⟩
  constructor
  · unfold batchCounts
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    exact ⟨(parameter, b, encoding), js, hmem, rfl⟩
  · exact measure_le_maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) parameter b encoding js hmem

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A tree has at most the batches of a game. -/
theorem treeBatches_le_gameBatches (hrun : 0 < runLimit) (tree : Tree) :
    treeBatches settings tree ≤ gameBatches settings runLimit := by
  unfold gameBatches
  refine le_trans ?_ (Nat.le_mul_of_pos_left _ hrun)
  cases tree with
  | top => exact Nat.le_add_right _ _
  | bottom b =>
    exact le_trans (Finset.single_le_sum (f := fun b => treeBatches settings (.bottom b))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)) (Nat.le_add_left _ _)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- One run and two more rounds are rounds of the game. The rounds of the seed generation pay the
padding of the charge of the pilot. -/
theorem treeFuel_add_two_le (hrun : 0 < runLimit) :
    treeFuel circuits settings + 2 ≤ dkgTsigRounds circuits settings runLimit := by
  unfold dkgTsigRounds
  have h : treeFuel circuits settings ≤ runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings := by
    calc treeFuel circuits settings = 1 * 1 * treeFuel circuits settings := by ring
      _ ≤ runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hrun (Nat.le_add_right _ _))
  have h2 : 2 ≤ setupRounds := by decide
  omega

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem coinKeysOf_add (a b : ℕ) :
    coinKeysOf circuits settings C (a + b) = coinKeysOf circuits settings C a + coinKeysOf circuits settings C b := by
  unfold coinKeysOf
  ring

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The honest coin keys of the batches of one run are coin keys of the game. -/
theorem coinKeysOf_le (hrun : 0 < runLimit) (tree : Tree) (batches : ℕ) (h : batches ≤ treeBatches settings tree) :
    coinKeysOf circuits settings C batches ≤ gameCoinKeys circuits settings runLimit C := by
  unfold coinKeysOf gameCoinKeys
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (h.trans (treeBatches_le_gameBatches settings runLimit hrun tree)))

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The room of one run. A ledger that the start budget of the game and the cells of `rounds` rounds
and `batches` batches of one run bound is within the budgets of `batchCheckError`. -/
theorem ledgerRoom_of_run (hrun : 0 < runLimit) (tree : Tree) (q step rounds batches : ℕ) (ℓ : StartBudget)
    (hrounds : rounds ≤ treeFuel circuits settings) (hbatches : batches ≤ treeBatches settings tree)
    (hq : dkgTsigRounds circuits settings runLimit * step ≤ q)
    (hcoins : ℓ.coins ≤ q + gameCoinKeys circuits settings runLimit C + rounds * step +
      coinKeysOf circuits settings C batches)
    (hkeys : ℓ.keys ≤ gameCoinKeys circuits settings runLimit C + coinKeysOf circuits settings C batches)
    (hsalts : ℓ.salts ≤ splitBudget settings runLimit C q + rounds * step + batches * termHashes C) :
    LedgerRoom circuits settings runLimit C q step ℓ := by
  have hpad : (rounds + 2) * step ≤ q :=
    le_trans (Nat.mul_le_mul_right _ ((Nat.add_le_add_right hrounds 2).trans
      (treeFuel_add_two_le circuits settings runLimit hrun))) hq
  have hck := coinKeysOf_le (C := C) circuits settings runLimit hrun tree batches hbatches
  have htH : batches * termHashes C ≤ gameBatches settings runLimit * termHashes C :=
    Nat.mul_le_mul_right _ (hbatches.trans (treeBatches_le_gameBatches settings runLimit hrun tree))
  have hsplit : splitBudget settings runLimit C q = q + gameBatches settings runLimit * termHashes C := rfl
  have hexp : (rounds + 2) * step = rounds * step + 2 * step := by ring
  refine ⟨by omega, by omega, by omega⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The padded rounds of a phase of one run are within `q`. -/
theorem padded_le (hrun : 0 < runLimit) (q step rounds : ℕ) (hrounds : rounds ≤ treeFuel circuits settings)
    (hq : dkgTsigRounds circuits settings runLimit * step ≤ q) : (rounds + 2) * step ≤ q :=
  le_trans (Nat.mul_le_mul_right _ ((Nat.add_le_add_right hrounds 2).trans
    (treeFuel_add_two_le circuits settings runLimit hrun))) hq

/-- The fresh part of one ceremony from a start with at most `hiddenKeys` keys under each name. -/
def ceremonyFresh (C : Committee) (hiddenKeys : ℕ) : ℝ := ((prssKeyCount C * hiddenKeys : ℕ) : ℝ) / 2 ^ 256

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem topFresh_le : ceremonyFresh C (gameSetups runLimit) ≤ freshError runLimit C .top := by
  unfold ceremonyFresh freshError
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast (show prssKeyCount C * gameSetups runLimit ≤
      treeSetups .top * prssKeyCount C * (gameSetups runLimit + treeSetups .top) by
    simp only [treeSetups, one_mul]
    exact Nat.mul_le_mul_left _ (Nat.le_succ _))

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem bottomFresh_le (b : Fin (2 ^ layerHeight)) :
    ceremonyFresh C (gameSetups runLimit) + ceremonyFresh C (gameSetups runLimit + 1) ≤
      freshError runLimit C (.bottom b) := by
  unfold ceremonyFresh freshError
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  simp only [treeSetups]
  norm_cast
  nlinarith [Nat.zero_le (prssKeyCount C), Nat.zero_le (prssKeyCount C * gameSetups runLimit)]

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem chunks_length {α : Type} (size : ℕ) (items : List α) :
    (chunks size items).length = (items.length + size - 1) / size := by
  simp [chunks]

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The batches of the two ceremonies of a bottom tree are `treeBatches`, for each encoding. -/
theorem bottomBatches (b : Fin (2 ^ layerHeight)) (encoding : Encoding) :
    (chunks settings.batchSize (bottomJobs b)).length +
      (chunks settings.batchSize (signJobs b encoding)).length = treeBatches settings (.bottom b) := by
  simp [treeBatches, chunks_length, signJobs]

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The batches of the ceremony of the top tree are `treeBatches`. -/
theorem topBatches : (chunks settings.batchSize topJobs).length = treeBatches settings .top := rfl

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The room for the first ceremony of a run from the start budget of the game. -/
theorem ledgerRoom_first (hrun : 0 < runLimit) (tree : Tree) (q step rounds batches : ℕ)
    (hrounds : rounds ≤ treeFuel circuits settings) (hbatches : batches ≤ treeBatches settings tree)
    (hq : dkgTsigRounds circuits settings runLimit * step ≤ q) :
    LedgerRoom circuits settings runLimit C q step
      (ledgerStep circuits settings C step rounds batches (startBudget circuits settings runLimit C q)) :=
  ledgerRoom_of_run circuits settings runLimit hrun tree q step rounds batches _ hrounds hbatches hq
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-! ## The top tree -/

omit [DecidableEq E] in
/-- The bound of a run of the top tree, from the ceremony lemma and the monitor split. -/
theorem runBad_top (runs : 0 < runLimit) (hsize : 0 < settings.batchSize)
    (compute : CircuitsCompute circuits prims.Th)
    (bad : CeremonyBad prims K circuits settings runLimit)
    (cover : TopCover prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step : ℕ)
    (hstep : ∀ st sent, IsQueryBoundP (net.round st sent) Counted step)
    (hq : dkgTsigRounds circuits settings runLimit * step ≤ q)
    (s : RealState C net.State) (world : StreamState C)
    (ready : RunReady prims (startBudget circuits settings runLimit C q) D s world) (hP : HiddenProvenance D world)
    (flag : s.flag = false) :
    (Pr{let r ← (streamTreeRun prims K circuits settings D net .top s).run world}[
        r.1.2 = true ∧ ¬ GlobalEvent r.2]).toReal ≤ runError (E := E) circuits settings runLimit C q .top := by
  have hcover := ENNReal.toReal_mono (prEvent_ne_top _) (cover hsize compute _ D net s world ready flag)
  have hready : CeremonyReady D (startBudget circuits settings runLimit C q) (topStart s) world :=
    ⟨ready.1, ledgerFits_of_runReady prims ready, hP⟩
  have hjobs : (topStart (σ := net.State) s).jobs = topJobs := by simp only [topStart]
  have hbatches : (chunks settings.batchSize (topStart (σ := net.State) s).jobs).length = treeBatches settings .top := by
    rw [hjobs]
    exact topBatches settings
  have hroom := ledgerRoom_first (C := C) circuits settings runLimit runs .top q step (treeFuel circuits settings)
    (chunks settings.batchSize (topStart (σ := net.State) s).jobs).length le_rfl hbatches.le hq
  have hbad := bad hsize D net q step (treeFuel circuits settings) hstep _ (topStart s) world
    (admissible_of_protocol circuits settings 0 (fun _ => digit 0) _ (Or.inl hjobs)) hready hroom
    (padded_le circuits settings runLimit runs q step _ le_rfl hq)
  have hfresh := topFresh_le (C := C) runLimit
  rw [hbatches] at hbad
  unfold runError
  unfold ceremonyFresh at hfresh
  have hk : (startBudget circuits settings runLimit C q).hiddenKeys = gameSetups runLimit := rfl
  rw [hk] at hbad
  linarith

/-! ## A bottom tree -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- Consistent keys stay consistent when some operators lose their keys. -/
theorem seedsDiffer_sub (D : C.Coalition) (keys keys' : C.Party → Option (Keys C))
    (h : ∀ i k, keys' i = some k → keys i = some k) (hk : seedsDiffer D keys = false) :
    seedsDiffer D keys' = false := by
  unfold seedsDiffer at hk ⊢
  rw [decide_eq_false_iff_not] at hk ⊢
  rintro ⟨i, j, ki, kj, hi, hj, hki, hkj, hne⟩
  exact hk ⟨i, j, ki, kj, hi, hj, h i ki hki, h j kj hkj, hne⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem aliveKeys_some {σ : Type} (s : RealState C σ) (i : C.Party) (k : Keys C) (h : aliveKeys s i = some k) :
    (s.operators i).keys = some k := by
  unfold aliveKeys at h
  split at h
  · rename_i hk _
    rw [hk]
    exact h
  · exact absurd h (by simp)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- Consistent keys have one parameter at the honest operators. -/
theorem exists_parameter (D : C.Coalition) {σ : Type} (s : RealState C σ)
    (hk : seedsDiffer D (fun i => (s.operators i).keys) = false) :
    ∃ parameter : PublicParameter, ∀ i, i ∉ D.1 → ∀ keys, (s.operators i).keys = some keys →
      keys.parameter = parameter := by
  unfold seedsDiffer at hk
  rw [decide_eq_false_iff_not] at hk
  by_cases h : ∃ j, j ∉ D.1 ∧ ∃ kj, (s.operators j).keys = some kj
  · obtain ⟨j, hj, kj, hkj⟩ := h
    refine ⟨kj.parameter, fun i hi ki hki => ?_⟩
    by_contra hne
    exact hk ⟨i, j, ki, kj, hi, hj, hki, hkj, Or.inl hne⟩
  · exact ⟨0, fun i hi ki hki => absurd ⟨i, hi, ki, hki⟩ h⟩

omit [Fintype E] [DecidableEq E] in
/-- The split of a run of a bottom tree at its head, by `executePhase_split`. The run has the law of
the head and then the rest with the monitor. -/
theorem bottomSplit (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (n m : ℕ) (hfuel : treeFuel circuits settings = n + m)
    (htimed : ∀ i ∉ D.1, Timed n (CheckTiming.bottomHead K circuits settings i (s.operators i) b).run) :
    (streamTreeRun prims K circuits settings D net (.bottom b) s).run world =ᵈ
      ((bottomCut prims K circuits settings D net b s n).run world >>= fun z =>
        (bottomRest prims K circuits settings D net b s z.1.1 z.1.2 m).run z.2) := by
  unfold streamTreeRun bottomCut bottomRest
  rw [show (fun i => treeProgram K circuits settings i (s.operators i) (.bottom b)) =
      fun i => CheckTiming.bottomHead K circuits settings i (s.operators i) b >>=
        CheckTiming.bottomTail K circuits settings i (s.operators i) b from
    funext fun i => CheckTiming.treeProgram_bottom K circuits settings i _ b, hfuel]
  have h := WorldSplit.executePhase_split prims D net n m s.adversary
    (fun i => CheckTiming.bottomHead K circuits settings i (s.operators i) b)
    (fun i => CheckTiming.bottomTail K circuits settings i (s.operators i) b) htimed world
  simp only [simulateQ_bind, StateT.run_bind] at h ⊢
  exact (h.bind fun p => .rfl).trans (by rw [bind_assoc])

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The room for the second ceremony of a run of a bottom tree, from the ledger of the cut. -/
theorem ledgerRoom_second (hrun : 0 < runLimit) (tree : Tree) (q step n m b₁ b₂ : ℕ)
    (hrounds : n + m ≤ treeFuel circuits settings) (hbatches : b₁ + b₂ ≤ treeBatches settings tree)
    (hq : dkgTsigRounds circuits settings runLimit * step ≤ q) :
    LedgerRoom circuits settings runLimit C q step
      (ledgerStep circuits settings C step m b₂
        (ledgerStep circuits settings C step n b₁ (startBudget circuits settings runLimit C q))) := by
  refine ledgerRoom_of_run circuits settings runLimit hrun tree q step (n + m) (b₁ + b₂) _ hrounds hbatches hq
    ?_ ?_ ?_
  · rw [coinKeysOf_add, Nat.add_mul]
    simp only [ledgerStep, startBudget]
    omega
  · rw [coinKeysOf_add]
    simp only [ledgerStep, startBudget]
    omega
  · rw [Nat.add_mul, Nat.add_mul]
    simp only [ledgerStep, startBudget]
    omega

omit [DecidableEq E] in
/-- The bound of a run of a bottom tree, from the ceremony lemma used two times and the facts at the
cut. -/
theorem runBad_bottom (runs : 0 < runLimit) (hsize : 0 < settings.batchSize)
    (compute : CircuitsCompute circuits prims.Th)
    (bad : CeremonyBad prims K circuits settings runLimit)
    (fuel : HeadFuel circuits settings)
    (head : HeadCover prims K circuits settings)
    (cut : CutState prims K circuits settings)
    (dead : CutDead prims K circuits settings)
    (mono : CutMonotone prims K circuits settings)
    (rest : RestCover prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step : ℕ)
    (hstep : ∀ st sent, IsQueryBoundP (net.round st sent) Counted step)
    (hq : dkgTsigRounds circuits settings runLimit * step ≤ q)
    (b : Fin (2 ^ layerHeight)) (s : RealState C net.State) (world : StreamState C)
    (ready : RunReady prims (startBudget circuits settings runLimit C q) D s world) (hP : HiddenProvenance D world)
    (flag : s.flag = false) :
    (Pr{let r ← (streamTreeRun prims K circuits settings D net (.bottom b) s).run world}[
        r.1.2 = true ∧ ¬ GlobalEvent r.2]).toReal ≤
      runError (E := E) circuits settings runLimit C q (.bottom b) := by
  obtain ⟨parameter, hpar⟩ := exists_parameter D s ready.1
  obtain ⟨n, hn⟩ : ∃ n, CheckTiming.firstRounds circuits settings parameter (.bottom b) = n := ⟨_, rfl⟩
  have hnle : n ≤ treeFuel circuits settings := hn ▸ fuel parameter b
  obtain ⟨m, hm⟩ : ∃ m, treeFuel circuits settings - n = m := ⟨_, rfl⟩
  have hfuel : treeFuel circuits settings = n + m := by omega
  have htimed : ∀ i ∉ D.1, Timed n (CheckTiming.bottomHead K circuits settings i (s.operators i) b).run :=
    fun i hi => hn ▸ CheckTiming.timed_bottomHead K circuits settings parameter i (s.operators i) b (hpar i hi)
  obtain ⟨b₁, hb₁⟩ : ∃ k, (chunks settings.batchSize (bottomJobs b)).length = k := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ k, (chunks settings.batchSize (signJobs b fun _ => digit 0)).length = k := ⟨_, rfl⟩
  have hb : b₁ + b₂ = treeBatches settings (.bottom b) := by
    rw [← hb₁, ← hb₂]
    exact bottomBatches settings b _
  have hkeys : seedsDiffer D (aliveKeys s) = false :=
    seedsDiffer_sub D _ _ (aliveKeys_some s) ready.1
  -- The first ceremony.
  have hj₁ : (firstStart (σ := net.State) b s).jobs = bottomJobs b := by simp only [firstStart]
  have hready₁ : CeremonyReady D (startBudget circuits settings runLimit C q) (firstStart b s) world :=
    ⟨hkeys, ledgerFits_of_runReady prims ready, hP⟩
  have hroom₁ := ledgerRoom_first (C := C) circuits settings runLimit runs (.bottom b) q step n b₁ hnle
    (by omega) hq
  have hbad₁ := bad hsize D net q step n hstep _ (firstStart b s) world
    (admissible_of_protocol circuits settings b (fun _ => digit 0) _ (Or.inr (Or.inl hj₁))) hready₁
    (by rw [hj₁, hb₁]; exact hroom₁) (padded_le circuits settings runLimit runs q step n hnle hq)
  rw [hj₁, hb₁] at hbad₁
  have hhead := ENNReal.toReal_mono (prEvent_ne_top _) (head D net b s world n htimed)
  -- The second ceremony.
  obtain ⟨ε₂, hε₂def⟩ : ∃ ε : ℝ, ε = b₂ * checkErrorMax (E := E) circuits settings runLimit C q +
      ceremonyFresh C (gameSetups runLimit + 1) := ⟨_, rfl⟩
  have hε₂ : 0 ≤ ε₂ := by
    rw [hε₂def]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (checkErrorMax_nonneg circuits settings runLimit q))
      (by unfold ceremonyFresh; positivity)
  have hz : ∀ z ∈ support ((bottomCut prims K circuits settings D net b s n).run world),
      Pr{let y ← (bottomRest prims K circuits settings D net b s z.1.1 z.1.2 m).run z.2}[
          y.1.2 = true ∧ ¬ GlobalEvent y.2] ≤
        (if FirstWrong prims circuits D b s z ∧ ¬ GlobalEvent z.2 then 1 else 0) +
          (if True then ENNReal.ofReal ε₂ else 0) := by
    intro z hzs
    obtain ⟨hfit, hPz, hagree⟩ := cut D net step hstep _ b s world n htimed hready₁ z hzs
    by_cases hp : FirstWrong prims circuits D b s z ∧ ¬ GlobalEvent z.2
    · simp only [hp, ↓reduceIte]
      exact (prEvent_le_one _).trans le_self_add
    · simp only [hp, ↓reduceIte, zero_add]
      by_cases hge : GlobalEvent z.2
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun y hy h =>
          h.2 (mono D net b s z.1.1 z.1.2 m z.2 hge y hy)]
        exact bot_le
      · have hfw : ¬ FirstWrong prims circuits D b s z := fun h => hp ⟨h, hge⟩
        by_cases hdead : ∃ i, i ∉ D.1 ∧ z.1.2 i = none
        · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun y hy h => by
            have hfalse := dead D net b s z.1.1 z.1.2 m z.2 hdead y hy
            rw [hfalse] at h
            exact absurd h.1 (by simp)]
          exact bot_le
        · obtain ⟨x, hx⟩ : ∃ x : HeadResult, ∀ i, i ∉ D.1 → z.1.2 i = some x := by
            by_cases hne : ∃ i, i ∉ D.1
            · obtain ⟨i₀, hi₀⟩ := hne
              obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 fun h => hdead ⟨i₀, hi₀, h⟩
              refine ⟨x, fun i hi => ?_⟩
              obtain ⟨xi, hxi⟩ := Option.ne_none_iff_exists'.1 fun h => hdead ⟨i, hi, h⟩
              rw [hxi, hagree hge i i₀ xi x hi hi₀ hxi hx]
            · exact ⟨(([], 0, 0, fun _ => digit 0), (0, 0)), fun i hi => absurd ⟨i, hi⟩ hne⟩
          refine (rest hsize compute _ D net b s world n m ready flag z hzs x hx hfw).trans ?_
          rw [ENNReal.le_ofReal_iff_toReal_le (prEvent_ne_top _) hε₂]
          have hj₂ : (secondStart (σ := net.State) b s z.1.1 x).jobs = signJobs b x.1.2.2.2 := by
            simp only [secondStart]
          have hlen : (chunks settings.batchSize (signJobs b x.1.2.2.2)).length = b₂ := by
            rw [← hb₂]
            simp [chunks_length, signJobs]
          have hready₂ : CeremonyReady D
              (ledgerStep circuits settings C step n b₁ (startBudget circuits settings runLimit C q))
              (secondStart b s z.1.1 x) z.2 := ⟨hkeys, hb₁ ▸ hfit, hPz⟩
          have hbad₂ := bad hsize D net q step m hstep _ (secondStart b s z.1.1 x) z.2
            (admissible_of_protocol circuits settings b x.1.2.2.2 _ (Or.inr (Or.inr hj₂))) hready₂
            (by rw [hj₂, hlen]
                exact ledgerRoom_second circuits settings runLimit runs (.bottom b) q step n m b₁ b₂
                  (by omega) (by omega) hq)
            (padded_le circuits settings runLimit runs q step m (by omega) hq)
          rw [hj₂, hlen] at hbad₂
          rw [hε₂def]
          exact hbad₂
  have hmain := probEvent_bind_le_split (fun z => FirstWrong prims circuits D b s z ∧ ¬ GlobalEvent z.2)
    (fun _ => True) (ENNReal.ofReal ε₂) hz
  have hle := hmain.trans (add_le_add le_rfl (mul_le_of_le_one_left' (prEvent_le_one _)))
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨prEvent_ne_top _, ENNReal.ofReal_ne_top⟩) hle
  rw [ENNReal.toReal_add (prEvent_ne_top _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε₂] at hreal
  rw [(bottomSplit prims K circuits settings D net b s world n m hfuel htimed).prEvent_eq
    (fun r => r.1.2 = true ∧ ¬ GlobalEvent r.2)]
  have hfresh := bottomFresh_le (C := C) runLimit b
  have hk : (startBudget circuits settings runLimit C q).hiddenKeys = gameSetups runLimit := rfl
  rw [hk] at hbad₁
  unfold runError
  rw [← hb]
  push_cast
  unfold ceremonyFresh at hfresh hε₂def
  rw [hε₂def] at hreal
  linarith

/-! ## The run level -/

omit [DecidableEq E] in
/-- The bound of one run of a tree with `runError`, from the statements of the route. -/
theorem runBad_of_route (runs : 0 < runLimit) (hsize : 0 < settings.batchSize)
    (compute : CircuitsCompute circuits prims.Th)
    (bad : CeremonyBad prims K circuits settings runLimit)
    (top : TopCover prims K circuits settings)
    (fuel : HeadFuel circuits settings)
    (head : HeadCover prims K circuits settings)
    (cut : CutState prims K circuits settings)
    (dead : CutDead prims K circuits settings)
    (mono : CutMonotone prims K circuits settings)
    (rest : RestCover prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step : ℕ)
    (hstep : ∀ st sent, IsQueryBoundP (net.round st sent) Counted step)
    (hq : dkgTsigRounds circuits settings runLimit * step ≤ q)
    (tree : Tree) (s : RealState C net.State) (world : StreamState C)
    (ready : RunReady prims (startBudget circuits settings runLimit C q) D s world) (hP : HiddenProvenance D world)
    (flag : s.flag = false) :
    (Pr{let r ← (streamTreeRun prims K circuits settings D net tree s).run world}[
        r.1.2 = true ∧ ¬ GlobalEvent r.2]).toReal ≤ runError (E := E) circuits settings runLimit C q tree := by
  cases tree with
  | top =>
    exact runBad_top prims K circuits settings runLimit runs hsize compute bad top D net q step hstep hq s world
      ready hP flag
  | bottom b =>
    exact runBad_bottom prims K circuits settings runLimit runs hsize compute bad fuel head cut dead mono rest D net
      q step hstep hq b s world ready hP flag

omit [DecidableEq E] in
/-- The same bound from each start with `RunReadyL`, from the statements of the route with the
invariant `HiddenProvenance`. -/
theorem runHopL_of_route (runs : 0 < runLimit)
    (bad : ∀ prims, CeremonyBad prims K circuits settings runLimit)
    (top : ∀ prims, TopCover prims K circuits settings)
    (fuel : HeadFuel circuits settings)
    (head : ∀ prims, HeadCover prims K circuits settings)
    (cut : ∀ prims, CutState prims K circuits settings)
    (dead : ∀ prims, CutDead prims K circuits settings)
    (mono : ∀ prims, CutMonotone prims K circuits settings)
    (rest : ∀ prims, RestCover prims K circuits settings) :
    0 < settings.batchSize → ∀ prims, CircuitsCompute circuits prims.Th →
      ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
        ∀ (tree : Tree) (s : RealState C A.net.State) (world : StreamState C),
          RunReadyL prims (startBudget circuits settings runLimit C q) D s world → s.flag = false →
          (Pr{let r ← (streamTreeRun prims K circuits settings D A.net tree s).run world}[
              r.1.2 = true ∧ ¬ GlobalEvent r.2]).toReal ≤ runError (E := E) circuits settings runLimit C q tree := by
  intro hsize prims compute D A q bounded
  obtain ⟨start, step, forge, hsum, -, hround, -⟩ := id bounded
  have hstep : ∀ st sent, IsQueryBoundP (A.net.round st sent) Counted step := fun st sent =>
    isQueryBoundP_of_queryCostAtMost (hround st sent) fun _ ht =>
      one_le_ownCost (exists_inClass ht).choose_spec
  intro tree s world ready flag
  exact runBad_of_route prims K circuits settings runLimit runs hsize compute (bad prims) (top prims)
    fuel (head prims) (cut prims) (dead prims) (mono prims) (rest prims) D A.net q step hstep (by omega) tree s world
    ready.1 ready.2 flag


/-! ## The claim -/

omit [DecidableEq E] in
/-- `DkgCorrectness` with the error `part1Error`, in the form with the provenance of the hidden keys.
The game tests `RunReadyL` at each start of a run. The premises are the hops of the game over each
readiness test, `ReadyHopL`, `UsedHitHop`, and the statements of the route. -/
theorem part1L_of_route (usedHit : ℕ → ℝ)
    (flagFirst : ∀ prims, FlagFirstHopW prims K circuits settings runLimit)
    (seeds : ∀ prims, SeedsHopW prims K circuits settings runLimit)
    (runsUnion : ∀ prims, RunsUnionHopW prims K circuits settings runLimit)
    (ready : ∀ prims, ReadyHopL prims K circuits settings runLimit)
    (echo : ∀ prims, CollisionHopW prims K circuits settings runLimit EchoDomain (echoError runLimit C))
    (usedHitHop : ∀ prims, UsedHitHop prims K circuits settings runLimit usedHit)
    (reuse : ∀ prims, CollisionHopW prims K circuits settings runLimit DeriveDomain (reuseError runLimit C))
    (copy : ∀ prims, CollisionHopW prims K circuits settings runLimit CopyDomain (copyError settings runLimit C))
    (split : ∀ prims, CollisionHopW prims K circuits settings runLimit SplitHashDomain (splitError settings runLimit C))
    (bad : ∀ prims, CeremonyBad prims K circuits settings runLimit)
    (top : ∀ prims, TopCover prims K circuits settings)
    (fuel : HeadFuel circuits settings)
    (head : ∀ prims, HeadCover prims K circuits settings)
    (cut : ∀ prims, CutState prims K circuits settings)
    (dead : ∀ prims, CutDead prims K circuits settings)
    (mono : ∀ prims, CutMonotone prims K circuits settings)
    (rest : ∀ prims, RestCover prims K circuits settings) :
    Part1With K circuits settings runLimit (part1Error (E := E) circuits settings runLimit C usedHit) := by
  intro batch runs
  exact part1_of_hopsW K circuits settings runLimit usedHit
    (fun prims q D _ => RunReadyL prims (startBudget circuits settings runLimit C q) D)
    flagFirst seeds runsUnion ready echo usedHitHop reuse copy split
    (runHopL_of_route K circuits settings runLimit runs bad top fuel head cut dead mono rest) batch runs

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.runHopL_of_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.runHopL_of_route

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.part1L_of_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.part1L_of_route
