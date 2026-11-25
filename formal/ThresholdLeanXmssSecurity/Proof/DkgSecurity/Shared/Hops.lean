import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Events
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.ReductionCost
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Game

/-!
# The hops with the shared bad event and the field `dkgSecurityPreservation`

Each game of the chain runs in `loggedWorld` with recorded runs and gives the win, the flag of the
shared event and, after the seed generation of the simulator, the data of the dealer. The hops
compare the event "win and no flag". The flag is paid one time, in the first game, at `flagError`,
which has one check term for each run. The first hit is paid one time, in the game with no emulated
run. A step of the privacy of the runs has only the slack of a hash collision.

Each hop is a named `Prop`. `MonitorErase` and `TableHop` are the hops at the two ends of the chain.
`zeroRuns` proves `ZeroRuns`, the case with no run. `dkgSecurityPreservation_of_shared` gives the field from the
hops and from the inequality between `sharedError` and the approved `dkgError`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The hops at the ends of the chain -/

/-- The stream-key event of `dkgTsigGame` is at most as likely as the one of `dkgTreeGame`. The two
games differ in the monitor and in the component of the result. The monitor calls `.prf` and `.hash`
on the free copy, and `UsedHit` reads the stream-key cells and the hidden keys. -/
def MonitorErase : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    usedHitProb prims D (dkgTsigGame K circuits settings runLimit D A) ≤
      usedHitProb prims D (dkgTreeGame K circuits settings runLimit D A)

/-- The error of the flag of `dkgTreeGame` in `streamWorld`. It is `dkgCorrectnessError` with no
`setupHybridError`. -/
def flagError (C : Committee) (q : ℕ) : ℝ :=
  seedGenHashError C q + echoError runLimit C q + reuseError runLimit C q + copyError settings runLimit C q +
    splitError settings runLimit C q +
    runLimit * (runError (E := E) circuits settings runLimit C q .top +
      ∑ b : Fin (2 ^ layerHeight), runError (E := E) circuits settings runLimit C q (.bottom b))

/-- The forger. `dealtGame` with each run emulated wins at most as often as the forger `dkgReduction`
wins `tsigGame`. The dealer moves to the start, the setup domains move to the table of the forger,
and the hidden streams move to its cache. -/
def TableHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) ≤
      accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A))

/-- With no run the adversary never wins. -/
def ZeroRuns : Prop :=
  runLimit = 0 → ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    accepts prims (dkgTsigGame K circuits settings runLimit D A) = 0

/-! ## The trees -/

section Runs

variable {prims K circuits settings runLimit}

/-- The trees. -/
def allTrees : List Tree := .top :: (List.finRange (2 ^ layerHeight)).map .bottom

/-- Each run of the trees of `trees` is emulated. -/
def raised (runLimit : ℕ) (trees : List Tree) : Tree → ℕ := fun t => if t ∈ trees then runLimit else 0

theorem allTrees_nodup : (allTrees).Nodup := by
  refine List.nodup_cons.mpr ⟨by simp [List.mem_map], ?_⟩
  exact (List.nodup_finRange _).map fun a b h => by cases h; rfl

theorem raised_allTrees (runLimit : ℕ) : raised runLimit allTrees = fun _ => runLimit := by
  funext t
  cases t with
  | top => simp [raised, allTrees]
  | bottom b => simp [raised, allTrees]

private theorem sum_cons_finRange {n : ℕ} (head : Tree) (g : Fin n → Tree) (f : Tree → ℝ) :
    ((head :: (List.finRange n).map g).map f).sum = f head + ∑ i, f (g i) := by
  simp [List.map_map, Fin.sum_univ_def, Function.comp_def]

theorem allTrees_sum (f : Tree → ℝ) :
    (allTrees.map f).sum = f .top + ∑ b : Fin (2 ^ layerHeight), f (.bottom b) := by
  unfold allTrees
  exact sum_cons_finRange .top .bottom f

end Runs

omit [Field E] [DecidableEq E] [Algebra Bit E] in
theorem flagError_add_setupHybridError (q : ℕ) :
    flagError (E := E) circuits settings runLimit C q + setupHybridError runLimit C q =
      dkgCorrectnessError (E := E) circuits settings runLimit C q := by
  unfold flagError setupHybridError dkgCorrectnessError
  ring

/-! ## The run limit 0 -/

/-- No operator holds a top tree at the start of the game. -/
theorem topHolder_startState {σ : Type} (D : C.Coalition) (state : σ) (keys : C.Party → Option (Keys C)) :
    topHolder D (startState D state keys).operators = none := by
  unfold topHolder
  rw [List.find?_eq_none.mpr (by simp [startState])]

/-- No operator holds a top tree after the vote of the seed generation. -/
theorem topHolder_seedState {σ : Type} (D : C.Coalition) (state : σ) (keys : C.Party → Option (Keys C))
    (ok : Bool) : topHolder D (seedState D state keys ok).operators = none :=
  topHolder_startState D state (committed ok keys)

/-- A game that ends with `false` never accepts. -/
theorem accepts_bind_false {α : Type} (X : OracleComp (WorldSpec C) α) :
    accepts prims (X >>= fun _ => (pure false : OracleComp (WorldSpec C) Bool)) = 0 := by
  unfold accepts runWorld
  rw [ENNReal.toReal_eq_zero_iff]
  left
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_
  simp only [simulateQ_bind, simulateQ_pure] at hr
  simp at hr
  erw [support_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  simp

omit [Fintype E] [DecidableEq E] in
/-- With no run the adversary never wins. -/
theorem zeroRuns [Fintype E] [DecidableEq E] : ZeroRuns prims K circuits settings runLimit := by
  intro h0 D A
  subst h0
  have hgame : dkgTsigGame K circuits settings 0 D A =
      (realExecution D A.net noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [] >>= fun r =>
          voteRound worldRoles D A.net r.1 fun i => (r.2 i).map seedVote) >>= fun _ =>
          (pure false : OracleComp (WorldSpec C) Bool) := by
    simp [dkgTsigGame, dkgTsigRun, treeRuns, dkgSigning, topHolder_seedState]
  rw [hgame]
  exact accepts_bind_false prims _

/-! ## The hops -/

/-- The records and the log change no result. `dkgTsigGame` in `streamWorld` wins as often as the
real game with the shared event. -/
def SharedStart : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (dkgTsigGame K circuits settings runLimit D A) =
      realProb prims K circuits settings runLimit true D A fun r => r.1 = true

/-- The bound of the shared event in the real game. The flag is the seeds, a bad check of a run in
its records, a reused hidden key, or a global event. Each of them has its term in `flagError`, and a
bad check has one term for each batch of each run. No premise is on an output of an honest
operator. -/
def SharedBadBound : Prop :=
  0 < settings.batchSize → 0 < runLimit → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      realProb prims K circuits settings runLimit true D A (fun r => r.2 = true) ≤
        flagError (E := E) circuits settings runLimit C q

/-- The answers of the dealer with the shared event. With no flag each kept output is the output of
`referenceTree`, because a wrong output of a run needs a bad check in its records. The flag has no
monitor of the outputs. So the hop needs a positive batch size and circuits that compute `Th`. With
the batch size 0 a run has no check and gives an output that is not the reference output. -/
def SharedRefDealer : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
      realProb prims K circuits settings runLimit true D A Clean ≤
        realProb prims K circuits settings runLimit false D A Clean

/-- The budget of the table adversary with the distinguisher `tableRestShared`. -/
def SharedSeedBound : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    IsQueryBounded (tableNet prims A.net) (tableRestShared prims K circuits settings runLimit D A) setupRounds q

/-- The real end of the seed generation claim, with the shared event. -/
def SharedSeedReal : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    accepts prims (distinguish (realExecution D (tableNet prims A.net) noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])
        (tableRestShared prims K circuits settings runLimit D A)) =
      realProb prims K circuits settings runLimit false D A Clean

/-- The ideal end of the seed generation claim, with the shared event. -/
def SharedSeedIdeal : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    accepts prims (distinguish (idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D (tableNet prims A.net))
        (fun _ => ()) []) (tableRestShared prims K circuits settings runLimit D A)) =
      dealtProb prims K circuits settings runLimit Mode.real D A fun r => Clean r.1.1

/-- No run after a failed search of the dealer, with the shared event. -/
def SharedSearch : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    dealtProb prims K circuits settings runLimit Mode.real D A (fun r => Clean r.1.1) ≤
      dealtProb prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (fun r => Clean r.1.1) +
        2 ^ layerHeight * searchFailure

/-- The bound of a first hit, one time, in the game with no emulated run. -/
def SharedHit (hit : ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    dealtProb prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (HitOf D) ≤ hit q

/-- The privacy of one run with the shared event. The next real run of `tree` becomes an emulated
run. With no flag and no first hit the two games give the adversary the same view. The error
`slack tree q` is for a collision of a history or digest cell of a hidden term that only one of the
two runs makes, because the two runs hash different histories of the hidden terms. -/
def SharedStep (slack : Tree → ℕ → ℝ) : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      ∀ (level : Tree → ℕ) (tree : Tree), level tree < runLimit →
        dealtProb prims K circuits settings runLimit ⟨true, level⟩ D A (CleanNoHit D) ≤
          dealtProb prims K circuits settings runLimit ⟨true, Function.update level tree (level tree + 1)⟩ D A
            (CleanNoHit D) + slack tree q

/-- The records and the log change no result in the last game. -/
def SharedEnd : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    dealtProb prims K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A (fun r => r.1.1.1 = true) =
      streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A)

/-! ## The sum over the runs, for each function of the level -/

section Levels

variable {runLimit}

theorem level_tree (f : (Tree → ℕ) → ℝ) (ε : Tree → ℝ)
    (step : ∀ (level : Tree → ℕ) (tree : Tree), level tree < runLimit →
      f level ≤ f (Function.update level tree (level tree + 1)) + ε tree)
    (level : Tree → ℕ) (tree : Tree) : ∀ n : ℕ, level tree + n ≤ runLimit →
      f level ≤ f (Function.update level tree (level tree + n)) + n * ε tree
  | 0, _ => by simp
  | n + 1, h => by
    have ih := level_tree f ε step level tree n (by omega)
    have hs := step (Function.update level tree (level tree + n)) tree (by rw [Function.update_self]; omega)
    rw [Function.update_idem, Function.update_self] at hs
    have e : level tree + n + 1 = level tree + (n + 1) := by omega
    rw [e] at hs
    push_cast
    linarith

theorem level_trees (f : (Tree → ℕ) → ℝ) (ε : Tree → ℝ)
    (step : ∀ (level : Tree → ℕ) (tree : Tree), level tree < runLimit →
      f level ≤ f (Function.update level tree (level tree + 1)) + ε tree) :
    ∀ trees : List Tree, trees.Nodup →
      f (fun _ => 0) ≤ f (raised runLimit trees) + (trees.map fun t => runLimit * ε t).sum
  | [], _ => by
    have e : raised runLimit ([] : List Tree) = fun _ => 0 := by funext t; simp [raised]
    rw [e]
    simp
  | t :: trees, h => by
    have ih := level_trees f ε step trees (List.nodup_cons.mp h).2
    have hnot : t ∉ trees := (List.nodup_cons.mp h).1
    have ht : raised runLimit trees t = 0 := by simp [raised, hnot]
    have hs := level_tree f ε step (raised runLimit trees) t runLimit (by omega)
    have e : Function.update (raised runLimit trees) t (raised runLimit trees t + runLimit) =
        raised runLimit (t :: trees) := by
      funext x
      by_cases hx : x = t
      · subst hx; simp [raised, hnot]
      · simp [raised, hx]
    rw [e] at hs
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- The last level from the first, with the error of each run of each tree. -/
theorem level_all (f : (Tree → ℕ) → ℝ) (ε : Tree → ℝ)
    (step : ∀ (level : Tree → ℕ) (tree : Tree), level tree < runLimit →
      f level ≤ f (Function.update level tree (level tree + 1)) + ε tree) :
    f (fun _ => 0) ≤ f (fun _ => runLimit) + runLimit * (ε .top + ∑ b : Fin (2 ^ layerHeight), ε (.bottom b)) := by
  have h := level_trees f ε step allTrees allTrees_nodup
  rw [raised_allTrees, allTrees_sum (fun t => (runLimit : ℝ) * ε t)] at h
  rw [mul_add, Finset.mul_sum]
  exact h

end Levels

/-! ## Covers of events -/

/-- An event that two events cover is at most as likely as their sum. -/
theorem prReal_cover {α : Type} (mx : ProbComp α) (p q r : α → Prop) (h : ∀ a, p a → q a ∨ r a) :
    (Pr{let a ← mx}[p a]).toReal ≤ (Pr{let a ← mx}[q a]).toReal + (Pr{let a ← mx}[r a]).toReal :=
  (prReal_mono mx p (fun a => q a ∨ r a) fun a _ => h a).trans (prReal_or_le mx q r)

omit [Fintype E] [DecidableEq E] in
theorem realProb_cover (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) (p q r : Bool × Bool → Prop)
    (h : ∀ a, p a → q a ∨ r a) :
    realProb prims K circuits settings runLimit own D A p ≤
      realProb prims K circuits settings runLimit own D A q + realProb prims K circuits settings runLimit own D A r :=
  prReal_cover ((sharedReal prims K circuits settings runLimit own D A).run ((∅, ∅), []))
    (fun x : (Bool × Bool) × LogState C => p x.1) (fun x => q x.1) (fun x => r x.1) fun a => h a.1

omit [Fintype E] [DecidableEq E] in
theorem dealtProb_cover (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (p q r : DealtOut C × LogState C → Prop) (h : ∀ a, p a → q a ∨ r a) :
    dealtProb prims K circuits settings runLimit m D A p ≤
      dealtProb prims K circuits settings runLimit m D A q + dealtProb prims K circuits settings runLimit m D A r :=
  prReal_cover _ p q r h

omit [Fintype E] [DecidableEq E] in
theorem dealtProb_mono (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (p q : DealtOut C × LogState C → Prop) (h : ∀ a, p a → q a) :
    dealtProb prims K circuits settings runLimit m D A p ≤ dealtProb prims K circuits settings runLimit m D A q :=
  prReal_mono _ p q fun a _ => h a

/-! ## The glue -/

/-- The error of the hops with the shared event. It has `dkgCorrectnessError` one time, so one check
term for each run, the bound `hit q` of a first hit one time, and the slack of each step. -/
def sharedError (hit : ℕ → ℝ) (slack : Tree → ℕ → ℝ) (C : Committee) (q : ℕ) : ℝ :=
  dkgCorrectnessError (E := E) circuits settings runLimit C q + seedGenHashError C q +
    2 ^ layerHeight * searchFailure + hit q +
    runLimit * (slack .top q + ∑ b : Fin (2 ^ layerHeight), slack (.bottom b) q)

omit [DecidableEq E] in
/-- The bound of the second conjunct of `DkgSecurityPreservation` with the error `sharedError`, for a positive run
limit. -/
theorem secondConjunct_of_shared (hit : ℕ → ℝ) (slack : Tree → ℕ → ℝ)
    (monitor : MonitorErase prims K circuits settings runLimit)
    (usedHit : UsedHitHop prims K circuits settings runLimit (setupHybridError runLimit C))
    (start : SharedStart prims K circuits settings runLimit)
    (bad : SharedBadBound prims K circuits settings runLimit)
    (ref : SharedRefDealer prims K circuits settings runLimit)
    (seedBound : SharedSeedBound prims K circuits settings runLimit)
    (seedReal : SharedSeedReal prims K circuits settings runLimit)
    (seedIdeal : SharedSeedIdeal prims K circuits settings runLimit)
    (search : SharedSearch prims K circuits settings runLimit)
    (hits : SharedHit prims K circuits settings runLimit hit)
    (step : SharedStep prims K circuits settings runLimit slack)
    (finish : SharedEnd prims K circuits settings runLimit)
    (table : TableHop prims K circuits settings runLimit)
    (batch : 0 < settings.batchSize) (runs : 0 < runLimit) (compute : CircuitsCompute circuits prims.Th)
    (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ) (bounded : DkgTsigBounded circuits settings runLimit A q) :
    accepts prims (dkgTsigGame K circuits settings runLimit D A) ≤
      accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A)) +
        sharedError (E := E) circuits settings runLimit hit slack C q +
        streamAdvantage prims D (dkgTsigGame K circuits settings runLimit D A) := by
  have h₀ : accepts prims (dkgTsigGame K circuits settings runLimit D A) ≤
      streamAccepts prims D (dkgTsigGame K circuits settings runLimit D A) +
        probBad_streamKey prims D (dkgTsigGame K circuits settings runLimit D A) +
        streamAdvantage prims D (dkgTsigGame K circuits settings runLimit D A) :=
    streamHop prims D (dkgTsigGame K circuits settings runLimit D A)
  have h₁ : probBad_streamKey prims D (dkgTsigGame K circuits settings runLimit D A) ≤
      setupHybridError runLimit C q :=
    ((probBad_streamKey_le_usedHit prims D (dkgTsigGame K circuits settings runLimit D A)).trans
      (monitor D A)).trans (usedHit D A q bounded)
  have h₂ := start D A
  have h₃ := realProb_cover prims K circuits settings runLimit true D A (fun r => r.1 = true) Clean
    (fun r => r.2 = true) fun r hr => by
      by_cases hb : r.2 = true
      · exact Or.inr hb
      · exact Or.inl ⟨hr, by simpa using hb⟩
  have h₄ := bad batch runs compute D A q bounded
  have h₅ := ref batch compute D A
  have hseed := (seedGenSecurity (C := C) (E := E) prims) D (tableNet prims A.net) (fun _ => ()) []
    (tableRestShared prims K circuits settings runLimit D A) q trivial (seedBound D A q bounded)
  have h₆ : realProb prims K circuits settings runLimit false D A Clean -
      dealtProb prims K circuits settings runLimit Mode.real D A (fun r => Clean r.1.1) ≤ seedGenHashError C q := by
    rw [← seedReal D A, ← seedIdeal D A]
    exact (abs_le.mp hseed.2).2
  have h₇ := search D A
  have h₈ := dealtProb_cover prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (fun r => Clean r.1.1)
    (CleanNoHit D) (HitOf D) fun r hr => by
      by_cases hh : HitOf D r
      · exact Or.inr hh
      · exact Or.inl ⟨hr, hh⟩
  have h₉ := hits D A q bounded
  have h₁₀ := level_all (runLimit := runLimit)
    (fun level => dealtProb prims K circuits settings runLimit ⟨true, level⟩ D A (CleanNoHit D))
    (fun tree => slack tree q) (fun level tree hl => step batch compute D A q bounded level tree hl)
  have h₁₁ := dealtProb_mono prims K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A (CleanNoHit D)
    (fun r => r.1.1.1 = true) fun r hr => hr.1.1
  have h₁₂ := finish D A
  have h₁₃ := table D A
  have hsum := flagError_add_setupHybridError (E := E) circuits settings runLimit (C := C) q
  unfold sharedError
  linarith

omit [Field E] [Algebra Bit E] [DecidableEq E] in
/-- The error of `DkgSecurityPreservation` is not negative. -/
theorem dkgError_nonneg (C : Committee) (q : ℕ) : 0 ≤ dkgError (E := E) circuits settings runLimit C q := by
  have hsearch : 0 ≤ searchFailure := by
    rw [← toReal_failure]
    exact ENNReal.toReal_nonneg
  have hrun : ∀ tree, 0 ≤ runError (E := E) circuits settings runLimit C q tree := fun tree =>
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (checkErrorMax_nonneg circuits settings runLimit q))
      (by unfold freshError; positivity)
  have hsum : 0 ≤ ∑ b : Fin (2 ^ layerHeight), runError (E := E) circuits settings runLimit C q (.bottom b) :=
    Finset.sum_nonneg fun b _ => hrun _
  have htop := hrun .top
  have hsplit : 0 ≤ splitError settings runLimit C q := splitRisk_nonneg _ _
  have hcorrect : 0 ≤ dkgCorrectnessError (E := E) circuits settings runLimit C q := by
    unfold dkgCorrectnessError seedGenHashError prssSetupHashError freshKeyError prssRandHashError echoError
      reuseError copyError
    positivity
  unfold dkgError privacyHitError privacyStepError seedGenHashError copyError
  positivity

omit [DecidableEq E] in
/-- The field `dkgSecurityPreservation` from the hops with the shared event and from the inequality between the
error of these hops and the approved error. -/
theorem dkgSecurityPreservation_of_shared (hit : ℕ → ℝ) (slack : Tree → ℕ → ℝ)
    (monitor : MonitorErase prims K circuits settings runLimit)
    (usedHit : UsedHitHop prims K circuits settings runLimit (setupHybridError runLimit C))
    (start : SharedStart prims K circuits settings runLimit)
    (bad : SharedBadBound prims K circuits settings runLimit)
    (ref : SharedRefDealer prims K circuits settings runLimit)
    (seedBound : SharedSeedBound prims K circuits settings runLimit)
    (seedReal : SharedSeedReal prims K circuits settings runLimit)
    (seedIdeal : SharedSeedIdeal prims K circuits settings runLimit)
    (search : SharedSearch prims K circuits settings runLimit)
    (hits : SharedHit prims K circuits settings runLimit hit)
    (step : SharedStep prims K circuits settings runLimit slack)
    (finish : SharedEnd prims K circuits settings runLimit)
    (table : TableHop prims K circuits settings runLimit)
    (gap : 0 < runLimit → ∀ q : ℕ, sharedError (E := E) circuits settings runLimit hit slack C q ≤
      dkgError (E := E) circuits settings runLimit C q) :
    CircuitsCompute circuits prims.Th →
      DkgSecurityPreservation prims K circuits settings runLimit (dkgReduction K circuits settings runLimit) := by
  intro compute batch D A q bounded
  refine ⟨dkgReduction_cost prims K circuits settings runLimit batch D A q bounded, ?_⟩
  rcases Nat.eq_zero_or_pos runLimit with h0 | runs
  · rw [zeroRuns prims K circuits settings runLimit h0 D A]
    have herr := dkgError_nonneg (E := E) circuits settings runLimit C q
    have hacc : 0 ≤ accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A)) :=
      ENNReal.toReal_nonneg
    have hadv : 0 ≤ streamAdvantage prims D (dkgTsigGame K circuits settings runLimit D A) :=
      ENNReal.toReal_nonneg
    linarith
  · have h := secondConjunct_of_shared prims K circuits settings runLimit hit slack monitor usedHit start bad ref
      seedBound seedReal seedIdeal search hits step finish table batch runs compute D A q bounded
    have hg := gap runs q
    linarith

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.zeroRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.zeroRuns

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dkgSecurityPreservation_of_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dkgSecurityPreservation_of_shared
