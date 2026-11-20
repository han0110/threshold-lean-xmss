import ThresholdLeanXmssSecurity.Proof.Check

/-!
# The check on one shared cache

`mapRoles` runs both network roles through one oracle implementation, and
`simulateQ_executePhase_mapRoles` moves an oracle implementation through a whole phase. `mapRoles_world`
lets the counted and the free copy answer from one cache. `checkRealRun` is the real run of the check
on the shared cache, and `CheckSoundStage` states the soundness step of the check as a named `Prop`.
When the honest copies agree but a tuple is wrong, an honest operator of the real run outputs with
probability at most the soundness error plus the coin-key collisions.
-/

noncomputable section

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

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
    simp only [simulateQ_pure, simulateQ_bind]
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

end Zero

/-! ## Assembly -/

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [DecidableEq E] [SampleableType E] in
lemma checkErrorOf_nonneg (K : Constants C E) (d R q : ℕ) : 0 ≤ checkErrorOf (E := E) d R q := by
  have hc : (2 : ℝ) < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  unfold checkErrorOf
  have h1 : (0 : ℝ) < Fintype.card E - 2 := by linarith
  positivity

end Assembly

end ThresholdLeanXmssSecurity

end

noncomputable section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## The masked real run -/

section Masked

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The real run of the check on the shared cache, before the distinguisher. -/
def checkRealRun (K : Constants C E) (fuel : ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option Unit)) := do
  let st ← A.start (corruptInputs D x) z
  executePhase localRoles D A (checkFunctionalities K) fuel st fun i => checkProtocol K i (x i)

/-- The honest holders agree on every copy, the first conjunct of the accept bit of `F_multVerify`. -/
def MultVerifyAgree (D : C.Coalition) (inputs : C.Party → Option (List (Tuple C))) : Prop :=
  ∀ k < (firstInput inputs).length, ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 →
    ∀ g < (((List.range (firstInput inputs).length).map (tupleAt inputs)).getD k
        ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count,
      ((inputs i).bind (·[k]?)).map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) =
        ((inputs j).bind (·[k]?)).map fun τ => (τ.x T g, τ.y T g, τ.z T g)

end Masked

/-! ## The hash budget -/

section Budget

variable {C : Committee}

lemma soundHashError_nonneg (count q : ℕ) : 0 ≤ soundHashError count q := by
  unfold soundHashError; positivity

end Budget

/-! ## The soundness stage -/

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- When the honest copies agree but a tuple is wrong, an honest operator of the real run
outputs with probability at most the soundness error of GS20, Lemmas 8 to 10, plus the coin-key
collisions. -/
def CheckSoundStage (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) (q : ℕ),
    TupleInputs K counts D x → IsQueryBounded A Z (checkRounds counts.sum) q →
    counts.sum ≠ 0 → q < 2 ^ 128 →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 = false →
    (Pr{let r ←
      (simulateQ (localAnswer prims) (checkRealRun K (checkRounds counts.sum) D A x z)).run' ∅}[∃ i, i ∉ D.1 ∧ r.2 i = some ()]).toReal ≤
      checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q + soundHashError counts.sum q

end Assembly

end ThresholdLeanXmssSecurity

end

/-- info: 'ThresholdLeanXmssSecurity.simulateQ_executePhase_mapRoles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.simulateQ_executePhase_mapRoles
