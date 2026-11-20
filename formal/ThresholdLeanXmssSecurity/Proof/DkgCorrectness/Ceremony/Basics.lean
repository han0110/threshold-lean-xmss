import ThresholdLeanXmss.Ideal
import ThresholdLeanXmss.Statement.Execution
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutRun
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RecordedRun
import ThresholdLeanXmssSecurity.Proof.Pilot.Final

/-!
# The facts of the old run level that the ceremony lemma uses

`CheckHop` bounds an accepted check from a start with the premises of the pilot, and
`checkHop_of_pilot` proves it from `pilotSound`. `SoundAt` is an accepted sound case at the joint
start of the check of batch `k`. `executePhaseR_erase` drops the records of a recorded phase. `KeysFresh` states that no PRSS
key of a start has a cell in the hidden cache, and `prReal_exists_finset_le` is the union bound over a
finite set.
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

/-! ## The bound of a check from the pilot -/

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget)

/-- The pilot with agreeing copies, with the budget of the game. -/
def CheckHop (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step : ℕ) : Prop :=
  ∀ c : CheckStart C net.State, SoundCase K circuits settings runLimit D q step c →
    (Pr{let out ← checkFrom prims K D net c}[∃ i, i ∉ D.1 ∧ out.1.2 i = some ()]).toReal ≤
      batchCheckError (E := E) circuits settings runLimit C q c.counts.sum

omit [Field E] [DecidableEq E] [Algebra Bit E] in
theorem batchCheckError_le_max {q count : ℕ} (h : count ∈ batchCounts circuits settings) :
    batchCheckError (E := E) circuits settings runLimit C q count ≤
      checkErrorMax (E := E) circuits settings runLimit C q :=
  (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.2 (Finset.le_sup (f := fun count =>
    (batchCheckError (E := E) circuits settings runLimit C q count).toNNReal) h))

/-- `CheckHop` holds by the pilot `pilotSound`. The budget of the check start bounds the error of the
pilot by `batchCheckError`. -/
theorem checkHop_of_pilot [SampleableType E] (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (q step : ℕ) (hstep : ∀ st sent, IsQueryBoundP (net.round st sent) Counted step) :
    CheckHop prims K circuits settings runLimit D net q step := by
  rintro c ⟨htuple, hwrong, hmv, hagree, hfresh, seen, expansionKeys, salts, split, hcache, hseen, hkeys, hsalts,
    hround, -⟩
  have h := pilotSound prims K D net step hstep c.keys c.prss c.counts c.x c.L c.tg c.st c.world.1 c.world.2 seen
    expansionKeys salts split htuple hwrong hmv hagree hfresh hcache
  have hlaw : Pr{let out ← checkFrom prims K D net c}[∃ i, i ∉ D.1 ∧ out.1.2 i = some ()] =
      Pr{let out ← pilotOutputs prims K D net c.keys c.prss c.counts c.x c.L c.tg c.st c.world.1 c.world.2}[
        ∃ i, i ∉ D.1 ∧ out.2 i = some ()] := by
    unfold checkFrom pilotOutputs
    rw [StateT.run'_eq, prEvent_map]
  rw [hlaw]
  refine h.trans ?_
  unfold splitBudget at hsalts
  unfold pilotSoundError batchCheckError pilotDigestError checkErrorOf soundHashError
  have h₁ : ((halvings c.counts.sum + 2) * (seen.card + checkRounds c.counts.sum * step) : ℕ) ≤
      (halvings c.counts.sum + 2) * (2 * q + 2 * gameCoinKeys circuits settings runLimit C) :=
    Nat.mul_le_mul_left _ hseen
  have h₂ : ((halvings c.counts.sum + 2) * (seen.card + checkRounds c.counts.sum * step + expansionKeys.card +
      halvings c.counts.sum + 2) : ℕ) ≤
      (halvings c.counts.sum + 2) * (2 * q + 4 * gameCoinKeys circuits settings runLimit C + halvings c.counts.sum + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₃ : (C.terms.length * (salts.card + 4 * checkRounds c.counts.sum * step + (C.n + 1) * C.terms.length) : ℕ) ≤
      C.terms.length * (6 * q + 2 * (gameBatches settings runLimit * termHashes C) + (C.n + 1) * C.terms.length) :=
    Nat.mul_le_mul_left _ (by rw [mul_assoc 4]; omega)
  have h₁' := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).2 h₁) (sq_nonneg (Fintype.card E : ℝ))
  have h₂' := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).2 h₂) (by positivity : (0 : ℝ) ≤ 2 ^ 256)
  have h₃' := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).2 h₃) (by positivity : (0 : ℝ) ≤ 2 ^ 256)
  linarith

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The program that stops at a check -/

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

variable (prims : Primitives) (runLimit : ℕ) (budget : StartBudget)

/-- An accepted sound case at the joint start of the check of batch `k`. -/
def SoundAt (D : C.Coalition) (q step : ℕ) {σ : Type}
    (r : Option (CheckStart C σ) × Option ((σ × (C.Party → Option Unit)) × StreamState C)) : Prop :=
  ∃ c out, r = (some c, some out) ∧ (∃ i, i ∉ D.1 ∧ out.1.2 i = some ()) ∧
    SoundCase K circuits settings runLimit D q step c

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives) (runLimit : ℕ)
  (budget : StartBudget)

/-! ## The honest output -/

/-- An honest operator has an output. -/
def HonestOutput (D : C.Coalition) {α : Type} (outputs : C.Party → Option α) : Prop :=
  ∃ i, i ∉ D.1 ∧ (outputs i).isSome

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## The ghost executor -/

section Ghost

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α R : Type}

theorem RStep.outbox_erase (s : RStep C E G α R) : s.erase.outbox = s.outbox := by
  cases s <;> rfl

theorem RStep.delivered_erase (s : RStep C E G α R) : s.erase.delivered = s.delivered := by
  rcases s with ⟨_ | _, _⟩ | _ | _ <;> rfl

theorem RStep.callInput_erase (s : RStep C E G α R) : s.erase.callInput = s.callInput := by
  cases s <;> rfl

theorem RStep.output_erase (s : RStep C E G α R) : s.erase.output = s.output := by
  cases s <;> rfl

end Ghost

section Execution

variable {C : Committee} {E : Type} {m : Type → Type} [Monad m] {I O L Rs Ia α ρ : Type}

/-- A program with its record dropped. -/
def dropRecord (program : OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) : PartyM C E (CallSpec I O) α :=
  OptionT.mk (Prod.fst <$> program)

/-! ## The erasure theorem -/

variable [LawfulMonad m]

theorem stepRoundR_erase (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs) (blank : ρ) (state : A.State)
    (steps : C.Party → RStep C E (CallSpec I O) α ρ) :
    stepRound Ro D A F state (fun i => (steps i).erase) =
      (fun r => (r.1, (fun i => (r.2.1 i).erase), r.2.2)) <$> stepRoundR Ro D A F blank state steps := by
  unfold stepRound stepRoundR
  simp only [RStep.callInput_erase, RStep.isDone_erase, RStep.outbox_erase, RStep.delivered_erase]
  split_ifs
  · simp only [map_bind, map_pure]
    refine bind_congr fun r => ?_
    rw [sequenceFin_map_bind (g := RStep.erase) (k := fun steps' => pure (r.1, steps', fun _ _ => none))]
    congr 2
    funext j
    cases hs : steps j with
    | done out record => simp [RStep.erase]
    | wait outbox resume => simp [RStep.erase]
    | call input resume =>
      simp only [RStep.erase]
      split_ifs
      · simp [RStep.erase]
      · rw [← advanceR_erase, hRo]
  · simp only [map_bind, map_pure]
    refine bind_congr fun r => ?_
    rw [sequenceFin_map_bind (g := RStep.erase) (k := fun steps' => pure (r.1, steps', r.2))]
    congr 2
    funext j
    cases hs : steps j with
    | done out record => simp [RStep.erase]
    | wait outbox resume =>
      simp only [RStep.erase]
      split_ifs
      · simp [RStep.erase]
      · rw [← advanceR_erase, hRo]
    | call input resume => simp [RStep.erase]

theorem executeRoundsR_erase (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs) (blank : ρ) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → RStep C E (CallSpec I O) α ρ),
    executeRounds Ro D A F fuel state (fun i => (steps i).erase) =
      (fun r => (r.1, fun i => (r.2 i).output)) <$> executeRoundsR Ro D A F blank fuel state steps
  | 0, state, steps => by simp [executeRounds, executeRoundsR, RStep.output_erase]
  | fuel + 1, state, steps => by
    simp only [executeRounds, executeRoundsR, RStep.isDone_erase]
    split_ifs
    · simp [RStep.output_erase]
    · rw [stepRoundR_erase Ro hRo, map_bind, bind_map_left]
      refine bind_congr fun r => ?_
      exact executeRoundsR_erase Ro hRo D A F blank fuel r.1 r.2.1

theorem startStepsR_erase (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (blank : ρ) (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) :
    startSteps Ro D (fun i => dropRecord (program i)) =
      (fun steps i => (steps i).erase) <$> startStepsR Ro D blank program := by
  unfold startSteps startStepsR
  have h : ∀ i : C.Party, (if i ∈ D.1 then pure (Step.done none) else Ro.honest (advance (dropRecord (program i)).run)) =
      ((if i ∈ D.1 then pure (RStep.done none blank) else Ro.honest (advanceR (program i))) >>=
        fun s => pure s.erase) := by
    intro i
    split_ifs
    · simp [RStep.erase]
    · rw [show (dropRecord (program i)).run = Prod.fst <$> program i from rfl, ← advanceR_erase, hRo,
        map_eq_bind_pure_comp]
      rfl
  simp only [h]
  rw [sequenceFin_bind_pure, map_eq_bind_pure_comp]
  rfl

/-- The erasure theorem. With the records dropped, the ghost run is `executePhase` of the programs
with their records dropped, with the same state of the adversary and the same fuel. It holds for
each roles whose honest role commutes with a map, so for `worldRoles` under each handler. -/
theorem executePhaseR_erase (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs) (blank : ρ) (fuel : ℕ)
    (state : A.State) (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) :
    executePhase Ro D A F fuel state (fun i => dropRecord (program i)) =
      (fun r => (r.1, fun i => (r.2 i).output)) <$> executePhaseR Ro D A F blank fuel state program := by
  unfold executePhase executePhaseR
  rw [startStepsR_erase Ro hRo, bind_map_left, map_bind]
  exact bind_congr fun steps => executeRoundsR_erase Ro hRo D A F blank fuel state steps

end Execution

/-! ## The keys of the hidden names -/

section Run

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives) (runLimit : ℕ)
  (budget : StartBudget)

/-- Operator `i` holds `key` under the hidden-capable name `name` with the PRSS keys `prss`. -/
def NameKey (i : C.Party) (prss : PrssKeys C) (name : KeyName C) (key : HashOutput) : Prop :=
  (∃ T, i ∈ C.holders T ∧ name = .term T ∧ key = prss.term T) ∨
    ∃ j, ∃ h : j ≠ i, name = .pair (C.pairOf i j (Ne.symm h)) ∧ key = prss.pair j

/-- No PRSS key of a joint start under a hidden name has a stream cell in the hidden cache `hidden`
of the start of the run. -/
def KeysFresh (D : C.Coalition) (hidden : HiddenCache C) {σ : Type} (c : CheckStart C σ) : Prop :=
  ∀ i, i ∉ D.1 → ∀ name key, NameKey i (c.prss i) name key → Hidden D name →
    ∀ ρ idx position, hidden ((name, key), ρ, idx, position) = none

/-! ## A union bound over a finite set -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem prReal_exists_finset_le {α : Type} (mx : ProbComp α) (t : Finset ℕ) (p : ℕ → α → Prop) :
    (Pr{let a ← mx}[∃ k ∈ t, p k a]).toReal ≤ ∑ k ∈ t, (Pr{let a ← mx}[p k a]).toReal := by
  rw [← ENNReal.toReal_sum fun k _ => prEvent_ne_top _]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun k _ => prEvent_ne_top _) (prEvent_exists_finset_le t mx p)

end Run

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## Programs that reach a round -/

section Programs

variable {ι : Type} {G : OracleSpec ι}

/-- Local work in the local oracles before the round keeps the property. -/
theorem startsWithRound_localStep_bind {α β : Type} (oa : OracleComp (LocalSpec C) β)
    (f : β → PartyM C E G α) (h : ∀ b, StartsWithRound (f b)) :
    StartsWithRound (localStep oa >>= f) := by
  intro step hs
  rw [advance_localStep_bind, mem_support_bind_iff] at hs
  obtain ⟨b, -, hb⟩ := hs
  exact h b step hb

/-- A step that the honest roles of the real game give for the local work of a program, under a
handler of `WorldSpec` with a state, is a step of the plain program. So `StartsWithRound` holds for
the steps under each such handler. -/
theorem mem_support_advance_of_handler {α σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (p : PartyM C E G α) (s : σ) (step : Step C E G α)
    (hs : step ∈ support ((simulateQ impl (worldRoles.honest (advance p.run))).run' s)) :
    step ∈ support (advance p.run) :=
  support_simulateQ_subset _ _ (support_simulateQ_run'_subset impl _ s hs)

end Programs

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.checkHop_of_pilot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.checkHop_of_pilot

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.executePhaseR_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.executePhaseR_erase
