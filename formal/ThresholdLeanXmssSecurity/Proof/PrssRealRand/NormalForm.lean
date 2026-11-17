import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.PhaseQuiet
import ThresholdLeanXmssSecurity.Proof.PrssRand.Runs
import ThresholdLeanXmssSecurity.Proof.SeedGenGames

/-!
# The normal form of one PRSS setup with the calls of `Rand`

`prssRealRandProtocol` runs `prssSetup` and then the public list `calls` of `Rand`. Its real run is
the run of the setup, then the draws `liveStreams` of the live honest operators on the outputs.

* `executePhase_prssRealRand` is the normal form from every state of the adversary and for every
  functionality.
* `realExecution_prssRealRand` is the normal form of `realExecution`.
* `distinguish_prssRealRand` is the normal form of the game with `Z`.

Each one is an equation of programs of `OracleComp (WorldSpec C)`. So it holds under each handler
(`simulateQ_prssRealRand`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Carrier

variable {C : Committee} {E : Type}

/-- The run of `prssSetup` is the run of the carrier setup under `carrierPrssKeys`, from every state
of the adversary. This is `realExecution_prssSetup` at `executePhase`. -/
theorem executePhase_prssSetup {Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty PEmpty L R) (st : A.State) :
    executePhase worldRoles D A F setupRounds st (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) =
      (fun r => (r.1, fun i => (r.2 i).map carrierPrssKeys)) <$> executePhase worldRoles D A F setupRounds st
        (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) := by
  unfold executePhase
  simp only [map_bind, prssSetup_eq_map]
  rw [startSteps_map worldRoles worldRoles_honest_map, bind_map_left]
  refine bind_congr fun steps => ?_
  exact executeRounds_map worldRoles worldRoles_honest_map D A F carrierPrssKeys setupRounds st steps

end Carrier

section Draws

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The draws of the calls of each live honest operator, from its own keys, one operator after the
other. A corrupt operator and an operator with no output draw nothing. -/
def liveStreams (K : Constants C E)
    (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit)) (D : C.Coalition)
    (out : C.Party → Option (Keys C)) (label : ℕ) (calls : List RandCall) :
    OracleComp (LocalSpec C) (C.Party → Option (List (RandOutput C E))) :=
  OverPermutation.sequenceFin fun j => if j ∈ D.1 then pure none else
    match out j with
    | some k => some <$> liftComp (randStreams K bits (carrierPrssKeys k) j label calls) (LocalSpec C)
    | none => pure none

end Draws

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)

/-- A phase with no round of the calls of `Rand` is the draws of the live honest operators. The state
of the adversary does not change. -/
theorem executePhase_randCalls {Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty PEmpty L R) (label : ℕ) (calls : List RandCall) (st : A.State)
    (out : C.Party → Option (Keys C)) :
    executePhase worldRoles D A F 0 st (fun i => (out i).elim failure fun keys =>
        ((calls.mapM (randCall K { localContext i with prss := carrierPrssKeys keys })).run' ⟨fun _ => [], label, 0⟩ :
          PartyM C E RealSpec (List (RandOutput C E)))) =
      (fun streams => (st, streams)) <$> free (liveStreams K prgBits D out label calls) := by
  have hstep : ∀ i : C.Party,
      (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance ((out i).elim failure fun keys =>
        ((calls.mapM (randCall K { localContext i with prss := carrierPrssKeys keys })).run' ⟨fun _ => [], label, 0⟩ :
          PartyM C E RealSpec (List (RandOutput C E)))).run)) =
      free (if i ∈ D.1 then pure none else
        match out i with
        | some k => some <$> liftComp (randStreams K prgBits (carrierPrssKeys k) i label calls) (LocalSpec C)
        | none => pure none) >>= fun o => pure (Step.done o) := fun i => by
    by_cases hi : i ∈ D.1
    · simp only [hi, ↓reduceIte, free_pure, pure_bind]
    · cases ho : out i with
      | none => simp only [hi, ↓reduceIte, worldRoles, Option.elim_none, advance_run_failure, free_pure, pure_bind]
      | some keys =>
        simp only [hi, ↓reduceIte, worldRoles, Option.elim_some]
        rw [advance_randCalls]
        simp only [map_eq_bind_pure_comp, free_bind, free_pure, bind_assoc, pure_bind, Function.comp_def]
        rfl
  unfold executePhase startSteps liveStreams
  rw [free_sequenceFin, funext hstep, sequenceFin_bind_pure]
  simp only [executeRounds, bind_assoc, pure_bind, Step.output, map_eq_bind_pure_comp, Function.comp_def]

/-- The normal form from every state of the adversary. A run of the PRSS setup with the calls of `Rand` is the
run of the setup, then the draws of the live honest operators from their own outputs, one operator
after the other. -/
theorem executePhase_prssRealRand {Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty PEmpty L R) (label : ℕ) (calls : List RandCall) (st : A.State) :
    executePhase worldRoles D A F setupRounds st (fun i => prssRealRandProtocol K label calls i ()) =
      executePhase worldRoles D A F setupRounds st
          (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) >>= fun r =>
        (fun streams => (r.1, streams)) <$> free (liveStreams K prgBits D r.2 label calls) := by
  have h := executePhase_bind_eq D A F setupRounds 0 st
    (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C)))
    (fun i keys => ((calls.mapM (randCall K { localContext i with prss := carrierPrssKeys keys })).run'
      ⟨fun _ => [], label, 0⟩ : PartyM C E RealSpec (List (RandOutput C E))))
    (fun i _ => timedQuiet_setupKeys .prss i)
  have hprog : (fun i : C.Party => prssRealRandProtocol K label calls i ()) =
      fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun keys =>
        ((calls.mapM (randCall K { localContext i with prss := carrierPrssKeys keys })).run'
          ⟨fun _ => [], label, 0⟩ : PartyM C E RealSpec (List (RandOutput C E))) :=
    funext fun i => by rw [prssRealRandProtocol, prssSetup_eq_map, bind_map_left]
  rw [hprog]
  refine h.trans (bind_congr fun r => ?_)
  exact executePhase_randCalls K D A F label calls r.1 r.2

/-- The real run of the PRSS setup with the calls of `Rand` is the real run of the setup,
then `liveStreams` of its outputs. -/
theorem realExecution_prssRealRand (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    realExecution D A noFunctionality setupRounds (prssRealRandProtocol K label calls) x z =
      realExecution D A noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z >>= fun r =>
        (fun streams => (r.1, streams)) <$> free (liveStreams K prgBits D r.2 label calls) := by
  unfold realExecution
  rw [bind_assoc]
  exact bind_congr fun st => executePhase_prssRealRand K D A noFunctionality label calls st

/-- The normal form of the game. The real game is the setup run, then `liveStreams` of its outputs, then
`Z` on the counted copy. -/
theorem distinguish_prssRealRand (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    distinguish (realExecution D A noFunctionality setupRounds (prssRealRandProtocol K label calls) x z) Z =
      (do
        let r ← realExecution D A noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z
        let streams ← free (liveStreams K prgBits D r.2 label calls)
        worldRoles.adversary (Z (r.1, streams))) := by
  unfold distinguish
  rw [realExecution_prssRealRand]
  simp only [bind_assoc, map_eq_bind_pure_comp, Function.comp_def, pure_bind]

/-- The normal form under a handler. From each state, the game runs the setup, then `liveStreams` from the
state after the setup, then `Z` from the state after the draws. -/
theorem simulateQ_prssRealRand {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (label : ℕ)
    (calls : List RandCall) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (List (RandOutput C E))) (s : σ) :
    (simulateQ impl (distinguish (realExecution D A noFunctionality setupRounds (prssRealRandProtocol K label calls) x z) Z)).run s =
      (do
        let a ← (simulateQ impl (realExecution D A noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)).run s
        let b ← (simulateQ impl (free (liveStreams K prgBits D a.1.2 label calls))).run a.2
        (simulateQ impl (worldRoles.adversary (Z (a.1.1, b.1)))).run b.2) := by
  rw [distinguish_prssRealRand]
  simp only [simulateQ_bind, StateT.run_bind]

end ThresholdLeanXmssSecurity
