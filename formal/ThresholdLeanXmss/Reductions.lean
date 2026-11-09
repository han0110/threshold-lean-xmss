import ThresholdLeanXmss.Ideal

/-!
# The simulators and the reductions

The explicit simulators of the keygen and of a ceremony, and the reduction to the AES term.
-/

open OracleComp OracleSpec LeanXmss

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-! ## The simulators -/

/-- A log of the `H` calls of the adversary. -/
abbrev CallLog (C : Committee) := List (Query C × HashOutput)

/-- A step of the adversary on the counted copy, with its `H` calls (CDG+18, observation). -/
def observe {α : Type} (oa : OracleComp (LocalSpec C) α) : OracleComp (WorldSpec C) (α × CallLog C) :=
  let impl : QueryImpl (LocalSpec C) (WriterT (CallLog C) (OracleComp (WorldSpec C))) := fun t =>
    match t with
    | .inr (.inl q) => do
        let y ← liftM (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C)))
        tell [(q, y)]
        pure y
    | t => liftM (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  (simulateQ impl oa).run

/-- The adversary under observation and the emulated honest operators on the free copy. -/
def observedRoles : Roles C (WriterT (CallLog C) (OracleComp (WorldSpec C))) :=
  ⟨fun oa => WriterT.mk (observe oa), fun oa => liftM (free oa)⟩

/-- A programming query on the counted copy. -/
def program (q : Query C) (value : HashOutput) : OracleComp (WorldSpec C) Bool :=
  counted (OracleComp.lift (OracleSpec.query (spec := SimulatorSpec C) (.inr (q, value))))

/-- The reveal of corrupt operator `j` to `i`, from an observed `H` call that opens the commitment
that `j` sent to `i` (CDG+18, extraction). -/
def extractReveal (calls : CallLog C) (sent : C.Party → C.Party → Option (Msg E)) (j i : C.Party) :
    List HashOutput :=
  (calls.findSome? fun (q, out) => match q with
    | .commit .keygen j' i' reveal => if j' = j ∧ i' = i ∧ [out] = Msg.hashesOf (sent j i) then some reveal else none
    | _ => none).getD []

/-- A party, which exists because `n ≥ 1`. -/
def firstParty (C : Committee) : C.Party := ⟨0, by have := C.one_le_t; unfold Committee.n; omega⟩

/-- The cache of the ideal streams under the hidden keys. -/
abbrev StreamCache (C : Committee) := (PrgInput C →ₒ Bit).QueryCache

/-- The monad of an emulation, with the ideal streams and the log of the observed calls. -/
abbrev EmulationM (C : Committee) := StateT (StreamCache C) (WriterT (CallLog C) (OracleComp (WorldSpec C)))

/-- The observed adversary and the emulated honest operators. An emulated stream under a hidden key
gives uniform bits, the same for every holder (GS20, Lemma 4, Hybrid 2, and CDI05). Every other call
of an emulated operator runs on the free copy. -/
def emulatedRoles (D : C.Coalition) : Roles C (EmulationM C) where
  adversary oa := StateT.lift (WriterT.mk (observe oa))
  honest oa :=
    let impl : QueryImpl (LocalSpec C) (EmulationM C) := fun t =>
      match t with
      | .inr (.inr x) => if Hidden D x.1 then
          StateT.mk fun cache => liftM (free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache) (LocalSpec C)))
        else StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x))))))
      | t => StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query t))))
    simulateQ impl oa

/-- The state of an explicit simulator. It keeps the log of every observed call of the adversary
from its start, and the inputs of the corrupt operators. -/
structure SimulatorState (C : Committee) (I σ : Type) where
  adversary : σ
  log : CallLog C
  corrupt : C.Party → Option I

/-- The simulator of the keygen (CDG+18). It runs `A` with emulated honest operators on the free copy
and observes every `H` call of `A`. After the commit round, it extracts the corrupt reveals from all
observed calls. Then it programs `H` so that `P`, the corrupt seeds and the corrupt pair keys are
those of `F_keygen`. The receivers are the emulated honest operators that do not abort (GL05). -/
def keygenSimulator (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) A.State where
  State := SimulatorState C Unit A.State
  start corrupt z := do
    let (state, log) ← observe (A.start corrupt z)
    pure ⟨state, log, corrupt⟩
  answer st := fun (parameter, corrupt) => do
    let parts ← free (liftComp (Concrete.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
    let steps ← startSteps worldRoles D fun i => (keygenWith i (parts i) : PartyM C E RealSpec (Keys C))
    let ((state, steps, sent), calls) ← (stepRound observedRoles D A noFunctionality st.adversary steps).run
    let log := st.log ++ calls
    let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
    let view := fun (i j : C.Party) =>
      if j ∈ D.1 then readReveal .keygen (extractReveal log sent j i) i j else parts j
    let h₀ := firstHonest Finset.univ
    let high ← free (liftComp ($ᵗ HashOutput) _)
    let _ ← program (.derive .keygen .parameter (C.parties.map fun j => (view h₀ j).parameter))
      (high >>> digestBits <<< digestBits ||| parameter.setWidth hashOutputBits)
    let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j =>
        let i := firstHonest (C.holders T)
        program (.derive .keygen .term ((C.parties.filter (· ∈ C.holders T)).map fun k => (view i k).term T))
          (((corrupt j).map (·.seed T)).getD 0)
      | none => pure true
    let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        program (.derive .keygen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((corrupt j).map (·.pairKey i)).getD 0)
      else pure true
    let ((state, keys), rest) ← (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state steps).run
    pure (⟨state, log ++ rest, st.corrupt⟩, Finset.univ.filter fun i => (keys i).isSome)
  output st := pure st.adversary

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The simulator of one ceremony, after GS20, Theorem 2. It runs `A` with emulated honest operators.
They use `P` from `F_tree`, the seeds of the corrupt operators for the terms that a corrupt operator
holds, and zero seeds elsewhere. Their streams under hidden PRSS keys are ideal. The opening of each
batch shifts the first lacked term `T₀`, so it opens the output of `F_tree` (GS20, Theorem 2, output
phase, and MPClan, App. B). `Rerand` makes `T₀` uniform first (BBY23, Section 4.3). The receivers
are the emulated honest operators that do not abort (GL05). -/
def treeSimulator (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) (Keys C) (PublicParameter × List (List (List Bit))) (Finset C.Party) A.State where
  State := SimulatorState C (Keys C) A.State
  start corrupt z := do
    let (state, log) ← observe (A.start corrupt z)
    pure ⟨state, log, corrupt⟩
  answer st := fun (parameter, openings) => do
    let T₀ := lackedTerm D.1
    let seeds : C.Term → HashOutput := fun T => (C.parties.findSome? fun j =>
      if j ∈ C.holders T then (st.corrupt j).map (·.seed T) else none).getD 0
    let keys : Keys C := ⟨parameter, seeds, fun _ => 0⟩
    let gadgets := fun (ctx : Context C) (k : ℕ) (jobs : List Job) =>
      { realRunGadgets K ctx settings.mode with
        output := fun v count => do
          let clear ← StateT.lift (oracleStep (jobs.mapM (evalJob circuits parameter seeds)))
          let shift := fun g => ((openings.getD k []).flatten.getD g 0) + (clear.flatten.getD g 0)
          StateT.lift (openRep K ctx (fun T g => if T₀ = some T then v T g + shift g else v T g) count) }
    let (((state, outputs), _), calls) ← ((executePhase (emulatedRoles D) D A noFunctionality
      (ceremonyFuel circuits settings) st.adversary fun i =>
        (ceremonyWith K circuits settings gadgets i keys top tree : PartyM C E RealSpec TreeOutput)).run ∅).run
    pure (⟨state, st.log ++ calls, st.corrupt⟩, Finset.univ.filter fun i => (outputs i).isSome)
  output st := pure st.adversary

/-! ## The reduction to the AES term -/

/-- The PRF oracle of the streams under the hidden keys. -/
abbrev StreamSpec (C : Committee) := PRFScheme.PRFOracleSpec ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) Bit

/-- The reduction to `hiddenStreams`. It runs `game` on the world, and each honest stream under a key
that is hidden from `D` comes from the PRF oracle (CDI05, the PRSS of the lacked term). The counted
copy keeps the real answers, also for a hidden key. -/
def prgReduction (prims : Primitives) (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    PRFScheme.PRFAdversary ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) Bit :=
  let lift := fun {α : Type} (oa : StateT (HashCache C) ProbComp α) =>
    (StateT.mk fun s => liftComp (oa.run s) (StreamSpec C) : StateT (HashCache C) (OracleComp (StreamSpec C)) α)
  let real : QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (StreamSpec C))) :=
    fun t => lift (localAnswer prims t)
  let honest : QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (StreamSpec C))) := fun t =>
    match t with
    | .inr (.inr x) => if Hidden D x.1 then
        StateT.lift (query (spec := StreamSpec C) (.inr ((x.1, x.2.1), x.2.2)))
      else real (.inr (.inr x))
    | t => real t
  let programming : QueryImpl (ProgramSpec C) (StateT (HashCache C) (OracleComp (StreamSpec C))) :=
    fun x => lift (programAnswer x)
  (simulateQ ((real + programming) + honest) game).run' ∅

end ThresholdLeanXmss
