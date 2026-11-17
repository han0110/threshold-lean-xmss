import ThresholdLeanXmss.Ideal

/-!
# The simulators and the reductions

The explicit simulators of the setups, of a ceremony and of a PRSS setup with its `Rand` calls, and
the reduction to the AES term.
-/

set_option autoImplicit false

open OracleComp OracleSpec  HashSig LeanXmss

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-! ## The simulators -/

/-- A log of the `H` calls of the adversary. -/
abbrev CallLog (C : Committee) := List (Query C × HashOutput)

/-- A step of the adversary on the counted copy, with the log of its `H` calls. The simulator reads
each call of `A`, as with the local random oracle of CDG+18, Section 3 and Fig. 2(a). It is not the
`Observe` query of CDG+18, Fig. 10, which gives only the illegitimate calls to a global oracle. -/
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

/-- The reveal of corrupt operator `j` to `i` in a setup of `phase`, from an observed `H` call that
opens the commitment that `j` sent to `i`. The extraction follows the proof of CDG+18, Theorem 6
(Section 5.3). -/
def extractReveal (phase : Phase) (calls : CallLog C) (sent : C.Party → C.Party → Option (Msg E)) (j i : C.Party) :
    List HashOutput :=
  (calls.findSome? fun (q, out) => match q with
    | .commit phase' j' i' reveal =>
      if phase' = phase ∧ j' = j ∧ i' = i ∧ [out] = Msg.hashesOf (sent j i) then some reveal else none
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

/-- The simulator of a setup of `phase`. It runs `A` with emulated honest operators on the free copy
and observes every `H` call of `A`. After the commit round, it extracts the corrupt reveals from all
observed calls, as in the proof of CDG+18, Theorem 6 (Section 5.3). Then it programs `H` so that the
term keys and the pair keys of the corrupt operators are those of the dealer. This programming is an
adaptation of this project. The seed generation also programs `P`. The receivers are the emulated
honest operators that do not abort (GL05). `setup` is the setup of one emulated operator, and `dealt`
reads the parameter and the corrupt keys from the leak of the dealer. In the seed generation the
parameter is `P`. In the PRSS setup the leak has no `P`, and `dealt` gives the parameter `0`. -/
def setupSimulator (phase : Phase) {O L : Type} (setup : C.Party → Parts C → PartyM C E RealSpec O)
    (dealt : L → PublicParameter × (C.Party → Option (PrssKeys C)))
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit L (Finset C.Party) A.State where
  State := SimulatorState C Unit A.State
  start corrupt z := do
    let (state, log) ← observe (A.start corrupt z)
    pure ⟨state, log, corrupt⟩
  answer st := fun l => do
    let (parameter, corrupt) := dealt l
    let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
    let steps ← startSteps worldRoles D fun i => setup i (parts i)
    let ((state, steps, sent), calls) ← (stepRound observedRoles D A noFunctionality st.adversary steps).run
    let log := st.log ++ calls
    let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
    let view := fun (i j : C.Party) =>
      if j ∈ D.1 then readReveal phase (extractReveal phase log sent j i) i j else parts j
    let _ ← (if phase = .seedGen then do
        let high ← free (liftComp ($ᵗ HashOutput) _)
        program (.derive phase .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
          (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
      else pure true)
    let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j =>
        let i := firstHonest (C.holders T)
        program (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun k => (view i k).term T))
          (((corrupt j).map (·.term T)).getD 0)
      | none => pure true
    let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        program (.derive phase .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((corrupt j).map (·.pair i)).getD 0)
      else pure true
    let ((state, keys), rest) ← (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state steps).run
    pure (⟨state, log ++ rest, st.corrupt⟩, Finset.univ.filter fun i => (keys i).isSome)
  output st := pure st.adversary

/-- The simulator of the seed generation. It programs `P`, the corrupt seeds and the corrupt pair
keys of `F_seedGen`. -/
def seedGenSimulator (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) A.State :=
  setupSimulator .seedGen seedGenWith (fun l => (l.1, fun j => (l.2 j).map fun k => ⟨k.seed, k.pairKey⟩)) D A

/-- The simulator of the PRSS setup. It programs the corrupt term keys and pair keys of
`F_prssKeys`, and no `P`. -/
def prssSetupSimulator (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit (C.Party → Option (PrssKeys C)) (Finset C.Party) A.State :=
  setupSimulator .prss prssSetupWith (fun corrupt => (0, corrupt)) D A

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The simulator of one ceremony, after GS20, Theorem 2. It runs `A` with emulated honest operators.
They use `P` from `F_ceremony`, the seeds of the corrupt operators for the terms that a corrupt
operator holds, and zero seeds elsewhere. Their streams under hidden PRSS keys are ideal. The
opening of each batch shifts the first lacked term `T₀`, so it opens the outputs of `F_ceremony`
(GS20, Theorem 2, output phase, and MPClan, App. B). Batch `k` is at position `k - counters.2` of
the ceremony, so it opens the outputs of the jobs at that position of `chunks`. `Rerand` makes `T₀`
uniform first (BBY23, Section 4.3). The receivers are the emulated honest operators that do not
abort (GL05). -/
def ceremonySimulator (counters : ℕ × ℕ) (jobs : List Job) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) (Keys C) (PublicParameter × List (List Bit)) (Finset C.Party) A.State where
  State := SimulatorState C (Keys C) A.State
  start corrupt z := do
    let (state, log) ← observe (A.start corrupt z)
    pure ⟨state, log, corrupt⟩
  answer st := fun (parameter, opened) => do
    let T₀ := lackedTerm D.1
    let seeds : C.Term → HashOutput := fun T => (C.parties.findSome? fun j =>
      if j ∈ C.holders T then (st.corrupt j).map (·.seed T) else none).getD 0
    let keys : Keys C := ⟨parameter, seeds, fun _ => 0⟩
    let openings := chunks settings.batchSize opened
    let buildingBlocks := fun (ctx : Context C) (k : ℕ) (batch : List Job) =>
      { realRunBuildingBlocks K ctx settings.mode with
        output := fun v count => do
          let clear ← StateT.lift (oracleStep (batch.mapM (evalJob circuits parameter seeds)))
          let shift := fun g => ((openings.getD (k - counters.2) []).flatten.getD g 0) + (clear.flatten.getD g 0)
          StateT.lift (openRep K ctx (fun T g => if T₀ = some T then v T g + shift g else v T g) count) }
    let (((state, outputs), _), calls) ← ((executePhase (emulatedRoles D) D A noFunctionality
      (ceremonyFuel circuits settings) st.adversary fun i =>
        (ceremonyWith K circuits settings buildingBlocks i keys counters jobs : PartyM C E RealSpec (List (List Bit)))).run ∅).run
    pure (⟨state, st.log ++ calls, st.corrupt⟩, Finset.univ.filter fun i => (outputs i).isSome)
  output st := pure st.adversary

/-- The streams of one call under the keys that the coalition knows and an honest receiver holds, at
the `count` positions. The terms have a corrupt holder and a holder that is an honest receiver.
Pair stream `(j, i)` is the stream of a corrupt operator `j` and an honest receiver `i`. -/
def knownStreams {R : Type} [Zero R] (D : C.Coalition) (receivers : Finset C.Party) (codec : Codec C E R)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (Shares C R × (C.Party → C.Party → ℕ → R)) := do
  let r ← C.terms.mapM fun T =>
    if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
      codec.draw (.term T) (term T) ρ idx count
    else pure fun _ => 0
  let Z ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
      let p := C.pairOf i j (fun e => h.2.1 (e ▸ h.1))
      codec.draw (.pair p) (pair p) ρ idx count
    else pure fun _ => 0
  pure (fun T g => if g < count then (r.getD (C.terms.idxOf T) fun _ => 0) g else 0,
    fun j i g => if g < count then ((Z.getD j.val []).getD i.val fun _ => 0) g else 0)

/-- The key of term `T` at the first honest holder that has keys. -/
def liveTermKey (D : C.Coalition) (out : C.Party → Option (PrssKeys C)) (T : C.Term) : HashOutput :=
  (C.parties.findSome? fun i => if i ∉ D.1 ∧ i ∈ C.holders T then (out i).map (·.term T) else none).getD 0

/-- The key of pair `p` at its first honest endpoint that has keys. -/
def livePairKey (D : C.Coalition) (out : C.Party → Option (PrssKeys C)) (p : C.Pair) : HashOutput :=
  if p.1.1 ∉ D.1 ∧ (out p.1.1).isSome then ((out p.1.1).map (·.pair p.1.2)).getD 0
  else ((out p.1.2).map (·.pair p.1.1)).getD 0

/-- The state of `prssRealRandSimulator`. It holds the state of the adversary, the keys of the
emulated operators, the next round label and the calls that `F_rand` did not leak yet. -/
structure PrssRealRandState (C : Committee) (σ : Type) where
  adversary : σ
  keys : C.Party → Option (PrssKeys C)
  label : ℕ
  calls : List RandCall

/-- The simulator of `prssRealRandProtocol`. It runs `A` on the counted copy. At the first leak it
emulates the PRSS setup of the honest operators on the free copy, as the real operators run it, and
names the emulated operators that have keys. For each call of `F_rand` it replies with the streams
under the keys of the coalition, on the free copy (CDI05). It makes no programming query and reads no
call of `A`. -/
def prssRealRandSimulator (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit RandLeak (RandReplies C E) A.State where
  State := PrssRealRandState C A.State
  start corrupt z := do
    let state ← worldRoles.adversary (A.start corrupt z)
    pure ⟨state, fun _ => none, label, calls⟩
  answer st l :=
    match l with
    | .inl () => do
        let (state, keys) ← executePhase worldRoles D A noFunctionality setupRounds st.adversary fun i =>
          (prssSetup i : PartyM C E RealSpec (PrssKeys C))
        pure ({ st with adversary := state, keys := keys }, .inl (Finset.univ.filter fun i => (keys i).isSome))
    | .inr _ =>
      let receivers := Finset.univ.filter fun i => (st.keys i).isSome
      match st.calls with
      | [] => pure (st, .inr (.inl (0, 0)))
      | .elements idx count :: rest => do
          let known ← free (liftComp (knownStreams D receivers (elementCodec K) (liveTermKey D st.keys)
            (livePairKey D st.keys) st.label idx count) _)
          pure ({ st with label := st.label + 1, calls := rest }, .inr (.inl known))
      | .bits idx count :: rest => do
          let known ← free (liftComp (knownStreams D receivers (bitCodec (E := E)) (liveTermKey D st.keys)
            (livePairKey D st.keys) st.label idx count) _)
          pure ({ st with label := st.label + 1, calls := rest }, .inr (.inr known))
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
