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

/-! ## The forger of the lifetime claim -/

section Forger

/-- The oracles of the forger, namely the local oracles and the signing oracles of the game. -/
abbrev ForgerSpec (C : Committee) := LocalSpec C + TsigSpec C

/-- The oracles of the emulated lifetime, namely the world and the signing oracles of the game. -/
abbrev ReplaySpec (C : Committee) := WorldSpec C + TsigSpec C

/-- The points that `keygenSimulator` programs. -/
def KeygenPoint : Query C → Prop
  | .derive .keygen _ _ => True
  | _ => False

/-- The world of the emulated lifetime, as the forger answers it. The forger cannot program `H`. So
it keeps the points of `KeygenPoint` in its own table, as a lazy random oracle that
`keygenSimulator` programs. Every other call goes to the oracles of the forger. -/
def forgerWorld : QueryImpl (ReplaySpec C) (StateT (HashCache C) (OracleComp (ForgerSpec C))) :=
  let table := fun {α : Type} (step : StateT (HashCache C) ProbComp α) =>
    (StateT.mk fun s => liftComp (step.run s) (ForgerSpec C) : StateT (HashCache C) (OracleComp (ForgerSpec C)) α)
  let localPart : QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (ForgerSpec C))) := fun t =>
    match t with
    | .inr (.inl q) => if KeygenPoint q then table ((Query C →ₒ HashOutput).randomOracle q) else
        StateT.lift (OracleComp.lift (OracleSpec.query (spec := ForgerSpec C) (.inl (.inr (.inl q)))))
    | t => StateT.lift (OracleComp.lift (OracleSpec.query (spec := ForgerSpec C) (.inl t)))
  let signing : QueryImpl (TsigSpec C) (StateT (HashCache C) (OracleComp (ForgerSpec C))) :=
    fun q => StateT.lift (OracleComp.lift (OracleSpec.query (spec := ForgerSpec C) (.inr q)))
  (localPart + (fun x => table (programAnswer (C := C) x)) + localPart) + signing

/-- A computation of the world in the emulated lifetime. -/
def inWorld {α : Type} (oa : OracleComp (WorldSpec C) α) : OracleComp (ReplaySpec C) α :=
  simulateQ (fun t => query (spec := ReplaySpec C) (.inl t)) oa

/-- The roles of an emulated run of `F_tree`. The run keeps its own table of ideal streams, as
`treeSimulator` does. -/
def replayRoles (D : C.Coalition) : Roles C (StateT (StreamCache C) (OracleComp (ReplaySpec C))) where
  adversary oa := StateT.lift (inWorld (worldRoles.adversary oa))
  honest oa := StateT.mk fun streams =>
    inWorld (Prod.fst <$> (((emulatedRoles D).honest oa).run streams).run)

/-- The openings of each batch of a ceremony, from its public output. `ρ` is the opened randomizer
value of the top key of a bottom tree. The job order and the batching of `signJobs` do not depend on
the positions, so the positions here are zero. The chain values themselves come from the signature. -/
def treeOpenings (settings : Settings) (ρ : Digest) : Tree → TreeOutput → List (List (List Bit))
  | .top, .top tree => (chunks settings.batchSize topJobs).map fun jobs => jobs.map fun job =>
      match job.kind with
      | .chainEnd e l => bitsOfDigest (tree.chainEnd e l)
      | _ => []
  | .bottom b, .bottom tree =>
      ((chunks settings.batchSize (bottomJobs b)) ++ chunks settings.batchSize (signJobs b fun _ => digit 0)).map
        fun jobs => jobs.map fun job =>
          match job.kind with
          | .chainRow e l => bitsOfDigest (tree.cpk e l).1 ++ bitsOfDigest (tree.cpk e l).2.1 ++ bitsOfDigest (tree.cpk e l).2.2
          | .chainValue _ l _ => bitsOfDigest (tree.topSignature.chainValues l)
          | .commitment e => bitsOfDigest (tree.commitment e)
          | .randomizer => bitsOfDigest ρ
          | _ => []
  | _, _ => []

/-- `LifetimeState.settle` for a run of `F_tree`. An emulated operator that ends with an output is a
receiver of `F_tree` and keeps `output` (GL05). -/
def settleIdeal (D : C.Coalition) (output : Option TreeOutput) (st : LifetimeState C E) : LifetimeState C E :=
  match st.running with
  | some (tree, fuel, steps) =>
      let out := fun i => if ((steps i).output).isSome then output else none
      if fuel = 0 ∨ ∀ i, i ∉ D.1 → (steps i).isDone then
        match tree with
        | .top => { st with running := none, top := fun i => (st.top i).or (TreeOutput.topTree (out i)) }
        | .bottom b =>
            let bottom := fun i => Function.update (st.bottom i) b ((st.bottom i b).or
              (match out i with | some (.bottom tree) => some tree | _ => none))
            { st with running := none, bottom := bottom }
      else st
  | none => st

variable (attempts : ℕ)

/-- The lifetime oracles of the forger. They are `lifetimeOraclesWith` with two changes.

* A signing request that the lifetime admits goes to the signing oracles of the game.
* Each ceremony is a run of `F_tree` with the emulated operators of `treeSimulator`. The output of
  `F_tree` is the top tree of the game or the answer of its tree oracle.

`corrupt` holds the keys of the coalition, `top` the top tree of the game and `h` the first honest
operator. The state holds the stream table and the output of `F_tree` of the running ceremony. -/
def forgerOracles (D : C.Coalition) (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C))
    (top : TopTree) (h : C.Party) :
    QueryImpl (LifetimeSpec C E)
      (StateT (LifetimeState C E × Option (StreamCache C × Option TreeOutput)) (OracleComp (ReplaySpec C))) := fun q =>
  let ask := fun (q : TsigQuery C) =>
    (StateT.lift (OracleComp.lift (OracleSpec.query (spec := ReplaySpec C) (.inr q))) :
      StateT (LifetimeState C E × Option (StreamCache C × Option TreeOutput)) (OracleComp (ReplaySpec C)) (TsigSpec C q))
  let admit := fun (i : C.Party) (e : KeyIndex) => (do
    let (st, run) ← get
    if st.running.map (·.1) = some (.bottom (treeOf e)) ∨ st.bottom i (treeOf e) = none then pure false else do
      set ({ st with signed := insert (treeOf e) st.signed }, run)
      pure true :
    StateT (LifetimeState C E × Option (StreamCache C × Option TreeOutput)) (OracleComp (ReplaySpec C)) Bool)
  let seeds : C.Term → HashOutput := fun T => (C.parties.findSome? fun j =>
    if j ∈ C.holders T then (corrupt j).map (·.seed T) else none).getD 0
  match q with
  | .sign (.corrupt _) => pure none
  | .sign (.tree b) => do
      if ((← get).1.bottom h b).isSome then ask (.tree b) else pure none
  | .sign (.round1 i J e message) => do
      if ← admit i e then ask (.round1 i J e message) else pure none
  | .sign (.round2 i J e message parts) => do
      if ← admit i e then ask (.round2 i J e message parts) else pure none
  | .publicKey => do pure ((← get).1.publicKey parameter h)
  | .start tree => do
      let (st, _) ← get
      let open_ := st.running = none ∧ match tree with
        | .top => st.topRuns < attempts ∧ ∃ i, i ∉ D.1 ∧ st.top i = none
        | .bottom b => st.bottomRuns b < attempts ∧ b ∉ st.signed ∧ (∀ i, i ∉ D.1 → (st.top i).isSome) ∧
            ∃ i, i ∉ D.1 ∧ st.bottom i b = none
      if ¬ open_ then pure none else do
        let (output, ρ) ← (match tree with
          | .top => pure (some (.top top), 0)
          | .bottom b => (fun r => (r.map (.bottom ·.1), (r.map (·.2)).getD 0)) <$> ask (.tree b) :
          StateT (LifetimeState C E × Option (StreamCache C × Option TreeOutput)) (OracleComp (ReplaySpec C))
            (Option TreeOutput × Digest))
        let openings := (output.map (treeOpenings settings ρ tree)).getD []
        let gadgets := fun (ctx : Context C) (k : ℕ) (jobs : List Job) =>
          { realRunGadgets K ctx settings.mode with
            output := fun v count => do
              let clear ← StateT.lift (oracleStep (jobs.mapM (evalJob circuits parameter seeds)))
              let shift := fun g => ((openings.getD k []).flatten.getD g 0) + (clear.flatten.getD g 0)
              StateT.lift (openRep K ctx (fun T g => if lackedTerm D.1 = some T then v T g + shift g else v T g) count) }
        let (steps, streams) ← StateT.lift ((startSteps (replayRoles D) D fun i =>
          (ceremonyWith K circuits settings gadgets i ⟨parameter, seeds, fun _ => 0⟩ ((st.top h).getD emptyTop) tree :
            PartyM C E RealSpec TreeOutput)).run ∅)
        let st := match tree with
          | .top => { st with topRuns := st.topRuns + 1 }
          | .bottom b => { st with bottomRuns := Function.update st.bottomRuns b (st.bottomRuns b + 1) }
        set (settleIdeal D output { st with running := some (tree, ceremonyFuel circuits settings, steps) },
          some (streams, output))
        pure (some (toCoalition D steps))
  | .round sent => do
      let (st, run) ← get
      let some (tree, fuel, steps) := st.running | pure none
      let some (streams, output) := run | pure none
      let ((_, steps, _), streams) ← StateT.lift ((stepRound (replayRoles D) D (roundAdversary (I := PEmpty) sent)
        noFunctionality () steps).run streams)
      set (settleIdeal D output { st with running := some (tree, fuel - 1, steps) }, some (streams, output))
      pure (some (toCoalition D steps))

/-- The forger of the lifetime claim. It runs the lifetime adversary `A` in the signing game, in a
lifetime where the keygen is `F_keygen` and each ceremony is `F_tree`.

* It corrupts the coalition `D` and gets its keys. It asks no other corruption.
* It emulates the keygen with `keygenSimulator`, with the public parameter of the game. It keeps
  the programmed keygen points in its own table, because it cannot program `H`.
* It answers the lifetime queries with `forgerOracles`. From the game it uses only the keys of `D`,
  `.tree b` for each bottom tree that it holds, and the signing rounds. The keys of `D` include its
  pair keys with honest operators, but it gets no hidden term seed and no key that only honest
  operators share. The output of `.tree b` is enough to rebuild the openings for `treeSimulator`.
* It outputs the forgery of `A`.

It uses `circuits` in each emulated ceremony, and `circuits` compute the fixed `Th`.
`SigningSecurityStatement` does not bound the advantage of this forger. That claim is for
`signingWorld`, where all of `H` is a random oracle. -/
def lifetimeForger (D : C.Coalition) (A : LifetimeAdversary C E) : TsigAdversary C := fun publicKey top =>
  let replay : OracleComp (ReplaySpec C) Forgery := do
    let corrupt ← Concrete.sequenceFin fun (i : C.Party) =>
      if i ∈ D.1 then OracleComp.lift (OracleSpec.query (spec := ReplaySpec C) (.inr (.corrupt i))) else pure none
    let Sim := keygenSimulator D A.keygen
    let st ← inWorld (Sim.start (corruptInputs D fun _ => ()) [])
    let (st, _) ← inWorld (Sim.answer st (publicKey.parameter, corrupt))
    let state ← inWorld (Sim.output st)
    let h := (C.parties.find? (· ∉ D.1)).getD (firstParty C)
    let adversary : QueryImpl (LocalSpec C)
        (StateT (LifetimeState C E × Option (StreamCache C × Option TreeOutput)) (OracleComp (ReplaySpec C))) :=
      fun t => StateT.lift (inWorld (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
    (simulateQ (adversary + forgerOracles K circuits settings attempts D publicKey.parameter corrupt top h)
      (A.run state publicKey.parameter)).run'
      (⟨⟨D.1, fun _ => none, [], fun _ => none⟩, fun _ => none, fun _ _ => none, 0, fun _ => 0, ∅, none⟩, none)
  (simulateQ forgerWorld replay).run' ∅

end Forger

/-! ## The reductions of the lifetime claim -/

section Lifetime

variable (attempts : ℕ)

/-- The roles of the hybrid of run `n`. The runs before run `n` use ideal streams under the hidden
keys, as `emulatedRoles`. The honest operators of run `n`, the keygen and the signing run on the free
copy. The honest operators of the later runs run on the counted copy. -/
def lifetimeHybridRoles (D : C.Coalition) (n : ℕ) : ℕ → Roles C (EmulationM C) := fun r =>
  if r < n then emulatedRoles D
  else if r = n then ⟨(emulatedRoles D).adversary, fun oa => StateT.lift (liftM (free oa))⟩
  else ⟨(emulatedRoles D).adversary, (emulatedRoles D).adversary⟩

/-- The reduction of run `n` of the lifetime to `hiddenStreams`. It runs `prgReduction` on the
lifetime with `lifetimeHybridRoles D n`. Only the honest streams of run `n` reach the PRF oracle,
because the keygen and the signing call no `PRG`. -/
def lifetimeRunReduction (prims : Primitives) (D : C.Coalition) (A : LifetimeAdversary C E) (n : ℕ) :
    PRFScheme.PRFAdversary ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) Bit :=
  prgReduction prims D ((fun r => r.1.1) <$>
    ((lifetimeGameWith K circuits settings attempts (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A).run ∅).run)

end Lifetime

end ThresholdLeanXmss
