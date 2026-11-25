import ThresholdLeanXmss.Statement.DkgGame

/-!
# The reduction of the security of the setup

`dkgReduction` turns an adversary `A` of `dkgTsigGame` into a forger of `tsigGame`, as the proofs of
Lemmas 3 to 5 of Gurkan and others build one. The forger runs `A` and plays the honest operators
toward it in the seed generation, in each run of the top tree, in each run of a bottom tree and in
the signing phase. It follows `dkgTsigRun` step by step, except in the points of the list below.

The forger has these sources and no other.

* The oracles of `tsigGame`. It asks `corrupt i` only for the operators of the coalition, `tree b`
  for the outputs of bottom tree `b`, and `round1` and `round2` for the signing requests of `A`.
* The public key and the top tree that `tsigGame` gives it.
* Its own table for the domains of `H` that only the setup uses, and `PRG` as AES under that table.
  Each call in a domain that the signing uses goes to `tsigGame`.
* Fresh randomness, and the messages and the calls of `A`.

The forger has no seed of the dealer that the coalition lacks. Its emulated operators use the seeds
of the emulated seed generation. The opening of each batch shifts the first term that the coalition
lacks by the outputs of a dealer run that succeeds plus the outputs in the clear. The opening gives
the outputs of the dealer only when the emulated output equals the output in the clear, that is
outside the bad events of consistency and of soundness of the check. The emulated operators also
run the honest challenge search of each check (`findChallenge`), on the own table. That search finds
no secret.

The forger differs from the game in these points. Each point is an obligation of the proof, which
needs a coupling or a bad event with a bound.

* It gives `forge` the public key and the top tree of the dealer, not those of the first honest
  operator that holds a top tree.
* When the randomizer search of the dealer fails, `tree b` gives `none` and the forger runs no tree
  run. It still asked `tree b`, so the state of the dealer game changed. The bound must cover the
  first divergence that the adversary can see.
* It asks `tree b` also when no run is allowed. This builds bottom tree `b` of the dealer earlier
  than the game does. A coupling by lazy sampling is the planned way.
* An emulated operator of a bottom run makes no randomizer search. It takes the randomizer of the
  top signature from the answer of `tree b`, which is public data of `tsigGame`, and gets the
  codeword from one hash. With the same public parameter and the same hash oracle, when the outputs
  of the first ceremony are those of the dealer, the result of the dealer is the result that the
  search of the game gives. The outputs agree outside the bad events of consistency and of
  soundness.
* A signing request to an emulated operator with keys, a top tree and an output of the bottom tree
  goes to the oracle of the dealer, also when the emulated output of that operator is wrong.
* After the seed generation, each emulated operator with keys votes on the parameter of the public
  key of the dealer. In the game, each honest operator with keys votes on the parameter of its own
  keys. The two agree
  unless an emulated operator ends the seed generation with another parameter.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A party, which exists because `n ≥ 1`. -/
def firstParty (C : Committee) : C.Party := ⟨0, by have := C.one_le_t; unfold Committee.n; omega⟩

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (aes : Aes) (D : C.Coalition)

/-! ## The own table of the setup domains -/

/-- An input of `H` in a domain that only the setup uses. -/
def isSetupQuery : Query C → Bool
  | .hash _ => false
  | .prf .. => false
  | .mask .. => false
  | _ => true

/-- One step of the private table. `H` is a lazy random oracle, and `PRG` is AES under the first
128 bits of the table value of `.streamKey key`. -/
def privateStep (aes : Aes) : QueryImpl (RoSpec C) (StateT (HashCache C) ProbComp) :=
  (Query C →ₒ HashOutput).randomOracle + fun (x : PrgInput C) => do
    let derived ← (Query C →ₒ HashOutput).randomOracle (.streamKey x.2.1)
    pure (aes.eval (truncateHash derived) x.2.2)

/-- A log of the `H` calls of the adversary. -/
abbrev CallLog (C : Committee) := List (Query C × HashOutput)

/-- The cache of the ideal streams under the hidden keys. -/
abbrev StreamCache (C : Committee) := (PrgInput C →ₒ Bit).QueryCache

/-- The state of the world of the forger. It holds the own table of the setup domains, the ideal
streams under the PRSS keys that the coalition lacks, and the log of the calls of `A` in the setup
domains. -/
structure TableState (C : Committee) where
  table : HashCache C
  streams : StreamCache C
  log : CallLog C

/-- The world of the forger, on the oracles of `tsigGame`. -/
abbrev TableM (C : Committee) := StateT (TableState C) (OracleComp (LocalSpec C + TsigSpec C))

/-- A query to the oracles of `tsigGame`. -/
def forward (t : (LocalSpec C + TsigSpec C).Domain) : TableM C ((LocalSpec C + TsigSpec C).Range t) :=
  liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C + TsigSpec C) t))

/-- A query to the signing oracles of `tsigGame`. -/
def tsigCall (q : TsigQuery C) : TableM C (TsigSpec C q) := forward (.inr q)

/-- One step of the own table on private coins. -/
def tableCall (x : (RoSpec C).Domain) : TableM C ((RoSpec C).Range x) :=
  StateT.mk fun s => do
    let (y, table) ← liftComp ((privateStep aes x).run s.table) (LocalSpec C + TsigSpec C)
    pure (y, { s with table := table })

/-- A call of `A`. A call of `H` in a setup domain goes to the own table and into the log, as the
local random oracle of CDG+18, Section 3, lets the simulator read it. `PRG` goes to the own table.
Sampling and each other call of `H` go to `tsigGame`. -/
def adversaryCall : QueryImpl (LocalSpec C) (TableM C) := fun t =>
  match t with
  | .inl n => forward (.inl (.inl n))
  | .inr (.inl q) =>
      if isSetupQuery q then do
        let y : HashOutput ← tableCall aes (.inl q)
        modify fun s => { s with log := s.log ++ [(q, y)] }
        pure y
      else forward (.inl (.inr (.inl q)))
  | .inr (.inr x) => tableCall aes (.inr x)

/-- A call of an emulated honest operator. A stream under a PRSS key that the coalition lacks gives
uniform bits, the same for every holder. This is the ideal stream of CDI05 and of the hybrid argument
of GS20, Lemma 4, Hybrid 2, here on the real network. Each other call goes where a call of `A` goes,
with no log. -/
def honestCall : QueryImpl (LocalSpec C) (TableM C) := fun t =>
  match t with
  | .inl n => forward (.inl (.inl n))
  | .inr (.inl q) => if isSetupQuery q then tableCall aes (.inl q) else forward (.inl (.inr (.inl q)))
  | .inr (.inr x) =>
      if Hidden D x.1 then StateT.mk fun s => do
        let (y, streams) ← liftComp (((PrgInput C →ₒ Bit).randomOracle x).run s.streams) (LocalSpec C + TsigSpec C)
        pure (y, { s with streams := streams })
      else tableCall aes (.inr x)

/-- `A` and the emulated honest operators in the world of the forger. -/
def reductionRoles : Roles C (TableM C) :=
  ⟨fun oa => simulateQ (adversaryCall aes) oa, fun oa => simulateQ (honestCall aes D) oa⟩

/-- A write of `value` into cell `q` of the own table. A cell that has a value keeps it. -/
def writeTable (q : Query C) (value : HashOutput) : TableM C Unit :=
  modify fun s => if (s.table q).isSome then s else { s with table := s.table.cacheQuery q value }

/-! ## The seed generation -/

/-- The reveal of corrupt operator `j` to `i` in a setup of `phase`, from an observed `H` call that
opens the commitment that `j` sent to `i`. The extraction follows the proof of CDG+18, Theorem 6
(Section 5.3). -/
def extractReveal (phase : Phase) (calls : CallLog C) (sent : C.Party → C.Party → Option (Msg E)) (j i : C.Party) :
    List HashOutput :=
  (calls.findSome? fun (q, out) => match q with
    | .commit phase' j' i' reveal =>
      if phase' = phase ∧ j' = j ∧ i' = i ∧ [out] = Msg.hashesOf (sent j i) then some reveal else none
    | _ => none).getD []

/-- The seed generation with emulated honest operators on fresh parts, as `realExecution` runs it.
After the commit round, the forger extracts the reveals of the coalition from the log of `A`
(CDG+18, Theorem 6). Then it writes the derived keys into its own table. `P` gets the parameter of
the public key in its low half and uniform bits in its high half. A term with a corrupt holder gets
the seed that `corrupt` gave. A pair of a corrupt and an honest operator gets the pair key that
`corrupt` gave. Each write holds only when its cell is empty, and a cell that `A` or an emulated
operator already asked keeps its value. The write of `P` uses the view of the first honest operator,
the write of a term the view of its first honest holder, and the write of a pair the view of its
honest operator. -/
def seedGenEmulation (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C))
    (net : Adversary C E Unit PEmpty PEmpty) : TableM C (net.State × (C.Party → Option (Keys C))) := do
  let Ro := reductionRoles aes D
  let state ← Ro.adversary (net.start (corruptInputs D fun _ => ()) [])
  let parts ← Ro.honest (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps Ro D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let (state, steps, sent) ← stepRound Ro D net noFunctionality state steps
  let log := (← get).log
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let view := fun (i j : C.Party) =>
    if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
  let high ← Ro.honest (liftComp ($ᵗ HashOutput) _)
  writeTable (.derive .seedGen .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
    (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
  for T in C.terms do
    match C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T with
    | some j =>
        writeTable (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
          (view (firstHonest (C.holders T)) k).term T)) (((corrupt j).map (·.seed T)).getD 0)
    | none => pure ()
  for j in C.parties do
    for i in C.parties do
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        writeTable (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((corrupt j).map (·.pairKey i)).getD 0)
  executeRounds Ro D net noFunctionality (setupRounds - 1) state steps

/-! ## The runs of the trees -/

/-- `newTree` with the building blocks `buildingBlocks`. -/
def newTreeWith {ι : Type} {G : OracleSpec ι}
    (buildingBlocks : Context C → ℕ → List Job → RunBuildingBlocks C E G) (i : C.Party) (keys : Keys C)
    (top : TopTree) (tree : Tree) : PartyM C E G TreeOutput := do
  let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E G))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (ceremonyRun K circuits settings buildingBlocks i keys) top tree).run' (0, 0) | failure
  pure output

/-- `ceremonyOutput` of bottom tree `b` with the randomizer `randomizer` in the place of the
randomizer search. It is a copy of the branch of a bottom tree of `ceremonyOutput`, the same but for
that step. The codeword comes from one hash, the message digest of the root at `randomizer`, and no
search runs. -/
def bottomOutputWith {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit)))) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (randomizer : Randomizer) : m (Option TreeOutput) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange chainCount).map fun l => (bottomKey b k, l)
  let some outputs ← run (bottomJobs b) | pure none
  let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
    let bits := outputs.getD (keys.idxOf (e, l)) []
    (digestAt bits 0, digestAt bits 1, digestAt bits 2)
  let commitment := fun (e : KeyIndex) => digestAt (outputs.getD (keys.length + e.val % 2 ^ layerHeight) []) 0
  let root ← lift (merkleNode parameter bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val)
  let message := littleEndianBytes 16 root
  let digest ← lift (Verification.messageDigestWithHash parameter topLayer (topKey b) message randomizer)
  let some encoding := Codeword.decode digest | pure none
  let some values ← run (signJobs b encoding) | pure none
  let path ← lift (merklePath parameter topLayer top.chainEnd (topKey b))
  let signature : LayerSignature := ⟨randomizer, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← lift (Verification.layerRootWithHash parameter topLayer (topKey b) message signature)
  if topRoot ≠ some top.root then pure none else
  pure (some (.bottom ⟨cpk, commitment, root, signature⟩))

/-- `newTreeWith` for bottom tree `b` with `bottomOutputWith` in the place of `ceremonyOutput`. -/
def newBottomWith {ι : Type} {G : OracleSpec ι}
    (buildingBlocks : Context C → ℕ → List Job → RunBuildingBlocks C E G) (i : C.Party) (keys : Keys C)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (randomizer : Randomizer) : PartyM C E G TreeOutput := do
  let some output ← (bottomOutputWith (m := StateT (ℕ × ℕ) (PartyM C E G))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (ceremonyRun K circuits settings buildingBlocks i keys) top b randomizer).run' (0, 0) | failure
  pure output

/-- The openings of each batch of a run of the top tree, from the top tree of the dealer. The output
of the job of chain `l` of top key `e` is the bits of its chain end. -/
def topLeak (top : TopTree) : List (List (List Bit)) :=
  chunks settings.batchSize (topJobs.map fun job => match job.kind with
    | .chainEnd e l => bitsOfDigest (top.chainEnd e l)
    | _ => [])

/-- The openings of each batch of a run of bottom tree `b`, from the answer `(tree, ρ)` of `tree b`.
The first ceremony opens the three digests of `cpk` of each chain, each commitment `c_e` and the
randomizer value `ρ` of top key `b`. The second ceremony opens the chain values of the top
signature. -/
def bottomLeak (b : Fin (2 ^ layerHeight)) (tree : BottomTree) (ρ : Digest) : List (List (List Bit)) :=
  chunks settings.batchSize ((bottomJobs b).map fun job => match job.kind with
    | .chainRow e l => bitsOfDigest (tree.cpk e l).1 ++ bitsOfDigest (tree.cpk e l).2.1 ++ bitsOfDigest (tree.cpk e l).2.2
    | .commitment e => bitsOfDigest (tree.commitment e)
    | .randomizer => bitsOfDigest ρ
    | _ => []) ++
  chunks settings.batchSize ((List.finRange chainCount).map fun l => bitsOfDigest (tree.topSignature.chainValues l))

/-- The building blocks of an emulated run, after the simulator of GS20, Theorem 2, which is for the
hybrid model. Here they run on the real network. They are the real building blocks, except that the
opening of batch `k` shifts the first term that the coalition lacks, so it opens batch `k` of
`openings` (MPClan, App. B). The shift is `openings` plus the outputs of the batch in the
clear on `seeds` and `parameter`. So the opening is batch `k` of `openings` only when the
reconstructed emulated output equals the output in the clear, that is outside the bad events of
consistency and of soundness of the check. `Rerand` makes that term uniform first (BBY23, Section
4.3). -/
def shiftedBuildingBlocks (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (ctx : Context C) (k : ℕ) (batch : List Job) :
    RunBuildingBlocks C E RealSpec :=
  { realRunBuildingBlocks K ctx settings.mode with
    output := fun v count => do
      let clear ← StateT.lift (oracleStep (batch.mapM (evalJob circuits parameter seeds)))
      let shift := fun g => ((openings.getD k []).flatten.getD g 0) + (clear.flatten.getD g 0)
      StateT.lift (openRep K ctx (fun T g => if lackedTerm D.1 = some T then v T g + shift g else v T g) count) }

/-- The program of emulated operator `i` in a run of `tree`. It is `treeProgram` with the building
blocks `buildingBlocks`. For a bottom tree it takes the randomizer `randomizer` of the dealer and
makes no randomizer search (`newBottomWith`). A top tree reads no randomizer. An operator without
keys, or without a top tree for a bottom tree, stops at once, as an operator that aborts. -/
def emulatedProgram (buildingBlocks : Context C → ℕ → List Job → RunBuildingBlocks C E RealSpec)
    (randomizer : Randomizer) (i : C.Party) (operator : OperatorState C) : Tree → PartyM C E RealSpec TreeOutput
  | .top => match operator.keys with
    | some keys => newTreeWith K circuits settings buildingBlocks i keys emptyTop .top
    | none => failure
  | .bottom b => match operator.keys, operator.top with
    | some keys, some top => newBottomWith K circuits settings buildingBlocks i keys top b randomizer
    | _, _ => failure

/-- The monad of the forger after the seed generation. Its state is the state of the game, with the
emulated operators in the place of the honest operators. -/
abbrev RedM (C : Committee) (σ : Type) := StateT (RealState C σ) (TableM C)

/-- One emulated run of `tree` with `net`, the openings `openings` and the randomizer `randomizer`
of the dealer, as `treeRun`. The clear
outputs of the shift use `gameSeeds` and `gameParameter` on the keys of the emulated operators, which
are values of the own table. Each operator keeps its first output. -/
def emulatedRun (net : Adversary C E Unit PEmpty PEmpty) (openings : List (List (List Bit)))
    (randomizer : Randomizer) (tree : Tree) : RedM C net.State Unit := do
  let s ← get
  let keys := fun i => (s.operators i).keys
  let buildingBlocks := shiftedBuildingBlocks K circuits settings D (gameParameter D keys) (gameSeeds D keys) openings
  let (state, outputs) ← StateT.lift (executePhase (reductionRoles aes D) D net noFunctionality
    (treeFuel circuits settings) s.adversary fun i =>
      emulatedProgram K circuits settings buildingBlocks randomizer i (s.operators i) tree)
  let (state, ok) ← StateT.lift (voteRound (reductionRoles aes D) D net state fun i =>
    (outputs i).map (treeVote tree))
  let operators := fun i => (s.operators i).keep (committed ok outputs i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag⟩ : RealState C net.State)

/-- At most `count` emulated runs of `tree`, each while a run is allowed, as `treeRuns`. -/
def emulatedRuns (net : Adversary C E Unit PEmpty PEmpty) (openings : List (List (List Bit)))
    (randomizer : Randomizer) (tree : Tree) : ℕ → RedM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      emulatedRun K circuits settings aes D net openings randomizer tree
      emulatedRuns net openings randomizer tree count

/-! ## The signing oracles of the forger -/

/-- A request of bottom tree `b`, as `treeRequest`. The forger asks `tree b`. With its answer it runs
the tree once if a run is allowed, with the randomizer of the top signature of the answer in the
place of the randomizer search. It gives the output of the first honest operator that holds one,
with the randomizer value of the answer. When `tree b` gives `none`, the randomizer search of the
dealer failed. Then the forger runs no tree run and changes no state of its own. The request
`tree b` itself made the dealer build bottom tree `b`. -/
def emulatedTreeRequest (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) :
    RedM C net.State (Option (BottomTree × Digest)) := do
  let dealt : Option (BottomTree × Digest) ← StateT.lift (tsigCall (.tree b))
  match dealt with
  | some (tree, ρ) =>
      emulatedRuns K circuits settings runLimit aes D net (bottomLeak settings b tree ρ) tree.topSignature.randomizer
        (.bottom b) 1
  | none => pure ()
  let s ← get
  match heldBottom D s.operators b, dealt with
  | some tree, some (_, ρ) => pure (some (tree, ρ))
  | _, _ => pure none

/-- A signing request to emulated operator `i` at key `e`, as `signRequest`. It ends the runs of the
bottom tree of `e`. An operator with keys, a top tree and an output of the bottom tree of `e` answers
with the oracle of `tsigGame`, and each other operator answers `none`. -/
def emulatedSignRequest {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) : RedM C σ (TsigSpec C q) := do
  modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true }
  let s ← get
  match (s.operators i).keys, (s.operators i).top, (s.operators i).bottom (treeOf e) with
  | some _, some _, some _ => StateT.lift (tsigCall q)
  | _, _, _ => pure (noAnswer q)

/-- The oracles of `forge`, as `realOracles` and the state cell of `dkgSigning`. `corrupt` gives
nothing, `tree b` runs the emulated tree, and `round1` and `round2` go to the emulated operators. -/
def forgeOracles (net : Adversary C E Unit PEmpty PEmpty) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec net.State)) (RedM C net.State) := fun t =>
  match t with
  | .inl t => StateT.lift (adversaryCall aes t)
  | .inr (.inl (.corrupt i)) => pure (noAnswer (.corrupt i))
  | .inr (.inl (.tree b)) => emulatedTreeRequest K circuits settings runLimit aes D net b
  | .inr (.inl (.round1 i J e message)) => emulatedSignRequest i e (.round1 i J e message)
  | .inr (.inl (.round2 i J e message parts)) => emulatedSignRequest i e (.round2 i J e message parts)
  | .inr (.inr .read) => (·.adversary) <$> (get : RedM C net.State _)
  | .inr (.inr (.write state)) => modify fun s : RealState C net.State => { s with adversary := state }

/-- A forgery with zero entries. -/
def idleForgery : Forgery := ⟨0, ⟨⟨0, by simp [lifetime]⟩, fun _ => ⟨0, fun _ => 0, fun _ => 0⟩⟩⟩

/-! ## The forger -/

/-- The forger of `tsigGame` from an adversary `A` of `dkgTsigGame` with the static coalition `D`,
after the proofs of Lemmas 3 to 5 of Gurkan and others. It follows `dkgTsigRun`.

* It asks `corrupt i` for each operator `i` of `D`.
* It runs the seed generation with `A` and emulated honest operators (`seedGenEmulation`).
* It runs the vote round after the seed generation and after each emulated run of a tree, as the
  game does. An emulated operator with an output hashes its vote in the own table. After the seed
  generation, each emulated operator with keys votes on the parameter of the public key.
* It runs the top tree at most `runLimit` times, with the openings from the top tree of the dealer.
  A top run reads no randomizer, so it gets `0`.
* If no honest operator holds a top tree, it outputs `idleForgery`, where the real game ends with no
  win.
* Else it runs `forge` on the public key and the top tree of `tsigGame`, with `forgeOracles`, and
  outputs its forgery with no change. -/
def dkgReduction (A : DkgTsigAdversary C E) : TsigAdversary C := fun pk top =>
  (do
    let corrupt ← OverPermutation.sequenceFin fun i =>
      if i ∈ D.1 then tsigCall (.corrupt i) else (pure none : TableM C (Option (Keys C)))
    let (state, keys) ← seedGenEmulation aes D pk.parameter corrupt A.net
    let (state, ok) ← voteRound (reductionRoles aes D) D A.net state fun i =>
      (keys i).map fun _ => (.vote 0 0 [bitsOfDigest pk.parameter] : Query C)
    let start : RealState C A.net.State :=
      ⟨state, fun i => ⟨committed ok keys i, none, fun _ => none⟩, fun _ => 0, fun _ => false, false⟩
    (do
      emulatedRuns K circuits settings runLimit aes D A.net (topLeak settings top) 0 .top runLimit
      match topHolder D (← get).operators with
      | none => pure idleForgery
      | some _ => simulateQ (forgeOracles K circuits settings runLimit aes D A.net) (A.forge pk top)).run' start).run'
    ⟨∅, ∅, []⟩

end ThresholdLeanXmss
