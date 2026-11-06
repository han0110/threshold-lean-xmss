import ThresholdLeanXmss.Scheme
import LeanXmss.Statement
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.EvalDist.TVDist

/-!
# Threshold leanXMSS security statement

The claims about the protocol of `Scheme.lean`, in the classical random-oracle model.

* There are `n = 2t - 1` operators, synchronous rounds and private authenticated links (GS20,
  Section 3.1). A rushing malicious adversary corrupts at most `t - 1` operators.
* `H` is a random oracle, except on the inputs that the MPC evaluates as a circuit, a chain step and
  the commitment `c_e`. There `H` is the fixed function `keccak`. `PRG` is `aes` under the key
  `H16("rss-prss" ‖ key ‖ session)`, and `aes` is a PRF. A counted oracle counts every call of `H`.
* The key generation securely computes the trusted dealer with selective abort (GL05, Definition 5).
  The distinguisher reads the joint output of the adversary and the honest operators (GL05,
  Definition 8, and Canetti 2000, Definition 4).
* The signing is strongly unforgeable in the game of PRAWNS, Figure 3, as `doc/sign.md`, Section 4,
  changes it.

Each bound is a fixed expression in the parameters, `q / 2 ^ bits` for `q` hash calls, the exact
error of the checks, and the advantage of a reduction that this file defines.
-/

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-! ## The oracle world -/

/-- The inputs that the MPC evaluates as a circuit, namely a chain step and the commitment `c_e`. -/
def MpcInput (input : HashInput) : Prop :=
  (∃ parameter lay key step l value, input = tweakableHashInput parameter (.chain lay key step)
    (Concrete.chainPayload l value)) ∨
  ∃ parameter e ρ, input = commitmentInput parameter e ρ

/-- `H` on one input. -/
def hashAnswer (keccak : HashInput → HashOutput) (input : HashInput) :
    StateT HashSpec.QueryCache ProbComp HashOutput :=
  open Classical in if MpcInput input then pure (keccak input) else HashSpec.randomOracle input

/-- `"rss-prss" ‖ key ‖ session`, the input of the `aes` key of a stream. -/
def streamKeyInput (key session : HashOutput) : HashInput :=
  "rss-prss".toUTF8.toList ++ bytesLE 32 key ++ bytesLE 32 session

/-- The `aes` model of `PRG` gives one bit of a stream at a position. -/
abbrev Aes := PRFScheme Digest (StreamId × ℕ) Bit

/-- The world gives private sampling, `H`, and `PRG` from `aes`. Each `H` call costs one query. -/
def world (keccak : HashInput → HashOutput) (aes : Aes) :
    QueryImpl (LocalSpec C) (AddWriterT ℕ (StateT HashSpec.QueryCache ProbComp)) :=
  (unifFwdImpl HashSpec + hashAnswer keccak +
    fun (x : KeyName C × HashOutput × HashOutput × StreamId × ℕ) => do
      let derived ← hashAnswer keccak (streamKeyInput x.2.1 x.2.2.1)
      pure (aes.eval (truncateHash derived) x.2.2.2)).withAddCost
      fun | .inl (.inl _) => 0 | _ => 1

/-- Run a computation in the world from an empty cache, with its number of hash queries. -/
def runWorld {α : Type} (keccak : HashInput → HashOutput) (aes : Aes)
    (oa : OracleComp (LocalSpec C) α) : ProbComp (α × ℕ) :=
  (simulateQ (world keccak aes) oa).run.run' ∅

/-! ## The network -/

/-- A rushing adversary. Each round it reads the messages to the corrupt operators, then it sends
the messages of the corrupt operators. -/
structure Adversary (C : Committee) (E : Type) where
  State : Type
  start : OracleComp (LocalSpec C) State
  /-- The start of a phase, namely the setup or a ceremony. -/
  newPhase : State → OracleComp (LocalSpec C) State
  round : State → (C.Party → C.Party → Option (Msg E)) →
    OracleComp (LocalSpec C) (State × (C.Party → C.Party → Option (Msg E)))

def Step.outbox {α : Type} : Step C E α → Mail C E
  | .wait outbox _ => outbox
  | .done _ => fun _ => none

def Step.output {α : Type} : Step C E α → Option α
  | .done out => out
  | .wait _ _ => none

def Step.isDone {α : Type} : Step C E α → Bool
  | .done _ => true
  | .wait _ _ => false

/-- Run the honest programs in synchronous rounds with the adversary, which controls `D`. -/
def runRounds {α : Type} (D : C.Coalition) (A : Adversary C E) :
    ℕ → A.State → (C.Party → Step C E α) → OracleComp (LocalSpec C) (A.State × (C.Party → Option α))
  | 0, state, steps => pure (state, fun i => (steps i).output)
  | fuel + 1, state, steps =>
    if C.parties.all fun i => decide (i ∈ D.1) || (steps i).isDone then
      pure (state, fun i => (steps i).output) else do
    let (state, sent) ← A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none
    let steps' ← Concrete.sequenceFin fun j => match steps j with
      | .done out => pure (Step.done out)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
          advance (resume fun k => if k ∈ D.1 then sent k j else (steps k).outbox j)
    runRounds D A fuel state steps'

/-- One phase, in which every honest operator runs its program to its output or its abort. -/
def runPhase {α : Type} (D : C.Coalition) (A : Adversary C E) (state : A.State)
    (program : C.Party → PartyM C E α) : OracleComp (LocalSpec C) (A.State × (C.Party → Option α)) := do
  let state ← A.newPhase state
  let steps ← Concrete.sequenceFin fun i =>
    if i ∈ D.1 then pure (Step.done none) else advance (program i).run
  runRounds D A roundLimit state steps

/-! ## Real and ideal key generation -/

/-- The outputs of an operator, namely its keys and then the output of each ceremony. `none` is an
abort. -/
abbrev DkgOutput (C : Committee) := Option (Keys C) × List (Option TreeOutput)

def latestTop (outputs : List (Option TreeOutput)) : Option TopTree :=
  outputs.foldl (fun top out => match out with | some (.top tree) => some tree | _ => top) none

def emptyTop : TopTree := ⟨fun _ _ => 0, 0⟩

variable (K : Constants C E) (settings : Settings) (circuits : Circuits)

/-- The real key generation runs the setup, then the ceremonies of `schedule` in order. -/
def realExecution (D : C.Coalition) (A : Adversary C E) (schedule : List Tree) :
    OracleComp (LocalSpec C) (A.State × (C.Party → DkgOutput C)) := do
  let (state, keys) ← runPhase D A (← A.start) fun i => setup i
  let none' : C.Party → List (Option TreeOutput) := fun _ => []
  let (state, trees) ← schedule.foldlM (init := (state, none')) fun (state, outputs) tree => do
    let (state, output) ← runPhase D A state fun i => match keys i, tree, latestTop (outputs i) with
      | none, _, _ => failure
      | some _, .bottom _, none => failure
      | some k, _, top => ceremony K circuits settings i k (top.getD emptyTop) tree
    pure (state, fun i => outputs i ++ [output i])
  pure (state, fun i => (keys i, trees i))

/-- A simulator. It gives the contributions of the corrupt operators, reads their outputs, and names
the honest operators that receive their outputs (GL05, Definition 5). It ends with a state of the
adversary. The outputs of the corrupt operators in the setup are their keys and the honest reveals
that the setup sends them. -/
structure Simulator (C : Committee) (σ : Type) where
  State : Type
  contribute : OracleComp (LocalSpec C) (State × (C.Party → Contribution C))
  setup : State → (C.Party → Option (Keys C)) → (C.Party → C.Party → List UInt8) →
    OracleComp (LocalSpec C) (State × Finset C.Party)
  ceremony : State → Option TreeOutput → OracleComp (LocalSpec C) (State × Finset C.Party)
  output : State → OracleComp (LocalSpec C) σ

/-- A party, which exists because `n ≥ 1`. -/
def firstParty (C : Committee) : C.Party := ⟨0, by have := C.one_le_t; unfold Committee.n; omega⟩

/-- The trusted dealer with selective abort. It derives the keys from fresh honest contributions and
the corrupt contributions, computes each ceremony in the clear, and gives each output to the honest
operators that the simulator names. -/
def idealExecution {σ : Type} (D : C.Coalition) (S : Simulator C σ) (schedule : List Tree) :
    OracleComp (LocalSpec C) (σ × (C.Party → DkgOutput C)) := do
  let (state, corrupt) ← S.contribute
  let honest ← Concrete.sequenceFin fun i => liftComp (sampleContribution i) _
  let contributions := fun i => if i ∈ D.1 then corrupt i else honest i
  let keys ← dealerKeys contributions
  let seeds ← deriveSeeds contributions
  let parameter := (keys (firstParty C)).parameter
  let top ← dealerTree circuits parameter seeds emptyTop .top
  let (state, receivers) ← S.setup state (fun i => if i ∈ D.1 then some (keys i) else none)
    fun i j => if i ∉ D.1 ∧ j ∈ D.1 then revealTo (honest i) i j else []
  let none' : C.Party → List (Option TreeOutput) := fun _ => []
  let (state, trees) ← schedule.foldlM (init := (state, none')) fun (state, outputs) tree => do
    let output ← dealerTree circuits parameter seeds
      (match top with | some (.top t) => t | _ => emptyTop) tree
    let (state, chosen) ← S.ceremony state output
    pure (state, fun i => outputs i ++ [if i ∈ chosen ∧ i ∈ receivers ∧ i ∉ D.1 then output else none])
  pure (← S.output state, fun i => (if i ∈ receivers ∧ i ∉ D.1 then some (keys i) else none, trees i))

/-- The joint output of the adversary and the honest operators, read by a distinguisher with oracle
access (GL05, Definition 8, and Canetti 2000, Definition 4). -/
abbrev Distinguisher (C : Committee) (σ : Type) :=
  σ × (C.Party → DkgOutput C) → OracleComp (LocalSpec C) Bool

/-! ## Error terms -/

/-- The most AND gates of one job. -/
def Circuits.jobGates (circuits : Circuits) : ℕ :=
  let gates := fun (c : Circuit) => (c.layers.map List.length).sum
  (Finset.univ.sup fun x : PublicParameter × KeyIndex × ChainIndex => gates (circuits.chainEnd x.1 x.2.1 x.2.2)) ⊔
  (Finset.univ.sup fun x : PublicParameter × KeyIndex × ChainIndex => gates (circuits.chainRow x.1 x.2.1 x.2.2)) ⊔
  (Finset.univ.sup fun x : PublicParameter × KeyIndex × ChainIndex × Digit =>
    gates (circuits.chainValue x.1 x.2.1 x.2.2.1 x.2.2.2)) ⊔
  (Finset.univ.sup fun x : PublicParameter × KeyIndex => gates (circuits.commitment x.1 x.2))

/-- `m` and `d` of the check of a full batch. -/
def batchHalvings : ℕ := halvings (settings.batchSize * circuits.jobGates)
def batchCoins : ℕ := coins (settings.batchSize * circuits.jobGates)

/-- The batches with a check in a ceremony. -/
def Tree.batches (tree : Tree) : ℕ :=
  let ceil := fun a : ℕ => (a + settings.batchSize - 1) / settings.batchSize
  match tree with
  | .top => ceil (2 ^ layerHeight * numChains)
  | .bottom _ => ceil (2 ^ layerHeight * numChains + 2 ^ layerHeight) + ceil numChains

/-- The soundness error of the checks of all batches, with `(d + 2 (m + 1)) / (|E| - 2)` each (GS20,
Lemmas 8 to 10, and `doc/dkg.md` 3.3). -/
def checkError (schedule : List Tree) : ℝ :=
  ((schedule.map (Tree.batches settings)).sum : ℝ) *
    ((batchCoins settings circuits + 2 * (batchHalvings settings circuits + 1) : ℕ) / (Fintype.card E - 2 : ℝ))

/-- Read `count` elements of `E` of the coin stream `index` from a PRF oracle, as `coinValues`. -/
def readCoin (index count : ℕ) : OracleComp (PRFScheme.PRFOracleSpec (StreamId × ℕ) Bit) (List E) := do
  let bits ← (List.range (elementBits * count)).mapM fun position =>
    query (spec := (StreamId × ℕ) →ₒ Bit) (((0, index, 0), position))
  pure ((List.range count).map fun k => K.encode.symm fun b => bits.getD (elementBits * k + b) 0)

/-- The PRF test of a coin checks if its first `k` values or its challenge hit the roots of `p`. -/
def rootTest {k : ℕ} (p : MvPolynomial (Fin k) E) (rejection : Bool) :
    OracleComp (PRFScheme.PRFOracleSpec (StreamId × ℕ) Bit) Bool := do
  let candidates ← (List.range 2).mapM fun index => readCoin K index 1
  let challenge := ((candidates.map (·.getD 0 0)).filter (· ∉ ({0, 1} : Set E))).take 1
  let values ← (if rejection then pure challenge else readCoin K 0 k :
    OracleComp (PRFScheme.PRFOracleSpec (StreamId × ℕ) Bit) (List E))
  pure (@decide (MvPolynomial.eval (fun b => values.getD b.val 0) p = 0) (Classical.propDecidable _))

/-- The advantage against `aes` of the best root test of a nonzero polynomial of degree at most two
in each of at most `d` coin values. A check needs `aes` under a fresh key to miss such roots. -/
def coinAdvantage (aes : Aes) : ℝ :=
  (⨆ (k : Fin (batchCoins settings circuits + 1)) (p : MvPolynomial (Fin k) E)
      (_ : p ≠ 0 ∧ ∀ b, p.degreeOf b ≤ 2) (rejection : Bool),
    ENNReal.ofReal ((PRFScheme.prfAdvantage aes (rootTest K p rejection)))).toReal

/-- The coin term, with `m + 2` calls of `coin` in each batch. -/
def coinError (aes : Aes) (schedule : List Tree) : ℝ :=
  ((schedule.map (Tree.batches settings)).sum * (batchHalvings settings circuits + 2) : ℕ) *
    coinAdvantage K settings circuits aes

/-- A key that the coalition does not know, namely a term with no corrupt holder or a pair of honest
operators. -/
def Hidden (D : C.Coalition) : KeyName C → Prop
  | .term T => ∀ j ∈ D.1, j ∉ C.holders T
  | .pair p => p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1
  | .coin => False

instance : Fintype (KeyName C) :=
  Fintype.ofEquiv (C.Term ⊕ C.Pair ⊕ Unit)
    ⟨fun | .inl T => .term T | .inr (.inl p) => .pair p | .inr (.inr ()) => .coin,
     fun | .term T => .inl T | .pair p => .inr (.inl p) | .coin => .inr (.inr ()),
     fun x => by rcases x with T | p | u <;> rfl, fun x => by cases x <;> rfl⟩

/-- The streams under the hidden keys, with one independent `aes` key for each key and session. -/
def hiddenStreams (aes : Aes) :
    PRFScheme (KeyName C × HashOutput → Digest) ((KeyName C × HashOutput) × StreamId × ℕ) Bit where
  keygen := $ᵗ (KeyName C × HashOutput → Digest)
  eval keys input := aes.eval (keys input.1) input.2

abbrev HiddenSpec (C : Committee) :=
  PRFScheme.PRFOracleSpec ((KeyName C × HashOutput) × StreamId × ℕ) Bit

def liftWorld {α : Type} (oa : StateT HashSpec.QueryCache ProbComp α) :
    StateT HashSpec.QueryCache (OracleComp (HiddenSpec C)) α :=
  StateT.mk fun s => liftComp (oa.run s) _

/-- The reduction to `hiddenStreams`. It is the real key generation and the distinguisher, with each
stream under a hidden key from the PRF oracle (CDI05, the PRSS of the lacked term). -/
def prgReduction (keccak : HashInput → HashOutput) (aes : Aes) (D : C.Coalition) (A : Adversary C E)
    (schedule : List Tree) (Z : Distinguisher C A.State) :
    PRFScheme.PRFAdversary ((KeyName C × HashOutput) × StreamId × ℕ) Bit :=
  let streams : QueryImpl (PrgSpec C) (StateT HashSpec.QueryCache (OracleComp (HiddenSpec C))) :=
    fun x => open Classical in if Hidden D x.1 then
        StateT.lift (query (spec := ((KeyName C × HashOutput) × StreamId × ℕ) →ₒ Bit)
          (m := OracleComp (HiddenSpec C)) ((x.1, x.2.2.1), x.2.2.2))
      else liftWorld do
        let derived ← hashAnswer keccak (streamKeyInput x.2.1 x.2.2.1)
        pure (aes.eval (truncateHash derived) x.2.2.2)
  let impl : QueryImpl (LocalSpec C) (StateT HashSpec.QueryCache (OracleComp (HiddenSpec C))) :=
    ((fun n => liftWorld (unifFwdImpl HashSpec n) :
        QueryImpl unifSpec (StateT HashSpec.QueryCache (OracleComp (HiddenSpec C)))) +
      (fun input => liftWorld (hashAnswer keccak input) :
        QueryImpl HashSpec (StateT HashSpec.QueryCache (OracleComp (HiddenSpec C))))) + streams
  (simulateQ impl (realExecution K settings circuits D A schedule >>= Z)).run' ∅

/-! ## Signing -/

/-- `H` as the fixed function `keccak`. -/
def fixedHash (keccak : HashInput → HashOutput) : QueryImpl HashSpec Id := fun input => keccak input

/-- `steps` chain steps from position `start` with `H = keccak`. -/
def chainWalk (keccak : HashInput → HashOutput) (parameter : PublicParameter) (lay : Layer)
    (e : KeyIndex) (l : ChainIndex) (start steps : ℕ) (value : Digest) : Digest :=
  simulateQ (fixedHash keccak) (Concrete.chainWalk parameter lay e l start steps value)

/-- The circuits compute the chain values and the commitment of leanXMSS with `H = keccak`. -/
def Circuits.Computes (circuits : Circuits) (keccak : HashInput → HashOutput) : Prop :=
  (∀ P e l x, (circuits.chainEnd P e l).eval (bitsOfDigest x) =
    bitsOfDigest (chainWalk keccak P topLayer e l 0 3 x)) ∧
  (∀ P e l x₀ x₁ x₂, (circuits.chainRow P e l).eval (bitsOfDigest x₀ ++ bitsOfDigest x₁ ++ bitsOfDigest x₂) =
    bitsOfDigest (chainWalk keccak P bottomLayer e l 0 1 x₀ ^^^ x₁) ++
    bitsOfDigest (chainWalk keccak P bottomLayer e l 0 2 x₀ ^^^ x₂) ++
    bitsOfDigest (chainWalk keccak P bottomLayer e l 0 3 x₀)) ∧
  (∀ P e l p x, (circuits.chainValue P e l p).eval (bitsOfDigest x) =
    bitsOfDigest (chainWalk keccak P topLayer e l 0 p.val x)) ∧
  (∀ P e ρ, (circuits.commitment P e).eval (bitsOfDigest ρ) =
    bitsOfDigest (truncateHash (keccak (commitmentInput P e ρ))))

/-- The oracles of PRAWNS, Figure 3, namely `OCorrupt`, the public outputs of a bottom tree, and the
two rounds of `OSign`, with the quorum as input (PRAWNS, Section 4). -/
inductive TsigQuery (C : Committee)
  | corrupt (i : C.Party)
  | tree (b : Fin (2 ^ layerHeight))
  | round1 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
  | round2 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest)

def TsigSpec (C : Committee) : OracleSpec (TsigQuery C)
  | .corrupt _ => Option (Keys C)
  | .tree _ => Option BottomTree
  | .round1 .. => Option Digest
  | .round2 .. => Option (ChainIndex → Option Digest)

/-- A forger. It gets the public key, the hash, and the signing oracles. -/
structure TsigAdversary (C : Committee) where
  main : PublicKey → OracleComp (LocalSpec C + TsigSpec C) Forgery

/-- The keys of the operators that sign, and the public outputs of the trees. -/
structure Dealt (C : Committee) where
  keys : C.Party → Option (Keys C)
  parameter : PublicParameter
  /-- The seeds of all terms, which only the game uses, for the signature of the dealer. -/
  seed : C.Term → HashOutput
  bottom : Fin (2 ^ layerHeight) → OracleComp (LocalSpec C) (Option BottomTree)

structure TsigState (C : Committee) where
  corrupt : Finset C.Party
  /-- The one message that the honest operators sign at a key, over all quorums and aborts. -/
  bound : KeyIndex → Option Message
  /-- The honest operators that sent chain parts at a key for a message. -/
  released : List (KeyIndex × Message × C.Party)
  /-- The randomizer values that honest signers accepted. -/
  opened : List (KeyIndex × Digest)

/-- The bottom tree of a bottom key. -/
def treeOf (e : KeyIndex) : Fin (2 ^ layerHeight) :=
  ⟨e.val / 2 ^ layerHeight, by
    have := e.isLt; simp only [lifetime, numLayers, layerHeight] at *; omega⟩

/-- The signing oracles. The rule of `doc/sign.md`, Section 4, replaces line 8 of PRAWNS, Figure 3.
At each key, honest operators sign one message only. Corruption is adaptive unless `static`, and
stops at `t - 1` operators. -/
def tsigOracles (dealt : Dealt C) (static : Bool) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (OracleComp (LocalSpec C))) := fun q =>
  match q with
  | .corrupt i => do
      let st ← get
      if static ∨ C.t - 1 < (insert i st.corrupt).card then pure none else do
        set { st with corrupt := insert i st.corrupt }
        pure (dealt.keys i)
  | .tree b => liftM (dealt.bottom b)
  | .round1 i J e message => do
      let st ← get
      let some keys := dealt.keys i | pure none
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ (st.bound e).any (· ≠ message) then pure none else do
        set { st with bound := Function.update st.bound e (some message) }
        some <$> liftM (signRound1 keys i J e message : OracleComp (LocalSpec C) Digest)
  | .round2 i J e message parts => do
      let st ← get
      let some keys := dealt.keys i | pure none
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else do
        let some tree ← liftM (dealt.bottom (treeOf e)) | pure none
        let own ← liftM (signRound1 keys i J e message : OracleComp (LocalSpec C) Digest)
        let parts := Function.update parts i own
        let some values ← liftM (signRound2 keys i J (tree.commitment e) e message parts :
            OracleComp (LocalSpec C) _) | pure none
        set { st with released := st.released ++ [(e, message, i)],
                      opened := st.opened ++ [(e, combine J parts)] }
        pure (some values)

/-- The signature of the dealer at bottom key `e` for `m`, which every honest quorum outputs. -/
def honestSignature (dealt : Dealt C) (e : KeyIndex) (m : Message) :
    OracleComp (LocalSpec C) (Option Signature) := do
  let some tree ← dealt.bottom (treeOf e) | pure none
  let value := fun x => (prfValue (C := C) dealt.seed x : OracleComp (LocalSpec C) Digest)
  let ρ ← value (randomizerPoint bottomLayer e)
  let some (randomness, encoding) ← signCodeword dealt.parameter (tree.commitment e) e m ρ
    | pure none
  let values ← Concrete.sequenceFin fun l => match (encoding l).val with
    | 0 => value (prfPoint bottomLayer e l 0)
    | 3 => pure (tree.cpk e l).2.2
    | p => do
        let f ← value (prfPoint bottomLayer e l p)
        pure ((if p = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ f)
  let path ← merklePath dealt.parameter bottomLayer (fun e l => (tree.cpk e l).2.2) e
  pure (some ⟨e, fun lay => if lay = bottomLayer then ⟨randomness, values, path⟩
    else tree.topSignature⟩)

/-- The game of PRAWNS, Figure 3, for strong unforgeability. The forgery wins if it verifies and
fewer than `t` operators gave chain parts at its key for its message, or if it differs from the
signature of the dealer there. Strong unforgeability goes beyond PRAWNS, which proves plain
unforgeability, and matches the SUF-CMA of leanVM. -/
def tsigGameWithKeys (dealt : Dealt C) (corrupt : Finset C.Party) (static : Bool) (pk : PublicKey)
    (forge : OracleComp (LocalSpec C + TsigSpec C) Forgery) :
    OracleComp (LocalSpec C) (Bool × TsigState C × Forgery) := do
  let (forgery, st) ← (simulateQ (QueryImpl.ofLift (LocalSpec C)
      (StateT (TsigState C) (OracleComp (LocalSpec C))) + tsigOracles dealt static) forge).run
    ⟨corrupt, fun _ => none, [], []⟩
  let verified ← Concrete.verify pk forgery.message forgery.signature
  let signers := st.corrupt ∪ ((st.released.filter fun r =>
    r.1 = forgery.signature.leafIndex ∧ r.2.1 = forgery.message).map (·.2.2)).toFinset
  let fresh ← if signers.card < C.t then pure true else do
    let honest ← honestSignature dealt forgery.signature.leafIndex forgery.message
    pure (decide (honest ≠ some forgery.signature))
  pure (verified && fresh, st, forgery)

/-- PRAWNS `KeyGen` samples a uniform parameter, uniform term seeds and uniform pair keys. -/
def prawnsKeyGen : ProbComp (PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) := do
  let parameter ← sampleKey
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairKeys ← $ᵗ (C.Pair → HashOutput)
  pure (truncateHash parameter, seeds, fun i => ⟨truncateHash parameter,
    fun T => if i ∈ C.holders T then seeds T else 0,
    fun j => if h : j = i then 0 else pairKeys (C.pairOf i j (Ne.symm h))⟩)

/-- The dealer data of `KeyGen`, with `run` evaluating the jobs of the trees. -/
def dealtFrom (parameter : PublicParameter) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C)
    (top : TopTree) (run : ℕ → List Job → OracleComp (LocalSpec C) (Option (List (List Bit)))) :
    Dealt C :=
  ⟨fun i => some (keys i), parameter, seeds, fun b => (fun | some (.bottom t) => some t | _ => none) <$>
    ceremonyOutput circuits parameter run top (.bottom b)⟩

def clearRun (seeds : C.Term → HashOutput) : ℕ → List Job → OracleComp (LocalSpec C) (Option (List (List Bit))) :=
  fun _ jobs => some <$> jobs.mapM (evalJob seeds)

/-- The game `G^tsig` of PRAWNS, Figure 3, with the trusted dealer (Theorem 4). -/
def tsigGame (A : TsigAdversary C) :
    OracleComp (LocalSpec C) (Bool × TsigState C × Forgery × Dealt C) := do
  let (parameter, seeds, keys) ← liftComp prawnsKeyGen _
  let some (.top top) ← dealerTree circuits parameter seeds emptyTop .top
    | pure (false, ⟨∅, fun _ => none, [], []⟩,
        ⟨0, ⟨⟨0, by decide⟩, fun _ => ⟨0, fun _ => 0, fun _ => 0⟩⟩⟩,
        ⟨fun _ => none, parameter, seeds, fun _ => pure none⟩)
  let pk : PublicKey := ⟨top.root, parameter⟩
  let dealt := dealtFrom circuits parameter seeds keys top (clearRun seeds)
  let (win, st, forgery) ← tsigGameWithKeys dealt ∅ false pk (A.main pk)
  pure (win, st, forgery, dealt)

variable (keccak : HashInput → HashOutput) (aes : Aes)

def tsigAdvantage (A : TsigAdversary C) : ℝ≥0∞ :=
  Pr[fun r => r.1.1 = true | runWorld keccak aes (tsigGame circuits A)]

/-- Every execution uses at most `q` hash calls, including the dealer, the honest operators and the
verification. -/
def HasHashQueryBound {α : Type} (oa : OracleComp (LocalSpec C) α) (q : ℕ) : Prop :=
  ∀ r ∈ support (runWorld keccak aes oa), r.2 ≤ q

/-- The task is to find `x'` at position `j - 1` whose chain reaches `f^3(x)`, given `y = f^j(x)`
for a uniform `x` and `j ∈ {1, 2, 3}` on a uniform chain (PRAWNS, Definition 3.3, for the chains of
leanXMSS). -/
abbrev SprAdversary (C : Committee) :=
  PublicParameter → Layer → KeyIndex → ChainIndex → Digest → ℕ → OracleComp (LocalSpec C) Digest

def sprGame (B : SprAdversary C) : OracleComp (LocalSpec C) Bool := do
  let parameter ← liftComp ($ᵗ Digest) _
  let lay ← liftComp ($ᵗ Layer) _
  let e ← liftComp ($ᵗ KeyIndex) _
  let l ← liftComp ($ᵗ ChainIndex) _
  let x ← liftComp ($ᵗ Digest) _
  let j := (← liftComp ($ᵗ Fin 3) _).val + 1
  let y ← Concrete.chainWalk parameter lay e l 0 j x
  let x' ← B parameter lay e l y j
  let top ← Concrete.chainWalk parameter lay e l 0 3 x
  let top' ← Concrete.chainWalk parameter lay e l (j - 1) (4 - j) x'
  pure (decide (top' = top))

def sprAdvantage (B : SprAdversary C) : ℝ≥0∞ :=
  Pr[fun r => r.1 = true | runWorld keccak aes (sprGame B)]

/-- The reduction to `sprGame` (PRAWNS, Theorem 3.1, Games 2 and 3). It is the dealer game with the
challenge chain built from `y` above position `j` and uniform masked values below it. It returns the
forged value on that chain, walked up to position `j - 1`. -/
def sprReduction (A : TsigAdversary C) : SprAdversary C := fun parameter lay e l y j => do
  let (_, seeds, keys) ← liftComp prawnsKeyGen _
  let keys := fun i => { keys i with parameter := parameter }
  let masks ← liftComp ($ᵗ (Fin 3 → Digest)) _
  let above := fun p => Concrete.chainWalk parameter lay e l j (p - j) y
  let run : ℕ → List Job → OracleComp (LocalSpec C) (Option (List (List Bit))) := fun _ jobs =>
    some <$> jobs.mapM fun job => do
      if lay = bottomLayer ∧ job.points = [prfPoint lay e l 0, prfPoint lay e l 1, prfPoint lay e l 2] then do
        let row ← (List.finRange 3).mapM fun p => if p.val + 1 < j then pure (masks p) else do
          let value ← above (p.val + 1)
          if p.val + 1 = 3 then pure value
          else pure (value ^^^ (← prfValue seeds (prfPoint lay e l (p.val + 1))))
        pure (row.flatMap bitsOfDigest)
      else if lay = topLayer ∧ job.points = [prfPoint lay e l 0] then
        match (List.finRange chainLength).find? (fun p =>
            @decide (job.circuit = circuits.chainValue parameter e l p) (Classical.propDecidable _)) with
        | some p => if j ≤ p.val then bitsOfDigest <$> above p.val else evalJob seeds job
        | none => bitsOfDigest <$> above 3
      else evalJob seeds job
  let some (.top top) ← ceremonyOutput circuits parameter run emptyTop .top | pure 0
  let pk : PublicKey := ⟨top.root, parameter⟩
  let (_, _, forgery) ← tsigGameWithKeys (dealtFrom circuits parameter seeds keys top run) ∅ false pk
    (A.main pk)
  let signature := forgery.signature
  let message ← if lay = bottomLayer then pure (bytesLE 32 forgery.message) else do
    let root ← Concrete.layerRoot parameter bottomLayer (keyAt signature.leafIndex bottomLayer)
      (bytesLE 32 forgery.message) (signature.layers bottomLayer)
    pure (bytesLE 16 (root.getD 0))
  let part := signature.layers lay
  let digest ← Concrete.messageDigest parameter lay e message part.randomness
  let some encoding := Codeword.decode digest | pure 0
  Concrete.chainWalk parameter lay e l (encoding l).val (j - 1 - (encoding l).val) (part.chainValues l)

/-- A collision of one chain step on the walks of two values from `position`. -/
def walkCollision (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (l : ChainIndex) :
    ℕ → ℕ → Digest → Digest → OracleComp (LocalSpec C) (Option (HashInput × HashInput))
  | 0, _, _, _ => pure none
  | steps + 1, position, a, b =>
    if a = b then pure none else
    if h : position < chainLength - 1 then do
      let inputA := tweakableHashInput parameter (.chain lay e ⟨position, h⟩) (Concrete.chainPayload l a)
      let inputB := tweakableHashInput parameter (.chain lay e ⟨position, h⟩) (Concrete.chainPayload l b)
      let outputA := truncateHash (← query (spec := HashSpec) inputA)
      let outputB := truncateHash (← query (spec := HashSpec) inputB)
      if outputA = outputB then pure (some (inputA, inputB))
      else walkCollision parameter lay e l steps (position + 1) outputA outputB
    else pure none

/-- The reduction to a collision of `keccak` on the MPC inputs. Either an honest signer accepted a
randomizer value with the commitment `c_e` of another value, or the forgery and the signature of
the dealer reach one chain end from two values. -/
def collisionReduction (A : TsigAdversary C) :
    OracleComp (LocalSpec C) (HashInput × HashInput) := do
  let (_, st, forgery, dealt) ← tsigGame circuits A
  let opened ← st.opened.mapM fun (e, ρ') => do
    let ρ ← (prfValue (C := C) dealt.seed (randomizerPoint bottomLayer e) : OracleComp (LocalSpec C) Digest)
    pure (if ρ ≠ ρ' then some (commitmentInput dealt.parameter e ρ, commitmentInput dealt.parameter e ρ')
      else none)
  let signature := forgery.signature
  let some honest ← honestSignature dealt signature.leafIndex forgery.message
    | pure ((opened.filterMap id).headD ([], []))
  let bottomRoot ← Concrete.layerRoot dealt.parameter bottomLayer signature.leafIndex
    (bytesLE 32 forgery.message) (honest.layers bottomLayer)
  let chains ← [bottomLayer, topLayer].flatMapM fun lay => do
    let key := keyAt signature.leafIndex lay
    let message := if lay = bottomLayer then bytesLE 32 forgery.message else bytesLE 16 (bottomRoot.getD 0)
    let part := honest.layers lay
    if (signature.layers lay).randomness ≠ part.randomness then pure [] else do
    let digest ← Concrete.messageDigest dealt.parameter lay key message part.randomness
    let some encoding := Codeword.decode digest | pure []
    (List.finRange numChains).mapM fun l =>
      walkCollision dealt.parameter lay key l chainLength (encoding l).val
        ((signature.layers lay).chainValues l) (part.chainValues l)
  pure ((opened.filterMap id ++ chains.filterMap id).headD ([], []))

/-- The probability that the reduction outputs two MPC inputs with one value of `keccak`. -/
def collisionAdvantage (A : TsigAdversary C) : ℝ≥0∞ :=
  Pr[fun r => r.1.1 ≠ r.1.2 ∧ MpcInput r.1.1 ∧ MpcInput r.1.2 ∧
      truncateHash (keccak r.1.1) = truncateHash (keccak r.1.2) |
    runWorld keccak aes (collisionReduction circuits A)]

/-! ## Composition and honest runs -/

/-- A forger that first plays the corrupt operators in the key generation. -/
structure ComposedAdversary (C : Committee) (E : Type) where
  dkg : Adversary C E
  forge : dkg.State → PublicKey → OracleComp (LocalSpec C + TsigSpec C) Forgery

/-- The first honest output of a scheduled ceremony that `pick` accepts. -/
def firstOutput {α : Type} (D : C.Coalition) (schedule : List Tree) (outputs : C.Party → DkgOutput C)
    (pick : Tree → TreeOutput → Option α) : Option α :=
  (C.parties.filter (· ∉ D.1)).firstM fun i =>
    ((outputs i).2.zip schedule).firstM fun (out, tree) => out.bind (pick tree)

/-- The game of Theorem 5 after the real key generation, as a distinguisher of its outputs. The
honest operators sign with their keys, and the public key and the trees come from honest outputs.
Without them there is no public key and the forger loses. -/
def tsigGameAfterDkg (D : C.Coalition) (schedule : List Tree) (A : ComposedAdversary C E) :
    Distinguisher C A.dkg.State := fun (state, outputs) => do
  let some top := firstOutput D schedule outputs (fun _ out => match out with
      | .top t => some t
      | _ => none)
    | pure false
  let some parameter := (C.parties.filter (· ∉ D.1)).firstM fun i => (outputs i).1.map (·.parameter)
    | pure false
  let pk : PublicKey := ⟨top.root, parameter⟩
  let seed := fun T => ((C.parties.filter (· ∉ D.1)).firstM fun i =>
    if i ∈ C.holders T then (outputs i).1.map (·.seed T) else none).getD 0
  let dealt : Dealt C := ⟨fun i => if i ∈ D.1 then none else (outputs i).1, parameter, seed, fun b =>
    pure (firstOutput D schedule outputs fun tree out => match tree, out with
      | .bottom b', .bottom t => if b' = b then some t else none
      | _, _ => none)⟩
  (·.1) <$> tsigGameWithKeys dealt D.1 true pk (A.forge state pk)

/-- The adversary of an honest run, which controls no operator. -/
def idle : Adversary C E := ⟨Unit, pure (), fun _ => pure (), fun _ _ => pure ((), fun _ _ => none)⟩

def noCoalition : C.Coalition := ⟨∅, by simp⟩

/-- The simulator of an honest run, which gives every output to every operator. -/
def everyone : Simulator C Unit :=
  ⟨Unit, pure ((), fun _ => ⟨[], fun _ => [], fun _ => []⟩), fun _ _ _ => pure ((), Finset.univ),
    fun _ _ => pure ((), Finset.univ), fun _ => pure ()⟩

/-- An honest quorum signs `m` at key `e` with the trusted dealer. The result is `none` if a
randomizer search fails, and otherwise tells whether the signature verifies. -/
def honestSigning (J : C.Quorum) (e : KeyIndex) (message : Message) :
    OracleComp (LocalSpec C) (Option Bool) := do
  let (parameter, seeds, keys) ← liftComp prawnsKeyGen _
  let some (.top top) ← dealerTree circuits parameter seeds emptyTop .top | pure none
  let some (.bottom tree) ← dealerTree circuits parameter seeds top (.bottom (treeOf e)) | pure none
  let parts ← Concrete.sequenceFin fun i => if i ∈ J.1 then signRound1 (keys i) i J e message else pure 0
  let some _ ← signCodeword parameter (tree.commitment e) e message (combine J parts) | pure none
  let chainParts ← Concrete.sequenceFin fun i => do
    let values ← signRound2 (keys i) i J (tree.commitment e) e message parts
    pure fun l => ((values.bind (· l)).getD 0)
  let some signature ← assemble parameter tree e message J parts chainParts | pure (some false)
  some <$> Concrete.verify ⟨top.root, parameter⟩ message signature

/-! ## The claims -/

variable (K : Constants C E) (settings : Settings) (circuits : Circuits)
variable (keccak : HashInput → HashOutput) (aes : Aes)

/-- An honest key generation gives the outputs of the dealer, except when a check aborts on a zero
coin (Theorem 1). Security with abort alone allows a protocol that always aborts. -/
def DkgCompletenessStatement : Prop :=
  ∀ schedule : List Tree, schedule.head? = some .top →
    tvDist ((fun r => r.1.2) <$> runWorld keccak aes (realExecution K settings circuits noCoalition idle schedule))
      ((fun r => r.1.2) <$> runWorld keccak aes (idealExecution circuits noCoalition everyone schedule)) ≤
      checkError (E := E) settings circuits schedule + coinError K settings circuits aes schedule

/-- The setup and the ceremonies of a schedule securely compute the trusted dealer with selective
abort against a static coalition (Theorem 2, after GL05, Definition 5, and GS20, Theorem 2). The
ideal run keeps the hash budget of the real run. -/
def DkgSecurityStatement : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E) (schedule : List Tree), ∃ S : Simulator C A.State,
    ∀ (Z : Distinguisher C A.State) (q : ℕ),
      HasHashQueryBound keccak aes (realExecution K settings circuits D A schedule >>= Z) q →
      HasHashQueryBound keccak aes (idealExecution circuits D S schedule >>= Z) q ∧
      |(Pr[fun r => r.1 = true | runWorld keccak aes (realExecution K settings circuits D A schedule >>= Z)]).toReal -
        (Pr[fun r => r.1 = true | runWorld keccak aes (idealExecution circuits D S schedule >>= Z)]).toReal| ≤
        checkError (E := E) settings circuits schedule + coinError K settings circuits aes schedule +
          PRFScheme.prfAdvantage (hiddenStreams aes) (prgReduction K settings circuits keccak aes D A schedule Z) +
          q / 2 ^ 125

/-- Every signature of an honest quorum verifies (Theorem 3, after PRAWNS, Definition 2.1). -/
def SigningCorrectnessStatement : Prop :=
  ∀ (J : C.Quorum) (e : KeyIndex) (m : Message),
    ∀ r ∈ support (runWorld keccak aes (honestSigning circuits J e m)), r.1 ≠ some false

/-- The signing is strongly unforgeable with the trusted dealer and adaptive corruption (Theorem 4,
by the game sequence of PRAWNS, Theorem 3.1). The guess of a layer, a key, a chain and a position
costs `2 · 2 ^ 32 · 58 · 3`. -/
def SigningSecurityStatement : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasHashQueryBound keccak aes (tsigGame circuits A) q →
    tsigAdvantage circuits keccak aes A ≤ q / 2 ^ 126 + collisionAdvantage circuits keccak aes A +
      (2 * lifetime * numChains * (chainLength - 1) : ℕ) * sprAdvantage keccak aes (sprReduction circuits A)

/-- Theorem 4 holds with the setup and the ceremonies of a schedule in place of the dealer (Theorem
5). The corruption is static, the strongest that the literature proves, because GS20 proves the key
generation for static corruption only and no paper composes a key generation with PRAWNS. -/
def ComposedSecurityStatement : Prop :=
  ∀ (D : C.Coalition) (A : ComposedAdversary C E) (schedule : List Tree) (q : ℕ),
    HasHashQueryBound keccak aes (realExecution K settings circuits D A.dkg schedule >>= tsigGameAfterDkg D schedule A) q →
    ∃ B : TsigAdversary C, HasHashQueryBound keccak aes (tsigGame circuits B) q ∧
      (Pr[fun r => r.1 = true | runWorld keccak aes
          (realExecution K settings circuits D A.dkg schedule >>= tsigGameAfterDkg D schedule A)]).toReal ≤
        (tsigAdvantage circuits keccak aes B).toReal +
          checkError (E := E) settings circuits schedule + coinError K settings circuits aes schedule +
          PRFScheme.prfAdvantage (hiddenStreams aes)
            (prgReduction K settings circuits keccak aes D A.dkg schedule (tsigGameAfterDkg D schedule A)) +
          q / 2 ^ 125

end ThresholdLeanXmss

open ThresholdLeanXmss in
/-- The security claim, for every committee of at most 16 signers and every circuit family that
computes the chain and the commitment of `keccak`. -/
abbrev ThresholdLeanXmssSecurityStatement : Prop :=
  ∀ (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (K : Constants C E) (settings : Settings) (circuits : Circuits)
    (keccak : HashInput → HashOutput) (aes : Aes),
    C.t ≤ 16 → circuits.Computes keccak →
      DkgCompletenessStatement K settings circuits keccak aes ∧
      DkgSecurityStatement K settings circuits keccak aes ∧
      SigningCorrectnessStatement (C := C) circuits keccak aes ∧
      SigningSecurityStatement (C := C) circuits keccak aes ∧
      ComposedSecurityStatement K settings circuits keccak aes
