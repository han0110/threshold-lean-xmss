import ThresholdLeanXmss.Ideal

/-!
# The simulators and the reductions

The explicit simulators of the keygen and of a ceremony, the reduction to the AES term, and the
reductions of PRAWNS, Theorem 3.1, which the claims of `Statement.lean` name.
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

/-! ## The reductions of the signing -/

/-- A computation of `H` in the local oracles. -/
def liftRo {β : Type} (oa : OracleComp (RoSpec C) β) : OracleComp (LocalSpec C) β := liftComp oa _

/-- All steps run in the local oracles. -/
def localRoles : Roles C (OracleComp (LocalSpec C)) := ⟨fun oa => oa, fun oa => oa⟩

/-- The local copy of `KeyGen`. -/
def localKeyGen : OracleComp (LocalSpec C) (Option (Dealt C (OracleComp (LocalSpec C)))) :=
  keyGenWith (fun oa => liftComp oa _) liftRo

/-- A collision of one chain step on the walks of two values from `position`. -/
def walkCollision (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (l : ChainIndex) :
    ℕ → ℕ → Digest → Digest → OracleComp HashSpec (Option (HashInput × HashInput))
  | 0, _, _, _ => pure none
  | steps + 1, position, a, b =>
    if a = b then pure none else
    if h : position < chainLength - 1 then do
      let inputA := tweakableHashInput parameter (.chain lay e ⟨position, h⟩) (Concrete.chainPayload l a)
      let inputB := tweakableHashInput parameter (.chain lay e ⟨position, h⟩) (Concrete.chainPayload l b)
      let outputA := truncateHash (← Concrete.oracleHash inputA)
      let outputB := truncateHash (← Concrete.oracleHash inputB)
      if outputA = outputB then pure (some (inputA, inputB))
      else walkCollision parameter lay e l steps (position + 1) outputA outputB
    else pure none

/-- The first node on the paths of two leaves of key `e` where two different inputs give one output. -/
def pathCollision (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (path path' : Fin layerHeight → Digest) :
    ℕ → Digest → Digest → OracleComp HashSpec (Option (HashInput × HashInput))
  | 0, _, _ => pure none
  | levels + 1, node, node' => do
    let level := layerHeight - (levels + 1)
    let sibling := fun (p : Fin layerHeight → Digest) => if h : level < layerHeight then p ⟨level, h⟩ else 0
    let payload := fun (current other : Digest) => if e.val.testBit level then Concrete.nodePayload other current
      else Concrete.nodePayload current other
    let input := tweakableHashInput parameter (.node lay (level + 1) (e.val / 2 ^ (level + 1))) (payload node (sibling path))
    let input' := tweakableHashInput parameter (.node lay (level + 1) (e.val / 2 ^ (level + 1))) (payload node' (sibling path'))
    let output := truncateHash (← Concrete.oracleHash input)
    let output' := truncateHash (← Concrete.oracleHash input')
    if output = output' ∧ input ≠ input' then pure (some (input, input'))
    else pathCollision parameter lay e path path' levels output output'

/-- What `KeyGen` exposes on one layer at the key of a forgery. `exposed` is the message and the
randomness of the signature whose chain parts reached `t` operators, if any. Without one, every
chain is at its end. -/
structure Reference where
  exposed : Option (HashInput × Randomness)
  chainValues : ChainIndex → Digest
  path : Fin layerHeight → Digest

/-- The encoding of a reference. -/
def Reference.encoding (ref : Reference) (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) :
    OracleComp HashSpec (Option Encoding) :=
  match ref.exposed with
  | some (message, randomness) => Codeword.decode <$> Concrete.messageDigest parameter lay e message randomness
  | none => pure (some fun _ => digit (chainLength - 1))

variable {m : Type → Type} [Monad m]

/-- On one layer at the key of the forgery, its message and layer signature, and the reference of
`KeyGen` there. On the bottom layer, the reference is the signature of the exposed message `m'` of
PRAWNS, Theorem 3.1, Game 2, or the chain ends if no message is exposed. On the top layer, it is the
signature of the root of the bottom tree, or the chain ends if the bottom tree is missing. -/
def layerViews (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) (st : TsigState C)
    (forgery : Forgery) (lay : Layer) : m (Option (HashInput × LayerSignature × Reference)) := do
  let index := forgery.signature.leafIndex
  let b := treeOf index
  if lay = bottomLayer then do
    let some tree ← dealt.bottom b | pure none
    let ends := fun l => (tree.cpk index l).2.2
    let path ← lift (tweakable (merklePath dealt.parameter bottomLayer (fun e l => (tree.cpk e l).2.2) index))
    let reference ← match exposedMessage st index with
      | some message' => do
          match ← honestSignature lift dealt index message' with
          | some given => pure ⟨some (bytesLE 32 message', (given.layers bottomLayer).randomness),
              (given.layers bottomLayer).chainValues, path⟩
          | none => pure ⟨none, ends, path⟩
      | none => pure ⟨none, ends, path⟩
    pure (some (bytesLE 32 forgery.message, forgery.signature.layers bottomLayer, reference))
  else do
    let root ← lift (tweakable (Concrete.layerRoot dealt.parameter bottomLayer index (bytesLE 32 forgery.message)
      (forgery.signature.layers bottomLayer)))
    let path ← lift (tweakable (merklePath dealt.parameter topLayer dealt.top.chainEnd (topKey b)))
    let reference : Reference ← match ← dealt.bottom b with
      | some tree => pure ⟨some (bytesLE 16 tree.root, tree.topSignature.randomness), tree.topSignature.chainValues, path⟩
      | none => pure ⟨none, dealt.top.chainEnd (topKey b), path⟩
    pure (some (bytesLE 16 (root.getD 0), forgery.signature.layers topLayer, reference))

/-- A collision of `Th` between a forged layer signature and the reference on one layer. It is the
first pair of different inputs with one output along the verification, namely at the message
digest, at a chain step, at the leaf, or at a node of the authentication path. -/
def layerCollision (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (message : HashInput)
    (part : LayerSignature) (reference : Reference) : OracleComp HashSpec (Option (HashInput × HashInput)) := do
  let digestInput := fun (m : HashInput) (randomness : Randomness) =>
    tweakableHashInput parameter (.message lay e) (m ++ bytesLE 16 randomness)
  let digest ← Concrete.messageDigest parameter lay e message part.randomness
  if let some (message', randomness') := reference.exposed then
    let digest' ← Concrete.messageDigest parameter lay e message' randomness'
    if digestInput message part.randomness ≠ digestInput message' randomness' ∧ digest = digest' then
      return some (digestInput message part.randomness, digestInput message' randomness')
  let some encoding := Codeword.decode digest | pure none
  let some encoding' ← reference.encoding parameter lay e | pure none
  let chains ← (List.finRange numChains).mapM fun l => do
    let top := max (encoding l).val (encoding' l).val
    let value ← Concrete.chainWalk parameter lay e l (encoding l).val (top - (encoding l).val) (part.chainValues l)
    let value' ← Concrete.chainWalk parameter lay e l (encoding' l).val (top - (encoding' l).val) (reference.chainValues l)
    walkCollision parameter lay e l chainLength top value value'
  if let some found := (chains.filterMap id).head? then return some found
  let ends ← Concrete.sequenceFin fun l => Concrete.recoverChain parameter lay e l (encoding l) (part.chainValues l)
  let ends' ← Concrete.sequenceFin fun l => Concrete.recoverChain parameter lay e l (encoding' l) (reference.chainValues l)
  let leaf ← Concrete.leafHash parameter lay e ends
  let leaf' ← Concrete.leafHash parameter lay e ends'
  if ends ≠ ends' ∧ leaf = leaf' then
    pure (some (tweakableHashInput parameter (.leaf lay e) (Concrete.leafPayload ends),
      tweakableHashInput parameter (.leaf lay e) (Concrete.leafPayload ends')))
  else pathCollision parameter lay e part.path reference.path layerHeight leaf leaf'

/-- `E_1` of Theorem 3.1, Game 1, as a collision of `Th`. An honest signer accepted a randomizer
value whose commitment `c_e` matches another value. Or a layer of the forgery collides with the
reference of `KeyGen` there. -/
def findCollision (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) (st : TsigState C)
    (forgery : Forgery) : m (Option (HashInput × HashInput)) := do
  let opened ← st.opened.mapM fun (e, ρ') => do
    let ρ ← dealt.value (.randomizer bottomLayer e)
    pure (if ρ ≠ ρ' then some (commitmentInput dealt.parameter e ρ, commitmentInput dealt.parameter e ρ') else none)
  let layers ← [bottomLayer, topLayer].mapM fun lay => do
    let some (message, part, reference) ← layerViews lift dealt st forgery lay | pure none
    lift (tweakable (layerCollision dealt.parameter lay (keyAt forgery.signature.leafIndex lay) message part reference))
  pure (opened.filterMap id ++ layers.filterMap id).head?

/-- The reduction to collision resistance of the fixed `Th` (PRAWNS, Theorem 3.1, Game 1). It wins
when the collision lies on chain steps or commitments. A collision on leaves, nodes or digests is a
random-oracle event of the signing claim. -/
def collisionReduction (A : TsigAdversary C) : CollisionAdversary C := do
  let some dealt ← localKeyGen | pure ([], [])
  let (_, st, forgery) ← tsigGameWith localRoles dealt A
  (·.getD ([], [])) <$> findCollision liftRo dealt st forgery

/-- The point of position `p` of the target chain of a guess. -/
def Guess.point (guess : Guess) (p : ℕ) (h : p < chainLength := by decide) : Point :=
  .chain guess.1 guess.2.1 guess.2.2.1 ⟨p, h⟩

/-- `E_2` of Theorem 3.1, Game 2. On the target chain, position `j` lies above the forgery and at or
below the reference of `KeyGen` at its key. -/
def coveredAt (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) (st : TsigState C)
    (guess : Guess) (forgery : Forgery) : m Bool := do
  let (lay, e, l, j) := guess
  if keyAt forgery.signature.leafIndex lay ≠ e then pure false else do
  let some (message, part, reference) ← layerViews lift dealt st forgery lay | pure false
  let some forged ← lift (tweakable
    (Codeword.decode <$> Concrete.messageDigest dealt.parameter lay e message part.randomness)) | pure false
  let some given ← lift (tweakable (reference.encoding dealt.parameter lay e)) | pure false
  pure (decide ((forged l).val < j.val + 1 ∧ j.val + 1 ≤ (given l).val))

/-- The operators `0` to `t - 1` as a quorum. -/
def firstQuorum (C : Committee) : Option C.Quorum :=
  let J := Finset.univ.filter fun i : C.Party => i.val < C.t
  if h : J.card = C.t then some ⟨J, h⟩ else none

/-- The reduction to the threshold PRF (PRAWNS, Theorem 3.1, Games 2 and 3). It samples its own
parameter and guesses the target. It answers the positions below the target from `OChallenge`, and
every other PRF value from `t` parts of `OEval` under a fixed context. Signing goes to `OEval`, also
for a request that reaches fewer than `t` signers. Corruption goes to `OCorrupt`, and the keys carry
the parameter of the reduction. It outputs `1` if the forgery verifies, `E_2` holds and `E_1` does
not. -/
def tprfReduction (A : TsigAdversary C) : TprfAdversary C := do
  let guess ← liftComp ($ᵗ Guess) _
  let parameter ← liftComp ($ᵗ PublicParameter) _
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (LocalSpec C + TprfSpec C) β := fun oa => liftComp oa _
  let ask := fun (q : TprfQuery C) => (OracleComp.lift (OracleSpec.query (spec := LocalSpec C + TprfSpec C) (.inr q)))
  let some quorum := firstQuorum C | pure false
  let value : Point → OracleComp (LocalSpec C + TprfSpec C) Digest := fun x =>
    if ∃ p < guess.2.2.2.val + 1, ∃ h : p < chainLength, x = guess.point p h then do
      pure ((← ask (.challenge x) : Option Digest).getD 0)
    else do
      let parts ← C.parties.mapM fun i =>
        if i ∈ quorum.1 then do pure ((← ask (.eval i quorum x 0) : Option Digest).getD 0) else pure 0
      pure (combine quorum fun i => parts.getD i.val 0)
  let dealtBase := dealtWith lift parameter (fun _ => ⟨parameter, fun _ => 0, fun _ => 0⟩) emptyTop value
  let some (.top top) ← referenceTree (fun oa => lift (tweakable oa)) value parameter emptyTop .top | pure false
  let dealt : Dealt C (OracleComp (LocalSpec C + TprfSpec C)) :=
    { dealtBase with
      top := top
      part := fun i J x message => do pure ((← ask (.eval i J x message) : Option Digest).getD 0)
      bottom := fun b => (fun | some (.bottom tree) => some tree | _ => none) <$>
        referenceTree (fun oa => lift (tweakable oa)) value parameter top (.bottom b) }
  let roles : Roles C (OracleComp (LocalSpec C + TprfSpec C)) := ⟨fun oa => liftComp oa _, fun oa => liftComp oa _⟩
  let corrupting : QueryImpl (TsigSpec C) (StateT (TsigState C) (OracleComp (LocalSpec C + TprfSpec C))) := fun q =>
    match q with
    | .corrupt i => do
        let st ← get
        if C.t - 1 < (insert i st.corrupt).card then pure none else do
          let keys : Option (Keys C) ← liftM (ask (.corrupt i))
          set { st with corrupt := insert i st.corrupt }
          pure (keys.map fun k => { k with parameter := parameter })
    | q => tsigOracles lift dealt q
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (OracleComp (LocalSpec C + TprfSpec C))) :=
    fun t => liftM (roles.adversary (OracleComp.lift (OracleSpec.query t)))
  let (forgery, st) ← (simulateQ (forger + corrupting) (A ⟨top.root, parameter⟩ top)).run ⟨∅, fun _ => none, [], []⟩
  let verified ← lift (tweakable (Concrete.verify ⟨top.root, parameter⟩ forgery.message forgery.signature))
  let covered ← coveredAt lift dealt st guess forgery
  let collision ← findCollision lift dealt st forgery
  pure (verified && covered && collision.isNone)

/-- The reduction to the iterated SPR of the chains (PRAWNS, Theorem 3.1, Game 3). It runs Game 3
with the challenge parameter, the target chain from `y` at and above the target position, and
uniform masked values below it. It returns the forged value on the target chain, walked up to
position `j - 1`. -/
def sprReduction (A : TsigAdversary C) : SprAdversary C := fun parameter guess y => do
  let (lay, e, l, j) := guess
  let (_, seeds, keys) ← liftComp prawnsKeyGen _
  let keys := fun i => { keys i with parameter := parameter }
  let masks ← liftComp ($ᵗ (Fin (chainLength - 1) → Digest)) _
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (LocalSpec C) β := liftRo
  let above := fun (p : ℕ) => lift (tweakable (Concrete.chainWalk parameter lay e l (j.val + 1) (p - (j.val + 1)) y))
  let F := fun x => lift (prfValue seeds x)
  let job : Job → OracleComp (LocalSpec C) (List Bit) := fun job =>
    match job.kind with
    | .chainRow e' l' => if lay = bottomLayer ∧ e' = e ∧ l' = l then do
        let row ← (List.finRange (chainLength - 1)).mapM fun p =>
          if p.val + 1 < j.val + 1 then pure (masks p) else do
            let v ← above (p.val + 1)
            if p.val + 1 = chainLength - 1 then pure v
            else pure (v ^^^ (← F (.chain lay e l ⟨p.val + 1, by omega⟩)))
        pure (row.flatMap bitsOfDigest)
      else referenceJob (fun oa => lift (tweakable oa)) F parameter job
    | .chainEnd e' l' => if lay = topLayer ∧ e' = e ∧ l' = l then bitsOfDigest <$> above (chainLength - 1)
      else referenceJob (fun oa => lift (tweakable oa)) F parameter job
    | .chainValue e' l' p => if lay = topLayer ∧ e' = e ∧ l' = l ∧ j.val + 1 ≤ p.val then bitsOfDigest <$> above p.val
      else referenceJob (fun oa => lift (tweakable oa)) F parameter job
    | _ => referenceJob (fun oa => lift (tweakable oa)) F parameter job
  let tree := fun top t => ceremonyOutput (fun oa => lift (tweakable oa)) parameter
    (fun jobs => some <$> jobs.mapM job) top t
  let some (.top top) ← tree emptyTop .top | pure 0
  let dealt : Dealt C (OracleComp (LocalSpec C)) :=
    { dealtWith lift parameter keys top F with
      bottom := fun b => (fun | some (.bottom t) => some t | _ => none) <$> tree top (.bottom b) }
  let (_, _, forgery) ← tsigGameWith localRoles dealt A
  let signature := forgery.signature
  lift (tweakable do
    let root ← Concrete.layerRoot parameter bottomLayer (keyAt signature.leafIndex bottomLayer)
      (bytesLE 32 forgery.message) (signature.layers bottomLayer)
    let message := if lay = bottomLayer then bytesLE 32 forgery.message else bytesLE 16 (root.getD 0)
    let part := signature.layers lay
    let digest ← Concrete.messageDigest parameter lay e message part.randomness
    let some encoding := Codeword.decode digest | pure 0
    Concrete.chainWalk parameter lay e l (encoding l).val (j.val - (encoding l).val) (part.chainValues l))

end ThresholdLeanXmss
