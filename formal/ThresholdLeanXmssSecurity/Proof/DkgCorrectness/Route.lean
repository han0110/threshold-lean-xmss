import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cores

/-!
# The route with one cut, the statements

The run level of `DkgCorrectness` with one ceremony as the unit. A run of the top tree is one
ceremony and local steps. A run of a bottom tree is cut one time, after the search of its head.

* Part 1 has the ledger of the caches and the readiness `RunReadyL` with `HiddenProvenance`.
* Part 2 has the two statements on one ceremony, `CeremonyBad` and `CeremonySupport`.
* Part 3 has the statements on a run of a tree, namely `TopCover` for the top tree and the facts at
  the cut of a bottom tree.
* Part 4 has `ReadyHopL`, the hop of the readiness at the test `RunReadyL`, and the statements on the
  provenance of the hidden keys that it needs.

`Game.lean` has the game with the readiness test as a parameter, and `Glue.lean` has the glue to
`Part1With`.
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

/-! ## Part 1. The ledger and the readiness -/

/-- Each hidden stream key of the cache is the output of a cached derive input of a PRSS setup. -/
def HiddenProvenance (D : C.Coalition) (world : StreamState C) : Prop :=
  ∀ name key ρ idx position, Hidden D name → world.2 ((name, key), ρ, idx, position) ≠ none →
    ∃ kind parts, world.1 (.derive .prss kind parts) = some key

/-- The caches are within the ledger `ℓ`. These are the four budget parts of `RunReady`. -/
def LedgerFits (ℓ : StartBudget) (world : StreamState C) : Prop :=
  SplitCacheBound (splitRegionCache SplitHashDomain world.1) ℓ.split ∧
    (∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 world.1 seen keys ∧
      seen.card ≤ ℓ.coins ∧ keys.card ≤ ℓ.keys) ∧
    (∃ salts : Finset (List Bit), DigestSaltsCovered world.1 salts ∧ salts.card ≤ ℓ.salts) ∧
    HiddenKeyBound world.2 ℓ.hiddenKeys

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The honest coin keys of `batches` batches, at most `n (R + 2)` in each batch. -/
def coinKeysOf (C : Committee) (batches : ℕ) : ℕ :=
  batches * C.n * (maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2)

/-- The ledger after one ceremony of `batches` batches in a phase of `rounds` rounds, with an
adversary of `step` calls in a round. -/
def ledgerStep (C : Committee) (step rounds batches : ℕ) (ℓ : StartBudget) : StartBudget :=
  ⟨ℓ.split + rounds * step + batches * termHashes C, ℓ.coins + rounds * step + coinKeysOf circuits settings C batches,
    ℓ.keys + coinKeysOf circuits settings C batches, ℓ.salts + rounds * step + batches * termHashes C,
    ℓ.hiddenKeys + 1⟩

/-- A ledger is within the budgets of `batchCheckError`. The charge of the pilot for the tested check
has two rounds more than the fuel of a batch, so the charged cells have a padding of `2 * step`. -/
def LedgerRoom (C : Committee) (q step : ℕ) (ℓ : StartBudget) : Prop :=
  ℓ.coins + 2 * step ≤ 2 * q + 2 * gameCoinKeys circuits settings runLimit C ∧
    ℓ.keys ≤ 2 * gameCoinKeys circuits settings runLimit C ∧
    ℓ.salts ≤ 2 * splitBudget settings runLimit C q

/-- The readiness with the provenance of the hidden keys. -/
def RunReadyL (budget : StartBudget) (D : C.Coalition) {σ : Type} (s : RealState C σ) (world : StreamState C) :
    Prop :=
  RunReady prims budget D s world ∧ HiddenProvenance D world

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- `RunReadyL` gives `RunReady`. -/
theorem runReady_of_runReadyL {budget : StartBudget} {D : C.Coalition} {σ : Type} {s : RealState C σ}
    {world : StreamState C} (h : RunReadyL prims budget D s world) : RunReady prims budget D s world :=
  h.1

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A ready start is within the ledger of its budget. -/
theorem ledgerFits_of_runReady {budget : StartBudget} {D : C.Coalition} {σ : Type} {s : RealState C σ}
    {world : StreamState C} (h : RunReady prims budget D s world) : LedgerFits budget world :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ## Part 2. One ceremony -/

/-- The batches of `jobs` have the counts of batches of the protocol, for each parameter. The tuple
count of each batch is in `batchCounts`, which `CheckBudget` needs, and its halving steps are at most
those of `maxBatch`, which the count of the coin keys needs. -/
def AdmissibleJobs (jobs : List Job) : Prop :=
  ∀ (parameter : PublicParameter), ∀ js ∈ chunks settings.batchSize jobs,
    tupleCount (runCircuits circuits parameter js) ∈ batchCounts circuits settings ∧
      halvings (tupleCount (runCircuits circuits parameter js)) ≤
        maxBatch circuits settings fun jobs => halvings (tupleCount jobs)

/-- The start of one ceremony. `keys i = none` is an operator that is not alive. -/
structure CeremonyStart (C : Committee) (σ : Type) where
  adversary : σ
  keys : C.Party → Option (Keys C)
  counters : ℕ × ℕ
  jobs : List Job

/-- The start of a ceremony is ready with the ledger `ℓ`. The honest keys are consistent, the caches
are within the ledger, and the hidden keys have their provenance. -/
def CeremonyReady (D : C.Coalition) (ℓ : StartBudget) {σ : Type}
    (c : CeremonyStart C σ) (world : StreamState C) : Prop :=
  seedsDiffer D c.keys = false ∧ LedgerFits ℓ world ∧ HiddenProvenance D world

/-- The result of one ceremony at one operator, namely the opened outputs and the end counters. -/
abbrev CeremonyResult := List (List Bit) × (ℕ × ℕ)

/-- The program of operator `i` in one ceremony, `ceremonyRun` from the counters of the start. An
operator that is not alive aborts at once. -/
def ceremonyProgram (i : C.Party) {σ : Type} (c : CeremonyStart C σ) : PartyM C E RealSpec CeremonyResult :=
  match c.keys i with
  | some keys => (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode)
      i keys c.jobs).run c.counters >>= fun p => p.1.elim failure fun outputs => pure (outputs, p.2)
  | none => failure

/-- One ceremony on the network in a phase of `rounds` rounds, answered by `streamWorld`. -/
def ceremonyPhase (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) :
    StateT (StreamState C) ProbComp (net.State × (C.Party → Option CeremonyResult)) :=
  simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality rounds c.adversary fun i =>
    ceremonyProgram K circuits settings i c)

/-- The opened outputs `outputs` are not the circuit values of `jobs` on the seeds and the parameter
of the honest keys `keys`, with `H` from the cache `cache`. -/
def WrongOutputs (D : C.Coalition) (keys : C.Party → Option (Keys C)) (jobs : List Job) (cache : HashCache C)
    (outputs : List (List Bit)) : Prop :=
  some outputs ≠ evalRun prims circuits (gameParameter D keys) (gameSeeds D keys) (hashOf prims cache) jobs

/-- An honest operator ends the ceremony with wrong opened outputs. -/
def WrongCeremony (D : C.Coalition) {σ : Type} (c : CeremonyStart C σ)
    (r : (σ × (C.Party → Option CeremonyResult)) × StreamState C) : Prop :=
  ∃ i, i ∉ D.1 ∧ ∃ o, r.1.2 i = some o ∧ WrongOutputs prims circuits D c.keys c.jobs r.2.1 o.1

/-- The counters after a ceremony of `jobs` from the counters `counters`. -/
def endCounters (parameter : PublicParameter) (counters : ℕ × ℕ) (jobs : List Job) : ℕ × ℕ :=
  (counters.1 + ((chunks settings.batchSize jobs).map (jobLabel circuits parameter)).sum,
    counters.2 + (chunks settings.batchSize jobs).length)

/-- The ceremony lemma, the probability part. From a ready start with a ledger that has room for
this ceremony, an honest operator ends one ceremony of admissible jobs with wrong opened outputs,
with no global event at the end, with probability at most the batches times `checkErrorMax` plus
`prssKeyCount C * ℓ.hiddenKeys / 2^256`. The batch size is positive. With the batch size 0 a
ceremony has no batch and opens nothing, and then its outputs are wrong for each job list with a
job. -/
def CeremonyBad : Prop :=
  0 < settings.batchSize →
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step rounds : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (ℓ : StartBudget) (c : CeremonyStart C net.State) (world : StreamState C),
      AdmissibleJobs circuits settings c.jobs → CeremonyReady D ℓ c world →
      LedgerRoom circuits settings runLimit C q step
        (ledgerStep circuits settings C step rounds (chunks settings.batchSize c.jobs).length ℓ) →
      (rounds + 2) * step ≤ q →
      (Pr{let r ← (ceremonyPhase prims K circuits settings D net rounds c).run world}[
          WrongCeremony prims circuits D c r ∧ ¬ GlobalEvent r.2]).toReal ≤
        (chunks settings.batchSize c.jobs).length * checkErrorMax (E := E) circuits settings runLimit C q +
          ((prssKeyCount C * ℓ.hiddenKeys : ℕ) : ℝ) / 2 ^ 256

/-- The ceremony lemma, the support part. On each outcome of one ceremony of admissible jobs from a
ready start, the honest results have the end counters of the job list, an operator that is not alive
at the start leaves no honest result, the end world is within the ledger with the cells of this
ceremony and keeps the provenance of the hidden keys, and with no global event the honest results are
equal.

The abort clause is on the start only. An honest operator that aborts in the last round of the
ceremony leaves the results of the others. They meet its abort frame in their next exchange, which
is the first exchange of the next ceremony, and there the clause on the start applies. -/
def CeremonySupport : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (ℓ : StartBudget) (c : CeremonyStart C net.State) (world : StreamState C),
      AdmissibleJobs circuits settings c.jobs → CeremonyReady D ℓ c world →
      ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
        (∀ i o, i ∉ D.1 → r.1.2 i = some o →
          o.2 = endCounters circuits settings (gameParameter D c.keys) c.counters c.jobs) ∧
        ((∃ i, i ∉ D.1 ∧ c.keys i = none) → ∀ i, i ∉ D.1 → r.1.2 i = none) ∧
        (LedgerFits (ledgerStep circuits settings C step rounds (chunks settings.batchSize c.jobs).length ℓ) r.2 ∧
          HiddenProvenance D r.2) ∧
        (¬ GlobalEvent r.2 → ∀ i j oi oj, i ∉ D.1 → j ∉ D.1 → r.1.2 i = some oi → r.1.2 j = some oj → oi = oj)

/-! ## Part 3. One run of a tree

### The top tree -/

/-- The start of the ceremony of the top tree, from the start of the run. -/
def topStart {σ : Type} (s : RealState C σ) : CeremonyStart C σ :=
  ⟨s.adversary, fun i => (s.operators i).keys, (0, 0), topJobs⟩

/-- The monitor split of the top tree. The run of the top tree is one ceremony of `topJobs` from the
counters `(0, 0)` and the local hash of the root. From a ready start, a wrong output of the top tree
with no global event at the end is at most as likely as wrong opened outputs of that ceremony with no
global event at its end. The phase of the ceremony has the fuel of a run. -/
def TopCover : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
  ∀ (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (s : RealState C net.State) (world : StreamState C),
    RunReady prims budget D s world → s.flag = false →
    Pr{let r ← (streamTreeRun prims K circuits settings D net .top s).run world}[
        r.1.2 = true ∧ ¬ GlobalEvent r.2] ≤
      Pr{let r ← (ceremonyPhase prims K circuits settings D net (treeFuel circuits settings) (topStart s)).run world}[
        WrongCeremony prims circuits D (topStart s) r ∧ ¬ GlobalEvent r.2]

/-! ### The cut of a bottom tree -/

/-- The result of the head of a bottom tree at one operator, as `CheckTiming.bottomHead` gives it,
namely the outputs of the first ceremony, the root, the randomizer, the encoding, and the counters. -/
abbrev HeadResult := (List (List Bit) × Digest × Randomizer × Encoding) × (ℕ × ℕ)

/-- The keys of the operators that run a bottom tree. An operator runs it with keys and a top tree. -/
def aliveKeys {σ : Type} (s : RealState C σ) (i : C.Party) : Option (Keys C) :=
  match (s.operators i).keys, (s.operators i).top with
  | some keys, some _ => some keys
  | _, _ => none

/-- The start of the first ceremony of bottom tree `b`. -/
def firstStart (b : Fin (2 ^ layerHeight)) {σ : Type} (s : RealState C σ) : CeremonyStart C σ :=
  ⟨s.adversary, aliveKeys s, (0, 0), bottomJobs b⟩

/-- The start of the second ceremony of bottom tree `b` at the cut, from the state `st` of the
adversary and the head result `x` of the honest operators. -/
def secondStart (b : Fin (2 ^ layerHeight)) {σ : Type} (s : RealState C σ) (st : σ) (x : HeadResult) :
    CeremonyStart C σ :=
  ⟨st, aliveKeys s, x.2, signJobs b x.1.2.2.2⟩

/-- The head of a run of bottom tree `b` on the network in `n` rounds, answered by `streamWorld`.
It is the first ceremony and the local steps to the end of the search. -/
def bottomCut (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (n : ℕ) :
    StateT (StreamState C) ProbComp (net.State × (C.Party → Option HeadResult)) :=
  simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality n s.adversary fun i =>
    CheckTiming.bottomHead K circuits settings i (s.operators i) b)

/-- The rest of a run of bottom tree `b` after the cut in `m` rounds, with the monitor. An operator
with no head result is not alive. -/
def bottomRest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (st : net.State) (heads : C.Party → Option HeadResult) (m : ℕ) :
    StateT (StreamState C) ProbComp ((net.State × (C.Party → Option TreeOutput)) × Bool) :=
  simulateQ (streamWorld prims D) (do
    let r ← executePhase worldRoles D net noFunctionality m st fun i =>
      (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (s.operators i) b)
    let bad ← wrongOutput D (fun i => (s.operators i).keys) (.bottom b) r.2
    pure (r, bad))

/-- An honest operator holds wrong outputs of the first ceremony at the cut. -/
def FirstWrong (D : C.Coalition) (b : Fin (2 ^ layerHeight)) {σ : Type} (s : RealState C σ)
    (z : (σ × (C.Party → Option HeadResult)) × StreamState C) : Prop :=
  ∃ i, i ∉ D.1 ∧ ∃ x, z.1.2 i = some x ∧
    WrongOutputs prims circuits D (fun i => (s.operators i).keys) (bottomJobs b) z.2.1 x.1.1

/-- The head of a bottom tree has the rounds of its first ceremony within the fuel of a run. -/
def HeadFuel : Prop :=
  ∀ (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)),
    CheckTiming.firstRounds circuits settings parameter (.bottom b) ≤ treeFuel circuits settings

/-- The head of a bottom tree is its first ceremony and the local search. Wrong first outputs at the
cut with no global event are at most as likely as wrong opened outputs of the first ceremony with no
global event at its end. `n` is the round count of the head at each honest operator. -/
def HeadCover : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (n : ℕ),
    (∀ i ∉ D.1, Timed n (CheckTiming.bottomHead K circuits settings i (s.operators i) b).run) →
    Pr{let z ← (bottomCut prims K circuits settings D net b s n).run world}[
        FirstWrong prims circuits D b s z ∧ ¬ GlobalEvent z.2] ≤
      Pr{let r ← (ceremonyPhase prims K circuits settings D net n (firstStart b s)).run world}[
        WrongCeremony prims circuits D (firstStart b s) r ∧ ¬ GlobalEvent r.2]

/-- The state at the cut. From a ready start of the first ceremony, the world of the cut is within
the ledger with the cells of the head and keeps the provenance of the hidden keys. With no global event
at the cut, the
honest operators with a head result hold one result, so one encoding and one pair of counters. -/
def CutState : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (ℓ : StartBudget) (b : Fin (2 ^ layerHeight)) (s : RealState C net.State) (world : StreamState C) (n : ℕ),
      (∀ i ∉ D.1, Timed n (CheckTiming.bottomHead K circuits settings i (s.operators i) b).run) →
      CeremonyReady D ℓ (firstStart b s) world →
      ∀ z ∈ support ((bottomCut prims K circuits settings D net b s n).run world),
        LedgerFits (ledgerStep circuits settings C step n (chunks settings.batchSize (bottomJobs b)).length ℓ) z.2 ∧
        HiddenProvenance D z.2 ∧
        (¬ GlobalEvent z.2 → ∀ i j xi xj, i ∉ D.1 → j ∉ D.1 → z.1.2 i = some xi → z.1.2 j = some xj → xi = xj)

/-- A dead operator at the cut. If an honest operator has no head result, the rest of the run gives
no wrong output. The operator sends abort frames from the first round of the rest, each other honest
operator starts the rest with the first exchange of the second PRSS setup, and so no honest operator
ends the rest with an output. -/
def CutDead : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (st : net.State) (heads : C.Party → Option HeadResult) (m : ℕ)
    (w : StreamState C), (∃ i, i ∉ D.1 ∧ heads i = none) →
    ∀ y ∈ support ((bottomRest prims K circuits settings D net b s st heads m).run w), y.1.2 = false

/-- A global event at the cut stays to the end of the run. -/
def CutMonotone : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (st : net.State) (heads : C.Party → Option HeadResult) (m : ℕ)
    (w : StreamState C), GlobalEvent w →
    ∀ y ∈ support ((bottomRest prims K circuits settings D net b s st heads m).run w), GlobalEvent y.2

/-- The monitor split of a bottom tree after the cut. Take a cut of a run from a ready start at which
each honest operator holds the head result `x` and no honest operator holds wrong first outputs. Then
a wrong output of the bottom tree with no global event at the end is at most as likely as wrong
opened outputs of the second ceremony, at the encoding and the counters of `x`, with no global event
at its end. -/
def RestCover : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
  ∀ (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (n m : ℕ),
    RunReady prims budget D s world → s.flag = false →
    ∀ z ∈ support ((bottomCut prims K circuits settings D net b s n).run world), ∀ x : HeadResult,
      (∀ i, i ∉ D.1 → z.1.2 i = some x) → ¬ FirstWrong prims circuits D b s z →
      Pr{let y ← (bottomRest prims K circuits settings D net b s z.1.1 z.1.2 m).run z.2}[
          y.1.2 = true ∧ ¬ GlobalEvent y.2] ≤
        Pr{let r ← (ceremonyPhase prims K circuits settings D net m (secondStart b s z.1.1 x)).run z.2}[
          WrongCeremony prims circuits D (secondStart b s z.1.1 x) r ∧ ¬ GlobalEvent r.2]

/-! ## Part 4. The readiness hop at the test `RunReadyL` -/

/-- The readiness hop over the test `RunReadyL`. In the game that tests `RunReadyL` at each start
of a run, no start is recorded as not ready with no global event. -/
def ReadyHopL : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    firstProbWith prims K circuits settings runLimit D A
      (RunReadyL prims (startBudget circuits settings runLimit C q) D)
      (fun r => ∃ tree index world, r.1.first = some (.unready tree index, world) ∧ ¬ GlobalEvent world) = 0

/-! ## The provenance of the hidden keys through the game

`ReadyHopL` needs the four budget parts of `RunReady` at the starts of `firstRunWith` at the test
`RunReadyL`, and `ProvenanceAtUnready`. The game keeps `HiddenProvenance` by the five facts below. -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The start of the game. The empty caches have the provenance of their hidden keys. -/
theorem provenance_empty (D : C.Coalition) : HiddenProvenance D ((∅, ∅) : StreamState C) := by
  intro name key ρ idx position _ h
  exact absurd rfl h

/-- A computation of the world keeps the provenance of the hidden keys, from each world. -/
def KeepsProvenance (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  ∀ world : StreamState C, HiddenProvenance D world →
    ∀ r ∈ support ((simulateQ (streamWorld prims D) oa).run world), HiddenProvenance D r.2

/-- The seed generation keeps the provenance. It makes no hidden draw. -/
def ProvenanceSeedGen : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    KeepsProvenance prims D (realExecution D A.net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])

/-- A run of a tree with its monitor keeps the provenance, also when an operator aborts. Each hidden
draw of an honest operator is under a PRSS key that `deriveKeys` of the same setup gave, and that
derive cell stays in the cache. -/
def ProvenanceTreeRun : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State)
    (world : StreamState C), HiddenProvenance D world →
    ∀ r ∈ support ((streamTreeRun prims K circuits settings D net tree s).run world), HiddenProvenance D r.2

/-- A counted computation of the adversary keeps the provenance. A counted call writes no hidden
cell. -/
def ProvenanceCounted : Prop :=
  ∀ (D : C.Coalition) {α : Type} (oa : OracleComp (LocalSpec C) α),
    KeepsProvenance prims D (worldRoles.adversary oa)

/-- A signing request keeps the provenance. The answer of an operator and the value of `F` make
calls of `.prf`, `.mask` and `.hash` only. -/
def ProvenanceSigning : Prop :=
  ∀ (D : C.Coalition) {σ : Type} (operators : C.Party → OperatorState C) (operator : OperatorState C)
    (e : KeyIndex) (q : TsigQuery C) (st : TsigState C) (fs : FirstState C σ) (x : Point)
    (world : StreamState C), HiddenProvenance D world →
    (∀ r ∈ support ((((operatorAnswer (m := FirstM C σ) (firstLift prims D (σ := σ))
        (firstValue prims D operators) operator e q).run st).run fs).run world), HiddenProvenance D r.2) ∧
    ∀ r ∈ support (((firstValue prims D operators x : FirstM C σ Digest).run fs).run world), HiddenProvenance D r.2

/-- The fifth budget part of `ReadyHopL`. A start that `firstRunWith` at the test `RunReadyL` records
as not ready, with no global event, has the provenance of its hidden keys. It follows from
`provenance_empty` and the four statements above by a walk of the game. -/
def ProvenanceAtUnready : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReadyL prims (startBudget circuits settings runLimit C q) D)),
      ∀ tree index w, r.1.first = some (.unready tree index, w) → ¬ GlobalEvent w → HiddenProvenance D w

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end
