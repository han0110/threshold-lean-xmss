import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Basics
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Route

/-!
# The lemma of one ceremony, the statements of its parts

`ghostCeremony` runs one ceremony with the records of its batches, and `cutCeremony` cuts it at the
check of batch `k`. The parts of `CeremonyBad` (`CeremonyMonitor` to `CeremonyTupleInputs`), of
`CeremonySupport` (`CeremonyCounters` to `CeremonyProvenance`) and of `ProvenanceTreeRun`
(`TreePhaseProvenance`, `MonitorProvenance`) are stated here.
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

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## Part 1. The ghost run of one ceremony -/

/-- The program of operator `i` in one ceremony with the record of its batches, `recRun` from the
counters of the start. An operator that is not alive aborts at once. -/
def recCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) : RecM C E CeremonyResult :=
  match c.keys i with
  | some keys => (recRun K circuits settings i keys c.jobs).run c.counters >>= fun p =>
      p.1.elim failure fun outputs => pure (outputs, p.2)
  | none => failure

/-- The last step of each operator in a ghost run of one ceremony, with its record. -/
abbrev CeremonySteps (C : Committee) (E : Type) := C.Party → RStep C E RealSpec CeremonyResult (Record C E)

/-- One ceremony with the recorded programs on the ghost executor, answered by `streamWorld`. -/
def ghostCeremony (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) : StateT (StreamState C) ProbComp (net.State × CeremonySteps C E) :=
  simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) rounds
    c.adversary fun i => (recCeremony K circuits settings i c).run.run)

/-- The record of operator `i` at the end of a ghost run of one ceremony. -/
def ceremonyRecord (steps : CeremonySteps C E) (i : C.Party) : Record C E := (steps i).record []

/-- The outputs of the operators at the end of a ghost run of one ceremony. -/
def ceremonyOutputs (steps : CeremonySteps C E) : C.Party → Option CeremonyResult := fun i => (steps i).output

/-- The tuples of the check of batch `k` at each operator, from its record. -/
def ceremonyTuplesAt (k : ℕ) (steps : CeremonySteps C E) : C.Party → List (Tuple C) := fun i =>
  (((startsOf (ceremonyRecord steps i))[k]?).map fun b => batchTuples K b.mode b.circuits b.inputs b.zs b.v').getD []

/-- Each honest operator recorded the start of the check of batch `k`. -/
def StartedAt (D : C.Coalition) (k : ℕ) (steps : CeremonySteps C E) : Prop :=
  ∀ i, i ∉ D.1 → ((startsOf (ceremonyRecord steps i))[k]?).isSome

/-- The check of batch `k` is bad in the records. Each honest operator reached it, the tuples have a
wrong tuple or split copies, and an honest operator passed it. -/
def BadCheckAt (D : C.Coalition) (k : ℕ) (steps : CeremonySteps C E) : Prop :=
  StartedAt D k steps ∧
    (WrongTuple D (ceremonyTuplesAt K k steps) ∨
      ¬ MultVerifyAgree D (honestTuples D (ceremonyTuplesAt K k steps))) ∧
    ∃ i, i ∉ D.1 ∧ k < (openingsOf (ceremonyRecord steps i)).length

/-- An honest operator with an output recorded a batch `k` whose output is not the circuit value of
its jobs. -/
def WrongBatch (D : C.Coalition) {σ : Type} (c : CeremonyStart C σ) (k : ℕ)
    (ω : (σ × CeremonySteps C E) × StreamState C) : Prop :=
  ∃ i, i ∉ D.1 ∧ (ω.1.2 i).output.isSome ∧ ∃ b out, (startsOf (ceremonyRecord ω.1.2 i))[k]? = some b ∧
    (batchOutputsOf (ceremonyRecord ω.1.2 i))[k]? = some out ∧
    WrongOutputs prims circuits D c.keys b.jobs ω.2.1 out

/-- An honest operator recorded a start with the key `key` under the name `name`. -/
def UsesKey (D : C.Coalition) (name : KeyName C) (key : HashOutput) (steps : CeremonySteps C E) : Prop :=
  ∃ i, i ∉ D.1 ∧ ∃ b ∈ startsOf (ceremonyRecord steps i), NameKey i b.ctx.prss name key

/-- A PRSS key of the ceremony under a hidden name has a stream cell in the hidden cache `hidden` of
the start. -/
def ReusedKey (D : C.Coalition) (hidden : HiddenCache C) (steps : CeremonySteps C E) : Prop :=
  ∃ name key, Hidden D name ∧ UsesKey D name key steps ∧ ∃ ρ idx position, hidden ((name, key), ρ, idx, position) ≠ none

/-! ## Part 2. The cut of one ceremony at a check -/

/-- The outcome of a program that stops at most one time at a check. -/
abbrev CutOf (C : Committee) (E : Type) (α : Type) :=
  α ⊕ (CheckPoint C × (RunState C → PartyM C E RealSpec α))

/-- The result of `ceremonyRun` with its end counters. -/
abbrev RunResult := Option (List (List Bit)) × (ℕ × ℕ)

/-- The program of operator `i` in one ceremony that stops at the check of batch `k` of the ceremony.
`cutRun` stops at a tag, and the tags of the ceremony start at the tag `c.counters.2` of its start, so
batch `k` has the tag `c.counters.2 + k`. The records of the ghost run count the batches of the
ceremony from 0, so `k` is the same index in both. -/
def cutCeremony (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    PartyM C E RealSpec (CutOf C E RunResult) :=
  match c.keys i with
  | some keys => ((cutRun K circuits settings (c.counters.2 + k) i keys c.jobs).run c.counters).run
  | none => failure

/-- The prefix of one ceremony up to the check of its batch `k`, answered by `streamWorld`. -/
def ceremonyPrefix (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds k : ℕ)
    (c : CeremonyStart C net.State) :
    StateT (StreamState C) ProbComp (net.State × (C.Party → Option (CutOf C E RunResult))) :=
  simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality rounds c.adversary fun i =>
    cutCeremony K circuits settings k i c)

/-- The start of the check of operator `i` in an outcome of a prefix. -/
def stopPoint {α : Type} (i : C.Party) (o : Option (CutOf C E α)) : CheckPoint C :=
  match o with
  | some (.inr (point, _)) => point
  | _ => ⟨localContext i, [], ⟨fun _ => [], 0, 0⟩⟩

/-- Each honest operator stops at the start of the check in an outcome of a prefix. -/
def AllStop {α : Type} (D : C.Coalition) (outcomes : C.Party → Option (CutOf C E α)) : Prop :=
  ∀ i, i ∉ D.1 → ∃ point rest, outcomes i = some (.inr (point, rest))

/-- The joint start of the check in an outcome of a prefix, when each honest operator stops at it.
The counts, the label and the tag are those of the first honest operator. -/
def jointStop {α : Type} (D : C.Coalition) {σ : Type} (r : σ × (C.Party → Option (CutOf C E α)))
    (world : StreamState C) : Option (CheckStart C σ) :=
  if AllStop D r.2 then
    match C.parties.find? fun i => i ∉ D.1 with
    | some j =>
      let lead := stopPoint j (r.2 j)
      some ⟨fun i => (stopPoint i (r.2 i)).ctx.keys, fun i => (stopPoint i (r.2 i)).ctx.prss,
        lead.tuples.map (·.count), fun i => (stopPoint i (r.2 i)).tuples, lead.state.label, lead.state.tag, r.1, world⟩
    | none => none
  else none

/-- The prefix of one ceremony and then the real check from the joint start, which is the pilot. -/
def ceremonyCheckAt (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds k : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) :
    ProbComp (Option (CheckStart C net.State) × Option ((net.State × (C.Party → Option Unit)) × StreamState C)) :=
  (ceremonyPrefix prims K circuits settings D net rounds k c).run world >>= fun z =>
    match jointStop D z.1 z.2 with
    | some start => (fun out => (some start, some out)) <$> checkFrom prims K D net start
    | none => pure (none, none)

/-! ## Part 3. The sub-statements of `CeremonyBad` -/

/-- The monitor of one ceremony. With a positive batch size, wrong opened outputs of an honest
operator with no global event at the end have a batch `k` whose recorded output is wrong. The opened
outputs are the recorded batch outputs in their order, and the jobs are the recorded batches in
their order. -/
def CeremonyMonitor : Prop :=
  0 < settings.batchSize →
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world),
      (∃ i, i ∉ D.1 ∧ ∃ o, (ω.1.2 i).output = some o ∧ WrongOutputs prims circuits D c.keys c.jobs ω.2.1 o.1) →
      ¬ GlobalEvent ω.2 → ∃ k < (chunks settings.batchSize c.jobs).length, WrongBatch prims circuits D c k ω

/-- The wrong batch. With no global event at the end, a wrong recorded batch `k` of an honest output
has a bad check `k` in the records, or an honest operator that did not record its start. -/
def CeremonyBatch : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world), ¬ GlobalEvent ω.2 →
      ∀ k < (chunks settings.batchSize c.jobs).length, WrongBatch prims circuits D c k ω →
        BadCheckAt K D k ω.1.2 ∨ ¬ StartedAt D k ω.1.2

/-- The abort before a check. With no global event at the end, when an honest operator did not
record the start of check `k`, no honest operator has an output. The start of a check is before the
exchanges of that check and its `OpenRep`. -/
def CeremonyAbort : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world), ¬ GlobalEvent ω.2 →
      ∀ k < (chunks settings.batchSize c.jobs).length, ¬ StartedAt D k ω.1.2 →
        ∀ i, i ∉ D.1 → (ω.1.2 i).output = none

/-- The fresh part for one old key. Take a hidden name and a key with a derive cell in the hash
cache of the start. An honest operator of the ceremony holds that key under that name, with no
global event at the end, with probability at most `2^-256`. With no derive collision the derive input
of the honest key is the cached one, which is fixed before the honest parts are drawn. -/
def FreshOne : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (name : KeyName C) (key : HashOutput),
    Hidden D name → (∃ kind parts, world.1 (.derive .prss kind parts) = some key) →
    Pr{let ω ← (ghostCeremony prims K circuits settings D net rounds c).run world}[
        UsesKey D name key ω.1.2 ∧ ¬ GlobalEvent ω.2] ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- The hidden names are at most the PRSS keys of one setup. -/
def HiddenNames (C : Committee) : Prop :=
  ∀ D : C.Coalition, ∃ names : Finset (KeyName C), names.card ≤ prssKeyCount C ∧ ∀ name, Hidden D name → name ∈ names

/-- The synchronization at the checks of one ceremony. With no global event at the end, when each
honest operator recorded the start of check `k`, they recorded the same modes, circuits, labels and
tags at each check up to `k`. The job list is public, so no agreement of jobs is a premise. -/
def CeremonySync : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world), ¬ GlobalEvent ω.2 →
      ∀ k < (chunks settings.batchSize c.jobs).length, StartedAt D k ω.1.2 → ∀ i j, i ∉ D.1 → j ∉ D.1 → ∀ k' ≤ k,
        ((startsOf (ceremonyRecord ω.1.2 i))[k']?).map (fun b => (b.mode, b.circuits, b.state.label, b.state.tag)) =
          ((startsOf (ceremonyRecord ω.1.2 j))[k']?).map (fun b => (b.mode, b.circuits, b.state.label, b.state.tag))

/-- The label freshness. At a joint start of check `k` on the support of the prefix, with no global
event, when no PRSS key of the start has a cell in the hidden cache of the start of the ceremony, the
streams are fresh at the label of the check. -/
def CeremonyInterval : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ k < (chunks settings.batchSize c.jobs).length,
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world), ∀ start,
      jointStop D z.1 z.2 = some start → ¬ GlobalEvent z.2 → KeysFresh D world.2 start →
        StreamsFresh D start.L start.prss start.world.2

/-- The coupling of the ghost run of one ceremony to its cut at check `k`. With the synchronization
and the label freshness, a bad check `k` in the records with no reused key, an honest output and no
global event at the end is at most as likely as a bad check of `ceremonyCheckAt k`, in a phase with the
rounds of the ceremony. A check with the count 0 has no wrong tuple and no split copies, so it is
never bad, and it is its own case of the proof. -/
def CeremonyCoupling : Prop :=
  CeremonySync prims K circuits settings → CeremonyInterval prims K circuits settings →
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds →
    ∀ k < (chunks settings.batchSize c.jobs).length,
    (Pr{let ω ← (ghostCeremony prims K circuits settings D net rounds c).run world}[
        BadCheckAt K D k ω.1.2 ∧ ¬ ReusedKey D world.2 ω.1.2 ∧ HonestOutput D (ceremonyOutputs ω.1.2) ∧
          ¬ GlobalEvent ω.2]).toReal ≤
      (Pr{let r ← ceremonyCheckAt prims K circuits settings D net rounds k c world}[CheckBad D r]).toReal

/-- The PRSS keys at the cut. At each joint start of a check on the support of the prefix, the
honest operators agree on the PRSS keys, or two echo hashes collide. -/
def CeremonyKeysAgree : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C),
    ∀ k < (chunks settings.batchSize c.jobs).length,
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world), ∀ start,
      jointStop D z.1 z.2 = some start → PrssKeysAgree D start.prss ∨ DomainCollision EchoDomain z.2.1

/-- The budget at the cut, for a check with a positive count. From a ready start with a ledger that
has room for this ceremony, in a phase with the rounds of the ceremony, each joint start of a check
with a positive count on the support of the prefix, with no global event, fits `CheckBudget`. The
charge of the tested check has `checkRounds` rounds, two more than its batch has, and the padding of
`LedgerRoom` pays them. With fewer rounds than the ceremony has, the prefix can reach a check that
the phase cannot end, and then the charge is not paid. A check with the count 0 has the charge
`checkRounds 0` and no round, so it is not in this statement. -/
def CeremonyBudget : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step rounds : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (ℓ : StartBudget) (c : CeremonyStart C net.State) (world : StreamState C),
      AdmissibleJobs circuits settings c.jobs → CeremonyReady D ℓ c world →
      LedgerRoom circuits settings runLimit C q step
        (ledgerStep circuits settings C step rounds (chunks settings.batchSize c.jobs).length ℓ) →
      (rounds + 2) * step ≤ q →
      CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds →
      ∀ k < (chunks settings.batchSize c.jobs).length,
      ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world), ∀ start,
        jointStop D z.1 z.2 = some start → ¬ GlobalEvent z.2 → start.counts.sum ≠ 0 →
          CheckBudget circuits settings runLimit q step start

/-- A check with the count 0. At a joint start whose tuples have the count 0 in sum, no tuple is
wrong and the copies agree. So such a check is never bad. -/
def ZeroCheck : Prop :=
  ∀ (D : C.Coalition) {σ α : Type} (r : σ × (C.Party → Option (CutOf C E α))) (world : StreamState C)
    (start : CheckStart C σ), jointStop D r world = some start → start.counts.sum = 0 →
    ¬ WrongTuple D start.x ∧ MultVerifyAgree D (honestTuples D start.x)

/-- A phase with fewer rounds than the ceremony has. No honest operator ends one ceremony from a
ready start in such a phase. -/
def ShortFuel : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    rounds < CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs →
    ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
      ∀ i, i ∉ D.1 → r.1.2 i = none

/-- The tuple inputs from the prefix. At each joint start of a check on the support of the prefix
from a ready start, with no global event, the tuples have `TupleInputs` when the honest operators
agree on the PRSS keys. -/
def CeremonyTupleInputs : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ k < (chunks settings.batchSize c.jobs).length,
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world), ∀ start,
      jointStop D z.1 z.2 = some start → ¬ GlobalEvent z.2 → PrssKeysAgree D start.prss →
        TupleInputs K start.counts D start.x

/-! ## Part 4. The sub-statements of `CeremonySupport` -/

/-- The end counters. Each honest result of one ceremony from a ready start has the end counters of
the job list. -/
def CeremonyCounters : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
      ∀ i o, i ∉ D.1 → r.1.2 i = some o →
        o.2 = endCounters circuits settings (gameParameter D c.keys) c.counters c.jobs

/-- The agreement of the opened outputs. With no global event at the end of one ceremony from a ready
start, two honest results have the same opened outputs. -/
def CeremonyOutputsAgree : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world), ¬ GlobalEvent r.2 →
      ∀ i j oi oj, i ∉ D.1 → j ∉ D.1 → r.1.2 i = some oi → r.1.2 j = some oj → oi.1 = oj.1

/-- The ledger of the history and digest cells. One ceremony adds at most `rounds * step` cells of
the adversary and `batches * termHashes C` honest cells. -/
def LedgerSplit : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (n : ℕ) (c : CeremonyStart C net.State) (world : StreamState C),
      SplitCacheBound (splitRegionCache SplitHashDomain world.1) n →
      ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
        SplitCacheBound (splitRegionCache SplitHashDomain r.2.1)
          (n + rounds * step + (chunks settings.batchSize c.jobs).length * termHashes C)

/-- The ledger of the coin inputs and the expansion keys. One ceremony of admissible jobs adds at
most `rounds * step` charged inputs of the adversary and, for each batch, `n (R + 2)` honest coin
inputs and expansion keys. -/
def LedgerSound : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (coins keys : ℕ) (c : CeremonyStart C net.State) (world : StreamState C),
      AdmissibleJobs circuits settings c.jobs →
      (∃ (seen : Finset (Query C)) (expansionKeys : Finset HashOutput), SoundCache 0 world.1 seen expansionKeys ∧
        seen.card ≤ coins ∧ expansionKeys.card ≤ keys) →
      ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
        ∃ (seen : Finset (Query C)) (expansionKeys : Finset HashOutput), SoundCache 0 r.2.1 seen expansionKeys ∧
          seen.card ≤ coins + rounds * step +
            coinKeysOf circuits settings C (chunks settings.batchSize c.jobs).length ∧
          expansionKeys.card ≤ keys + coinKeysOf circuits settings C (chunks settings.batchSize c.jobs).length

/-- The ledger of the digest salts. One ceremony adds at most `rounds * step` salts of the adversary
and `batches * termHashes C` honest salts. -/
def LedgerSalts : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (n : ℕ) (c : CeremonyStart C net.State) (world : StreamState C),
      (∃ salts : Finset (List Bit), DigestSaltsCovered world.1 salts ∧ salts.card ≤ n) →
      ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
        ∃ salts : Finset (List Bit), DigestSaltsCovered r.2.1 salts ∧
          salts.card ≤ n + rounds * step + (chunks settings.batchSize c.jobs).length * termHashes C

/-- The ledger of the hidden keys. One ceremony adds at most one key under each hidden name. The
holders of a hidden name are honest and get each part on honest links. -/
def LedgerHidden : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (n : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C), HiddenKeyBound world.2 n →
    ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
      HiddenKeyBound r.2.2 (n + 1)

/-- One ceremony keeps the provenance of the hidden keys, also when an operator aborts. -/
def CeremonyProvenance : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C), HiddenProvenance D world →
    ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world), HiddenProvenance D r.2

/-! ## Part 5. The sub-statements of `ProvenanceTreeRun` -/

/-- The phase of a run of a tree keeps the provenance of the hidden keys, also when an operator
aborts. It is the walk of `CeremonyProvenance` on the programs of a tree: each hidden draw of
`prssRandomness` is under a key that `deriveKeys` of the same setup gave. -/
def TreePhaseProvenance : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State),
    KeepsProvenance prims D (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
      fun i => treeProgram K circuits settings i (s.operators i) tree)

/-- The monitor keeps the provenance of the hidden keys. It makes calls of `.hash` and `.prf` only. -/
def MonitorProvenance : Prop :=
  ∀ (D : C.Coalition) (keys : C.Party → Option (Keys C)) (tree : Tree) (outputs : C.Party → Option TreeOutput),
    KeepsProvenance prims D (wrongOutput D keys tree outputs)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end
