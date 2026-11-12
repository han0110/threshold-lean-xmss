import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkHybrid

/-!
# Retained opening executions for the check walk

The shared opening certificate records the actual local head and its incoming
copy hashes. Its adapters supply the existing indexed and dealer certificates.
An ordered round retains each successful head together with the execution of
its own continuation from the same intermediate world state. The phase
extraction also retains the hash pass, adversary reply and later scheduler
execution, including branches that subsequently abort.

The pinned and current leanVM proof libraries have no synchronous opening or
pending-tail scheduler lemma. These constructions use the threshold scheduler's
`support_sequenceFin_state` and `treeLockstep_open_local_factor`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The common execution fields of the indexed and dealer opening witnesses. -/
structure TreeCheckOpeningRun (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (count : ℕ) (v : C.Party → Shares C Bit) where
  live : C.Party → Bool
  ds : C.Party → List HashOutput
  sent : C.Party → Mail C E
  party : C.Party
  before : TreeSimState C
  after : TreeSimState C
  output : ℕ → Bit
  hashes : ∀ h, h ∉ D.1 → live h = true →
    (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      TreeSimHashAnswer before.2 (.copy (vector count (v h T))) u
  run : (some output, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (free (liftComp (treeSimOpenHead K D live count v ds sent party) (LocalSpec C)))).run before)

namespace TreeCheckOpeningRun

variable {prims : Primitives} {K : Constants C E} {circuits : Circuits}
variable {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
variable {b : TreeCheckBatchBoundary A} {o : TreeCheckTailCheckpoint A}

/-- The indexed adapter adds only the identification of the recorded output. -/
def toTrace (opening : TreeCheckOpeningRun prims K D
    (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
    (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.1))
    (record : TreeSimCheckBatchRecord C)
    (recorded : assemble (b.jobs.map (circuits b.parameter ·.kind)) opening.output = record.outputs) :
    TreeCheckOpeningTrace prims K circuits D A b o record where
  live := opening.live
  ds := opening.ds
  sent := opening.sent
  party := opening.party
  before := opening.before
  after := opening.after
  output := opening.output
  hashes := opening.hashes
  run := opening.run
  recorded := recorded

/-- The dealer adapter keeps the same local execution. -/
def toAt (opening : TreeCheckOpeningRun prims K D
    (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
    (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.1))
    (seeds : C.Term → HashOutput)
    (seed : ∀ i T, i ∉ D.1 → i ∈ C.holders T → (b.ctx i).keys.seed T = seeds T)
    (hash : Query C → HashOutput)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ o.2.2 →
      TreeSimCheckWorldHashes hash t u)
    (good : ¬ TreeSimHashBudgetCollision opening.after.2)
    (wrong : assemble (b.jobs.map (circuits b.parameter ·.kind)) opening.output ≠
      b.jobs.map (fun job => ThresholdLeanXmssSecurity.D prims hash
        (evalJob circuits b.parameter seeds job))) :
    TreeCheckOpeningAt prims K circuits D A b o where
  seeds := seeds
  seed := seed
  hash := hash
  rows := rows
  live := opening.live
  ds := opening.ds
  sent := opening.sent
  party := opening.party
  before := opening.before
  after := opening.after
  output := opening.output
  hashes := opening.hashes
  run := opening.run
  good := good
  wrong := wrong

theorem log_prefix {count : ℕ} {v : C.Party → Shares C Bit}
    (opening : TreeCheckOpeningRun prims K D count v) : opening.before.2 <+: opening.after.2 :=
  treeSimLoggedWorld_prefix prims D _ opening.before (some opening.output, opening.after) opening.run

end TreeCheckOpeningRun

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

/-- Each surviving local step retains its own head and continuation from the
ordered execution; earlier local tails are included in its incoming log. -/
theorem treeCheck_open_locals_retained {α : Type}
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (s : TreeSimState C)
    (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector count (v h T))) u)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (Concrete.sequenceFin fun i =>
        roundLocal D (treeSimOpenPartial K D live count v ds k) sent i))).run s)) :
    ∀ i, r.1 i ≠ .done none → ∃ opening : TreeCheckOpeningRun prims K D count v,
      opening.live = live ∧ opening.ds = ds ∧ opening.sent = sent ∧ opening.party = i ∧
      s.2 <+: opening.before.2 ∧ ∃ tail : TreeSimState C,
        (r.1 i, tail) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (advance (k i opening.output).run))).run opening.after) ∧
        tail.2 <+: r.2.2 := by
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 <+: t.2
    le_refl := fun _ => List.prefix_refl _
    le_trans := fun _ _ _ => List.IsPrefix.trans }
  rw [free_sequenceFin, simulateQ_sequenceFin] at run
  apply (support_sequenceFin_state s _
    (fun i step final => step ≠ .done none → ∃ opening : TreeCheckOpeningRun prims K D count v,
      opening.live = live ∧ opening.ds = ds ∧ opening.sent = sent ∧ opening.party = i ∧
      s.2 <+: opening.before.2 ∧ ∃ tail : TreeSimState C,
        (step, tail) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (advance (k i opening.output).run))).run opening.after) ∧ tail.2 <+: final.2)
    ?_ ?_ s (List.prefix_refl _) r run).2
  · intro i before hprefix out localRun
    refine ⟨treeSimLoggedWorld_prefix prims D _ before out localRun, ?_⟩
    intro kept
    rw [treeLockstep_open_local_factor] at localRun
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at localRun
    obtain ⟨⟨value, after⟩, head, rest⟩ := localRun
    cases value with
    | none =>
      simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at rest
      exact (kept (congrArg Prod.fst rest)).elim
    | some value =>
      have grows : s.2 <+: before.2 := hprefix
      let opening : TreeCheckOpeningRun prims K D count v := {
        live := live
        ds := ds
        sent := sent
        party := i
        before := before
        after := after
        output := value
        hashes := by
          intro h honest active
          obtain ⟨length, hs⟩ := hashes h honest active
          refine ⟨length, fun T => ?_⟩
          obtain ⟨u, hu, hash⟩ := hs T
          exact ⟨u, hu, hash.imp (fun h => grows.subset h) (fun h => grows.subset h)⟩
        run := head }
      exact ⟨opening, rfl, rfl, rfl, rfl, hprefix, out.2, rest, List.prefix_refl _⟩
  · intro i step before after h hprefix kept
    obtain ⟨opening, live, ds, sent, party, start, tail, rest, last⟩ := h kept
    exact ⟨opening, live, ds, sent, party, start, tail, rest, last.trans hprefix⟩

/-- The hash pass, common reply, ordered local work and scheduler suffix of
one opening phase. The suffix may abort any or all operators. -/
structure TreeCheckOpeningPhaseRun {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C) where
  ds : C.Party → List HashOutput
  afterHashes : TreeSimState C
  reply : A.State × (C.Party → Mail C E)
  afterReply : TreeSimState C
  steps : C.Party → Step C E RealSpec α
  afterLocals : TreeSimState C
  hashesRun : (ds, afterHashes) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (free (treeLockstepOpenHashes D (fun _ => true) count v))).run s)
  replyRun : (reply, afterReply) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (A.round state fun c i =>
      if c ∈ D.1 ∧ i ∉ D.1 then treeSimOpenOut K i count (v i) (ds i) c else none))).run afterHashes)
  localsRun : (steps, afterLocals) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (free (Concrete.sequenceFin fun i => roundLocal D
      (treeSimOpenPartial K D (fun _ => true) count v ds k) reply.2 i))).run afterReply)
  restRun : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executeRounds worldRoles D A noFunctionality fuel reply.1 steps)).run afterLocals)

/-- Decompose a supported phase without replaying any honest or adversarial
query. All four component runs use their actual predecessor world state. -/
def treeCheckOpeningPhaseRun_of_run {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (ctx i) (v i) count >>= k i))).run s)) :
    TreeCheckOpeningPhaseRun prims K D A fuel state count v k s r :=
  Classical.choice (by
    rw [treeLockstep_open_phase_cont K D A fuel state ctx self] at run
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨⟨ds, afterHashes⟩, hashesRun, ⟨reply, afterReply⟩, replyRun,
      ⟨steps, afterLocals⟩, localsRun, restRun⟩ := run
    exact ⟨⟨ds, afterHashes, reply, afterReply, steps, afterLocals,
      hashesRun, replyRun, localsRun, restRun⟩⟩)

namespace TreeCheckOpeningPhaseRun

variable {prims K D} {α : Type}
variable {A : Adversary C E (Keys C) PEmpty PEmpty} {fuel : ℕ} {state : A.State}
variable {count : ℕ} {v : C.Party → Shares C Bit}
variable {k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α}
variable {s : TreeSimState C} {r : (A.State × (C.Party → Option α)) × TreeSimState C}

/-- A surviving step has an actual opening certificate and its original
continuation. Its final phase result need not be successful. -/
theorem opening (phase : TreeCheckOpeningPhaseRun prims K D A fuel state count v k s r)
    (i : C.Party) (kept : phase.steps i ≠ .done none) :
    ∃ opening : TreeCheckOpeningRun prims K D count v,
      opening.live = (fun _ => true) ∧ opening.ds = phase.ds ∧
      opening.sent = phase.reply.2 ∧ opening.party = i ∧
      s.2 <+: opening.before.2 ∧ opening.after.2 <+: r.2.2 ∧
      ∃ tail : TreeSimState C,
        (phase.steps i, tail) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (advance (k i opening.output).run))).run opening.after) ∧
        tail.2 <+: phase.afterLocals.2 := by
  have hashes := treeLockstep_open_hashes_logged prims D (fun _ => true) count v s
    (phase.ds, phase.afterHashes) phase.hashesRun
  have hashesPrefix := treeSimLoggedWorld_prefix prims D _ s
    (phase.ds, phase.afterHashes) phase.hashesRun
  have replyPrefix := treeSimLoggedWorld_prefix prims D _ phase.afterHashes
    (phase.reply, phase.afterReply) phase.replyRun
  have restPrefix := treeSimLoggedWorld_prefix prims D _ phase.afterLocals r phase.restRun
  have hashesAtReply : ∀ h, h ∉ D.1 → (fun _ : C.Party => true) h = true →
      (phase.ds h).length = C.terms.length ∧
      ∀ T, ∃ u, (phase.ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer phase.afterReply.2 (.copy (vector count (v h T))) u := by
    intro h honest live
    obtain ⟨length, hs⟩ := hashes h honest live
    refine ⟨length, fun T => ?_⟩
    obtain ⟨u, hu, hash⟩ := hs T
    exact ⟨u, hu, hash.imp (fun h => replyPrefix.subset h) (fun h => replyPrefix.subset h)⟩
  obtain ⟨opening, live, ds, sent, party, before, tail, continued, later⟩ :=
    treeCheck_open_locals_retained prims K D (fun _ => true) count v phase.ds k phase.reply.2
      phase.afterReply (phase.steps, phase.afterLocals) hashesAtReply phase.localsRun i kept
  exact ⟨opening, live, ds, sent, party, hashesPrefix.trans (replyPrefix.trans before),
    (treeSimLoggedWorld_prefix prims D _ opening.after (phase.steps i, tail) continued).trans
      (later.trans restPrefix), tail, continued, later⟩

end TreeCheckOpeningPhaseRun

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- Continue the retained setup outputs for a fixed number of exchanges.
Failed setup outputs stay absent, before any continuation can query. -/
def treeCheckAfterSetupPrefix {α : Type} (fuel : ℕ)
    (k : C.Party → Keys C → PrssKeys C → PartyM C E RealSpec α) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    ProbComp ((A.State × (C.Party → Option α)) × TreeSimState C) :=
  (simulateQ (treeSimLoggedWorld prims D) (do
    let next ← free (Concrete.sequenceFin fun i => continueStep (k i (x i)) (.done (p.1.2 i)))
    executeRounds worldRoles D A noFunctionality fuel p.1.1 next)).run p.2

/-- Exact setup composition for a prefix program, preserving both caches,
the adversary state, and all aborted rows. -/
theorem treeCheckAfterSetupPrefix_split {α : Type} (fuel : ℕ)
    (k : C.Party → Keys C → PrssKeys C → PartyM C E RealSpec α)
    (x : C.Party → Keys C) (z : Aux) :
    (simulateQ (treeSimLoggedWorld prims D)
      (realExecution D A noFunctionality (fuel + setupRounds)
        (fun i keys => prssSetup i >>= k i keys) x z)).run ((∅, ∅), []) =
      treeSaltSetup prims D A x z >>= treeCheckAfterSetupPrefix prims D A fuel k x := by
  unfold realExecution treeSaltSetup treeCheckAfterSetupPrefix
  simp only [setupRounds, executePhase_prssSetup_bind, simulateQ_bind, StateT.run_bind,
    bind_assoc, treeSimRealRoles, ← simulateQ_executePhase]

/-- The supported continuation supplies an actual position from the empty
world, together with provenance from this exact setup log. -/
theorem treeCheckAfterSetupPrefix_supported {α : Type} (fuel : ℕ)
    (k : C.Party → Keys C → PrssKeys C → PartyM C E RealSpec α)
    (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (out : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : out ∈ support (treeCheckAfterSetupPrefix prims D A fuel k x p)) :
    out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (realExecution D A noFunctionality (fuel + setupRounds)
        (fun i keys => prssSetup i >>= k i keys) x z)).run ((∅, ∅), [])) ∧
      p.2.2 <+: out.2.2 := by
  constructor
  · rw [treeCheckAfterSetupPrefix_split, mem_support_bind_iff]
    exact ⟨p, hp, run⟩
  · exact treeSimLoggedWorld_prefix prims D _ p.2 out run

/-- Construct the budget position from the actual supported continuation,
rather than a law-equivalent copy of the checkpoint. -/
def TreeCheckPrefixPosition.of_afterSetup (circuits : Circuits) (settings : Settings)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) {q : ℕ}
    (budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q)
    (fuel count : ℕ)
    (k : C.Party → Keys C → PrssKeys C → PartyM C E RealSpec
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (checkpoint : TreeCheckTailCheckpoint A)
    (run : checkpoint ∈ support (treeCheckAfterSetupPrefix prims D A fuel k x p))
    (room : fuel + setupRounds + (2 * halvings count + 5) ≤ ceremonyFuel circuits settings) :
    TreeCheckPrefixPosition prims circuits settings D A x z Z budget count checkpoint where
  rounds := fuel + setupRounds
  outputType := MainInput C × (Shares C Bit × List (Tuple C)) × RunState C
  program := fun i keys => prssSetup i >>= k i keys
  output := checkpoint
  run := (treeCheckAfterSetupPrefix_supported prims D A fuel k x z p hp checkpoint run).1
  state := rfl
  world := rfl
  room := room

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckOpeningRun.log_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckOpeningRun.log_prefix

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_open_locals_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_open_locals_retained

/-- info: 'ThresholdLeanXmssSecurity.treeCheckOpeningPhaseRun_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckOpeningPhaseRun_of_run

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckOpeningPhaseRun.opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckOpeningPhaseRun.opening

/-- info: 'ThresholdLeanXmssSecurity.treeCheckAfterSetupPrefix_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckAfterSetupPrefix_split

/-- info: 'ThresholdLeanXmssSecurity.treeCheckAfterSetupPrefix_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckAfterSetupPrefix_supported

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrefixPosition.of_afterSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckPrefixPosition.of_afterSetup

end ThresholdLeanXmssSecurity
