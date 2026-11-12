import ThresholdLeanXmssSecurity.Proof.TreeCheckCoinClock
import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestLog
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkPositions
import XmssSecurity.Proof.QueryBoundSupport
import XmssSecurity.Proof.EncodingQueryAccounting

/-! # The check label at a decoded signing checkpoint

The complete first-pass result is shared by the actual pending program and
its decoded boundary. A live honest continuation probes the boundary's saved
coin label. Quiet prefix rounds preserve every honest-log cutoff.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckSigningProbe
open TreeCheckCoinClock TreeCheckHonestLog TreeCheckWalkState TreeCheckWalkRecipe
open TreeCheckHonestDisc TreeSimHashCount
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β : Type}

private theorem floor_left {limit : ℕ} {p : PartyM C E RealSpec α}
    {k : α → PartyM C E RealSpec β} (h : CheckFloor limit (p >>= k).run) :
    CheckFloor limit p.run := by
  exact IsQueryBoundP.of_bind_left h

private theorem floor_right {limit : ℕ} {p : PartyM C E RealSpec α}
    {k : α → PartyM C E RealSpec β} (h : CheckFloor limit (p >>= k).run)
    (a : α) (ha : some a ∈ support p.run) : CheckFloor limit (k a).run := by
  exact XmssSecurity.OracleComp.IsQueryBoundP.bind_right_of_mem_support h (some a) ha

/-- A successful timed prefix exposes the continuation of the same suspended step. -/
theorem suspended_floor {limit n : ℕ}
    {allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop} (step : Step C E RealSpec α)
    (timed : TreeSimCheckTimedStep (n + 1) step) (k : α → PartyM C E RealSpec β)
    (a : α) (replay : TreeSimCheckStepAllowed allowed step a)
    (floor : ∀ inbox, CheckFloor limit (resumed (suspendStep k step) inbox)) :
    CheckFloor limit (k a).run := by
  cases step with
  | done out =>
    have stopped : out = none := timed
    have live : out = some a := replay
    rw [stopped] at live
    cases live
  | wait out resume =>
    obtain ⟨inbox, run⟩ := replay
    exact floor_right (floor inbox) a run.choose_spec.1.mem_support
  | call impossible resume => exact impossible.elim

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- A supported nonempty check queries the label saved before its first coin. -/
theorem check_floor_label (ctx : Context C) (st : RunState C) (tuples : List (Tuple C))
    (nonzero : (tuples.map (·.count)).sum ≠ 0) (checked : Unit × RunState C)
    (run : some checked ∈ support ((check (G := RealSpec) K ctx (realCheckGadgets K ctx) tuples).run st).run)
    (limit : ℕ) (floor : CheckFloor limit
      ((check (G := RealSpec) K ctx (realCheckGadgets K ctx) tuples).run st).run) : limit ≤ st.label := by
  rw [check_eq K ctx _ tuples nonzero] at floor run
  simp only [StateT.run_bind] at floor run
  have coinFloor := floor_left floor
  obtain ⟨key, keyRun, rest⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind] at coinFloor keyRun
  obtain ⟨values, valuesRun, hashRun⟩ := treeSimCheck_some_bind _ _ _ keyRun
  have hashFloor := floor_right coinFloor values valuesRun
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
    (.inl (.inl (.inr (.inl (.coinKey st.tag st.label
      (values.1.flatMap fun v => List.ofFn (K.encode v)))))))) >>=
    (fun key => pure (some (key, values.2)))) _ 0 at hashFloor
  rw [isQueryBoundP_query_bind_iff] at hashFloor
  have noBelow := hashFloor.1
  simp only [PartyQuery, CoinBelow] at noBelow
  omega

variable (prims : Primitives) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings)

/-- One first-pass witness supports the live label probe and every log cutoff. -/
theorem boundary_probe (Z : Distinguisher C A.State TreeOutput)
    (b : TreeCheckTailBoundary A)
    (self : ∀ i, (b.batch.ctx i).self = i)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (nonzero : tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) ≠ 0)
    (o : TreeCheckTailCheckpoint A) (preRun : o ∈ support (b.pre prims K circuits settings D))
    (r : TreeCheckTailResult A)
    (contRun : r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o))
    (i : C.Party) (honest : i ∉ D.1)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C)) (accepted : r.1.2.2 i = some actual) :
    ∃ out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world),
      out.2.1.1 ≤ o.2.1.1 ∧ out.2.2 <+: o.2.2 ∧
      (∀ limit, HonestCheckLog limit out.2.1.1 out.2.2 → HonestCheckLog limit o.2.1.1 o.2.2) ∧
      ∀ limit, (∀ inbox, CheckFloor limit (resumed (out.1 i) inbox)) →
        limit ≤ b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1 := by
  let p := fun i => treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial
  let k := fun i data => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs
    b.batch.initial data >>= b.batch.k i
  have timed i : TreeSimCheckTimed
      (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds + 1)
      (p i).run := treeLockstep_localPrelude_timed _ _ _ (by
        simpa only [parameter i] using treeSimCheckBatchPrefix_timed K circuits settings
          (b.batch.ctx i) b.batch.jobs b.batch.initial)
  have start := treeSimCheckTimed_start D
    (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds)
    p k timed
  have same : (b.program K circuits settings) = fun i => p i >>= k i := by
    funext i
    simp only [TreeCheckTailBoundary.program, treeSimCheckBatchAudit_run_prefix, bind_assoc, p, k]
  have run := preRun
  unfold TreeCheckTailBoundary.pre executePhase at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨started, hs, run⟩ := run
  let out := ((fun i => suspendStep (k i) (started.1 i)), started.2)
  have firstRun : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world) := by
    rw [same, start, simulateQ_map, StateT.run_map, support_map]
    exact ⟨started, hs, rfl⟩
  refine ⟨out, firstRun, treeSim_logged_grows prims D _ _ _ run,
    treeSimLoggedWorld_prefix prims D _ _ _ run, ?_, ?_⟩
  · intro limit log
    apply rounds_honest prims D limit _ _ started.1 _ started.2 log o run
    intro h
    have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) h
    by_cases hh : h ∈ D.1
    · simp only [if_pos hh, mem_support_pure_iff] at each
      rw [each]
      trivial
    · simp only [if_neg hh, worldRoles] at each
      exact prelude_advance_quiet _ _ (batchPrefix_quiet K circuits settings _ _ _) _
        (treeSimCheck_support_free _ each)
  · intro limit floor
    obtain ⟨data, present, localRun⟩ := TreeCheckWalkRecipe.batchCont_local_support
      prims K circuits D A Z b.batch o r contRun i honest actual accepted
    have replay := treeSimCheck_rounds_replay D A noFunctionality _ _ _
      started.1 o.1 (treeLockstep_logged_run_allowed prims D _ _ o run) i honest data present
    have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) i
    simp only [if_neg honest, worldRoles] at each
    have pending := (timed i).advance_mem _ (treeSimCheck_support_free _ each)
    have finishFloor := suspended_floor (started.1 i) pending (k i) data replay floor
    have counts := b.counts prims K circuits settings D Z self parameter o preRun r contRun
      ⟨i, actual, accepted⟩ i honest
    obtain ⟨data', present', history, label, tag, counts, modes⟩ := counts
    have eq : data' = data := Option.some.inj (present'.symm.trans present)
    subst data'
    have dataNonzero : (data.2.1.2.map (·.count)).sum ≠ 0 := by
      rw [counts, TreeCheckBatchWalk.counts_sum]
      exact nonzero
    simp only [k, treeSimCheckBatchFinish, treeSimCheckAfterVerify, bind_assoc] at finishFloor localRun
    obtain ⟨checked, checkRun, rest⟩ := treeSimCheck_some_bind _ _ _ localRun
    have le := check_floor_label K (b.batch.ctx i) data.2.2 data.2.1.2 dataNonzero checked
      checkRun limit (floor_left finishFloor)
    exact label ▸ le

/-- The decoded source retains an actual first pass whose live future floor
cannot exceed the label of the fixed hybrid. -/
theorem source_probe (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (dealt : DealtInputs D x) (z : Aux) (j : Fin (treeBatches settings tree))
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : TreeCheckWalkDef.Decoded (decode prims K D A circuits settings top tree x setup.1.2 j.val))
    (o : TreeCheckTailCheckpoint A)
    (preRun : o ∈ support (((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).boundary c).pre
      prims K circuits settings D))
    (r : TreeCheckTailResult A)
    (contRun : r ∈ support (((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r)
    (i : C.Party) (honest : i ∉ D.1)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C)) (accepted : r.1.2.2 i = some actual) :
    ∃ out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D c.1.1.program)).run c.1.1.world),
      out.2.1.1 ≤ o.2.1.1 ∧ out.2.2 <+: o.2.2 ∧
      (∀ limit, HonestCheckLog limit out.2.1.1 out.2.2 → HonestCheckLog limit o.2.1.1 o.2.2) ∧
      ∀ limit, (∀ inbox, CheckFloor limit (resumed (out.1 i) inbox)) →
        limit ≤ ((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).hybrid c o).label := by
  let b := (sourceWalk prims K D A circuits settings top tree x j.val Z step setup).boundary c
  have self h : (b.batch.ctx h).self = h := rfl
  have parameter h : (b.batch.ctx h).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, keys⟩ := dealt
    change (x h).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [keys h, keys (refHolder D K.publicTerm)]
    rfl
  have nonzero := TreeCheckWalkPositions.source_count_ne_zero prims K D A circuits settings
    top tree x z j Z step setup c o r contRun bad
  obtain ⟨out, supported, grows, logPrefix, logs, probe⟩ := boundary_probe K prims D A circuits settings
    Z b self parameter nonzero o preRun r contRun i honest actual accepted
  refine ⟨out, ?_, grows, logPrefix, logs, probe⟩
  have fits := decode_sound prims K D A circuits settings top tree x setup.1.2 j.val c
  rw [fits.2.2]
  exact supported

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningProbe.suspended_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms suspended_floor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningProbe.check_floor_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_floor_label

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningProbe.boundary_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_probe

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningProbe.source_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_probe

end TreeCheckSigningProbe
end ThresholdLeanXmssSecurity
