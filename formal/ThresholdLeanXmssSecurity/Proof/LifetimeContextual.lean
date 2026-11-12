import ThresholdLeanXmssSecurity.Proof.LifetimeJointSimStages
import ThresholdLeanXmssSecurity.Proof.TreeTwinKinds
import ThresholdLeanXmssSecurity.Proof.TreeLockstepLateBottom
import ThresholdLeanXmssSecurity.Proof.TreeHashBudgetRun

/-!
# Round certificates after a selecting prefix

The event family retains the selecting program in the adversary's initialization.
Its hash flag is exactly `TreeSimHashBad3`, and its check flag uses the same
complete transcript. The selector, its sampled keys and its cache remain joint.

The pinned and current leanVM proof directories were searched for prefix
absorption, logged dealer commutation and contextual round certificates. The
threshold interfaces below use `withPrefix` and the existing commutation laws.

`contextualStages_of_linked` reduces the round certificates to the existing
linked-kind invariant. `contextualCheckBound_of_indexed` reduces the check
estimate to fixed indexed events on one actual joint audit. Its per-index
allowances sum to the selected-tree error, preserving adaptive tree weights.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeContextual

open LifetimeBridge LifetimeJointSimStages

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} (prims : Primitives)
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The prefix is executed, retaining its calls and discarding only its result
after the actual selected input has been fixed for a support argument. -/
def absorbed (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty) (z : Aux) :=
  withPrefix A ((fun _ => z) <$> jointPrefix pre)

/-- Both flags use one absorbed adversary and one full real transcript. -/
def events (pre : Selector C) : TreeSimEvents C E := fun top tree D A x z Z log =>
  treeSimEvents3 prims K circuits settings top tree D (absorbed pre A z) x z Z log

theorem hashFlag (pre : Selector C) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C) :
    (events prims K circuits settings pre top tree D A x z Z log).1 =
      decide (TreeSimHashBad3 D log) := rfl

theorem absorbed_bound (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) (fuel q0 q : ℕ)
    (prefixBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (adversary : IsQueryBounded A Z fuel q) :
    IsQueryBounded (absorbed pre A z) Z fuel (q0 + q) := by
  apply isQueryBounded_withPrefix A Z _ fuel q0 q _ adversary
  simpa only [isQueryBoundP_map_iff] using prefixBudget

set_option backward.isDefEq.respectTransparency false in
/-- Changing initialization does not change a round certificate after that
initialization. Its recorded event is transported with the same adversary. -/
def roundStages_absorbed (pre : Selector C) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (stages : TreeSimRoundStages prims K circuits settings (treeSimEvents3 prims K circuits settings)
      top tree D (absorbed pre A z) parameter seeds pairs z Z dealt state s) :
    TreeSimRoundStages prims K circuits settings (events prims K circuits settings pre)
      top tree D A parameter seeds pairs z Z dealt state s where
  Bad := stages.Bad
  Inv := stages.Inv
  stage _ := .ceremony
  Q := stages.Q
  entry := by simpa only [absorbed, executePhase_withPrefix] using stages.entry
  noSetup _ _ _ _ h := by cases h
  badPersistent := stages.badPersistent
  done := stages.done
  output := stages.output
  peerBoundary _ _ h := by cases h
  collectorBoundary _ _ h := by cases h
  collectorNextBoundary _ _ h := by cases h
  rerandBoundary _ _ h := by cases h
  coinBoundary _ _ h := by cases h
  extendMultBoundary _ _ h := by cases h
  checkBoundary _ _ h := by cases h
  openingBoundary _ _ h := by cases h
  emptyOpeningBoundary _ _ h := by cases h
  ceremony a b _ inv good active := by
    have step : RelTriple
        ((stepRound (treeSimRealRoles prims D) D (absorbed pre A z) noFunctionality a.1.1 a.1.2).run a.2)
        ((stepRound (treeSimIdealRoles prims D) D (absorbed pre A z) noFunctionality b.1.1 b.1.2).run b.2)
        (fun x y => stages.Bad x.2 ∨ stages.Inv ((x.1.1, x.1.2.1), x.2) ((y.1.1, y.1.2.1), y.2)) := by
      cases tag : stages.stage a with
      | prssSetup => exact (stages.noSetup a b inv good tag).elim
      | reshare => exact stages.peer a b tag inv good active
      | reshareCollector => exact stages.collector a b tag inv good active
      | reshareCollectorNext => exact stages.collectorNext a b tag inv good active
      | rerand => exact stages.rerand a b tag inv good active
      | coin => exact stages.coin a b tag inv good active
      | extendMult => exact stages.extendMult a b tag inv good active
      | check => exact stages.check a b tag inv good active
      | openRep => exact stages.opening a b tag inv good active
      | openRepEmpty => exact stages.openingEmpty a b tag inv good active
      | ceremony => exact stages.ceremony a b tag inv good active
    simpa only [absorbed, stepRound_withPrefix] using step
  observeGood := stages.observeGood
  badRecorded := stages.badRecorded

/-- A local computation that returns its actual counted transcript. -/
def localLogged {α : Type} (p : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (α × TreeSimLog C) :=
  (simulateQ (QueryImpl.withTraceAppend (spec := LocalSpec C)
    (fun t => OracleComp.lift (OracleSpec.query t))
    (fun t u => ([⟨.inl (.inl t), u⟩] : TreeSimLog C))) p).run

set_option backward.isDefEq.respectTransparency false in
/-- Logging a local program preserves its whole result/cache law, with the
private-stream cache and incoming log retained. -/
theorem localLogged_run {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α)
    (cache : HashCache C) (hidden : HiddenCache C) (log : TreeSimLog C) :
    (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((cache, hidden), log) =
      (fun r => (r.1.1, (r.2, hidden), log ++ r.1.2)) <$>
        (simulateQ (localAnswer prims) (localLogged p)).run cache := by
  induction p using OracleComp.inductionOn generalizing cache hidden log with
  | pure a => simp [localLogged, worldRoles, counted_pure, WriterT.run_pure]
  | query_bind t k ih =>
    simp only [show worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun u => worldRoles.adversary (k u) from rfl,
      adversary_query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      treeSimLoggedWorld, streamWorld, onHash, StateT.run_mk,
      localLogged, QueryImpl.withTraceAppend_apply, WriterT.run_bind,
      WriterT.run_liftM, WriterT.run_tell, pure_bind, bind_assoc,
      simulateQ_map, StateT.run_map, bind_map_left, map_bind, Functor.map_map]
    simp only [ih, List.append_assoc]
    rfl

/-- A fixed dealer commutes with the logged selector without erasing either
result, the final cache, or a single real log entry. -/
theorem logged_dealer_swap {α β : Type} (D : C.Coalition)
    (p : OracleComp (LocalSpec C) α) (dealer : OracleComp (LocalSpec C) β)
    (cache : HashCache C) (hidden : HiddenCache C) (log : TreeSimLog C) :
    𝒟[do
      let r ← (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((cache, hidden), log)
      let d ← (simulateQ (localAnswer prims) dealer).run r.2.1.1
      pure ((r.1, d.1), ((d.2, r.2.1.2), r.2.2))] =
    𝒟[do
      let d ← (simulateQ (localAnswer prims) dealer).run cache
      let r ← (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((d.2, hidden), log)
      pure ((r.1, d.1), r.2)] := by
  have commute := (commutes_simulateQ (localAnswer prims)
    (fun t u => commutes_of_isAtom (isAtom_localAnswer prims t) (isAtom_localAnswer prims u))
    (localLogged p) dealer).bind (fun r d => pure (r, d)) cache
  have mapped := congrArg (fun d =>
    (fun r => ((r.1.1.1, r.1.2), ((r.2, hidden), log ++ r.1.1.2))) <$> d) commute
  simpa only [localLogged_run, StateT.run_bind, StateT.run_pure,
    bind_map_left, map_bind, map_pure, ← evalDist_map] using mapped

/-- Supported runs can be reordered while retaining their complete joint output. -/
theorem logged_dealer_swap_support {α β : Type} (D : C.Coalition)
    (p : OracleComp (LocalSpec C) α) (dealer : OracleComp (LocalSpec C) β)
    (r : α × TreeSimState C) (d : β × HashCache C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (worldRoles.adversary p)).run ((∅, ∅), [])))
    (hd : d ∈ support ((simulateQ (localAnswer prims) dealer).run r.2.1.1)) :
    ∃ d' ∈ support ((simulateQ (localAnswer prims) dealer).run ∅),
      ∃ r' ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary p)).run ((d'.2, ∅), [])),
        ((r.1, d.1), ((d.2, r.2.1.2), r.2.2)) = ((r'.1, d'.1), r'.2) := by
  have first : ((r.1, d.1), ((d.2, r.2.1.2), r.2.2)) ∈ support (do
      let r ← (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((∅, ∅), [])
      let d ← (simulateQ (localAnswer prims) dealer).run r.2.1.1
      pure ((r.1, d.1), ((d.2, r.2.1.2), r.2.2))) := by
    simp only [mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨r, hr, d, hd, rfl⟩
  have second := (mem_support_iff_of_evalDist_eq
    (logged_dealer_swap prims D p dealer ∅ ∅ []) _).mp first
  simpa only [mem_support_bind_iff, mem_support_pure_iff] using second

theorem absorbed_start (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (z z' : Aux) (corrupt : C.Party → Option (Keys C)) :
    worldRoles.adversary ((absorbed pre A z).start corrupt z') =
      (worldRoles.adversary (jointPrefix pre) >>= fun _ => worldRoles.adversary (A.start corrupt z)) := by
  simp only [absorbed, withPrefix, bind_map_left, worldRoles, liftComp_bind, counted_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Each reached joint initialization is a supported component initialization
with precisely its selected keys, dealer output, cache, state and transcript. -/
theorem commonPrefix_absorbed (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : JointInput C → PublicParameter) (seeds : JointInput C → C.Term → HashOutput)
    (pairs : JointInput C → C.Pair → HashOutput)
    (valid : ∀ p ∈ support (loggedPrefix prims D pre),
      p.1.1 = dealtKeys (parameter p.1) (seeds p.1) (pairs p.1))
    (p : (JointInput C × (Option TreeOutput × List (List (List Bit)))) × (A.State × TreeSimState C))
    (reached : p ∈ support (commonPrefix prims D pre A (dealerProgram circuits settings parameter seeds))) :
    (p.1.2, p.2) ∈ support (treeSimCommonPrefix prims circuits settings p.1.1.2.1 p.1.1.2.2.1 D
      (absorbed pre A p.1.1.2.2.2) (parameter p.1.1) (seeds p.1.1) (pairs p.1.1) p.1.1.2.2.2) := by
  simp only [commonPrefix, mem_support_bind_iff, mem_support_pure_iff] at reached
  obtain ⟨before, hb, d, hd, state, hs, rfl⟩ := reached
  obtain ⟨d', hd', before', hb', eq⟩ := logged_dealer_swap_support prims D (jointPrefix pre)
    (dealerProgram circuits settings parameter seeds before.1) before d hb hd
  have dealerEq : d'.1 = d.1 := (congrArg (fun r => r.1.2) eq).symm
  have stateEq : before'.2 = ((d.2, before.2.1.2), before.2.2) := (congrArg Prod.snd eq).symm
  simp only [treeSimCommonPrefix, absorbed_start, simulateQ_bind, StateT.run_bind,
    bind_assoc, mem_support_bind_iff, mem_support_pure_iff]
  refine ⟨d', hd', before', hb', state, ?_, ?_⟩
  · rw [stateEq, ← valid before hb]
    exact hs
  · exact Prod.ext dealerEq.symm rfl

/-- Component round certificates apply at every actual selected prefix. This
is support transport; no component probability is conditioned on selection. -/
theorem contextualStages_of_stages (stages : TreeSimStagesGoal3 prims K circuits settings) :
    ContextualStages prims K circuits settings (events prims K circuits settings) := by
  intro hb D pre A Z q0 q prefixBudget adversaryBudget small
  obtain ⟨parameter, seeds, pairs, valid⟩ := dealtData_exists prims D pre
  refine ⟨parameter, seeds, pairs, valid, ?_⟩
  intro p reached
  have member := commonPrefix_absorbed prims circuits settings D pre A parameter seeds pairs valid p reached
  obtain ⟨padding, certificates⟩ := stages hb p.1.1.2.1 p.1.1.2.2.1 D
    (absorbed pre A p.1.1.2.2.2) (parameter p.1.1) (seeds p.1.1) (pairs p.1.1) p.1.1.2.2.2 Z
    (q0 + q) (absorbed_bound pre A _ Z _ q0 q prefixBudget adversaryBudget) small (p.1.2, p.2) member
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨certificate⟩ := certificates r hr
  exact ⟨roundStages_absorbed prims K circuits settings pre _ _ D A _ _ _ _ Z _ _ _ certificate⟩

/-- The joint trace for a selected tail, retaining the selection and all calls. -/
def selectedTrace {α : Type} (D : C.Coalition) (pre : Selector C)
    (tail : JointInput C → OracleComp (WorldSpec C) α) :
    ProbComp ((JointInput C × α) × TreeSimLog C) := do
  let p ← loggedPrefix prims D pre
  (fun r : α × TreeSimState C => ((p.1, r.1), r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D) (tail p.1)).run p.2

/-- Absorbing a selector on support retains the actual selected tail and log.
The statement does not compare probabilities conditioned on its output. -/
theorem selectedTrace_support {α : Type} (D : C.Coalition) (pre : Selector C)
    (tail : JointInput C → OracleComp (WorldSpec C) α)
    (r : (JointInput C × α) × TreeSimLog C)
    (reached : r ∈ support (selectedTrace prims D pre tail)) :
    (r.1.2, r.2) ∈ support (treeSimLoggedRun prims D
      (worldRoles.adversary (jointPrefix pre) >>= fun _ => tail r.1.1)) := by
  simp only [selectedTrace, mem_support_bind_iff, support_map, Set.mem_image] at reached
  obtain ⟨p, hp, out, hout, rfl⟩ := reached
  rw [treeSimLoggedRun_eq_run]
  simp only [simulateQ_bind, StateT.run_bind, support_map, Set.mem_image, mem_support_bind_iff]
  exact ⟨out, ⟨p, hp, hout⟩, rfl⟩

def auditTail (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (input : JointInput C) :=
  treeSimCheckAuditedGame K circuits settings input.2.1 input.2.2.1 D A input.1 input.2.2.2 Z

/-- One audit of the actual selected ceremony; its prefix is neither reset
nor sampled independently of its selected input. -/
def auditTrace (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :=
  selectedTrace prims D pre (auditTail K circuits settings D A Z)

theorem audited_absorbed (pre : Selector C) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeSimCheckAuditedGame K circuits settings top tree D (absorbed pre A z) x z Z =
      (worldRoles.adversary (jointPrefix pre) >>= fun _ =>
        treeSimCheckAuditedGame K circuits settings top tree D A x z Z) := by
  simp only [treeSimCheckAuditedGame, realExecution]
  rw [absorbed_start]
  simp only [absorbed, executePhase_withPrefix, bind_assoc]

/-- Erasing the audit retains exactly the original joint real transcript. -/
theorem auditTrace_erase (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    (fun r => ((r.1.1, r.1.2.1), r.2)) <$> auditTrace prims K circuits settings D pre A Z =
      trace prims K circuits settings D pre A Z := by
  rw [trace_split]
  simp only [auditTrace, selectedTrace, map_bind, Functor.map_map]
  apply bind_congr
  intro p
  have erase := treeSimCheck_audited_game_erase K circuits settings p.1.2.1 p.1.2.2.1 D A
    p.1.1 p.1.2.2.2 Z
  simp only [auditTail, selectedGame, Bool.false_eq_true, ↓reduceIte]
  rw [← erase]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]

/-- The indexed event is evaluated on the same selected audit and full log. -/
def IndexedBad (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (j : ℕ)
    (r : (JointInput C × (Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))))) × TreeSimLog C) : Prop :=
  ∃ hj : j < treeBatches settings r.1.1.2.2.1,
    ¬ TreeSimHashBudgetCollision r.2 ∧
    TreeSimCheckIndexedBad prims K circuits settings r.1.1.2.1 r.1.1.2.2.1 D
      (absorbed pre A r.1.1.2.2.2) r.1.1.1 r.1.1.2.2.2 ⟨j, hj⟩ r.2 r.1.2.2

/-- The check flag forces an actual audited first-incorrect batch. -/
theorem check_indexed_cover (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (r : (JointInput C × (Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))))) × TreeSimLog C)
    (reached : r ∈ support (auditTrace prims K circuits settings D pre A Z))
    (bad : (flags (events prims K circuits settings pre) D A Z ((r.1.1, r.1.2.1), r.2)).2 = true) :
    ∃ j, IndexedBad prims K circuits settings D pre A j r := by
  have member := selectedTrace_support prims D pre (auditTail K circuits settings D A Z) r reached
  dsimp only [auditTail] at member
  rw [← audited_absorbed] at member
  simp only [flags, events, treeSimEvents3, decide_eq_true_eq] at bad
  obtain ⟨j, hj⟩ := treeSimCheck_indexed_cover prims K circuits settings hb r.1.1.2.1 r.1.1.2.2.1 D
    (absorbed pre A r.1.1.2.2.2) r.1.1.1 r.1.1.2.2.2 Z (r.1.2, r.2) member
    ⟨fun hash => bad.1 (Or.inl (Or.inl hash)), bad.2⟩
  exact ⟨j.val, j.isLt, fun collision => bad.1 (Or.inr collision), hj⟩

/-- The check flag is covered by batch indices, with no union over selectors,
parties, caches or scheduler rounds. -/
theorem check_indexed_union (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    (Pr[fun r => (flags (events prims K circuits settings pre) D A Z r).2 = true |
      trace prims K circuits settings D pre A Z]).toReal ≤
    ∑ j ∈ Finset.range (ceremonyBatches settings),
      (Pr[IndexedBad prims K circuits settings D pre A j |
        auditTrace prims K circuits settings D pre A Z]).toReal := by
  have bound : Pr[fun r => (flags (events prims K circuits settings pre) D A Z r).2 = true |
      trace prims K circuits settings D pre A Z] ≤
      ∑ j ∈ Finset.range (ceremonyBatches settings),
        Pr[IndexedBad prims K circuits settings D pre A j |
          auditTrace prims K circuits settings D pre A Z] := by
    rw [← auditTrace_erase, probEvent_map]
    refine (probEvent_mono ?_).trans (probEvent_exists_finset_le_sum _ _ _)
    intro r reached bad
    obtain ⟨j, hj⟩ := check_indexed_cover prims K circuits settings hb D pre A Z r reached bad
    exact ⟨j, Finset.mem_range.mpr
      (hj.choose.trans_le (treeBatches_le_ceremonyBatches settings r.1.1.2.2.1)), hj⟩
  have realBound := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun _ _ => probEvent_ne_top)) bound
  simpa only [ENNReal.toReal_sum (fun _ _ => probEvent_ne_top)] using realBound

/-- Each batch index is charged on the actual joint audit, against the
selected tree's contribution to the fixed check error. These are unconditional
probability inequalities on the complete prefix-and-tail experiment. -/
def IndexedCheckBounds : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q0 + q < 2 ^ 128 →
    ∀ j ∈ Finset.range (ceremonyBatches settings),
      (Pr[IndexedBad prims K circuits settings D pre A j |
        auditTrace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree => if j < treeBatches settings tree then
        checkErrorOf (E := E) (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
          (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q0 + q) else 0)

theorem batch_sum (N n : ℕ) (hn : n ≤ N) (e : ℝ) :
    (∑ j ∈ Finset.range N, if j < n then e else 0) = n * e := by
  rw [← Finset.sum_filter]
  have filter : (Finset.range N).filter (fun j => j < n) = Finset.range n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp [filter]

/-- Summing the active indexed allowances gives the expected selected-tree
error exactly, without replacing it by the largest tree's error. -/
theorem indexed_allowance_sum (pre : Selector C) (q : ℕ) :
    (∑ j ∈ Finset.range (ceremonyBatches settings),
      jointError prims pre (fun tree => if j < treeBatches settings tree then
        checkErrorOf (E := E) (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
          (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q else 0)) =
      jointError prims pre (fun tree => treeCheckError (E := E) circuits settings tree q) := by
  classical
  unfold jointError
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [selectedError, ← Finset.mul_sum]
  rw [batch_sum _ _ (treeBatches_le_ceremonyBatches settings p.1.2.2.1)]
  rfl

/-- The actual indexed caps discharge the contextual check bound for the
same event family used by the round-certificate reduction. -/
theorem contextualCheckBound_of_indexed (checks : IndexedCheckBounds prims K circuits settings) :
    ContextualCheckBound prims K circuits settings (events prims K circuits settings) := by
  intro hb D pre A Z q0 q prefixBudget adversaryBudget small
  apply (check_indexed_union prims K circuits settings hb D pre A Z).trans
  rw [← indexed_allowance_sum prims (E := E) circuits settings pre (q0 + q)]
  exact Finset.sum_le_sum (checks hb D pre A Z q0 q prefixBudget adversaryBudget small)

/-- One concrete event family supplies both contextual obligations and the
exact required hash flag. Its two semantic inputs use no independent event witnesses. -/
theorem contextual_of_stages_indexed
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (checks : IndexedCheckBounds prims K circuits settings) :
    (∀ pre top tree D A x z Z log,
      (events prims K circuits settings pre top tree D A x z Z log).1 = decide (TreeSimHashBad3 D log)) ∧
    ContextualStages prims K circuits settings (events prims K circuits settings) ∧
    ContextualCheckBound prims K circuits settings (events prims K circuits settings) :=
  ⟨hashFlag prims K circuits settings,
    contextualStages_of_stages prims K circuits settings stages,
    contextualCheckBound_of_indexed prims K circuits settings checks⟩

/-- The complete lockstep schedule reduces the contextual stage construction
to the original linked-kind invariant. -/
theorem contextualStages_of_linked (linked : TreeTwinLinkedGoal prims K circuits settings) :
    ContextualStages prims K circuits settings (events prims K circuits settings) :=
  contextualStages_of_stages prims K circuits settings
    (treeSimStagesGoal3_of_linked prims K circuits settings
      (treeLockstepStagesGoal_of_segments circuits prims K settings
        (treeLockstepSegments K circuits settings prims))
      (treeTwinDigestDrawsGoal circuits prims K settings) linked)

/-- The joint simulation bound uses the same fixed events throughout, the
exact honest hash budget, and the existing linked-kind and salt obligations. -/
theorem jointSimulationFromComponent_of_linked_indexed
    (linked : TreeTwinLinkedGoal prims K circuits settings)
    (checks : IndexedCheckBounds prims K circuits settings)
    (salts : JointSaltBounds prims K circuits settings) :
    JointSimulationFromComponent prims K circuits settings :=
  jointSimulationFromComponent_of_contextual prims K circuits settings
    (events prims K circuits settings) (hashFlag prims K circuits settings)
    (contextualStages_of_linked prims K circuits settings linked)
    (treeSimHashHonestBudget K prims circuits settings) salts
    (contextualCheckBound_of_indexed prims K circuits settings checks)

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.hashFlag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hashFlag

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.absorbed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms absorbed_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.roundStages_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundStages_absorbed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.localLogged_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localLogged_run

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.logged_dealer_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logged_dealer_swap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.commonPrefix_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commonPrefix_absorbed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.contextualStages_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contextualStages_of_stages

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.selectedTrace_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectedTrace_support

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.auditTrace_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditTrace_erase

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.check_indexed_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_indexed_cover

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.check_indexed_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_indexed_union

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.indexed_allowance_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms indexed_allowance_sum

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.contextualCheckBound_of_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contextualCheckBound_of_indexed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.contextual_of_stages_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contextual_of_stages_indexed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.contextualStages_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contextualStages_of_linked

/-- info: 'ThresholdLeanXmssSecurity.LifetimeContextual.jointSimulationFromComponent_of_linked_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSimulationFromComponent_of_linked_indexed

end ThresholdLeanXmssSecurity.LifetimeContextual
