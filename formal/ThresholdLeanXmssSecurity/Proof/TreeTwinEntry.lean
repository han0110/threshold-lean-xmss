import ThresholdLeanXmssSecurity.Proof.TreeTwinLater
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedFinal

/-!
# Concrete code and finite cache coverage for twin entry

The target is the entry part of `TreeTwinLinkedGoal`. The original goal also
requires closure of every later round kind. In particular, zero-output batches
must use their own kinds, rather than an added restriction on `Circuits`.

The pinned and current leanVM proof trees were searched for threshold entry,
finite expansion coverage and history padding. The threshold-specific cache
coverage lemmas below reuse `TreeSimStages` and its generic query prefetching.

The finite prefix covers real/dummy PRF inputs, all batch tuple counts,
check expansions, challenge attempts and histories up to a supplied bound.
Coverage survives the original setup and every reached prefix, including
aborts. An actual supported pre-check program supplies its tuple/history bound.

`TreeTwinEntryGoal` retains the original entry quantifiers and relation. Its
witness must select the original saved
continuations, establish entry with the linked stages (including partial setup
and zero-output cases), and bound the tags and ideal histories at later reached
gadgets. The code filter below alone does not constrain those continuations.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A filter for real/simulator batch gadgets and positive-width circuits.
Selecting the original saved continuations is a separate entry obligation. -/
def TreeTwinEntryAllowed (D : C.Coalition) (parameter : PublicParameter)
    (openings : List (List (List Bit))) (code : TreeTwinCode C E) : Prop :=
  ∃ (b : Fin (2 ^ layerHeight)) (enc : Encoding) (jobs : List Job) (batch : ℕ),
    (jobs ∈ chunks settings.batchSize topJobs ∨
      jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      jobs ∈ chunks settings.batchSize (signJobs b enc)) ∧
    code.2.2.2.2.1 = runCircuits circuits parameter jobs ∧
    (outputsOf code.2.2.2.2.1).length ≠ 0 ∧
    code.2.2.1 = (fun i => realRunGadgets K (code.1 i) settings.mode) ∧
    code.2.2.2.1 = (fun i => treeSimGadgets K circuits settings D parameter
      (code.2.1 i).keys.seed openings (code.2.1 i) batch jobs)

theorem treeTwinEntryAllowed_outputs (D : C.Coalition) (parameter : PublicParameter)
    (openings : List (List (List Bit))) :
    TreeTwinAllowedOutputs (TreeTwinEntryAllowed K circuits settings D parameter openings) := by
  rintro code ⟨b, enc, jobs, batch, mem, same, outputs, rest⟩
  exact outputs

/-- The finite count bound follows from the concrete circuit code, rather
than from the relational saved-tuple invariant. -/
theorem treeTwinEntryAllowed_count (D : C.Coalition) (parameter : PublicParameter)
    (openings : List (List (List Bit))) (code : TreeTwinCode C E)
    (allowed : TreeTwinEntryAllowed K circuits settings D parameter openings code) :
    tupleCount code.2.2.2.2.1 ≤ maxBatch circuits settings tupleCount := by
  obtain ⟨b, enc, jobs, batch, mem, same, rest⟩ := allowed
  rw [same]
  exact measure_le_maxBatch circuits settings tupleCount parameter b enc jobs mem

/-- Histories of every length up to a fixed bound, including the ideal
history needed by the digest swap's `inner'` premise. -/
def treeTwinHistoryQueries (limit : ℕ) : List (Query C) :=
  (List.range (limit + 1)).flatMap fun n =>
    (Finset.univ : Finset (Fin n → Bit)).toList.map fun v => .history (List.ofFn v)

def treeTwinHistoryPadding (limit : ℕ) : OracleComp (LocalSpec C) Unit := do
  let _ ← (treeTwinHistoryQueries (C := C) limit).mapM fun q => liftComp (hashQuery q) (LocalSpec C)
  pure ()

/-- Adapted from the existing finite-copy and check-padding proofs in
`TreeSimStages`: only the query constructor and bounded-length enumeration differ. -/
theorem treeTwin_historyPadding_covered (limit : ℕ) (cache : HashCache C)
    (r : Unit × HashCache C)
    (run : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinHistoryPadding (C := C) limit)).run cache)) :
    cache ≤ r.2 ∧ ∀ history : List Bit, history.length ≤ limit →
      ∃ value, r.2 (.history history) = some value := by
  simp only [treeTwinHistoryPadding, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨u, hu, rfl⟩ := run
  obtain ⟨grows, covered⟩ := treeStages_prefetch_queries prims _ (by
    intro q hq
    obtain ⟨n, hn, v, hv, rfl⟩ := by
      simpa only [treeTwinHistoryQueries, List.mem_flatMap, List.mem_map] using hq
    rintro ⟨_, heq, _⟩
    cases heq) cache u hu
  refine ⟨grows, ?_⟩
  intro history bound
  apply covered
  simp only [treeTwinHistoryQueries, List.mem_flatMap, List.mem_map]
  refine ⟨history.length, List.mem_range.mpr (by omega),
    (fun i : Fin history.length => history[i.val]), by simp, ?_⟩
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Filled histories never exceed the total tuple count, also for nonholders. -/
theorem treeTwin_filledHistory_length_le (i : C.Party) (tuples : List (Tuple C)) (T : C.Term) :
    (filledHistory K i tuples T).length ≤ (tuples.map (·.count)).sum := by
  unfold filledHistory
  split_ifs
  · induction tuples with
    | nil => simp
    | cons t ts ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.map_cons, List.sum_cons]
      exact Nat.add_le_add ((List.length_filter_le _ _).trans_eq List.length_range) ih
  · simp

/-- The actual real prefix supplies the history bound; no final ceremony
success is assumed. -/
theorem treeTwin_beforeVerify_history_bound (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (label tag : ℕ)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (run : some (out, final) ∈ support
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run ⟨fun _ => [], label, tag⟩).run)
    (T : C.Term) : (final.history T).length ≤ tupleCount jobs := by
  have shape := treeSimCheckBeforeVerify_state K ctx mode jobs inputs label tag out final run
  rw [shape.1, ← treeSimCheckBeforeVerify_count K ctx mode jobs inputs label tag out final run]
  exact treeTwin_filledHistory_length_le K ctx.self out.2 T

/-- One finite prefix for real and simulator inputs, every possible check
expansion count, rejection-sampler attempts, and bounded ideal histories. -/
def treeTwinEntryPadding (seeds : C.Term → HashOutput) (tagLabels : List (ℕ × ℕ))
    (historyLimit : ℕ) : OracleComp (LocalSpec C) Unit := do
  treeStagesCeremonyPrfPadding seeds
  treeStagesCheckPadding K tagLabels (List.range (maxBatch circuits settings tupleCount + 1)) 1
  treeStagesChallengePadding K tagLabels 1
  treeTwinHistoryPadding historyLimit

structure TreeTwinEntryCoverage (D : C.Coalition) (seeds : C.Term → HashOutput)
    (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ) (cache : HashCache C) : Prop where
  realInputs : ∀ jobs, TreeStagesPrfCovered cache seeds jobs
  idealInputs : ∀ jobs, TreeStagesPrfCovered cache (fun T => if KnownTo D.1 T then seeds T else 0) jobs
  expansion : ∀ tag label, (tag, label) ∈ tagLabels →
    ∀ count, count ≤ maxBatch circuits settings tupleCount →
      ∀ values : List E, values.length = 1 → TreeStagesExpansionCovered K cache tag label values count
  challenge : ∀ tag label, (tag, label) ∈ tagLabels →
    ∀ values : List E, values.length = 1 → TreeStagesChallengeCovered K cache tag label values
  history : ∀ history : List Bit, history.length ≤ historyLimit →
    ∃ value, cache (.history history) = some value

theorem TreeTwinEntryCoverage.mono {D : C.Coalition} {seeds : C.Term → HashOutput}
    {tagLabels : List (ℕ × ℕ)} {historyLimit : ℕ} {a b : HashCache C}
    (covered : TreeTwinEntryCoverage K circuits settings D seeds tagLabels historyLimit a)
    (grows : a ≤ b) : TreeTwinEntryCoverage K circuits settings D seeds tagLabels historyLimit b := by
  refine ⟨fun jobs => treeStages_prfCovered_mono grows _ _ (covered.realInputs jobs),
    fun jobs => treeStages_prfCovered_mono grows _ _ (covered.idealInputs jobs), ?_, ?_, ?_⟩
  · intro tag label mem count bound values length
    exact treeStages_expansionCovered_mono K grows tag label values count
      (covered.expansion tag label mem count bound values length)
  · intro tag label mem values length
    exact treeStages_challengeCovered_mono K grows tag label values
      (covered.challenge tag label mem values length)
  · intro history bound
    obtain ⟨value, cached⟩ := covered.history history bound
    exact ⟨value, grows cached⟩

theorem treeTwin_entryPadding_covered (D : C.Coalition) (seeds : C.Term → HashOutput)
    (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ) (cache : HashCache C) (r : Unit × HashCache C)
    (run : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit)).run cache)) :
    cache ≤ r.2 ∧ TreeTwinEntryCoverage K circuits settings D seeds tagLabels historyLimit r.2 := by
  simp only [treeTwinEntryPadding, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨u, hu, v, hv, w, hw, hr⟩ := run
  obtain ⟨gu, inputs⟩ := treeStages_ceremonyPrfPadding_covered prims D seeds cache u hu
  obtain ⟨gv, expansion⟩ := treeStages_checkPadding_covered prims K tagLabels
    (List.range (maxBatch circuits settings tupleCount + 1)) 1 u.2 v hv
  obtain ⟨gw, challenge⟩ := treeStages_challengePadding_covered prims K tagLabels 1 v.2 w hw
  obtain ⟨gr, history⟩ := treeTwin_historyPadding_covered prims historyLimit w.2 r hr
  refine ⟨gu.trans (gv.trans (gw.trans gr)), ?_⟩
  refine ⟨fun jobs => treeStages_prfCovered_mono (gv.trans (gw.trans gr)) _ _ (inputs jobs).1,
    fun jobs => treeStages_prfCovered_mono (gv.trans (gw.trans gr)) _ _ (inputs jobs).2,
    ?_, ?_, history⟩
  · intro tag label mem count bound values length
    exact treeStages_expansionCovered_mono K (gw.trans gr) tag label values count
      (expansion tag label mem count (List.mem_range.mpr (by omega)) values length)
  · intro tag label mem values length
    exact treeStages_challengeCovered_mono K gr tag label values
      (challenge tag label mem values length)

/-- The original reached trace, including its setup and aborting branches,
retains every public cache entry installed by padding. -/
theorem treeTwin_reach_cache_grows (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A x state s n a) :
    s.1.1 ≤ a.2.1.1 := by
  simp only [TreeStagesReach, treeStagesTrace, StateT.run_bind, mem_support_bind_iff] at reach
  obtain ⟨setup, hs, next, hn, ha⟩ := reach
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hs
  exact (treeSim_logged_grows prims D _ s setup hs).trans
    ((treeSim_logged_grows prims D _ setup.2 next hn).trans
      (treeStages_executeSteps_grows prims D A n setup.1.1 next.1 next.2 a ha))

theorem treeTwin_entryPadding_reached (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (seeds : C.Term → HashOutput)
    (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ) (r : Unit × HashCache C)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit)).run s.1.1))
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A x state
      ((r.2, s.1.2), s.2) n a) :
    TreeTwinEntryCoverage K circuits settings D seeds tagLabels historyLimit a.2.1.1 :=
  (treeTwin_entryPadding_covered prims K circuits settings D seeds tagLabels historyLimit s.1.1 r padding).2.mono
    K circuits settings (treeTwin_reach_cache_grows prims K circuits settings top tree D A x state
      ((r.2, s.1.2), s.2) n a reach)

/-- At a supported pre-check return, the cache covers the actual tuple count
and history. Only membership of the saved tag and label is still explicit. -/
theorem TreeTwinEntryCoverage.beforeVerify {D : C.Coalition} {seeds : C.Term → HashOutput}
    {tagLabels : List (ℕ × ℕ)} {historyLimit : ℕ} {cache : HashCache C}
    (covered : TreeTwinEntryCoverage K circuits settings D seeds tagLabels historyLimit cache)
    (ctx : Context C) (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (enc : Encoding)
    (jobs : List Job)
    (mem : jobs ∈ chunks settings.batchSize topJobs ∨
      jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      jobs ∈ chunks settings.batchSize (signJobs b enc))
    (inputs : List (C.Term → List Bit)) (label tag : ℕ)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (run : some (out, final) ∈ support
      ((treeSimCheckBeforeVerify K ctx settings.mode (runCircuits circuits parameter jobs) inputs).run
        ⟨fun _ => [], label, tag⟩).run)
    (tags : (final.tag, final.label) ∈ tagLabels)
    (historyBound : tupleCount (runCircuits circuits parameter jobs) ≤ historyLimit) :
    (∀ values : List E, values.length = 1 → TreeStagesExpansionCovered K cache final.tag final.label
      values (out.2.map (·.count)).sum) ∧
      ∀ T, ∃ value, cache (.history (final.history T)) = some value := by
  have count := treeSimCheckBeforeVerify_count K ctx settings.mode
    (runCircuits circuits parameter jobs) inputs label tag out final run
  constructor
  · intro values length
    apply covered.expansion final.tag final.label tags _ _ values length
    rw [count]
    exact measure_le_maxBatch circuits settings tupleCount parameter b enc jobs mem
  · intro T
    exact covered.history _ ((treeTwin_beforeVerify_history_bound K ctx settings.mode
      (runCircuits circuits parameter jobs) inputs label tag out final run T).trans historyBound)

/-- The exact entry part of `TreeTwinLinkedGoal`, with its original setup,
padding, allowed-code and stage witnesses. The later `next` obligations are A68. -/
def TreeTwinEntryGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ (Allowed : TreeTwinCode C E → Prop)
      (others : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
        TreeSimConfig A (HashCache C × HiddenCache C) → Prop)),
    TreeTwinAllowedOutputs Allowed ∧
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D (treeTwinDataStage K D (fun _ => False) (treeTwinLinkedKinds K D Allowed others)))

theorem treeTwinEntryGoal_of_linked (linked : TreeTwinLinkedGoal prims K circuits settings) :
    TreeTwinEntryGoal prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq small p hp good
  obtain ⟨padding, hpadding⟩ := linked hb top tree D A parameter seeds pairs z Z q hq small p hp good
  refine ⟨padding, ?_⟩
  intro r hr
  obtain ⟨allowed, others, outputs, entry, _⟩ := hpadding r hr
  exact ⟨allowed, others, outputs, entry⟩

/-- info: 'ThresholdLeanXmssSecurity.treeTwinEntryAllowed_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinEntryAllowed_count

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_historyPadding_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_historyPadding_covered

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_beforeVerify_history_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_beforeVerify_history_bound

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_entryPadding_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_entryPadding_covered

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_entryPadding_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_entryPadding_reached

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinEntryCoverage.beforeVerify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinEntryCoverage.beforeVerify

/-- info: 'ThresholdLeanXmssSecurity.treeTwinEntryGoal_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinEntryGoal_of_linked

end ThresholdLeanXmssSecurity
