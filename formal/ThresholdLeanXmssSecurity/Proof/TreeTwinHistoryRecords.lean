import ThresholdLeanXmssSecurity.Proof.TreeTwinSavedEntry

/-!
# History records and remaining field budgets

Exact field encoding lengths preserve cross-run history lengths; known histories
remain equal under the actual held shift. Entry budgets require the incoming bit
budget and tuple counts on the same caller. Reached padding covers history reads
through the twin's digest permutations.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinHistoryRecords

open TreeTwinLinked2
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

theorem recordPeer_element_length_eq (i : C.Party) (h : C.Term → List Bit)
    (z : Shares C E) (count : ℕ) (T : C.Term) :
    (recordPeer K (elementCodec K) i h z count T).length = (h T).length +
      if i ∈ C.holders T then
        ((List.range count).filter fun g => (filler K .peer T g).isSome).length * elementBits
      else 0 := by
  have length (gs : List ℕ) :
      (gs.flatMap (fun g => List.ofFn (K.encode (z T g)))).length = gs.length * elementBits := by
    induction gs with
    | nil => simp
    | cons g gs ih => simp [ih, Nat.add_mul, Nat.add_comm]
  unfold recordPeer
  split_ifs <;> simp [elementCodec, Function.comp_def, length]

theorem recordMode_length_le (mode : ReshareMode) (i : C.Party) (h : C.Term → List Bit)
    (z : Shares C Bit) (count : ℕ) (T : C.Term) :
    (recordMode K mode i h z count T).length ≤ (h T).length + count := by
  unfold recordMode
  split_ifs
  · simp only [bitCodec, Function.comp_def, ← List.map_eq_flatMap, List.length_append,
      List.length_map]
    exact Nat.add_le_add_left ((List.length_filter_le _ _).trans_eq List.length_range) _
  · omega

theorem recordPeer_bit_length_le (i : C.Party) (h : C.Term → List Bit)
    (z : Shares C Bit) (count : ℕ) (T : C.Term) :
    (recordPeer K bitCodec i h z count T).length ≤ (h T).length + count :=
  recordMode_length_le K .peer i h z count T

/-- Equal hidden lengths and exact equality at every other term. -/
def HistoryLenAt (D : C.Coalition) (i : C.Party) (a b : RunState C) : Prop :=
  ∀ T, if i ∈ C.holders T ∧ lackedTerm D.1 = some T then
    (a.history T).length = (b.history T).length else b.history T = a.history T

def HistoryLenRel (D : C.Coalition) (a b : C.Party → RunState C) : Prop :=
  ∀ i, i ∉ D.1 → HistoryLenAt D i (a i) (b i)

theorem historyLenAt_of_runState (D : C.Coalition) (i : C.Party) (difference : List Bit)
    (a b : RunState C) (h : TreeSimRunStateRel D i difference a b) : HistoryLenAt D i a b := by
  intro T
  have ht := h.2.2 T
  split_ifs with held
  · rw [if_pos held] at ht
    simp [ht.2, List.length_zipWith, ht.1]
  · simpa only [if_neg held] using ht

theorem HistoryLenAt.length {D : C.Coalition} {i : C.Party} {a b : RunState C}
    (h : HistoryLenAt D i a b) (T : C.Term) : (a.history T).length = (b.history T).length := by
  have ht := h T
  split_ifs at ht
  · exact ht
  · rw [ht]

theorem historyLenAt_fieldExit (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (i : C.Party) (hi : i ∉ D.1) (x y : Shares C E × RunState C)
    (before : HistoryLenAt D i (d.st₁ i) (d.st₂ i))
    (exit : TreeSimExtendMultExitRel K D d i x y) : HistoryLenAt D i x.2 y.2 := by
  intro T
  rcases exit with ⟨shift, left, right⟩
  rw [left, right]
  dsimp only
  rw [d.self₁ i hi, d.self₂ i hi]
  by_cases held : i ∈ C.holders T ∧ lackedTerm D.1 = some T
  · rw [if_pos held, recordPeer_element_length_eq, recordPeer_element_length_eq,
      before.length T]
  · rw [if_neg held]
    have same := before T
    rw [if_neg held] at same
    by_cases ih : i ∈ C.holders T
    · have hidden : lackedTerm D.1 ≠ some T := fun h => held ⟨ih, h⟩
      have values : y.1 T = x.1 T := by
        funext g
        simp [shift, treeSimFieldHeldShift, hidden]
      simp [recordPeer, ih, same, values]
    · simp [recordPeer, ih, same]

theorem historyLenRel_fieldExit (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (x y : C.Party → Shares C E × RunState C)
    (before : HistoryLenRel D d.st₁ d.st₂)
    (exit : ∀ i, i ∉ D.1 → TreeSimExtendMultExitRel K D d i (x i) (y i)) :
    HistoryLenRel D (fun i => (x i).2) (fun i => (y i).2) :=
  fun i hi => historyLenAt_fieldExit K D d i hi (x i) (y i) (before i hi) (exit i hi)

theorem fieldExit_length_le (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (i : C.Party) (x y : Shares C E × RunState C)
    (exit : TreeSimExtendMultExitRel K D d i x y) (T : C.Term) :
    (x.2.history T).length ≤ ((d.st₁ i).history T).length + d.count * elementBits ∧
    (y.2.history T).length ≤ ((d.st₂ i).history T).length + d.count * elementBits := by
  rw [exit.2.1, exit.2.2]
  exact ⟨recordPeer_element_length K _ _ _ _ _, recordPeer_element_length K _ _ _ _ _⟩

theorem peerOutputs_history {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) (x : Shares C Bit × RunState C)
    (out : treeSimPeerOutputs K D ctx count rnd v st k sent i = some x) :
    x.2.history = recordPeer K bitCodec (ctx i).self (st i).history x.1 count := by
  simp only [treeSimPeerOutputs, treeSimPeerReturn] at out
  split_ifs at out
  cases out
  rfl

/-- Reserve every remaining two-product field record, including final randomization. -/
def FieldBudget (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (count index : ℕ) (st : C.Party → RunState C) : Prop :=
  ∀ i, i ∉ D.1 → ∀ T, ((st i).history T).length +
    (halvings count + 1 - index) * (2 * elementBits) ≤ historyLimit circuits settings



variable (circuits : Circuits) (settings : Settings)

theorem _root_.ThresholdLeanXmssSecurity.TreeTwinLinked2.BatchSite.jobs_mem {tree : Tree} (site : BatchSite settings tree) :
    ∃ (b : Fin (2 ^ layerHeight)) (enc : Encoding),
      site.jobs settings ∈ chunks settings.batchSize topJobs ∨
      site.jobs settings ∈ chunks settings.batchSize (bottomJobs b) ∨
      site.jobs settings ∈ chunks settings.batchSize (signJobs b enc) := by
  have mem : site.jobs settings ∈ chunks settings.batchSize site.phase.jobs := by
    unfold BatchSite.jobs
    rw [← List.getElem_eq_getD (h := site.bound)]
    exact List.getElem_mem _
  cases phase : site.phase with
  | top => exact ⟨0, (fun _ => ⟨0, by decide⟩), Or.inl (by simpa [phase, BatchPhase.jobs] using mem)⟩
  | bottom b => exact ⟨b, (fun _ => ⟨0, by decide⟩), Or.inr (Or.inl (by simpa [phase, BatchPhase.jobs] using mem))⟩
  | sign b a z w enc =>
    exact ⟨b, enc, Or.inr (Or.inr (by simpa [phase, BatchPhase.jobs] using mem))⟩

/-- The proposed layer-count invariant supplies the existing count-sum premise. -/
theorem layerCounts_total (circs : List Circuit) (tuples : List (Tuple C))
    (counts : tuples.map (·.count) =
      (List.range (depth circs)).map (fun l => (gatesAt circs l).length)) :
    (tuples.map (·.count)).sum + (outputsOf circs).length = tupleCount circs := by
  rw [counts, tupleCount_eq]

/-- Actual successful Rerand output, with the bit budget and counts kept explicit. -/
theorem fieldBudget_entry (top : TopTree) (tree : Tree) (D : C.Coalition)
    (parameter : PublicParameter) (openings : List (List (List Bit)))
    (c : Caller K circuits settings top tree D parameter openings)
    (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 → treeSimPeerOutputs K D c.peer.ctx₁ c.peer.count c.peer.rnd₁
      c.peer.v₁ c.peer.st₁ c.peer.k₁ c.sent i = some (x i))
    (budget : ∀ i, i ∉ D.1 → ∀ T,
      ((c.peer.st₁ i).history T).length ≤ ((c.rest.p₁ i).2.map (·.count)).sum)
    (counts : ∀ i, i ∉ D.1 → ((c.rest.p₁ i).2.map (·.count)).sum +
      (outputsOf c.rest.circs).length = tupleCount c.rest.circs) :
    FieldBudget circuits settings D (tupleCount c.rest.circs) 0 (fun i => (x i).2) := by
  obtain ⟨site, prior, circs, rest⟩ := c.batch
  obtain ⟨b, enc, mem⟩ := BatchSite.jobs_mem settings site
  have bound := measure_le_maxBatch circuits settings
    (fun cs => tupleCount cs + (halvings (tupleCount cs) + 1) * (2 * elementBits))
    parameter b enc (site.jobs settings) mem
  change c.rest.circs = runCircuits circuits parameter (site.jobs settings) at circs
  rw [← circs] at bound
  intro i hi T
  have record := congrFun (peerOutputs_history K D c.peer.ctx₁ c.peer.count c.peer.rnd₁
    c.peer.v₁ c.peer.st₁ c.peer.k₁ c.sent i (x i) (out i hi)) T
  have length := recordPeer_bit_length_le K (c.peer.ctx₁ i).self (c.peer.st₁ i).history
    (x i).1 c.peer.count T
  rw [← record, c.rest.count] at length
  have initial := budget i hi T
  have count := counts i hi
  change _ ≤ historyLimit circuits settings
  change _ ≤ maxBatch circuits settings _
  simp only [Nat.sub_zero]
  omega

/-- Padding coverage at the reached real cache after every digest permutation. -/
theorem treeTwin_reached_historyCovered (prims : Primitives)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (seeds : C.Term → HashOutput)
    (tagLabels : List (ℕ × ℕ)) (limit : ℕ) (r : Unit × HashCache C)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels limit)).run s.1.1))
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A x state
      ((r.2, s.1.2), s.2) n a)
    (swaps : List (List Bit × HashOutput × HashOutput))
    (history : List Bit) (length : history.length ≤ limit) :
    ∃ value, (treeStagesTwin swaps a.2).1.1 (.history history) = some value := by
  obtain ⟨value, hv⟩ := (treeTwin_entryPadding_reached prims K circuits settings top tree D A
    x state s seeds tagLabels limit r padding n a reach).history history length
  refine ⟨value, ?_⟩
  change treeStagesSwapAll swaps a.2.1.1 (.history history) = some value
  rw [treeTwin_swapAll_read swaps a.2.1.1 _ (fun v _ =>
    digestSwap_history v.1 history v.2.1 v.2.2)]
  exact hv

/-- The related simulated cache contains exactly the same covered history read. -/
theorem historyCovered_of_streamRel (δ : HiddenAddress C → Bit) (a : TreeSimState C)
    (b : HashCache C × HiddenCache C) (related : TreeSimStreamRel δ a b)
    (history : List Bit) (covered : ∃ value, a.1.1 (.history history) = some value) :
    ∃ value, b.1 (.history history) = some value := by
  rw [← related.1]
  exact covered

end ThresholdLeanXmssSecurity.TreeTwinHistoryRecords

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.recordPeer_element_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.recordPeer_element_length_eq

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.recordMode_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.recordMode_length_le

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.recordPeer_bit_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.recordPeer_bit_length_le

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyLenAt_of_runState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyLenAt_of_runState

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.HistoryLenAt.length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.HistoryLenAt.length

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyLenAt_fieldExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyLenAt_fieldExit

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyLenRel_fieldExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyLenRel_fieldExit

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.fieldExit_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.fieldExit_length_le

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.peerOutputs_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.peerOutputs_history

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.BatchSite.jobs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinLinked2.BatchSite.jobs_mem

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.layerCounts_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.layerCounts_total

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.fieldBudget_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.fieldBudget_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.treeTwin_reached_historyCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.treeTwin_reached_historyCovered

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyCovered_of_streamRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHistoryRecords.historyCovered_of_streamRel
