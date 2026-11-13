import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRows
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncBackend

/-! # Virtual and pending rows established by a bottom-tree build -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncChain SigningCompilerSyncRows
open SigningCompilerSyncBackend
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false

/-- Every X-source computation preserves the already allocated domains. -/
theorem runX_rows {α : Type}
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (oa : SourceMX C α) (src : SourceState C) (st : FullState C Tag)
    (r : (α × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) oa src st)) :
    (dataOf x st).virtual ⊆ (dataOf x r.2).virtual ∧
      ∀ p, (dataOf x st).pending p ≠ none → (dataOf x r.2).pending p ≠ none :=
  simulate_rows tagOf x q s pads τ g noise rest (oa.run src) st r hr

/-- A virtual call records its actual term and point in the tagged backend. -/
theorem backendT_virtual_seen (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (T : C.Term) (p : Point) (st : FullState C Tag)
    (r : Unit × FullState C Tag)
    (hr : r ∈ support ((shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.virtual T p))))).run st)) :
    (T, p) ∈ (dataOf x r.2).virtual := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run,
    ordinary, SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    compilerImpl, deferredImpl, map_pure] at hr
  subst r
  simp [dataOf, merged, splitRest, withCache]

/-- Sampling a chain pending answer allocates that precise pending input. -/
theorem freshPendingT_seen (noise : ChainNoiseIndex → HashOutput)
    (rest : RestSlot C → HashOutput) (edge : ChainNoiseIndex) (st : CappedCompilerState C)
    (r : DeferredOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshPending edge st))) :
    r.2.1.1.data.pending (chainPending edge) ≠ none := by
  cases hp : st.1.1.data.pending (chainPending edge) with
  | some v =>
    simp only [freshPending, hp, simulateQ_pure, mem_support_pure_iff] at hr
    subst r
    simpa only [incrementCompilerCount] using (by simp [hp] : st.1.1.data.pending (chainPending edge) ≠ none)
  | none =>
    simp only [freshPending, hp, simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, resolvePrivateTable,
      Sum.elim_inl, simulateQ_pure, pure_bind, mem_support_pure_iff] at hr
    subst r
    simp

/-- The bottom-chain pending query allocates its exact row in the merged data. -/
theorem backendT_bottom_seen (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep) (st : FullState C Tag)
    (r : DeferredOutput × FullState C Tag)
    (hr : r ∈ support ((shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.pending (.bottom e l d)))))).run st)) :
    (dataOf x r.2).pending (.bottom e l d) ≠ none := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, simulateQ_pure, StateT.run, mem_support_bind_iff,
    mem_support_pure_iff] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  simpa [dataOf, merged, splitRest, withCache, chainPending] using
    freshPendingT_seen noise rest (l, .inl e, d) _ a ha

/-- Recording a concrete hash answer allocates the specified pending input. -/
theorem backendT_record_seen (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : PendingInput) (value : HashOutput) (st : FullState C Tag)
    (r : Unit × FullState C Tag)
    (hr : r ∈ support ((shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.record p value))))).run st)) :
    (dataOf x r.2).pending p ≠ none := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run,
    ordinary, SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    compilerImpl, deferredImpl, map_pure] at hr
  subst r
  simp [dataOf, merged, splitRest, withCache]

/-- A source chain virtual call establishes its actual term row. -/
theorem sourceVirtualX_chain_seen (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (T : C.Term) (lay : Layer) (e : KeyIndex) (l : ChainIndex) (d : Digit)
    (src : SourceState C) (st : FullState C Tag)
    (r : (Unit × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceVirtualX x.1 x.2.1 T (.chain lay e l d)) src st)) :
    (T, .chain lay e l d) ∈ (dataOf x r.2).virtual := by
  simp only [sourceVirtualX, runX_bind, runX_deferred, mem_support_bind_iff,
    support_map, runX_pure, mem_support_pure_iff] at hr
  obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hr
  exact backendT_virtual_seen tagOf x q s pads τ g noise rest T _ st a ha

/-- A bottom pending source call allocates its row in either cache branch. -/
theorem sourcePendingX_bottom_seen (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep)
    (src : SourceState C) (st : FullState C Tag)
    (r : (DeferredOutput × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourcePendingX x.1 (.bottom e l d)) src st)) :
    (dataOf x r.2).pending (.bottom e l d) ≠ none := by
  simp only [sourcePendingX, runX_bind, runX_get, pure_bind] at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨a, _, hr⟩ := hr
  cases hp : a.1.1 <;> cases hk : a.1.2.revealed (PendingInput.bottom e l d).key <;>
    cases hn : (PendingInput.bottom e l d).next <;>
    simp only [hp, hk, hn] at hr
  all_goals
    simp only [Option.isNone_none, Option.isNone_some, Option.isSome_none,
      Option.isSome_some, Bool.and_false,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte, runX_bind, runX_modify,
      runX_pure, pure_bind, runX_deferred, support_map, mem_support_bind_iff,
      mem_support_pure_iff] at hr
  all_goals
    first
    | obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hr
      exact backendT_bottom_seen tagOf x q s pads τ g noise rest e l d _ a ha
    | obtain ⟨_, ⟨a, _, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact backendT_record_seen tagOf x q s pads τ g noise rest _ _ _ b hb

/-- Sequential source operations retain every property established by a member,
provided that the property is preserved by intervening source computations.
Port of `runSource_mapM_cached`, with its cache-specific invariant abstracted. -/
theorem runX_mapM_seen {α β : Type}
    (B : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (items : List α) (oa : α → SourceMX C β) (seen : α → FullState C Tag → Prop)
    (keep : ∀ a (oa : SourceMX C (List β)) src st r,
      r ∈ support (runX B oa src st) → seen a st → seen a r.2)
    (step : ∀ a ∈ items, ∀ src st r,
      r ∈ support (runX B (oa a) src st) → seen a r.2)
    (src : SourceState C) (st : FullState C Tag)
    (r : (List β × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX B (items.mapM oa) src st)) :
    ∀ a ∈ items, seen a r.2 := by
  induction items generalizing src st r with
  | nil => simp
  | cons a items ih =>
    simp only [List.mapM_cons, runX_bind, mem_support_bind_iff] at hr
    obtain ⟨head, hhead, tail, htail, hr⟩ := hr
    rw [runX_pure, mem_support_pure_iff] at hr
    subst r
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact keep b (items.mapM oa) head.1.2 head.2 tail htail (step b (List.mem_cons_self ..) _ _ _ hhead)
    · exact ih (fun a ha => step a (List.mem_cons_of_mem _ ha)) _ _ _ htail b hb

/-- The source interpreter preserves the exact row schedule of the backend. -/
theorem sourceBottomRowX_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) :
    sourceBottomRowX P seeds e l = (do
      let _ ← (bottomRowPrfCalls C e l).mapM fun q => do
        let _ ← sourceBackendX P seeds q
        pure ()
      let cpk₁ ← liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l (digit 1))))
      let cpk₂ ← liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l (digit 2))))
      let outputs : List DeferredOutput ← (bottomRowCalls e l).mapM (sourcePendingX P)
      pure (cpk₁, cpk₂, match outputs.getLast?.map (fun a : DeferredOutput => a.low) with
        | some (DeferredDigest.known value) => value
        | _ => 0)) := by
  simp [sourceBottomRowX, deferredBottomRow, simulateQ_list_mapM, backendQuery,
    sourceBackendX]
  rfl

/-- The complete bottom row establishes all three virtual and pending positions. -/
theorem sourceBottomRowX_rows (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (src : SourceState C) (st : FullState C Tag)
    (r : ((Digest × Digest × Digest) × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceBottomRowX x.1 x.2.1 e l) src st)) :
    ∀ d : XmssSecurity.ChainStep,
      (∀ T, (T, .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit d)) ∈
        (dataOf x r.2).virtual) ∧
      (dataOf x r.2).pending (.bottom e l d) ≠ none := by
  simp only [sourceBottomRowX_eq, runX_bind, mem_support_bind_iff,
    runX_pure, mem_support_pure_iff] at hr
  obtain ⟨v, hv, p₁, hp₁, p₂, hp₂, ps, hps, rfl⟩ := hr
  have virtuals := runX_mapM_seen (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) (bottomRowPrfCalls C e l)
    (fun query => do let _ ← sourceBackendX x.1 x.2.1 query; pure ())
    (fun query st => ∀ T p, query = .virtual T p → (T, p) ∈ (dataOf x st).virtual)
    (by
      intro query oa src st r hr h T p he
      exact (runX_rows tagOf x q s pads τ g noise rest oa src st r hr).1 (h T p he))
    (by
      intro query hquery src st r hr
      simp only [bottomRowPrfCalls, List.mem_flatMap, List.mem_map] at hquery
      obtain ⟨d, _, T, _, rfl⟩ := hquery
      simp only [sourceBackendX, runX_bind, runX_pure, mem_support_bind_iff,
        mem_support_pure_iff] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      intro U p he
      cases he
      exact sourceVirtualX_chain_seen tagOf x q s pads τ g noise rest T _ e l d src st a ha)
    src st v hv
  have pendings := runX_mapM_seen (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) (bottomRowCalls e l) (sourcePendingX x.1)
    (fun p st => (dataOf x st).pending p ≠ none)
    (by
      intro p oa src st r hr h
      exact (runX_rows tagOf x q s pads τ g noise rest oa src st r hr).2 p h)
    (by
      intro p hp src st r hr
      simp only [bottomRowCalls, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact sourcePendingX_bottom_seen tagOf x q s pads τ g noise rest e l _ src st r hr)
    p₂.1.2 p₂.2 ps hps
  intro d
  constructor
  · intro T
    have hm : (DeferredQuery.virtual T (.chain bottomLayer e l
        (XmssSecurity.CappedChain.chainStepDigit d))) ∈ bottomRowPrfCalls C e l := by
      simp only [bottomRowPrfCalls, List.mem_flatMap, List.mem_map]
      refine ⟨_, ?_, T, ?_, rfl⟩
      · fin_cases d <;> simp [XmssSecurity.CappedChain.chainStepDigit, digit]
      · simp [Committee.terms]
    have h := virtuals _ hm T _ rfl
    exact (runX_rows tagOf x q s pads τ g noise rest _ _ _ ps hps).1
      ((runX_rows tagOf x q s pads τ g noise rest _ _ _ p₂ hp₂).1
      ((runX_rows tagOf x q s pads τ g noise rest _ _ _ p₁ hp₁).1 h))
  · apply pendings
    fin_cases d <;> simp [bottomRowCalls]

/-- Every bottom build, including a failed search, establishes its full row domain. -/
theorem sourceBottomTreeX_rows (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) (src : SourceState C) (st : FullState C Tag)
    (r : (Option DeferredBottomTree × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceBottomTreeX x.1 x.2.1 top b) src st)) :
    ∀ k l (d : XmssSecurity.ChainStep),
      (∀ T, (T, .chain bottomLayer (bottomKey b k) l
        (XmssSecurity.CappedChain.chainStepDigit d)) ∈ (dataOf x r.2).virtual) ∧
      (dataOf x r.2).pending (.bottom (bottomKey b k) l d) ≠ none := by
  unfold sourceBottomTreeX at hr
  rw [runX_bind, mem_support_bind_iff] at hr
  obtain ⟨rows, hrows, hr⟩ := hr
  have established := runX_mapM_seen
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
    ((List.finRange (2 ^ layerHeight)).flatMap fun k =>
      (List.finRange numChains).map fun l => (bottomKey b k, l))
    (fun el => sourceBottomRowX x.1 x.2.1 el.1 el.2)
    (fun el st => ∀ d : XmssSecurity.ChainStep,
      (∀ T, (T, .chain bottomLayer el.1 el.2
        (XmssSecurity.CappedChain.chainStepDigit d)) ∈ (dataOf x st).virtual) ∧
      (dataOf x st).pending (.bottom el.1 el.2 d) ≠ none)
    (by
      intro el oa src st r hr h d
      have hm := runX_rows tagOf x q s pads τ g noise rest oa src st r hr
      exact ⟨fun T => hm.1 ((h d).1 T), hm.2 _ (h d).2⟩)
    (fun el _ src st r hr => sourceBottomRowX_rows tagOf x q s pads τ g noise rest
      el.1 el.2 src st r hr) src st rows hrows
  intro k l d
  have hm : (bottomKey b k, l) ∈ ((List.finRange (2 ^ layerHeight)).flatMap fun k =>
      (List.finRange numChains).map fun l => (bottomKey b k, l)) := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨k, List.mem_finRange k, l, List.mem_finRange l, rfl⟩
  have h := established _ hm d
  have keep := runX_rows tagOf x q s pads τ g noise rest _ _ _ r hr
  exact ⟨fun T => keep.1 (h.1 T), keep.2 _ h.2⟩

/-- The row domain attached to one stored bottom tree. -/
def BottomRows (x : Keys3 C) (b : XmssSecurity.TopIndex) (st : FullState C Tag) : Prop :=
  ∀ k l (d : XmssSecurity.ChainStep),
    (∀ T, (T, .chain bottomLayer (bottomKey b k) l
      (XmssSecurity.CappedChain.chainStepDigit d)) ∈ (dataOf x st).virtual) ∧
    (dataOf x st).pending (.bottom (bottomKey b k) l d) ≠ none

/-- D17 either retains the stored row domain or establishes it with the first build. -/
theorem sourceBottomOnceX_rows (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) (src : SourceState C) (st : FullState C Tag)
    (stored : src.trees b ≠ none → BottomRows x b st)
    (r : (Option DeferredBottomTree × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceBottomOnceX x.1 x.2.1 top b) src st)) :
    BottomRows x b r.2 := by
  simp only [sourceBottomOnceX, runX_bind, runX_get, pure_bind] at hr
  cases ht : src.trees b with
  | some tree =>
    simp only [ht, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact stored (by simp [ht])
  | none =>
    simp only [ht, runX_bind, runX_modify, runX_pure, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    exact sourceBottomTreeX_rows tagOf x q s pads τ g noise rest top b src st a ha

end ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.runX_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.runX_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.backendT_virtual_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.backendT_virtual_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.freshPendingT_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.freshPendingT_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.backendT_bottom_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.backendT_bottom_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.backendT_record_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.backendT_record_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceVirtualX_chain_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceVirtualX_chain_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourcePendingX_bottom_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourcePendingX_bottom_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.runX_mapM_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.runX_mapM_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomRowX_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomRowX_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomRowX_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomRowX_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomTreeX_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomTreeX_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomOnceX_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeRows.sourceBottomOnceX_rows
