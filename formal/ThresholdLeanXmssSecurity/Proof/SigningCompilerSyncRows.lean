import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncChain

/-! # Monotonicity of compiler virtual rows and pending domains -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncRows
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncChain
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false

/-- Virtual-row version of deferredImpl_pending_mono. -/
theorem deferredImpl_virtual_mono (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) : st.virtual ⊆ r.2.virtual := by
  cases t with
  | hash query =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact Finset.Subset.refl _
  | pending key =>
      cases hk : st.pending key
      · simp only [deferredImpl, StateT.run, hk, support_map] at hr
        obtain ⟨a, _, rfl⟩ := hr
        exact Finset.Subset.refl _
      · simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
        subst r
        exact Finset.Subset.refl _
  | pad point =>
      cases hk : st.pads point
      · simp only [deferredImpl, StateT.run, hk, support_map] at hr
        obtain ⟨a, _, rfl⟩ := hr
        exact Finset.Subset.refl _
      · simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
        subst r
        exact Finset.Subset.refl _
  | plant input value =>
      cases hc : st.cache input.query <;>
        simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr <;>
        subst r <;> exact Finset.Subset.refl _
  | sample | uniform _ =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact Finset.Subset.refl _
  | virtual term point =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact Finset.subset_insert _ _
  | record _ _ | inspect _ | snapshot | bindKey _ _ =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact Finset.Subset.refl _

/-- The cached-extra wrapper changes neither virtual rows nor their monotonicity. -/
theorem compilerImpl_virtual_mono (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) :
    st.data.virtual ⊆ r.2.data.virtual := by
  cases t with
  | hash query =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, _, rfl⟩ := hr
      exact deferredImpl_virtual_mono (.hash query) st.data a ha
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact Finset.Subset.refl _
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_virtual_mono _ st.data a ha

/-- The count/reveal cap does not remove virtual rows. -/
theorem cappedCompiler_virtual_mono (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) :
    backend.1.1.data.virtual ⊆ r.2.1.1.data.virtual := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_virtual_mono P seeds t backend.1.1 b hb
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      exact Finset.Subset.refl _

/-- Fixed pads preserve virtual rows just as the counted backend does. -/
theorem ordinary_virtual_mono (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinary P seeds q s pads t st)) :
    st.1.1.data.virtual ⊆ r.2.1.1.data.virtual := by
  have cap (t : DeferredQuery C ⊕ HiddenKey)
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
      (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run st)) :
      st.1.1.data.virtual ⊆ r.2.1.1.data.virtual :=
    cappedCompiler_virtual_mono P seeds q s t st r hr
  cases t with
  | inr k => exact cap (.inr k) r hr
  | inl t =>
    cases t with
    | pad p =>
      cases hp : st.1.1.data.pads p <;>
        simp only [ordinary, padStep, hp, mem_support_pure_iff] at hr <;>
        subst r <;> exact Finset.Subset.refl _
    | _ => exact cap _ r hr

/-- Cached-extra calls update the cache and trace, not the virtual-row set. -/
theorem hashTail_virtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : Query C) (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (hashTail P seeds input st value cache)) :
    r.2.1.1.data.virtual = st.1.1.data.virtual := by
  simp only [hashTail, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  rfl

attribute [local irreducible] hashTail

/-- Sampling a fixed pending answer retains all old rows and pending entries. -/
theorem freshPendingT_rows (noise : ChainNoiseIndex → HashOutput)
    (rest : RestSlot C → HashOutput) (edge : ChainNoiseIndex) (st : CappedCompilerState C)
    (r : DeferredOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshPending edge st))) :
    st.1.1.data.virtual ⊆ r.2.1.1.data.virtual ∧
      ∀ p, st.1.1.data.pending p ≠ none → r.2.1.1.data.pending p ≠ none := by
  cases hp : st.1.1.data.pending (chainPending edge) with
  | some v =>
    simp only [freshPending, hp, simulateQ_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨Finset.Subset.refl _, fun _ h => h⟩
  | none =>
    simp only [freshPending, hp, simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, resolvePrivateTable,
      Sum.elim_inl, simulateQ_pure, pure_bind, mem_support_pure_iff] at hr
    subst r
    refine ⟨Finset.Subset.refl _, ?_⟩
    intro p h
    by_cases he : p = chainPending edge
    · subst p
      simp
    · simpa [Function.update_of_ne he] using h

/-- Reading a fixed rest slot retains all old rows and pending entries. -/
theorem freshRestT_rows (x : Keys3 C) (noise : ChainNoiseIndex → HashOutput)
    (rest : RestSlot C → HashOutput) (z : RestSlot C) (st : CappedCompilerState C)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshRest x.1 x.2.1 x.2.2 z st))) :
    st.1.1.data.virtual ⊆ r.2.1.1.data.virtual ∧
      ∀ p, st.1.1.data.pending p ≠ none → r.2.1.1.data.pending p ≠ none := by
  rw [freshRestT_run] at hr
  cases hc : st.1.1.data.cache (restInput x.2.1 x.2.2 z) <;> rw [hc] at hr
  all_goals
    have hv := hashTail_virtual x.1 x.2.1 _ st _ _ r hr
    have hp := (hashTail_grows x.1 x.2.1 _ st _ _ r hr).2
    constructor
    · rw [hv]
    · intro p h
      rwa [hp]

/-- Every fixed-table ordinary query preserves virtual and pending domains. -/
theorem ordinaryT_rows (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinaryT x.1 x.2.1 x.2.2 q s pads noise rest t st)) :
    st.1.1.data.virtual ⊆ r.2.1.1.data.virtual ∧
      ∀ p, st.1.1.data.pending p ≠ none → r.2.1.1.data.pending p ≠ none := by
  have plain (t : DeferredQuery C ⊕ HiddenKey)
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
      (hr : r ∈ support (ordinary x.1 x.2.1 q s pads t st)) :=
    And.intro (ordinary_virtual_mono x.1 x.2.1 q s pads t st r hr)
      (ordinary_grows x.1 x.2.1 q s pads t st r hr).2
  cases t with
  | inr k =>
    simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
    exact plain _ r hr
  | inl t =>
    cases t with
    | hash input =>
      simp only [ordinaryT, ordinaryRaw] at hr
      cases hz : restRoute x.2.1 x.2.2 input with
      | some z =>
        simp only [hz] at hr
        exact freshRestT_rows x noise rest z st r hr
      | none =>
        simp only [hz, resolvePrivateTable_lift] at hr
        exact plain _ r hr
    | pending p =>
      cases p with
      | bottom e l p => exact freshPendingT_rows noise rest _ st r hr
      | top b l p => exact freshPendingT_rows noise rest _ st r hr
      | _ =>
        simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
        exact plain _ r hr
    | _ =>
      simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
      exact plain _ r hr

/-- No query of the tagged backend removes an allocated row or pending entry. -/
theorem backendT_rows (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SpecX C).Domain) (st : FullState C Tag)
    (r : SpecX C t × FullState C Tag)
    (hr : r ∈ support (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest t st)) :
    (dataOf x st).virtual ⊆ (dataOf x r.2).virtual ∧
      ∀ p, (dataOf x st).pending p ≠ none → (dataOf x r.2).pending p ≠ none := by
  apply backendT_preserves (fun _ => True) tagOf x q s pads τ g noise rest
    (fun cs _ => st.1.1.1.1.data.virtual ⊆ cs.1.1.data.virtual ∧
      ∀ p, st.1.1.1.1.data.pending p ≠ none → cs.1.1.data.pending p ≠ none)
    ?_ ?_ ?_ t trivial st ⟨Finset.Subset.refl _, fun _ h => h⟩ r hr
  · intro t ht cs sh h r hr
    have hh := ordinaryT_rows x q s pads noise rest t (merged x.2.1 cs sh.cache) r hr
    exact ⟨h.1.trans hh.1, fun p hp => hh.2 p (h.2 p hp)⟩
  · intro cs sh h T p tag a ha r hr
    have hv := hashTail_virtual x.1 x.2.1 _ _ _ _ r hr
    have hp := (hashTail_grows x.1 x.2.1 _ _ _ _ r hr).2
    change st.1.1.1.1.data.virtual ⊆ r.2.1.1.data.virtual ∧
      ∀ p, st.1.1.1.1.data.pending p ≠ none → r.2.1.1.data.pending p ≠ none
    constructor
    · rw [hv]
      exact h.1
    · intro p hq
      rw [hp]
      exact h.2 p hq
  · intro cs sh h p target tag a ha
    exact h

/-- Arbitrary adaptive compiled programs preserve the two allocated domains. -/
theorem simulate_rows {α : Type}
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (oa : OracleComp (SpecX C) α) (st : FullState C Tag)
    (r : α × FullState C Tag)
    (hr : r ∈ support ((simulateQ
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) oa).run st)) :
    (dataOf x st).virtual ⊆ (dataOf x r.2).virtual ∧
      ∀ p, (dataOf x st).pending p ≠ none → (dataOf x r.2).pending p ≠ none := by
  apply simulateQ_sticky _ (fun fs => (dataOf x st).virtual ⊆ (dataOf x fs).virtual ∧
      ∀ p, (dataOf x st).pending p ≠ none → (dataOf x fs).pending p ≠ none)
    ?_ oa st ⟨Finset.Subset.refl _, fun _ h => h⟩ r hr
  intro t before h next hn
  have hs := backendT_rows tagOf x q s pads τ g noise rest t before next hn
  exact ⟨h.1.trans hs.1, fun p hp => hs.2 p (h.2 p hp)⟩

end ThresholdLeanXmssSecurity.SigningCompilerSyncRows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.deferredImpl_virtual_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.deferredImpl_virtual_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.compilerImpl_virtual_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.compilerImpl_virtual_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.cappedCompiler_virtual_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.cappedCompiler_virtual_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.ordinary_virtual_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.ordinary_virtual_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.hashTail_virtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.hashTail_virtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.freshPendingT_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.freshPendingT_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.freshRestT_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.freshRestT_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.ordinaryT_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.ordinaryT_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.backendT_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.backendT_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRows.simulate_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRows.simulate_rows
