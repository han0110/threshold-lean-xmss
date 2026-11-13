import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTables
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareSource

/-!
# Frames of the compiler's private tables

Free slots agree with their fixed table, share cells agree with their eager
table, and pending answers retain their symbolic next coordinate.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncFrame
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] hashTail

def RestAgree (x : Keys3 C) (rest : RestSlot C → HashOutput)
    (cs : CappedCompilerState C) : Prop :=
  ∀ z v, cs.1.1.data.cache (restInput x.2.1 x.2.2 z) = some v → v = rest z

def ShareG (g : C.Term × CPoint → HashOutput) (sh : ShareStateT C Tag) : Prop :=
  ∀ y v, sh.cache y = some v → v = g y

/-- Mask sibling of SigningPartnerCompareProof.outsideTrials_prf. -/
theorem outsideTrials_mask (P : PublicParameter) (seed : HashOutput) (point : Point)
    (message : Message) (J : C.Quorum) :
    SigningPartnerCompareProof.OutsideTrials P (.mask seed point message J : Query C) :=
  ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩

def WritesMask (seed : HashOutput) (point : Point) (message : Message) (J : C.Quorum) : DeferredQuery C → Prop
  | .hash query => query = .mask seed point message J
  | .plant input _ => input.query (C := C) = .mask seed point message J
  | _ => False

/-- Deferred backend calls frame every mask entry they do not address. Pending
plants address the hash domain and therefore cannot change a mask entry. -/
theorem deferredImpl_mask_frame (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) (seed : HashOutput) (point : Point) (message : Message) (J : C.Quorum)
    (ht : ¬WritesMask seed point message J t) :
    r.2.cache (.mask seed point message J) = st.cache (.mask seed point message J) := by
  cases t with
  | hash query =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact (randomOracle_support query st.cache a ha).2.2 (.mask seed point message J) (Ne.symm (show query ≠ .mask seed point message J from ht))
  | pending key =>
      cases hk : st.pending key with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          rfl
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          rfl
  | pad p =>
      cases hk : st.pads p with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          rfl
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          rfl
  | plant input value =>
      cases hc : st.cache input.query with
      | some prior =>
          simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr
          subst r
          rfl
      | none =>
          simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr
          subst r
          exact QueryCache.cacheQuery_of_ne _ _
            (Ne.symm (show input.query (C := C) ≠ .mask seed point message J from ht))
  | sample =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | virtual term p =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | inspect p =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | snapshot =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | record p value =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | bindKey e message =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual cached-extra grind adds only trial hashes, so the full compiler
has the same exact mask frame as its deferred backend. -/
theorem compilerImpl_mask_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) (seed : HashOutput) (point : Point) (message : Message) (J : C.Quorum)
    (ht : ¬WritesMask seed point message J t) :
    r.2.data.cache (.mask seed point message J) = st.data.cache (.mask seed point message J) := by
  cases t with
  | hash query =>
      obtain ⟨a, ha, b, hb, rfl⟩ := SigningCompilerPotential.compiler_hash_support
        P seeds query st r hr
      have frame := SigningReleasedTransferProof.cachedExtra_frame seeds P
        (((st.data.cache, 0), []), compilerSigning st, false)
        (.inr (.inr (.inl query)))
        (((a.2.cache, 0), []), compilerSigning st, false) b (by
          dsimp only [StateT.run] at hb ⊢
          with_reducible exact hb)
      exact (frame.2 (.mask seed point message J)
        (outsideTrials_mask P seed point message J)).trans
          (deferredImpl_mask_frame (.hash query) st.data a ha seed point message J ht)
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_mask_frame _ st.data a ha seed point message J ht

def SourceWritesMask (seed : HashOutput) (point : Point) (message : Message) (J : C.Quorum) : DeferredQuery C ⊕ HiddenKey → Prop
  | .inl t => WritesMask seed point message J t
  | .inr _ => False

/-- Reveals and counter updates preserve the same concrete mask cache frame. -/
theorem cappedCompiler_mask_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))
    (seed : HashOutput) (point : Point) (message : Message) (J : C.Quorum) (ht : ¬SourceWritesMask seed point message J t) :
    r.2.1.1.data.cache (.mask seed point message J) = backend.1.1.data.cache (.mask seed point message J) := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_mask_frame P seeds t backend.1.1 b hb seed point message J ht
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      rfl


/-- Mask port of SigningCompilerShare.hashTail_frame. -/
theorem hashTail_mask_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (query : Query C) (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C)
    (result : HashOutput × CappedCompilerState C)
    (hr : result ∈ support (hashTail P seeds query st value cache))
    (seed : HashOutput) (p : Point) (message : Message) (J : C.Quorum) :
    result.2.1.1.data.cache (.mask seed p message J) = cache (.mask seed p message J) := by
  simp only [hashTail, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨prefetched, hp, rfl⟩ := hr
  have frame := SigningReleasedTransferProof.cachedExtra_frame seeds P
    (((st.1.1.data.cache, 0), []), compilerSigning st.1.1, false)
    (.inr (.inr (.inl query))) (((cache, 0), []), compilerSigning st.1.1, false)
    prefetched (by
      dsimp only [StateT.run] at hp ⊢
      with_reducible exact hp)
  exact frame.2 (.mask seed p message J) (outsideTrials_mask P seed p message J)


/-- The cached trial suffix cannot write any free slot. -/
theorem hashTail_rest_frame (x : Keys3 C) (input : Query C)
    (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (hashTail x.1 x.2.1 input st value cache)) (z : RestSlot C) :
    r.2.1.1.data.cache (restInput x.2.1 x.2.2 z) = cache (restInput x.2.1 x.2.2 z) := by
  rcases z with ⟨(⟨T, p⟩ | ⟨pair, p, m, J⟩), hz⟩
  · exact hashTail_frame x.1 x.2.1 input st value cache r hr _ _
  · exact hashTail_mask_frame x.1 x.2.1 input st value cache r hr _ _ _ _

section Eager
open SigningShareLazy
variable {κ ι B : Type} [DecidableEq κ] [DecidableEq ι]

/-- Port of private SigningShareLazy.fillTerms_agree (1492). -/
theorem fillTerms_agree (g : κ × ι → SigningShareLazy.HashOutput) (p : ι) (todo : List κ)
    (st : ShareState κ ι B) (h : ∀ y v, st.cache y = some v → g y = v) :
    ∀ st' ∈ support (fillTerms (fun y => pure (g y)) p todo st),
      ∀ y v, st'.cache y = some v → g y = v := by
  induction todo generalizing st with
  | nil =>
      intro st' hs
      have he : st' = st := by simpa [fillTerms] using hs
      subst st'
      exact h
  | cons a todo ih =>
      intro st' hs
      change st' ∈ support (fillTerm (fun y => pure (g y)) p a st >>=
        fillTerms (fun y => pure (g y)) p todo) at hs
      obtain ⟨mid, hm, hs⟩ := mem_support_bind_peel _ _ hs
      apply ih mid _ st' hs
      cases hc : st.cache (a, p) with
      | some v =>
          have he : mid = st := by simpa [SigningShareLazy.fillTerm, hc] using hm
          subst mid
          exact h
      | none =>
          have he : mid = put st a p (g (a, p)) := by simpa [SigningShareLazy.fillTerm, hc] using hm
          subst mid
          intro y v hv
          by_cases hy : y = (a, p)
          · subst y
            simpa [put] using hv
          · exact h y v (by simpa [put, Function.update, hy] using hv)

end Eager

theorem shareG_put (g : C.Term × CPoint → HashOutput) (sh : ShareStateT C Tag)
    (h : ShareG g sh) (T : C.Term) (p : CPoint) :
    ShareG g (SigningShareLazy.put sh T p (g (T, p))) := by
  intro y v hv
  by_cases hy : y = (T, p)
  · subst y; simpa [SigningShareLazy.put] using hv.symm
  · exact h y v (by simpa [SigningShareLazy.put, Function.update, hy] using hv)

theorem eagerImpl_shareG (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : SigningShareLazy.ShareQuery C.Term CPoint Tag) (sh : ShareStateT C Tag)
    (h : ShareG g sh) (r : SigningShareLazy.ShareSpec C.Term CPoint Tag t × ShareStateT C Tag)
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g t).run sh)) :
    ShareG g r.2 := by
  cases t with
  | read T p tag =>
    cases hc : sh.cache (T, p) <;>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, hc,
        StateT.run, pure_bind, mem_support_pure_iff] at hr <;> subst r
    · exact shareG_put g sh h T p
    · exact h
  | complete p target tag =>
    simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run] at hr
    split at hr
    · simp only [mem_support_pure_iff] at hr; subst r; exact h
    · cases hs : SigningShareLazy.slack C.terms sh p with
      | none =>
        simp only [hs, mem_support_pure_iff] at hr; subst r; exact h
      | some T =>
        simp only [hs, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨mid, hm, rfl⟩ := hr
        apply shareG_put g mid _ T p
        exact fun y v hv => (fillTerms_agree g p _ sh (fun y v hv => (h y v hv).symm)
          mid hm y v hv).symm
  | view =>
    simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      mem_support_pure_iff] at hr
    subst r; exact h

/-- The fixed-pad variant preserves the same mask frame. -/
theorem ordinary_mask_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinary P seeds q s pads t st))
    (seed : HashOutput) (p : Point) (message : Message) (J : C.Quorum)
    (ht : ¬SourceWritesMask seed p message J t) :
    r.2.1.1.data.cache (.mask seed p message J) = st.1.1.data.cache (.mask seed p message J) := by
  cases t with
  | inr k => exact cappedCompiler_mask_frame P seeds q s (.inr k) st r hr seed p message J ht
  | inl t =>
    cases t with
    | pad point =>
      cases hp : st.1.1.data.pads point <;>
        simp only [ordinary, padStep, hp, mem_support_pure_iff] at hr <;> subst r <;> rfl
    | _ => exact cappedCompiler_mask_frame P seeds q s _ st r hr seed p message J ht

def OrdinaryAllowed (t : DeferredQuery C ⊕ HiddenKey) : Prop :=
  match t with | .inl t => DeferredAllowed t | .inr _ => True

/-- Free cells are framed by an ordinary call which does not read any of them. -/
theorem ordinary_rest_frame (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (ha : OrdinaryAllowed t)
    (hn : ∀ input, t = .inl (.hash input) → restRoute x.2.1 x.2.2 input = none)
    (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinary x.1 x.2.1 q s pads t st)) (z : RestSlot C) :
    r.2.1.1.data.cache (restInput x.2.1 x.2.2 z) = st.1.1.data.cache (restInput x.2.1 x.2.2 z) := by
  have no_read : ∀ input, t = .inl (.hash input) → input ≠ restInput x.2.1 x.2.2 z := by
    intro input ht he
    have hh := hn input ht
    unfold restRoute at hh
    split at hh
    · cases hh
    · next h => exact h ⟨z, he.symm⟩
  rcases z with ⟨(⟨T, p⟩ | ⟨pair, p, m, J⟩), hz⟩
  · apply ordinary_prf_frame x.1 x.2.1 q s pads t st r hr
    cases t with
    | inr k => simp [SourceWritesPrf]
    | inl t =>
      cases t <;> simp only [SourceWritesPrf, WritesPrf, not_false_eq_true]
      · exact no_read _ rfl
      · rename_i input value
        cases input with
        | prf T p => exact ha.elim
        | pending p value => intro h; cases h
  · apply ordinary_mask_frame x.1 x.2.1 q s pads t st r hr
    cases t with
    | inr k => simp [SourceWritesMask]
    | inl t =>
      cases t <;> simp only [SourceWritesMask, WritesMask, not_false_eq_true]
      · exact no_read _ rfl
      · rename_i input value
        cases input <;> intro h <;> cases h

theorem ordinary_pendingValid (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (h : PendingValid st.1.1.data)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinary P seeds q s pads t st)) : PendingValid r.2.1.1.data := by
  cases t with
  | inr k =>
    simp only [ordinary, SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
      mem_support_pure_iff] at hr
    subst r; exact h
  | inl t =>
    cases t with
    | pad point =>
      cases hp : st.1.1.data.pads point <;>
        simp only [ordinary, padStep, hp, mem_support_pure_iff] at hr <;> subst r <;> exact h
    | _ =>
      simp only [ordinary, SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_pendingValid P seeds _ st.1.1 h b hb

@[simp] theorem restAgree_merged (x : Keys3 C) (rest : RestSlot C → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (cs : CappedCompilerState C) (sh : ShareCache C) :
    RestAgree x rest (merged x.2.1 cs sh) ↔ RestAgree x rest cs := by
  simp only [RestAgree, merged, withCache, merge_rest x.2.1 x.2.2 hi]

@[simp] theorem restAgree_split (x : Keys3 C) (rest : RestSlot C → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (cs : CappedCompilerState C) :
    RestAgree x rest (splitRest x.2.1 cs) ↔ RestAgree x rest cs := by
  simp only [RestAgree, splitRest, withCache, erase_rest x.2.1 x.2.2 hi]

@[simp] theorem mergedPendingValid (seeds : C.Term → HashOutput)
    (cs : CappedCompilerState C) (sh : ShareCache C) :
    PendingValid (merged seeds cs sh).1.1.data ↔ PendingValid cs.1.1.data := Iff.rfl

@[simp] theorem splitPendingValid (seeds : C.Term → HashOutput) (cs : CappedCompilerState C) :
    PendingValid (splitRest seeds cs).1.1.data ↔ PendingValid cs.1.1.data := Iff.rfl

/-- Fixed-table resolution of a free-slot read. -/
theorem freshRestT_run (x : Keys3 C) (noise : ChainNoiseIndex → HashOutput)
    (rest : RestSlot C → HashOutput) (z : RestSlot C) (st : CappedCompilerState C) :
    simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshRest x.1 x.2.1 x.2.2 z st) =
      match st.1.1.data.cache (restInput x.2.1 x.2.2 z) with
      | some v => hashTail x.1 x.2.1 (restInput x.2.1 x.2.2 z) st v st.1.1.data.cache
      | none => hashTail x.1 x.2.1 (restInput x.2.1 x.2.2 z) st (rest z)
          (st.1.1.data.cache.cacheQuery (restInput x.2.1 x.2.2 z) (rest z)) := by
  cases hc : st.1.1.data.cache (restInput x.2.1 x.2.2 z) <;>
    simp only [freshRest, hc, pure_bind, simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, resolvePrivateTable, Sum.elim_inr, resolvePrivateTable_lift]

/-- Free reads preserve agreement with their fixed table. -/
theorem freshRestT_restAgree (x : Keys3 C)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (z : RestSlot C) (st : CappedCompilerState C) (h : RestAgree x rest st)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshRest x.1 x.2.1 x.2.2 z st))) : RestAgree x rest r.2 := by
  rw [freshRestT_run] at hr
  cases hc : st.1.1.data.cache (restInput x.2.1 x.2.2 z) with
  | some v =>
    rw [hc] at hr
    intro w v hv
    exact h w v ((hashTail_rest_frame x _ st _ _ r hr w) ▸ hv)
  | none =>
    rw [hc] at hr
    intro w v hv
    rw [hashTail_rest_frame x _ st _ _ r hr w] at hv
    by_cases hw : w = z
    · subst w; simpa using hv.symm
    · rw [QueryCache.cacheQuery_of_ne _ _
        (fun he => hw (restInput_injective x.2.1 x.2.2 hi he))] at hv
      exact h w v hv

/-- Pending reads leave every free cell unchanged. -/
theorem freshPendingT_restAgree (x : Keys3 C) (noise : ChainNoiseIndex → HashOutput)
    (rest : RestSlot C → HashOutput) (edge : ChainNoiseIndex) (st : CappedCompilerState C)
    (h : RestAgree x rest st)
    (r : DeferredOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshPending edge st))) :
    RestAgree x rest r.2 := by
  cases hp : st.1.1.data.pending (chainPending edge) with
  | some v =>
    simp only [freshPending, hp, simulateQ_pure, mem_support_pure_iff] at hr
    subst r; exact h
  | none =>
    simp only [freshPending, hp, simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, resolvePrivateTable, Sum.elim_inl, simulateQ_pure, pure_bind, mem_support_pure_iff] at hr
    subst r
    exact h

/-- Both parts of the ordinary private-table handler preserve the frame. -/
theorem ordinaryT_restAgree (x : Keys3 C)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : DeferredQuery C ⊕ HiddenKey)
    (ha : OrdinaryAllowed t)
    (st : CappedCompilerState C) (h : RestAgree x rest st)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinaryT x.1 x.2.1 x.2.2 q s pads noise rest t st)) :
    RestAgree x rest r.2 := by
  have ho (t : DeferredQuery C ⊕ HiddenKey)
      (ha : OrdinaryAllowed t)
      (hn : ∀ input, t = .inl (.hash input) → restRoute x.2.1 x.2.2 input = none)
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
      (hr : r ∈ support (ordinary x.1 x.2.1 q s pads t st)) :
      RestAgree x rest r.2 :=
    fun z v hv => h z v ((ordinary_rest_frame x q s pads t ha hn st r hr z) ▸ hv)
  cases t with
  | inr k =>
    simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
    exact ho (.inr k) ha (by intro a he; cases he) r hr
  | inl t =>
    cases t with
    | hash input =>
      simp only [ordinaryT, ordinaryRaw] at hr
      cases hz : restRoute x.2.1 x.2.2 input with
      | some z =>
        simp only [hz] at hr
        exact freshRestT_restAgree x hi noise rest z st h r hr
      | none =>
        simp only [hz, resolvePrivateTable_lift] at hr
        exact ho (.inl (.hash input)) ha (by intro a he; cases he; exact hz) r hr
    | pending p =>
      cases p with
      | bottom e l p => exact freshPendingT_restAgree x noise rest _ st h r hr
      | top b l p => exact freshPendingT_restAgree x noise rest _ st h r hr
      | _ =>
        simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
        exact ho _ ha (by intro a he; cases he) r hr
    | _ =>
      simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
      exact ho _ ha (by intro a he; cases he) r hr

attribute [local irreducible] ordinaryStepTag readStepTag eagerHandlerTag
  SigningShareLazy.eagerImpl ordinary ordinaryFullRaw eagerBackend

/-- A common invariant rule for the concrete table backend. -/
theorem backendT_preserves (permit : (SpecX C).Domain → Prop)
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (I : CappedCompilerState C → ShareStateT C Tag → Prop)
    (hord : ∀ t, permit (.inl (.inl t)) → ∀ cs sh, I cs sh →
      ∀ r ∈ support (ordinaryT x.1 x.2.1 x.2.2 q s pads noise rest t
        (merged x.2.1 cs sh.cache)), I (splitRest x.2.1 r.2) sh)
    (hread : ∀ cs sh, I cs sh → ∀ T p tag,
      ∀ a ∈ support ((SigningShareLazy.eagerImpl C.terms τ g (.read T p tag)).run sh),
      ∀ r ∈ support (hashTail x.1 x.2.1 (key x.2.1 (T, p))
        (merged x.2.1 cs sh.cache) a.1 (merge x.2.1 cs.1.1.data.cache a.2.cache)),
        I (splitRest x.2.1 r.2) a.2)
    (hcomplete : ∀ cs sh, I cs sh → ∀ p target tag,
      ∀ a ∈ support ((SigningShareLazy.eagerImpl C.terms τ g (.complete p target tag)).run sh),
        I cs a.2)
    (t : (SpecX C).Domain) (ht : permit t) (st : FullState C Tag) (h : I st.1.1 st.2)
    (r : SpecX C t × FullState C Tag)
    (hr : r ∈ support (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest t st)) :
    I r.2.1.1 r.2.2 := by
  have ho (t : DeferredQuery C ⊕ HiddenKey) (ht : permit (.inl (.inl t)))
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × FullState C Tag)
      (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
        (ordinaryFullRaw x.1 x.2.1 x.2.2 q s pads t st))) : I r.2.1.1 r.2.2 := by
    simp only [ordinaryFullRaw, simulateQ_bind, simulateQ_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    exact hord t ht st.1.1 st.2 h a ha
  rcases t with ((t | k) | mark) | ⟨p, target⟩
  · cases t with
    | hash input =>
      cases hrout : route x.2.1 input with
      | none =>
        simp only [shareBackendTagT, backendRaw, hrout] at hr
        exact ho (.inl (.hash input)) ht r hr
      | some z =>
        rcases z with ⟨T, p⟩
        simp only [shareBackendTagT, backendRaw, hrout, resolvePrivateTable_lift,
          eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        change r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ (eagerHandlerTag τ g) (readStepTag tagOf x.1 x.2.1 T p st.1)).run st.2) at hr
        rw [eager_read] at hr
        simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨a, ha, b, hb, rfl⟩ := hr
        exact hread st.1.1 st.2 h T p (tagOf st.1) a ha b hb
    | pending p =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.pending p)) ht r hr
    | virtual T p =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.virtual T p)) ht r hr
    | pad p =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.pad p)) ht r hr
    | inspect p =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.inspect p)) ht r hr
    | plant input value =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.plant input value)) ht r hr
    | snapshot =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.snapshot)) ht r hr
    | sample =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.sample)) ht r hr
    | record p value =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.record p value)) ht r hr
    | uniform n =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.uniform n)) ht r hr
    | bindKey e message =>
      simp only [shareBackendTagT, backendRaw] at hr
      exact ho (.inl (.bindKey e message)) ht r hr
  · simp only [shareBackendTagT, backendRaw] at hr
    exact ho (.inr k) ht r hr
  · simp only [shareBackendTagT, backendRaw, resolvePrivateTable_lift,
      eagerBackend, SigningCompilerUntil.fuse, StateT.run, shareBackendTag, simulateQ_pure] at hr
    subst r; exact h
  · by_cases hp : Constrained p
    · simp only [shareBackendTagT, backendRaw, resolvePrivateTable_lift,
        eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hp, dif_pos] at hr
      change r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (do
          let value ← shareQueryTag (.complete ⟨p, hp⟩ target (tagOf st.1))
          pure (value, st.1))).run st.2) at hr
      simp only [simulateQ_bind, StateT.run_bind, eager_share, simulateQ_pure,
        StateT.run_pure, map_bind, map_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact hcomplete st.1.1 st.2 h ⟨p, hp⟩ target (tagOf st.1) a ha
    · simp only [shareBackendTagT, backendRaw, resolvePrivateTable_lift,
        eagerBackend, SigningCompilerUntil.fuse, StateT.run, shareBackendTag, hp] at hr
      subst r; exact h

/-- All backend queries preserve agreement of share cells with their fixed table. -/
theorem backendT_shareG (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SpecX C).Domain) (st : FullState C Tag) (h : ShareG g st.2)
    (r : SpecX C t × FullState C Tag)
    (hr : r ∈ support (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest t st)) :
    ShareG g r.2.2 := by
  apply backendT_preserves (fun _ => True) tagOf x q s pads τ g noise rest
    (fun _ sh => ShareG g sh) ?_ ?_ ?_ t trivial st h r hr
  · intro t _ cs sh h r hr; exact h
  · intro cs sh h T p tag a ha r hr; exact eagerImpl_shareG τ g _ sh h a ha
  · intro cs sh h p target tag a ha; exact eagerImpl_shareG τ g _ sh h a ha

def Frame (x : Keys3 C) (rest : RestSlot C → HashOutput)
    (cs : CappedCompilerState C) : Prop :=
  RestAgree x rest cs ∧ RestFree x.2.1 cs.1.1.data.cache ∧ PendingValid cs.1.1.data

/-- Allowed queries preserve free-slot agreement and the disjoint cache domain. -/
theorem backendT_restFrame (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SpecX C).Domain) (ht : Allowed t) (st : FullState C Tag)
    (h : RestAgree x rest st.1.1 ∧ RestFree x.2.1 st.1.1.1.1.data.cache) (r : SpecX C t × FullState C Tag)
    (hr : r ∈ support (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest t st)) :
    RestAgree x rest r.2.1.1 ∧ RestFree x.2.1 r.2.1.1.1.1.data.cache := by
  apply backendT_preserves Allowed tagOf x q s pads τ g noise rest
    (fun cs _ => RestAgree x rest cs ∧ RestFree x.2.1 cs.1.1.data.cache) ?_ ?_ ?_ t ht st h r hr
  · intro t ht cs sh h r hr
    have ha : OrdinaryAllowed t := by
      cases t <;> exact ht
    have hh := ordinaryT_restAgree x hi q s pads noise rest t ha (merged x.2.1 cs sh.cache)
      ((restAgree_merged x rest hi cs sh.cache).mpr h.1) r hr
    exact ⟨(restAgree_split x rest hi _).mpr hh, restFree_erase _ _⟩
  · intro cs sh h T p tag a ha r hr
    refine ⟨?_, restFree_erase _ _⟩
    · apply (restAgree_split x rest hi _).mpr
      intro z v hv
      rw [hashTail_rest_frame x _ _ _ _ r hr z, merge_rest x.2.1 x.2.2 hi] at hv
      exact h.1 z v hv
  · intro cs sh h p target tag a ha; exact h

theorem freshPendingT_pendingValid (_x : Keys3 C) (noise : ChainNoiseIndex → HashOutput)
    (rest : RestSlot C → HashOutput) (edge : ChainNoiseIndex) (st : CappedCompilerState C)
    (h : PendingValid st.1.1.data)
    (r : DeferredOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshPending edge st))) :
    PendingValid r.2.1.1.data := by
  cases hp : st.1.1.data.pending (chainPending edge) with
  | some v =>
    simp only [freshPending, hp, simulateQ_pure, mem_support_pure_iff] at hr
    subst r; exact h
  | none =>
    simp only [freshPending, hp, simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, resolvePrivateTable, Sum.elim_inl, simulateQ_pure, pure_bind, mem_support_pure_iff] at hr
    subst r
    intro p v hv
    by_cases he : p = chainPending edge
    · subst p
      simp only [Function.update_self, Option.some.injEq] at hv
      subst v
      cases hn : (chainPending edge).next with
      | none => exact Or.inr ⟨rfl, (XmssSecurity.Rom.hashOutputEquivDigestPair (noise edge)).2, by simp [pendingOutput, hn]⟩
      | some k => exact Or.inl ⟨k, rfl, by simp [pendingOutput, hn]⟩
    · exact h p v (by simpa [Function.update_of_ne he] using hv)


theorem freshRestT_pendingValid (x : Keys3 C) (noise : ChainNoiseIndex → HashOutput)
    (rest : RestSlot C → HashOutput) (z : RestSlot C) (st : CappedCompilerState C)
    (h : PendingValid st.1.1.data) (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshRest x.1 x.2.1 x.2.2 z st))) : PendingValid r.2.1.1.data := by
  rw [freshRestT_run] at hr
  cases hc : st.1.1.data.cache (restInput x.2.1 x.2.2 z) <;> rw [hc] at hr
  all_goals
    have hp := (hashTail_grows x.1 x.2.1 _ st _ _ r hr).2
    intro p v hv; exact h p v (hp ▸ hv)

/-- Pending validity has no alphabet restriction. -/
theorem ordinaryT_pendingValid (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (h : PendingValid st.1.1.data)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinaryT x.1 x.2.1 x.2.2 q s pads noise rest t st)) :
    PendingValid r.2.1.1.data := by
  cases t with
  | inr k =>
    simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
    exact ordinary_pendingValid x.1 x.2.1 q s pads _ st h r hr
  | inl t =>
    cases t with
    | hash input =>
      simp only [ordinaryT, ordinaryRaw] at hr
      cases hz : restRoute x.2.1 x.2.2 input with
      | some z =>
        simp only [hz] at hr
        exact freshRestT_pendingValid x noise rest z st h r hr
      | none =>
        simp only [hz, resolvePrivateTable_lift] at hr
        exact ordinary_pendingValid x.1 x.2.1 q s pads _ st h r hr
    | pending p =>
      cases p with
      | bottom e l p => exact freshPendingT_pendingValid x noise rest _ st h r hr
      | top b l p => exact freshPendingT_pendingValid x noise rest _ st h r hr
      | _ =>
        simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
        exact ordinary_pendingValid x.1 x.2.1 q s pads _ st h r hr
    | _ =>
      simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
      exact ordinary_pendingValid x.1 x.2.1 q s pads _ st h r hr

/-- Every query preserves pending validity of the merged backend. -/
theorem backendT_pendingValid (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SpecX C).Domain) (st : FullState C Tag)
    (h : PendingValid (merged x.2.1 st.1.1 st.2.cache).1.1.data)
    (r : SpecX C t × FullState C Tag)
    (hr : r ∈ support (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest t st)) :
    PendingValid (merged x.2.1 r.2.1.1 r.2.2.cache).1.1.data := by
  apply backendT_preserves (fun _ => True) tagOf x q s pads τ g noise rest
    (fun cs _ => PendingValid cs.1.1.data) ?_ ?_ ?_ t trivial st h r hr
  · intro t _ cs sh h r hr
    exact ordinaryT_pendingValid x q s pads noise rest t (merged x.2.1 cs sh.cache) h r hr
  · intro cs sh h T p tag a ha r hr
    have hp := (hashTail_grows x.1 x.2.1 _ _ _ _ r hr).2
    intro p v hv; exact h p v (hp ▸ hv)
  · intro cs sh h p target tag a ha; exact h

/-- Allowed queries preserve the rest table, its disjoint domain, and pending validity. -/
theorem backendT_frame (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SpecX C).Domain) (ht : Allowed t) (st : FullState C Tag)
    (h : Frame x rest st.1.1) (r : SpecX C t × FullState C Tag)
    (hr : r ∈ support (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest t st)) :
    Frame x rest r.2.1.1 := by
  have hf := backendT_restFrame tagOf x hi q s pads τ g noise rest t ht st ⟨h.1, h.2.1⟩ r hr
  exact ⟨hf.1, hf.2, backendT_pendingValid tagOf x q s pads τ g noise rest t st h.2.2 r hr⟩

/-- Alphabet-restricted version of SigningOpeningProof.simulateQ_sticky. -/
theorem queries_preserve {ι σ α : Type} {spec : OracleSpec ι}
    (allowed : ι → Prop) (impl : QueryImpl spec (StateT σ ProbComp)) (I : σ → Prop)
    (step : ∀ t, allowed t → ∀ st, I st → ∀ r ∈ support ((impl t).run st), I r.2)
    (oa : OracleComp spec α) (ha : Queries allowed oa) (st : σ) (h : I st)
    (r : α × σ) (hr : r ∈ support ((simulateQ impl oa).run st)) : I r.2 := by
  induction oa using OracleComp.inductionOn generalizing st r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r; exact h
  | query_bind t next ih =>
    have hq := (isQueryBound_query_bind_iff ..).mp ha
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨a, ha, hr⟩ := hr
    exact ih a.1 (hq.2 a.1) a.2 (step t hq.1 st h a ha) r hr

/-- Frame and table agreement lifted through any safe source program. -/
theorem safe_frame {α : Type} (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (oa : SourceMX C α) (ha : Safe oa) (src : SourceState C) (st : FullState C Tag)
    (h : Frame x rest st.1.1 ∧ ShareG g st.2)
    (r : (α × SourceState C) × FullState C Tag)
    (hr : r ∈ support ((simulateQ
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) (oa.run src)).run st)) :
    Frame x rest r.2.1.1 ∧ ShareG g r.2.2 := by
  apply queries_preserve Allowed _ (fun fs => Frame x rest fs.1.1 ∧ ShareG g fs.2)
    ?_ (oa.run src) (ha src) st h r hr
  intro t ht st h r hr
  exact ⟨backendT_frame tagOf x hi q s pads τ g noise rest t ht st h.1 r hr,
    backendT_shareG tagOf x q s pads τ g noise rest t st h.2 r hr⟩

/-- The actual adversary-facing compiler handler preserves the frames. -/
theorem compAdv_frame (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (LocalSpec C + TsigSpec C).Domain) (src : SourceState C) (st : FullState C Tag)
    (h : Frame x rest st.1.1 ∧ ShareG g st.2)
    (r : (LocalSpec C + TsigSpec C) t × (SourceState C × FullState C Tag))
    (hr : r ∈ support ((SigningCompilerUntil.fuse (sourceOraclesX prims x top)
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) t).run (src, st))) :
    Frame x rest r.2.2.1.1 ∧ ShareG g r.2.2.2 := by
  simp only [SigningCompilerUntil.fuse, StateT.run, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact safe_frame tagOf x hi q s pads τ g noise rest _
    (safe_sourceOraclesX prims x top t) src st h a ha

/-- The same invariant through the complete adversary program. -/
theorem compAdv_simulate_frame {α : Type} (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (src : SourceState C) (st : FullState C Tag)
    (h : Frame x rest st.1.1 ∧ ShareG g st.2)
    (r : α × (SourceState C × FullState C Tag))
    (hr : r ∈ support ((simulateQ (SigningCompilerUntil.fuse (sourceOraclesX prims x top)
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)) oa).run (src, st))) :
    Frame x rest r.2.2.1.1 ∧ ShareG g r.2.2.2 := by
  apply simulateQ_sticky _ (fun sc => Frame x rest sc.2.1.1 ∧ ShareG g sc.2.2)
    ?_ oa (src, st) h r hr
  intro t sc h r hr
  exact compAdv_frame tagOf prims x top hi q s pads τ g noise rest t sc.1 sc.2 h r hr

theorem initial_frame (x : Keys3 C) (rest : RestSlot C → HashOutput)
    (g : C.Term × CPoint → HashOutput) :
    Frame x rest (initial (C := C) (Tag := Tag)).1.1 ∧
      ShareG g (initial (C := C) (Tag := Tag)).2 := by
  refine ⟨⟨?_, ?_, pendingValid_init⟩, ?_⟩
  · intro z v hv; cases hv
  · intro input z hz; rfl
  · intro y v hv; cases hv

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncFrame.compAdv_simulate_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compAdv_simulate_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncFrame.backendT_shareG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms backendT_shareG

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncFrame.backendT_pendingValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms backendT_pendingValid

end ThresholdLeanXmssSecurity.SigningCompilerSyncFrame
