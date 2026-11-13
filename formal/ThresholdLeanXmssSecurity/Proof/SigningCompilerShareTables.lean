import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTag
import ThresholdLeanXmssSecurity.Proof.SigningCompilerRealTables
import ThresholdLeanXmssSecurity.Proof.SigningCompilerCouplingUntil

/-!
# Private tables for the eager signing compiler

The compiler retains its visible pending and hash caches. A separate private
oracle supplies fresh chain answers and free slot reads; sampling that oracle
in advance preserves the complete compiler outcome and share metadata.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShareTables
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerRealTables
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

abbrev TableIndex (C : Committee) := ChainNoiseIndex ⊕ RestSlot C
abbrev PrivateSpec (C : Committee) := SigningGuessProof.PrivateRoSpec (TableIndex C) HashOutput
abbrev PrivateCache (C : Committee) := (TableIndex C →ₒ HashOutput).QueryCache
abbrev FullState (C : Committee) (Tag : Type) :=
  (CappedCompilerState C × Bool) × ShareStateT C Tag

def restInput (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : RestSlot C) : Query C := TprfSecurityProof.slotInput seeds pairs z.val

def restRoute (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (query : Query C) : Option (RestSlot C) :=
  if h : ∃ z, restInput seeds pairs z = query then some h.choose else none

theorem restInput_injective (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs)) :
    Function.Injective (restInput seeds pairs) := fun _ _ h => Subtype.ext (hi h)

theorem restRoute_spec (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (query : Query C) (z : RestSlot C) :
    restRoute seeds pairs query = some z ↔ restInput seeds pairs z = query := by
  unfold restRoute
  split_ifs with h
  · constructor
    · intro he; simpa only [Option.some.inj he] using h.choose_spec
    · intro he
      exact congrArg some (restInput_injective seeds pairs hi (h.choose_spec.trans he.symm))
  · constructor
    · intro he; cases he
    · intro he; exact (h ⟨z, he⟩).elim

theorem route_rest (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs)) (z : RestSlot C) :
    route seeds (restInput seeds pairs z) = none := by
  unfold route
  split_ifs with h
  · obtain ⟨u, hu⟩ := h
    exact (z.property u.1 u.2 (hi hu)).elim
  · rfl

@[simp] theorem merge_rest (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (cache : HashCache C) (share : ShareCache C) (z : RestSlot C) :
    merge seeds cache share (restInput seeds pairs z) = cache (restInput seeds pairs z) := by
  simp [merge, route_rest seeds pairs hi z]

@[simp] theorem erase_rest (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (cache : HashCache C) (z : RestSlot C) :
    erase seeds cache (restInput seeds pairs z) = cache (restInput seeds pairs z) := by
  simp [erase, route_rest seeds pairs hi z]

def freshPending (edge : ChainNoiseIndex) (st : CappedCompilerState C) :
    OracleComp (PrivateSpec C) (DeferredOutput × CappedCompilerState C) :=
  match st.1.1.data.pending (chainPending edge) with
  | some value => pure (value, incrementCompilerCount st)
  | none => do
    let value ← query (spec := PrivateSpec C) (.inr (.inl edge))
    let answer := pendingOutput (chainPending edge) value
    pure (answer, (({ st.1.1 with data := { st.1.1.data with
      pending := Function.update st.1.1.data.pending (chainPending edge) (some answer) } },
      st.1.2 + 1), st.2))

def freshRest (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (z : RestSlot C) (st : CappedCompilerState C) :
    OracleComp (PrivateSpec C) (HashOutput × CappedCompilerState C) := do
  let input := restInput seeds pairs z
  let read ← match st.1.1.data.cache input with
    | some value => pure (value, st.1.1.data.cache)
    | none => do
      let value ← query (spec := PrivateSpec C) (.inr (.inr z))
      pure (value, st.1.1.data.cache.cacheQuery input value)
  liftM (hashTail P seeds input st read.1 read.2)

def ordinaryRaw (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    QueryImpl (DeferredSpec C + RevealSpec HiddenKey Digest)
      (StateT (CappedCompilerState C) (OracleComp (PrivateSpec C)))
  | .inl (.pending (.bottom e l p)) => freshPending (l, .inl e, p)
  | .inl (.pending (.top b l p)) => freshPending (l, .inr b, p)
  | .inl (.hash input) => fun st => match restRoute seeds pairs input with
      | some z => freshRest P seeds pairs z st
      | none => liftM (ordinary P seeds q s pads (.inl (.hash input)) st)
  | t => fun st => liftM (ordinary P seeds q s pads t st)

def ordinaryT (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput) :
    QueryImpl (DeferredSpec C + RevealSpec HiddenKey Digest)
      (StateT (CappedCompilerState C) ProbComp) := fun t st =>
  simulateQ (resolvePrivateTable (Sum.elim noise rest)) (ordinaryRaw P seeds pairs q s pads t st)

/-- The two private caches record only coordinates already visible to the source. -/
def Fresh (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (cache : PrivateCache C) (st : CappedCompilerState C) : Prop :=
  (∀ e, st.1.1.data.pending (chainPending e) = none → cache (.inl e) = none) ∧
  (∀ z, st.1.1.data.cache (restInput seeds pairs z) = none → cache (.inr z) = none)


attribute [local irreducible] hashTail

/-- Fixed pads preserve both domains just as ordinary capped steps do. -/
theorem ordinary_grows (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinary P seeds q s pads t st)) :
    st.1.1.data.cache ≤ r.2.1.1.data.cache ∧
      ∀ p, st.1.1.data.pending p ≠ none → r.2.1.1.data.pending p ≠ none := by
  have cap (t : DeferredQuery C ⊕ HiddenKey)
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
      (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run st)) :
      st.1.1.data.cache ≤ r.2.1.1.data.cache ∧
        ∀ p, st.1.1.data.pending p ≠ none → r.2.1.1.data.pending p ≠ none :=
    ⟨cappedCompiler_cache_le P seeds q s t st r hr,
      fun p hp => cappedCompiler_pending_mono P seeds q s t st r hr p hp⟩
  cases t with
  | inr k => exact cap (.inr k) r hr
  | inl t =>
    cases t with
    | pad p =>
      cases hp : st.1.1.data.pads p <;>
        simp only [ordinary, padStep, hp, mem_support_pure_iff] at hr <;>
        subst r <;> exact ⟨le_rfl, fun _ h => h⟩
    | _ => exact cap _ r hr

theorem Fresh.mono (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    {cache : PrivateCache C} {st st' : CappedCompilerState C}
    (h : Fresh seeds pairs cache st)
    (hc : st.1.1.data.cache ≤ st'.1.1.data.cache)
    (hp : ∀ p, st.1.1.data.pending p ≠ none → st'.1.1.data.pending p ≠ none) :
    Fresh seeds pairs cache st' := by
  constructor
  · intro e he; apply h.1 e; by_contra hn; exact hp _ hn he
  · intro z hz; apply h.2 z
    cases he : st.1.1.data.cache (restInput seeds pairs z) with
    | none => rfl
    | some v => have hv := hc he; rw [hz] at hv; cases hv

set_option linter.constructorNameAsVariable false in
theorem hashTail_grows (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : Query C) (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (hashTail P seeds input st value cache)) :
    cache ≤ r.2.1.1.data.cache ∧ r.2.1.1.data.pending = st.1.1.data.pending := by
  simp only [hashTail, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  have hf := SigningReleasedTransferProof.cachedExtra_frame seeds P
    (((st.1.1.data.cache, 0), []), compilerSigning st.1.1, false)
    (.inr (.inr (.inl input))) (((cache, 0), []), compilerSigning st.1.1, false) a (by
      dsimp only [StateT.run] at ha ⊢
      with_reducible exact ha)
  exact ⟨hf.1, rfl⟩

/-- Constructor sibling of ordinary_hash_prf, covering all free slot inputs. -/
theorem ordinary_hash_rest (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (z : RestSlot C) (st : CappedCompilerState C) :
    ordinary P seeds q s pads (.inl (.hash (restInput seeds pairs z))) st = (do
      let r ← ((Query C →ₒ HashOutput).randomOracle (restInput seeds pairs z)).run st.1.1.data.cache
      hashTail P seeds (restInput seeds pairs z) st r.1 r.2) := by
  rcases z with ⟨(⟨T, p⟩ | ⟨pair, p, m, J⟩), hz⟩
  · exact ordinary_hash_prf P seeds q s pads (seeds T) p st
  · simp only [restInput, TprfSecurityProof.slotInput, ordinary,
      SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
      deferredCounted, deferredInputSide, deferredCandidate, Option.isSome_none,
      Bool.false_eq_true, false_and, and_false, or_false, decide_false,
      Bool.or_false, if_true, compilerImpl, deferredImpl, StateT.run, StateT.mk,
      map_bind, bind_map_left, map_pure, hashTail]

theorem freshPending_run (edge : ChainNoiseIndex) (st : CappedCompilerState C)
    (cache : PrivateCache C)
    (hf : st.1.1.data.pending (chainPending edge) = none → cache (.inl edge) = none) :
    (simulateQ SigningGuessProof.privateRoImpl (freshPending edge st)).run cache =
    match st.1.1.data.pending (chainPending edge) with
    | some answer => pure ((answer, incrementCompilerCount st), cache)
    | none => (fun value : HashOutput =>
      let answer := pendingOutput (chainPending edge) value
      ((answer, (({ st.1.1 with data := { st.1.1.data with
        pending := Function.update st.1.1.data.pending (chainPending edge) (some answer) } },
        st.1.2 + 1), st.2)), cache.cacheQuery (.inl edge) value)) <$> ($ᵗ HashOutput) := by
  cases hp : st.1.1.data.pending (chainPending edge) with
  | some answer => simp only [freshPending, hp, simulateQ_pure, StateT.run_pure]
  | none =>
    simp only [freshPending, hp, HasQuery.instOfMonadLift_query, simulateQ_bind,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_pure, StateT.run_bind, StateT.run_pure,
      SigningGuessProof.privateRoImpl, QueryImpl.add_apply_inr]
    simp only [bind_pure_comp]
    erw [QueryImpl.withCaching_run_none _ (hf hp), Functor.map_map]

theorem freshRest_run (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (z : RestSlot C) (st : CappedCompilerState C)
    (cache : PrivateCache C)
    (hf : st.1.1.data.cache (restInput seeds pairs z) = none → cache (.inr z) = none) :
    (simulateQ SigningGuessProof.privateRoImpl (freshRest P seeds pairs z st)).run cache =
    (match st.1.1.data.cache (restInput seeds pairs z) with
    | some value => (fun r => (r, cache)) <$>
        hashTail P seeds (restInput seeds pairs z) st value st.1.1.data.cache
    | none => do
      let value ← $ᵗ HashOutput
      let r ← hashTail P seeds (restInput seeds pairs z) st value
        (st.1.1.data.cache.cacheQuery (restInput seeds pairs z) value)
      pure (r, cache.cacheQuery (.inr z) value)) := by
  cases hp : st.1.1.data.cache (restInput seeds pairs z) with
  | some value =>
    simp only [freshRest, hp, pure_bind, SigningGuessProof.privateRoImpl, roSim.run_liftM]
  | none =>
    simp only [freshRest, hp, pure_bind, simulateQ_bind, StateT.run_bind,
      HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, SigningGuessProof.privateRoImpl,
      QueryImpl.add_apply_inr, roSim.run_liftM]
    erw [QueryImpl.withCaching_run_none _ (hf hp), bind_map_left]


theorem Fresh.cache_left (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    {cache : PrivateCache C} {st : CappedCompilerState C} (h : Fresh seeds pairs cache st)
    (e : ChainNoiseIndex) (v : HashOutput) (hp : st.1.1.data.pending (chainPending e) ≠ none) :
    Fresh seeds pairs (cache.cacheQuery (.inl e) v) st := by
  constructor
  · intro f hf
    by_cases he : f = e
    · subst f; exact (hp hf).elim
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using he)]
      exact h.1 f hf
  · intro z hz
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    exact h.2 z hz

theorem Fresh.cache_right (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    {cache : PrivateCache C} {st : CappedCompilerState C} (h : Fresh seeds pairs cache st)
    (z : RestSlot C) (v : HashOutput) (hp : st.1.1.data.cache (restInput seeds pairs z) ≠ none) :
    Fresh seeds pairs (cache.cacheQuery (.inr z) v) st := by
  constructor
  · intro e he
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    exact h.1 e he
  · intro w hw
    by_cases he : w = z
    · subst w; exact (hp hw).elim
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using he)]
      exact h.2 w hw

theorem freshPending_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (edge : ChainNoiseIndex) (st : CappedCompilerState C) (cache : PrivateCache C)
    (hf : st.1.1.data.pending (chainPending edge) = none → cache (.inl edge) = none) :
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl (freshPending edge st)).run cache =
      ordinary P seeds q s pads (.inl (.pending (chainPending edge))) st := by
  rw [freshPending_run edge st cache hf]
  change _ = (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
    (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
    (.inl (.pending (chainPending edge)))).run st
  rw [cappedCompiler_pending_run]
  cases hp : st.1.1.data.pending (chainPending edge) <;>
    simp only [Functor.map_map, map_pure]

theorem freshRest_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (z : RestSlot C) (st : CappedCompilerState C) (cache : PrivateCache C)
    (hf : st.1.1.data.cache (restInput seeds pairs z) = none → cache (.inr z) = none) :
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl (freshRest P seeds pairs z st)).run cache =
      ordinary P seeds q s pads (.inl (.hash (restInput seeds pairs z))) st := by
  rw [freshRest_run P seeds pairs z st cache hf, ordinary_hash_rest]
  cases hp : st.1.1.data.cache (restInput seeds pairs z) with
  | some value =>
    rw [QueryImpl.withCaching_run_some _ hp]
    simp only [pure_bind, Functor.map_map, id_map']
  | none =>
    rw [QueryImpl.withCaching_run_none _ hp]
    simp only [map_bind, map_pure, bind_pure, bind_map_left]
    rfl

theorem freshPending_inv (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (edge : ChainNoiseIndex) (st : CappedCompilerState C) (cache : PrivateCache C)
    (h : Fresh seeds pairs cache st)
    (r : (DeferredOutput × CappedCompilerState C) × PrivateCache C)
    (hr : r ∈ support ((simulateQ SigningGuessProof.privateRoImpl (freshPending edge st)).run cache)) :
    Fresh seeds pairs r.2 r.1.2 := by
  rw [freshPending_run edge st cache (h.1 edge)] at hr
  cases hp : st.1.1.data.pending (chainPending edge) with
  | some value =>
    simp only [hp, mem_support_pure_iff] at hr
    subst r; exact h
  | none =>
    simp only [hp, support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    refine Fresh.cache_left seeds pairs ?_ edge v ?_
    · refine Fresh.mono seeds pairs h ?_ ?_
      · exact le_rfl
      intro p hn
      by_cases he : p = chainPending edge
      · subst p; simp
      · simpa only [Function.update_of_ne he] using hn
    · simp

theorem freshRest_inv (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (z : RestSlot C) (st : CappedCompilerState C)
    (cache : PrivateCache C) (h : Fresh seeds pairs cache st)
    (r : (HashOutput × CappedCompilerState C) × PrivateCache C)
    (hr : r ∈ support ((simulateQ SigningGuessProof.privateRoImpl (freshRest P seeds pairs z st)).run cache)) :
    Fresh seeds pairs r.2 r.1.2 := by
  rw [freshRest_run P seeds pairs z st cache (h.2 z)] at hr
  cases hp : st.1.1.data.cache (restInput seeds pairs z) with
  | some value =>
    simp only [hp, support_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    have hg := hashTail_grows P seeds _ st value _ a ha
    exact h.mono seeds pairs hg.1 (fun p hn => hg.2 ▸ hn)
  | none =>
    simp only [hp, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨v, _, a, ha, rfl⟩ := hr
    have hg := hashTail_grows P seeds _ st v _ a ha
    refine Fresh.cache_right seeds pairs ?_ z v ?_
    · exact h.mono seeds pairs ((QueryCache.le_cacheQuery _ hp).trans hg.1)
        (fun p hn => hg.2 ▸ hn)
    · intro hn
      have hv := hg.1 (QueryCache.cacheQuery_self st.1.1.data.cache (restInput seeds pairs z) v)
      rw [hn] at hv; cases hv


/-- One private-table step retains the actual visible outcome and freshness. -/
theorem ordinaryRaw_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (cache : PrivateCache C) (h : Fresh seeds pairs cache st) :
    (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
      (ordinaryRaw P seeds pairs q s pads t st)).run cache = ordinary P seeds q s pads t st) ∧
    (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      (ordinaryRaw P seeds pairs q s pads t st)).run cache), Fresh seeds pairs r.2 r.1.2) := by
  have liftStep (t : DeferredQuery C ⊕ HiddenKey) :
      (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (liftM (ordinary P seeds q s pads t st) : OracleComp (PrivateSpec C) _)).run cache =
        ordinary P seeds q s pads t st) ∧
      (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
        (liftM (ordinary P seeds q s pads t st) : OracleComp (PrivateSpec C) _)).run cache),
        Fresh seeds pairs r.2 r.1.2) := by
    rw [SigningGuessProof.privateRoImpl, roSim.run_liftM]
    constructor
    · simp only [Functor.map_map, id_map']
    · intro r hr
      simp only [support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have hg := ordinary_grows P seeds q s pads t st a ha
      exact h.mono seeds pairs hg.1 hg.2
  have pend (e : ChainNoiseIndex) :
      (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (freshPending e st)).run cache = ordinary P seeds q s pads (.inl (.pending (chainPending e))) st) ∧
      (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl (freshPending e st)).run cache),
        Fresh seeds pairs r.2 r.1.2) :=
    ⟨freshPending_eq P seeds q s pads e st cache (h.1 e),
      freshPending_inv seeds pairs e st cache h⟩
  cases t with
  | inr k => exact liftStep (.inr k)
  | inl t =>
    cases t with
    | pending p =>
      cases p with
      | bottom e l p => exact pend (l, .inl e, p)
      | top b l p => exact pend (l, .inr b, p)
      | commitment e => exact liftStep (.inl (.pending (.commitment e)))
      | base lay e m => exact liftStep (.inl (.pending (.base lay e m)))
    | hash input =>
      cases hr : restRoute seeds pairs input with
      | none => simpa only [ordinaryRaw, hr] using liftStep (.inl (.hash input))
      | some z =>
        have he := (restRoute_spec seeds pairs hi input z).mp hr
        subst input
        simp only [ordinaryRaw, hr]
        exact ⟨freshRest_eq P seeds pairs q s pads z st cache (h.2 z),
          freshRest_inv P seeds pairs z st cache h⟩
    | _ => exact liftStep _


def eagerBackend (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp) :=
  SigningCompilerUntil.fuse (shareBackendTag tagOf P seeds q s pads) (eagerHandlerTag τ g)

def ordinaryFullRaw (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : FullState C Tag) :
    OracleComp (PrivateSpec C) ((DeferredSpec C + RevealSpec HiddenKey Digest) t × FullState C Tag) := do
  let a ← ordinaryRaw P seeds pairs q s pads t (merged seeds st.1.1 st.2.cache)
  pure (a.1, ((splitRest seeds a.2, st.1.2), st.2))

def backendRaw (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    QueryImpl (SpecX C) (StateT (FullState C Tag) (OracleComp (PrivateSpec C)))
  | .inl (.inl (.inl (.hash input))) => fun st => match route seeds input with
      | some _ => liftM (eagerBackend tagOf P seeds q s pads τ g (.inl (.inl (.inl (.hash input)))) st)
      | none => ordinaryFullRaw P seeds pairs q s pads (.inl (.hash input)) st
  | .inl (.inl (.inl t)) => ordinaryFullRaw P seeds pairs q s pads (.inl t)
  | .inl (.inl (.inr k)) => ordinaryFullRaw P seeds pairs q s pads (.inr k)
  | t => fun st => liftM (eagerBackend tagOf P seeds q s pads τ g t st)

def shareBackendTagT (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput) :
    QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp) := fun t st =>
  simulateQ (resolvePrivateTable (Sum.elim noise rest))
    (backendRaw tagOf P seeds pairs q s pads τ g t st)

@[simp] theorem eager_share (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : SigningShareLazy.ShareQuery C.Term CPoint Tag) (share : ShareStateT C Tag) :
    (simulateQ (eagerHandlerTag τ g) (shareQueryTag t)).run share =
      (SigningShareLazy.eagerImpl C.terms τ g t).run share := by
  simp [shareQueryTag, eagerHandlerTag]

@[simp] theorem eager_lift (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    {α : Type} (oa : ProbComp α) (share : ShareStateT C Tag) :
    (simulateQ (eagerHandlerTag τ g) (liftM oa : OracleComp (RunSpecT C Tag) α)).run share =
      (fun a => (a, share)) <$> oa := unif_lift _ oa share

@[simp] theorem eager_view (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (share : ShareStateT C Tag) :
    (simulateQ (eagerHandlerTag τ g) (shareQueryTag .view)).run share =
      pure ((share.cache, share.done), share) := by rw [eager_share]; rfl

theorem eager_ordinary (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : DeferredQuery C ⊕ HiddenKey) (st : FullState C Tag) :
    (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (eagerHandlerTag τ g) (ordinaryStepTag P seeds q s pads t st.1)).run st.2 =
      (fun a => (a.1, ((splitRest seeds a.2, st.1.2), st.2))) <$>
        ordinary P seeds q s pads t (merged seeds st.1.1 st.2.cache) := by
  simp only [ordinaryStepTag, simulateQ_bind, StateT.run_bind, eager_view, pure_bind, eager_lift,
    bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]

@[simp] theorem eagerImpl_view (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (st : ShareStateT C Tag) :
    (SigningShareLazy.eagerImpl C.terms τ g .view).run st = pure ((st.cache, st.done), st) := rfl

theorem eager_read (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (T : C.Term) (p : CPoint) (st : FullState C Tag) :
    (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (eagerHandlerTag τ g) (readStepTag tagOf P seeds T p st.1)).run st.2 = (do
      let a ← (SigningShareLazy.eagerImpl C.terms τ g (.read T p (tagOf st.1))).run st.2
      let r ← hashTail P seeds (key seeds (T, p)) (merged seeds st.1.1 st.2.cache)
        a.1 (merge seeds st.1.1.1.1.data.cache a.2.cache)
      pure (r.1, ((splitRest seeds r.2, st.1.2), a.2))) := by
  simp only [readStepTag, simulateQ_bind, StateT.run_bind, pure_bind, eager_share, eager_lift, map_bind,
    bind_pure_comp, eagerImpl_view, simulateQ_map, StateT.run_map, Functor.map_map]


@[simp] theorem fresh_merged (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (cache : PrivateCache C) (st : CappedCompilerState C) (share : ShareCache C) :
    Fresh seeds pairs cache (merged seeds st share) ↔ Fresh seeds pairs cache st := by
  simp only [Fresh, merged, withCache, merge_rest seeds pairs hi]

@[simp] theorem fresh_split (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (cache : PrivateCache C) (st : CappedCompilerState C) :
    Fresh seeds pairs cache (splitRest seeds st) ↔ Fresh seeds pairs cache st := by
  simp only [Fresh, splitRest, withCache, erase_rest seeds pairs hi]

attribute [local irreducible] ordinaryStepTag readStepTag eagerHandlerTag SigningShareLazy.eagerImpl ordinary

theorem eagerBackend_fresh (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : (SpecX C).Domain) (st : FullState C Tag) (cache : PrivateCache C)
    (h : Fresh seeds pairs cache st.1.1)
    (r : (SpecX C t) × FullState C Tag)
    (hr : r ∈ support (eagerBackend tagOf P seeds q s pads τ g t st)) :
    Fresh seeds pairs cache r.2.1.1 := by
  have hord (t : DeferredQuery C ⊕ HiddenKey)
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × FullState C Tag)
      (hr : r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (ordinaryStepTag P seeds q s pads t st.1)).run st.2)) :
      Fresh seeds pairs cache r.2.1.1 := by
    rw [eager_ordinary] at hr
    simp only [support_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    apply (fresh_split seeds pairs hi cache a.2).mpr
    have hg := ordinary_grows P seeds q s pads t _ a ha
    exact ((fresh_merged seeds pairs hi cache _ st.2.cache).mpr h).mono seeds pairs hg.1 hg.2
  have hread (T : C.Term) (p : CPoint)
      (r : HashOutput × FullState C Tag)
      (hr : r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (readStepTag tagOf P seeds T p st.1)).run st.2)) :
      Fresh seeds pairs cache r.2.1.1 := by
    rw [eager_read] at hr
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, _, b, hb, rfl⟩ := hr
    apply (fresh_split seeds pairs hi cache b.2).mpr
    have hg := hashTail_grows P seeds _ _ a.1 _ b hb
    have hf := (fresh_merged seeds pairs hi cache st.1.1 a.2.cache).mpr h
    refine Fresh.mono seeds pairs hf hg.1 ?_
    intro p hp
    simpa only [hg.2, merged, withCache] using hp
  rcases t with ((t | k) | mark) | ⟨p, target⟩
  · cases t with
    | hash input =>
      cases hrout : route seeds input with
      | none => exact hord (.inl (.hash input)) r (by
          simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hrout] at hr
          exact hr)
      | some z => exact hread z.1 z.2 r (by
          simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hrout] at hr
          exact hr)
    | pending p => exact hord (.inl (.pending p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | virtual T p => exact hord (.inl (.virtual T p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | pad p => exact hord (.inl (.pad p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | inspect p => exact hord (.inl (.inspect p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | plant p v => exact hord (.inl (.plant p v)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | snapshot => exact hord (.inl .snapshot) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | sample => exact hord (.inl .sample) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | record p v => exact hord (.inl (.record p v)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | uniform n => exact hord (.inl (.uniform n)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
    | bindKey e m => exact hord (.inl (.bindKey e m)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
        exact hr)
  · apply hord (.inr k) r
    simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr
    exact hr
  · simp only [eagerBackend, SigningCompilerUntil.fuse, StateT.run, shareBackendTag, simulateQ_pure] at hr
    subst r; exact h
  · by_cases hp : Constrained p
    · simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hp, dif_pos] at hr
      change r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (do
          let value ← shareQueryTag (.complete ⟨p, hp⟩ target (tagOf st.1))
          pure (value, st.1))).run st.2) at hr
      simp only [simulateQ_bind, StateT.run_bind, eager_share, simulateQ_pure,
        StateT.run_pure, map_bind, map_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact h
    · simp only [eagerBackend, SigningCompilerUntil.fuse, StateT.run, shareBackendTag, hp] at hr
      subst r; exact h



theorem ordinaryFullRaw_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : DeferredQuery C ⊕ HiddenKey) (st : FullState C Tag)
    (cache : PrivateCache C) (h : Fresh seeds pairs cache st.1.1) :
    (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
      (ordinaryFullRaw P seeds pairs q s pads t st)).run cache =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (ordinaryStepTag P seeds q s pads t st.1)).run st.2) ∧
    (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      (ordinaryFullRaw P seeds pairs q s pads t st)).run cache), Fresh seeds pairs r.2 r.1.2.1.1) := by
  have hs := ordinaryRaw_step P seeds pairs hi q s pads t (merged seeds st.1.1 st.2.cache) cache
    ((fresh_merged seeds pairs hi cache _ st.2.cache).mpr h)
  simp only [ordinaryFullRaw, bind_pure_comp, simulateQ_map, StateT.run_map]
  constructor
  · rw [eager_ordinary]
    simpa only [Functor.map_map] using congrArg
      (fun oa => (fun a => (a.1, ((splitRest seeds a.2, st.1.2), st.2))) <$> oa) hs.1
  · intro r hr
    simp only [support_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    exact (fresh_split seeds pairs hi a.2 a.1.2).mpr (hs.2 a ha)

theorem backendRaw_step (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : (SpecX C).Domain) (st : FullState C Tag) (cache : PrivateCache C)
    (h : Fresh seeds pairs cache st.1.1) :
    (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
      (backendRaw tagOf P seeds pairs q s pads τ g t st)).run cache =
      eagerBackend tagOf P seeds q s pads τ g t st) ∧
    (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      (backendRaw tagOf P seeds pairs q s pads τ g t st)).run cache), Fresh seeds pairs r.2 r.1.2.1.1) := by
  have hlift (t : (SpecX C).Domain) :
      (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (liftM (eagerBackend tagOf P seeds q s pads τ g t st) : OracleComp (PrivateSpec C) _)).run cache =
        eagerBackend tagOf P seeds q s pads τ g t st) ∧
      (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
        (liftM (eagerBackend tagOf P seeds q s pads τ g t st) : OracleComp (PrivateSpec C) _)).run cache),
        Fresh seeds pairs r.2 r.1.2.1.1) := by
    rw [SigningGuessProof.privateRoImpl, roSim.run_liftM]
    constructor
    · simp only [Functor.map_map, id_map']
    · intro r hr
      simp only [support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact eagerBackend_fresh tagOf P seeds pairs hi q s pads τ g t st cache h a ha
  have ho := ordinaryFullRaw_step (Tag := Tag) P seeds pairs hi q s pads τ g
  rcases t with ((t | k) | mark) | ⟨p, target⟩
  · cases t with
    | hash input =>
      cases hrout : route seeds input with
      | none =>
        simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hrout]
        exact ho (.inl (.hash input)) st cache h
      | some z =>
        simpa only [backendRaw, hrout] using hlift (.inl (.inl (.inl (.hash input))))
    | pending p =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.pending p)) st cache h
    | virtual T p =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.virtual T p)) st cache h
    | pad p =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.pad p)) st cache h
    | inspect p =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.inspect p)) st cache h
    | plant p v =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.plant p v)) st cache h
    | snapshot =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl .snapshot) st cache h
    | sample =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl .sample) st cache h
    | record p v =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.record p v)) st cache h
    | uniform n =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.uniform n)) st cache h
    | bindKey e m =>
      simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
      exact ho (.inl (.bindKey e m)) st cache h
  · simp only [backendRaw, eagerBackend, SigningCompilerUntil.fuse, shareBackendTag]
    exact ho (.inr k) st cache h
  · exact hlift (.inl (.inr mark))
  · exact hlift (.inr (p, target))

/-- Structural reification keeps the complete compiler and share state. -/
theorem programRaw_eq (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (hi : Function.Injective (TprfSecurityProof.slotInput seeds pairs))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    {α : Type} (oa : OracleComp (SpecX C) α) (st : FullState C Tag) (cache : PrivateCache C)
    (h : Fresh seeds pairs cache st.1.1) :
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
      ((simulateQ (backendRaw tagOf P seeds pairs q s pads τ g) oa).run st)).run cache =
      (simulateQ (eagerBackend tagOf P seeds q s pads τ g) oa).run st := by
  induction oa using OracleComp.inductionOn generalizing st cache with
  | pure a => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    have hs := backendRaw_step tagOf P seeds pairs hi q s pads τ g t st cache h
    calc
      _ = (simulateQ SigningGuessProof.privateRoImpl
          (backendRaw tagOf P seeds pairs q s pads τ g t st)).run cache >>= fun r =>
          (simulateQ (eagerBackend tagOf P seeds q s pads τ g) (next r.1.1)).run r.1.2 := by
        apply bind_congr_of_forall_mem_support
        intro r hr
        exact ih r.1.1 r.1.2 r.2 (hs.2 r hr)
      _ = _ := by
        change _ = eagerBackend tagOf P seeds q s pads τ g t st >>= fun r =>
          (simulateQ (eagerBackend tagOf P seeds q s pads τ g) (next r.1)).run r.2
        rw [← hs.1, bind_map_left]


def finish {α : Type} (seeds : C.Term → HashOutput) (r : α × FullState C Tag) :
    (α × CappedCompilerState C) × ShareStateT C Tag :=
  ((r.1, merged seeds r.2.1.1 r.2.2.cache), r.2.2)

def initial : FullState C Tag :=
  ((((compilerInit, 0), fun _ => none, false), false), SigningShareLazy.init)

def eagerRunTag (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    ProbComp (CompilerOutcome C × ShareStateT C Tag) :=
  (simulateQ (eagerHandlerTag τ g) (shareRunTag tagOf prims A x q s pads)).run SigningShareLazy.init

def rawProgram (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    OracleComp (PrivateSpec C) (CompilerOutcome C × ShareStateT C Tag) :=
  finish x.2.1 <$> (simulateQ (backendRaw tagOf x.1 x.2.1 x.2.2 q s pads τ g)
    (sourceProgramX prims A x)).run initial

def eagerRunTagT (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput) :
    ProbComp (CompilerOutcome C × ShareStateT C Tag) :=
  simulateQ (resolvePrivateTable (Sum.elim noise rest))
    (rawProgram tagOf prims A x q s pads τ g)

attribute [local irreducible] sourceProgramX

theorem eagerRunTag_fused (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    eagerRunTag tagOf prims A x q s pads τ g =
      finish x.2.1 <$> (simulateQ (eagerBackend tagOf x.1 x.2.1 q s pads τ g)
        (sourceProgramX prims A x)).run initial := by
  rw [eagerBackend, ← SigningCompilerUntil.simulateQ_fuse]
  simp only [eagerRunTag, shareRunTag, initial, simulateQ_bind, StateT.run_bind, eager_view,
    bind_pure_comp, finish, Functor.map_map, simulateQ_map, StateT.run_map, map_pure]

theorem eagerRunTag_raw (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    eagerRunTag tagOf prims A x q s pads τ g =
      Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (rawProgram tagOf prims A x q s pads τ g)).run ∅ := by
  rw [eagerRunTag_fused]
  have h := programRaw_eq tagOf x.1 x.2.1 x.2.2 hi q s pads τ g
    (sourceProgramX prims A x) initial ∅ ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [← h]
  simp only [rawProgram, simulateQ_map, StateT.run_map, Functor.map_map]

theorem eagerRunTagT_backend (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput) :
    eagerRunTagT tagOf prims A x q s pads τ g noise rest =
      finish x.2.1 <$> (simulateQ
        (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
        (sourceProgramX prims A x)).run initial := by
  simp only [eagerRunTagT, rawProgram, simulateQ_map]
  rw [simulateQ_StateT_compose _ _ _ (fun _ _ => rfl)]
  rfl

/-- Reuse the pinned independent-uniform-pair law under an arbitrary continuation. -/
private theorem uniform_pair {α β γ : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] (next : α → β → ProbComp γ) :
    𝒟[do let a ← $ᵗ α; let b ← $ᵗ β; next a b] =
      𝒟[($ᵗ (α × β)) >>= fun z => next z.1 z.2] := by
  have h := congrArg (fun d => d >>= fun z => 𝒟[next z.1 z.2])
    (XmssSecurity.evalDist_independent_uniform_pair (α := α) (β := β))
  simpa only [← evalDist_bind, bind_assoc, pure_bind] using h

/-- Independent noise and free-slot tables preserve every compiler field and
all eager share metadata, including the first-bad lucky bit. -/
theorem eagerRunTag_eq_tables (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    𝒟[eagerRunTag tagOf prims A x q s pads τ g] =
      𝒟[do let noise ← $ᵗ (ChainNoiseIndex → HashOutput)
           let rest ← $ᵗ (RestSlot C → HashOutput)
           eagerRunTagT tagOf prims A x q s pads τ g noise rest] := by
  have hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2) := by
    simp only [TprfSecurityProof.KeyCollision, not_or, not_not] at hkeys
    exact TprfSecurityProof.slotInput_injective hkeys.1 hkeys.2
  rw [eagerRunTag_raw tagOf prims A x hi, privateRo_eq_table]
  simp only [tableExtending_empty]
  let e := Equiv.sumArrowEquivProdArrow ChainNoiseIndex (RestSlot C) HashOutput
  have hu := evalDist_map_bijective_uniform_cross (α := TableIndex C → HashOutput) e e.bijective
  have hm := congrArg (fun d => d >>= fun z =>
    𝒟[simulateQ (resolvePrivateTable (e.symm z)) (rawProgram tagOf prims A x q s pads τ g)]) hu
  simp only [← evalDist_bind, bind_map_left, Equiv.symm_apply_apply] at hm
  rw [hm, uniform_pair (fun noise rest => eagerRunTagT tagOf prims A x q s pads τ g noise rest)]
  rfl


/-- The initial fiber table does not depend on the type of bad metadata. -/
theorem fiberTable_init_bad {B B' : Type} (τ : CPoint → Digest)
    (u : C.Term × CPoint → HashOutput) :
    SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init (B := B)) u =
      SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init (B := B')) u := rfl

end ThresholdLeanXmssSecurity.SigningCompilerShareTables

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTables.ordinaryRaw_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTables.ordinaryRaw_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTables.backendRaw_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTables.backendRaw_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTables.programRaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTables.programRaw_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTables.eagerRunTag_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTables.eagerRunTag_raw

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTables.eagerRunTagT_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTables.eagerRunTagT_backend

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTables.eagerRunTag_eq_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTables.eagerRunTag_eq_tables
