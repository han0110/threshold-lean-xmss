import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncFrame
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncReal
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncStop

/-! # Opening release against the visible real table

Opening pendings have public low halves. Completing their PRF row and planting
their allocated inputs preserves the compiler's visible-cache relation.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncRelease
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false

theorem key_opening_next (p : PendingInput) (lay : Layer) (e : KeyIndex)
    (h : p.key = .opening lay e) : p.next = none := by
  exact PendingInput.next_none_of_opening p lay e h

theorem plant_low_known (data : DeferredState C) (h : PendingValid data)
    (p : PendingInput) (a : DeferredOutput) (ha : data.pending p = some a)
    (lay : Layer) (e : KeyIndex) (hk : p.key = .opening lay e) :
    ∃ d, a.low = .known d := by
  rcases h p a ha with ⟨k, hn, _⟩ | ⟨_, hl⟩
  · rw [key_opening_next p lay e hk] at hn
    cases hn
  · exact hl

/-- Pointwise extension of both visible caches, with unchanged symbolic cells. -/
theorem _root_.ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.CacheRelation.grow
    {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data nextData : DeferredState C}
    {visible nextVisible : HashCache C} (h : CacheRelation P seeds s data visible)
    (hv : visible ≤ nextVisible) (hd : data.cache ≤ nextData.cache)
    (hp : nextData.pending = data.pending) (ht : nextData.virtual = data.virtual)
    (hnewD : ∀ q v, data.cache q = none → nextData.cache q = some v →
      nextVisible q = some v)
    (hnewV : ∀ q v, visible q = none → nextVisible q = some v →
      nextData.cache q = some v) : CacheRelation P seeds s nextData nextVisible := by
  refine ⟨?_, ?_⟩
  · intro q hq
    cases hn : nextData.cache q with
    | some value =>
      cases ho : data.cache q with
      | none => exact hnewD q value ho hn
      | some old =>
        have he : old = value := Option.some.inj ((hd ho).symm.trans hn)
        subst old
        exact hv (h.cache_le ho)
    | none =>
      have ho : data.cache q = none := by
        cases hc : data.cache q with
        | none => rfl
        | some value => have he := hd hc; rw [hn] at he; cases he
      have hnot : ¬SuspendedQuery P seeds s data q := by
        simpa only [SuspendedQuery, hn, ho, hp, ht] using hq
      have hv0 : visible q = none := (h.agree q hnot).trans ho
      cases hc : nextVisible q with
      | none => rfl
      | some value => have he := hnewV q value hv0 hc; rw [hn] at he; cases he
  · intro p value hvalue
    rw [hp] at hvalue
    exact hv (h.pending p value hvalue)

/-- The public fill frame applies to arbitrary draws and bad metadata. -/
theorem doneCached_fill {B : Type} (draw : C.Term × CPoint → ProbComp HashOutput)
    (sh : SigningShareLazy.ShareState C.Term CPoint B) (h : DoneCached sh)
    (p : CPoint) (todo : List C.Term)
    (r : SigningShareLazy.ShareState C.Term CPoint B)
    (hr : r ∈ support (SigningShareLazy.fillTerms draw p todo sh)) : DoneCached r := by
  obtain ⟨hd, _, hkeep, _, _⟩ := fillTerms_frame draw p todo sh r hr
  intro point hp T
  have hn := h point (hd ▸ hp) T
  cases hc : sh.cache (T, point) with
  | none => exact (hn hc).elim
  | some value => rw [hkeep _ _ hc]; exact Option.some_ne_none _

/-- Generic-tag eager port of `SigningCompilerShare.doneCached_lazy`. -/
theorem eagerImpl_doneCached (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (sh : ShareStateT C Tag) (h : DoneCached sh)
    (t : SigningShareLazy.ShareQuery C.Term CPoint Tag)
    (r : SigningShareLazy.ShareSpec C.Term CPoint Tag t × ShareStateT C Tag)
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g t).run sh)) :
    DoneCached r.2 := by
  cases t with
  | view =>
    simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      mem_support_pure_iff] at hr
    subst r; exact h
  | read T p tag =>
    cases hc : sh.cache (T, p) <;>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hc, pure_bind, mem_support_pure_iff] at hr <;> subst r
    · intro point hp U
      by_cases he : (U, point) = (T, p)
      · simp [SigningShareLazy.put, he]
      · simpa [SigningShareLazy.put, Function.update_of_ne he] using h point hp U
    · exact h
  | complete p target tag =>
    by_cases hd : p ∈ sh.done
    · simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hd, if_true, mem_support_pure_iff] at hr
      subst r; exact h
    · cases hs : SigningShareLazy.slack C.terms sh p with
      | none =>
        simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
          hd, if_false, hs, mem_support_pure_iff] at hr
        subst r; exact h
      | some T =>
        simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
          hd, if_false, hs, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨filled, hf, rfl⟩ := hr
        have frames := fillTerms_frame (fun y => pure (g y)) p
          (C.terms.filter (· ≠ T)) sh filled hf
        have hdone := doneCached_fill (fun y => pure (g y)) sh h p _ filled hf
        intro point hp U
        by_cases he : (U, point) = (T, p)
        · simp [SigningShareLazy.put, he]
        · change Function.update filled.cache (T, p) _ (U, point) ≠ none
          rw [Function.update_of_ne he]
          rcases Finset.mem_insert.mp hp with hp | hp
          · subst point
            apply frames.2.2.2.2 U
            simp only [List.mem_filter, mem_terms, true_and, ne_eq, decide_eq_true_eq]
            intro hU
            exact he (Prod.ext hU rfl)
          · exact hdone point hp U

theorem backendT_doneCached (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SpecX C).Domain) (st : FullState C Tag) (h : DoneCached st.2)
    (r : SpecX C t × FullState C Tag)
    (hr : r ∈ support (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest t st)) :
    DoneCached r.2.2 := by
  apply backendT_preserves (fun _ => True) tagOf x q s pads τ g noise rest
    (fun _ sh => DoneCached sh) ?_ ?_ ?_ t trivial st h r hr
  · intro t _ cs sh h r hr; exact h
  · intro cs sh h T p tag a ha r hr; exact eagerImpl_doneCached τ g sh h _ a ha
  · intro cs sh h p target tag a ha; exact eagerImpl_doneCached τ g sh h _ a ha

/-- Completion fills every term, including when the row was already done. -/
theorem eager_complete_cached (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (sh : ShareStateT C Tag) (h : DoneCached sh) (p : CPoint) (target : Digest) (tag : Tag)
    (r : Bool × ShareStateT C Tag)
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.complete p target tag)).run sh)) :
    (∀ T, r.2.cache (T, p) ≠ none) ∧
      (∀ y v, sh.cache y = some v → r.2.cache y = some v) := by
  by_cases hd : p ∈ sh.done
  · simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      hd, if_true, mem_support_pure_iff] at hr
    subst r
    exact ⟨h p hd, fun _ _ hv => hv⟩
  · cases hs : SigningShareLazy.slack C.terms sh p with
    | none =>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hd, if_false, hs, mem_support_pure_iff] at hr
      subst r
      have hall : ∀ T ∈ C.terms, sh.cache (T, p) ≠ none := by
        simpa [SigningShareLazy.slack, List.find?_eq_none] using hs
      exact ⟨fun T => hall T (mem_terms T), fun _ _ hv => hv⟩
    | some T =>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hd, if_false, hs, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨filled, hf, rfl⟩ := hr
      have frames := fillTerms_frame (fun y => pure (g y)) p
        (C.terms.filter (· ≠ T)) sh filled hf
      have hT : sh.cache (T, p) = none := by
        simpa [SigningShareLazy.slack] using List.find?_some hs
      constructor
      · intro U
        by_cases he : U = T
        · subst U; simp [SigningShareLazy.put]
        · change Function.update filled.cache (T, p) _ (U, p) ≠ none
          rw [Function.update_of_ne (by simpa using he)]
          apply frames.2.2.2.2 U
          simp [mem_terms, he]
      · intro y v hv
        have he : y ≠ (T, p) := by
          intro he; subst y; rw [hT] at hv; cases hv
        simpa [SigningShareLazy.put, Function.update_of_ne he] using frames.2.2.1 y v hv

/-- The exact old-cache and post-slot-read cases used by opening release. -/
def VisibleAfter (x : Keys3 C) (g : C.Term × CPoint → HashOutput)
    (e : KeyIndex) (query : Query C) (old next : HashCache C) : Prop :=
  (¬IsSlot x query ∧ next = old) ∨
  (old query ≠ none ∧ next = old) ∨
  ∃ T, query = .prf (x.2.1 T) (.randomizer bottomLayer e) ∧ old query = none ∧
    next = old.cacheQuery query (g (T, ⟨.randomizer bottomLayer e,
      constrained_bottom_randomizer e⟩))

theorem VisibleAfter.grows {x : Keys3 C} {g : C.Term × CPoint → HashOutput}
    {e : KeyIndex} {query : Query C} {old next : HashCache C}
    (h : VisibleAfter x g e query old next) : old ≤ next := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨T, _, hn, rfl⟩
  · exact le_rfl
  · exact le_rfl
  · exact QueryCache.le_cacheQuery old hn

theorem readyAfter_covers (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (priv old next : HashCache C) (data : DeferredState C) (signing : TsigState C)
    (e : KeyIndex) (query : Query C)
    (hr : RealPrivate x s pads noise g rest priv old)
    (hc : CacheRelation x.1 x.2.1 s data old)
    (hv : ∀ T p, (T, p) ∈ data.virtual → old (.prf (x.2.1 T) p) ≠ none)
    (hready : ReadyAfter x.2.1 data signing e query)
    (hafter : VisibleAfter x g e query old next) :
    ∀ T, next (.prf (x.2.1 T) (.randomizer bottomLayer e)) =
      some (g (T, ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩)) := by
  have hcached (T : C.Term)
      (hn : old (.prf (x.2.1 T) (.randomizer bottomLayer e)) ≠ none) :
      old (.prf (x.2.1 T) (.randomizer bottomLayer e)) =
        some (g (T, ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩)) := by
    cases ho : old (.prf (x.2.1 T) (.randomizer bottomLayer e)) with
    | none => exact (hn ho).elim
    | some value =>
      have he := realPrivate_slotValue x hkeys s pads noise g rest priv old hr
        (.inl (T, .randomizer bottomLayer e)) value ho
      rw [realTable_constrained g rest T
        ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩] at he
      exact congrArg some he
  intro T
  rcases hready.2 T with ht | ht | ht
  · exact hafter.grows (hcached T (hv T _ ht))
  · cases hd : data.cache (.prf (x.2.1 T) (.randomizer bottomLayer e)) with
    | none => simp [hd] at ht
    | some value =>
      exact hafter.grows (hcached T (by rw [hc.cache_le hd]; exact Option.some_ne_none _))
  · rcases hafter with ⟨hn, _⟩ | ⟨hn, rfl⟩ | ⟨U, hu, _, rfl⟩
    · exact (hn ⟨.inl (T, .randomizer bottomLayer e), ht.symm⟩).elim
    · exact hcached T (ht ▸ hn)
    · have hi : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
      have he : U = T := hi (Query.prf.inj (hu.symm.trans ht)).1
      subst U
      rw [ht, QueryCache.cacheQuery_self]

theorem erase_merge_of_restFree (seeds : C.Term → HashOutput) (cache : HashCache C)
    (share : ShareCache C) (h : RestFree seeds cache) :
    erase seeds (merge seeds cache share) = cache := by
  funext query
  cases hr : route seeds query with
  | none => simp [erase, merge, hr]
  | some z => simp [erase, hr, h query z hr]

theorem splitRest_merged_of_restFree (seeds : C.Term → HashOutput)
    (cs : CappedCompilerState C) (share : ShareCache C)
    (h : RestFree seeds cs.1.1.data.cache) :
    splitRest seeds (merged seeds cs share) = cs := by
  simp only [splitRest, merged, withCache, erase_merge_of_restFree seeds _ share h]

/-- The reveal branch changes only the revealed map of the full state. -/
theorem backendT_reveal (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (k : HiddenKey) (st : FullState C Tag) (h : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inr k)))).run st =
      pure ((st.1.1.2.1 k).getD (s k),
        (((st.1.1.1, Function.update st.1.1.2.1 k
          (some ((st.1.1.2.1 k).getD (s k))), st.1.1.2.2), st.1.2), st.2)) := by
  simp [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    ordinary, SigningCappedExpectProof.cappedHybrid,
    revealImpl, StateT.run, StateT.mk, splitRest, merged, withCache,
    erase_merge_of_restFree x.2.1 _ st.2.cache h]

/-- X-source port of `sourceReveal_correct`, with the full table state framed. -/
theorem sourceRevealX_sync (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (k : HiddenKey) (src : SourceState C) (st : FullState C Tag)
    (h : RevealRelation s src st.1.1) (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (r : (Digest × SourceState C) × FullState C Tag)
    (hr : r ∈ support ((simulateQ
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      ((sourceRevealX k).run src)).run st)) :
    r.1.1 = s k ∧ RevealRelation s r.1.2 r.2.1.1 ∧
      r.1.2 = { src with revealed := Function.update src.revealed k (some (s k)) } ∧
      r.2 = (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)),
        st.1.1.2.2), st.1.2), st.2) := by
  cases hk : src.revealed k with
  | some value =>
    have he := h.2 k value hk
    subst value
    simp [sourceRevealX, hk, StateT.run_bind, StateT.run_get, StateT.run_pure] at hr
    subst r
    have hu : Function.update src.revealed k (some (s k)) = src.revealed := by
      rw [← hk, Function.update_eq_self]
    have hb : Function.update st.1.1.2.1 k (some (s k)) = st.1.1.2.1 := by
      rw [← h.1, hu]
    exact ⟨rfl, h, by rw [hu], by rw [hb]⟩
  | none =>
    have hb : st.1.1.2.1 k = none := h.1 ▸ hk
    simp [sourceRevealX, hk, revealQueryX, StateT.run_bind, StateT.run_get,
      StateT.run_modify, backendT_reveal tagOf x q s pads
      τ g noise rest k st hf, hb] at hr
    subst r
    refine ⟨rfl, ⟨congrArg (fun f => Function.update f k (some (s k))) h.1, ?_⟩,
      rfl, rfl⟩
    intro key value hv
    change Function.update src.revealed k (some (s k)) key = some value at hv
    by_cases he : key = k
    · subst key; simpa only [Function.update_self, Option.some.injEq] using hv.symm
    · rw [Function.update_of_ne he] at hv
      exact h.2 key value hv

@[simp] theorem route_hash (seeds : C.Term → HashOutput) (input : HashInput) :
    route seeds (.hash input) = none := by simp [route, key]

@[simp] theorem merge_hash (seeds : C.Term → HashOutput) (cache : HashCache C)
    (share : ShareCache C) (input : HashInput) :
    merge seeds cache share (.hash input) = cache (.hash input) := by simp [merge]

theorem erase_cacheQuery_hash (seeds : C.Term → HashOutput) (cache : HashCache C)
    (input : HashInput) (value : HashOutput) :
    erase seeds (cache.cacheQuery (.hash input) value) =
      (erase seeds cache).cacheQuery (.hash input) value := by
  funext query
  by_cases he : query = .hash input
  · subst query; simp [erase]
  · simp [erase, QueryCache.cacheQuery_of_ne _ _ he]

theorem merge_cacheQuery_hash (seeds : C.Term → HashOutput) (cache : HashCache C)
    (share : ShareCache C) (input : HashInput) (value : HashOutput) :
    merge seeds (cache.cacheQuery (.hash input) value) share =
      (merge seeds cache share).cacheQuery (.hash input) value := by
  funext query
  by_cases he : query = .hash input
  · subst query; simp
  · simp [merge, QueryCache.cacheQuery_of_ne _ _ he]

theorem backendT_complete (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : CPoint) (target : Digest) (st : FullState C Tag) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inr (p.val, target))).run st =
      (fun a => (a.1, st.1, a.2)) <$>
        (SigningShareLazy.eagerImpl C.terms τ g (.complete p target (tagOf st.1))).run st.2 := by
  simp only [shareBackendTagT, backendRaw, resolvePrivateTable_lift, eagerBackend,
    SigningCompilerUntil.fuse, shareBackendTag, p.property, dif_pos, StateT.run]
  change (fun z => (z.1.1, z.1.2, z.2)) <$>
    ((simulateQ (eagerHandlerTag τ g) (do
      let value ← shareQueryTag (.complete p target (tagOf st.1))
      pure (value, st.1))).run st.2) = _
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map, eager_share, Functor.map_map]
  rfl

theorem backendT_inspect (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : PendingInput) (st : FullState C Tag) (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.inspect p))))).run st =
      pure (st.1.1.1.1.data.pending p, st) := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run]
  rw [ordinary_uncounted x.1 x.2.1 q s pads (.inspect p)
    (by exact not_false) (by intro p; simp)]
  simp [compilerImpl, deferredImpl, StateT.run, splitRest_merged_of_restFree _ _ _ hf]
  rfl

theorem backendT_plant (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : PendingInput) (input : Digest) (value : HashOutput) (st : FullState C Tag)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.plant (.pending x.1 p input) value))))).run st =
      match st.1.1.1.1.data.cache (.hash (p.input x.1 input)) with
      | some prior => pure (decide (prior = value), st)
      | none => pure (true, ((withCache st.1.1
          (st.1.1.1.1.data.cache.cacheQuery (.hash (p.input x.1 input)) value), st.1.2), st.2)) := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run, ordinary_plant]
  simp only [merged, withCache, PlantInput.query, merge_hash]
  cases hc : st.1.1.1.1.data.cache (.hash (p.input x.1 input)) <;>
    simp [splitRest, withCache, erase_cacheQuery_hash,
      erase_merge_of_restFree _ _ st.2.cache hf]

/-- Completing one row leaves every other row untouched. -/
theorem eager_complete_outside (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (sh : ShareStateT C Tag) (p : CPoint) (target : Digest) (tag : Tag)
    (r : Bool × ShareStateT C Tag)
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.complete p target tag)).run sh)) :
    ∀ y, y.2 ≠ p → r.2.cache y = sh.cache y := by
  by_cases hd : p ∈ sh.done
  · simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      hd, if_true, mem_support_pure_iff] at hr
    subst r; exact fun _ _ => rfl
  · cases hs : SigningShareLazy.slack C.terms sh p with
    | none =>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hd, if_false, hs, mem_support_pure_iff] at hr
      subst r; exact fun _ _ => rfl
    | some T =>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hd, if_false, hs, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨filled, hf, rfl⟩ := hr
      have frames := fillTerms_frame (fun y => pure (g y)) p
        (C.terms.filter (· ≠ T)) sh filled hf
      intro y hy
      have he : y ≠ (T, p) := fun he => hy (congrArg Prod.snd he)
      simpa [SigningShareLazy.put, Function.update_of_ne he] using frames.2.2.2.1 y (Or.inl hy)

theorem completion_cache_sync (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (s : HiddenKey → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (cs : CappedCompilerState C) (sh : ShareStateT C Tag)
    (old next : HashCache C) (e : KeyIndex) (query : Query C)
    (hc : CacheRelation x.1 x.2.1 s (merged x.2.1 cs sh.cache).1.1.data old)
    (hg : ShareG g sh) (hd : DoneCached sh)
    (ha : VisibleAfter x g e query old next)
    (hv : ∀ T, next (.prf (x.2.1 T) (.randomizer bottomLayer e)) =
      some (g (T, ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩)))
    (target : Digest) (tag : Tag) (r : Bool × ShareStateT C Tag)
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.complete ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩ target tag)).run sh)) :
    CacheRelation x.1 x.2.1 s (merged x.2.1 cs r.2.cache).1.1.data next ∧
      (merged x.2.1 cs sh.cache).1.1.data.cache ≤
        (merged x.2.1 cs r.2.cache).1.1.data.cache ∧
      SigningGuessProof.RandomizerCached x.2.1
        (merged x.2.1 cs r.2.cache).1.1.data.cache e := by
  let p : CPoint := ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩
  have hfilled := eager_complete_cached τ g sh hd p target tag r hr
  have hg' := eagerImpl_shareG τ g (.complete p target tag) sh hg r hr
  have hout := eager_complete_outside τ g sh p target tag r hr
  have grow : (merged x.2.1 cs sh.cache).1.1.data.cache ≤
      (merged x.2.1 cs r.2.cache).1.1.data.cache := by
    intro query value hvalue
    change merge x.2.1 cs.1.1.data.cache r.2.cache query = some value
    change merge x.2.1 cs.1.1.data.cache sh.cache query = some value at hvalue
    cases hrout : route x.2.1 query <;> simp only [merge, hrout] at hvalue ⊢
    · exact hvalue
    · exact hfilled.2 _ _ hvalue
  have row (T : C.Term) : (merged x.2.1 cs r.2.cache).1.1.data.cache
      (.prf (x.2.1 T) (.randomizer bottomLayer e)) = some (g (T, p)) := by
    change merge x.2.1 cs.1.1.data.cache r.2.cache (key x.2.1 (T, p)) = _
    rw [merge_key x.2.1 hinj]
    cases hv : r.2.cache (T, p) with
    | none => exact (hfilled.1 T hv).elim
    | some value => exact congrArg some (hg' _ _ hv)
  refine ⟨hc.grow ha.grows grow rfl rfl ?_ ?_, grow, ?_⟩
  · intro other value ho hn
    change merge x.2.1 cs.1.1.data.cache sh.cache other = none at ho
    change merge x.2.1 cs.1.1.data.cache r.2.cache other = some value at hn
    cases hrout : route x.2.1 other with
    | none =>
      simp only [merge, hrout] at hn ho
      rw [ho] at hn
      cases hn
    | some z =>
      have he := (route_spec x.2.1 hinj other z).mp hrout
      simp only [merge, hrout] at ho hn
      have hp : z.2 = p := by
        by_contra hp
        rw [hout z hp, ho] at hn
        cases hn
      rcases z with ⟨T, point⟩
      simp only at hp
      subst point
      rw [he]
      exact (hv T).trans (congrArg some (hg' _ _ hn).symm)
  · intro other value ho hn
    rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨T, hquery, _, rfl⟩
    · rw [ho] at hn; cases hn
    · rw [ho] at hn; cases hn
    · by_cases he : other = query
      · subst other
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hn
        subst value
        rw [hquery]
        exact row T
      · rw [QueryCache.cacheQuery_of_ne _ _ he, ho] at hn
        cases hn
  · intro T; exact ⟨g (T, p), row T⟩

theorem restFree_cacheQuery_hash (seeds : C.Term → HashOutput) (cache : HashCache C)
    (h : RestFree seeds cache) (input : HashInput) (value : HashOutput) :
    RestFree seeds (cache.cacheQuery (.hash input) value) := by
  intro query z hz
  have hn : query ≠ .hash input := by
    intro he; subst query; rw [route_hash] at hz; cases hz
  rw [QueryCache.cacheQuery_of_ne _ _ hn]
  exact h query z hz

abbrev dataOf (x : Keys3 C) (st : FullState C Tag) : DeferredState C :=
  (merged x.2.1 st.1.1 st.2.cache).1.1.data

abbrev cacheState (st : FullState C Tag) (cache : HashCache C) : FullState C Tag :=
  ((withCache st.1.1 cache, st.1.2), st.2)

/-- Terminal X planting is the cache-only port of `sourcePlant_terminal_frame`;
the coupled pending value also makes its consistency check succeed. -/
theorem sourcePlantX_sync (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : PendingInput) (src : SourceState C) (st : FullState C Tag) (visible : HashCache C)
    (hv : PendingValid (dataOf x st)) (hp : p.next = none)
    (hk : src.revealed p.key = some (s p.key))
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) visible)
    (r : (Unit × SourceState C) × FullState C Tag)
    (hr : r ∈ support ((simulateQ
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      ((sourcePlantX x.1 p).run src)).run st)) :
    r.1.2 = src ∧ r.2 = cacheState st r.2.1.1.1.1.data.cache ∧
      CacheRelation x.1 x.2.1 s (dataOf x r.2) visible ∧
      (dataOf x st).cache ≤ (dataOf x r.2).cache ∧
      RestFree x.2.1 r.2.1.1.1.1.data.cache ∧
      ∀ a, (dataOf x st).pending p = some a →
        (dataOf x r.2).cache (.hash (p.input x.1 (s p.key))) = some (a.interpret s) := by
  cases ha : (dataOf x st).pending p with
  | none =>
    change st.1.1.1.1.data.pending p = none at ha
    simp [sourcePlantX, StateT.run_bind, deferredQueryX, backendT_inspect tagOf x q s pads
      τ g noise rest p st hf, ha, StateT.run_pure] at hr
    subst r
    exact ⟨rfl, rfl, hc, le_rfl, hf, fun _ h => by cases h⟩
  | some a =>
    obtain ⟨low, hlow⟩ : ∃ low, a.low = .known low := by
      rcases hv p a ha with ⟨k, hn, _⟩ | ⟨_, hlow⟩
      · rw [hp] at hn; cases hn
      · exact hlow
    have hinterp : a.interpret s =
        XmssSecurity.Rom.hashOutputEquivDigestPair.symm (a.high, low) := by
      simp [DeferredOutput.interpret, hlow, DeferredDigest.interpret]
    have hvalue := hc.pending p a ha
    change st.1.1.1.1.data.pending p = some a at ha
    cases hcache : st.1.1.1.1.data.cache (.hash (p.input x.1 (s p.key))) with
    | some prior =>
      have hprior : prior = a.interpret s := by
        have hh : (dataOf x st).cache (.hash (p.input x.1 (s p.key))) = some prior := by
          simpa [dataOf, merged, withCache] using hcache
        exact Option.some.inj ((hc.cache_le hh).symm.trans hvalue)
      simp [sourcePlantX, StateT.run_bind, deferredQueryX, backendT_inspect tagOf x q s pads
        τ g noise rest p st hf, ha, sourceRevealX, StateT.run_get, hk, StateT.run_pure,
        sourceRevealDigestX, hlow, backendT_plant tagOf x q s pads τ g noise rest p
          (s p.key) _ st hf, hcache, hprior, hinterp, StateT.run_modify] at hr
      subst r
      refine ⟨rfl, rfl, hc, le_rfl, hf, ?_⟩
      intro b hb
      have he : a = b := Option.some.inj hb
      subst b
      simpa [dataOf, merged, withCache, hprior] using hcache
    | none =>
      simp [sourcePlantX, StateT.run_bind, deferredQueryX, backendT_inspect tagOf x q s pads
        τ g noise rest p st hf, ha, sourceRevealX, StateT.run_get, hk, StateT.run_pure,
        sourceRevealDigestX, hlow, backendT_plant tagOf x q s pads τ g noise rest p
          (s p.key) _ st hf, hcache, StateT.run_modify] at hr
      subst r
      have hd : dataOf x (cacheState st (st.1.1.1.1.data.cache.cacheQuery
          (.hash (p.input x.1 (s p.key))) (a.interpret s))) =
          { dataOf x st with cache := ((dataOf x st).cache.cacheQuery
            (.hash (p.input x.1 (s p.key))) (a.interpret s)) } := by
        simp [dataOf, withCache, merged, merge_cacheQuery_hash]
      rw [← hinterp]
      refine ⟨rfl, rfl, ?_, ?_, restFree_cacheQuery_hash _ _ hf _ _, ?_⟩
      · rw [hd]; exact hc.materialize _ _ hvalue
      · rw [hd]; apply QueryCache.le_cacheQuery
        simpa [dataOf, merged, withCache] using hcache
      · intro b hb
        have he : a = b := Option.some.inj hb
        subst b
        simp only [hd, QueryCache.cacheQuery_self]

def runX {α : Type} (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (oa : SourceMX C α) (src : SourceState C) (st : FullState C Tag) :
    ProbComp ((α × SourceState C) × FullState C Tag) :=
  (simulateQ backend (oa.run src)).run st

theorem runX_bind {α β : Type}
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (oa : SourceMX C α) (next : α → SourceMX C β) (src : SourceState C) (st : FullState C Tag) :
    runX backend (oa >>= next) src st = runX backend oa src st >>= fun r =>
      runX backend (next r.1.1) r.1.2 r.2 := by
  simp only [runX, StateT.run_bind, simulateQ_bind]

@[simp] theorem runX_pure {α : Type}
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (a : α) (src : SourceState C) (st : FullState C Tag) :
    runX backend (pure a) src st = pure ((a, src), st) := by
  simp [runX, StateT.run_pure]

/-- Finite allocated terminal plants preserve all control fields and cover every
pending in their list. This is the X analogue of `sourcePlants_terminal_slack`. -/
theorem sourcePlantsX_sync (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (pending : List PendingInput) (src : SourceState C) (st : FullState C Tag)
    (visible : HashCache C)
    (hp : ∀ p ∈ pending, p.next = none ∧ src.revealed p.key = some (s p.key))
    (hv : PendingValid (dataOf x st)) (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) visible)
    (r : (List Unit × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (pending.mapM (sourcePlantX x.1)) src st)) :
    r.1.2 = src ∧ r.2 = cacheState st r.2.1.1.1.1.data.cache ∧
      CacheRelation x.1 x.2.1 s (dataOf x r.2) visible ∧
      (dataOf x st).cache ≤ (dataOf x r.2).cache ∧
      RestFree x.2.1 r.2.1.1.1.1.data.cache ∧
      ∀ p ∈ pending, ∀ a, (dataOf x st).pending p = some a →
        (dataOf x r.2).cache (.hash (p.input x.1 (s p.key))) = some (a.interpret s) := by
  induction pending generalizing src st r with
  | nil =>
    simp only [List.mapM_nil, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨rfl, rfl, hc, le_rfl, hf, fun _ h => by cases h⟩
  | cons p ps ih =>
    simp only [List.mapM_cons, runX_bind, mem_support_bind_iff] at hr
    obtain ⟨a, ha, b, hb, hr⟩ := hr
    rw [runX_pure, mem_support_pure_iff] at hr
    subst r
    have hhead := sourcePlantX_sync tagOf x q s pads τ g noise rest p src st visible
      hv (hp p (List.mem_cons_self ..)).1 (hp p (List.mem_cons_self ..)).2 hf hc a ha
    have hpending : (dataOf x a.2).pending = (dataOf x st).pending := by
      rw [hhead.2.1]; rfl
    have hv' : PendingValid (dataOf x a.2) := by
      intro p value hvp
      rw [hpending] at hvp
      exact hv p value hvp
    have htail := ih a.1.2 a.2 (by
      intro p hp'
      rw [hhead.1]
      exact hp p (List.mem_cons_of_mem _ hp')) hv' hhead.2.2.2.2.1 hhead.2.2.1 b hb
    refine ⟨htail.1.trans hhead.1, ?_, htail.2.2.1,
      hhead.2.2.2.1.trans htail.2.2.2.1, htail.2.2.2.2.1, ?_⟩
    · rw [htail.2.1, hhead.2.1]
      rfl
    · intro key hkey value hvalue
      rcases List.mem_cons.mp hkey with he | he
      · subst key
        exact htail.2.2.2.1 (hhead.2.2.2.2.2 value hvalue)
      · exact htail.2.2.2.2.2 key he value (hpending ▸ hvalue)

@[simp] theorem runX_get
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (src : SourceState C) (st : FullState C Tag) :
    runX backend get src st = pure ((src, src), st) := by simp [runX, StateT.run_get]

@[simp] theorem runX_modify
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (f : SourceState C → SourceState C) (src : SourceState C) (st : FullState C Tag) :
    runX backend (modify f) src st = pure (((), f src), st) := by
  simp [runX, StateT.run_modify]

theorem runX_complete (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : CPoint) (target : Digest) (src : SourceState C) (st : FullState C Tag) :
    runX (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (liftM (completeQ (C := C) p.val target)) src st =
      (fun a => ((a.1, src), st.1, a.2)) <$>
        (SigningShareLazy.eagerImpl C.terms τ g (.complete p target (tagOf st.1))).run st.2 := by
  simp [runX, completeQ]
  rw [backendT_complete tagOf x q s pads τ g noise rest p target st]
  simp only [Functor.map_map]

theorem eager_complete_null (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (sh : ShareStateT C (Bool × Bool)) (hb : sh.bad = none)
    (p : CPoint) (target : Digest) (cap : Bool) (r : Bool × ShareStateT C (Bool × Bool))
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.complete p target (false, cap))).run sh)) :
    r.2.bad = none ∨ NullBad r.2 := by
  by_cases hd : p ∈ sh.done
  · simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      hd, if_true, mem_support_pure_iff] at hr
    subst r; exact Or.inl hb
  · cases hs : SigningShareLazy.slack C.terms sh p with
    | none =>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hd, if_false, hs, mem_support_pure_iff] at hr
      subst r
      exact Or.inr ⟨cap, .complete, false, by simp [hb]⟩
    | some T =>
      simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
        hd, if_false, hs, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨filled, _, rfl⟩ := hr
      by_cases he : target = τ p
      · exact Or.inl (by simp [hb, he])
      · exact Or.inr ⟨cap, .complete, false, by simp [hb, he]⟩

def openedState (s : HiddenKey → Digest) (e : KeyIndex) (st : FullState C Tag)
    (cache : HashCache C) (sh : ShareStateT C Tag) : FullState C Tag :=
  ((withCache (st.1.1.1, Function.update st.1.1.2.1 (.opening bottomLayer e)
      (some (s (.opening bottomLayer e))), st.1.1.2.2) cache, st.1.2), sh)

/-- Exact compiler-only frame and cache facts after P. -/
structure ReleasePost (x : Keys3 C) (s : HiddenKey → Digest) (e : KeyIndex)
    (visible : HashCache C) (src : SourceState C) (st : CompState C)
    (src' : SourceState C) (st' : CompState C) : Prop where
  source : src' = { src with
    revealed := Function.update src.revealed (.opening bottomLayer e) (some (s (.opening bottomLayer e)))
    consistent := src'.consistent }
  backend : st' = openedState s e st st'.1.1.1.1.data.cache st'.2
  reveal : RevealRelation s src' st'.1.1
  cache : CacheRelation x.1 x.2.1 s (dataOf x st') visible
  grows : (dataOf x st).cache ≤ (dataOf x st').cache
  released : ReleasedPending x.1 s src' (dataOf x st')
  randomizer : SigningGuessProof.RandomizerCached x.2.1 (dataOf x st').cache e
  bad : st'.2.bad = none ∨ NullBad st'.2

theorem releaseOpening_post (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (query : Query C) (src : SourceState C) (st : CompState C)
    (old visible : HashCache C)
    (hmark : st.1.2 = false) (hunrev : src.revealed (.opening bottomLayer e) = none)
    (hrev : RevealRelation s src st.1.1)
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) old)
    (hrel : ReleasedPending x.1 s src (dataOf x st))
    (hp : PendingValid (dataOf x st))
    (halloc : ∀ p, (dataOf x st).pending p ≠ none → p ∈ src.allocated)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hg : ShareG g st.2) (hd : DoneCached st.2) (hb : st.2.bad = none)
    (hafter : VisibleAfter x g e query old visible)
    (hrow : ∀ T, visible (.prf (x.2.1 T) (.randomizer bottomLayer e)) =
      some (g (T, ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩)))
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX
      (shareBackendTagT SigningCompilerShareCap.capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceReleaseOpeningX x.1 x.2.1 e) src st)) :
    ReleasePost x s e visible src st r.1.2 r.2 := by
  let k := HiddenKey.opening bottomLayer e
  let p : CPoint := ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩
  simp only [sourceReleaseOpeningX, runX_bind, runX_get, pure_bind, hunrev,
    Option.isNone_none, if_true, runX_modify, runX_pure, mem_support_bind_iff,
    mem_support_pure_iff] at hr
  obtain ⟨revealed, hrrev, completed, hrcomp, planted, hrplant, rfl⟩ := hr
  have hR := sourceRevealX_sync SigningCompilerShareCap.capTag x q s pads τ g noise rest
    k src st hrev hf revealed hrrev
  have heq : revealed = ((s k, { src with revealed := Function.update src.revealed k (some (s k)) }),
      (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2), st.2)) :=
    Prod.ext (Prod.ext hR.1 hR.2.2.1) hR.2.2.2
  subst revealed
  rw [runX_complete SigningCompilerShareCap.capTag x q s pads τ g noise rest p] at hrcomp
  simp only [support_map] at hrcomp
  obtain ⟨a, ha, rfl⟩ := hrcomp
  have hcomp := completion_cache_sync x hinj s τ g st.1.1 st.2 old visible e query
    hc hg hd hafter hrow (s k) (SigningCompilerShareCap.capTag
      ((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2)) a ha
  have hbad := eager_complete_null τ g st.2 hb p (s k) st.1.1.2.2 a (by
    change a ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.complete p (s k) (st.1.2, st.1.1.2.2))).run st.2) at ha
    rw [hmark] at ha
    exact ha)
  let srcC : SourceState C := { src with
    revealed := Function.update src.revealed k (some (s k))
    consistent := src.consistent && a.1 }
  let stC : CompState C :=
    (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2), a.2)
  have hplants := sourcePlantsX_sync SigningCompilerShareCap.capTag x q s pads τ g noise rest
    (src.allocated.filter (fun pending => pending.key = k)) srcC stC visible (by
      intro pending hmem
      have hkey : pending.key = k := of_decide_eq_true (List.mem_filter.mp hmem).2
      refine ⟨key_opening_next pending bottomLayer e hkey, ?_⟩
      change Function.update src.revealed k (some (s k)) pending.key = some (s pending.key)
      rw [hkey, Function.update_self]) (by exact hp) hf (by exact hcomp.1) planted hrplant
  have hsrc : planted.1.2 = { src with
      revealed := Function.update src.revealed k (some (s k))
      consistent := src.consistent && a.1 } := hplants.1
  have hstate : planted.2 = openedState s e st planted.2.1.1.1.1.data.cache a.2 := hplants.2.1
  have hpend : (dataOf x planted.2).pending = (dataOf x st).pending := by
    rw [hstate]; rfl
  have hgrow : (dataOf x st).cache ≤ (dataOf x planted.2).cache :=
    hcomp.2.1.trans hplants.2.2.2.1
  refine ⟨?_, ?_, ?_, hplants.2.2.1, hgrow, ?_, ?_, ?_⟩
  · rw [hsrc]
  · rw [hstate]; rfl
  · rw [hsrc, hstate]
    exact hR.2.1
  · intro pending value hvalue hreleased
    rw [hpend] at hvalue
    by_cases he : pending.key = k
    · apply hplants.2.2.2.2.2 pending ?_ value hvalue
      exact List.mem_filter.mpr ⟨halloc pending (by rw [hvalue]; exact Option.some_ne_none _),
        by simpa only [decide_eq_true_eq] using he⟩
    · have hold : src.revealed pending.key ≠ none := by
        rw [hsrc] at hreleased
        simpa only [Function.update_of_ne he] using hreleased
      exact hgrow (hrel pending value hvalue hold)
  · intro T
    obtain ⟨value, hv⟩ := hcomp.2.2 T
    exact ⟨value, hplants.2.2.2.1 hv⟩
  · rw [hstate]
    exact hbad

abbrev visibleOf (a : RealState C) : HashCache C := a.1.1.1.1.1.1.1

/-- C1–C3, C5–C8, C9.trace, and C10–C15 of the local synchronization contract.
C4 and C9.count are separated so P can use its post-real-read visible cache. -/
structure SyncFields (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (b : SourceState C × CompState C) : Prop where
  corrupt : b.1.signing.corrupt = a.1.2.1.1.corrupt
  bound : b.1.signing.bound = a.1.2.1.1.bound
  released : b.1.signing.released = a.1.2.1.1.released
  exposed : b.1.exposed = a.1.2.2.1
  candidates : b.1.candidates = a.1.2.2.2
  flag : b.1.hiddenFlag = a.1.2.1.2
  reveal : RevealRelation s b.1 b.2.1.1
  releasedPending : ReleasedPending x.1 s b.1 (dataOf x b.2)
  opening : OpeningRelation x.2.1 s b.1 (dataOf x b.2) (visibleOf a)
  pendingValid : PendingValid (dataOf x b.2)
  allocated : ∀ p, (dataOf x b.2).pending p ≠ none → p ∈ b.1.allocated
  virtualSeen : ∀ T p, (T, p) ∈ (dataOf x b.2).virtual →
    visibleOf a (.prf (x.2.1 T) p) ≠ none
  compilerBound : b.2.1.1.1.1.bound = b.1.signing.bound
  trace : a.1.1.2 = b.2.1.1.1.1.trace
  bad : b.2.2.bad = none
  share : ShareG g b.2.2
  restAgree : RestAgree x rest b.2.1.1
  restFree : RestFree x.2.1 b.2.1.1.1.1.data.cache
  realPrivate : RealPrivate x s pads noise g rest a.2 (visibleOf a)
  frontier : ∀ edge, (dataOf x b.2).pending (chainPending edge) = none →
    b.1.revealed (chainPending edge).key = none
  candidatesPaid : ∀ c ∈ b.1.candidates, c.2 = s c.1 → b.1.revealed c.1 ≠ none
  doneCached : DoneCached b.2.2

def SyncWithoutCount (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (b : SourceState C × CompState C) : Prop :=
  SyncFields x s pads noise g rest a b ∧
    CacheRelation x.1 x.2.1 s (dataOf x b.2) (visibleOf a)

def SyncCore (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (b : SourceState C × CompState C) : Prop :=
  SyncWithoutCount x s pads noise g rest a b ∧ a.1.1.1.1.1.1.2 = b.2.1.1.1.2

structure LocalFrame (x : Keys3 C) (a a' : RealState C)
    (b b' : SourceState C × CompState C) : Prop where
  realSigning : a'.1.2.1.1 = a.1.2.1.1
  realExposed : a'.1.2.2.1 = a.1.2.2.1
  visible : visibleOf a ≤ visibleOf a'
  signing : b'.1.signing = b.1.signing
  trees : b'.1.trees = b.1.trees
  exposed : b'.1.exposed = b.1.exposed
  allocated : b'.1.allocated = b.1.allocated
  pending : (dataOf x b'.2).pending = (dataOf x b.2).pending
  virtual : (dataOf x b'.2).virtual = (dataOf x b.2).virtual
  cache : (dataOf x b.2).cache ≤ (dataOf x b'.2).cache
  revealed : ∀ k, (∀ e, k ≠ .opening bottomLayer e) → b'.1.revealed k = b.1.revealed k

theorem simulate_doneCached {α : Type}
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (oa : OracleComp (SpecX C) α) (st : FullState C Tag) (h : DoneCached st.2)
    (r : α × FullState C Tag)
    (hr : r ∈ support ((simulateQ
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) oa).run st)) :
    DoneCached r.2.2 := by
  apply simulateQ_sticky _ (fun fs => DoneCached fs.2) ?_ oa st h r hr
  intro t st h r hr
  exact backendT_doneCached tagOf x q s pads τ g noise rest t st h r hr

theorem chainPending_key_ne_opening (edge : ChainNoiseIndex) (e : KeyIndex) :
    (chainPending edge).key ≠ .opening bottomLayer e := by
  rcases edge with ⟨l, key | b, p⟩ <;> simp [chainPending, PendingInput.key]

theorem ReleasePost.localFrame (x : Keys3 C) (s : HiddenKey → Digest) (e : KeyIndex)
    (a : RealState C) (src src' : SourceState C) (st st' : CompState C)
    (h : ReleasePost x s e (visibleOf a) src st src' st') :
    LocalFrame x a a (src, st) (src', st') := by
  refine ⟨rfl, rfl, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, h.grows, ?_⟩
  · rw [h.source]
  · rw [h.source]
  · rw [h.source]
  · rw [h.source]
  · rw [h.backend]; rfl
  · rw [h.backend]; rfl
  · intro key hk
    rw [h.source]
    exact Function.update_of_ne (hk e) _ _

theorem ReleasePost.syncFields (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (e : KeyIndex) (a : RealState C)
    (src src' : SourceState C) (st st' : CompState C)
    (hs : SyncFields x s pads noise g rest a (src, st))
    (h : ReleasePost x s e (visibleOf a) src st src' st')
    (hf : Frame x rest st'.1.1 ∧ ShareG g st'.2)
    (hd : DoneCached st'.2) (hb : st'.2.bad = none) :
    SyncFields x s pads noise g rest a (src', st') := by
  have frame := h.localFrame x s e a src src' st st'
  have hsign : src'.signing = src.signing := frame.signing
  have hrev : src'.revealed = Function.update src.revealed (.opening bottomLayer e)
      (some (s (.opening bottomLayer e))) := congrArg SourceState.revealed h.source
  have hbound : st'.1.1.1.1.bound = st.1.1.1.1.bound := by rw [h.backend]; rfl
  have htrace : st'.1.1.1.1.trace = st.1.1.1.1.trace := by rw [h.backend]; rfl
  refine {
    corrupt := ?_, bound := ?_, released := ?_, exposed := ?_, candidates := ?_, flag := ?_
    reveal := h.reveal, releasedPending := h.released, opening := ?_
    pendingValid := hf.1.2.2, allocated := ?_, virtualSeen := ?_, compilerBound := ?_
    trace := ?_, bad := hb, share := hf.2, restAgree := hf.1.1, restFree := hf.1.2.1
    realPrivate := hs.realPrivate, frontier := ?_, candidatesPaid := ?_, doneCached := hd }
  · rw [hsign]; exact hs.corrupt
  · rw [hsign]; exact hs.bound
  · rw [hsign]; exact hs.released
  · rw [frame.exposed]; exact hs.exposed
  · have he := congrArg SourceState.candidates h.source
    exact he.trans hs.candidates
  · have he := congrArg SourceState.hiddenFlag h.source
    exact he.trans hs.flag
  · refine ⟨hs.opening.actualValue, ?_⟩
    intro other ho
    by_cases he : other = e
    · subst other; exact h.randomizer
    · have hk : HiddenKey.opening bottomLayer other ≠ .opening bottomLayer e := by simpa using he
      rw [hrev, Function.update_of_ne hk] at ho
      intro T
      obtain ⟨value, hv⟩ := hs.opening.released other ho T
      exact ⟨value, h.grows hv⟩
  · intro pending hp
    rw [frame.allocated]
    exact hs.allocated pending (frame.pending ▸ hp)
  · intro T p hp
    exact hs.virtualSeen T p (frame.virtual ▸ hp)
  · rw [hbound, hsign]
    exact hs.compilerBound
  · exact hs.trace.trans htrace.symm
  · intro edge hp
    rw [hrev, Function.update_of_ne (chainPending_key_ne_opening edge e)]
    exact hs.frontier edge (frame.pending ▸ hp)
  · intro candidate hc he
    have hcandidate := congrArg SourceState.candidates h.source
    change src'.candidates = src.candidates at hcandidate
    rw [hcandidate] at hc
    rw [hrev]
    by_cases hk : candidate.1 = .opening bottomLayer e
    · rw [hk, Function.update_self]; exact Option.some_ne_none _
    · rw [Function.update_of_ne hk]
      exact hs.candidatesPaid candidate hc he

/-- R6 with the real-private and virtual-seen clauses already at the post-read
visible state, as required by the intermediate P contract. -/
theorem readyAfter_covers_visible (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (priv old next : HashCache C) (data : DeferredState C) (signing : TsigState C)
    (e : KeyIndex) (query : Query C)
    (hr : RealPrivate x s pads noise g rest priv next)
    (hc : CacheRelation x.1 x.2.1 s data old)
    (hv : ∀ T p, (T, p) ∈ data.virtual → next (.prf (x.2.1 T) p) ≠ none)
    (hready : ReadyAfter x.2.1 data signing e query)
    (hafter : VisibleAfter x g e query old next) :
    ∀ T, next (.prf (x.2.1 T) (.randomizer bottomLayer e)) =
      some (g (T, ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩)) := by
  have hcached (T : C.Term)
      (hn : next (.prf (x.2.1 T) (.randomizer bottomLayer e)) ≠ none) :
      next (.prf (x.2.1 T) (.randomizer bottomLayer e)) =
        some (g (T, ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩)) := by
    cases ho : next (.prf (x.2.1 T) (.randomizer bottomLayer e)) with
    | none => exact (hn ho).elim
    | some value =>
      have he := realPrivate_slotValue x hkeys s pads noise g rest priv next hr
        (.inl (T, .randomizer bottomLayer e)) value ho
      rw [realTable_constrained g rest T
        ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩] at he
      exact congrArg some he
  intro T
  rcases hready.2 T with ht | ht | ht
  · exact hcached T (hv T _ ht)
  · cases hd : data.cache (.prf (x.2.1 T) (.randomizer bottomLayer e)) with
    | none => simp [hd] at ht
    | some value =>
      exact hcached T (by rw [hafter.grows (hc.cache_le hd)]; exact Option.some_ne_none _)
  · apply hcached T
    rcases hafter with ⟨hn, _⟩ | ⟨hn, rfl⟩ | ⟨U, _, _, rfl⟩
    · exact (hn ⟨.inl (T, .randomizer bottomLayer e), ht.symm⟩).elim
    · exact ht ▸ hn
    · rw [← ht, QueryCache.cacheQuery_self]; exact Option.some_ne_none _

/-- P preserves every synchronization field except the deliberately omitted
count equality. The compiler count and trace are unchanged. -/
theorem releaseOpening_sync (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (seed : HashOutput) (a : RealState C)
    (src : SourceState C) (st : CompState C) (old : HashCache C)
    (hs : SyncFields x s pads noise g rest a (src, st))
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) old)
    (hmark : st.1.2 = false) (hunrev : src.revealed (.opening bottomLayer e) = none)
    (hready : ReadyAfter x.2.1 (dataOf x st) src.signing e
      (.prf seed (.randomizer bottomLayer e)))
    (hafter : VisibleAfter x g e (.prf seed (.randomizer bottomLayer e)) old (visibleOf a))
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support ((simulateQ
      (shareBackendTagT SigningCompilerShareCap.capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      ((sourceReleaseOpeningX x.1 x.2.1 e).run src)).run st)) :
    Stop r.2 ∨
      (SyncWithoutCount x s pads noise g rest a (r.1.2, r.2) ∧
        LocalFrame x a a (src, st) (r.1.2, r.2) ∧
        SigningGuessProof.RandomizerCached x.2.1 (dataOf x r.2).cache e ∧
        r.2.1.1.1.2 = st.1.1.1.2 ∧ r.2.1.1.1.1.trace = st.1.1.1.1.trace) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  have hi := TprfSecurityProof.slotInput_injective hinj (not_not.mp (not_or.mp hkeys).2)
  have hrow := readyAfter_covers_visible x hkeys s pads noise g rest a.2 old (visibleOf a)
    (dataOf x st) src.signing e _ hs.realPrivate hc hs.virtualSeen hready hafter
  have hp := releaseOpening_post x hinj q s pads τ g noise rest e _ src st old (visibleOf a)
    hmark hunrev hs.reveal hc hs.releasedPending hs.pendingValid hs.allocated
    hs.restFree hs.share hs.doneCached hs.bad hafter hrow r hr
  rcases hp.bad with hb | hb
  · have hf := safe_frame SigningCompilerShareCap.capTag x hi q s pads τ g noise rest
      (sourceReleaseOpeningX x.1 x.2.1 e)
      (SigningCompilerShare.safe_sourceReleaseOpeningX x.1 x.2.1 e) src st
      ⟨⟨hs.restAgree, hs.restFree, hs.pendingValid⟩, hs.share⟩ r hr
    have hd := simulate_doneCached SigningCompilerShareCap.capTag x q s pads τ g noise rest
      ((sourceReleaseOpeningX x.1 x.2.1 e).run src) st hs.doneCached r hr
    refine Or.inr ⟨⟨hp.syncFields x s pads noise g rest e a src r.1.2 st r.2 hs hf hd hb,
      hp.cache⟩, hp.localFrame x s e a src r.1.2 st r.2, hp.randomizer, ?_, ?_⟩
    · rw [hp.backend]; rfl
    · rw [hp.backend]; rfl
  · exact Or.inl (Or.inl hb)

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.releaseOpening_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms releaseOpening_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.backendT_doneCached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms backendT_doneCached

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.eager_complete_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eager_complete_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.readyAfter_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readyAfter_covers

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.sourceRevealX_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceRevealX_sync

end ThresholdLeanXmssSecurity.SigningCompilerSyncRelease
