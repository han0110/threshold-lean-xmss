import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRelease

/-! # Chain completion against an already sampled real table -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncChain
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false

/-- Port of `completion_cache_sync` to any constrained point with the visible cache fixed. -/
theorem completion_cache_sync_at (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (s : HiddenKey → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (cs : CappedCompilerState C) (sh : ShareStateT C Tag)
    (visible : HashCache C) (p : CPoint)
    (hc : CacheRelation x.1 x.2.1 s (merged x.2.1 cs sh.cache).1.1.data visible)
    (hg : ShareG g sh) (hd : DoneCached sh)
    (hv : ∀ T, visible (.prf (x.2.1 T) p.val) = some (g (T, p)))
    (target : Digest) (tag : Tag) (r : Bool × ShareStateT C Tag)
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.complete p target tag)).run sh)) :
    CacheRelation x.1 x.2.1 s (merged x.2.1 cs r.2.cache).1.1.data visible ∧
      (merged x.2.1 cs sh.cache).1.1.data.cache ≤
        (merged x.2.1 cs r.2.cache).1.1.data.cache := by
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
  refine ⟨hc.grow le_rfl grow rfl rfl ?_ ?_, grow⟩
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
    rw [ho] at hn
    cases hn

/-- A fixed-pad backend call is the existing pad step on the compiler state. -/
theorem backendT_pad (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : Point) (st : FullState C Tag) (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.pad p))))).run st =
      pure ((padStep pads p st.1.1).1, ((padStep pads p st.1.1).2, st.1.2), st.2) := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run, ordinary]
  cases hp : st.1.1.1.1.data.pads p
  · simp [padStep, merged, withCache, hp, splitRest, erase_merge_of_restFree _ _ _ hf]
  · simp [padStep, merged, withCache, hp, splitRest, erase_merge_of_restFree _ _ _ hf]

/-- Only a bottom-chain pending has the corresponding bottom-chain secret key. -/
theorem pendingKey_bottomChain (p : PendingInput) (e : XmssSecurity.LeafIndex)
    (l : XmssSecurity.ChainIndex) (d : XmssSecurity.ChainStep)
    (h : p.key = .bottomChain e l d) : p = .bottom e l d := by
  cases p <;> simp_all [PendingInput.key]

/-- A virtual constrained row is already present, with the sampled value, on the real side. -/
theorem chainRow_of_virtual (x : Keys3 C)
    (hkeys : ¬ TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (a : RealState C) (b : SourceState C × CompState C)
    (hs : SyncFields x s pads noise g rest a b) (p : CPoint)
    (hv : ∀ T, (T, p.val) ∈ (dataOf x b.2).virtual) :
    ∀ T, visibleOf a (.prf (x.2.1 T) p.val) = some (g (T, p)) := by
  intro T
  obtain ⟨v, he⟩ := Option.ne_none_iff_exists'.mp (hs.virtualSeen T p.val (hv T))
  have hvalue := realPrivate_slotValue x hkeys s pads noise g rest a.2 (visibleOf a)
    hs.realPrivate (.inl (T, p.val)) v he
  rw [realTable_constrained g rest T p] at hvalue
  simpa only [hvalue] using he

/-- Port of sourcePlantX_sync when a secret next key has already been revealed. -/
theorem sourcePlantX_sync_next (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : PendingInput) (src : SourceState C) (st : FullState C Tag) (visible : HashCache C)
    (hv : PendingValid (dataOf x st)) (hp : ∀ k, p.next = some k → src.revealed k = some (s k))
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
    have hlow : (sourceRevealDigestX (C := C) a.low).run src =
        pure (a.low.interpret s, src) := by
      rcases hv p a ha with ⟨k, hn, hl⟩ | ⟨_, hl⟩
      · simp [sourceRevealDigestX, hl, sourceRevealX, StateT.run_bind,
          StateT.run_get, StateT.run_pure, hp k hn, DeferredDigest.interpret]
      · obtain ⟨low, hl⟩ := hl
        simp [sourceRevealDigestX, hl, StateT.run_pure, DeferredDigest.interpret]
    have hinterp : a.interpret s =
        XmssSecurity.Rom.hashOutputEquivDigestPair.symm (a.high, a.low.interpret s) := rfl
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
        hlow, backendT_plant tagOf x q s pads τ g noise rest p
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
        hlow, backendT_plant tagOf x q s pads τ g noise rest p
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

/-- List port of sourcePlantsX_sync with already revealed next keys. -/
theorem sourcePlantsX_sync_next (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (pending : List PendingInput) (src : SourceState C) (st : FullState C Tag)
    (visible : HashCache C)
    (hp : ∀ p ∈ pending, (∀ k, p.next = some k → src.revealed k = some (s k)) ∧
      src.revealed p.key = some (s p.key))
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
    have hhead := sourcePlantX_sync_next tagOf x q s pads τ g noise rest p src st visible
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

end ThresholdLeanXmssSecurity.SigningCompilerSyncChain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncChain.completion_cache_sync_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncChain.completion_cache_sync_at

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncChain.backendT_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncChain.backendT_pad

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncChain.pendingKey_bottomChain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncChain.pendingKey_bottomChain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncChain.chainRow_of_virtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncChain.chainRow_of_virtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncChain.sourcePlantX_sync_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncChain.sourcePlantX_sync_next

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncChain.sourcePlantsX_sync_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncChain.sourcePlantsX_sync_next
