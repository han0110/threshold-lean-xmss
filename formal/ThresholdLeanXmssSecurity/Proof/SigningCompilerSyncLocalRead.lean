import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncBackend
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRealRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTrigger
import XmssSecurity.Proof.MarginalCoupling

/-! # Ordinary local reads

Non-slot reads use the visible cache after any opening-release prefix. The
counted real call and free compiler call retain their separate trace routes.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncBackend SigningCompilerSyncRealRead
open SigningCompilerSyncTrigger SigningCompilerUntil
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  SigningLaneUnionProof.traceStepAt

theorem ordinary_routes (x : Keys3 C) (input : Query C) (hn : ¬IsSlot x input) :
    route x.2.1 input = none ∧ restRoute x.2.1 x.2.2 input = none := by
  constructor
  · apply dif_neg
    rintro ⟨⟨T, p⟩, h⟩
    exact hn ⟨.inl (T, p), h.symm⟩
  · apply dif_neg
    rintro ⟨z, h⟩
    exact hn ⟨z.val, h⟩

/-- A visible hit and a quiet miss have one common lazy-cache law. -/
theorem realRead_ordinary (x : Keys3 C) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (priv vis : HashCache C) (hr : RealPrivate x s pads noise g rest priv vis)
    (input : Query C)
    (h : (∃ value, vis input = some value) ∨ Quiet x s pads noise input) :
    ((realImpl x g rest) (.inr input)).run priv =
      (fun r => (r.1, syncPrivate x s pads noise priv r.2)) <$>
        ((Query C →ₒ HashOutput).randomOracle input).run vis := by
  rcases h with ⟨value, hv⟩ | hq
  · rw [realRead_hit x s pads noise g rest priv vis hr input value hv,
      OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hv, map_pure,
      syncPrivate_eq x s pads noise priv vis hr.quiet]
  · exact realRead_quiet x s pads noise g rest priv vis hr input hq

/-- The opening-release program tested before an ordinary hash read. -/
def ordinaryPrefix (x : Keys3 C) (input : Query C)
    (src : SourceState C) (st : CompState C) : SourceMX C Unit :=
  match input with
  | .prf _ (.randomizer lay e) =>
    if lay = bottomLayer ∧ ReadyAfter x.2.1 (dataOf x st) src.signing e input
    then sourceReleaseOpeningX x.1 x.2.1 e else pure ()
  | _ => pure ()

-- Port of TreeSim.treeSim_relTriple_support, avoiding its ceremony imports.
theorem relTriple_supported {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : α → β → Prop} (h : RelTriple oa ob R) :
    RelTriple oa ob (fun a b => R a b ∧ a ∈ support oa ∧ b ∈ support ob) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, ?_⟩
  filter_upwards [hc, ae_mem_support_prod c] with z hz hmem
  exact ⟨hz, hmem.1, hmem.2⟩

/-- A coupled marginal retains the complete states and their support facts. -/
theorem relTriple_of_projections {α β γ δ : Type} (oa : ProbComp α) (ob : ProbComp β)
    (f : α → γ) (g : β → δ) {R : γ → δ → Prop}
    (h : RelTriple (f <$> oa) (g <$> ob) R) :
    RelTriple oa ob (fun a b => R (f a) (g b) ∧ a ∈ support oa ∧ b ∈ support ob) := by
  apply relTriple_supported
  have hl : RelTriple oa (f <$> oa) (fun a b => f a = b) := by
    simpa only [id_map] using
      (relTriple_map (f := id) (g := f)
        (relTriple_post_mono (relTriple_refl oa) (fun _ _ he => congrArg f he)))
  have hr : RelTriple (g <$> ob) ob (fun a b => a = g b) := by
    simpa only [id_map] using
      (relTriple_map (f := g) (g := id)
        (relTriple_post_mono (relTriple_refl ob) (fun _ _ he => congrArg g he)))
  apply relTriple_post_mono
    (XmssSecurity.relTriple_trans_exists (XmssSecurity.relTriple_trans_exists hl h) hr)
  rintro a b ⟨_, ⟨_, rfl, hab⟩, rfl⟩
  exact hab

abbrev ReadView (C : Committee) (α : Type) :=
  α × HashCache C × (XmssSecurity.SigningCacheTrace × Bool)

/-- The visible-cache marginal of one read, including its complete trace. -/
def cacheRead (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : Query C) (call : (WorldSpec C).Domain) (signing : TsigState C)
    (trace : XmssSecurity.SigningCacheTrace × Bool) (cache : HashCache C) :
    ProbComp (ReadView C HashOutput) := do
  let r ← ((Query C →ₒ HashOutput).randomOracle input).run cache
  let before : SigningFlatProof.FlatState C := (((cache, 0), []), signing, false)
  let after : SigningFlatProof.FlatState C := (((r.2, 0), []), signing, false)
  let prefetched ← (simulateQ (Query C →ₒ HashOutput).randomOracle
    (SigningR1FixedProof.cachedExtra seeds P before call after)).run r.2
  pure (r.1, prefetched.2, SigningLaneUnionProof.traceStepAt seeds P cache signing
    call prefetched.2 trace)

theorem randomOracle_observe (cache : HashCache C) (input : Query C)
    (r : HashOutput × HashCache C)
    (hr : r ∈ support (((Query C →ₒ HashOutput).randomOracle input).run cache)) :
    cache.cacheQuery input r.1 = r.2 := by
  cases hv : cache input with
  | none =>
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hv, support_map] at hr
    obtain ⟨value, _, rfl⟩ := hr
    rfl
  | some value =>
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hv,
      mem_support_pure_iff] at hr
    subst r
    exact observe_same cache input value hv

/-- The existing deferred-read coupling, projected to its two ordinary caches. -/
theorem cacheQuery_rel (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) (input : Query C)
    (hn : ¬SuspendedQuery P seeds s data input) :
    RelTriple (((Query C →ₒ HashOutput).randomOracle input).run actual)
      (((Query C →ₒ HashOutput).randomOracle input).run data.cache)
      (fun a b => a.1 = b.1 ∧ CacheRelation P seeds s { data with cache := b.2 } a.2) := by
  have hread := relTriple_supported (relTriple_deferredHash P seeds s data actual h input hn)
  have hpost : RelTriple (((Query C →ₒ HashOutput).randomOracle input).run actual)
      ((deferredImpl (.hash input)).run data)
      (fun a b => a.1 = b.1 ∧
        CacheRelation P seeds s { data with cache := b.2.cache } a.2) := by
    apply relTriple_post_mono hread
    intro a b hb
    obtain ⟨⟨he, hc⟩, _, hr⟩ := hb
    simp only [deferredImpl, StateT.run, support_map] at hr
    obtain ⟨z, _, rfl⟩ := hr
    exact ⟨he, hc⟩
  have hm := relTriple_map (f := id) (g := fun b : HashOutput × DeferredState C => (b.1, b.2.cache))
    (R := fun a b : HashOutput × HashCache C => a.1 = b.1 ∧
      CacheRelation P seeds s { data with cache := b.2 } a.2)
    hpost
  simp only [deferredImpl, StateT.run, Functor.map_map, Function.comp_apply] at hm
  change RelTriple (id <$> _) (id <$> _) _ at hm
  simp only [id_map] at hm
  exact hm

/-- Both hash routes preserve the cache relation and the entire trace pair. -/
theorem cacheRead_hash_rel (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (source : SourceState C) (data : DeferredState C)
    (actual : HashCache C) (actualSigning signing : TsigState C)
    (trace : XmssSecurity.SigningCacheTrace × Bool) (input : HashInput)
    (call otherCall : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input call)
    (hother : SigningFlatProof.HashCallAt input otherCall)
    (hcache : CacheRelation P seeds s data actual)
    (hopening : OpeningRelation seeds s source data actual)
    (hreleased : ReleasedPending P s source data)
    (hsource : actualSigning.bound = source.signing.bound)
    (hbound : source.signing.bound = signing.bound)
    (hno : ∀ k, hiddenCandidate P input = some (k, s k) → source.revealed k ≠ none) :
    RelTriple (cacheRead P seeds (.hash input) call actualSigning trace actual)
      (cacheRead P seeds (.hash input) otherCall signing trace data.cache)
      (fun a b => a.1 = b.1 ∧
        CacheRelation P seeds s { data with cache := b.2.1 } a.2.1 ∧ a.2.2 = b.2.2) := by
  unfold cacheRead
  apply relTriple_bind (relTriple_supported (cacheQuery_rel P seeds s data actual hcache
    (.hash input) (hashInput_not_suspended P seeds s input source data hreleased hno)))
  intro a b hab
  obtain ⟨⟨he, hc⟩, ha, hb⟩ := hab
  have hva := (randomOracle_support (.hash input) actual a ha).2.1
  have hvb := (randomOracle_support (.hash input) data.cache b hb).2.1
  have hpost : a.2 (.hash input) = b.2 (.hash input) := by rw [hva, hvb, he]
  have hp := cachedExtra_sync P seeds s input call otherCall hcall hother source data
    (((actual, 0), []), actualSigning, false) (((a.2, 0), []), actualSigning, false)
    (((data.cache, 0), []), signing, false) (((b.2, 0), []), signing, false)
    hsource rfl hcache hopening hbound hno hpost
  dsimp only
  rw [← hp]
  apply relTriple_bind (relTriple_supported (relTriple_cachedExtra P seeds s
    (((actual, 0), []), actualSigning, false) (((a.2, 0), []), actualSigning, false)
    call { data with cache := b.2 } a.2 hc))
  intro c d hcd
  obtain ⟨⟨_, hcd⟩, _, hd⟩ := hcd
  have hdgrow := SigningGuessProof.raw_randomOracle_cache_le _ b.2 d hd
  have hdcached : d.2 (.hash input) = some b.1 := hdgrow hvb
  have hpost' : c.2 (.hash input) = d.2 (.hash input) := hcd.agree (.hash input) (by
    rintro ⟨hn, _⟩
    exact Option.some_ne_none _ (hdcached.symm.trans hn))
  apply relTriple_pure_pure
  refine ⟨he, hcd, ?_⟩
  exact traceStepAt_sync P seeds s input call otherCall hcall hother source data
    { data with cache := d.2 } actual c.2 actualSigning signing hcache hcd
    hopening hreleased hsource hbound hno hpost' trace

def realReadView {α : Type} (r : α × RealState C) : ReadView C α :=
  (r.1, visibleOf r.2, r.2.1.1.2)

def compilerReadView {α : Type} (x : Keys3 C) (r : α × CompState C) : ReadView C α :=
  (r.1, (dataOf x r.2).cache, r.2.1.1.1.1.trace)

theorem ordinary_merged_gen (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest)
    (input : Query C) (hn : ¬IsSlot x input) (st : CompState C)
    (m : CappedCompilerState C) (hm : merged x.2.1 st.1.1 st.2.cache = m)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
      (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) q s
      (.inl (.hash input))).run m)) :
    merged x.2.1 (splitRest x.2.1 r.2) st.2.cache = r.2 := by
  apply merged_split_of_agree x.2.1 hinj
  intro z
  have ht : ¬SourceWritesPrf (C := C) (x.2.1 z.1) z.2.val (.inl (.hash input)) := by
    intro he
    exact hn ⟨.inl (z.1, z.2), he.symm⟩
  have hf := cappedCompiler_prf_frame x.1 x.2.1 q s (.inl (.hash input)) m r hr (x.2.1 z.1) z.2.val ht
  refine hf.trans ?_
  rw [← hm]
  simp only [merged, withCache]
  exact merge_key x.2.1 hinj st.1.1.1.1.data.cache st.2.cache z

/-- Splitting the ordinary backend preserves its complete visible read marginal. -/
theorem compilerRead_view (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (input : Query C) (hn : ¬IsSlot x input) (st : CompState C) :
    compilerReadView x <$>
      (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest
        (.inl (.inl (.inl (.hash input))))).run st =
    cacheRead x.1 x.2.1 input (.inr (.inr (.inl input)))
      (compilerSigning st.1.1.1.1) st.1.1.1.1.trace (dataOf x st).cache := by
  obtain ⟨hroute, hrest⟩ := ordinary_routes x input hn
  rw [backendT_ordinaryHash capTag x q s pads τ g noise rest input hroute hrest st,
    Functor.map_map]
  show _ = cacheRead x.1 x.2.1 input (.inr (.inr (.inl input)))
    (compilerSigning (merged x.2.1 st.1.1 st.2.cache).1.1)
    (merged x.2.1 st.1.1 st.2.cache).1.1.trace (merged x.2.1 st.1.1 st.2.cache).1.1.data.cache
  generalize hM : merged x.2.1 st.1.1 st.2.cache = M
  have hmap :
      (fun r : HashOutput × CappedCompilerState C =>
        compilerReadView x (r.1, ((splitRest x.2.1 r.2, st.1.2), st.2))) <$>
        (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
          (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) q s
          (.inl (.hash input))).run M =
      (fun r : HashOutput × CappedCompilerState C =>
        (r.1, r.2.1.1.data.cache, r.2.1.1.trace)) <$>
        (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
          (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) q s
          (.inl (.hash input))).run M := by
    simp only [map_eq_bind_pure_comp]
    apply bind_congr_of_forall_mem_support
    intro r hr
    have hm := ordinary_merged_gen x hinj q s input hn st M hM r hr
    exact congrArg pure (Prod.ext rfl (Prod.ext (congrArg (fun z => z.1.1.data.cache) hm) rfl))
  erw [hmap]
  simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    StateT.run_mk, StateT.mk, compilerImpl, deferredImpl, StateT.run, Functor.map_map,
    bind_map_left, map_bind, map_pure, cacheRead]

theorem keyedSplit_cache_forget {α : Type}
    (keyOf : HashInput → Option XmssSecurity.LeafIndex)
    (oa : OracleComp (Query C →ₒ HashOutput) α)
    (st : (HashCache C × SigningPartnerBoundProof.Monitor) × (XmssSecurity.LeafIndex → Bool)) :
    (fun r => (r.1, r.2.1.1)) <$>
      (simulateQ (SigningOneRunProof.keyedSplitOracle keyOf) oa).run st =
      (simulateQ (Query C →ₒ HashOutput).randomOracle oa).run st.1.1 := by
  rw [← SigningFlatEagerProof.monitoredOracle_run_forget keyOf oa st.1.1 st.1.2,
    ← SigningOneRunProof.keyedSplitOracle_run_forget keyOf oa st.1 st.2,
    Functor.map_map]

theorem cachedExtra_congr (seeds : C.Term → HashOutput) (P : PublicParameter)
    (before after otherBefore otherAfter : SigningFlatProof.FlatState C)
    (call : (WorldSpec C).Domain) (hcache : before.1.1.1 = otherBefore.1.1.1)
    (hsigning : before.2.1 = otherBefore.2.1) (hafter : after.1.1.1 = otherAfter.1.1.1) :
    SigningR1FixedProof.cachedExtra seeds P before call after =
      SigningR1FixedProof.cachedExtra seeds P otherBefore call otherAfter := by
  obtain ⟨⟨⟨c1, n1⟩, l1⟩, s1, b1⟩ := before
  obtain ⟨⟨⟨c2, n2⟩, l2⟩, s2, b2⟩ := otherBefore
  obtain ⟨⟨⟨c3, n3⟩, l3⟩, s3, b3⟩ := after
  obtain ⟨⟨⟨c4, n4⟩, l4⟩, s4, b4⟩ := otherAfter
  dsimp only at hcache hsigning hafter
  subst hcache hsigning hafter
  unfold SigningR1FixedProof.cachedExtra SigningFlatEagerProof.grindExtra
  split_ifs with h1 h2 <;> try rfl
  dsimp only
  cases hs : s1.bound h2.choose with
  | none => simp only [hs]
  | some message =>
    simp only [hs]
    split <;> simp_all

theorem ordinary_not_suspended (x : Keys3 C) (s : HiddenKey → Digest)
    (data : DeferredState C) (input : Query C) (hn : ¬IsSlot x input)
    (hh : ∀ i, input ≠ .hash i) : ¬SuspendedQuery x.1 x.2.1 s data input := by
  rintro ⟨_, hp | hv⟩
  · obtain ⟨p, value, _, he⟩ := hp
    exact hh _ he
  · obtain ⟨T, p, _, he⟩ := hv
    exact hn ⟨.inl (T, p), he.symm⟩

theorem ordinary_nonhash_quiet (x : Keys3 C) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (input : Query C) (hn : ¬IsSlot x input) (hh : ∀ i, input ≠ .hash i) :
    Quiet x s pads noise input := by
  refine ⟨hn, ?_⟩
  cases hc : realCache x s pads noise input with
  | none => rfl
  | some value =>
    obtain ⟨edge, he⟩ := realCache_some_chain x s pads noise input value hc
    exact (hh _ he).elim

/-- Every ordinary read preserves the share cells and the source-independent fields. -/
theorem compilerRead_fields (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (input : Query C) (hn : ¬IsSlot x input) (st : CompState C)
    (r : HashOutput × CompState C)
    (hr : r ∈ support ((shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.hash input))))).run st)) :
    r.2.2 = st.2 ∧ r.2.1.1.2.1 = st.1.1.2.1 ∧
      r.2.1.1.1.1.bound = st.1.1.1.1.bound ∧
      r.2.1.1.1.2 = st.1.1.1.2 + 1 ∧
      (dataOf x r.2).pending = (dataOf x st).pending ∧
      (dataOf x r.2).virtual = (dataOf x st).virtual ∧
      (dataOf x st).cache ≤ (dataOf x r.2).cache := by
  obtain ⟨hroute, hrest⟩ := ordinary_routes x input hn
  rw [backendT_ordinaryHash capTag x q s pads τ g noise rest input hroute hrest st] at hr
  simp only [support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  generalize hM : merged x.2.1 st.1.1 st.2.cache = M at hz
  have hm := ordinary_merged_gen x hinj q s input hn st M hM z hz
  have hdata := congrArg (fun t => t.1.1.data) hm
  have hgrow := cappedCompiler_cache_le x.1 x.2.1 q s (.inl (.hash input)) M z hz
  simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    StateT.run_mk, support_map] at hz
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hz
  obtain ⟨c, hc, d, _, rfl⟩ := SigningCompilerPotential.compiler_hash_support
    x.1 x.2.1 input M.1.1 b hb
  simp only [deferredImpl, StateT.run, support_map] at hc
  obtain ⟨u, _, rfl⟩ := hc
  subst hM
  exact ⟨rfl, rfl, rfl, by simp [splitRest, withCache, merged, deferredCounted],
    (congrArg DeferredState.pending hdata).trans rfl,
    (congrArg DeferredState.virtual hdata).trans rfl,
    le_of_le_of_eq hgrow (congrArg DeferredState.cache hdata).symm⟩

end ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_routes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_routes

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.realRead_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.realRead_ordinary

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.relTriple_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.relTriple_supported

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.relTriple_of_projections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.relTriple_of_projections

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.randomOracle_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.randomOracle_observe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.cacheQuery_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.cacheQuery_rel

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.cacheRead_hash_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.cacheRead_hash_rel

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_merged_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_merged_gen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.compilerRead_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.compilerRead_view

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.keyedSplit_cache_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.keyedSplit_cache_forget

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.cachedExtra_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.cachedExtra_congr

/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_not_suspended' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_not_suspended

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_nonhash_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.ordinary_nonhash_quiet

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.compilerRead_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalRead.compilerRead_fields
