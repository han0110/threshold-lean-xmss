import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncHonestRead

/-! # A hash call at a bottom base input

`baseRead_sync` couples one hash call at a bottom base input on the real side with the hash call of
the compiler. The call can be the canonical base call of a bound key, so the trace can grow. The
relation `SyncAt` holds after the call, for each reveal map that the source holds.

- `realRead_facts` and `compRead_facts` give the effect of the call on each side.
- `trace_clauses` gives the clauses `staleFree` and `baseTraced` after the trace step.
- `core_post` and `extra_post` give `SyncCore` and `ExtraOpen` after the call.
- `baseRead_couple` couples a call with no hidden hit. `baseRead_hit` gives a stop at a hidden hit.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame
open SigningCompilerSyncBackend SigningCompilerSyncRealRead SigningCompilerSyncTrigger
open SigningCompilerSyncLocalRead SigningCompilerSyncHonestRead
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  SigningLaneUnionProof.traceStepAt

/-! ## The real call -/

section Real
variable (prims : Primitives) (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
  (noise : ChainNoiseIndex → HashOutput)

/-- One real call of `H` on either route. It keeps the log agreement, the private relation and the
carried state, and it counts once. The trace takes one step. The visible cache grows, and it
changes only at the input and at the trial inputs. This is `honest_call` of
`SigningCompilerO1RealLog` on both routes, with more facts. -/
private theorem realRead_facts (input : Query C) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr (.inl input))) ∨ t = .inr (.inr (.inl input))) (a : RealState C)
    (hlog : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1)
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (r : (WorldSpec C).Range t × RealState C)
    (hr : r ∈ support ((realWorld prims x s pads u rest t).run a)) :
    SigningPartnerCompareProof.LogAgreement x.1 r.2.1.1.1.1.1 ∧
      RealPrivate x s pads noise (gOf s pads u) rest r.2.2 (visibleOf r.2) ∧
      realLog a ≤ realLog r.2 ∧ r.2.1.2 = a.1.2 ∧
      r.2.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1 ∧
      r.2.1.1.2 = SigningLaneUnionProof.traceStepAt x.2.1 x.1 (visibleOf a) a.1.2.1.1 t
        (visibleOf r.2) a.1.1.2 ∧
      visibleOf a ≤ visibleOf r.2 ∧
      ∀ query, SigningPartnerCompareProof.OutsideTrials x.1 query → query ≠ input →
        visibleOf r.2 query = visibleOf a query := by
  have hpr := realWorld_preserves (x := x) (s := s) (pads := pads) (noise := noise)
    (g := gOf s pads u) (rest := rest) prims t a hpriv r hr
  have hfields := realWorld_read_fields_route prims x (gOf s pads u) rest (.inl input) t ht a r hr
  change r ∈ support ((ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) t).run a) at hr
  rw [rawTraceWorld_read_route prims x (gOf s pads u) rest (.inl input) t ht a.1 a.2] at hr
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨z, hz, y, hy, rfl⟩ := hr
  simp only [readInput, readAnswer] at hz hy
  have hpz : RealPrivate x s pads noise (gOf s pads u) rest z.2
      ((visibleOf a).cacheQuery input z.1) := by
    by_cases hs : IsSlot x input
    · rw [realImpl_slot x _ rest input hs, mem_support_pure_iff] at hz
      rw [hz]
      exact hpriv.observe_slot input hs
    · rw [realImpl_other x _ rest input hs] at hz
      exact hpriv.observe_other input hs z hz
  have hw : (z.1, (visibleOf a).cacheQuery input z.1) ∈
      support (((Query C →ₒ HashOutput).randomOracle input).run (visibleOf a)) := by
    cases hv : visibleOf a input with
    | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hv]
      simp [uniformSampleImpl]
    | some value =>
      rw [realRead_hit x s pads noise _ rest a.2 (visibleOf a) hpriv input value hv,
        mem_support_pure_iff] at hz
      subst z
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hv,
        observe_same (visibleOf a) input value hv]
      simp
  rw [grind_quiet_transport x s pads noise (gOf s pads u) rest _ _ _ _ _ hpz.quiet,
    support_map] at hy
  obtain ⟨y', hy'', hyy⟩ := hy
  have hy1 : y.1 = y' := by rw [← hyy]
  have hro := Set.mem_image_of_mem (fun r => (r.1, r.2.1.1)) hy''
  rw [← support_map, keyedSplit_cache_forget] at hro
  have hf := SigningReleasedTransferProof.cachedExtra_frame x.2.1 x.1 _ _ _ _ hro
  have hcall : SigningCacheLogProof.hashCall ⟨t, cast (by rcases ht with rfl | rfl <;> rfl) z.1⟩ =
      some (input, z.1) := by
    rcases ht with rfl | rfl <;> rfl
  have hl := SigningPartnerCompareProof.logAgreement_hash x.1 input a.1.1.1.1.1 hlog _ hw
    (a.1.1.1.1.1.2.logQuery t (cast (by rcases ht with rfl | rfl <;> rfl) z.1))
    (fun _ => by rw [SigningCacheLogProof.logCache_logQuery, hcall]; rfl) 0
  have hrd := randomOracle_support input (visibleOf a) _ hw
  refine ⟨?_, hpr, ?_, hfields.1, hfields.2, rfl, ?_, ?_⟩
  · rw [hy1]
    exact ⟨hl.1.trans hf.1, fun q hq => (hf.2 q hq).trans (hl.2 q hq)⟩
  · intro q v hq
    change SigningCacheLogProof.logCache (a.1.1.1.1.1.2.logQuery t
      (cast (by rcases ht with rfl | rfl <;> rfl) z.1)) q = some v
    rw [SigningCacheLogProof.logCache_logQuery,
      show SigningCacheLogProof.logCache a.1.1.1.1.1.2 q = some v from hq]
    rfl
  · rw [hy1]
    exact hrd.1.trans hf.1
  · intro q hq hne
    rw [hy1]
    exact (hf.2 q hq).trans (hrd.2.2 q hne)
end Real

/-! ## The trace step -/

section Trace
variable (x : Keys3 C) (s : HiddenKey → Digest)

/-- Two canonical randomizer inputs that are equal have the same key. -/
theorem randomizerInput_key (P : PublicParameter) (e f : KeyIndex) (ρ τ : Digest)
    (m m' : HashInput) (h : randomizerInput P bottomLayer e ρ m = randomizerInput P bottomLayer f τ m') :
    e = f ∧ ρ = τ := by
  have hk := congrArg (hiddenCandidate P) h
  rw [hiddenCandidate_randomizerInput, hiddenCandidate_randomizerInput] at hk
  simp only [Option.some.injEq, Prod.mk.injEq, HiddenKey.opening.injEq] at hk
  exact ⟨hk.1.2, hk.2⟩

/-- The trace clauses `staleFree` and `baseTraced` after a hash call at `input`. A cached
canonical base input has a trace entry, so the stale bit stays down. A fresh canonical base input
appends an entry. A new canonical entry of the cache is the input, and the premise `hcanon` makes
the call a canonical base call then. -/
theorem trace_clauses (input : HashInput) (t : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input t) (cache cache' : HashCache C)
    (signing : TsigState C) (bound : KeyIndex → Option Message)
    (aux : XmssSecurity.SigningCacheTrace × Bool) (hbound : signing.bound = bound)
    (hstale : aux.2 = false)
    (htraced : ∀ e message, bound e = some message →
      cache (.hash (randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e))
        (bytesLE 32 message))) ≠ none → e ∈ aux.1.leafIndices)
    (hvalue : ∀ e, SigningGuessProof.RandomizerCached x.2.1 cache e →
      SigningGuessProof.cachedRandomizer x.2.1 cache e = s (.opening bottomLayer e))
    (hcanon : ∀ e message, input = randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e))
      message → SigningGuessProof.RandomizerCached x.2.1 cache e)
    (hframe : ∀ i, i ≠ input → ¬IsMsg i → cache' (.hash i) = cache (.hash i)) :
    (SigningLaneUnionProof.traceStepAt x.2.1 x.1 cache signing t cache' aux).2 = false ∧
      ∀ e message, bound e = some message →
        cache' (.hash (randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e))
          (bytesLE 32 message))) ≠ none →
        e ∈ (SigningLaneUnionProof.traceStepAt x.2.1 x.1 cache signing t cache' aux).1.leafIndices := by
  have hnew : ∀ e message, cache' (.hash (randomizerInput x.1 bottomLayer e
      (s (.opening bottomLayer e)) (bytesLE 32 message))) ≠ none →
      cache (.hash (randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e))
        (bytesLE 32 message))) ≠ none ∨
      randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e)) (bytesLE 32 message) = input := by
    intro e message h
    by_cases he : randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e))
      (bytesLE 32 message) = input
    · exact Or.inr he
    · left
      rwa [← hframe _ he (SigningLane2BridgeProof.not_isMsg_randomizerInput _ _ _ _ _)]
  by_cases h : ∃ e, SigningGuessProof.RandomizerCached x.2.1 cache e ∧
      SigningFlatProof.BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 cache e) signing t
  · obtain ⟨e0, hp, hb⟩ := h
    obtain ⟨m0, hm0, hi⟩ := (baseCall_hashAt_iff x.1 e0 _ signing input t hcall).mp hb
    rw [hvalue e0 hp] at hi
    rw [traceStepAt_at x.1 x.2.1 cache cache' signing input t hcall aux e0 m0 hp hb hm0]
    by_cases hc : cache (.hash input) = none
    · rw [if_pos hc]
      refine ⟨hstale, ?_⟩
      intro e message hm h'
      simp only [XmssSecurity.SigningCacheTrace.leafIndices, List.map_append, List.map_cons,
        List.map_nil, List.mem_append, List.mem_singleton]
      rcases hnew e message h' with h1 | h1
      · exact Or.inl (htraced e message hm h1)
      · exact Or.inr (randomizerInput_key x.1 e e0 _ _ _ _ (h1.trans hi)).1
    · rw [if_neg hc]
      have hin : e0 ∈ aux.1.leafIndices :=
        htraced e0 m0 (hbound ▸ hm0) (by rw [← hi]; exact hc)
      refine ⟨by simp [hstale, hin], ?_⟩
      intro e message hm h'
      rcases hnew e message h' with h1 | h1
      · exact htraced e message hm h1
      · exact htraced e message hm (by rw [h1]; exact hc)
  · have heq : SigningLaneUnionProof.traceStepAt x.2.1 x.1 cache signing t cache' aux = aux := by
      unfold SigningLaneUnionProof.traceStepAt
      exact dif_neg h
    rw [heq]
    refine ⟨hstale, ?_⟩
    intro e message hm h'
    rcases hnew e message h' with h1 | h1
    · exact htraced e message hm h1
    · exfalso
      have hc := hcanon e (bytesLE 32 message) h1.symm
      apply h
      refine ⟨e, hc, ?_⟩
      rw [baseCall_hashAt_iff x.1 e _ signing input t hcall]
      exact ⟨message, hbound ▸ hm, by rw [hvalue e hc]; exact h1.symm⟩

end Trace

/-! ## The relation after the call -/

section Post
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The cache relation reads the cache, the pending answers and the virtual terms only. -/
private theorem cacheRelation_congr {P : PublicParameter} {seeds : C.Term → HashOutput}
    {data data' : DeferredState C} {actual : HashCache C}
    (hc : data'.cache = data.cache) (hp : data'.pending = data.pending)
    (hv : data'.virtual = data.virtual) (h : CacheRelation P seeds s data actual) :
    CacheRelation P seeds s data' actual := by
  obtain ⟨c, p, v, d⟩ := data
  obtain ⟨c', p', v', d'⟩ := data'
  simp only at hc hp hv
  subst hc hp hv
  exact ⟨h.agree, h.pending⟩

/-- A larger cache keeps each entry. -/
private theorem ne_none_of_le {cache cache' : HashCache C} (hle : cache ≤ cache') (query : Query C)
    (h : cache query ≠ none) : cache' query ≠ none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hle hv]
  exact Option.some_ne_none v

set_option maxHeartbeats 1600000 in
/-- One ordinary hash call of the compiler keeps the share state, the mark, the reveal map, the
bound map, the pending answers and the virtual terms. It counts once and grows the cache. It keeps
the free-slot frame and the fixed pads. -/
private theorem compRead_facts (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (input : HashInput)
    (st : CompState C) (r : HashOutput × CompState C)
    (hr : r ∈ support ((compBackend x q s pads u rest noise
      (.inl (.inl (.inl (.hash (.hash input)))))).run st))
    (hframe : RestAgree x rest st.1.1 ∧ RestFree x.2.1 st.1.1.1.1.data.cache)
    (hpads : PadsFixed x pads st) :
    r.2.2 = st.2 ∧ r.2.1.2 = st.1.2 ∧ r.2.1.1.2.1 = st.1.1.2.1 ∧
      r.2.1.1.1.1.bound = st.1.1.1.1.bound ∧ r.2.1.1.1.2 = st.1.1.1.2 + 1 ∧
      (dataOf x r.2).pending = (dataOf x st).pending ∧
      (dataOf x r.2).virtual = (dataOf x st).virtual ∧
      (dataOf x st).cache ≤ (dataOf x r.2).cache ∧
      (RestAgree x rest r.2.1.1 ∧ RestFree x.2.1 r.2.1.1.1.1.data.cache) ∧ PadsFixed x pads r.2 := by
  simp only [TprfSecurityProof.KeyCollision, not_or, not_not] at hkeys
  have hi := TprfSecurityProof.slotInput_injective hkeys.1 hkeys.2
  have hf := compilerRead_fields x hkeys.1 q s pads (tauOf s pads) (gOf s pads u) noise rest
    (.hash input) (not_isSlot_hash x input) st r hr
  have hmark : r.2.1.2 = st.1.2 := by
    obtain ⟨hroute, hrest⟩ := ordinary_routes x (.hash input) (not_isSlot_hash x input)
    have hr' := hr
    rw [backendT_ordinaryHash capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest
      (.hash input) hroute hrest st, support_map] at hr'
    obtain ⟨z, _, rfl⟩ := hr'
    rfl
  exact ⟨hf.1, hmark, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2,
    backendT_restFrame capTag x hi q s pads (tauOf s pads) (gOf s pads u) noise rest
      (.inl (.inl (.inl (.hash (.hash input))))) trivial st hframe r hr,
    backendT_padsFixed x q s pads u rest noise (.inl (.inl (.inl (.hash (.hash input))))) st hpads
      r hr⟩

/-- `SyncCore` after one hash call on both sides. The visible cache grows and keeps its PRF
entries. The compiler keeps each field but the cache, the count and the trace. The coupling gives
the cache relation and the trace. -/
private theorem core_post (cCore : Carried C) (a a' : RealState C) (src : SourceState C)
    (st st' : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a'.2 (visibleOf a'))
    (hle : visibleOf a ≤ visibleOf a')
    (hprf : ∀ seed p, visibleOf a' (.prf seed p) = visibleOf a (.prf seed p))
    (hcount : a'.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1)
    (hshare : st'.2 = st.2) (hreveal : st'.1.1.2.1 = st.1.1.2.1)
    (hbound : st'.1.1.1.1.bound = st.1.1.1.1.bound) (hcount' : st'.1.1.1.2 = st.1.1.1.2 + 1)
    (hpend : (dataOf x st').pending = (dataOf x st).pending)
    (hvirt : (dataOf x st').virtual = (dataOf x st).virtual)
    (hcle : (dataOf x st).cache ≤ (dataOf x st').cache)
    (hrest : RestAgree x rest st'.1.1 ∧ RestFree x.2.1 st'.1.1.1.1.data.cache)
    (hc : CacheRelation x.1 x.2.1 s { dataOf x st with cache := (dataOf x st').cache }
      (visibleOf a'))
    (htr : a'.1.1.2 = st'.1.1.1.1.trace) :
    SyncCore x s pads noise (gOf s pads u) rest (withCarried a' cCore) (src, st') := by
  obtain ⟨⟨hf, -⟩, hcnt⟩ := hs
  have hrc : ∀ e, SigningGuessProof.RandomizerCached x.2.1 (visibleOf a') e ↔
      SigningGuessProof.RandomizerCached x.2.1 (visibleOf a) e := by
    intro e
    simp only [SigningGuessProof.RandomizerCached, hprf]
  have hcr : ∀ e, SigningGuessProof.cachedRandomizer x.2.1 (visibleOf a') e =
      SigningGuessProof.cachedRandomizer x.2.1 (visibleOf a) e := by
    intro e
    simp only [SigningGuessProof.cachedRandomizer, hprf]
  have hfields : SyncFields x s pads noise (gOf s pads u) rest (withCarried a' cCore) (src, st') :=
    { corrupt := hf.corrupt
      bound := hf.bound
      released := hf.released
      exposed := hf.exposed
      candidates := hf.candidates
      flag := hf.flag
      reveal := hf.reveal.frame rfl hreveal
      releasedPending := fun p v hp hk => hcle (hf.releasedPending p v (hpend ▸ hp) hk)
      opening := ⟨fun e he => (hcr e).trans (hf.opening.actualValue e ((hrc e).mp he)),
        fun e he => SigningGuessProof.randomizerCached_mono _ _ _ hcle e
          (hf.opening.released e he)⟩
      pendingValid := fun p v hp => hf.pendingValid p v (hpend ▸ hp)
      allocated := fun p hp => hf.allocated p (hpend ▸ hp)
      virtualSeen := fun T p hp => ne_none_of_le hle _ (hf.virtualSeen T p (hvirt ▸ hp))
      compilerBound := hbound.trans hf.compilerBound
      trace := htr
      bad := hshare ▸ hf.bad
      share := hshare ▸ hf.share
      restAgree := hrest.1
      restFree := hrest.2
      realPrivate := hpriv
      frontier := fun edge he => hf.frontier edge (hpend ▸ he)
      candidatesPaid := hf.candidatesPaid
      doneCached := hshare ▸ hf.doneCached }
  refine ⟨⟨hfields, ?_⟩, ?_⟩
  · change CacheRelation x.1 x.2.1 s (dataOf x st') (visibleOf a')
    generalize dataOf x st' = D' at hpend hvirt hc ⊢
    generalize dataOf x st = D at hpend hvirt hc
    exact cacheRelation_congr s (data := { D with cache := D'.cache }) (data' := D') rfl hpend hvirt hc
  · change a'.1.1.1.1.1.1.2 = st'.1.1.1.2
    rw [hcount, hcount']
    exact congrArg (· + 1) hcnt

/-- The clauses of `ExtraOpen` after one hash call at `input` on both sides. The visible cache keeps
its PRF entries, and it changes only at the input and at the trial inputs. The input is no hidden
hit. The compiler keeps its pending answers and its virtual terms. The log grows, and the trace
facts come from `trace_clauses`. -/
theorem extra_post (top : TopTree) (rev : HiddenKey → Option Digest) (cTime : Carried C)
    (input : HashInput) (a a' : RealState C) (b : SourceStateO1 C × CompState C)
    (st' : CompState C)
    (hx : ExtraOpen prims x top s rev (fun _ _ => False) (withCarried a cTime) b)
    (hlog : SigningPartnerCompareProof.LogAgreement x.1 a'.1.1.1.1.1)
    (hlogle : realLog a ≤ realLog a')
    (hprf : ∀ seed p, visibleOf a' (.prf seed p) = visibleOf a (.prf seed p))
    (hhash : ∀ i, i ≠ input → ¬IsMsg i → visibleOf a' (.hash i) = visibleOf a (.hash i))
    (hno : ∀ k, hiddenCandidate x.1 input = some (k, s k) → b.1.base.revealed k ≠ none)
    (hpend : (dataOf x st').pending = (dataOf x b.2).pending)
    (hvirt : (dataOf x st').virtual = (dataOf x b.2).virtual)
    (hstale : a'.1.1.2.2 = false)
    (htraced : ∀ e message, cTime.1.1.bound e = some message →
      visibleOf a' (.hash (randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e))
        (bytesLE 32 message))) ≠ none → e ∈ a'.1.1.2.1.leafIndices) :
    ExtraOpen prims x top s rev (fun _ _ => False) (withCarried a' cTime)
      (⟨b.1.base, b.1.starts⟩, st') := by
  have hr := hx.rest
  have hvirt' : ∀ T p, (T, p) ∈ (dataOf x b.2).virtual → (T, p) ∈ (dataOf x st').virtual := by
    intro T p h
    rw [hvirt]
    exact h
  have hpend' : ∀ p, (dataOf x b.2).pending p ≠ none → (dataOf x st').pending p ≠ none := by
    intro p h
    rw [hpend]
    exact h
  have hquiet : ∀ (i : HashInput) (k : HiddenKey), hiddenCandidate x.1 i = some (k, s k) →
      b.1.base.revealed k = none → ¬IsMsg i → visibleOf a (.hash i) = none →
      visibleOf a' (.hash i) = none := by
    intro i k hk hrev hmsg h0
    by_cases he : i = input
    · subst i
      exact absurd hrev (hno k hk)
    · rw [hhash i he hmsg]
      exact h0
  refine ⟨{ hr with
      treeRows := fun bi hbi k l d => by
        have hrows := hr.treeRows bi hbi k l d
        exact ⟨fun T => hvirt' _ _ (hrows.1 T), hpend' _ hrows.2⟩
      storedTopDigit := fun bi tree ht => topDigit_mono hlogle x.1 bi _ _ (hr.storedTopDigit bi tree ht)
      staleFree := hstale
      noEarlyGuess := fun e message hk =>
        hquiet _ _ (hiddenCandidate_randomizerInput x.1 bottomLayer e _ message) hk
          (SigningLane2BridgeProof.not_isMsg_randomizerInput _ _ _ _ _) (hr.noEarlyGuess e message hk)
      guessFree := fun p hk hp => by
        have hp0 : (dataOf x b.2).pending p = none := by
          rw [← hpend]
          exact hp
        exact hquiet _ _ (PendingInput.hiddenCandidate x.1 p (s p.key)) hk
          (PendingInput.not_isMsg x.1 p (s p.key)) (hr.guessFree p hk hp0)
      treeTerms := fun bi hbi => by
        obtain ⟨h1, h2⟩ := hr.treeTerms bi hbi
        exact ⟨fun k T => hvirt' _ _ (h1 k T), fun T => hvirt' _ _ (h2 T)⟩
      treeStarts := fun bi tree ht T l => hvirt' _ _ (hr.treeStarts bi tree ht T l)
      baseTraced := htraced
      logAgreement := hlog
      storedRuns := SigningGuessProof.StoredTreeRuns.mono prims x top hlogle hr.storedRuns
      startsTraced := fun e l d hd => by
        obtain ⟨receipt, h1, h2, h3, h4⟩ := hr.startsTraced e l d hd
        exact ⟨receipt, h1, h2, h3, SigningGuessProof.ReceiptRuns.mono prims x top hlogle receipt h4⟩
      prfSeen := fun hfl => by cases hfl
      bottomSeen := fun hfl => by cases hfl }, ?_, ?_⟩
  · intro hfl T p hv
    exact hx.prfSeen hfl T p (fun h0 => hv ((hprf _ _).trans h0))
  · intro hfl T e l d ho hv
    rcases hx.bottomSeen hfl T e l d ho (fun h0 => hv ((hprf _ _).trans h0)) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr fun d' => hpend' _ (h1 d')

end Post

/-! ## The coupling of the two calls -/

section Couple
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A map on the left side of a coupling moves into its post. -/
private theorem relTriple_map_left {α β γ : Type} {oa : ProbComp α} {ob : ProbComp β} {f : α → γ}
    {R : γ → β → Prop} (h : RelTriple oa ob (fun a b => R (f a) b)) : RelTriple (f <$> oa) ob R := by
  simpa only [id_map] using relTriple_map (f := f) (g := id) (R := R) h

/-- A map on the right side of a coupling moves into its post. -/
private theorem relTriple_map_right {α β δ : Type} {oa : ProbComp α} {ob : ProbComp β} {g : β → δ}
    {R : α → δ → Prop} (h : RelTriple oa ob (fun a b => R a (g b))) : RelTriple oa (g <$> ob) R := by
  simpa only [id_map] using relTriple_map (f := id) (g := g) (R := R) h

set_option maxHeartbeats 1600000 in
/-- A hash call with no hidden hit. The real read and the compiler read are lazy reads of their
caches, and the coupling of the two reads gives the same answer, the cache relation and the same
trace. -/
theorem baseRead_couple (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (input : HashInput)
    (t : (WorldSpec C).Domain) (ht : SigningFlatProof.HashCallAt input t) (cCore : Carried C)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (hsig : a.1.2.1.1.bound = cCore.1.1.bound)
    (hno : ∀ k, hiddenCandidate x.1 input = some (k, s k) → src.revealed k ≠ none)
    (hread : (∃ v, visibleOf a (.hash input) = some v) ∨ Quiet x s pads noise (.hash input)) :
    RelTriple ((realWorld prims x s pads u rest t).run a)
      ((compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash (.hash input)))))).run st)
      (fun ra rb => cast (by rcases ht with rfl | rfl <;> rfl) ra.1 = rb.1 ∧
        CacheRelation x.1 x.2.1 s { dataOf x st with cache := (dataOf x rb.2).cache }
          (visibleOf ra.2) ∧
        ra.2.1.1.2 = rb.2.1.1.1.1.trace ∧
        ra ∈ support ((realWorld prims x s pads u rest t).run a) ∧
        rb ∈ support ((compBackend x q s pads u rest noise
          (.inl (.inl (.inl (.hash (.hash input)))))).run st)) := by
  have hT : (WorldSpec C).Range t = HashOutput := by rcases ht with rfl | rfl <;> rfl
  obtain ⟨⟨hf, hcache⟩, -⟩ := hs
  have hinj : Function.Injective x.2.1 := by
    simp only [TprfSecurityProof.KeyCollision, not_or, not_not] at hkeys
    exact hkeys.1
  have hrv := realWorld_read_view_route prims x s pads noise (gOf s pads u) rest (.inl (.hash input))
    t ht a hf.realPrivate hread
  have hcv := compilerRead_view x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest (.hash input)
    (not_isSlot_hash x input) st
  have hrel := cacheRead_hash_rel x.1 x.2.1 s src (dataOf x st) (visibleOf a) a.1.2.1.1
    (compilerSigning st.1.1.1.1) a.1.1.2 input t (.inr (.inr (.inl (.hash input)))) ht (Or.inr rfl)
    hcache hf.opening hf.releasedPending (hsig.trans hf.bound.symm) hf.compilerBound.symm hno
  have htr : a.1.1.2 = st.1.1.1.1.trace := hf.trace
  rw [htr] at hrel hrv
  simp only [readInput] at hrv
  have hw : (realWorld prims x s pads u rest t).run a = (ThresholdLeanXmssSecurity.fuse
      (rawTraceWorld prims x) (realImpl x (gOf s pads u) rest) t).run a := rfl
  have h1 : RelTriple (realReadView <$> (realWorld prims x s pads u rest t).run a)
      (compilerReadView x <$> (compBackend x q s pads u rest noise
        (.inl (.inl (.inl (.hash (.hash input)))))).run st)
      (fun v w => cast hT v.1 = w.1 ∧
        CacheRelation x.1 x.2.1 s { dataOf x st with cache := w.2.1 } v.2.1 ∧ v.2.2 = w.2.2) := by
    rw [hw, hrv, hcv]
    refine relTriple_map_left (relTriple_post_mono hrel ?_)
    intro v w h
    exact ⟨by simpa [readAnswer] using h.1, h.2.1, h.2.2⟩
  refine relTriple_post_mono (relTriple_of_projections _ _ _ _ h1) ?_
  rintro ra rb ⟨⟨hv, hc, htr'⟩, hra, hrb⟩
  exact ⟨hv, hc, htr', hra, hrb⟩


/-- A hash call at an input that carries the secret of an unrevealed key. Below the budget the
compiler is stuck. At the budget the real call goes above it. -/
theorem baseRead_hit (input : HashInput) (t : (WorldSpec C).Domain)
    (ht : SigningFlatProof.HashCallAt input t) (cCore : Carried C) (a : RealState C)
    (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (k : HiddenKey) (hk : hiddenCandidate x.1 input = some (k, s k))
    (hrev : src.revealed k = none) :
    RelTriple ((realWorld prims x s pads u rest t).run a)
      ((compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash (.hash input)))))).run st)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2) := by
  obtain ⟨⟨hf, -⟩, hcount⟩ := hs
  by_cases hcap : st.1.1.1.2 < q
  · refine relTriple_of_support_right (fun rb hrb _ => Or.inr (Or.inr ?_))
    exact capHit_stuck x q s pads (tauOf s pads) (gOf s pads u) noise rest input k src st
      hk hf.reveal hrev hcap hf.bad rb hrb
  · refine relTriple_of_support_left (fun ra hra _ => Or.inl (Or.inr ?_))
    have hc := (realWorld_read_fields_route prims x (gOf s pads u) rest (.inl (.hash input)) t ht
      a ra hra).2
    have hq : ¬q < a.1.1.1.1.1.1.2 := fun h => ha (Or.inr h)
    have he : a.1.1.1.1.1.1.2 = st.1.1.1.2 := hcount
    change q < ra.2.1.1.1.1.1.1.2
    omega

set_option maxHeartbeats 1600000 in
/-- The call of `baseRead_sync` on one route of the real world, with the compiler hash call. -/
theorem baseRead_world (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (cCore cTime : Carried C) (e : KeyIndex) (ρ : Digest)
    (message : HashInput) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a b)
    (hsig : a.1.2.1.1.bound = cCore.1.1.bound) (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (t : (WorldSpec C).Domain)
    (ht : SigningFlatProof.HashCallAt (randomizerInput x.1 bottomLayer e ρ message) t) :
    RelTriple ((realWorld prims x s pads u rest t).run a)
      ((compBackend x q s pads u rest noise
        (.inl (.inl (.inl (.hash (.hash (randomizerInput x.1 bottomLayer e ρ message))))))).run b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (cast (by rcases ht with rfl | rfl <;> rfl) ra.1 = rb.1 ∧
          SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime ra.2
            (⟨b.1.base, b.1.starts⟩, rb.2) ∧
          rb.2.1.2 = b.2.1.2 ∧ ra.2.1.2 = a.1.2 ∧ realLog a ≤ realLog ra.2 ∧
          (ρ = s (.opening bottomLayer e) → b.1.base.revealed (.opening bottomLayer e) ≠ none))) := by
  obtain ⟨hcore, hx, htop, hpads⟩ := hs
  have hf := hcore.1.1
  have hcache := hcore.1.2
  by_cases hhit : ∃ k, hiddenCandidate x.1 (randomizerInput x.1 bottomLayer e ρ message) =
      some (k, s k) ∧ b.1.base.revealed k = none
  · obtain ⟨k, hk, hrev⟩ := hhit
    exact relTriple_post_mono (baseRead_hit prims x q s pads u rest noise _ t ht cCore a b.1.base b.2
      hcore ha k hk hrev) (fun ra rb h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have hno : ∀ k, hiddenCandidate x.1 (randomizerInput x.1 bottomLayer e ρ message) =
      some (k, s k) → b.1.base.revealed k ≠ none := fun k hk hr => hhit ⟨k, hk, hr⟩
  have hread := ((hash_dichotomy x s pads noise b.1.base (dataOf x b.2) (visibleOf a) hcache
    hf.releasedPending hf.frontier _).resolve_left hhit).2
  refine relTriple_post_mono (baseRead_couple prims x q s pads u rest noise hkeys _ t ht cCore a
    b.1.base b.2 hcore hsig hno hread) ?_
  rintro ra rb ⟨hv, hc, htr, hra, hrb⟩
  obtain ⟨hlog', hpriv', hlogle, hcarried, hcount', htrace, hle, hout⟩ :=
    realRead_facts prims x s pads u rest noise (.hash (randomizerInput x.1 bottomLayer e ρ message))
      t ht a hx.rest.logAgreement hf.realPrivate ra hra
  obtain ⟨hshare, hmark', hreveal, hbound, hcountc, hpend, hvirt, hcle, hrestc, hpads'⟩ :=
    compRead_facts x q s pads u rest noise hkeys _ b.2 rb hrb ⟨hf.restAgree, hf.restFree⟩ hpads
  have hprf : ∀ seed p, visibleOf ra.2 (.prf seed p) = visibleOf a (.prf seed p) :=
    fun seed p => hout _ (SigningPartnerCompareProof.outsideTrials_prf x.1 seed p)
      (by intro h; cases h)
  have hhash : ∀ i, i ≠ randomizerInput x.1 bottomLayer e ρ message → ¬IsMsg i →
      visibleOf ra.2 (.hash i) = visibleOf a (.hash i) := by
    intro i hi hm
    refine hout _ ⟨SigningCacheLogProof.tracked_hash i, fun e' payload h => hm ?_⟩
      (fun h => hi (Query.hash.inj h))
    rw [Query.hash.inj h]
    exact byte23_msg _ _ _ _
  have hcanon : ∀ e' m, randomizerInput x.1 bottomLayer e ρ message =
      randomizerInput x.1 bottomLayer e' (s (.opening bottomLayer e')) m →
      SigningGuessProof.RandomizerCached x.2.1 (visibleOf a) e' := by
    intro e' m h
    obtain ⟨he, hρ⟩ := randomizerInput_key x.1 e e' ρ _ message m h
    subst he
    have hr := hno (.opening bottomLayer e) (by rw [hiddenCandidate_randomizerInput, hρ])
    exact (hcache.randomizer e (hf.opening.released e hr)).1
  have htc := trace_clauses x s _ t ht (visibleOf a) (visibleOf ra.2) a.1.2.1.1 cTime.1.1.bound
    a.1.1.2 (hsig.trans htime.symm) hx.rest.staleFree hx.rest.baseTraced hf.opening.actualValue
    hcanon hhash
  rw [← htrace] at htc
  have htop' : TopO1 prims x top ra.2 (⟨b.1.base, b.1.starts⟩, rb.2) := by
    obtain ⟨start, result, h1, h2, h3⟩ := htop.topRun
    refine ⟨fun bi l d => ?_, start, result, h1, h2, h3.trans hlogle⟩
    change (dataOf x rb.2).pending _ ≠ none
    rw [hpend]
    exact htop.topRows bi l d
  refine Or.inr (Or.inr ⟨hv, ⟨core_post x s pads u rest noise cCore a ra.2 b.1.base b.2 rb.2 hcore
    hpriv' hle hprf hcount' hshare hreveal hbound hcountc hpend hvirt hcle hrestc hc htr,
    extra_post prims x s top rev cTime _ a ra.2 b rb.2 hx hlog' hlogle hprf hhash hno hpend hvirt
      htc.1 htc.2, htop', hpads'⟩, hmark', hcarried, hlogle,
    fun hρ => hno _ (by rw [hiddenCandidate_randomizerInput, hρ])⟩)

end Couple

section Calls
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A hash call at a bottom base input. It can be the canonical base call of a bound key, so the
trace can grow. The statement keeps the full relation, for each reveal map that the source holds.
It needs the bound map of the carried state of the real run. -/
theorem baseRead_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (forger : Bool)
    (top : TopTree) (rev : HiddenKey → Option Digest) (cCore cTime : Carried C) (e : KeyIndex)
    (ρ : Digest) (message : HashInput) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a b)
    (hsig : a.1.2.1.1.bound = cCore.1.1.bound) (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((readCall prims x s pads u rest forger
        (.inl (.hash (randomizerInput x.1 bottomLayer e ρ message)))).run a)
      (runX (compBackend x q s pads u rest noise)
        (sourceHashX x.1 x.2.1 (.hash (randomizerInput x.1 bottomLayer e ρ message))) b.1.base b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧
          SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime ra.2
            (⟨rb.1.2, b.1.starts⟩, rb.2) ∧
          rb.1.2 = b.1.base ∧ rb.2.1.2 = false ∧ ra.2.1.2 = a.1.2 ∧ realLog a ≤ realLog ra.2 ∧
          (ρ = s (.opening bottomLayer e) → b.1.base.revealed (.opening bottomLayer e) ≠ none))) := by
  have hcomp : runX (compBackend x q s pads u rest noise)
      (sourceHashX x.1 x.2.1 (.hash (randomizerInput x.1 bottomLayer e ρ message))) b.1.base b.2 =
      (fun r => ((r.1, b.1.base), r.2)) <$> (compBackend x q s pads u rest noise
        (.inl (.inl (.inl (.hash (.hash (randomizerInput x.1 bottomLayer e ρ message))))))).run
          b.2 := by
    simp only [sourceHashX]
    exact runX_deferred _ _ _ _
  rw [hcomp]
  cases forger
  · have h := baseRead_world prims x q s pads u rest noise hkeys top rev cCore cTime e ρ message a b
      hs hsig htime ha _ (Or.inr rfl)
    refine relTriple_map_right (relTriple_post_mono h ?_)
    rintro ra rb (h1 | h1 | ⟨h1, h2, h3, h4, h5, h6⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h2, rfl, h3.trans hmark, h4, h5, h6⟩)
  · have h := baseRead_world prims x q s pads u rest noise hkeys top rev cCore cTime e ρ message a b
      hs hsig htime ha _ (Or.inl rfl)
    refine relTriple_map_right (relTriple_post_mono h ?_)
    rintro ra rb (h1 | h1 | ⟨h1, h2, h3, h4, h5, h6⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h2, rfl, h3.trans hmark, h4, h5, h6⟩)

end Calls

end ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.randomizerInput_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.randomizerInput_key

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.trace_clauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.trace_clauses

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.extra_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.extra_post

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_couple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_couple

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_hit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_world

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BaseRead.baseRead_sync
