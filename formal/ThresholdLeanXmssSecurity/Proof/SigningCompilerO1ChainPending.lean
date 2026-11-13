import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncHonestRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Reads

/-! # Chain calls of the O1 coupling

`chainPending_sync` couples an honest hash call at the input of a chain edge at its secret with
the pending call of the compiler at that edge.

- The private cache holds the answer of the edge from the start (`realImpl_preload`). A chain
  input is no bottom base input (`chainInput_ne_randomizer`), so the real call runs no grind and
  keeps the trace (`chainCall_readStep`).
- The clause `frontier` gives an unrevealed key when no answer is pending. So the compiler returns
  the stored answer, or it stores the answer of the fixed noise (`backendT_chainPending`).
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerSyncBackend SigningCompilerSyncRealRead
open SigningCompilerSyncTrigger SigningCompilerSyncLocalRead SigningCompilerSyncHonestRead
open SigningCompilerO1Reads
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-- A chain input is no randomizer input. -/
theorem chainInput_ne_randomizer (P : PublicParameter) (edge : ChainNoiseIndex) (d : Digest)
    (lay : Layer) (e : KeyIndex) (ρ : Digest) (message : HashInput) :
    (chainPending edge).input P d ≠ randomizerInput P lay e ρ message := by
  intro he
  have h1 := PendingInput.hiddenCandidate P (chainPending edge) d
  rw [he, hiddenCandidate_randomizerInput] at h1
  rcases edge with ⟨l, e' | b, p⟩ <;> simp [chainPending, PendingInput.key] at h1

/-! ## The real side of one read -/

/-- The effect of one real read of `input` with the answer `v`. The read observes the answer in the
visible cache, counts once, logs the answer and keeps the private cache, the carried state and the
trace. -/
structure ReadStep (input : Query C) (v : HashOutput) (a a' : RealState C) : Prop where
  visible : visibleOf a' = (visibleOf a).cacheQuery input v
  seen : ∀ w, visibleOf a input = some w → w = v
  priv : a'.2 = a.2
  carried : a'.1.2 = a.1.2
  trace : a'.1.1.2 = a.1.1.2
  count : a'.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1
  log : ∃ t value, a'.1.1.1.1.1.2 = a.1.1.1.1.1.2.logQuery t value ∧
    SigningCacheLogProof.hashCall ⟨t, value⟩ = some (input, v)

/-- A cache that holds `v` at `input` or nothing there grows when it observes `v`. -/
theorem le_cacheQuery_of_seen (vis : HashCache C) (input : Query C) (v : HashOutput)
    (h : ∀ w, vis input = some w → w = v) : vis ≤ vis.cacheQuery input v := by
  cases hv : vis input with
  | none => exact QueryCache.le_cacheQuery vis hv
  | some w =>
    rw [h w hv] at hv
    rw [observe_same vis input v hv]

/-- The observed cache is a result of the lazy read. -/
theorem observe_mem_support (vis : HashCache C) (input : Query C) (v : HashOutput)
    (h : ∀ w, vis input = some w → w = v) :
    (v, vis.cacheQuery input v) ∈ support (((Query C →ₒ HashOutput).randomOracle input).run vis) := by
  cases hv : vis input with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hv]
    simp [uniformSampleImpl]
  | some w =>
    rw [h w hv] at hv
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hv, observe_same vis input v hv]
    simp

theorem ReadStep.realLog_le {input : Query C} {v : HashOutput} {a a' : RealState C}
    (h : ReadStep input v a a') : realLog a ≤ realLog a' := by
  obtain ⟨t, value, hl, -⟩ := h.log
  intro query w hq
  change SigningCacheLogProof.logCache a'.1.1.1.1.1.2 query = some w
  rw [hl, SigningCacheLogProof.logCache_logQuery]
  rw [show SigningCacheLogProof.logCache a.1.1.1.1.1.2 query = some w from hq]
  rfl

theorem ReadStep.logAgreement (P : PublicParameter) {input : Query C} {v : HashOutput}
    {a a' : RealState C} (h : ReadStep input v a a')
    (hl : SigningPartnerCompareProof.LogAgreement P a.1.1.1.1.1) :
    SigningPartnerCompareProof.LogAgreement P a'.1.1.1.1.1 := by
  obtain ⟨t, value, hlog, hcall⟩ := h.log
  have hw := observe_mem_support (visibleOf a) input v h.seen
  have hagree := SigningPartnerCompareProof.logAgreement_hash P input a.1.1.1.1.1 hl _ hw
    a'.1.1.1.1.1.2 (fun q' => by
      rw [hlog, SigningCacheLogProof.logCache_logQuery, hcall]
      by_cases he : input = q' <;> simp [he]) a'.1.1.1.1.1.1.2
  have hv : a'.1.1.1.1.1.1.1 = (visibleOf a).cacheQuery input v := h.visible
  rw [← hv] at hagree
  exact hagree

theorem ReadStep.fresh {input : Query C} {v : HashOutput} {a a' : RealState C}
    (h : ReadStep input v a a') (query : Query C) (hq : visibleOf a' query ≠ none) :
    visibleOf a query ≠ none ∨ query = input := by
  by_cases he : query = input
  · exact Or.inr he
  · rw [h.visible, QueryCache.cacheQuery_of_ne _ _ he] at hq
    exact Or.inl hq

theorem ne_none_of_le {c c' : HashCache C} (hle : c ≤ c') {query : Query C}
    (h : c query ≠ none) : c' query ≠ none := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
  rw [hle hw]
  exact Option.some_ne_none _

/-- The synchronization fields pass to a real state with a larger visible cache, the same carried
state and the same trace. -/
theorem syncFields_observe (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (u : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
    (a a' : RealState C) (b : SourceState C × CompState C)
    (hs : SyncFields x s pads noise (gOf s pads u) rest a b)
    (hr : RealPrivate x s pads noise (gOf s pads u) rest a'.2 (visibleOf a'))
    (hle : visibleOf a ≤ visibleOf a') (hc : a'.1.2 = a.1.2) (ht : a'.1.1.2 = a.1.1.2) :
    SyncFields x s pads noise (gOf s pads u) rest a' b :=
  { hs with
    corrupt := by rw [hc]; exact hs.corrupt
    bound := by rw [hc]; exact hs.bound
    released := by rw [hc]; exact hs.released
    exposed := by rw [hc]; exact hs.exposed
    candidates := by rw [hc]; exact hs.candidates
    flag := by rw [hc]; exact hs.flag
    opening := ⟨fun e he => realPrivate_actualValue x hkeys s pads noise u rest _ _ hr e he,
      hs.opening.released⟩
    virtualSeen := fun T p hp => ne_none_of_le hle (hs.virtualSeen T p hp)
    trace := ht.trans hs.trace
    realPrivate := hr }

/-- A new pending answer at a chain edge keeps the cache relation when the visible cache observes
its value at the input. -/
theorem cacheRelation_chainPending (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (vis : HashCache C)
    (h : CacheRelation P seeds s data vis) (p : PendingInput) (answer : DeferredOutput)
    (hseen : ∀ w, vis (.hash (p.input P (s p.key))) = some w → w = answer.interpret s) :
    CacheRelation P seeds s { data with pending := Function.update data.pending p (some answer) }
      (vis.cacheQuery (.hash (p.input P (s p.key))) (answer.interpret s)) := by
  refine ⟨fun query hq => ?_, fun p' value hp' => ?_⟩
  · by_cases he : query = .hash (p.input P (s p.key))
    · subst query
      rw [QueryCache.cacheQuery_self]
      cases hcq : data.cache (.hash (p.input P (s p.key))) with
      | none =>
        exact (hq ⟨hcq, Or.inl ⟨p, answer, Function.update_self _ _ _, rfl⟩⟩).elim
      | some w =>
        have hns : ¬SuspendedQuery P seeds s data (.hash (p.input P (s p.key))) := by
          intro hs
          have h0 := hs.1
          rw [hcq] at h0
          cases h0
        have hv := h.agree _ hns
        rw [hcq] at hv
        rw [hseen w hv]
    · rw [QueryCache.cacheQuery_of_ne _ _ he]
      refine h.agree query fun hs => hq ⟨hs.1, ?_⟩
      rcases hs.2 with ⟨p', value, hp', hq'⟩ | hv
      · by_cases hpp : p' = p
        · subst p'
          exact (he hq').elim
        · refine Or.inl ⟨p', value, ?_, hq'⟩
          change Function.update data.pending p (some answer) p' = some value
          rw [Function.update_of_ne hpp]
          exact hp'
      · exact Or.inr hv
  · change Function.update data.pending p (some answer) p' = some value at hp'
    by_cases hpp : p' = p
    · subst p'
      rw [Function.update_self, Option.some.injEq] at hp'
      subst value
      rw [QueryCache.cacheQuery_self]
    · rw [Function.update_of_ne hpp] at hp'
      exact le_cacheQuery_of_seen vis _ _ hseen (h.pending p' value hp')

/-- The data of the compiler state does not read the count. -/
theorem dataOf_count (x : Keys3 C) (st : CompState C) (count : ℕ) :
    dataOf x ((((st.1.1.1.1, count), st.1.1.2), st.1.2), st.2) = dataOf x st := rfl

/-- The data of the compiler state after a new pending answer. -/
theorem dataOf_pending (x : Keys3 C) (st : CompState C) (p : PendingInput)
    (answer : DeferredOutput) (count : ℕ) :
    dataOf x (((({ st.1.1.1.1 with data := { st.1.1.1.1.data with
      pending := Function.update st.1.1.1.1.data.pending p (some answer) } },
        count), st.1.1.2), st.1.2), st.2) =
      { dataOf x st with pending := Function.update (dataOf x st).pending p (some answer) } := rfl

/-- The synchronization fields do not read the count of the compiler. -/
theorem syncFields_count (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (src : SourceState C) (st : CompState C)
    (count : ℕ) (h : SyncFields x s pads noise g rest a (src, st)) :
    SyncFields x s pads noise g rest a (src, ((((st.1.1.1.1, count), st.1.1.2), st.1.2), st.2)) :=
  { corrupt := h.corrupt, bound := h.bound, released := h.released
    exposed := h.exposed, candidates := h.candidates, flag := h.flag
    reveal := h.reveal, releasedPending := h.releasedPending, opening := h.opening
    pendingValid := h.pendingValid, allocated := h.allocated, virtualSeen := h.virtualSeen
    compilerBound := h.compilerBound, trace := h.trace, bad := h.bad, share := h.share
    restAgree := h.restAgree, restFree := h.restFree, realPrivate := h.realPrivate
    frontier := h.frontier, candidatesPaid := h.candidatesPaid, doneCached := h.doneCached }

/-- A new pending answer at a chain edge with an unrevealed key keeps the synchronization fields.
The source allocates the edge. -/
theorem syncFields_chainPending (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (src : SourceState C) (st : CompState C)
    (edge : ChainNoiseIndex) (answer : DeferredOutput) (count : ℕ)
    (h : SyncFields x s pads noise g rest a (src, st))
    (hrev : src.revealed (chainPending edge).key = none)
    (hframe : Frame x rest ((({ st.1.1.1.1 with data := { st.1.1.1.1.data with
      pending := Function.update st.1.1.1.1.data.pending (chainPending edge) (some answer) } },
        count), st.1.1.2))) :
    SyncFields x s pads noise g rest a
      ({ src with allocated := src.allocated ++ [chainPending edge] },
        (((({ st.1.1.1.1 with data := { st.1.1.1.1.data with
          pending := Function.update st.1.1.1.1.data.pending (chainPending edge) (some answer) } },
            count), st.1.1.2), st.1.2), st.2)) := by
  have hpend : ∀ p, (dataOf x (((({ st.1.1.1.1 with data := { st.1.1.1.1.data with
      pending := Function.update st.1.1.1.1.data.pending (chainPending edge) (some answer) } },
        count), st.1.1.2), st.1.2), st.2)).pending p =
      Function.update (dataOf x st).pending (chainPending edge) (some answer) p := fun _ => rfl
  exact
    { corrupt := h.corrupt, bound := h.bound, released := h.released
      exposed := h.exposed, candidates := h.candidates, flag := h.flag
      reveal := h.reveal
      releasedPending := fun p' value hp' hk => by
        rw [hpend] at hp'
        by_cases he : p' = chainPending edge
        · subst p'
          exact (hk hrev).elim
        · rw [Function.update_of_ne he] at hp'
          exact h.releasedPending p' value hp' hk
      opening := ⟨h.opening.actualValue, h.opening.released⟩
      pendingValid := hframe.2.2
      allocated := fun p' hp' => by
        rw [hpend] at hp'
        by_cases he : p' = chainPending edge
        · subst p'
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [Function.update_of_ne he] at hp'
          exact List.mem_append_left _ (h.allocated p' hp')
      virtualSeen := h.virtualSeen, compilerBound := h.compilerBound, trace := h.trace
      bad := h.bad, share := h.share, restAgree := hframe.1, restFree := hframe.2.1
      realPrivate := h.realPrivate
      frontier := fun edge' hp' => by
        rw [hpend] at hp'
        by_cases he : edge' = edge
        · subst edge'
          rw [Function.update_self] at hp'
          cases hp'
        · rw [Function.update_of_ne (fun heq => he (chainPending_injective heq))] at hp'
          exact h.frontier edge' hp'
      candidatesPaid := h.candidatesPaid, doneCached := h.doneCached }

section Calls
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
set_option backward.isDefEq.respectTransparency false

/-- The pending call at a chain edge returns the stored answer, or it stores the answer of the
fixed noise. Both count once. -/
theorem backendT_chainPending (edge : ChainNoiseIndex) (st : CompState C)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (compBackend x q s pads u rest noise (.inl (.inl (.inl (.pending (chainPending edge)))))).run st =
      match st.1.1.1.1.data.pending (chainPending edge) with
      | some answer => pure (answer, ((((st.1.1.1.1, st.1.1.1.2 + 1), st.1.1.2), st.1.2), st.2))
      | none => pure (pendingOutput (chainPending edge) (noise edge),
          (((({ st.1.1.1.1 with data := { st.1.1.1.1.data with
            pending := Function.update st.1.1.1.1.data.pending (chainPending edge)
              (some (pendingOutput (chainPending edge) (noise edge))) } },
            st.1.1.1.2 + 1), st.1.1.2), st.1.2), st.2)) := by
  rcases edge with ⟨l, e | b, p⟩ <;>
    simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw, StateT.run,
      chainPending, freshPending] <;>
    simp only [merged, withCache] <;>
    (cases st.1.1.1.1.data.pending _) <;>
    simp [incrementCompilerCount, splitRest, withCache, erase_merge_of_restFree _ _ _ hf,
      resolvePrivateTable]

/-- A mapped source update runs with no backend call. -/
theorem runX_map_modify {α : Type} (backend : QueryImpl (SpecX C) (StateT (CompState C) ProbComp))
    (f : Unit → α) (g : SourceState C → SourceState C) (src : SourceState C) (st : CompState C) :
    runX backend (f <$> modify g) src st = pure ((f (), g src), st) := by
  rw [map_eq_bind_pure_comp, runX_bind, runX_modify, pure_bind, Function.comp_apply, runX_pure]

/-- The source side of a pending call with a stored answer. -/
theorem runX_sourcePendingX_some (p : PendingInput) (answer : DeferredOutput) (src : SourceState C)
    (st : CompState C) (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hprior : st.1.1.1.1.data.pending p = some answer) :
    runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st =
      (fun r => ((r.1, src), r.2)) <$>
        (compBackend x q s pads u rest noise (.inl (.inl (.inl (.pending p))))).run st := by
  simp [sourcePendingX, runX_bind, runX_deferred, runX_get,
    backendT_inspect capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest p st hf, hprior]
  exact runX_deferred _ _ _ _

/-- The source side of a fresh pending call with an unrevealed key. -/
theorem runX_sourcePendingX_fresh (p : PendingInput) (src : SourceState C) (st : CompState C)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hprior : st.1.1.1.1.data.pending p = none) (hrev : src.revealed p.key = none) :
    runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st =
      (fun r => ((r.1, { src with allocated := src.allocated ++ [p] }), r.2)) <$>
        (compBackend x q s pads u rest noise (.inl (.inl (.inl (.pending p))))).run st := by
  simp [sourcePendingX, runX_bind, runX_deferred, runX_get,
    backendT_inspect capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest p st hf, hprior,
    hrev, runX_map_modify]

/-- A real honest call at a chain input returns the answer of the private cache and observes it.
It runs no grind. -/
theorem chainCall_readStep (edge : ChainNoiseIndex) (a : RealState C)
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (ra : HashOutput × RealState C)
    (hra : ra ∈ support ((realCall prims x s pads u rest
      (.hash ((chainPending edge).input x.1 (s (chainPending edge).key)))).run a)) :
    ra.1 = (pendingOutput (chainPending edge) (noise edge)).interpret s ∧
      ReadStep (.hash ((chainPending edge).input x.1 (s (chainPending edge).key)))
        ((pendingOutput (chainPending edge) (noise edge)).interpret s) a ra.2 := by
  have hpre := hpriv.preload (noise_interpret x s pads noise edge)
  have hseen : ∀ w, visibleOf a (.hash ((chainPending edge).input x.1 (s (chainPending edge).key))) =
      some w → w = (pendingOutput (chainPending edge) (noise edge)).interpret s := by
    intro w hw
    have h1 := hpriv.visible _ w hw
    rw [dif_neg (not_isSlot_hash x _), hpre] at h1
    exact (Option.some.inj h1).symm
  have hb : ∀ i, SigningFlatProof.HashCallAt i ((.inr (.inr (.inl (.hash ((chainPending edge).input
      x.1 (s (chainPending edge).key)))))) : (WorldSpec C).Domain) →
      ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message := by
    intro i hi e ρ message
    have h1 := hashCallAt_read (.inl (.hash ((chainPending edge).input x.1
      (s (chainPending edge).key)))) _ (Or.inr rfl) i hi
    simp only [readInput, Query.hash.injEq] at h1
    rw [← h1]
    exact chainInput_ne_randomizer x.1 edge _ bottomLayer e ρ message
  change ra ∈ support ((ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) (.inr (.inr (.inl (.hash ((chainPending edge).input x.1
      (s (chainPending edge).key))))))).run a) at hra
  rw [rawTraceWorld_read_honest prims x (gOf s pads u) rest _ a.1 a.2] at hra
  simp only [readInput, readAnswer] at hra
  rw [realImpl_preload x s pads noise _ rest a.2 (visibleOf a) hpriv edge, pure_bind,
    noBase_cachedExtra x.2.1 x.1 _ _ _ hb] at hra
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, mem_support_pure_iff] at hra
  rw [noBase_traceStepAt x.2.1 x.1 _ _ _ _ _ hb] at hra
  subst ra
  exact ⟨rfl, rfl, hseen, rfl, rfl, rfl, rfl, _, _, rfl, rfl⟩

/-- A chain call. The real side reads the answer that the private cache holds from the start. The
compiler side returns the pending answer of the edge. -/
theorem chainPending_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (edge : ChainNoiseIndex) (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : HashOutput × RealState C)
    (hra : ra ∈ support ((realCall prims x s pads u rest
      (.hash ((chainPending edge).input x.1 (s (chainPending edge).key)))).run a))
    (rb : (DeferredOutput × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourcePendingX x.1 (chainPending edge)) src st)) :
    CallPost x q s pads u rest noise cCore
      (fun query => query = .hash ((chainPending edge).input x.1 (s (chainPending edge).key)))
      a src st (fun va vb => va = vb.interpret s ∧
        (dataOf x rb.2).pending (chainPending edge) = some vb) ra rb := by
  have hi := TprfSecurityProof.slotInput_injective (not_not.mp (not_or.mp hkeys).1)
    (not_not.mp (not_or.mp hkeys).2)
  obtain ⟨⟨hf, hc⟩, hcnt⟩ := hs
  obtain ⟨hva, hstep⟩ := chainCall_readStep prims x s pads u rest noise edge a
    (no_implicit_lambda% hf.realPrivate) ra (no_implicit_lambda% hra)
  have hle : visibleOf a ≤ visibleOf ra.2 := by
    rw [hstep.visible]
    exact le_cacheQuery_of_seen _ _ _ hstep.seen
  have hpriv1 : RealPrivate x s pads noise (gOf s pads u) rest ra.2.2 (visibleOf ra.2) := by
    have hz : ((pendingOutput (chainPending edge) (noise edge)).interpret s, a.2) ∈
        support (((Query C →ₒ HashOutput).randomOracle
          (.hash ((chainPending edge).input x.1 (s (chainPending edge).key)))).run a.2) := by
      rw [← realImpl_other x (gOf s pads u) rest _ (not_isSlot_hash x _),
        realImpl_preload x s pads noise _ rest a.2 (visibleOf a) hf.realPrivate edge]
      simp
    have ho := hf.realPrivate.observe_other _ (not_isSlot_hash x _) _ hz
    rw [hstep.priv, hstep.visible]
    exact ho
  have hf1 : SyncFields x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) (src, st) :=
    syncFields_observe x hkeys s pads u rest noise (withCarried a cCore) (withCarried ra.2 cCore)
      (src, st) hf hpriv1 hle rfl hstep.trace
  have hcount : (withCarried ra.2 cCore).1.1.1.1.1.1.2 = st.1.1.1.2 + 1 := by
    change ra.2.1.1.1.1.1.1.2 = st.1.1.1.2 + 1
    rw [hstep.count]
    exact congrArg (· + 1) hcnt
  have hframe (r0 : DeferredOutput × CompState C)
      (hr0 : r0 ∈ support ((compBackend x q s pads u rest noise
        (.inl (.inl (.inl (.pending (chainPending edge)))))).run st)) :
      Frame x rest r0.2.1.1 ∧ ShareG (gOf s pads u) r0.2.2 :=
    safe_frame capTag x hi q s pads (tauOf s pads) (gOf s pads u) noise rest
      (liftM (deferredQueryX (.pending (chainPending edge)))) (safe_deferred _ trivial) src st
      ⟨⟨hf.restAgree, hf.restFree, hf.pendingValid⟩, hf.share⟩ ((r0.1, src), r0.2) (by
        change ((r0.1, src), r0.2) ∈ support (runX (compBackend x q s pads u rest noise)
          (liftM (deferredQueryX (.pending (chainPending edge)))) src st)
        rw [runX_deferred, support_map]
        exact ⟨r0, hr0, rfl⟩)
  have frame (src' : SourceState C) (st' : CompState C)
      (hsrc : src' = src ∨ src' = { src with allocated := src.allocated ++ [chainPending edge] })
      (hpend : ∀ p, (dataOf x st).pending p ≠ none → (dataOf x st').pending p ≠ none)
      (hvirt : (dataOf x st').virtual = (dataOf x st).virtual) :
      CallFrame x (fun query => query = .hash ((chainPending edge).input x.1
        (s (chainPending edge).key))) a ra.2 (src, st) (src', st') := by
    rcases hsrc with rfl | rfl <;>
      exact { carried := hstep.carried, visible := hle, fresh := hstep.fresh
              log := hstep.realLog_le, logAgreement := hstep.logAgreement x.1
              trace := hstep.trace, signing := rfl, trees := rfl, exposed := rfl
              candidates := rfl, revealed := fun _ _ => rfl
              opened := fun _ h h' => (h' h).elim, pending := hpend
              virtual := fun T p hp => hvirt ▸ hp }
  have hrun := backendT_chainPending x q s pads u rest noise edge st hf.restFree
  cases hp : st.1.1.1.1.data.pending (chainPending edge) with
  | some answer =>
    rw [hp] at hrun
    have hpd : (dataOf x st).pending (chainPending edge) = some answer := hp
    have hc' : CacheRelation x.1 x.2.1 s (dataOf x st) (visibleOf a) := hc
    have hr0 : (answer, ((((st.1.1.1.1, st.1.1.1.2 + 1), st.1.1.2), st.1.2), st.2)) ∈
        support ((compBackend x q s pads u rest noise
          (.inl (.inl (.inl (.pending (chainPending edge)))))).run st) := by
      rw [hrun]
      simp
    have h0 := hframe _ hr0
    rw [runX_sourcePendingX_some x q s pads u rest noise _ answer src st hf.restFree hp, hrun]
      at hrb
    simp only [map_pure, mem_support_pure_iff] at hrb
    clear hrun hr0
    subst hrb
    have hvis := hc'.pending _ answer hpd
    have hv := hstep.seen _ hvis
    have hvis' : visibleOf ra.2 = visibleOf a := by
      rw [hstep.visible, ← hv]
      exact observe_same _ _ _ hvis
    refine Or.inr (Or.inr ⟨⟨hva.trans hv.symm, ?_⟩, ⟨⟨?_, ?_⟩, hcount⟩,
      frame _ _ (Or.inl rfl) (fun _ h => ?_) ?_, hmark⟩)
    · exact hpd
    · exact syncFields_count x s pads noise (gOf s pads u) rest _ src st _ hf1
    · change CacheRelation x.1 x.2.1 s (dataOf x st) (visibleOf ra.2)
      rw [hvis']
      exact hc'
    · exact h
    · rfl
  | none =>
    rw [hp] at hrun
    have hrev := hf.frontier edge hp
    have hc' : CacheRelation x.1 x.2.1 s (dataOf x st) (visibleOf a) := hc
    have hr0 : (pendingOutput (chainPending edge) (noise edge),
        (((({ st.1.1.1.1 with data := { st.1.1.1.1.data with
          pending := Function.update st.1.1.1.1.data.pending (chainPending edge)
            (some (pendingOutput (chainPending edge) (noise edge))) } },
          st.1.1.1.2 + 1), st.1.1.2), st.1.2), st.2)) ∈
        support ((compBackend x q s pads u rest noise
          (.inl (.inl (.inl (.pending (chainPending edge)))))).run st) := by
      rw [hrun]
      simp
    have h0 := hframe _ hr0
    rw [runX_sourcePendingX_fresh x q s pads u rest noise _ src st hf.restFree hp hrev, hrun]
      at hrb
    simp only [map_pure, mem_support_pure_iff] at hrb
    clear hrun hr0
    subst hrb
    refine Or.inr (Or.inr ⟨⟨hva, ?_⟩, ⟨⟨?_, ?_⟩, hcount⟩, frame _ _ (Or.inr rfl) (fun p' h => ?_) ?_,
      hmark⟩)
    · rw [dataOf_pending]
      exact Function.update_self _ _ _
    · exact syncFields_chainPending x s pads noise (gOf s pads u) rest _ src st edge _ _ hf1 hrev h0.1
    · rw [dataOf_pending]
      change CacheRelation x.1 x.2.1 s
        { dataOf x st with pending := (Function.update (dataOf x st).pending (chainPending edge)
          (some (pendingOutput (chainPending edge) (noise edge)))) } (visibleOf ra.2)
      rw [hstep.visible]
      exact cacheRelation_chainPending x.1 x.2.1 s _ _ hc' (chainPending edge) _ hstep.seen
    · rw [dataOf_pending]
      change Function.update (dataOf x st).pending (chainPending edge)
        (some (pendingOutput (chainPending edge) (noise edge))) p' ≠ none
      by_cases he : p' = chainPending edge
      · rw [he, Function.update_self]
        exact Option.some_ne_none _
      · rw [Function.update_of_ne he]
        exact h
    · rw [dataOf_pending]

end Calls

end ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.chainInput_ne_randomizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.chainInput_ne_randomizer

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.le_cacheQuery_of_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.le_cacheQuery_of_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.observe_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.observe_mem_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ReadStep.realLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ReadStep.realLog_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ReadStep.logAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ReadStep.logAgreement

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ReadStep.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ReadStep.fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ne_none_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.ne_none_of_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.syncFields_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.syncFields_observe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.cacheRelation_chainPending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.cacheRelation_chainPending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.dataOf_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.dataOf_count

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.dataOf_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.dataOf_pending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.syncFields_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.syncFields_count

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.syncFields_chainPending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.syncFields_chainPending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.backendT_chainPending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.backendT_chainPending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.runX_map_modify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.runX_map_modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.runX_sourcePendingX_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.runX_sourcePendingX_some

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.runX_sourcePendingX_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.runX_sourcePendingX_fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.chainCall_readStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.chainCall_readStep

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.chainPending_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainPending.chainPending_sync
