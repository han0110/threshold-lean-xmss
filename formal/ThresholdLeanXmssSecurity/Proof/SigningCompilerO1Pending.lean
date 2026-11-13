import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Reads

/-! # Pending commitment and top base calls

`openingPending_sync` couples a hash call at a commitment input or a top base input at its secret.

- With a stored answer both sides return it. The compiler counts the pending call
  (`backendT_openPending`).
- With no answer and an unrevealed key the real read is quiet and fresh. The two samples couple by
  `relTriple_deferredPending_terminal`.
- With no answer and a revealed key the compiler makes the ordinary hash call (`read_call`) and
  records the answer (`backendT_record`, `cacheRelation_record`).
- `syncFields_real`, `syncFields_pending` and `syncFields_count` carry the fields of the relation
  over the real read, the new pending answer and the count.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Pending
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

section Calls
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
set_option backward.isDefEq.respectTransparency false

/-- The compiler state after a pending answer is stored and counted. -/
def withPending (st : CompState C) (p : PendingInput) (answer : DeferredOutput) (count : ℕ) :
    CompState C :=
  (((({ st.1.1.1.1 with data := { st.1.1.1.1.data with
    pending := Function.update st.1.1.1.1.data.pending p (some answer) } }, count),
    st.1.1.2), st.1.2), st.2)

/-- The data of the compiler after a stored pending answer. -/
theorem dataOf_withPending (st : CompState C) (p : PendingInput) (answer : DeferredOutput)
    (count : ℕ) :
    dataOf x (withPending st p answer count) =
      { dataOf x st with pending := Function.update (dataOf x st).pending p (some answer) } := by
  simp only [dataOf, merged, withCache, withPending]

/-- A pending call at a commitment or a top base input. It returns the stored answer, or it
samples a fresh one. Both count once. -/
theorem backendT_openPending (p : PendingInput)
    (hp : (∃ e, p = .commitment e) ∨ ∃ e message, p = .base topLayer e message)
    (st : CompState C) (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (compBackend x q s pads u rest noise (.inl (.inl (.inl (.pending p))))).run st =
      match st.1.1.1.1.data.pending p with
      | some answer => pure (answer, ((((st.1.1.1.1, st.1.1.1.2 + 1), st.1.1.2), st.1.2), st.2))
      | none => (fun value : HashOutput => (pendingOutput p value,
          withPending st p (pendingOutput p value) (st.1.1.1.2 + 1))) <$> ($ᵗ HashOutput) := by
  have hraw : (compBackend x q s pads u rest noise (.inl (.inl (.inl (.pending p))))).run st =
      (fun a => (a.1, ((splitRest x.2.1 a.2, st.1.2), st.2))) <$>
        (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
          (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) q s
          (.inl (.pending p))).run (merged x.2.1 st.1.1 st.2.cache) := by
    rcases hp with ⟨e, rfl⟩ | ⟨e, message, rfl⟩ <;>
      simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw, StateT.run,
        bind_pure_comp, simulateQ_map, resolvePrivateTable_lift, ordinary]
  rw [hraw, cappedCompiler_pending_run]
  simp only [merged, withCache]
  cases hpend : st.1.1.1.1.data.pending p with
  | some answer =>
    simp [incrementCompilerCount, splitRest, withCache, erase_merge_of_restFree _ _ _ hf]
  | none =>
    simp [withPending, splitRest, withCache, erase_merge_of_restFree _ _ _ hf]

/-- A record stores the answer of a hash call with no count. -/
theorem backendT_record (p : PendingInput) (value : HashOutput) (st : CompState C)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (compBackend x q s pads u rest noise (.inl (.inl (.inl (.record p value))))).run st =
      pure ((), withPending st p (pendingOutput p value) st.1.1.1.2) := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run]
  rw [ordinary_uncounted x.1 x.2.1 q s pads (.record p value)
    (by exact not_false) (by intro p; simp)]
  simp [compilerImpl, deferredImpl, StateT.run, withPending, splitRest, merged, withCache,
    erase_merge_of_restFree _ _ _ hf, pendingOutput]
  rfl

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

/-- The source side of a fresh pending call with a revealed key and no next secret. -/
theorem runX_sourcePendingX_hash (p : PendingInput) (hnext : p.next = none) (input : Digest)
    (src : SourceState C) (st : CompState C) (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hprior : st.1.1.1.1.data.pending p = none) (hrev : src.revealed p.key = some input) :
    runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st =
      (compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash (.hash (p.input x.1 input))))))).run
        st >>= fun r => (fun r' => ((pendingOutput p r.1, { src with allocated := src.allocated ++ [p] }),
          r'.2)) <$> (compBackend x q s pads u rest noise (.inl (.inl (.inl (.record p r.1))))).run
            r.2 := by
  simp [sourcePendingX, runX_bind, runX_deferred, runX_get,
    backendT_inspect capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest p st hf, hprior,
    hrev, hnext, pendingOutput, runX_map_modify]

/-- A real call that adds one visible entry at an input that is no slot keeps the fields of the
relation. -/
theorem syncFields_real (a a' : RealState C) (b : SourceState C × CompState C) (input : Query C)
    (hslot : ¬IsSlot x input)
    (h : SyncFields x s pads noise (gOf s pads u) rest a b) (hcar : a'.1.2 = a.1.2)
    (htrace : a'.1.1.2 = a.1.1.2) (hle : visibleOf a ≤ visibleOf a')
    (hother : ∀ query, query ≠ input → visibleOf a' query = visibleOf a query)
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a'.2 (visibleOf a')) :
    SyncFields x s pads noise (gOf s pads u) rest a' b := by
  have hagree (e : KeyIndex) := randomizer_agree x.2.1 (visibleOf a) (visibleOf a') e (by
    intro T
    apply hother
    intro he
    exact hslot ⟨.inl (T, (⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩ : CPoint)),
      he⟩)
  exact
    { corrupt := hcar ▸ h.corrupt, bound := hcar ▸ h.bound, released := hcar ▸ h.released
      exposed := hcar ▸ h.exposed, candidates := hcar ▸ h.candidates, flag := hcar ▸ h.flag
      reveal := h.reveal, releasedPending := h.releasedPending
      opening := ⟨fun e he =>
          (hagree e).2.trans (h.opening.actualValue e ((hagree e).1.mp he)), h.opening.released⟩
      pendingValid := h.pendingValid, allocated := h.allocated
      virtualSeen := fun T p hp => by
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (h.virtualSeen T p hp)
        rw [hle hv]
        exact Option.some_ne_none _
      compilerBound := h.compilerBound, trace := htrace.trans h.trace, bad := h.bad
      share := h.share, restAgree := h.restAgree, restFree := h.restFree, realPrivate := hpriv
      frontier := h.frontier, candidatesPaid := h.candidatesPaid, doneCached := h.doneCached }

/-- A new pending answer of a point that is no chain edge keeps the fields of the relation. The
source allocates the point. A revealed key needs the answer in the cache. -/
theorem syncFields_pending (a : RealState C) (src : SourceState C) (st : CompState C)
    (p : PendingInput) (hchain : ∀ edge, p ≠ chainPending edge) (hnext : p.next = none)
    (answer : DeferredOutput) (hlow : ∃ d, answer.low = .known d)
    (hrel : src.revealed p.key ≠ none →
      (dataOf x st).cache (.hash (p.input x.1 (s p.key))) = some (answer.interpret s))
    (count : ℕ) (h : SyncFields x s pads noise (gOf s pads u) rest a (src, st)) :
    SyncFields x s pads noise (gOf s pads u) rest a
      ({ src with allocated := src.allocated ++ [p] }, withPending st p answer count) := by
  have hpend : (dataOf x (withPending st p answer count)).pending =
      Function.update (dataOf x st).pending p (some answer) := rfl
  exact
    { corrupt := h.corrupt, bound := h.bound, released := h.released
      exposed := h.exposed, candidates := h.candidates, flag := h.flag
      reveal := h.reveal
      releasedPending := fun p' value hp' hk => by
        rw [hpend] at hp'
        by_cases he : p' = p
        · subst p'
          rw [Function.update_self] at hp'
          cases hp'
          exact hrel hk
        · rw [Function.update_of_ne he] at hp'
          exact h.releasedPending p' value hp' hk
      opening := ⟨h.opening.actualValue, h.opening.released⟩
      pendingValid := fun p' value hp' => by
        rw [hpend] at hp'
        by_cases he : p' = p
        · subst p'
          rw [Function.update_self] at hp'
          cases hp'
          exact Or.inr ⟨hnext, hlow⟩
        · rw [Function.update_of_ne he] at hp'
          exact h.pendingValid p' value hp'
      allocated := fun p' hp' => by
        rw [hpend] at hp'
        by_cases he : p' = p
        · subst p'
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [Function.update_of_ne he] at hp'
          exact List.mem_append_left _ (h.allocated p' hp')
      virtualSeen := h.virtualSeen, compilerBound := h.compilerBound, trace := h.trace
      bad := h.bad, share := h.share, restAgree := h.restAgree, restFree := h.restFree
      realPrivate := h.realPrivate
      frontier := fun edge hp' => by
        rw [hpend, Function.update_of_ne (hchain edge).symm] at hp'
        exact h.frontier edge hp'
      candidatesPaid := h.candidatesPaid, doneCached := h.doneCached }

/-- The fields of the relation do not read the count of the compiler. -/
theorem syncFields_count (a : RealState C) (src : SourceState C) (st : CompState C) (count : ℕ)
    (h : SyncFields x s pads noise (gOf s pads u) rest a (src, st)) :
    SyncFields x s pads noise (gOf s pads u) rest a
      (src, ((((st.1.1.1.1, count), st.1.1.2), st.1.2), st.2)) :=
  ⟨h.corrupt, h.bound, h.released, h.exposed, h.candidates, h.flag, h.reveal, h.releasedPending,
    h.opening, h.pendingValid, h.allocated, h.virtualSeen, h.compilerBound, h.trace, h.bad,
    h.share, h.restAgree, h.restFree, h.realPrivate, h.frontier, h.candidatesPaid, h.doneCached⟩

/-- A record of an answer that the cache holds keeps the cache relation. -/
theorem cacheRelation_record (P : PublicParameter) (seeds : C.Term → HashOutput)
    (data : DeferredState C) (actual : HashCache C) (h : CacheRelation P seeds s data actual)
    (p : PendingInput) (answer : DeferredOutput) (hp : data.pending p = none)
    (hc : data.cache (.hash (p.input P (s p.key))) = some (answer.interpret s)) :
    CacheRelation P seeds s { data with pending := Function.update data.pending p (some answer) }
      actual := by
  refine ⟨fun query hq => h.agree query fun hs => hq ?_, fun p' value hp' => ?_⟩
  · obtain ⟨hcq, hs'⟩ := hs
    refine ⟨hcq, ?_⟩
    rcases hs' with ⟨p', value, hp', he⟩ | hv
    · have hne : p' ≠ p := by
        rintro rfl
        rw [hp] at hp'
        cases hp'
      refine Or.inl ⟨p', value, ?_, he⟩
      change Function.update data.pending p (some answer) p' = some value
      rw [Function.update_of_ne hne]
      exact hp'
    · exact Or.inr hv
  · by_cases he : p' = p
    · subst p'
      simp only [Function.update_self, Option.some.injEq] at hp'
      subst value
      have hns : ¬SuspendedQuery P seeds s data (.hash (p.input P (s p.key))) := by
        intro hs
        have h0 := hs.1
        rw [hc] at h0
        cases h0
      rw [h.agree _ hns, hc]
    · change Function.update data.pending p (some answer) p' = some value at hp'
      rw [Function.update_of_ne he] at hp'
      exact h.pending p' value hp'

set_option maxHeartbeats 1600000 in
/-- An ordinary hash read with no bottom base input caches its answer. -/
theorem ordinaryHash_cached (hinj : Function.Injective x.2.1) (input : Query C)
    (hn : ¬IsSlot x input)
    (hcall : ∀ i, SigningFlatProof.HashCallAt i (.inr (.inr (.inl input))) →
      ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message)
    (st : CompState C) (r : HashOutput × CompState C)
    (hr : r ∈ support ((compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash input))))).run
      st)) : (dataOf x r.2).cache input = some r.1 := by
  have hc := compilerRead_view x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest input hn st
  rw [cacheRead_noBase x.1 x.2.1 _ _ _ _ _ hcall] at hc
  have hm : compilerReadView x r ∈ support (compilerReadView x <$>
      (compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash input))))).run st) := by
    rw [support_map]
    exact ⟨r, hr, rfl⟩
  rw [hc, support_map] at hm
  obtain ⟨w, hw, he⟩ := hm
  have h1 := (randomOracle_support input _ w hw).2.1
  have h2 : w.1 = r.1 := congrArg Prod.fst he
  have h3 : w.2 = (dataOf x r.2).cache := congrArg (fun z => z.2.1) he
  rw [← h3, ← h2]
  exact h1

/-- The read on the free copy is the honest call. -/
theorem readCall_false (rq : (RoSpec C).Domain) :
    readCall prims x s pads u rest false rq = realWorld prims x s pads u rest (.inr (.inr rq)) := by
  simp [readCall]

section Honest
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  SigningLaneUnionProof.traceStepAt

/-- `readCall_view` for an honest call. -/
theorem realCall_view (query : Query C) (a : RealState C)
    (hr : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (hhit : (∃ value, visibleOf a query = some value) ∨ Quiet x s pads noise query)
    (hbase : ∀ input, query = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message) :
    realReadView <$> (realWorld prims x s pads u rest (.inr (.inr (.inl query)))).run a =
      (fun w => (w.1, w.2, a.1.1.2)) <$>
        (((Query C →ₒ HashOutput).randomOracle query).run (visibleOf a)) := by
  have h := readCall_view prims x s pads u rest noise false (.inl query) a hr hhit hbase
  rw [readCall_false] at h
  exact h

set_option maxHeartbeats 1600000 in
/-- The effect of an honest call with no bottom base input on the real state. -/
theorem realCall_support (query : Query C) (t : (WorldSpec C).Domain)
    (ht : t = .inr (.inr (.inl query))) (a : RealState C)
    (hr : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (hhit : (∃ value, visibleOf a query = some value) ∨ Quiet x s pads noise query)
    (hbase : ∀ input, query = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
    (ra : (WorldSpec C).Range t × RealState C)
    (hra : ra ∈ support ((realWorld prims x s pads u rest t).run a)) :
    ∃ w ∈ support (((Query C →ₒ HashOutput).randomOracle query).run (visibleOf a)),
      visibleOf ra.2 = w.2 ∧ ra.2.1.2 = a.1.2 ∧ ra.2.1.1.2 = a.1.1.2 ∧
      ra.2.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1 ∧ realLog a ≤ realLog ra.2 ∧
      (SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1 →
        SigningPartnerCompareProof.LogAgreement x.1 ra.2.1.1.1.1.1) := by
  have ht' : t = .inl (.inl (.inr (.inl query))) ∨ t = .inr (.inr (.inl query)) := Or.inr ht
  have hb : ∀ i, SigningFlatProof.HashCallAt i t →
      ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message :=
    fun i hi => hbase i (hashCallAt_read (.inl query) t ht' i hi)
  have hcount := (realWorld_read_fields_route prims x (gOf s pads u) rest (.inl query) t ht' a ra
    hra).2
  change ra ∈ support ((ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) t).run (a.1, a.2)) at hra
  rw [rawTraceWorld_read_route prims x (gOf s pads u) rest (.inl query) t ht' a.1 a.2] at hra
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hra
  obtain ⟨z, hz, y, hy, rfl⟩ := hra
  rw [noBase_cachedExtra x.2.1 x.1 _ _ t hb] at hy
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hy
  subst hy
  rw [realRead_ordinary x s pads noise (gOf s pads u) rest a.2 (visibleOf a) hr
    (readInput (.inl query)) hhit, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hv := randomOracle_observe (visibleOf a) query w hw
  refine ⟨w, hw, hv, rfl, noBase_traceStepAt x.2.1 x.1 _ _ _ t _ hb, hcount,
    logCache_le_logQuery _ _ _, fun hL => ?_⟩
  have hfinal := SigningPartnerCompareProof.logAgreement_hash x.1 query _ hL w hw
    (a.1.1.1.1.1.2.logQuery t (cast (by rcases ht' with rfl | rfl <;> rfl)
      (readAnswer prims (.inl query) w.1))) ?_ (a.1.1.1.1.1.1.2 + SeedHitProof.signCost t)
  · rw [← hv] at hfinal
    exact hfinal
  intro q'
  rw [SigningCacheLogProof.logCache_logQuery]
  subst ht
  rfl

end Honest

set_option maxHeartbeats 1600000 in
/-- A commitment call or a top base call. With an answer already pending both sides return it. With
a revealed key the compiler side makes the hash call. Else both sides sample a fresh answer, and
the premise `hfree` states that the real input is fresh. -/
theorem openingPending_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (p : PendingInput)
    (hp : (∃ e, p = .commitment e) ∨ ∃ e message, p = .base topLayer e message)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (hfree : src.revealed p.key = none → (dataOf x st).pending p = none →
      visibleOf a (.hash (p.input x.1 (s p.key))) = none)
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false) :
    RelTriple ((realCall prims x s pads u rest (.hash (p.input x.1 (s p.key)))).run a)
      (runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st)
      (fun ra rb => CallPost x q s pads u rest noise cCore
        (fun query => query = .hash (p.input x.1 (s p.key))) a src st
        (fun va vb => va = vb.interpret s ∧ (∃ d, vb.low = .known d) ∧
          (dataOf x rb.2).pending p = some vb) ra rb) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  have hsf := hs.1.1
  have hnext : p.next = none := by
    rcases hp with ⟨e, rfl⟩ | ⟨e, message, rfl⟩ <;> rfl
  have hchain : ∀ edge, p ≠ chainPending edge := by
    intro edge he
    rcases edge with ⟨l, k | b, d⟩ <;> rcases hp with ⟨e, rfl⟩ | ⟨e, message, rfl⟩ <;>
      simp [chainPending] at he
  have hslot : ¬IsSlot x (readInput (C := C) (.inl (.hash (p.input x.1 (s p.key))))) :=
    not_isSlot_hash x _
  have hbase : ∀ input, readInput (C := C) (.inl (.hash (p.input x.1 (s p.key)))) = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message := by
    intro input hin e ρ message he
    have hin' : p.input x.1 (s p.key) = input := Query.hash.inj hin
    rw [← hin'] at he
    have hpe := pendingInput_injective x.1 p (.base bottomLayer e message) (s p.key) ρ he
    rcases hp with ⟨e', rfl⟩ | ⟨e', message', rfl⟩
    · cases hpe
    · simp only [PendingInput.base.injEq] at hpe
      exact absurd hpe.1 (by decide)
  have hcall : ∀ i, SigningFlatProof.HashCallAt (C := C) i
      (.inr (.inr (.inl (.hash (p.input x.1 (s p.key)))))) →
      ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message := by
    intro i hi
    rcases hi with h | h
    · cases h
    · exact hbase i (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h)))
  show RelTriple
    ((realWorld prims x s pads u rest (.inr (.inr (.inl (.hash (p.input x.1 (s p.key))))))).run a) _ _
  cases hprior : st.1.1.1.1.data.pending p with
  | some answer =>
    have hcomp : runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st =
        pure ((answer, src), ((((st.1.1.1.1, st.1.1.1.2 + 1), st.1.1.2), st.1.2), st.2)) := by
      rw [runX_sourcePendingX_some x q s pads u rest noise p answer src st hsf.restFree hprior,
        backendT_openPending x q s pads u rest noise p hp st hsf.restFree, hprior]
      simp only [map_pure]
    rw [hcomp]
    have hvisible : visibleOf a (.hash (p.input x.1 (s p.key))) = some (answer.interpret s) :=
      hs.1.2.pending p answer hprior
    have hhit : (∃ value, visibleOf a (.hash (p.input x.1 (s p.key))) = some value) ∨
        Quiet x s pads noise (.hash (p.input x.1 (s p.key))) := Or.inl ⟨_, hvisible⟩
    have hbase' : ∀ e ρ message, p.input x.1 (s p.key) ≠ randomizerInput x.1 bottomLayer e ρ message :=
      hbase _ rfl
    refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
    rintro ra rb ⟨-, hra, hrb⟩
    rw [mem_support_pure_iff] at hrb
    subst rb
    obtain ⟨w, hw, hvis, hcar, htrace, hcount, hlog, hlogA⟩ :=
      realCall_support prims x s pads u rest noise (.hash (p.input x.1 (s p.key))) _ rfl a
        hsf.realPrivate hhit hbase ra (by with_reducible exact hra)
    have hw' : w = (answer.interpret s, visibleOf a) := by
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hvisible,
        mem_support_pure_iff] at hw
      exact hw
    have hval : ra.1 = answer.interpret s := by
      have hv := realCall_view prims x s pads u rest noise _ a hsf.realPrivate hhit hbase
      have hm : realReadView ra ∈ support (realReadView <$>
          (realWorld prims x s pads u rest (.inr (.inr (.inl (.hash (p.input x.1 (s p.key))))))).run a) := by
        rw [support_map]
        exact ⟨ra, by with_reducible exact hra, rfl⟩
      rw [hv, OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hvisible, map_pure,
        mem_support_pure_iff] at hm
      exact congrArg Prod.fst hm
    have hpriv : RealPrivate x s pads noise (gOf s pads u) rest ra.2.2 (visibleOf ra.2) :=
      realWorld_preserves prims (.inr (.inr (.inl (.hash (p.input x.1 (s p.key)))))) a
        hsf.realPrivate ra (by with_reducible exact hra)
    have hvis' : visibleOf ra.2 = visibleOf a := hvis.trans (congrArg Prod.snd hw')
    refine Or.inr (Or.inr ⟨⟨hval, ?_, hprior⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_, hmark⟩)
    · rcases hsf.pendingValid p answer hprior with ⟨k, hk, -⟩ | ⟨-, hd⟩
      · rw [hnext] at hk
        cases hk
      · exact hd
    · exact syncFields_count x s pads u rest noise _ src st _
        (syncFields_real x s pads u rest noise (withCarried a cCore) (withCarried ra.2 cCore)
          (src, st) _ hslot hsf rfl htrace (le_of_eq hvis'.symm)
          (fun query _ => congrFun hvis' query) hpriv)
    · change CacheRelation x.1 x.2.1 s (dataOf x st) (visibleOf ra.2)
      rw [hvis']
      exact hs.1.2
    · change ra.2.1.1.1.1.1.1.2 = st.1.1.1.2 + 1
      rw [hcount]
      exact congrArg (· + 1) hs.2
    · exact ⟨hcar, le_of_eq hvis'.symm, fun query hq => Or.inl (by rw [hvis'] at hq; exact hq),
        hlog, hlogA, htrace, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h h' => (h' h).elim,
        fun _ h => h, fun _ _ h => h⟩
  | none =>
    cases hrev : src.revealed p.key with
    | none =>
      have hfresh : visibleOf a (.hash (p.input x.1 (s p.key))) = none := hfree hrev hprior
      have hquiet : Quiet x s pads noise (.hash (p.input x.1 (s p.key))) := by
        refine ⟨not_isSlot_hash x _, ?_⟩
        cases hc : realCache x s pads noise (.hash (p.input x.1 (s p.key))) with
        | none => rfl
        | some v =>
          obtain ⟨edge, he⟩ := realCache_some_chain x s pads noise _ v hc
          exact absurd (pendingInput_injective x.1 p (chainPending edge) _ _ (Query.hash.inj he))
            (hchain edge)
      have hhit : (∃ value, visibleOf a (.hash (p.input x.1 (s p.key))) = some value) ∨
          Quiet x s pads noise (.hash (p.input x.1 (s p.key))) := Or.inr hquiet
      have hprior' : (dataOf x st).pending p = none := hprior
      let src' : SourceState C := { src with allocated := src.allocated ++ [p] }
      have hcomp : runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st =
          (fun value : HashOutput => ((pendingOutput p value, src'),
            withPending st p (pendingOutput p value) (st.1.1.1.2 + 1))) <$> ($ᵗ HashOutput) := by
        rw [runX_sourcePendingX_fresh x q s pads u rest noise p src st hsf.restFree hprior hrev,
          backendT_openPending x q s pads u rest noise p hp st hsf.restFree, hprior]
        simp only [Functor.map_map]
        rfl
      have hd : (fun value : HashOutput => ((pendingOutput p value, src'),
            withPending st p (pendingOutput p value) (st.1.1.1.2 + 1))) <$> ($ᵗ HashOutput) =
          (fun b : DeferredOutput × DeferredState C => ((b.1, src'),
            withPending st p b.1 (st.1.1.1.2 + 1))) <$>
            (deferredImpl (.pending p)).run (dataOf x st) := by
        simp only [deferredImpl, StateT.run, hprior', samplePending_eq_map, Functor.map_map]
      rw [hcomp]
      have hv := realCall_view prims x s pads u rest noise _ a hsf.realPrivate hhit hbase
      have core : RelTriple (realReadView <$>
          (realWorld prims x s pads u rest (.inr (.inr (.inl (.hash (p.input x.1 (s p.key))))))).run a)
          (id <$> ((fun value : HashOutput => ((pendingOutput p value, src'),
            withPending st p (pendingOutput p value) (st.1.1.1.2 + 1))) <$> ($ᵗ HashOutput)))
          (fun va vb => va.1 = vb.1.1.interpret s ∧
            CacheRelation x.1 x.2.1 s (dataOf x vb.2) va.2.1) := by
        rw [hv, id_map, hd]
        apply relTriple_map
        refine relTriple_post_mono (relTriple_supported
          (relTriple_deferredPending_terminal x.1 x.2.1 s (dataOf x st) (visibleOf a) hs.1.2 p hnext
            hprior' hfresh)) ?_
        rintro w b ⟨⟨he, hrel⟩, -, hb'⟩
        refine ⟨he, ?_⟩
        simp only [deferredImpl, StateT.run, hprior', samplePending_eq_map, Functor.map_map,
          support_map, Set.mem_image] at hb'
        obtain ⟨v, -, rfl⟩ := hb'
        exact hrel
      refine relTriple_post_mono (relTriple_of_projections _ _ _ _ core) ?_
      rintro ra rb ⟨⟨hval, hrel⟩, hra, hrb⟩
      simp only [support_map, Set.mem_image] at hrb
      obtain ⟨v, -, rfl⟩ := hrb
      obtain ⟨w, hw, hvis, hcar, htrace, hcount, hlog, hlogA⟩ :=
        realCall_support prims x s pads u rest noise (.hash (p.input x.1 (s p.key))) _ rfl a
          hsf.realPrivate hhit hbase ra (by with_reducible exact hra)
      have hpriv : RealPrivate x s pads noise (gOf s pads u) rest ra.2.2 (visibleOf ra.2) :=
        realWorld_preserves prims (.inr (.inr (.inl (.hash (p.input x.1 (s p.key)))))) a
          hsf.realPrivate ra (by with_reducible exact hra)
      obtain ⟨hle, -, hother⟩ := randomOracle_support _ _ w hw
      have hgrow : visibleOf a ≤ visibleOf ra.2 := hvis ▸ hle
      have hlow : (pendingOutput p v).low = .known (XmssSecurity.Rom.hashOutputEquivDigestPair v).2 := by
        simp [pendingOutput, hnext]
      refine Or.inr (Or.inr ⟨⟨hval, ⟨_, hlow⟩, Function.update_self ..⟩, ⟨⟨?_, hrel⟩, ?_⟩, ?_,
        hmark⟩)
      · exact syncFields_pending x s pads u rest noise _ src st p hchain hnext _ ⟨_, hlow⟩
          (fun h => absurd hrev h) _
          (syncFields_real x s pads u rest noise (withCarried a cCore) (withCarried ra.2 cCore)
            (src, st) _ (not_isSlot_hash x _) hsf rfl htrace hgrow
            (fun query hq => hvis ▸ hother query hq) hpriv)
      · change ra.2.1.1.1.1.1.1.2 = st.1.1.1.2 + 1
        rw [hcount]
        exact congrArg (· + 1) hs.2
      · refine ⟨hcar, hgrow, ?_, hlog, hlogA, htrace, rfl, rfl, rfl, rfl, fun _ _ => rfl,
          fun _ h h' => (h' h).elim, ?_, fun _ _ h => h⟩
        · intro query hq
          by_cases he : query = .hash (p.input x.1 (s p.key))
          · exact Or.inr he
          · left
            rw [hvis, hother query he] at hq
            exact hq
        · intro p' hp'
          change Function.update (dataOf x st).pending p (some (pendingOutput p v)) p' ≠ none
          by_cases he : p' = p
          · subst he
            rw [Function.update_self]
            exact Option.some_ne_none _
          · rw [Function.update_of_ne he]
            exact hp'
    | some input =>
      have hin : input = s p.key := hsf.reveal.2 p.key input hrev
      subst hin
      have hno : ∀ k, hiddenCandidate x.1 (p.input x.1 (s p.key)) = some (k, s k) →
          src.revealed k ≠ none := by
        intro k hk
        rw [PendingInput.hiddenCandidate] at hk
        have hkey : p.key = k := (Prod.mk.inj (Option.some.inj hk)).1
        subst hkey
        rw [hrev]
        exact Option.some_ne_none _
      rcases hash_dichotomy x s pads noise src (dataOf x st) (visibleOf a) hs.1.2
          hsf.releasedPending hsf.frontier (p.input x.1 (s p.key)) with ⟨k, hk, hrk⟩ | ⟨hns, hread⟩
      · exact absurd hrk (hno k hk)
      rw [runX_sourcePendingX_hash x q s pads u rest noise p hnext (s p.key) src st hsf.restFree
        hprior hrev]
      have hrc := read_call prims x q s pads u rest noise hkeys false cCore
        (.inl (.hash (p.input x.1 (s p.key)))) hslot hbase a src st hs hread hns
      rw [readCall_false] at hrc
      rw [← bind_pure ((realWorld prims x s pads u rest
        (.inr (.inr (.inl (.hash (p.input x.1 (s p.key))))))).run a)]
      refine relTriple_bind (relTriple_supported hrc) ?_
      rintro ra r ⟨⟨hval, hsync, hframe, hmk⟩, -, hr⟩
      rw [backendT_record x q s pads u rest noise p r.1 r.2 hsync.1.1.restFree, map_pure]
      apply relTriple_pure_pure
      have hcached := ordinaryHash_cached x q s pads u rest noise hinj (.hash (p.input x.1 (s p.key)))
        (not_isSlot_hash x _) hcall st r (by with_reducible exact hr)
      have hpend : (dataOf x r.2).pending p = none := by
        rw [(compilerRead_fields x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest
          (.hash (p.input x.1 (s p.key))) (not_isSlot_hash x _) st r
          (by with_reducible exact hr)).2.2.2.2.1]
        exact hprior
      have hinterp : (pendingOutput p r.1).interpret s = r.1 := by
        simp [pendingOutput, hnext, DeferredOutput.interpret, DeferredDigest.interpret]
      have hlow : (pendingOutput p r.1).low =
          .known (XmssSecurity.Rom.hashOutputEquivDigestPair r.1).2 := by
        simp [pendingOutput, hnext]
      have hc' : (dataOf x r.2).cache (.hash (p.input x.1 (s p.key))) =
          some ((pendingOutput p r.1).interpret s) := by
        rw [hinterp]
        exact hcached
      have hrec := cacheRelation_record s x.1 x.2.1 (dataOf x r.2) _ hsync.1.2 p _ hpend hc'
      have hcr : CacheRelation x.1 x.2.1 s
          (dataOf x (withPending r.2 p (pendingOutput p r.1) r.2.1.1.1.2))
          (visibleOf (withCarried ra.2 cCore)) :=
        (dataOf_withPending x r.2 p (pendingOutput p r.1) r.2.1.1.1.2).symm ▸ hrec
      have hfields := syncFields_pending x s pads u rest noise _ src r.2 p hchain hnext _ ⟨_, hlow⟩
          (fun _ => hc') r.2.1.1.1.2 hsync.1.1
      refine Or.inr (Or.inr ⟨⟨hval.trans hinterp.symm, ⟨_, hlow⟩, Function.update_self ..⟩,
        ⟨⟨hfields, hcr⟩, hsync.2⟩, ?_, hmk.trans hmark⟩)
      refine (CallFrame.trans x _ _ a ra.2 ra.2 (src, st) (src, r.2)
        ({ src with allocated := src.allocated ++ [p] },
          withPending r.2 p (pendingOutput p r.1) r.2.1.1.1.2) hframe
        ⟨rfl, le_rfl, fun _ h => Or.inl h, le_rfl, id, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
          fun _ h h' => (h' h).elim, ?_, fun _ _ h => h⟩).weaken x _ _ _ _ _ _
        (fun query h => h.elim id False.elim)
      intro p' hp'
      change Function.update (dataOf x r.2).pending p (some (pendingOutput p r.1)) p' ≠ none
      by_cases he : p' = p
      · subst he
        rw [Function.update_self]
        exact Option.some_ne_none _
      · rw [Function.update_of_ne he]
        exact hp'

end Calls

end ThresholdLeanXmssSecurity.SigningCompilerO1Pending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.dataOf_withPending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.dataOf_withPending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.backendT_openPending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.backendT_openPending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.backendT_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.backendT_record

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_map_modify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_map_modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_sourcePendingX_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_sourcePendingX_some

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_sourcePendingX_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_sourcePendingX_fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_sourcePendingX_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.runX_sourcePendingX_hash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.syncFields_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.syncFields_real

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.syncFields_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.syncFields_pending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.syncFields_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.syncFields_count

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.cacheRelation_record' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.cacheRelation_record

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.ordinaryHash_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.ordinaryHash_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.readCall_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.readCall_false

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.realCall_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.realCall_view

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.realCall_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.realCall_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pending.openingPending_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pending.openingPending_sync
