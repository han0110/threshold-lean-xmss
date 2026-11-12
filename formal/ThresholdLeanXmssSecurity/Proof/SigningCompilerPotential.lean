import ThresholdLeanXmssSecurity.Proof.SigningLaneHybridCap
import ThresholdLeanXmssSecurity.Proof.SigningLaneHybrid

/-!
# The signing compiler's counted potential

The trace freezes the message-cache counts of a key at its first canonical
base call. Its eager grind is recorded as a deterministic replay certificate,
which persists under every conservative cache extension.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerPotential
open SigningLaneHybridCapProof SigningFlatProof SigningFlatEagerProof
  SigningLane2BridgeProof SigningLane2FlatProof SigningCappedExpectProof SigningOpeningProof
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Every recorded key has its fixed PRF terms and its complete canonical grind in the cache. -/
def EntryTrials (seeds : C.Term → HashOutput) (P : PublicParameter) (cache : HashCache C)
    (trace : XmssSecurity.SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, SigningGuessProof.RandomizerCached seeds cache entry.request.leafIndex ∧
    ∃ answer, cache (.hash (randomizerInput P bottomLayer entry.request.leafIndex
      (SigningGuessProof.cachedRandomizer seeds cache entry.request.leafIndex)
      (bytesLE 32 entry.request.message))) = some answer ∧
      DeterministicSigning.Resolves cache
        (baseGrind P entry.request.leafIndex entry.request.message answer) ()

/-- Completed deterministic grinds and their PRF terms survive cache growth. -/
theorem EntryTrials.mono {seeds : C.Term → HashOutput} {P : PublicParameter}
    {cache larger : HashCache C} {trace : XmssSecurity.SigningCacheTrace}
    (h : EntryTrials seeds P cache trace) (hle : cache ≤ larger) :
    EntryTrials seeds P larger trace := by
  intro entry he
  obtain ⟨hprf, answer, ha, resolved⟩ := h entry he
  refine ⟨SigningR1FixedProof.randomizerCached_mono hle hprf, answer, ?_, resolved.mono hle⟩
  rw [← SigningGuessProof.cachedRandomizer_stable seeds cache larger _ hle hprf]
  exact hle ha

/-- The cached trigger runs the queried key's canonical grind, independently of its chosen witness. -/
theorem cachedExtra_base (seeds : C.Term → HashOutput) (P : PublicParameter)
    (before after : FlatState C) (t : (WorldSpec C).Domain) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds before.1.1.1 e)
    (hcall : BaseCall P e (SigningGuessProof.cachedRandomizer seeds before.1.1.1 e) before.2.1 t)
    (bound : before.2.1.bound e = some message) (answer : HashOutput)
    (cached : after.1.1.1 (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds before.1.1.1 e) (bytesLE 32 message))) = some answer) :
    SigningR1FixedProof.cachedExtra seeds P before t after = baseGrind P e message answer := by
  have base : ∃ e, BaseCall P e (SigningGuessProof.cachedRandomizer seeds before.1.1.1 e) before.2.1 t :=
    ⟨e, hcall⟩
  have chosen := SigningR1FixedProof.baseCall_key_eq base.choose_spec hcall
  rw [SigningR1FixedProof.cachedExtra, if_pos ⟨e, hprf, hcall⟩,
    grindExtra, dif_pos base, chosen]
  simp only [bound, cached]


/-- A concrete hash step retains the underlying random-oracle support point. -/
theorem deferred_hash_support (q : Query C) (st : DeferredState C)
    (r : HashOutput × DeferredState C)
    (hr : r ∈ support ((deferredImpl (.hash q)).run st)) :
    (r.1, r.2.cache) ∈ support (((Query C →ₒ HashOutput).randomOracle q).run st.cache) := by
  simp only [deferredImpl, StateT.run, support_map] at hr
  obtain ⟨raw, hraw, rfl⟩ := hr
  exact hraw

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- A new trace entry records the grind just executed by the backend. Every
older entry retains its deterministic replay through conservative cache growth. -/
theorem compilerImpl_entryTrials (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C)
    (hs : EntryTrials seeds P st.data.cache st.trace.1)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) :
    EntryTrials seeds P r.2.data.cache r.2.trace.1 := by
  have grow := compilerImpl_cache_le P seeds t st r hr
  cases t with
  | hash q =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, hb, rfl⟩ := hr
      have old : EntryTrials seeds P b.2 st.trace.1 := hs.mono grow
      intro entry he
      change entry ∈ (SigningLaneUnionProof.traceStepAt seeds P st.data.cache (compilerSigning st)
        (.inr (.inr (.inl q))) b.2 st.trace).1 at he
      unfold SigningLaneUnionProof.traceStepAt at he
      split at he
      · rename_i hbase
        cases hm : (compilerSigning st).bound hbase.choose with
        | none =>
          simp only [hm] at he
          exact old entry he
        | some message =>
          simp only [hm] at he
          split at he
          · rcases List.mem_append.mp he with he | he
            · exact old entry he
            · simp only [List.mem_singleton] at he
              rw [he]
              have hprf := hbase.choose_spec.1
              have hcall := hbase.choose_spec.2
              have raw := deferred_hash_support q st.data a ha
              have hself := (randomOracle_support q st.data.cache (a.1, a.2.cache) raw).2.1
              have cached : a.2.cache (.hash (randomizerInput P bottomLayer hbase.choose
                  (SigningGuessProof.cachedRandomizer seeds st.data.cache hbase.choose)
                  (bytesLE 32 message))) = some a.1 := by
                have call := hashCallAt_of_baseCall hcall hm
                rcases call with impossible | call
                · cases impossible
                · have address : q = .hash (randomizerInput P bottomLayer hbase.choose
                      (SigningGuessProof.cachedRandomizer seeds st.data.cache hbase.choose)
                      (bytesLE 32 message)) := by
                    simpa only [Sum.inr.injEq, Sum.inl.injEq] using call
                  rw [← address]
                  exact hself
              have extra := cachedExtra_base seeds P
                (((st.data.cache, 0), []), compilerSigning st, false)
                (((a.2.cache, 0), []), compilerSigning st, false)
                (.inr (.inr (.inl q))) hbase.choose message hprf hcall hm a.1 cached
              rw [extra] at hb
              have replay := DeterministicSigning.resolves_of_run
                (baseGrind P hbase.choose message a.1) a.2.cache b hb
              have after : a.2.cache ≤ b.2 := DeterministicSigning.cache_le_of_run _ _ _ hb
              change SigningGuessProof.RandomizerCached seeds b.2 hbase.choose ∧
                ∃ answer, b.2 (.hash (randomizerInput P bottomLayer hbase.choose
                  (SigningGuessProof.cachedRandomizer seeds b.2 hbase.choose)
                  (bytesLE 32 message))) = some answer ∧
                    DeterministicSigning.Resolves b.2 (baseGrind P hbase.choose message answer) ()
              refine ⟨SigningR1FixedProof.randomizerCached_mono grow hprf, a.1, ?_, replay⟩
              rw [← SigningGuessProof.cachedRandomizer_stable seeds st.data.cache b.2 _ grow hprf]
              exact after cached
          · exact old entry he
      · exact old entry he
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hs
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact hs.mono grow

/-- Every compiler-reachable trace has replayable canonical base grinds. -/
theorem reachable_entryTrials (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : CompilerBackend C × ℕ) (hs : CompilerReachable P seeds st) :
    EntryTrials seeds P st.1.data.cache st.1.trace.1 := by
  induction hs with
  | initial => exact fun _ h => (List.not_mem_nil h).elim
  | step t st r _ hr ih =>
      simp only [countImpl, StateT.run_mk, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact compilerImpl_entryTrials P seeds t st.1 ih a ha


/-- With no canonical-base trigger, the compiler performs just the one
ordinary hash query; its pending data, binding map and trace are unchanged. -/
theorem compiler_hash_no_trigger (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) (st : CompilerBackend C)
    (noBase : ¬ ∃ e, SigningGuessProof.RandomizerCached seeds st.data.cache e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.data.cache e)
        (compilerSigning st) (.inr (.inr (.inl q)))) :
    (compilerImpl P seeds (.hash q)).run st =
      (fun r => (r.1, { st with data := { st.data with cache := r.2 } })) <$>
        (((Query C →ₒ HashOutput).randomOracle q).run st.data.cache) := by
  simp only [compilerImpl, deferredImpl, StateT.run, bind_map_left,
    SigningR1FixedProof.cachedExtra, noBase, if_false, simulateQ_pure, SigningLaneUnionProof.traceStepAt]
  rfl

/-- Message-digest calls can never trigger a randomizer-base grind. -/
theorem message_no_trigger (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : HashInput) (hmsg : IsMsg input) (st : CompilerBackend C) :
    ¬ ∃ e, SigningGuessProof.RandomizerCached seeds st.data.cache e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.data.cache e)
        (compilerSigning st) (.inr (.inr (.inl (.hash input)))) := by
  rintro ⟨e, _, hcall⟩
  exact SigningLaneHybridProof.not_baseCall_of_isMsg P
    (SigningGuessProof.cachedRandomizer seeds st.data.cache) (compilerSigning st)
    hmsg (Or.inr rfl) ⟨e, hcall⟩

/-- The concrete message step has exactly the raw random-oracle cache law. -/
theorem compiler_hash_message (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : HashInput) (hmsg : IsMsg input) (st : CompilerBackend C) :
    (compilerImpl P seeds (.hash (.hash input))).run st =
      (fun r => (r.1, { st with data := { st.data with cache := r.2 } })) <$>
        (((Query C →ₒ HashOutput).randomOracle (.hash input)).run st.data.cache) :=
  compiler_hash_no_trigger P seeds (.hash input) st (message_no_trigger P seeds input hmsg st)


/-- One ordinary hash call adds at most one message input to the frozen counts. -/
theorem raw_hash_count_le (P : PublicParameter) (input : HashInput) (cache : HashCache C)
    (trace : XmssSecurity.SigningCacheTrace) (r : HashOutput × HashCache C)
    (run : r ∈ support (((Query C →ₒ HashOutput).randomOracle (.hash input)).run cache)) :
    XmssSecurity.Ghost.nCount P (keptView IsMsg r.2) trace ≤
      XmssSecurity.Ghost.nCount P (keptView IsMsg cache) trace + 1 := by
  cases hc : cache (.hash input) with
  | some value =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at run
      subst r
      exact Nat.le_succ _
  | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc] at run
      simp only [support_map, Set.mem_image] at run
      obtain ⟨value, _, rfl⟩ := run
      by_cases hmsg : IsMsg input
      · rw [keptView_cacheQuery_of_kept hmsg]
        have empty : keptView IsMsg cache input = none := by
          change (if IsMsg input then cache (.hash input) else none) = none
          rw [if_pos hmsg]
          exact hc
        exact XmssSecurity.Ghost.counts_fresh_le empty value
      · rw [keptView_cacheQuery_of_not (K := IsMsg) (fun x he => by cases he; exact hmsg)]
        omega

/-- The trace decoder leaves an already recorded canonical base unchanged. -/
theorem traceStepAt_traced_base (P : PublicParameter) (seeds : C.Term → HashOutput)
    (cache completed : HashCache C) (state : TsigState C)
    (trace : XmssSecurity.SigningCacheTrace × Bool) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds cache e)
    (bound : state.bound e = some message) (answer : HashOutput)
    (cached : cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message))) = some answer)
    (recorded : e ∈ trace.1.leafIndices) :
    SigningLaneUnionProof.traceStepAt seeds P cache state
      (.inr (.inr (.inl (.hash (randomizerInput P bottomLayer e
        (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message)))))) completed trace = trace := by
  let call : (WorldSpec C).Domain := .inr (.inr (.inl (.hash (randomizerInput P bottomLayer e
    (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message)))))
  have base : BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e) state call :=
    ⟨_, by rw [baseInput, bound]; rfl, Or.inr rfl⟩
  have trigger : ∃ e, SigningGuessProof.RandomizerCached seeds cache e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e) state call := ⟨e, hprf, base⟩
  have chosen := SigningR1FixedProof.baseCall_key_eq trigger.choose_spec.2 base
  change SigningLaneUnionProof.traceStepAt seeds P cache state call completed trace = trace
  rw [SigningLaneUnionProof.traceStepAt, dif_pos trigger, chosen]
  simp only [bound, cached, reduceCtorEq, if_false, recorded, not_true_eq_false,
    decide_false, Bool.or_false]

/-- At a traced key, the same bound message and completed grind are available
without an independent choice of cache witness. -/
theorem traced_trials (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : CompilerBackend C)
    (bases : SigningLane2TraceLinkProof.EntryBases seeds P st.data.cache (compilerSigning st) st.trace.1)
    (trials : EntryTrials seeds P st.data.cache st.trace.1)
    (e : KeyIndex) (message : Message) (bound : st.bound e = some message)
    (recorded : e ∈ st.trace.1.leafIndices) :
    ∃ answer, st.data.cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message))) = some answer ∧
      DeterministicSigning.Resolves st.data.cache (baseGrind P e message answer) () := by
  obtain ⟨entry, he, leaf⟩ := List.mem_map.mp recorded
  have hb := (bases entry he).1
  change st.bound entry.request.leafIndex = some entry.request.message at hb
  rw [leaf] at hb
  have hm := Option.some.inj (hb.symm.trans bound)
  obtain ⟨_, answer, cached, resolved⟩ := trials entry he
  rw [leaf, hm] at cached resolved
  exact ⟨answer, cached, resolved⟩


/-- A cached concrete hash query is an exact replay of the same backend state. -/
theorem deferred_hash_cached (q : Query C) (st : DeferredState C) (answer : HashOutput)
    (cached : st.cache q = some answer) :
    (deferredImpl (.hash q)).run st = pure (answer, st) := by
  change (fun r => (r.1, { st with cache := r.2 })) <$>
    (((Query C →ₒ HashOutput).randomOracle q).run st.cache) = _
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ cached, map_pure]

/-- A fresh canonical base appends precisely its own before/after cache entry. -/
theorem traceStepAt_fresh_base (P : PublicParameter) (seeds : C.Term → HashOutput)
    (cache completed : HashCache C) (state : TsigState C)
    (trace : XmssSecurity.SigningCacheTrace × Bool) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds cache e)
    (bound : state.bound e = some message)
    (fresh : cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message))) = none) :
    SigningLaneUnionProof.traceStepAt seeds P cache state
      (.inr (.inr (.inl (.hash (randomizerInput P bottomLayer e
        (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message)))))) completed trace =
      (trace.1 ++ [⟨⟨e, message⟩, signOf (laneKey P) e
        (cachedFound completed P e (SigningGuessProof.cachedRandomizer seeds cache e) message),
        keptView IsMsg cache, keptView IsMsg completed⟩], trace.2) := by
  let call : (WorldSpec C).Domain := .inr (.inr (.inl (.hash (randomizerInput P bottomLayer e
    (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message)))))
  have base : BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e) state call :=
    ⟨_, by rw [baseInput, bound]; rfl, Or.inr rfl⟩
  have trigger : ∃ e, SigningGuessProof.RandomizerCached seeds cache e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e) state call := ⟨e, hprf, base⟩
  have chosen := SigningR1FixedProof.baseCall_key_eq trigger.choose_spec.2 base
  change SigningLaneUnionProof.traceStepAt seeds P cache state call completed trace = _
  rw [SigningLaneUnionProof.traceStepAt, dif_pos trigger, chosen]
  simp only [bound, fresh, if_true]

/-- The two cache operations of a concrete hash step retain their supported intermediate values. -/
theorem compiler_hash_support (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) (st : CompilerBackend C) (r : DeferredSpec C (.hash q) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash q)).run st)) :
    ∃ a ∈ support ((deferredImpl (.hash q)).run st.data),
      ∃ b ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningR1FixedProof.cachedExtra seeds P
          (((st.data.cache, 0), []), compilerSigning st, false)
          (.inr (.inr (.inl q)))
          (((a.2.cache, 0), []), compilerSigning st, false))).run a.2.cache),
        r = (a.1, { st with data := { a.2 with cache := b.2 }, trace := SigningLaneUnionProof.traceStepAt seeds P st.data.cache (compilerSigning st) (.inr (.inr (.inl q))) b.2 st.trace }) := by
  simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at run
  exact run

/-- Reading a compiler state uses just its concrete cache and stored trace. -/
theorem compilerView_update (data : DeferredState C) (bound : KeyIndex → Option Message)
    (trace : XmssSecurity.SigningCacheTrace × Bool) (cache : HashCache C) :
    compilerView { data := { data with cache := cache }, bound := bound, trace := trace } =
      (keptView IsMsg cache, trace.1) := rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Project the supported hash step before inspecting its canonical base behavior. -/
theorem compiler_hash_view_support (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) (st : CompilerBackend C) (r : DeferredSpec C (.hash q) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash q)).run st)) :
    ∃ a ∈ support ((deferredImpl (.hash q)).run st.data),
      ∃ b ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningR1FixedProof.cachedExtra seeds P
          (((st.data.cache, 0), []), compilerSigning st, false)
          (.inr (.inr (.inl q)))
          (((a.2.cache, 0), []), compilerSigning st, false))).run a.2.cache),
        compilerView r.2 = (keptView IsMsg b.2,
          (SigningLaneUnionProof.traceStepAt seeds P st.data.cache (compilerSigning st)
            (.inr (.inr (.inl q))) b.2 st.trace).1) := by
  obtain ⟨a, ha, b, hb, result⟩ := compiler_hash_support P seeds q st r run
  refine ⟨a, ha, b, ?_, ?_⟩
  · with_reducible exact hb
  · exact (congrArg (fun r => compilerView r.2) result).trans (compilerView_update a.2 st.bound _ b.2)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- The message-count ledger freezes a key before its first eager grind, so
that grind creates no extra counted message inputs in the ledger. -/
theorem compiler_fresh_base_count (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (st : CompilerBackend C) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds st.data.cache e)
    (bound : st.bound e = some message)
    (fresh : st.data.cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message))) = none)
    (q : Query C)
    (canonical : q = .hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message)))
    (r : DeferredSpec C (.hash q) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash q)).run st)) :
    XmssSecurity.Ghost.nCount P (compilerView r.2).1 (compilerView r.2).2 =
      XmssSecurity.Ghost.nCount P (compilerView st).1 (compilerView st).2 := by
  obtain ⟨a, ha, b, hb, result⟩ := compiler_hash_view_support P seeds q st r run
  clear run
  rw [result]
  clear result
  have raw := deferred_hash_support q st.data a ha
  rw [canonical] at raw
  have cached := (randomOracle_support _ st.data.cache (a.1, a.2.cache) raw).2.1
  have base : BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.data.cache e)
      (compilerSigning st) (.inr (.inr (.inl q))) := by
    rw [canonical]
    exact ⟨_, by change (st.bound e).map _ = _; rw [bound]; rfl, Or.inr rfl⟩
  have extra := cachedExtra_base seeds P
    (((st.data.cache, 0), []), compilerSigning st, false)
    (((a.2.cache, 0), []), compilerSigning st, false) _ e message hprf base bound a.1 cached
  rw [extra, baseGrind_eq, simulateQ_map, StateT.run_map] at hb
  simp only [support_map, Set.mem_image] at hb
  obtain ⟨completed, hg, hb⟩ := hb
  rw [← hb]
  clear hb
  have sign := SigningLane2TraceLinkProof.raw_fresh_sign_support prims P e
    (SigningGuessProof.cachedRandomizer seeds st.data.cache e) message st.data.cache a.2.cache
    completed.2 a.1 completed.1 fresh raw hg
  have ledger := (XmssSecurity.Ghost.counts_sign (laneKey P) (trace := st.trace.1)
    (request := ⟨e, message⟩) sign).1
  rw [canonical]
  rw [traceStepAt_fresh_base P seeds st.data.cache completed.2 (compilerSigning st) st.trace e message
    hprf bound fresh]
  rw [SigningLane2TraceLinkProof.foundGrind_cachedFound P e
    (SigningGuessProof.cachedRandomizer seeds st.data.cache e) message st.data.cache a.2.cache
    completed.2 a.1 completed.1 raw hg]
  exact ledger

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- A repeated canonical base at a recorded key replays both its raw answer
and its completed grind, preserving the whole message-cache view. -/
theorem compiler_traced_base_view (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : CompilerBackend C)
    (bases : SigningLane2TraceLinkProof.EntryBases seeds P st.data.cache (compilerSigning st) st.trace.1)
    (trials : EntryTrials seeds P st.data.cache st.trace.1)
    (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds st.data.cache e)
    (bound : st.bound e = some message) (recorded : e ∈ st.trace.1.leafIndices)
    (q : Query C)
    (canonical : q = .hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message)))
    (r : DeferredSpec C (.hash q) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash q)).run st)) :
    compilerView r.2 = compilerView st := by
  obtain ⟨answer, cached, resolved⟩ := traced_trials P seeds st bases trials e message bound recorded
  obtain ⟨a, ha, b, hb, result⟩ := compiler_hash_view_support P seeds q st r run
  clear run
  rw [result]
  clear result
  have cachedq : st.data.cache q = some answer := by rw [canonical]; exact cached
  rw [deferred_hash_cached q st.data answer cachedq] at ha
  have ha' : a = (answer, st.data) := (mem_support_pure_iff (m := ProbComp) _ _).mp ha
  subst a
  have base : BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.data.cache e)
      (compilerSigning st) (.inr (.inr (.inl q))) := by
    rw [canonical]
    exact ⟨_, by change (st.bound e).map _ = _; rw [bound]; rfl, Or.inr rfl⟩
  have extra := cachedExtra_base seeds P
    (((st.data.cache, 0), []), compilerSigning st, false)
    (((st.data.cache, 0), []), compilerSigning st, false) _ e message hprf base bound answer cached
  rw [extra, resolved.run_eq_pure, mem_support_pure_iff] at hb
  subst b
  rw [canonical]
  rw [traceStepAt_traced_base P seeds st.data.cache st.data.cache (compilerSigning st) st.trace e message
    hprf bound answer cached recorded]
  rfl

/-- A base call carries a bound message and the exact canonical query address. -/
theorem base_call_query (P : PublicParameter) (rho : Digest) (state : TsigState C)
    (q : Query C) (e : KeyIndex)
    (base : BaseCall P e rho state (.inr (.inr (.inl q)))) :
    ∃ message, state.bound e = some message ∧
      q = .hash (randomizerInput P bottomLayer e rho (bytesLE 32 message)) := by
  cases bound : state.bound e with
  | none =>
      obtain ⟨input, hinput, _⟩ := base
      simp [baseInput, bound] at hinput
  | some message =>
      refine ⟨message, rfl, ?_⟩
      rcases hashCallAt_of_baseCall base bound with bad | eq
      · cases bad
      · exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj eq))

/-- A cached canonical base without a recorded key stops the compiler trace. -/
theorem traceStepAt_stale_base (P : PublicParameter) (seeds : C.Term → HashOutput)
    (cache completed : HashCache C) (state : TsigState C)
    (trace : XmssSecurity.SigningCacheTrace × Bool) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds cache e)
    (bound : state.bound e = some message) (answer : HashOutput)
    (cached : cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message))) = some answer)
    (unrecorded : e ∉ trace.1.leafIndices) :
    (SigningLaneUnionProof.traceStepAt seeds P cache state
      (.inr (.inr (.inl (.hash (randomizerInput P bottomLayer e
        (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message)))))) completed trace).2 = true := by
  let call : (WorldSpec C).Domain := .inr (.inr (.inl (.hash (randomizerInput P bottomLayer e
    (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message)))))
  have base : BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e) state call :=
    ⟨_, by rw [baseInput, bound]; rfl, Or.inr rfl⟩
  have trigger : ∃ e, SigningGuessProof.RandomizerCached seeds cache e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e) state call := ⟨e, hprf, base⟩
  have chosen := SigningR1FixedProof.baseCall_key_eq trigger.choose_spec.2 base
  change (SigningLaneUnionProof.traceStepAt seeds P cache state call completed trace).2 = true
  rw [SigningLaneUnionProof.traceStepAt, dif_pos trigger, chosen]
  simp [bound, cached, unrecorded]

/-- The actual compiler marks a cached, unrecorded canonical base as stale. -/
theorem compiler_stale_base (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : CompilerBackend C) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds st.data.cache e)
    (bound : st.bound e = some message) (answer : HashOutput)
    (cached : st.data.cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message))) = some answer)
    (unrecorded : e ∉ st.trace.1.leafIndices) (q : Query C)
    (canonical : q = .hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message)))
    (r : DeferredSpec C (.hash q) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash q)).run st)) : r.2.trace.2 = true := by
  obtain ⟨a, _, b, _, result⟩ := compiler_hash_support P seeds q st r run
  have htrace := congrArg (fun r => r.2.trace.2) result
  refine htrace.trans ?_
  rw [canonical]
  exact traceStepAt_stale_base P seeds st.data.cache b.2 (compilerSigning st) st.trace e message
    hprf bound answer cached unrecorded

/-- At a non-stale hash successor, the frozen ledger grows by at most one. -/
theorem compiler_hash_count_le (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (st : CompilerBackend C)
    (bases : SigningLane2TraceLinkProof.EntryBases seeds P st.data.cache (compilerSigning st) st.trace.1)
    (trials : EntryTrials seeds P st.data.cache st.trace.1) (input : HashInput)
    (r : DeferredSpec C (.hash (.hash input)) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash (.hash input))).run st))
    (live : r.2.trace.2 = false) :
    XmssSecurity.Ghost.nCount P (compilerView r.2).1 (compilerView r.2).2 ≤
      XmssSecurity.Ghost.nCount P (compilerView st).1 (compilerView st).2 + 1 := by
  by_cases trigger : ∃ e, SigningGuessProof.RandomizerCached seeds st.data.cache e ∧
    BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.data.cache e)
      (compilerSigning st) (.inr (.inr (.inl (.hash input))))
  · obtain ⟨e, hprf, hcall⟩ := trigger
    obtain ⟨message, bound, canonical⟩ := base_call_query P
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (compilerSigning st) (.hash input) e hcall
    cases cached : st.data.cache (.hash (randomizerInput P bottomLayer e
        (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message))) with
    | none =>
      rw [compiler_fresh_base_count prims P seeds st e message hprf bound cached _ canonical r run]
      exact Nat.le_succ _
    | some answer =>
      by_cases recorded : e ∈ st.trace.1.leafIndices
      · rw [compiler_traced_base_view P seeds st bases trials e message hprf bound recorded _ canonical r run]
        exact Nat.le_succ _
      · have stop := compiler_stale_base P seeds st e message hprf bound answer cached recorded
          _ canonical r run
        simp [live] at stop
  · rw [compiler_hash_no_trigger P seeds (.hash input) st trigger] at run
    erw [support_map (m := ProbComp)] at run
    obtain ⟨raw, hraw, result⟩ := run
    rw [← result]
    exact raw_hash_count_le P input st.data.cache st.trace.1 raw hraw

/-- Each counted backend call pays for every increase of the non-stale frozen ledger. -/
theorem compiler_count_le (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (st : CompilerBackend C)
    (bases : SigningLane2TraceLinkProof.EntryBases seeds P st.data.cache (compilerSigning st) st.trace.1)
    (trials : EntryTrials seeds P st.data.cache st.trace.1) (t : DeferredQuery C)
    (r : DeferredSpec C t × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds t).run st)) (live : r.2.trace.2 = false) :
    XmssSecurity.Ghost.nCount P (compilerView r.2).1 (compilerView r.2).2 ≤
      XmssSecurity.Ghost.nCount P (compilerView st).1 (compilerView st).2 +
        if deferredCounted t then 1 else 0 := by
  by_cases counted : deferredCounted t
  swap
  · rw [(compilerImpl_view_uncounted P seeds t counted st r run).1, if_neg counted, Nat.add_zero]
  rw [if_pos counted]
  have same : compilerView r.2 = compilerView st →
      XmssSecurity.Ghost.nCount P (compilerView r.2).1 (compilerView r.2).2 ≤
        XmssSecurity.Ghost.nCount P (compilerView st).1 (compilerView st).2 + 1 := by
    intro eq
    rw [eq]
    exact Nat.le_succ _
  cases t with
  | hash q =>
    by_cases hhash : ∃ input, q = .hash input
    · obtain ⟨input, rfl⟩ := hhash
      exact compiler_hash_count_le prims P seeds st bases trials input r run live
    · exact same (compilerImpl_view_not_hash P seeds (.hash q)
        ⟨q, rfl, fun input eq => hhash ⟨input, eq⟩⟩ st r run).1
  | pending p => exact same (compilerImpl_view_pending P seeds p st r run).1
  | virtual T p => exact same (compilerImpl_view_virtual P seeds T p st r run).1
  | _ => simp [deferredCounted] at counted

/-- Every reachable compiler state that has not stopped satisfies leanVM's count invariant. -/
theorem reachable_ghostInv (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (st : CompilerBackend C × ℕ)
    (reachable : CompilerReachable P seeds st) (live : st.1.trace.2 = false) :
    XmssSecurity.Ghost.Inv (laneKey P) (compilerView st.1, st.2) := by
  induction reachable with
  | initial =>
    exact XmssSecurity.Ghost.inv_initial (laneKey P)
      (cache0 := keptView IsMsg (∅ : HashCache C)) (by intro e y; unfold keptView; split <;> rfl)
  | step t st r reachable run ih =>
    simp only [countImpl, StateT.run_mk, support_map, Set.mem_image] at run
    obtain ⟨a, ha, eq⟩ := run
    have liveA : a.2.trace.2 = false := by simpa only [← eq] using live
    have liveSt : st.1.trace.2 = false := by
      cases h : st.1.trace.2 with
      | false => rfl
      | true => simpa [liveA] using compilerImpl_stale P seeds t st.1 h a ha
    have old := ih liveSt
    have bound := compiler_count_le prims P seeds st.1
      (CompilerReachable.entryBases P seeds st reachable).1
      (reachable_entryTrials P seeds st reachable) t a ha liveA
    rw [← eq]
    change XmssSecurity.Ghost.nCount P (compilerView a.2).1 (compilerView a.2).2 ≤
      st.2 + if deferredCounted t then 1 else 0
    exact bound.trans (Nat.add_le_add_right old _)

/-- The projected compiler hash run keeps exactly the raw cache and the silent grind. -/
theorem compiler_hash_view_run (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) (st : CompilerBackend C) :
    (fun r => compilerView r.2) <$> ((compilerImpl P seeds (.hash q)).run st) =
      (((Query C →ₒ HashOutput).randomOracle q).run st.data.cache >>= fun a =>
        (simulateQ (Query C →ₒ HashOutput).randomOracle
          (SigningR1FixedProof.cachedExtra seeds P
            (((st.data.cache, 0), []), compilerSigning st, false) (.inr (.inr (.inl q)))
            (((a.2, 0), []), compilerSigning st, false))).run a.2 >>= fun b =>
        pure (keptView IsMsg b.2,
          (SigningLaneUnionProof.traceStepAt seeds P st.data.cache (compilerSigning st)
            (.inr (.inr (.inl q))) b.2 st.trace).1)) := by
  simp only [compilerImpl, deferredImpl, StateT.run, map_bind, bind_map_left, map_pure]
  rfl

/-- A fresh canonical base has exactly leanVM's signing law on the compiler view. -/
theorem compiler_fresh_base_viewLaw (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (st : CompilerBackend C) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds st.data.cache e)
    (bound : st.bound e = some message)
    (fresh : st.data.cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message))) = none)
    (q : Query C) (k : ℕ)
    (canonical : q = .hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message))) :
    𝒟[(fun r => compilerView r.2) <$> ((compilerImpl P seeds (.hash q)).run st)] =
      𝒟[(fun r => r.2.1) <$>
        (SigningLane2Proof.signWithBaseStep (laneKey P) ⟨e, message⟩).run (compilerView st, k)] := by
  rw [compiler_hash_view_run, canonical]
  have eager := eagerBase_signWithBaseStep prims P
    (SigningGuessProof.cachedRandomizer seeds st.data.cache e) ⟨e, message⟩ st.data.cache fresh st.trace.1 k
  have mapped := evalDist_map_eq_of_evalDist_eq eager (fun r => r.2.1)
  simp only [map_bind, map_pure] at mapped
  refine Eq.trans ?_ mapped
  apply congrArg (fun p : ProbComp (XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace) => 𝒟[p])
  apply OracleComp.bind_congr_of_forall_mem_support
  intro a ha
  have cached := (randomOracle_support _ st.data.cache a ha).2.1
  have base : BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.data.cache e)
      (compilerSigning st) (.inr (.inr (.inl (.hash (randomizerInput P bottomLayer e
        (SigningGuessProof.cachedRandomizer seeds st.data.cache e) (bytesLE 32 message)))))) :=
    ⟨_, by change (st.bound e).map _ = _; rw [bound]; rfl, Or.inr rfl⟩
  have extra := cachedExtra_base seeds P
    (((st.data.cache, 0), []), compilerSigning st, false)
    (((a.2, 0), []), compilerSigning st, false) _ e message hprf base bound a.1 cached
  rw [extra, baseGrind_eq, simulateQ_map, StateT.run_map, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro completed hg
  rw [traceStepAt_fresh_base P seeds st.data.cache completed.2 (compilerSigning st) st.trace e message
    hprf bound fresh]
  rw [SigningLane2TraceLinkProof.foundGrind_cachedFound P e
    (SigningGuessProof.cachedRandomizer seeds st.data.cache e) message st.data.cache a.2
    completed.2 a.1 completed.1 ha hg]

/-- The compensated leanVM sum, evaluated on one cache, trace and count. -/
def viewSum (P : PublicParameter) (q : ℕ) : XmssSecurity.Ghost.State → ℝ≥0∞ :=
  SigningLane2Proof.lane2Sum XmssSecurity.Partner.landing
    (XmssSecurity.Ghost.f1 (laneKey P)) (XmssSecurity.Ghost.f2 (laneKey P))
    (XmssSecurity.Ghost.f3 (laneKey P) q) (XmssSecurity.Ghost.f4 (laneKey P))

/-- The compensated sum at one leanVM step, before its count cap is applied. -/
theorem viewSum_step (publicKey : XmssSecurity.PublicKey) (P : PublicParameter) (q : ℕ)
    (hq : q < 2 ^ 127) (input : (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec).Domain)
    (s : XmssSecurity.Ghost.State) (inv : XmssSecurity.Ghost.Inv (laneKey P) s)
    (room : XmssSecurity.Ghost.IsAdvHash input → s.2 < q) :
    ∑' r, Pr[= r | (XmssSecurity.Ghost.impl publicKey (laneKey P) input).run s] * viewSum P q r.2 ≤
      viewSum P q s + (2 ^ 128 : ℝ≥0∞) *
        (XmssSecurity.Ghost.openCost (laneKey P) input s +
          XmssSecurity.Ghost.signedCost (laneKey P) input s) := by
  have cost3 : XmssSecurity.Ghost.cost3 (laneKey P) q input s =
      ENNReal.ofReal (XmssSecurity.Partner.momentA XmssSecurity.Ghost.pReal q) *
        XmssSecurity.Ghost.openCost (laneKey P) input s := by
    rw [XmssSecurity.Ghost.cost3, XmssSecurity.Ghost.overBudget,
      if_neg (fun h => Nat.not_le_of_gt (room h.1) h.2), zero_add]
    rfl
  exact SigningLane2Proof.lane2Sum_step (2 ^ 128) XmssSecurity.Partner.landing
    (ENNReal.ofReal (XmssSecurity.Partner.momentA XmssSecurity.Ghost.pReal q))
    (XmssSecurity.Ghost.f1 (laneKey P)) (XmssSecurity.Ghost.f2 (laneKey P))
    (XmssSecurity.Ghost.f3 (laneKey P) q) (XmssSecurity.Ghost.f4 (laneKey P))
    (XmssSecurity.Ghost.cost1 (laneKey P)) (XmssSecurity.Ghost.openCost (laneKey P))
    (XmssSecurity.Ghost.signedCost (laneKey P)) _ s input
    (XmssSecurity.Ghost.f1_step publicKey (laneKey P) input s)
    (XmssSecurity.Ghost.f2_step publicKey (laneKey P) input s)
    (by rw [← cost3]; exact XmssSecurity.Ghost.f3_step publicKey (laneKey P) q hq.le input s inv)
    (by simpa only [XmssSecurity.Ghost.cost4, XmssSecurity.Ghost.signedCost,
      Nat.cast_pow, Nat.cast_ofNat, XmssSecurity.digestBits] using
        XmssSecurity.Ghost.f4_step publicKey (laneKey P) input s)
    (SigningLane2Proof.f2_le_landing_mul_f3 (laneKey P) q)
    (SigningLane2Proof.f2_ne_top (laneKey P))
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat, XmssSecurity.digestBits] using
      XmssSecurity.Ghost.momentA_le_N hq) XmssSecurity.Ghost.landing_ne_zero
    XmssSecurity.Partner.landing_ne_top

/-- The signing step cannot increase the compensated sum. -/
theorem viewSum_sign (publicKey : XmssSecurity.PublicKey) (P : PublicParameter) (q : ℕ)
    (hq : q < 2 ^ 127) (request : XmssSecurity.SignRequest) (s : XmssSecurity.Ghost.State)
    (inv : XmssSecurity.Ghost.Inv (laneKey P) s) :
    ∑' r, Pr[= r | (SigningLane2Proof.signWithBaseStep (laneKey P) request).run s] *
      viewSum P q r.2 ≤ viewSum P q s := by
  have law := SigningLane2Proof.evalDist_signWithBaseStep publicKey (laneKey P) request s
  have transfer := SigningLane2Proof.tsum_view_eq _ _ id law (viewSum P q)
  rw [show (∑' r, Pr[= r | (SigningLane2Proof.signWithBaseStep (laneKey P) request).run s] *
      viewSum P q r.2) = _ from transfer]
  have h := viewSum_step publicKey P q hq (.inr request) s inv (by simp [XmssSecurity.Ghost.IsAdvHash])
  simpa only [XmssSecurity.Ghost.openCost, XmssSecurity.Ghost.signedCost,
    XmssSecurity.Ghost.onHash_sign, add_zero, mul_zero] using h

/-- On a live state within the cap, the compiler potential is the scaled compensated sum. -/
theorem compilerPotential_eq_sum (P : PublicParameter) (q : ℕ) (st : CompilerBackend C × ℕ)
    (live : st.1.trace.2 = false) (hk : st.2 ≤ q) :
    compilerPotential P q st = viewSum P q (compilerView st.1, st.2) *
      ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
  simp only [compilerPotential, live, Bool.false_eq_true, if_false,
    SigningLane2Proof.lane2Potential, if_pos hk, viewSum, SigningLane2Proof.lane2Sum]

/-- Stopping can only decrease the scaled compensated sum. -/
theorem compilerPotential_le_sum (P : PublicParameter) (q : ℕ) (st : CompilerBackend C × ℕ)
    (hk : st.2 ≤ q) :
    compilerPotential P q st ≤ viewSum P q (compilerView st.1, st.2) *
      ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
  cases live : st.1.trace.2 with
  | false => exact (compilerPotential_eq_sum P q st live hk).le
  | true => simp only [compilerPotential, live, if_true]; exact zero_le

/-- Once the next count exceeds the cap, every counted successor has zero potential. -/
theorem compilerPotential_over_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (t : DeferredQuery C) (counted : deferredCounted t)
    (st : CompilerBackend C × ℕ) (over : q ≤ st.2) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
      compilerPotential P q r.2 = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  by_cases hr : r ∈ support ((countImpl (compilerImpl P seeds) deferredCounted t).run st)
  · have count := SigningLane2Proof.countImpl_support_count (compilerImpl P seeds) deferredCounted t st r hr
    have past : ¬ r.2.2 ≤ q := by rw [count, if_pos counted]; omega
    simp only [compilerPotential, SigningLane2Proof.lane2Potential, if_neg past, ite_self, mul_zero]
  · simp [probOutput_eq_zero_of_not_mem_support hr]

/-- The count tick and stopping are harmless when bounding by the previous-count sum. -/
theorem counted_potential_le_previousSum (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (t : DeferredQuery C) (counted : deferredCounted t)
    (st : CompilerBackend C × ℕ) (within : st.2 ≤ q) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
      compilerPotential P q r.2 ≤
      (∑' r, Pr[= r | (compilerImpl P seeds t).run st.1] *
        viewSum P q (compilerView r.2, st.2)) * ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
  simp only [countImpl, StateT.run_mk]
  rw [tsum_probOutput_map_mul]
  simp only [if_pos counted]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro r
  rw [mul_assoc]
  exact mul_le_mul_right ((compilerPotential_tick P q r.2 st.2).trans
    (compilerPotential_le_sum P q (r.2, st.2) within)) _

/-- At a fresh canonical base, the expectation of the previous-count sum does not increase. -/
theorem fresh_base_sum_le (prims : Primitives) (publicKey : XmssSecurity.PublicKey)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (hq : q < 2 ^ 127)
    (st : CompilerBackend C × ℕ) (inv : XmssSecurity.Ghost.Inv (laneKey P) (compilerView st.1, st.2))
    (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds st.1.data.cache e)
    (bound : st.1.bound e = some message)
    (fresh : st.1.data.cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e) (bytesLE 32 message))) = none)
    (t : Query C)
    (canonical : t = .hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e) (bytesLE 32 message))) :
    ∑' r, Pr[= r | (compilerImpl P seeds (.hash t)).run st.1] *
      viewSum P q (compilerView r.2, st.2) ≤ viewSum P q (compilerView st.1, st.2) := by
  have law := compiler_fresh_base_viewLaw prims P seeds st.1 e message hprf bound fresh t st.2 canonical
  have transfer := SigningLane2Proof.tsum_map_eq
    ((compilerImpl P seeds (.hash t)).run st.1)
    ((SigningLane2Proof.signWithBaseStep (laneKey P) ⟨e, message⟩).run (compilerView st.1, st.2))
    (fun r => compilerView r.2) (fun r => r.2.1)
    law (fun v => viewSum P q (v, st.2))
  refine transfer.le.trans ?_
  have eq : (∑' r, Pr[= r | (SigningLane2Proof.signWithBaseStep (laneKey P) ⟨e, message⟩).run
      (compilerView st.1, st.2)] * viewSum P q (r.2.1, st.2)) =
      ∑' r, Pr[= r | (SigningLane2Proof.signWithBaseStep (laneKey P) ⟨e, message⟩).run
        (compilerView st.1, st.2)] * viewSum P q r.2 := by
    apply SigningLane2Proof.tsum_congr_support
    intro r hr
    have count := (SigningLane2Proof.counts_signWithBaseStep (laneKey P) ⟨e, message⟩
      (compilerView st.1, st.2) r hr).2.2
    rw [← count]
  rw [eq]
  exact viewSum_sign publicKey P q hq ⟨e, message⟩ (compilerView st.1, st.2) inv

/-- A counted step with unchanged live views cannot increase the stopped potential. -/
theorem compilerPotential_same_live_view (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (t : DeferredQuery C) (counted : deferredCounted t)
    (st : CompilerBackend C × ℕ) (live : st.1.trace.2 = false)
    (same : ∀ r ∈ support ((compilerImpl P seeds t).run st.1),
      r.2.trace.2 = false → compilerView r.2 = compilerView st.1) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st := by
  apply XmssSecurity.Ghost.tsum_le_of_support
  intro r hr
  simp only [countImpl, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨a, ha, eq⟩ := hr
  rw [← eq]
  cases after : a.2.trace.2 with
  | true => simp only [compilerPotential, after, if_true]; exact zero_le
  | false =>
    have view := same a ha after
    rw [compilerPotential_congr P q _ (st.1, st.2 + 1) view
      (after.trans live.symm) (by simp [counted])]
    exact compilerPotential_tick P q st.1 st.2

/-- A non-message query without a base trigger preserves the whole compiler view. -/
theorem compiler_hash_other_view (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : HashInput) (other : ¬ IsMsg input) (st : CompilerBackend C)
    (noBase : ¬ ∃ e, SigningGuessProof.RandomizerCached seeds st.data.cache e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.data.cache e)
        (compilerSigning st) (.inr (.inr (.inl (.hash input)))))
    (r : DeferredSpec C (.hash (.hash input)) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash (.hash input))).run st)) :
    compilerView r.2 = compilerView st := by
  rw [compiler_hash_no_trigger P seeds (.hash input) st noBase] at run
  erw [support_map (m := ProbComp)] at run
  obtain ⟨a, ha, result⟩ := run
  rw [← result]
  change (keptView IsMsg a.2, st.trace.1) = (keptView IsMsg st.data.cache, st.trace.1)
  cases cached : st.data.cache (.hash input) with
  | some value =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ cached,
      mem_support_pure_iff] at ha
    subst a
    rfl
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ cached] at ha
    simp only [support_map, Set.mem_image] at ha
    obtain ⟨value, _, rfl⟩ := ha
    rw [keptView_cacheQuery_of_not (K := IsMsg) (fun x he => by cases he; exact other)]

/-- A counted message step has exactly the state law of the ghost hash step. -/
theorem compiler_message_stateLaw (prims : Primitives) (publicKey : XmssSecurity.PublicKey)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (input : HashInput)
    (message : IsMsg input) (st : CompilerBackend C × ℕ) :
    𝒟[(fun r => (compilerView r.2.1, r.2.2)) <$>
      (countImpl (compilerImpl P seeds) deferredCounted (.hash (.hash input))).run st] =
      𝒟[(fun r => r.2) <$> (XmssSecurity.Ghost.impl publicKey (laneKey P)
        (.inl (.inr input))).run (compilerView st.1, st.2)] := by
  simp only [countImpl, StateT.run_mk, compiler_hash_message P seeds input message,
    Functor.map_map, deferredCounted, if_true]
  erw [Functor.map_map]
  have law := worldCall_stateLaw_isMsg prims publicKey (laneKey P) message
    st.1.data.cache st.1.trace.1 st.2
  simpa only [compilerView, hashAnswer, if_neg (fun h => not_isMsg_of_mpc h message)] using law

/-- The expected compensated sum of a message step increases by at most one digest space. -/
theorem compiler_message_sum_le (prims : Primitives) (publicKey : XmssSecurity.PublicKey)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (hq : q < 2 ^ 127)
    (input : HashInput) (message : IsMsg input) (st : CompilerBackend C × ℕ)
    (inv : XmssSecurity.Ghost.Inv (laneKey P) (compilerView st.1, st.2)) (room : st.2 < q) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted (.hash (.hash input))).run st] *
      viewSum P q (compilerView r.2.1, r.2.2) ≤ viewSum P q (compilerView st.1, st.2) + 2 ^ 128 := by
  have law := compiler_message_stateLaw prims publicKey P seeds input message st
  have transfer := SigningLane2Proof.tsum_view_eq
    ((countImpl (compilerImpl P seeds) deferredCounted (.hash (.hash input))).run st)
    ((XmssSecurity.Ghost.impl publicKey (laneKey P) (.inl (.inr input))).run (compilerView st.1, st.2))
    (fun s => (compilerView s.1, s.2)) law (viewSum P q)
  refine transfer.le.trans ((viewSum_step publicKey P q hq (.inl (.inr input))
    (compilerView st.1, st.2) inv (fun _ => room)).trans ?_)
  refine add_le_add le_rfl ?_
  have cost := XmssSecurity.Ghost.openCost_add_signedCost_le (laneKey P)
    (.inl (.inr input)) (compilerView st.1, st.2)
  have bounded : XmssSecurity.Ghost.openCost (laneKey P) (.inl (.inr input))
      (compilerView st.1, st.2) + XmssSecurity.Ghost.signedCost (laneKey P)
      (.inl (.inr input)) (compilerView st.1, st.2) ≤ 1 :=
    cost.trans (by split_ifs <;> simp)
  simpa only [mul_one] using mul_le_mul_right bounded (2 ^ 128 : ℝ≥0∞)

/-- Within the cap, stopping only decreases the next-state scaled sum. -/
theorem counted_potential_le_nextSum (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (t : DeferredQuery C) (counted : deferredCounted t)
    (st : CompilerBackend C × ℕ) (room : st.2 < q) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
      compilerPotential P q r.2 ≤
      (∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
        viewSum P q (compilerView r.2.1, r.2.2)) * ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro r
  rw [mul_assoc]
  by_cases run : r ∈ support ((countImpl (compilerImpl P seeds) deferredCounted t).run st)
  · have count := SigningLane2Proof.countImpl_support_count (compilerImpl P seeds) deferredCounted t st r run
    exact mul_le_mul_right (compilerPotential_le_sum P q r.2 (by rw [count, if_pos counted]; omega)) _
  · simp only [probOutput_eq_zero_of_not_mem_support run, zero_mul, le_refl]

/-- A message query pays at most one inverse digest space in stopped potential. -/
theorem compilerPotential_message (prims : Primitives) (publicKey : XmssSecurity.PublicKey)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (hq : q < 2 ^ 127)
    (input : HashInput) (message : IsMsg input) (st : CompilerBackend C × ℕ)
    (inv : XmssSecurity.Ghost.Inv (laneKey P) (compilerView st.1, st.2))
    (live : st.1.trace.2 = false) (room : st.2 < q) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted (.hash (.hash input))).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st + (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (counted_potential_le_nextSum P seeds q (.hash (.hash input)) trivial st room).trans ?_
  refine (mul_le_mul_left (compiler_message_sum_le prims publicKey P seeds q hq input message st inv room) _).trans ?_
  rw [compilerPotential_eq_sum P q st live room.le, add_mul]
  refine add_le_add le_rfl ?_
  have hzero : (2 ^ 128 : ℝ≥0∞) ≠ 0 := by norm_num
  have htop : (2 ^ 128 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [ENNReal.mul_inv (Or.inl hzero) (Or.inl htop), ← mul_assoc,
    ENNReal.mul_inv_cancel hzero htop, one_mul]

/-- The fixed compiler satisfies the complete stopped-potential step contract. -/
theorem compilerPotentialStep (prims : Primitives) : CompilerPotentialStep (C := C) := by
  apply compilerPotentialStep_iff_hashInput.mpr
  intro x q hq input st reachable live
  by_cases room : st.2 < q
  · have inv := reachable_ghostInv prims x.1 x.2.1 st reachable live
    by_cases message : IsMsg input
    · have side : ¬ deferredInputSide (C := C) x.1 (.hash (.hash input)) := by
        simp only [deferredInputSide, deferredCandidate,
          hiddenCandidate_none_of_isMsg x.1 input message, Option.isSome_none,
          Bool.false_eq_true, not_false_eq_true]
      rw [if_pos ⟨⟨trivial, room⟩, side⟩]
      exact compilerPotential_message prims ⟨0, x.1⟩ x.1 x.2.1 q hq input message st inv live room
    · suffices step : ∑' r, Pr[= r | (countImpl (compilerImpl x.1 x.2.1) deferredCounted
          (.hash (.hash input))).run st] * compilerPotential x.1 q r.2 ≤
          compilerPotential x.1 q st from step.trans le_self_add
      by_cases trigger : ∃ e, SigningGuessProof.RandomizerCached x.2.1 st.1.data.cache e ∧
          BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 st.1.data.cache e)
            (compilerSigning st.1) (.inr (.inr (.inl (.hash input))))
      · obtain ⟨e, hprf, base⟩ := trigger
        obtain ⟨m, bound, canonical⟩ := base_call_query x.1
          (SigningGuessProof.cachedRandomizer x.2.1 st.1.data.cache e)
          (compilerSigning st.1) (.hash input) e base
        cases cached : st.1.data.cache (.hash (randomizerInput x.1 bottomLayer e
            (SigningGuessProof.cachedRandomizer x.2.1 st.1.data.cache e) (bytesLE 32 m))) with
        | none =>
          refine (counted_potential_le_previousSum x.1 x.2.1 q (.hash (.hash input))
            trivial st room.le).trans ?_
          rw [compilerPotential_eq_sum x.1 q st live room.le]
          exact mul_le_mul_left (fresh_base_sum_le prims ⟨0, x.1⟩ x.1 x.2.1 q hq st inv
            e m hprf bound cached (.hash input) canonical) _
        | some answer =>
          apply compilerPotential_same_live_view x.1 x.2.1 q (.hash (.hash input)) trivial st live
          intro r run nextLive
          by_cases recorded : e ∈ st.1.trace.1.leafIndices
          · exact compiler_traced_base_view x.1 x.2.1 st.1
              (CompilerReachable.entryBases x.1 x.2.1 st reachable).1
              (reachable_entryTrials x.1 x.2.1 st reachable) e m hprf bound recorded
              (.hash input) canonical r run
          · have stale := compiler_stale_base x.1 x.2.1 st.1 e m hprf bound answer cached
              recorded (.hash input) canonical r run
            exact False.elim (Bool.false_ne_true (nextLive.symm.trans stale))
      · apply compilerPotential_same_live_view x.1 x.2.1 q (.hash (.hash input)) trivial st live
        intro r run _
        exact compiler_hash_other_view x.1 x.2.1 input message st.1 trigger r run
  · rw [compilerPotential_over_cap x.1 x.2.1 q (.hash (.hash input)) trivial st (by omega)]
    exact zero_le

end ThresholdLeanXmssSecurity.SigningCompilerPotential

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.EntryTrials.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.EntryTrials.mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.cachedExtra_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.cachedExtra_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.reachable_entryTrials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.reachable_entryTrials

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_hash_no_trigger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_hash_no_trigger

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_hash_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_hash_message

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.raw_hash_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.raw_hash_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.traceStepAt_traced_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.traceStepAt_traced_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.traced_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.traced_trials

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_fresh_base_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_fresh_base_count

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_traced_base_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_traced_base_view

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.reachable_ghostInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.reachable_ghostInv

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_fresh_base_viewLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compiler_fresh_base_viewLaw

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.viewSum_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.viewSum_sign

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compilerPotential_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compilerPotential_message

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerPotential.compilerPotentialStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerPotential.compilerPotentialStep
