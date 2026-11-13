import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncBackend
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRealRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTrigger

/-! # Synchronization of one local slot read

A term or mask slot observes the fixed table, then performs the compiler's
optional opening release and counted read. The relation retains the source,
private cache, share table and both stopping events.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot
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

theorem slot_not_hash (x : Keys3 C) (input : Query C) (h : IsSlot x input) :
    ∀ i, input ≠ .hash i := by
  obtain ⟨z, rfl⟩ := h
  cases z <;> simp [TprfSecurityProof.slotInput]

theorem slot_no_hashCall (x : Keys3 C) (input : Query C) (h : IsSlot x input) :
    (∀ i, ¬SigningFlatProof.HashCallAt i (.inl (.inl (.inr (.inl input))) :
      (WorldSpec C).Domain)) ∧
    (∀ i, ¬SigningFlatProof.HashCallAt i (.inr (.inr (.inl input)) :
      (WorldSpec C).Domain)) := by
  constructor <;> intro i hi <;>
    simp only [SigningFlatProof.HashCallAt, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, or_false, false_or] at hi <;>
    exact slot_not_hash x input h i hi

/-- The visible observation, counted log entry and unchanged nonhash trace. -/
def observed (input : Query C) (value : HashOutput) (a : RealState C) : RealState C :=
  let t : (WorldSpec C).Domain := .inl (.inl (.inr (.inl input)))
  let logged : SigningHitLaneProof.LoggedState C :=
    (( (visibleOf a).cacheQuery input value, a.1.1.1.1.1.1.2 + 1),
      a.1.1.1.1.1.2.logQuery t value)
  (((((logged, a.1.1.1.1.2), a.1.1.1.2), a.1.1.2), a.1.2), a.2)

theorem realWorld_slot (prims : Primitives) (x : Keys3 C)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (input : Query C) (hs : IsSlot x input) (a : RealState C) :
    ((SigningCompilerUntil.fuse (rawTraceWorld prims x) (realImpl x g rest)
      (.inl (.inl (.inr (.inl input))))).run a) =
        pure (realTable g rest hs.choose, observed input (realTable g rest hs.choose) a) := by
  change (ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x) (realImpl x g rest)
    (.inl (.inl (.inr (.inl input))))).run a = _
  rw [rawTraceWorld_read prims x g rest (.inl input) a.1 a.2]
  simp only [readInput]
  rw [realImpl_slot x g rest input hs]
  simp only [pure_bind, readAnswer]
  rw [nonhash_cachedExtra x.2.1 x.1 _ _ _ (slot_no_hashCall x input hs).1]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  rw [nonhash_traceStepAt x.2.1 x.1 _ _ _ _ _ (slot_no_hashCall x input hs).1]
  obtain ⟨z, hz⟩ := hs
  rcases z with ⟨T, p⟩ | m <;> subst input <;>
    simp [TprfSecurityProof.slotInput, SigningPartnerBoundProof.hashEntry,
      SigningFlatEagerProof.queryEntryStep, SeedHitProof.signCost, observed]

theorem hashTail_slot (x : Keys3 C) (input : Query C) (hs : IsSlot x input)
    (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C) :
    hashTail x.1 x.2.1 input st value cache =
      pure (value, (({ st.1.1 with data := { st.1.1.data with cache := cache } },
        st.1.2 + 1), st.2)) := by
  unfold hashTail
  dsimp only
  rw [nonhash_cachedExtra x.2.1 x.1 _ _ _ (slot_no_hashCall x input hs).2]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  rw [nonhash_traceStepAt x.2.1 x.1 _ _ _ _ _ (slot_no_hashCall x input hs).2]

theorem observe_slot_value (x : Keys3 C)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (priv vis : HashCache C) (hr : RealPrivate x s pads noise g rest priv vis)
    (input : Query C) (hs : IsSlot x input) :
    vis ≤ vis.cacheQuery input (realTable g rest hs.choose) := by
  cases hv : vis input with
  | none => exact QueryCache.le_cacheQuery vis hv
  | some v =>
    have he := hr.visible input v hv
    rw [dif_pos hs] at he
    rw [Option.some.inj he, observe_same vis input v hv]


/-- A concrete read materializes one nonhash cell in both cache views. -/
theorem cacheRelation_slot (x : Keys3 C) (s : HiddenKey → Digest)
    (data : DeferredState C) (vis : HashCache C) (input : Query C)
    (hs : IsSlot x input) (value : HashOutput)
    (hc : CacheRelation x.1 x.2.1 s data vis) :
    CacheRelation x.1 x.2.1 s { data with cache := data.cache.cacheQuery input value }
      (vis.cacheQuery input value) := by
  refine ⟨?_, ?_⟩
  · intro other hn
    by_cases he : other = input
    · subst other; simp only [QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ he]
      show vis other = data.cache.cacheQuery input value other
      rw [QueryCache.cacheQuery_of_ne _ _ he]
      apply hc.agree other
      simpa only [SuspendedQuery, QueryCache.cacheQuery_of_ne _ _ he] using hn
  · intro p v hp
    rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm (slot_not_hash x input hs _))]
    exact hc.pending p v hp

theorem merge_cacheQuery_other (seeds : C.Term → HashOutput)
    (cache : HashCache C) (share : ShareCache C) (input : Query C)
    (hr : route seeds input = none) (v : HashOutput) :
    merge seeds (cache.cacheQuery input v) share =
      (merge seeds cache share).cacheQuery input v := by
  funext other
  by_cases he : other = input
  · subst other; simp [merge, hr]
  · rw [QueryCache.cacheQuery_of_ne _ _ he]
    cases ho : route seeds other <;> simp [merge, ho, QueryCache.cacheQuery_of_ne _ _ he]

theorem merge_merge (seeds : C.Term → HashOutput) (rest : HashCache C)
    (share : ShareCache C) : merge seeds (merge seeds rest share) share = merge seeds rest share := by
  funext query
  cases h : route seeds query <;> simp [merge, h]

/-- State facts of the counted backend read, before its caller's control update. -/
structure ReadPost (x : Keys3 C) (input : Query C) (value : HashOutput)
    (before after : CompState C) : Prop where
  data : dataOf x after =
    { dataOf x before with cache := (dataOf x before).cache.cacheQuery input value }
  bound : after.1.1.1.1.bound = before.1.1.1.1.bound
  trace : after.1.1.1.1.trace = before.1.1.1.1.trace
  count : after.1.1.1.2 = before.1.1.1.2 + 1
  reveal : after.1.1.2 = before.1.1.2
  mark : after.1.2 = before.1.2

 theorem eager_read_cache (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (sh : ShareStateT C (Bool × Bool)) (hg : ShareG g sh)
    (T : C.Term) (p : CPoint) (tag : Bool × Bool)
    (r : HashOutput × ShareStateT C (Bool × Bool))
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g (.read T p tag)).run sh)) :
    r.2.cache = Function.update sh.cache (T, p) (some (g (T, p))) := by
  cases hc : sh.cache (T, p) <;>
    simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      hc, pure_bind, mem_support_pure_iff] at hr <;> subst r
  · rfl
  · rw [← hg _ _ hc, ← hc, Function.update_eq_self]

theorem backend_slot_read (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (input : Query C) (hs : IsSlot x input) (st : CompState C)
    (hg : ShareG g st.2) (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (ha : RestAgree x rest st.1.1) (hb : st.2.bad = none) (hm : st.1.2 = false)
    (r : HashOutput × CompState C)
    (hr : r ∈ support ((shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.hash input))))).run st)) :
    r.1 = realTable g rest hs.choose ∧
    ReadPost x input r.1 st r.2 ∧ (r.2.2.bad = none ∨ NullBad r.2.2) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  have hi := TprfSecurityProof.slotInput_injective hinj (not_not.mp (not_or.mp hkeys).2)
  cases hrout : route x.2.1 input with
  | some z =>
    obtain ⟨T, p⟩ := z
    have he := (route_spec x.2.1 hinj input (T, p)).mp hrout
    have hz : hs.choose = .inl (T, p.val) := hi (hs.choose_spec.trans he)
    rw [backendT_shareRead capTag x q s pads τ g noise rest input T p hrout] at hr
    simp only [hashTail_slot x (key x.2.1 (T, p)) (he ▸ hs)] at hr
    simp only [mem_support_bind_iff, mem_support_pure_iff, exists_eq_left] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    have hvalue := (eager_read_shareG τ g T p (capTag st.1) st.2 hg a ha).1
    have hcache := eager_read_cache τ g st.2 hg T p (capTag st.1) a ha
    refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · simpa only [hz, realTable_constrained] using hvalue
    · simp only [dataOf, merged, splitRest, withCache, merge_erase, hcache,
        merge_update x.2.1 hinj, hvalue]
      rw [he]
      congr 1
      funext other
      by_cases ho : other = key x.2.1 (T, p)
      · subst ho; simp only [QueryCache.cacheQuery_self]
      · rw [QueryCache.cacheQuery_of_ne _ _ ho, QueryCache.cacheQuery_of_ne _ _ ho]
        cases hro : route x.2.1 other <;>
          simp [merge, hro, QueryCache.cacheQuery_of_ne _ _ ho]
    · have htag : capTag st.1 = (false, st.1.1.2.2) := by rw [← hm]; rfl
      exact eager_read_null τ g st.2 hb T p st.1.1.2.2 a (htag ▸ ha)
  | none =>
    let z : RestSlot C := ⟨hs.choose, fun T p he => by
      have hiq : input = key x.2.1 (T, p) := hs.choose_spec.symm.trans (congrArg
        (TprfSecurityProof.slotInput x.2.1 x.2.2) he)
      have hh := (route_spec x.2.1 hinj input (T, p)).mpr hiq
      rw [hrout] at hh; cases hh⟩
    have hz : restInput x.2.1 x.2.2 z = input := hs.choose_spec
    have hrz := (restRoute_spec x.2.1 x.2.2 hi input z).mpr hz
    have hval : realTable g rest hs.choose = rest z := realTable_rest g rest z
    rw [backendT_rest capTag x q s pads τ g noise rest input z hrout hrz] at hr
    have hroute : route x.2.1 (restInput x.2.1 x.2.2 z) = none := hz.symm ▸ hrout
    have norm (value : HashOutput) (cache : HashCache C) :=
      hashTail_slot x (restInput x.2.1 x.2.2 z) (hz.symm ▸ hs)
        (merged x.2.1 st.1.1 st.2.cache) value cache
    cases hc : (dataOf x st).cache (restInput x.2.1 x.2.2 z) with
    | none =>
      simp only [hc, norm, map_pure, mem_support_pure_iff] at hr
      subst r
      refine ⟨hval.symm, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl hb⟩
      · simp only [dataOf, splitRest, merged, withCache]
        rw [merge_erase, merge_cacheQuery_other x.2.1 _ _ _ hroute, merge_merge, hz]
      all_goals simp only [splitRest, merged, withCache]
    | some v =>
      have hv : v = rest z := ha z v (by
        rw [← hc]; simp [dataOf, merged, withCache, merge, hroute])
      simp only [hc, norm, map_pure, mem_support_pure_iff] at hr
      subst r
      refine ⟨hv.trans hval.symm, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl hb⟩
      · simp only [dataOf, splitRest, merged, withCache]
        rw [merge_erase, merge_merge, ← hz,
          observe_same (merge x.2.1 st.1.1.1.1.data.cache st.2.cache) _ v hc]
      all_goals simp only [splitRest, merged, withCache]

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.slot_not_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.slot_not_hash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.slot_no_hashCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.slot_no_hashCall

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.realWorld_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.realWorld_slot

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.hashTail_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.hashTail_slot

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.observe_slot_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.observe_slot_value

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.cacheRelation_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.cacheRelation_slot

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.merge_cacheQuery_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.merge_cacheQuery_other

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.merge_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.merge_merge

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.backend_slot_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncLocalSlot.backend_slot_read
