import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncHonestRead

/-! # Coupled slot reads and virtual reads of the O1 coupling

- `slotRead_sync` couples a real read of a slot, on the copy of the forger or on the free copy, with
  `sourceHashX` at the slot input. Both sides return the table value.
- `virtualRead_sync` couples a real honest read of a term at a constrained point with
  `sourceVirtualX`. The term becomes virtual, and a ready bound key has a revealed opening.
- Both posts are `CallPost`. `ReadStep` holds the effect of one real read, and `syncFields_observe`
  and `syncFields_step` carry the synchronization fields over the two sides of a call.
- A support hypothesis passes to a lemma through `no_implicit_lambda%`. Without it the elaborator
  reduces the run of the real call.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Calls
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame
open SigningCompilerSyncBackend SigningCompilerSyncRealRead SigningCompilerSyncLocalRead
open SigningCompilerSyncLocalSlot SigningCompilerSyncHonestRead
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

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

/-- One real read grows the log cache. -/
theorem ReadStep.realLog_le {input : Query C} {v : HashOutput} {a a' : RealState C}
    (h : ReadStep input v a a') : realLog a ≤ realLog a' := by
  obtain ⟨t, value, hl, -⟩ := h.log
  intro query w hq
  change SigningCacheLogProof.logCache a'.1.1.1.1.1.2 query = some w
  rw [hl, SigningCacheLogProof.logCache_logQuery]
  rw [show SigningCacheLogProof.logCache a.1.1.1.1.1.2 query = some w from hq]
  rfl

/-- One real read keeps the log agreement. -/
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

/-- A new visible entry after one real read is at the read input. -/
theorem ReadStep.fresh {input : Query C} {v : HashOutput} {a a' : RealState C}
    (h : ReadStep input v a a') (query : Query C) (hq : visibleOf a' query ≠ none) :
    visibleOf a query ≠ none ∨ query = input := by
  by_cases he : query = input
  · exact Or.inr he
  · rw [h.visible, QueryCache.cacheQuery_of_ne _ _ he] at hq
    exact Or.inl hq

/-- A larger cache holds each entry of a smaller cache. -/
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

/-- The synchronization fields pass to a compiler step that keeps the reveal map, the bound map,
the trace and the pending map, grows the data cache and adds only seen virtual terms. -/
theorem syncFields_step (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (src : SourceState C)
    (st st' : CompState C) (hs : SyncFields x s pads noise g rest a (src, st))
    (hreveal : st'.1.1.2 = st.1.1.2) (hbound : st'.1.1.1.1.bound = st.1.1.1.1.bound)
    (htrace : st'.1.1.1.1.trace = st.1.1.1.1.trace)
    (hpend : (dataOf x st').pending = (dataOf x st).pending)
    (hcache : (dataOf x st).cache ≤ (dataOf x st').cache)
    (hvirt : ∀ T p, (T, p) ∈ (dataOf x st').virtual → visibleOf a (.prf (x.2.1 T) p) ≠ none)
    (hf : Frame x rest st'.1.1 ∧ ShareG g st'.2) (hd : DoneCached st'.2)
    (hb : st'.2.bad = none) :
    SyncFields x s pads noise g rest a (src, st') :=
  { hs with
    reveal := ⟨hs.reveal.1.trans (congrArg Prod.fst hreveal).symm, hs.reveal.2⟩
    releasedPending := fun p ans hp hr => hcache (hs.releasedPending p ans (hpend ▸ hp) hr)
    opening := ⟨hs.opening.actualValue, fun e he T => by
      obtain ⟨w, hw⟩ := hs.opening.released e he T
      exact ⟨w, hcache hw⟩⟩
    pendingValid := hf.1.2.2
    allocated := fun p hp => hs.allocated p (hpend ▸ hp)
    virtualSeen := hvirt
    compilerBound := hbound.trans hs.compilerBound
    trace := hs.trace.trans htrace.symm
    bad := hb
    share := hf.2
    restAgree := hf.1.1
    restFree := hf.1.2.1
    frontier := fun edge hp => hs.frontier edge (hpend ▸ hp)
    doneCached := hd }

/-- A source reveal map that adds the opening of a bound key keeps each earlier reveal, and each
new key is that opening. -/
theorem reveal_update_frame (src : SourceState C) (rev' : HiddenKey → Option Digest) (e : KeyIndex)
    (d : Digest) (hrev : rev' = Function.update src.revealed (.opening bottomLayer e) (some d))
    (hunrev : src.revealed (.opening bottomLayer e) = none) (hbound : src.signing.bound e ≠ none) :
    (∀ k, src.revealed k ≠ none → rev' k = src.revealed k) ∧
      ∀ k, src.revealed k = none → rev' k ≠ none →
        ∃ e', k = .opening bottomLayer e' ∧ src.signing.bound e' ≠ none := by
  subst rev'
  refine ⟨fun k hk => ?_, fun k hk hk' => ?_⟩
  · have hne : k ≠ .opening bottomLayer e := fun he => hk (he ▸ hunrev)
    exact Function.update_of_ne hne _ _
  · by_cases he : k = .opening bottomLayer e
    · exact ⟨e, he, hbound⟩
    · rw [Function.update_of_ne he] at hk'
      exact (hk' hk).elim

section Calls
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A real slot read on either copy returns the table value and observes it. -/
theorem slot_readStep (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (forger : Bool)
    (z : TprfSecurityProof.Slot C) (a : RealState C)
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (ra : HashOutput × RealState C)
    (hra : ra ∈ support ((readCall prims x s pads u rest forger
      (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 z))).run a)) :
    ra.1 = realTable (gOf s pads u) rest z ∧
      ReadStep (TprfSecurityProof.slotInput x.2.1 x.2.2 z) (realTable (gOf s pads u) rest z) a ra.2 := by
  have hi := TprfSecurityProof.slotInput_injective (not_not.mp (not_or.mp hkeys).1)
    (not_not.mp (not_or.mp hkeys).2)
  have hsl : IsSlot x (TprfSecurityProof.slotInput x.2.1 x.2.2 z) := ⟨z, rfl⟩
  have hz : hsl.choose = z := hi hsl.choose_spec
  have hseen : ∀ w, visibleOf a (TprfSecurityProof.slotInput x.2.1 x.2.2 z) = some w →
      w = realTable (gOf s pads u) rest z := fun w hw =>
    realPrivate_slotValue x hkeys s pads noise _ rest a.2 (visibleOf a) hpriv z w hw
  cases forger with
  | true =>
    change ra ∈ support ((SigningCompilerUntil.fuse (rawTraceWorld prims x)
      (realImpl x (gOf s pads u) rest) (.inl (.inl (.inr (.inl
        (TprfSecurityProof.slotInput x.2.1 x.2.2 z)))))).run a) at hra
    rw [realWorld_slot prims x _ rest _ hsl, hz, mem_support_pure_iff] at hra
    subst ra
    refine ⟨rfl, rfl, hseen, rfl, rfl, rfl, rfl, _, _, rfl, rfl⟩
  | false =>
    change ra ∈ support ((SigningCompilerUntil.fuse (rawTraceWorld prims x)
      (realImpl x (gOf s pads u) rest) (.inr (.inr (.inl
        (TprfSecurityProof.slotInput x.2.1 x.2.2 z))))).run a) at hra
    rw [realWorld_slot_route prims x _ rest _ hsl _ (Or.inr rfl), mem_support_pure_iff] at hra
    subst ra
    refine ⟨by rw [hz]; rfl, by rw [hz], hseen, rfl, rfl, rfl, rfl, _, _, rfl, ?_⟩
    rw [hz]
    rfl

/-- The release test before a read either does nothing or runs the release of an unrevealed
opening of a bottom key whose terms are ready. -/
theorem prefix_cases (backend : QueryImpl (SpecX C) (StateT (CompState C) ProbComp))
    (input : Query C) (src : SourceState C) (st : CompState C)
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX backend (ordinaryPrefix x input src st) src st)) :
    r = (((), src), st) ∨ ∃ seed e, input = .prf seed (.randomizer bottomLayer e) ∧
      ReadyAfter x.2.1 (dataOf x st) src.signing e input ∧
      src.revealed (.opening bottomLayer e) = none ∧
      r ∈ support (runX backend (sourceReleaseOpeningX x.1 x.2.1 e) src st) := by
  cases input with
  | prf seed point =>
    cases point with
    | randomizer lay e =>
      by_cases hp : lay = bottomLayer ∧
          ReadyAfter x.2.1 (dataOf x st) src.signing e (.prf seed (.randomizer lay e))
      · obtain ⟨rfl, hready⟩ := hp
        simp only [ordinaryPrefix, hready, and_self, if_true] at hr
        by_cases hrev : src.revealed (.opening bottomLayer e) = none
        · exact Or.inr ⟨seed, e, rfl, hready, hrev, hr⟩
        · rw [runX_releaseOpening_revealed _ x.1 x.2.1 e src st hrev, mem_support_pure_iff] at hr
          exact Or.inl hr
      · simp only [ordinaryPrefix, hp, if_false, runX_pure, mem_support_pure_iff] at hr
        exact Or.inl hr
    | _ => simp only [ordinaryPrefix, runX_pure, mem_support_pure_iff] at hr; exact Or.inl hr
  | _ => simp only [ordinaryPrefix, runX_pure, mem_support_pure_iff] at hr; exact Or.inl hr

/-- The opening release from the synchronization fields at a real state `a1` after the read. -/
theorem release_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (e : KeyIndex)
    (seed : HashOutput) (a1 : RealState C) (src : SourceState C) (st : CompState C)
    (old : HashCache C)
    (hs : SyncFields x s pads noise (gOf s pads u) rest a1 (src, st))
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) old)
    (hmark : st.1.2 = false) (hunrev : src.revealed (.opening bottomLayer e) = none)
    (hready : ReadyAfter x.2.1 (dataOf x st) src.signing e
      (.prf seed (.randomizer bottomLayer e)))
    (hafter : VisibleAfter x (gOf s pads u) e (.prf seed (.randomizer bottomLayer e)) old
      (visibleOf a1))
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceReleaseOpeningX x.1 x.2.1 e) src st)) :
    Stop r.2 ∨ (SyncWithoutCount x s pads noise (gOf s pads u) rest a1 (r.1.2, r.2) ∧
      r.2.1.1.1.2 = st.1.1.1.2 ∧ r.2.1.2 = st.1.2 ∧
      (dataOf x r.2).pending = (dataOf x st).pending ∧
      (dataOf x r.2).virtual = (dataOf x st).virtual ∧
      r.1.2.revealed = Function.update src.revealed (.opening bottomLayer e)
        (some (s (.opening bottomLayer e)))) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  have hrow := readyAfter_covers_visible x hkeys s pads noise (gOf s pads u) rest a1.2 old
    (visibleOf a1) (dataOf x st) src.signing e _ hs.realPrivate hc hs.virtualSeen hready hafter
  have hp := releaseOpening_post x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest e _
    src st old (visibleOf a1) hmark hunrev hs.reveal hc hs.releasedPending hs.pendingValid
    hs.allocated hs.restFree hs.share hs.doneCached hs.bad hafter hrow r hr
  rcases releaseOpening_sync x hkeys q s pads (tauOf s pads) (gOf s pads u) noise rest e seed a1
      src st old hs hc hmark hunrev hready hafter r hr with hstop | ⟨hsync, hframe, _, hcount, _⟩
  · exact Or.inl hstop
  · refine Or.inr ⟨hsync, hcount, ?_, hframe.pending, hframe.virtual,
      congrArg SourceState.revealed hp.source⟩
    rw [hp.backend]
    rfl

/-- A virtual call adds the term to the virtual set and counts once. It keeps every other part. -/
theorem backendT_virtual_step (T : C.Term) (p : Point) (st : CompState C)
    (r : Unit × CompState C)
    (hr : r ∈ support ((compBackend x q s pads u rest noise
      (.inl (.inl (.inl (.virtual T p))))).run st)) :
    r.2.2 = st.2 ∧ r.2.1.2 = st.1.2 ∧ r.2.1.1.2 = st.1.1.2 ∧
      r.2.1.1.1.2 = st.1.1.1.2 + 1 ∧ r.2.1.1.1.1.bound = st.1.1.1.1.bound ∧
      r.2.1.1.1.1.trace = st.1.1.1.1.trace ∧
      (dataOf x r.2).cache = (dataOf x st).cache ∧
      (dataOf x r.2).pending = (dataOf x st).pending ∧
      (dataOf x r.2).virtual = insert (T, p) (dataOf x st).virtual ∧
      RestFree x.2.1 r.2.1.1.1.1.data.cache := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run,
    ordinary, SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    compilerImpl, deferredImpl, map_pure] at hr
  simp [StateT.mk] at hr
  subst r
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_, restFree_erase _ _⟩
  all_goals simp [deferredInputSide, deferredCandidate, deferredCounted, splitRest, merged, withCache,
    dataOf, merge_erase, merge_merge]

/-- A virtual call after a real read of its cell keeps the cache relation. The real cell holds the
read value, and the term is a suspended cell or a materialized cell with the same value. -/
theorem cacheRelation_observeVirtual {P : PublicParameter} {seeds : C.Term → HashOutput}
    {data data' : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (T : C.Term) (p : Point) (v : HashOutput)
    (hseen : ∀ w, actual (.prf (seeds T) p) = some w → w = v)
    (hcache : data'.cache = data.cache) (hpend : data'.pending = data.pending)
    (hvirt : data'.virtual = insert (T, p) data.virtual) :
    CacheRelation P seeds s data' (actual.cacheQuery (.prf (seeds T) p) v) := by
  have hle := le_cacheQuery_of_seen actual _ v hseen
  refine ⟨fun query hn => ?_, fun p' value hp => hle (h.pending p' value (hpend ▸ hp))⟩
  by_cases he : query = .prf (seeds T) p
  · subst query
    rw [QueryCache.cacheQuery_self]
    cases hd : data'.cache (.prf (seeds T) p) with
    | none => exact (hn ⟨hd, Or.inr ⟨T, p, by rw [hvirt]; exact Finset.mem_insert_self _ _, rfl⟩⟩).elim
    | some w =>
      rw [hcache] at hd
      rw [hseen w (h.cache_le hd)]
  · rw [QueryCache.cacheQuery_of_ne _ _ he, hcache]
    apply h.agree query
    rintro ⟨hn1, hn2⟩
    refine hn ⟨hcache ▸ hn1, ?_⟩
    rcases hn2 with ⟨p', value, hp, hq⟩ | ⟨U, point, hu, hq⟩
    · exact Or.inl ⟨p', value, hpend ▸ hp, hq⟩
    · exact Or.inr ⟨U, point, by rw [hvirt]; exact Finset.mem_insert_of_mem hu, hq⟩

/-- A source virtual call runs the virtual call. Then it does nothing, or it runs the release of an
unrevealed opening of a ready bottom key. With no release a ready bottom key is revealed. -/
theorem virtual_cases (T : C.Term) (pt : Point) (src : SourceState C) (st : CompState C)
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceVirtualX x.1 x.2.1 T pt) src st)) :
    ∃ r0 ∈ support ((compBackend x q s pads u rest noise
        (.inl (.inl (.inl (.virtual T pt))))).run st),
      (r = (((), src), r0.2) ∧ ∀ e, pt = .randomizer bottomLayer e →
          OpeningReady x.2.1 (dataOf x r0.2) src.signing e →
            src.revealed (.opening bottomLayer e) ≠ none) ∨
      ∃ e, pt = .randomizer bottomLayer e ∧ OpeningReady x.2.1 (dataOf x r0.2) src.signing e ∧
        src.revealed (.opening bottomLayer e) = none ∧
        r ∈ support (runX (compBackend x q s pads u rest noise)
          (sourceReleaseOpeningX x.1 x.2.1 e) src r0.2) := by
  simp only [sourceVirtualX, runX_bind, runX_deferred, mem_support_bind_iff, support_map,
    Set.mem_image] at hr
  obtain ⟨_, ⟨r0, hr0, rfl⟩, hr⟩ := hr
  refine ⟨r0, hr0, ?_⟩
  have hfree := (backendT_virtual_step x q s pads u rest noise T pt st r0 hr0).2.2.2.2.2.2.2.2.2
  cases pt with
  | randomizer lay e =>
    by_cases hl : lay = bottomLayer
    · subst hl
      simp only [if_true, runX_bind, runX_deferred, backendT_snapshot capTag x q s pads
        (tauOf s pads) (gOf s pads u) noise rest r0.2 hfree, runX_get, map_pure, pure_bind] at hr
      by_cases hready : OpeningReady x.2.1 (dataOf x r0.2) src.signing e
      · simp only [hready, if_true] at hr
        by_cases hrev : src.revealed (.opening bottomLayer e) = none
        · exact Or.inr ⟨e, rfl, hready, hrev, hr⟩
        · rw [runX_releaseOpening_revealed _ x.1 x.2.1 e src r0.2 hrev, mem_support_pure_iff] at hr
          refine Or.inl ⟨hr, fun e' he _ => ?_⟩
          cases he
          exact hrev
      · simp only [hready, if_false, runX_pure, mem_support_pure_iff] at hr
        refine Or.inl ⟨hr, fun e' he hr' => ?_⟩
        cases he
        exact (hready hr').elim
    · simp only [hl, if_false, runX_pure, mem_support_pure_iff] at hr
      refine Or.inl ⟨hr, fun e' he _ => ?_⟩
      cases he
      exact (hl rfl).elim
  | _ =>
    simp only [runX_pure, mem_support_pure_iff] at hr
    exact Or.inl ⟨hr, fun e' he _ => by cases he⟩

/-- A slot read that returns its value. Both sides return the table value. The compiler side can
run the opening release before the read. -/
theorem slotRead_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (forger : Bool)
    (cCore : Carried C) (z : TprfSecurityProof.Slot C) (a : RealState C) (src : SourceState C)
    (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : HashOutput × RealState C)
    (hra : ra ∈ support ((readCall prims x s pads u rest forger
      (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 z))).run a))
    (rb : (HashOutput × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceHashX x.1 x.2.1 (TprfSecurityProof.slotInput x.2.1 x.2.2 z)) src st)) :
    CallPost x q s pads u rest noise cCore
      (fun query => query = TprfSecurityProof.slotInput x.2.1 x.2.2 z)
      a src st (fun va vb => va = vb ∧ va = realTable (gOf s pads u) rest z) ra rb := by
  have hi := TprfSecurityProof.slotInput_injective (not_not.mp (not_or.mp hkeys).1)
    (not_not.mp (not_or.mp hkeys).2)
  have hsl : IsSlot x (TprfSecurityProof.slotInput x.2.1 x.2.2 z) := ⟨z, rfl⟩
  have hz : hsl.choose = z := hi hsl.choose_spec
  obtain ⟨⟨hf, hc⟩, hcnt⟩ := hs
  obtain ⟨hva, hstep⟩ := slot_readStep prims x s pads u rest noise hkeys forger z a
    hf.realPrivate ra hra
  have hle : visibleOf a ≤ visibleOf ra.2 := by
    rw [hstep.visible]
    exact le_cacheQuery_of_seen _ _ _ hstep.seen
  have hpriv1 : RealPrivate x s pads noise (gOf s pads u) rest ra.2.2 (visibleOf ra.2) := by
    have ho := hf.realPrivate.observe_slot _ hsl
    rw [hz] at ho
    rw [hstep.priv, hstep.visible]
    exact ho
  have hf1 : SyncFields x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) (src, st) :=
    syncFields_observe x hkeys s pads u rest noise (withCarried a cCore) (withCarried ra.2 cCore)
      (src, st) hf hpriv1 hle rfl hstep.trace
  have hvis1 : visibleOf ra.2 (TprfSecurityProof.slotInput x.2.1 x.2.2 z) =
      some (realTable (gOf s pads u) rest z) := by
    rw [hstep.visible, QueryCache.cacheQuery_self]
  have hrb0 := hrb
  rw [runX_sourceHashX capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ src st
    hf.restFree] at hrb
  simp only [mem_support_bind_iff, support_map, Set.mem_image] at hrb
  obtain ⟨r1, hr1, r, hr, rfl⟩ := hrb
  have hr1' : r1 ∈ support (runX (compBackend x q s pads u rest noise)
      (ordinaryPrefix x (TprfSecurityProof.slotInput x.2.1 x.2.2 z) src st) src st) := hr1
  have hmid : Stop r1.2 ∨
      (SyncFields x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) (r1.1.2, r1.2) ∧
        (∃ old, CacheRelation x.1 x.2.1 s (dataOf x r1.2) old ∧ old ≤ visibleOf ra.2 ∧
          old.cacheQuery (TprfSecurityProof.slotInput x.2.1 x.2.2 z)
            (realTable (gOf s pads u) rest z) = visibleOf ra.2) ∧
        r1.2.1.1.1.2 = st.1.1.1.2 ∧ r1.2.1.2 = false ∧
        (dataOf x r1.2).pending = (dataOf x st).pending ∧
        (dataOf x r1.2).virtual = (dataOf x st).virtual ∧
        (∀ k, src.revealed k ≠ none → r1.1.2.revealed k = src.revealed k) ∧
        ∀ k, src.revealed k = none → r1.1.2.revealed k ≠ none →
          ∃ e', k = .opening bottomLayer e' ∧ src.signing.bound e' ≠ none) := by
    rcases prefix_cases x _ _ src st r1 hr1' with rfl | ⟨seed, e, hin, hready, hunrev, hrel⟩
    · exact Or.inr ⟨hf1, ⟨visibleOf a, hc, hle, hstep.visible.symm⟩, rfl, hmark, rfl, rfl,
        fun _ _ => rfl, fun _ h h' => (h' h).elim⟩
    · have hafter : VisibleAfter x (gOf s pads u) e (.prf seed (.randomizer bottomLayer e))
          (visibleOf a) (visibleOf (withCarried ra.2 cCore)) := by
        change VisibleAfter x (gOf s pads u) e (.prf seed (.randomizer bottomLayer e))
          (visibleOf a) (visibleOf ra.2)
        rw [← hin]
        by_cases hv : visibleOf a (TprfSecurityProof.slotInput x.2.1 x.2.2 z) = none
        · rcases z with ⟨T, pt⟩ | m
          · simp only [TprfSecurityProof.slotInput, Query.prf.injEq] at hin
            obtain ⟨rfl, rfl⟩ := hin
            refine Or.inr (Or.inr ⟨T, rfl, hv, ?_⟩)
            rw [hstep.visible, ← realTable_constrained (gOf s pads u) rest T
              ⟨_, constrained_bottom_randomizer e⟩]
          · simp [TprfSecurityProof.slotInput] at hin
        · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hv
          rw [hstep.seen w hw] at hw
          exact Or.inr (Or.inl ⟨hv, by rw [hstep.visible, observe_same _ _ _ hw]⟩)
      rcases release_sync x q s pads u rest noise hkeys e seed (withCarried ra.2 cCore) src st
          (visibleOf a) hf1 hc hmark hunrev (hin ▸ hready) hafter r1 hrel with
        hstop | ⟨⟨hf2, hc2⟩, hcount2, hmark2, hpend2, hvirt2, hrev2⟩
      · exact Or.inl hstop
      · obtain ⟨hk1, hk2⟩ := reveal_update_frame src _ e _ hrev2 hunrev hready.1
        exact Or.inr ⟨hf2, ⟨visibleOf ra.2, hc2, le_rfl, observe_same _ _ _ hvis1⟩, hcount2,
          hmark2.trans hmark, hpend2, hvirt2, hk1, hk2⟩
  rcases hmid with hstop | ⟨hf2, ⟨old, hc2, hold, hold'⟩, hcount2, hmark2, hpend2, hvirt2,
    hrevk, hopen⟩
  · exact Or.inr (Or.inl (backendT_stop x.1 x.2.1 x.2.2 q s pads _ _ noise rest _ r1.2 hstop r hr))
  obtain ⟨hval, hpost, hbad⟩ := backend_slot_read x hkeys q s pads (tauOf s pads) (gOf s pads u)
    noise rest _ hsl r1.2 hf2.share hf2.restFree hf2.restAgree hf2.bad hmark2 r hr
  rw [hz] at hval
  rcases hbad with hbad | hbad
  swap
  · exact Or.inr (Or.inl (Or.inl hbad))
  have hframe := safe_frame capTag x hi q s pads (tauOf s pads) (gOf s pads u) noise rest _
    (safe_sourceHashX x.1 x.2.1 _) src st ⟨⟨hf.restAgree, hf.restFree, hf.pendingValid⟩, hf.share⟩
    _ hrb0
  have hd := simulate_doneCached capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ st
    hf.doneCached _ hrb0
  have hcontrol := SourceKeepsX.run (sourceControl_sourceHash x.1 x.2.1 _) _ src st _ hrb0
  have hdata := hpost.data
  rw [hval] at hdata
  have hcache : (dataOf x r1.2).cache ≤ (dataOf x r.2).cache := by
    rw [hdata]
    apply le_cacheQuery_of_seen
    intro w hw
    have h1 := hold (hc2.cache_le hw)
    rw [← hold', QueryCache.cacheQuery_self] at h1
    exact (Option.some.inj h1).symm
  have hf3 := syncFields_step x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) r1.1.2
    r1.2 r.2 hf2 hpost.reveal hpost.bound hpost.trace (by rw [hdata]) hcache
    (by rw [hdata]; exact hf2.virtualSeen) hframe hd hbad
  refine Or.inr (Or.inr ⟨⟨hva.trans hval.symm, hva⟩, ⟨⟨hf3, ?_⟩, ?_⟩, ?_, hpost.mark.trans hmark2⟩)
  · show CacheRelation _ _ _ _ (visibleOf ra.2)
    rw [hdata, ← hold']
    exact cacheRelation_slot x s (dataOf x r1.2) old _ hsl _ hc2
  · change ra.2.1.1.1.1.1.1.2 = r.2.1.1.1.2
    rw [hstep.count, hpost.count, hcount2]
    exact congrArg (· + 1) hcnt
  · exact
      { carried := hstep.carried
        visible := hle
        fresh := hstep.fresh
        log := hstep.realLog_le
        logAgreement := hstep.logAgreement x.1
        trace := hstep.trace
        signing := congrArg (fun c => c.1) hcontrol
        trees := congrArg (fun c => c.2.1) hcontrol
        exposed := congrArg (fun c => c.2.2.2.1) hcontrol
        candidates := congrArg (fun c => c.2.2.2.2) hcontrol
        revealed := hrevk
        opened := hopen
        pending := fun p hp => by rw [hdata]; change (dataOf x r1.2).pending p ≠ none; rw [hpend2]; exact hp
        virtual := fun T p hp => by
          rw [hdata]; change (T, p) ∈ (dataOf x r1.2).virtual; rw [hvirt2]; exact hp }

/-- A real honest read of a term at a constrained point returns the table value and observes it. -/
theorem honestSlot_readStep (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (T : C.Term)
    (p : CPoint) (a : RealState C)
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (ra : HashOutput × RealState C)
    (hra : ra ∈ support ((realCall prims x s pads u rest (.prf (x.2.1 T) p.val)).run a)) :
    ra.1 = gOf s pads u (T, p) ∧ ReadStep (.prf (x.2.1 T) p.val) (gOf s pads u (T, p)) a ra.2 := by
  have hi := TprfSecurityProof.slotInput_injective (not_not.mp (not_or.mp hkeys).1)
    (not_not.mp (not_or.mp hkeys).2)
  have hsl : IsSlot x (.prf (x.2.1 T) p.val) := ⟨.inl (T, p.val), rfl⟩
  have hz : hsl.choose = .inl (T, p.val) := hi hsl.choose_spec
  have hseen : ∀ w, visibleOf a (.prf (x.2.1 T) p.val) = some w → w = gOf s pads u (T, p) :=
    fun w hw => (realPrivate_slotValue x hkeys s pads noise _ rest a.2 (visibleOf a) hpriv
      (.inl (T, p.val)) w hw).trans (realTable_constrained _ rest T p)
  change ra ∈ support ((SigningCompilerUntil.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) (.inr (.inr (.inl (.prf (x.2.1 T) p.val))))).run a) at hra
  rw [realWorld_slot_route prims x _ rest _ hsl _ (Or.inr rfl), mem_support_pure_iff] at hra
  subst ra
  have hv : realTable (gOf s pads u) rest hsl.choose = gOf s pads u (T, p) := by
    rw [hz]
    exact realTable_constrained _ rest T p
  refine ⟨by rw [← hv]; rfl, by rw [hv], hseen, rfl, rfl, rfl, rfl, _, _, rfl, ?_⟩
  rw [hv]
  rfl

/-- A slot read of a tree build. The real side reads the table value. The compiler side records a
virtual term and can run the opening release after it. When each term of a bound key is virtual,
the opening of the key is revealed. -/
theorem virtualRead_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (T : C.Term) (p : CPoint) (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : HashOutput × RealState C)
    (hra : ra ∈ support ((realCall prims x s pads u rest (.prf (x.2.1 T) p.val)).run a))
    (rb : (Unit × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceVirtualX x.1 x.2.1 T p.val) src st)) :
    CallPost x q s pads u rest noise cCore (fun query => query = .prf (x.2.1 T) p.val) a src st
      (fun va _ => va = gOf s pads u (T, p) ∧ (T, p.val) ∈ (dataOf x rb.2).virtual ∧
        ∀ e, p.val = .randomizer bottomLayer e → src.signing.bound e ≠ none →
          (∀ T', (T', p.val) ∈ (dataOf x rb.2).virtual) →
            rb.1.2.revealed (.opening bottomLayer e) ≠ none) ra rb := by
  have hi := TprfSecurityProof.slotInput_injective (not_not.mp (not_or.mp hkeys).1)
    (not_not.mp (not_or.mp hkeys).2)
  have hsl : IsSlot x (.prf (x.2.1 T) p.val) := ⟨.inl (T, p.val), rfl⟩
  have hz : hsl.choose = .inl (T, p.val) := hi hsl.choose_spec
  have hval : realTable (gOf s pads u) rest (.inl (T, p.val)) = gOf s pads u (T, p) :=
    realTable_constrained _ rest T p
  obtain ⟨⟨hf, hc⟩, hcnt⟩ := hs
  obtain ⟨hva, hstep⟩ := honestSlot_readStep prims x s pads u rest noise hkeys T p a
    hf.realPrivate ra (no_implicit_lambda% hra)
  have hle : visibleOf a ≤ visibleOf ra.2 := by
    rw [hstep.visible]
    exact le_cacheQuery_of_seen _ _ _ hstep.seen
  have hpriv1 : RealPrivate x s pads noise (gOf s pads u) rest ra.2.2 (visibleOf ra.2) := by
    have ho := hf.realPrivate.observe_slot _ hsl
    rw [hz, hval] at ho
    rw [hstep.priv, hstep.visible]
    exact ho
  have hf1 : SyncFields x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) (src, st) :=
    syncFields_observe x hkeys s pads u rest noise (withCarried a cCore) (withCarried ra.2 cCore)
      (src, st) hf hpriv1 hle rfl hstep.trace
  have hvis1 : visibleOf ra.2 (.prf (x.2.1 T) p.val) = some (gOf s pads u (T, p)) := by
    rw [hstep.visible, QueryCache.cacheQuery_self]
  have hrb0 := hrb
  obtain ⟨r0, hr0, hcase⟩ := virtual_cases x q s pads u rest noise T p.val src st rb
    (no_implicit_lambda% hrb)
  obtain ⟨h0share, h0mark, h0rev, h0count, h0bound, h0trace, h0cache, h0pend, h0virt, -⟩ :=
    backendT_virtual_step x q s pads u rest noise T p.val st r0 hr0
  have hframe0 := safe_frame capTag x hi q s pads (tauOf s pads) (gOf s pads u) noise rest
    (liftM (deferredQueryX (.virtual T p.val))) (safe_deferred _ trivial) src st
    ⟨⟨hf.restAgree, hf.restFree, hf.pendingValid⟩, hf.share⟩ ((r0.1, src), r0.2) (by
      change ((r0.1, src), r0.2) ∈ support (runX (compBackend x q s pads u rest noise)
        (liftM (deferredQueryX (.virtual T p.val))) src st)
      rw [runX_deferred, support_map]
      exact ⟨r0, hr0, rfl⟩)
  have hc0 : CacheRelation x.1 x.2.1 s (dataOf x r0.2) (visibleOf ra.2) := by
    rw [hstep.visible]
    exact cacheRelation_observeVirtual s hc T p.val _ hstep.seen h0cache h0pend h0virt
  have hf0 : SyncFields x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) (src, r0.2) :=
    syncFields_step x s pads noise (gOf s pads u) rest _ src st r0.2 hf1 h0rev h0bound h0trace
      h0pend (le_of_eq h0cache.symm) (fun T' p' hp' => by
        rw [h0virt, Finset.mem_insert] at hp'
        rcases hp' with he | hp'
        · cases he
          change visibleOf ra.2 _ ≠ none
          rw [hvis1]
          exact Option.some_ne_none _
        · exact hf1.virtualSeen T' p' hp') hframe0 (by rw [h0share]; exact hf.doneCached)
      (by rw [h0share]; exact hf.bad)
  have hcontrol := SourceKeepsX.run (sourceControl_sourceVirtual x.1 x.2.1 T p.val) _ src st _ hrb0
  have hcount0 : (withCarried ra.2 cCore).1.1.1.1.1.1.2 = r0.2.1.1.1.2 := by
    change ra.2.1.1.1.1.1.1.2 = r0.2.1.1.1.2
    rw [hstep.count, h0count]
    exact congrArg (· + 1) hcnt
  have hmem : (T, p.val) ∈ (dataOf x r0.2).virtual := by
    rw [h0virt]
    exact Finset.mem_insert_self _ _
  have frame (rb' : (Unit × SourceState C) × CompState C) (hb' : rb'.1.2 = rb.1.2)
      (hrevk : ∀ k, src.revealed k ≠ none → rb'.1.2.revealed k = src.revealed k)
      (hopen : ∀ k, src.revealed k = none → rb'.1.2.revealed k ≠ none →
        ∃ e', k = .opening bottomLayer e' ∧ src.signing.bound e' ≠ none)
      (hpend : (dataOf x rb'.2).pending = (dataOf x r0.2).pending)
      (hvirt : (dataOf x rb'.2).virtual = (dataOf x r0.2).virtual) :
      CallFrame x (fun query => query = .prf (x.2.1 T) p.val) a ra.2 (src, st) (rb'.1.2, rb'.2) :=
    { carried := hstep.carried
      visible := hle
      fresh := hstep.fresh
      log := hstep.realLog_le
      logAgreement := hstep.logAgreement x.1
      trace := hstep.trace
      signing := hb' ▸ congrArg (fun c => c.1) hcontrol
      trees := hb' ▸ congrArg (fun c => c.2.1) hcontrol
      exposed := hb' ▸ congrArg (fun c => c.2.2.2.1) hcontrol
      candidates := hb' ▸ congrArg (fun c => c.2.2.2.2) hcontrol
      revealed := hrevk
      opened := hopen
      pending := fun p' hp' => by
        change (dataOf x rb'.2).pending p' ≠ none
        rw [hpend, h0pend]
        exact hp'
      virtual := fun T' p' hp' => by
        change (T', p') ∈ (dataOf x rb'.2).virtual
        rw [hvirt, h0virt]
        exact Finset.mem_insert_of_mem hp' }
  rcases hcase with ⟨rfl, hside⟩ | ⟨e, hpe, hready, hunrev, hrel⟩
  · refine Or.inr (Or.inr ⟨⟨hva, hmem, fun e he hbnd hall => hside e he ⟨hbnd, fun T' =>
      Or.inl (he ▸ hall T')⟩⟩, ⟨⟨hf0, hc0⟩, hcount0⟩,
      frame _ rfl (fun _ _ => rfl) (fun _ h h' => (h' h).elim) rfl rfl, h0mark.trans hmark⟩)
  · have hready' : ReadyAfter x.2.1 (dataOf x r0.2) src.signing e
        (.prf (x.2.1 T) (.randomizer bottomLayer e)) :=
      ⟨hready.1, fun T' => (hready.2 T').elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    have hafter : VisibleAfter x (gOf s pads u) e (.prf (x.2.1 T) (.randomizer bottomLayer e))
        (visibleOf ra.2) (visibleOf (withCarried ra.2 cCore)) :=
      Or.inr (Or.inl ⟨by rw [← hpe, hvis1]; exact Option.some_ne_none _, rfl⟩)
    rcases release_sync x q s pads u rest noise hkeys e (x.2.1 T) (withCarried ra.2 cCore) src
        r0.2 (visibleOf ra.2) hf0 hc0 (h0mark.trans hmark) hunrev hready' hafter rb hrel with
      hstop | ⟨hsync, hcount2, hmark2, hpend2, hvirt2, hrev2⟩
    · exact Or.inr (Or.inl hstop)
    · obtain ⟨hk1, hk2⟩ := reveal_update_frame src _ e _ hrev2 hunrev hready.1
      refine Or.inr (Or.inr ⟨⟨hva, hvirt2 ▸ hmem, fun e' he' _ _ => ?_⟩,
        ⟨hsync, hcount0.trans hcount2.symm⟩, frame rb rfl hk1 hk2 hpend2 hvirt2,
        hmark2.trans (h0mark.trans hmark)⟩)
      rw [hpe] at he'
      cases he'
      rw [hrev2, Function.update_self]
      exact Option.some_ne_none _

end Calls

end ThresholdLeanXmssSecurity.SigningCompilerO1Calls

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.le_cacheQuery_of_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.le_cacheQuery_of_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.observe_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.observe_mem_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ReadStep.realLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ReadStep.realLog_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ReadStep.logAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ReadStep.logAgreement

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ReadStep.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ReadStep.fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ne_none_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.ne_none_of_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.syncFields_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.syncFields_observe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.syncFields_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.syncFields_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.reveal_update_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.reveal_update_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.slot_readStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.slot_readStep

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.prefix_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.prefix_cases

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.release_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.release_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.backendT_virtual_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.backendT_virtual_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.cacheRelation_observeVirtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.cacheRelation_observeVirtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.virtual_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.virtual_cases

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.slotRead_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.slotRead_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.honestSlot_readStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.honestSlot_readStep

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Calls.virtualRead_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Calls.virtualRead_sync
