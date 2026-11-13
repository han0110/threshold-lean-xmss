import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncHonestRead

/-! # Reads that are no slot

`ordinaryRead_sync` couples a read of `H` or of the PRG that is no slot and no bottom base input.

- A call with no bottom base input runs no grind and keeps the trace (`noBase_cachedExtra`,
  `noBase_traceStepAt`). So both views are lazy reads of their caches (`readCall_view`,
  `cacheRead_noBase`), and `cacheQuery_rel` couples them.
- `readCall_support` gives the effect of the real read on the visible cache, the carried state,
  the count and the log.
- `prefix_call` is the opening release before a read at a bottom randomizer point, with its frame.
- `read_call` is the read after the release when the input is no suspended point.
- An exact hit at an unrevealed key stops the compiler by `capHit_stuck`, or the real count passes
  `q`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Reads
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
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

section NoBase
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind

/-- A call with no bottom base input runs no grind. -/
theorem noBase_cachedExtra (seeds : C.Term → HashOutput) (P : PublicParameter)
    (before after : SigningFlatProof.FlatState C) (call : (WorldSpec C).Domain)
    (hb : ∀ i, SigningFlatProof.HashCallAt i call →
      ∀ e ρ message, i ≠ randomizerInput P bottomLayer e ρ message) :
    SigningR1FixedProof.cachedExtra seeds P before call after = pure () := by
  unfold SigningR1FixedProof.cachedExtra
  apply if_neg
  rintro ⟨e, _, i, hi, hc⟩
  obtain ⟨message, _, rfl⟩ := Option.map_eq_some_iff.mp hi
  exact hb _ hc _ _ _ rfl

/-- A call with no bottom base input keeps the trace and the stale bit. -/
theorem noBase_traceStepAt (seeds : C.Term → HashOutput) (P : PublicParameter)
    (before after : HashCache C) (signing : TsigState C) (call : (WorldSpec C).Domain)
    (aux : XmssSecurity.SigningCacheTrace × Bool)
    (hb : ∀ i, SigningFlatProof.HashCallAt i call →
      ∀ e ρ message, i ≠ randomizerInput P bottomLayer e ρ message) :
    SigningLaneUnionProof.traceStepAt seeds P before signing call after aux = aux := by
  unfold SigningLaneUnionProof.traceStepAt
  apply dif_neg
  rintro ⟨e, _, i, hi, hc⟩
  obtain ⟨message, _, rfl⟩ := Option.map_eq_some_iff.mp hi
  exact hb _ hc _ _ _ rfl

/-- A read with no bottom base input is a lazy read of the cache with the same trace. -/
theorem cacheRead_noBase (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : Query C) (call : (WorldSpec C).Domain) (signing : TsigState C)
    (trace : XmssSecurity.SigningCacheTrace × Bool) (cache : HashCache C)
    (hb : ∀ i, SigningFlatProof.HashCallAt i call →
      ∀ e ρ message, i ≠ randomizerInput P bottomLayer e ρ message) :
    cacheRead P seeds input call signing trace cache =
      (fun r => (r.1, r.2, trace)) <$>
        (((Query C →ₒ HashOutput).randomOracle input).run cache) := by
  unfold cacheRead
  simp only [noBase_cachedExtra seeds P _ _ call hb, simulateQ_pure,
    StateT.run_pure, noBase_traceStepAt seeds P _ _ signing call trace hb,
    map_pure, bind_pure_comp]

/-- A world read names its input in each hash call. -/
theorem hashCallAt_read (rq : (RoSpec C).Domain) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr rq)) ∨ t = .inr (.inr rq)) (i : HashInput)
    (hi : SigningFlatProof.HashCallAt i t) : readInput rq = .hash i := by
  rcases ht with rfl | rfl <;> rcases hi with h | h <;> cases h <;> rfl

end NoBase

section Log

/-- A read that adds no log entry at a tracked input keeps the comparison of the log. -/
theorem logAgreement_untracked (P : PublicParameter) (query : Query C)
    (hq : ¬SigningCacheLogProof.Tracked query) (L : SigningHitLaneProof.LoggedState C)
    (hL : SigningPartnerCompareProof.LogAgreement P L) (w : HashOutput × HashCache C)
    (hw : w ∈ support (((Query C →ₒ HashOutput).randomOracle query).run L.1.1))
    (log : QueryLog (WorldSpec C))
    (hlog : SigningCacheLogProof.logCache log = SigningCacheLogProof.logCache L.2) (n : ℕ) :
    SigningPartnerCompareProof.LogAgreement P ((w.2, n), log) := by
  obtain ⟨hle, _, hother⟩ := randomOracle_support query L.1.1 w hw
  refine ⟨?_, ?_⟩
  · rw [hlog]
    exact le_trans hL.1 hle
  · intro q' hq'
    change w.2 q' = SigningCacheLogProof.logCache log q'
    have hne : q' ≠ query := by
      rintro rfl
      exact hq hq'.1
    rw [hlog, hother q' hne]
    exact hL.2 q' hq'

/-- A logged call only adds entries to the cache of the log. -/
theorem logCache_le_logQuery (log : QueryLog (WorldSpec C)) (t : (WorldSpec C).Domain)
    (v : (WorldSpec C).Range t) :
    SigningCacheLogProof.logCache log ≤ SigningCacheLogProof.logCache (log.logQuery t v) := by
  intro q' v' h
  rw [SigningCacheLogProof.logCache_logQuery, h]
  rfl

end Log


section RealRead
variable (prims : Primitives) (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  SigningLaneUnionProof.traceStepAt
set_option backward.isDefEq.respectTransparency false

/-- The view of a real read with no bottom base input is a lazy read of the visible cache. -/
theorem readCall_view (forger : Bool) (rq : (RoSpec C).Domain) (a : RealState C)
    (hr : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (hhit : (∃ value, visibleOf a (readInput rq) = some value) ∨
      Quiet x s pads noise (readInput rq))
    (hbase : ∀ input, readInput rq = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message) :
    realReadView <$> (readCall prims x s pads u rest forger rq).run a =
      (fun w => (readAnswer prims rq w.1, w.2, a.1.1.2)) <$>
        (((Query C →ₒ HashOutput).randomOracle (readInput rq)).run (visibleOf a)) := by
  cases forger
  · have ht : (.inr (.inr rq) : (WorldSpec C).Domain) = .inl (.inl (.inr rq)) ∨
        (.inr (.inr rq) : (WorldSpec C).Domain) = .inr (.inr rq) := Or.inr rfl
    have hv := realWorld_read_view_route prims x s pads noise (gOf s pads u) rest rq _ ht a hr hhit
    rw [cacheRead_noBase x.1 x.2.1 _ _ _ _ _
      (fun i hi => hbase i (hashCallAt_read rq _ ht i hi)), Functor.map_map] at hv
    exact hv
  · have ht : (.inl (.inl (.inr rq)) : (WorldSpec C).Domain) = .inl (.inl (.inr rq)) ∨
        (.inl (.inl (.inr rq)) : (WorldSpec C).Domain) = .inr (.inr rq) := Or.inl rfl
    have hv := realWorld_read_view_route prims x s pads noise (gOf s pads u) rest rq _ ht a hr hhit
    rw [cacheRead_noBase x.1 x.2.1 _ _ _ _ _
      (fun i hi => hbase i (hashCallAt_read rq _ ht i hi)), Functor.map_map] at hv
    exact hv

/-- The effect of a real read with no bottom base input on the real state. -/
theorem readCall_support (forger : Bool) (rq : (RoSpec C).Domain) (a : RealState C)
    (hr : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (hhit : (∃ value, visibleOf a (readInput rq) = some value) ∨
      Quiet x s pads noise (readInput rq))
    (hbase : ∀ input, readInput rq = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
    (ra : (RoSpec C).Range rq × RealState C)
    (hra : ra ∈ support ((readCall prims x s pads u rest forger rq).run a)) :
    ∃ w ∈ support (((Query C →ₒ HashOutput).randomOracle (readInput rq)).run (visibleOf a)),
      visibleOf ra.2 = w.2 ∧ ra.2.1.2 = a.1.2 ∧ ra.2.1.1.2 = a.1.1.2 ∧
      ra.2.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1 ∧ realLog a ≤ realLog ra.2 ∧
      (SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1 →
        SigningPartnerCompareProof.LogAgreement x.1 ra.2.1.1.1.1.1) := by
  have route (t : (WorldSpec C).Domain) (ht : t = .inl (.inl (.inr rq)) ∨ t = .inr (.inr rq))
      (hlog : ∀ (L : SigningHitLaneProof.LoggedState C) (w : HashOutput × HashCache C),
        SigningPartnerCompareProof.LogAgreement x.1 L →
        w ∈ support (((Query C →ₒ HashOutput).randomOracle (readInput rq)).run L.1.1) →
        ∀ n, SigningPartnerCompareProof.LogAgreement x.1 ((w.2, n), L.2.logQuery t
          (cast (by rcases ht with rfl | rfl <;> rfl) (readAnswer prims rq w.1))))
      (r : (WorldSpec C).Range t × RealState C)
      (hr' : r ∈ support ((realWorld prims x s pads u rest t).run a)) :
      ∃ w ∈ support (((Query C →ₒ HashOutput).randomOracle (readInput rq)).run (visibleOf a)),
        visibleOf r.2 = w.2 ∧ r.2.1.2 = a.1.2 ∧ r.2.1.1.2 = a.1.1.2 ∧
        r.2.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1 ∧ realLog a ≤ realLog r.2 ∧
        (SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1 →
          SigningPartnerCompareProof.LogAgreement x.1 r.2.1.1.1.1.1) := by
    have hb : ∀ i, SigningFlatProof.HashCallAt i t →
        ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message :=
      fun i hi => hbase i (hashCallAt_read rq t ht i hi)
    have hcount := (realWorld_read_fields_route prims x (gOf s pads u) rest rq t ht a r hr').2
    change r ∈ support ((ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
      (realImpl x (gOf s pads u) rest) t).run (a.1, a.2)) at hr'
    rw [rawTraceWorld_read_route prims x (gOf s pads u) rest rq t ht a.1 a.2] at hr'
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr'
    obtain ⟨z, hz, y, hy, rfl⟩ := hr'
    rw [noBase_cachedExtra x.2.1 x.1 _ _ t hb] at hy
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hy
    subst hy
    rw [realRead_ordinary x s pads noise (gOf s pads u) rest a.2 (visibleOf a) hr _ hhit,
      support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hv := randomOracle_observe (visibleOf a) _ w hw
    refine ⟨w, hw, hv, rfl, noBase_traceStepAt x.2.1 x.1 _ _ _ t _ hb, hcount,
      logCache_le_logQuery _ _ _, fun hL => ?_⟩
    change SigningPartnerCompareProof.LogAgreement x.1
      (((visibleOf a).cacheQuery (readInput rq) w.1, _), _)
    rw [hv]
    exact hlog a.1.1.1.1.1 w hL hw _
  cases forger
  · refine route (.inr (.inr rq)) (Or.inr rfl) ?_ ra hra
    intro L w hL hw n
    cases rq with
    | inl query =>
      refine SigningPartnerCompareProof.logAgreement_hash x.1 query L hL w hw _ ?_ n
      intro q'
      rw [SigningCacheLogProof.logCache_logQuery]
      rfl
    | inr input =>
      refine logAgreement_untracked x.1 _ (fun h => h _ rfl) L hL w hw _ ?_ n
      funext q'
      rw [SigningCacheLogProof.logCache_logQuery]
      simp [SigningCacheLogProof.hashCall]
  · refine route (.inl (.inl (.inr rq))) (Or.inl rfl) ?_ ra hra
    intro L w hL hw n
    cases rq with
    | inl query =>
      refine SigningPartnerCompareProof.logAgreement_hash x.1 query L hL w hw _ ?_ n
      intro q'
      rw [SigningCacheLogProof.logCache_logQuery]
      rfl
    | inr input =>
      refine logAgreement_untracked x.1 _ (fun h => h _ rfl) L hL w hw _ ?_ n
      funext q'
      rw [SigningCacheLogProof.logCache_logQuery]
      simp [SigningCacheLogProof.hashCall]

end RealRead

section Calls
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
set_option backward.isDefEq.respectTransparency false

/-- The cache relation reads only the cache, the pending answers and the virtual terms. -/
theorem cacheRelation_congr (P : PublicParameter) (seeds : C.Term → HashOutput)
    (d d' : DeferredState C) (actual : HashCache C) (hc : d'.cache = d.cache)
    (hp : d'.pending = d.pending) (hv : d'.virtual = d.virtual)
    (h : CacheRelation P seeds s d actual) : CacheRelation P seeds s d' actual := by
  refine ⟨fun query hq => ?_, fun p value hpv => h.pending p value (hp ▸ hpv)⟩
  rw [hc]
  apply h.agree query
  intro hs
  apply hq
  unfold SuspendedQuery at hs ⊢
  rw [hc, hp, hv]
  exact hs

/-- A cache that agrees on the PRF cells of a bottom randomizer has the same opening value. -/
theorem randomizer_agree (seeds : C.Term → HashOutput) (cache cache' : HashCache C) (e : KeyIndex)
    (h : ∀ T, cache' (.prf (seeds T) (.randomizer bottomLayer e)) =
      cache (.prf (seeds T) (.randomizer bottomLayer e))) :
    (SigningGuessProof.RandomizerCached seeds cache' e ↔
      SigningGuessProof.RandomizerCached seeds cache e) ∧
    SigningGuessProof.cachedRandomizer seeds cache' e =
      SigningGuessProof.cachedRandomizer seeds cache e := by
  unfold SigningGuessProof.RandomizerCached SigningGuessProof.cachedRandomizer
  exact ⟨by simp only [h], by simp only [h]⟩

/-- The compiler side of a read of `H` or of the PRG is the read of its input. -/
theorem runX_sourceRoX (rq : (RoSpec C).Domain) (src : SourceState C) (st : CompState C) :
    runX (compBackend x q s pads u rest noise) (sourceRoX prims x.1 x.2.1 rq) src st =
      (fun r => ((readAnswer prims rq r.1.1, r.1.2), r.2)) <$>
        runX (compBackend x q s pads u rest noise) (sourceHashX x.1 x.2.1 (readInput rq)) src st := by
  cases rq with
  | inl query => simp [sourceRoX, readInput, readAnswer]
  | inr input =>
    simp only [sourceRoX, runX_bind, runX_pure, readInput, readAnswer, map_eq_bind_pure_comp]
    rfl

/-- An ordinary hash read keeps the mark of the compiler. -/
theorem ordinaryHash_mark (input : Query C) (hn : ¬IsSlot x input) (st : CompState C)
    (r : HashOutput × CompState C)
    (hr : r ∈ support ((compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash input))))).run
      st)) : r.2.1.2 = st.1.2 := by
  obtain ⟨hroute, hrest⟩ := ordinary_routes x input hn
  rw [backendT_ordinaryHash capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest input hroute
    hrest st] at hr
  simp only [support_map] at hr
  obtain ⟨z, _, rfl⟩ := hr
  rfl

/-- The opening release before a read that is no slot. It keeps the relation, the mark and the
frame with no seen query. -/
theorem prefix_call (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (input : Query C) (hn : ¬IsSlot x input) (a : RealState C) (src : SourceState C)
    (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (hmark : st.1.2 = false) (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise) (ordinaryPrefix x input src st)
      src st)) :
    Stop r.2 ∨ (SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (r.1.2, r.2) ∧
      CallFrame x (fun _ => False) a a (src, st) (r.1.2, r.2) ∧ r.2.1.2 = false) := by
  have hpure (he : ordinaryPrefix x input src st = pure ()) :
      Stop r.2 ∨ (SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (r.1.2, r.2) ∧
        CallFrame x (fun _ => False) a a (src, st) (r.1.2, r.2) ∧ r.2.1.2 = false) := by
    rw [he, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact Or.inr ⟨hs, CallFrame.refl x a (src, st), hmark⟩
  cases input with
  | prf seed point =>
    cases point with
    | randomizer lay e =>
      by_cases hp : lay = bottomLayer ∧
          ReadyAfter x.2.1 (dataOf x st) src.signing e (.prf seed (.randomizer lay e))
      · obtain ⟨rfl, hready⟩ := hp
        simp only [ordinaryPrefix, hready, and_self, if_true] at hr
        by_cases hreveal : src.revealed (.opening bottomLayer e) = none
        · have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
          have hafter : VisibleAfter x (gOf s pads u) e (.prf seed (.randomizer bottomLayer e))
              (visibleOf a) (visibleOf a) := Or.inl ⟨hn, rfl⟩
          have hrelease := releaseOpening_sync x hkeys q s pads (tauOf s pads) (gOf s pads u) noise
            rest e seed (withCarried a cCore) src st (visibleOf a) hs.1.1 hs.1.2 hmark hreveal hready
            hafter r hr
          rcases hrelease with hstop | ⟨hnext, hlocal, _, hcount, _⟩
          · exact Or.inl hstop
          have hrow := readyAfter_covers_visible x hkeys s pads noise (gOf s pads u) rest a.2
            (visibleOf a) (visibleOf a) (dataOf x st) src.signing e _ hs.1.1.realPrivate hs.1.2
            hs.1.1.virtualSeen hready hafter
          have hpost := releaseOpening_post x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest
            e _ src st (visibleOf a) (visibleOf a) hmark hreveal hs.1.1.reveal hs.1.2
            hs.1.1.releasedPending hs.1.1.pendingValid hs.1.1.allocated hs.1.1.restFree
            hs.1.1.share hs.1.1.doneCached hs.1.1.bad hafter hrow r hr
          have hsrc := hpost.source
          have hrev : r.1.2.revealed = Function.update src.revealed (.opening bottomLayer e)
              (some (s (.opening bottomLayer e))) := congrArg SourceState.revealed hsrc
          refine Or.inr ⟨⟨hnext, hs.2.trans hcount.symm⟩, ?_, ?_⟩
          · refine ⟨rfl, le_rfl, fun _ h => Or.inl h, le_rfl, id, rfl, hlocal.signing,
              hlocal.trees, hlocal.exposed, ?_, ?_, ?_, ?_, ?_⟩
            · change r.1.2.candidates = src.candidates
              rw [hsrc]
            · intro k hk
              change r.1.2.revealed k = src.revealed k
              rw [hrev]
              apply Function.update_of_ne
              rintro rfl
              exact hk hreveal
            · intro k hk hk'
              by_cases he : k = .opening bottomLayer e
              · exact ⟨e, he, hready.1⟩
              · change r.1.2.revealed k ≠ none at hk'
                rw [hrev, Function.update_of_ne he] at hk'
                exact absurd hk hk'
            · intro p hp
              change (dataOf x r.2).pending p ≠ none
              rw [hlocal.pending]
              exact hp
            · intro T p hp
              change (T, p) ∈ (dataOf x r.2).virtual
              rw [hlocal.virtual]
              exact hp
          · rw [hpost.backend]
            exact hmark
        · rw [runX_releaseOpening_revealed _ x.1 x.2.1 e src st hreveal,
            mem_support_pure_iff] at hr
          subst r
          exact Or.inr ⟨hs, CallFrame.refl x a (src, st), hmark⟩
      · exact hpure (if_neg hp)
    | _ => exact hpure rfl
  | _ => exact hpure rfl

set_option maxHeartbeats 1600000 in
/-- The read itself after the release, when the input is no suspended point and the real read is
a visible hit or quiet. -/
theorem read_call (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (forger : Bool)
    (cCore : Carried C) (rq : (RoSpec C).Domain) (hslot : ¬IsSlot x (readInput rq))
    (hbase : ∀ input, readInput rq = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (hhit : (∃ value, visibleOf a (readInput rq) = some value) ∨
      Quiet x s pads noise (readInput rq))
    (hns : ¬SuspendedQuery x.1 x.2.1 s (dataOf x st) (readInput rq)) :
    RelTriple ((readCall prims x s pads u rest forger rq).run a)
      ((compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash (readInput rq)))))).run st)
      (fun ra r => ra.1 = readAnswer prims rq r.1 ∧
        SyncCore x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) (src, r.2) ∧
        CallFrame x (fun query => query = readInput rq) a ra.2 (src, st) (src, r.2) ∧
        r.2.1.2 = st.1.2) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  have hi := TprfSecurityProof.slotInput_injective hinj (not_not.mp (not_or.mp hkeys).2)
  have hsf := hs.1.1
  have hcall : ∀ i, SigningFlatProof.HashCallAt i (.inr (.inr (.inl (readInput rq)))) →
      ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message := by
    intro i hi'
    rcases hi' with h | h
    · cases h
    · exact hbase i (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h)))
  have hv := readCall_view prims x s pads u rest noise forger rq a hsf.realPrivate hhit hbase
  have hc := compilerRead_view x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest
    (readInput rq) hslot st
  rw [cacheRead_noBase x.1 x.2.1 _ _ _ _ _ hcall] at hc
  have core : RelTriple (realReadView <$> (readCall prims x s pads u rest forger rq).run a)
      (compilerReadView x <$>
        (compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash (readInput rq)))))).run st)
      (fun va vb => va.1 = readAnswer prims rq vb.1 ∧
        CacheRelation x.1 x.2.1 s { dataOf x st with cache := vb.2.1 } va.2.1 ∧
        va.2.2 = vb.2.2) := by
    rw [hv, hc]
    apply relTriple_map
    refine relTriple_post_mono
      (cacheQuery_rel x.1 x.2.1 s (dataOf x st) (visibleOf a) hs.1.2 _ hns) ?_
    rintro w w' ⟨he, hrel⟩
    exact ⟨by rw [he], hrel, hsf.trace⟩
  refine relTriple_post_mono (relTriple_of_projections _ _ _ _ core) ?_
  rintro ra r ⟨⟨hval, hrel, htrace⟩, hra, hr⟩
  obtain ⟨w, hw, hvis, hcarried, hrealTrace, hcount, hlog, hlogA⟩ :=
    readCall_support prims x s pads u rest noise forger rq a hsf.realPrivate hhit hbase ra hra
  obtain ⟨hshare, hreveal, hbound, hcnt, hpend, hvirt, hgrow⟩ :=
    compilerRead_fields x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest (readInput rq)
      hslot st r hr
  have hframe := backendT_frame capTag x hi q s pads (tauOf s pads) (gOf s pads u) noise rest
    (.inl (.inl (.inl (.hash (readInput rq))))) (by exact trivial) st ⟨hsf.restAgree, hsf.restFree, hsf.pendingValid⟩ r hr
  have hpriv : RealPrivate x s pads noise (gOf s pads u) rest ra.2.2 (visibleOf ra.2) := by
    cases forger
    · exact realWorld_preserves prims (.inr (.inr rq)) a hsf.realPrivate ra hra
    · exact realWorld_preserves prims (.inl (.inl (.inr rq))) a hsf.realPrivate ra hra
  obtain ⟨hle, -, hother⟩ := randomOracle_support _ _ w hw
  have hcache : CacheRelation x.1 x.2.1 s (dataOf x r.2) (visibleOf ra.2) :=
    cacheRelation_congr s x.1 x.2.1 { dataOf x st with cache := (dataOf x r.2).cache } (dataOf x r.2)
      _ rfl hpend hvirt hrel
  have hagree (e : KeyIndex) := randomizer_agree x.2.1 (visibleOf a) (visibleOf ra.2) e (by
    intro T
    rw [hvis]
    apply hother
    intro he
    exact hslot ⟨.inl (T, (⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩ : CPoint)),
      he⟩)
  have hgrowV : visibleOf a ≤ visibleOf ra.2 := hvis ▸ hle
  refine ⟨hval, ⟨⟨?_, hcache⟩, ?_⟩, ?_, ordinaryHash_mark x q s pads u rest noise _ hslot st r hr⟩
  · exact
      { corrupt := hsf.corrupt, bound := hsf.bound, released := hsf.released
        exposed := hsf.exposed, candidates := hsf.candidates, flag := hsf.flag
        reveal := ⟨hsf.reveal.1.trans hreveal.symm, hsf.reveal.2⟩
        releasedPending := fun p value hp hk => hgrow (hsf.releasedPending p value (hpend ▸ hp) hk)
        opening := ⟨fun e he =>
            (hagree e).2.trans (hsf.opening.actualValue e ((hagree e).1.mp he)),
          fun e he T => by
            obtain ⟨value, hv⟩ := hsf.opening.released e he T
            exact ⟨value, hgrow hv⟩⟩
        pendingValid := hframe.2.2
        allocated := fun p hp => hsf.allocated p (hpend ▸ hp)
        virtualSeen := fun T p hp => by
          obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hsf.virtualSeen T p (hvirt ▸ hp))
          change visibleOf ra.2 _ ≠ none
          rw [hgrowV hv]
          exact Option.some_ne_none _
        compilerBound := hbound.trans hsf.compilerBound
        trace := htrace
        bad := hshare ▸ hsf.bad
        share := hshare ▸ hsf.share
        restAgree := hframe.1
        restFree := hframe.2.1
        realPrivate := hpriv
        frontier := fun edge hp => hsf.frontier edge (hpend ▸ hp)
        candidatesPaid := hsf.candidatesPaid
        doneCached := hshare ▸ hsf.doneCached }
  · change ra.2.1.1.1.1.1.1.2 = r.2.1.1.1.2
    rw [hcount, hcnt]
    exact congrArg (· + 1) hs.2
  · refine ⟨hcarried, ?_, ?_, hlog, hlogA, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun _ h h' => (h' h).elim, ?_, ?_⟩
    · exact hgrowV
    · intro query hq
      by_cases he : query = readInput rq
      · exact Or.inr he
      · left
        rw [hvis, hother query he] at hq
        exact hq
    · exact hrealTrace
    · intro p hp
      change (dataOf x r.2).pending p ≠ none
      rw [hpend]
      exact hp
    · intro T p hp
      change (T, p) ∈ (dataOf x r.2).virtual
      rw [hvirt]
      exact hp

/-- A map on the right of a coupling moves into the post. -/
theorem relTriple_map_right {α β γ : Type} {oa : ProbComp α} {ob : ProbComp β} (h : β → γ)
    {R : α → γ → Prop} (hr : RelTriple oa ob (fun a b => R a (h b))) :
    RelTriple oa (h <$> ob) R := by
  have hm := relTriple_map (f := id) (g := h) (R := R) hr
  rwa [id_map] at hm

/-- A real read counts once. -/
theorem readCall_count (forger : Bool) (rq : (RoSpec C).Domain) (a : RealState C)
    (ra : (RoSpec C).Range rq × RealState C)
    (hra : ra ∈ support ((readCall prims x s pads u rest forger rq).run a)) :
    ra.2.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1 := by
  cases forger
  · exact (realWorld_read_fields_route prims x (gOf s pads u) rest rq _ (Or.inr rfl) a ra hra).2
  · exact (realWorld_read_fields_route prims x (gOf s pads u) rest rq _ (Or.inl rfl) a ra hra).2

set_option maxHeartbeats 1600000 in
/-- A read that is no slot and no bottom base input. Both sides return the same answer. A hash
input that carries the secret of an unrevealed key stops one side. -/
theorem ordinaryRead_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (forger : Bool)
    (cCore : Carried C) (rq : (RoSpec C).Domain)
    (hslot : ¬IsSlot x (SigningCompilerSyncRealRead.readInput rq))
    (hbase : ∀ input, SigningCompilerSyncRealRead.readInput rq = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false) :
    RelTriple ((readCall prims x s pads u rest forger rq).run a)
      (runX (compBackend x q s pads u rest noise) (sourceRoX prims x.1 x.2.1 rq) src st)
      (fun ra rb => CallPost x q s pads u rest noise cCore
        (fun query => query = SigningCompilerSyncRealRead.readInput rq) a src st
        (fun va vb => va = vb ∧
          ∀ input, SigningCompilerSyncRealRead.readInput rq = .hash input → rb.1.2 = src ∧
            ∀ k, hiddenCandidate x.1 input = some (k, s k) → src.revealed k ≠ none) ra rb) := by
  have hsf := hs.1.1
  have hpre : runX (compBackend x q s pads u rest noise) (sourceHashX x.1 x.2.1 (readInput rq))
      src st = runX (compBackend x q s pads u rest noise) (ordinaryPrefix x (readInput rq) src st)
        src st >>= fun p => (fun r => ((r.1, p.1.2), r.2)) <$>
          (compBackend x q s pads u rest noise (.inl (.inl (.inl (.hash (readInput rq)))))).run p.2 :=
    runX_sourceHashX capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest (readInput rq) src st
      hsf.restFree
  rw [runX_sourceRoX prims x q s pads u rest noise rq src st, hpre]
  by_cases hh : ∃ i, readInput rq = .hash i
  · obtain ⟨i, hi⟩ := hh
    have hpure : ordinaryPrefix x (readInput rq) src st = pure () := by
      rw [hi]
      rfl
    rw [hpure, runX_pure, pure_bind, Functor.map_map]
    by_cases hhit : ∃ k, hiddenCandidate x.1 i = some (k, s k) ∧ src.revealed k = none
    · obtain ⟨k, hk, hrk⟩ := hhit
      refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
      rintro ra rb ⟨-, hra, hrb⟩
      simp only [support_map, Set.mem_image] at hrb
      obtain ⟨r, hr, rfl⟩ := hrb
      by_cases hcap : st.1.1.1.2 < q
      · rw [hi] at hr
        exact Or.inr (Or.inl (Or.inr (capHit_stuck x q s pads (tauOf s pads) (gOf s pads u) noise
          rest i k src st hk hsf.reveal hrk hcap hsf.bad r hr)))
      · left
        have hcount := readCall_count prims x s pads u rest forger rq a ra hra
        have hcore : a.1.1.1.1.1.1.2 = st.1.1.1.2 := hs.2
        right
        simp only [RealStop, not_or, not_lt] at ha
        omega
    · have hno : ∀ k, hiddenCandidate x.1 i = some (k, s k) → src.revealed k ≠ none :=
        fun k hk hrk => hhit ⟨k, hk, hrk⟩
      have hd := hash_dichotomy x s pads noise src (dataOf x st) (visibleOf a) hs.1.2
        hsf.releasedPending hsf.frontier i
      rcases hd with ⟨k, hk, hrk⟩ | ⟨hns, hread⟩
      · exact (hno k hk hrk).elim
      rw [← hi] at hns hread
      apply relTriple_map_right
      refine relTriple_post_mono (read_call prims x q s pads u rest noise hkeys forger cCore rq
        hslot hbase a src st hs hread hns) ?_
      rintro ra r ⟨hval, hsync, hframe, hmk⟩
      refine Or.inr (Or.inr ⟨⟨hval, fun input hin => ⟨rfl, ?_⟩⟩, hsync, hframe, hmk.trans hmark⟩)
      rw [hi] at hin
      cases hin
      exact hno
  · have hh' : ∀ i, readInput rq ≠ .hash i := fun i he => hh ⟨i, he⟩
    have hl : (readCall prims x s pads u rest forger rq).run a =
        (pure () : ProbComp Unit) >>= fun _ => (readCall prims x s pads u rest forger rq).run a :=
      (pure_bind _ _).symm
    rw [hl, map_bind]
    refine relTriple_bind (R := fun _ p => p ∈ support (runX (compBackend x q s pads u rest noise)
      (ordinaryPrefix x (readInput rq) src st) src st))
      (relTriple_of_support_right (fun p hp _ => hp)) ?_
    intro _ p hp
    rw [Functor.map_map]
    rcases prefix_call x q s pads u rest noise hkeys cCore (readInput rq) hslot a src st hs hmark p
      hp with hstop | ⟨hs1, hframe1, hmark1⟩
    · apply relTriple_of_support_right
      intro rb hrb _
      simp only [support_map, Set.mem_image] at hrb
      obtain ⟨r, hr, rfl⟩ := hrb
      exact Or.inr (Or.inl (backendT_stop x.1 x.2.1 x.2.2 q s pads _ _ noise rest _ p.2 hstop r hr))
    apply relTriple_map_right
    refine relTriple_post_mono (read_call prims x q s pads u rest noise hkeys forger cCore rq
      hslot hbase a p.1.2 p.2 hs1 (Or.inr (ordinary_nonhash_quiet x s pads noise _ hslot hh'))
      (ordinary_not_suspended x s (dataOf x p.2) _ hslot hh')) ?_
    rintro ra r ⟨hval, hsync, hframe, hmk⟩
    refine Or.inr (Or.inr ⟨⟨hval, fun input hin => (hh' input hin).elim⟩, hsync, ?_,
      hmk.trans hmark1⟩)
    exact (CallFrame.trans x _ _ a a ra.2 (src, st) (p.1.2, p.2) (p.1.2, r.2) hframe1 hframe).weaken
      x _ _ _ _ _ _ (fun query hq => hq.elim False.elim id)

end Calls

end ThresholdLeanXmssSecurity.SigningCompilerO1Reads

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.noBase_cachedExtra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.noBase_cachedExtra

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.noBase_traceStepAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.noBase_traceStepAt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.cacheRead_noBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.cacheRead_noBase

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.hashCallAt_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.hashCallAt_read

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.logAgreement_untracked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.logAgreement_untracked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.logCache_le_logQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.logCache_le_logQuery

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.readCall_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.readCall_view

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.readCall_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.readCall_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.cacheRelation_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.cacheRelation_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.randomizer_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.randomizer_agree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.runX_sourceRoX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.runX_sourceRoX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.ordinaryHash_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.ordinaryHash_mark

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.prefix_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.prefix_call

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.read_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.read_call

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.relTriple_map_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.relTriple_map_right

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.readCall_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.readCall_count

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Reads.ordinaryRead_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Reads.ordinaryRead_sync
