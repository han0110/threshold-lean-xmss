import ThresholdLeanXmssSecurity.Proof.SigningTopRowsCap
import ThresholdLeanXmssSecurity.Proof.SigningLane2Flat
import ThresholdLeanXmssSecurity.Proof.SigningLinkPaid
import XmssSecurity.Proof.Deterministic.Replay
import XmssSecurity.Proof.ConsistentQueryBound

/-!
# Local laws for the shared signing lane

A message-digest query cannot be a canonical randomizer-base query. Its eager
grind is empty, its signing trace is unchanged, and its cache projection is the
leanVM world step. These statements hold for every state of the flat lane run.

The randomizer-base case is separate: a fresh base appends a signing entry;
a repeated base whose trials are cached preserves the message cache. A cached
base with no signing entry is the `StaleBase` case. The cached-trials invariant
alone does not exclude that case, as `staleState_properties` shows.
-/

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningLaneHybridProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof
  SigningLane2BridgeProof SigningLane2FlatProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The cache contains the complete deterministic grind of every traced key
with its bound message. This is the replay form of `BaseTrialsCached`. -/
def BaseTrialsResolved (P : PublicParameter) (ρ : KeyIndex → Digest) (s : LaneState C) : Prop :=
  ∀ e message, s.2.1.bound e = some message → e ∈ s.1.2.leafIndices →
    ∃ u, s.1.1.1.1.1.1 (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) = some u ∧
      DeterministicSigning.Resolves s.1.1.1.1.1.1 (baseGrind P e message u) ()

/-- The support-wise cached-trials condition is exactly a deterministic replay
certificate, and therefore persists under cache extension. -/
theorem baseTrialsCached_iff_resolved (P : PublicParameter) (ρ : KeyIndex → Digest) (s : LaneState C) :
    BaseTrialsCached P ρ s ↔ BaseTrialsResolved P ρ s := by
  constructor
  · intro h e message hb he
    obtain ⟨u, hu, hkeep⟩ := h e message hb he
    obtain ⟨z, hz⟩ := XmssSecurity.probComp_support_nonempty
      ((simulateQ (Query C →ₒ HashOutput).randomOracle (baseGrind P e message u)).run s.1.1.1.1.1.1)
    have hres := DeterministicSigning.resolves_of_run _ _ z hz
    rw [hkeep z hz] at hres
    exact ⟨u, hu, hres⟩
  · intro h e message hb he
    obtain ⟨u, hu, hres⟩ := h e message hb he
    refine ⟨u, hu, fun z hz => ?_⟩
    rw [hres.run_eq_pure, mem_support_pure_iff] at hz
    exact congrArg Prod.snd hz

/-- Removing the two monitors from an eager grind leaves the same lazy-oracle
execution, including its final cache. -/
theorem splitOracle_support_forget
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (oa : OracleComp (Query C →ₒ HashOutput) Unit)
    (s : (HashCache C × SigningPartnerBoundProof.Monitor) × Bool)
    (z : Unit × ((HashCache C × SigningPartnerBoundProof.Monitor) × Bool))
    (hz : z ∈ support ((simulateQ (splitOracle keyOf) oa).run s)) :
    (z.1, z.2.1.1) ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle oa).run s.1.1) := by
  rw [← monitoredOracle_run_forget keyOf oa s.1.1 s.1.2,
    ← splitOracle_run_forget keyOf oa s.1 s.2, Functor.map_map, support_map]
  exact ⟨z, hz, rfl⟩

/-- The two copies of the hash oracle preserve the input address. -/
theorem hashCallAt_injective {a b : HashInput} {t : (WorldSpec C).Domain}
    (ha : HashCallAt a t) (hb : HashCallAt b t) : a = b := by
  rcases ha with rfl | rfl <;>
    rcases hb with hb | hb <;> simp_all

/-- A canonical randomizer-base query is outside the message-digest domain. -/
theorem not_baseCall_of_isMsg (P : PublicParameter) (ρ : KeyIndex → Digest)
    (st : TsigState C) {input : HashInput} {t : (WorldSpec C).Domain}
    (hmsg : IsMsg input) (hcall : HashCallAt input t) :
    ¬∃ e, BaseCall P e (ρ e) st t := by
  rintro ⟨e, address, haddress, hbase⟩
  have heq := hashCallAt_injective hcall hbase
  subst address
  cases hb : st.bound e with
  | none => simp [baseInput, hb] at haddress
  | some message =>
    simp only [baseInput, hb] at haddress
    have haddress : randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message) = input :=
      Option.some.inj haddress
    exact not_isMsg_randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message)
      (haddress.symm ▸ hmsg)

/-- At a non-base query, the flat lane's cache and trace are those of the
underlying counted world call. -/
theorem laneWorld_view_of_not_base
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain)
    (s : LaneState C) (hbase : ¬∃ e, BaseCall P e (ρ e) s.2.1 t) :
    (fun z : (WorldSpec C).Range t × LaneState C => laneView z.2) <$>
        (laneWorld prims keyOf P ρ t).run s =
      (fun w => (keptView IsMsg w.2.1, s.1.2)) <$>
        (SigningCacheProof.countImpl prims t).run s.1.1.1.1.1 := by
  simp only [laneWorld, StateT.run_mk, Functor.map_map, splitWorld,
    map_bind, grindExtra, hbase, dite_false, simulateQ_pure, StateT.run_pure,
    map_pure, bind_pure_comp]
  simp only [traceStep, hbase, dite_false, laneView, carry,
    SigningCostProof.loggedImpl, StateT.run_mk, Functor.map_map]
  rfl

/-- The exact message-call law of the flat lane, including its count. -/
theorem msgCallLaw (P : PublicParameter) (ρ : KeyIndex → Digest) :
    MsgCallLaw prims (C := C) P ρ := by
  intro keyOf publicKey input t hmsg hcall s k
  have hbase := not_baseCall_of_isMsg P ρ s.2.1 hmsg hcall
  have hview := laneWorld_view_of_not_base prims keyOf P ρ t s hbase
  have h := congrArg (fun m => (fun v => ((v, k + 1) : XmssSecurity.Ghost.State)) <$> m) hview
  simp only [Functor.map_map] at h
  rw [h]
  have hc := countImpl_hashCallAt prims hcall s.1.1.1.1.1
  have hc' := congrArg (fun m =>
    (fun v => (((keptView IsMsg v.1, s.1.2), k + 1) : XmssSecurity.Ghost.State)) <$> m) hc
  simp only [Functor.map_map] at hc'
  rw [hc']
  have hlaw := worldCall_stateLaw_isMsg prims publicKey (laneKey P) hmsg
    s.1.1.1.1.1.1 s.1.2 k
  simpa only [hashAnswer, if_neg (fun h => not_isMsg_of_mpc h hmsg), laneView] using hlaw

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
/-- Each world call preserves the complete grind certificate of every traced
key. A newly appended entry is certified by that call's actual eager grind. -/
theorem laneWorld_baseTrialsResolved
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain)
    (s : LaneState C) (hinv : BaseTrialsResolved P ρ s)
    (z : (WorldSpec C).Range t × LaneState C)
    (hz : z ∈ support ((laneWorld prims keyOf P ρ t).run s)) :
    BaseTrialsResolved P ρ z.2 := by
  simp only [laneWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  simp only [splitWorld, StateT.run_mk, support_bind, Set.mem_iUnion] at hr
  obtain ⟨w, hw, hr⟩ := hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  generalize hoa : grindExtra P ρ (s.1.1.1.1, s.2) t w.2 = oa at hv
  have hv' := splitOracle_support_forget (C := C) keyOf
    oa
    ((w.2.1.1.1, queryEntryStep keyOf s.1.1.1.2 (SigningPartnerBoundProof.hashEntry ⟨t, w.1⟩)),
      s.1.1.2) v hv
  have hgrow₁ := DeterministicSigning.cache_le_of_run oa _ _ hv'
  rw [← hoa] at hv'
  obtain ⟨step, hstep, _, hcache, hstate⟩ :=
    flatWorld_support prims t (s.1.1.1.1, s.2) w hw
  have hgrow₀ : s.1.1.1.1.1.1 ≤ w.2.1.1.1 := by
    rw [hcache]
    exact SigningCacheProof.countImpl_grows prims t s.1.1.1.1.1 step hstep
  have hgrow := hgrow₀.trans hgrow₁
  intro e message hb he
  change w.2.2.1.bound e = some message at hb
  rw [hstate] at hb
  have hold (heold : e ∈ s.1.2.leafIndices) :
      ∃ u, v.2.1.1 (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) = some u ∧
        DeterministicSigning.Resolves v.2.1.1 (baseGrind P e message u) () := by
    obtain ⟨u, hu, hres⟩ := hinv e message hb heold
    exact ⟨u, hgrow hu, hres.mono hgrow⟩
  change ∃ u, v.2.1.1 (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) = some u ∧
    DeterministicSigning.Resolves v.2.1.1 (baseGrind P e message u) ()
  unfold traceStep at he
  split at he
  · rename_i hbase
    cases hm : s.2.1.bound hbase.choose with
    | none =>
      simp only [hm] at he
      exact hold he
    | some m =>
      simp only [hm] at he
      split at he
      · rename_i hfresh
        rw [XmssSecurity.SigningCacheTrace.leafIndices_append] at he
        have he := List.mem_append.mp he
        rcases he with he | he
        · exact hold he
        · have he : e = hbase.choose := by
            simpa only [XmssSecurity.SigningCacheTrace.leafIndices,
              List.map_cons, List.map_nil, List.mem_singleton] using he
          have hb' : s.2.1.bound hbase.choose = some message := he ▸ hb
          obtain ⟨u, hu⟩ := countImpl_hash_cached prims _ t
            (hashCallAt_of_baseCall hbase.choose_spec hb') _ step hstep
          have hu' : w.2.1.1.1 (.hash
              (randomizerInput P bottomLayer hbase.choose (ρ hbase.choose) (bytesLE 32 message))) = some u := by
            rw [hcache]
            exact hu
          rw [grindExtra_base P ρ t (s.1.1.1.1, s.2) hbase hb' w.2 u hu'] at hv'
          have hres := DeterministicSigning.resolves_of_run _ _ _ hv'
          exact he.symm ▸ ⟨u, hgrow₁ hu', hres⟩
      · exact hold he
  · exact hold he

/-- The cached-trials invariant of the flat lane holds at every world call. -/
theorem baseTrialsCachedInvariant (P : PublicParameter) (ρ : KeyIndex → Digest) :
    BaseTrialsCachedInvariant prims (C := C) P ρ := by
  intro keyOf t s _ hs z hz
  exact (baseTrialsCached_iff_resolved P ρ z.2).mpr
    (laneWorld_baseTrialsResolved prims keyOf P ρ t s
      ((baseTrialsCached_iff_resolved P ρ s).mp hs) z hz)

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- At a repeated base of a traced key, the entire eager grind is a replay.
The message cache and the signing trace both stay unchanged. -/
theorem laneWorld_traced_base_view
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain)
    (s : LaneState C) (hinv : BaseTrialsCached P ρ s)
    (hbase : ∃ e, BaseCall P e (ρ e) s.2.1 t) (message : Message)
    (hb : s.2.1.bound hbase.choose = some message) (he : hbase.choose ∈ s.1.2.leafIndices)
    (z : (WorldSpec C).Range t × LaneState C)
    (hz : z ∈ support ((laneWorld prims keyOf P ρ t).run s)) : laneView z.2 = laneView s := by
  obtain ⟨u, hu, hres⟩ := (baseTrialsCached_iff_resolved P ρ s).mp hinv hbase.choose message hb he
  simp only [laneWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  simp only [splitWorld, StateT.run_mk, support_bind, Set.mem_iUnion] at hr
  obtain ⟨w, hw, hr⟩ := hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  generalize hoa : grindExtra P ρ (s.1.1.1.1, s.2) t w.2 = oa at hv
  have hv' := splitOracle_support_forget (C := C) keyOf oa
    ((w.2.1.1.1, queryEntryStep keyOf s.1.1.1.2 (SigningPartnerBoundProof.hashEntry ⟨t, w.1⟩)),
      s.1.1.2) v hv
  obtain ⟨step, hstep, _, hcache, _⟩ := flatWorld_support prims t (s.1.1.1.1, s.2) w hw
  have hc : w.2.1.1.1 = s.1.1.1.1.1.1 := by
    rw [hcache]
    exact countImpl_hash_hit prims _ t (hashCallAt_of_baseCall hbase.choose_spec hb)
      s.1.1.1.1.1 u hu step hstep
  have hu' : w.2.1.1.1 (.hash
      (randomizerInput P bottomLayer hbase.choose (ρ hbase.choose) (bytesLE 32 message))) = some u := by
    rw [hc]
    exact hu
  rw [← hoa, grindExtra_base P ρ t (s.1.1.1.1, s.2) hbase hb w.2 u hu'] at hv'
  change (v.1, v.2.1.1) ∈ support
    ((simulateQ (Query C →ₒ HashOutput).randomOracle (baseGrind P hbase.choose message u)).run w.2.1.1.1) at hv'
  rw [hc, hres.run_eq_pure, mem_support_pure_iff] at hv'
  have hvCache : v.2.1.1 = s.1.1.1.1.1.1 := congrArg Prod.snd hv'
  apply Prod.ext
  · exact congrArg (keptView IsMsg) hvCache
  · dsimp only [laneView]
    rw [traceStep, dif_pos hbase]
    simp only [hb]
    have hnot : SplitState.cache (s.1.1, s.2) (.hash
        (randomizerInput P bottomLayer hbase.choose (ρ hbase.choose) (bytesLE 32 message))) ≠ none := by
      exact fun h => Option.some_ne_none u (hu.symm.trans h)
    exact if_neg hnot

set_option backward.isDefEq.respectTransparency false in
/-- A fresh base cannot append a key already in the trace: the replay
invariant gives a cached randomizer input for every such key. -/
theorem traceStep_nodup (P : PublicParameter) (ρ : KeyIndex → Digest)
    (s : LaneState C) (hinv : BaseTrialsCached P ρ s) (hnodup : s.1.2.leafIndices.Nodup)
    (t : (WorldSpec C).Domain) (p' : SplitState C) :
    (traceStep P ρ (s.1.1, s.2) t p' s.1.2).leafIndices.Nodup := by
  unfold traceStep
  split
  · rename_i hbase
    cases hm : s.2.1.bound hbase.choose with
    | none => exact hnodup
    | some message =>
      simp only
      split
      · rename_i hfresh
        have hnot : hbase.choose ∉ s.1.2.leafIndices := by
          intro he
          obtain ⟨u, hu, _⟩ := hinv hbase.choose message hm he
          have hfalse : (some u : Option HashOutput) = none := hu.symm.trans hfresh
          cases hfalse
        rw [XmssSecurity.SigningCacheTrace.leafIndices_append]
        simp only [XmssSecurity.SigningCacheTrace.leafIndices, List.map_cons, List.map_nil,
          List.nodup_append, List.nodup_singleton, List.mem_singleton, ne_eq, true_and]
        exact ⟨hnodup, fun a ha b hb hab => hnot ((hab.trans hb) ▸ ha)⟩
      · exact hnodup
  · exact hnodup

/-- At a base query, excluding `StaleBase` leaves exactly the fresh-base case
and a key already represented in the signing trace. -/
theorem fresh_or_traced_of_not_stale (P : PublicParameter) (ρ : KeyIndex → Digest)
    (s : LaneState C) (hstale : ¬StaleBase P ρ s) (e : KeyIndex) (message : Message)
    (hb : s.2.1.bound e = some message) :
    s.1.1.1.1.1.1 (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) = none ∨
      e ∈ s.1.2.leafIndices := by
  by_cases hfresh : s.1.1.1.1.1.1
      (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) = none
  · exact Or.inl hfresh
  · exact Or.inr (by_contra fun he => hstale ⟨e, message, hb, hfresh, he⟩)

/-- A bound key with its base cached and no signing trace. This state tests the
logical content of the cached-trials invariant; it asserts no reachability. -/
def staleState (P : PublicParameter) (ρ : KeyIndex → Digest) (e : KeyIndex)
    (message : Message) : LaneState C :=
  let cache : HashCache C := (∅ : HashCache C).cacheQuery
    (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) 0
  let logged : SigningHitLaneProof.LoggedState C := ((cache, 0), [])
  let state : TsigState C :=
    { SigningCoreProof.tsigInit with bound := Function.update (fun _ => none) e (some message) }
  ((((logged, SigningPartnerBoundProof.Monitor.empty), false), []), (state, false))

/-- Cached trials and a trace without repeated keys can coexist with a stale
base. Excluding stale bases requires information beyond these two invariants. -/
theorem staleState_properties (P : PublicParameter) (ρ : KeyIndex → Digest)
    (e : KeyIndex) (message : Message) :
    BaseTrialsCached P ρ (staleState (C := C) P ρ e message) ∧
      (staleState (C := C) P ρ e message).1.2.leafIndices.Nodup ∧
      StaleBase P ρ (staleState (C := C) P ρ e message) := by
  refine ⟨?_, ?_, e, message, ?_, ?_, ?_⟩
  · intro e' message' hb he
    cases he
  · simp [staleState, XmssSecurity.SigningCacheTrace.leafIndices]
  · simp [staleState]
  · simp [staleState]
  · intro he
    cases he

end ThresholdLeanXmssSecurity.SigningLaneHybridProof

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridProof.msgCallLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneHybridProof.msgCallLaw

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridProof.baseTrialsCachedInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneHybridProof.baseTrialsCachedInvariant

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridProof.laneWorld_traced_base_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneHybridProof.laneWorld_traced_base_view

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridProof.traceStep_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneHybridProof.traceStep_nodup

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridProof.staleState_properties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneHybridProof.staleState_properties
