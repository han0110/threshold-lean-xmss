import ThresholdLeanXmssSecurity.Proof.SigningLaneUnion
import ThresholdLeanXmssSecurity.Proof.SigningReleasedAlign
import XmssSecurity.Proof.CachedSelectionBound

/-!
# Cached signing selections in the actual leanVM trace

The actual trace has distinct leaf indices and retains each canonical signing run.
At the first cached-selection flag, its key has a fresh entry, an existing entry
with the same selected input, or a stale base. The selected input is in the entry’s
initial cache; its partner yields leanVM’s pre-signing or post-signing ghost event.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section

namespace ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof

open SigningFlatProof SigningFlatEagerProof SigningJointEagerProof SigningOneRunProof
  SigningPartnerBoundProof SigningLaneUnionProof

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

variable {C : Committee}

/-- Each trace entry retains its bound message, fixed PRF terms and cached base. -/
def EntryBases (seeds : C.Term → HashOutput) (P : PublicParameter) (cache : HashCache C)
    (state : TsigState C) (trace : XmssSecurity.SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, state.bound entry.request.leafIndex = some entry.request.message ∧
    SigningGuessProof.RandomizerCached seeds cache entry.request.leafIndex ∧
    ∃ answer, cache (.hash (randomizerInput P bottomLayer entry.request.leafIndex
      (SigningGuessProof.cachedRandomizer seeds cache entry.request.leafIndex)
      (bytesLE 32 entry.request.message))) = some answer

/-- The same entry provenance holds after cache extension and compatible message binding. -/
theorem EntryBases.mono {seeds : C.Term → HashOutput} {P : PublicParameter}
    {cache cache' : HashCache C} {state state' : TsigState C} {trace : XmssSecurity.SigningCacheTrace}
    (h : EntryBases seeds P cache state trace) (hc : cache ≤ cache')
    (hs : SigningGuessProof.BoundExtends state state') : EntryBases seeds P cache' state' trace := by
  intro entry he
  obtain ⟨hb, hprf, answer, ha⟩ := h entry he
  refine ⟨hs _ _ hb, SigningR1FixedProof.randomizerCached_mono hc hprf, answer, ?_⟩
  rw [← SigningGuessProof.cachedRandomizer_stable seeds cache cache' _ hc hprf]
  exact hc ha

/-- A fresh canonical base belongs to no previous trace entry. -/
theorem fresh_base_not_mem (seeds : C.Term → HashOutput) (P : PublicParameter)
    (cache : HashCache C) (state : TsigState C) (trace : XmssSecurity.SigningCacheTrace)
    (h : EntryBases seeds P cache state trace) (e : KeyIndex) (message : Message)
    (hb : state.bound e = some message)
    (hf : cache (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds cache e) (bytesLE 32 message))) = none) :
    e ∉ trace.leafIndices := by
  intro he
  obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp he
  obtain ⟨hbound, _, answer, hanswer⟩ := h entry hentry
  change entry.request.leafIndex = e at hkey
  rw [hkey, hb] at hbound
  have hm : entry.request.message = message := (Option.some.inj hbound).symm
  rw [hkey, hm, hf] at hanswer
  cases hanswer

/-- The actual trace step appends each leaf index at most once. -/
theorem traceStepAt_bases (seeds : C.Term → HashOutput) (P : PublicParameter)
    (cache cache' : HashCache C) (state : TsigState C) (t : (WorldSpec C).Domain)
    (aux : XmssSecurity.SigningCacheTrace × Bool) (hc : cache ≤ cache')
    (hcall : ∀ input, HashCallAt input t → ∃ answer, cache' (.hash input) = some answer)
    (hbases : EntryBases seeds P cache state aux.1) (hnodup : aux.1.leafIndices.Nodup) :
    EntryBases seeds P cache' state (traceStepAt seeds P cache state t cache' aux).1 ∧
      (traceStepAt seeds P cache state t cache' aux).1.leafIndices.Nodup := by
  have hold := hbases.mono hc (fun _ _ h => h)
  unfold traceStepAt
  split
  · rename_i h
    obtain ⟨hprf, hbase⟩ := h.choose_spec
    cases hb : state.bound h.choose with
    | none => exact ⟨hold, hnodup⟩
    | some message =>
      simp only
      split
      · rename_i hf
        have hfresh := fresh_base_not_mem seeds P cache state aux.1 hbases h.choose message hb hf
        have hinput := SigningLane2FlatProof.hashCallAt_of_baseCall hbase hb
        obtain ⟨answer, ha⟩ := hcall _ hinput
        constructor
        · intro entry he
          rcases List.mem_append.mp he with he | he
          · exact hold entry he
          · simp only [List.mem_singleton] at he
            subst entry
            refine ⟨hb, SigningR1FixedProof.randomizerCached_mono hc hprf, answer, ?_⟩
            rw [← SigningGuessProof.cachedRandomizer_stable seeds cache cache' _ hc hprf]
            exact ha
        · simp only [XmssSecurity.SigningCacheTrace.leafIndices_append]
          change (List.append (α := XmssSecurity.LeafIndex) aux.1.leafIndices [h.choose]).Nodup
          refine List.nodup_append.mpr ⟨hnodup, by simp, ?_⟩
          intro a ha b hb he
          simp only [List.mem_singleton] at hb
          subst b
          exact hfresh (hb ▸ ha)
      · exact ⟨hold, hnodup⟩
  · exact ⟨hold, hnodup⟩

/-- The cache and trace provenance maintained by the actual trace run. -/
def TraceBases (x : SigningSecurityProof.Keys3 C) (s : TraceState C) : Prop :=
  EntryBases x.2.1 x.1 s.1.1.1.1.1.1 s.2.1.1 s.1.2.1 ∧ s.1.2.1.leafIndices.Nodup

/-- One actual traced world call preserves entry bases and unique leaf indices. -/
theorem traceWorld_bases (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : TraceState C) (hs : TraceBases x s)
    (r : (WorldSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceWorld prims x t).run s)) : TraceBases x r.2 := by
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  have hcache := SigningReleasedAlignProof.world_cache_le prims x t (s.1.1, s.2) step hstep
  have hstate := SigningReleasedLinkProof.world_carried prims x t (s.1.1, s.2) step hstep
  have hcall : ∀ input, HashCallAt input t → ∃ answer, step.2.1.1.1.1.1 (.hash input) = some answer := by
    intro input hi
    obtain ⟨called, hcalled, _, hle⟩ := SigningReleasedAlignProof.world_counted_step prims x t
      (s.1.1, s.2) step hstep
    obtain ⟨answer, ha⟩ := countImpl_hash_cached prims input t hi _ called hcalled
    exact ⟨answer, hle ha⟩
  have h := traceStepAt_bases x.2.1 x.1 _ _ _ t s.1.2 hcache hcall hs.1 hs.2
  change EntryBases x.2.1 x.1 step.2.1.1.1.1.1 step.2.2.1.1 _ ∧ _
  rw [hstate]
  exact h

theorem traceWorld_run_bases (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    {α : Type} (source : OracleComp (WorldSpec C) α) (s : TraceState C)
    (hs : TraceBases x s) (r : α × TraceState C)
    (hr : r ∈ support ((simulateQ (traceWorld prims x) source).run s)) : TraceBases x r.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (TraceBases x)
    (fun t p hp r hr => traceWorld_bases prims x t p hp r hr) source s hs r hr

theorem traceWorld_carried (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : TraceState C) (r : (WorldSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceWorld prims x t).run s)) : r.2.2 = s.2 := by
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  exact SigningReleasedLinkProof.world_carried prims x t (s.1.1, s.2) step hstep

theorem traceWorld_run_carried (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    {α : Type} (source : OracleComp (WorldSpec C) α) (s : TraceState C) (r : α × TraceState C)
    (hr : r ∈ support ((simulateQ (traceWorld prims x) source).run s)) : r.2.2 = s.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (fun p : TraceState C => p.2 = s.2)
    (fun t p hp r hr => (traceWorld_carried prims x t p r hr).trans hp) source s rfl r hr

abbrev traceForger (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree) :=
  flatWith (SigningOpeningProof.openingOracles x (dealtOf x top)) (traceWorld prims x)

theorem traceForger_split (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TraceState C)
    (r : (LocalSpec C + TsigSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceForger prims x top t).run s)) :
    (r.1, (r.2.1.1, r.2.2)) ∈ support
      ((SigningReleasedLinkProof.forger prims x top t).run (s.1.1, s.2)) := by
  have hf := forgets_flatWith (SigningOpeningProof.openingOracles x (dealtOf x top)) _ _
    (traceWorld_forgets prims x) t
  rw [← hf s.1.1 s.1.2 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- Message binding by the outer handler preserves every trace entry's fixed base. -/
theorem traceForger_bases (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TraceState C) (hs : TraceBases x s)
    (r : (LocalSpec C + TsigSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceForger prims x top t).run s)) : TraceBases x r.2 := by
  have hb := (SigningSupportProof.gameOracles_stateGrows (dealtOf x top) t _ _
    (SigningReleasedLinkProof.forger_source prims x top t (s.1.1, s.2) (r.1, (r.2.1.1, r.2.2))
      (traceForger_split prims x top t s r hr))).1
  simp only [traceForger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  have hi := traceWorld_run_bases prims x _ s hs w hw
  have hc := traceWorld_run_carried prims x _ s w hw
  refine ⟨?_, hi.2⟩
  have he := hi.1
  rw [hc] at he
  exact he.mono le_rfl hb

theorem traceForger_run_bases (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : TraceState C)
    (hs : TraceBases x s) (r : α × TraceState C)
    (hr : r ∈ support ((simulateQ (traceForger prims x top) source).run s)) : TraceBases x r.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (TraceBases x)
    (fun t p hp r hr => traceForger_bases prims x top t p hp r hr) source s hs r hr

/-- The actual trace has no repeated leaf index, including unsuccessful searches. -/
theorem traceRun_bases (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C)
    (hz : z ∈ support (traceRun prims A x)) : TraceBases x z.2 := by
  unfold traceRun traceGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hi : TraceBases x
      (((SigningOneRunProof.monitoredInit.1, fun _ => false), ([], false)), SigningOneRunProof.monitoredInit.2) := by
    exact ⟨fun _ h => (List.not_mem_nil h).elim, List.nodup_nil⟩
  have hset : TraceBases x setup.2 := by
    apply traceWorld_run_bases prims x _ _ hi setup
    with_reducible exact hsetup
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hset
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hset
    | top top =>
      simp only [hout, StateT.run_bind, getCarried, StateT.run_mk, pure_bind,
        mem_support_bind_iff] at hz
      obtain ⟨middle, hmiddle, finished, hfinished, hz⟩ := hz
      have hm : TraceBases x middle.2 := by
        apply traceForger_run_bases prims x top _ setup.2 hset middle
        with_reducible exact hmiddle
      have hf : TraceBases x finished.2 := by
        apply traceWorld_run_bases prims x _ middle.2 hm finished
        with_reducible exact hfinished
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hf

theorem traceRun_nodup (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C)
    (hz : z ∈ support (traceRun prims A x)) : z.2.1.2.1.leafIndices.Nodup :=
  (traceRun_bases prims A x z (by with_reducible exact hz)).2

/-- A cached selection collision is a pre-signing partner or a post-signing repeat.
The pure case split is the argument of pinned leanVM's
`cachedSelection_event_le`; its source-game invariants
are supplied explicitly here because this trace belongs to the threshold run. -/
theorem ghost_of_cachedCollision (secretKey : XmssSecurity.SecretKey)
    (trace : XmssSecurity.SigningCacheTrace) (cache : XmssSecurity.HashSpec.QueryCache)
    (hnodup : trace.leafIndices.Nodup) (hle : trace.CachesLe cache)
    (hselected : trace.SelectedValid secretKey)
    (hpreserves : trace.PreservesOtherValidEncodingInputs secretKey)
    (entry : XmssSecurity.SigningCacheEntry) (he : entry ∈ trace)
    (hcollision : entry.CachedSelectionCollision secretKey cache) :
    XmssSecurity.Ghost.PreBad secretKey trace ∨
      (trace.leafIndices.Nodup ∧ XmssSecurity.Ghost.PostBad secretKey.parameter trace cache) := by
  obtain ⟨signature, selectedOutput, otherInput, otherOutput, hs, hso, hoo, hne, hd⟩ := hcollision
  have hfirst := XmssSecurity.Ghost.first_of_nodup hnodup he
  cases hbefore : entry.initialCache
      (XmssSecurity.Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex otherInput) with
  | some answer =>
    have ha : otherOutput = answer := Option.some.inj (hoo.symm.trans ((hle entry he).1 hbefore))
    subst answer
    exact Or.inl ⟨entry.request.leafIndex, entry, hfirst, signature, selectedOutput,
      otherInput, otherOutput, hs, hso, hbefore, hne, hd⟩
  | none =>
    refine Or.inr ⟨hnodup, entry.request.leafIndex, entry, hfirst, signature, selectedOutput,
      otherInput, otherOutput, hs, hso, ?_, hoo, hd⟩
    cases hlocal : entry.finalCache
        (XmssSecurity.Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex otherInput) with
    | none => exact hlocal
    | some answer =>
      have ha : answer = otherOutput := Option.some.inj (((hle entry he).2 hlocal).symm.trans hoo)
      have hvalid := hselected entry he signature hs selectedOutput hso
      obtain ⟨encoding, hdecode⟩ := hvalid
      have hdecodeLocal : XmssSecurity.TargetSum.decodeDigest
          (XmssSecurity.Concrete.CacheView.encodingHash entry.finalCache secretKey.parameter
            entry.request.leafIndex otherInput) = some encoding := by
        rw [XmssSecurity.Concrete.CacheView.encodingHash,
          XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hlocal, ha, ← hd]
        exact hdecode
      have hinput : XmssSecurity.Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
          (entry.request.message, signature.randomness) ≠
          XmssSecurity.Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex otherInput :=
        fun h => hne (XmssSecurity.Concrete.CacheView.encodingInput_injective _ _ h).symm
      have hn := hpreserves entry he signature hs entry.request.leafIndex otherInput encoding
        hdecodeLocal hinput hbefore
      rw [hlocal] at hn
      cases hn

open SigningReleasedAlignProof

/-- Forgetting only the per-key flags retains the actual monitored query. -/
theorem keyed_trial_forget (keyOf : HashInput → Option KeyIndex) (input : HashInput)
    (s : TrialState C) (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf (.hash input)).run s)) :
    (r.1, r.2.1) ∈ support ((monitoredOracle keyOf (.hash input)).run s.1) := by
  simp only [keyedSplitOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact hw

/-- Every input recorded as seen has an answer in the current cache. -/
def SeenCached (cache : HashCache C) (monitor : Monitor) : Prop :=
  ∀ input ∈ monitor.seen, ∃ answer, cache (.hash input) = some answer

theorem SeenCached.mono {cache cache' : HashCache C} {monitor : Monitor}
    (h : SeenCached cache monitor) (hle : cache ≤ cache') : SeenCached cache' monitor := by
  intro input hi
  obtain ⟨answer, ha⟩ := h input hi
  exact ⟨answer, hle ha⟩

/-- A keyed trial keeps all seen inputs cached. -/
theorem keyed_seenCached (keyOf : HashInput → Option KeyIndex) (q : Query C)
    (s : TrialState C) (hs : SeenCached s.1.1 s.1.2) (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf q).run s)) : SeenCached r.2.1.1 r.2.1.2 := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  have hraw := randomOracle_support q s.1.1 a ha
  have hold := hs.mono hraw.1
  cases q with
  | hash input =>
    intro other ho
    simp only [trialStep] at ho
    split_ifs at ho with hi
    · exact hold other ho
    · rw [trialFresh_seen] at ho
      rcases Set.mem_insert_iff.mp ho with rfl | ho
      · exact ⟨a.1, hraw.2.1⟩
      · exact hold other ho
  | _ => exact hold

theorem keyed_run_seenCached (keyOf : HashInput → Option KeyIndex) {α : Type}
    (source : OracleComp (Query C →ₒ HashOutput) α) (s : TrialState C)
    (hs : SeenCached s.1.1 s.1.2) (r : α × TrialState C)
    (hr : r ∈ support ((simulateQ (keyedSplitOracle keyOf) source).run s)) :
    SeenCached r.2.1.1 r.2.1.2 :=
  SeedHitProof.support_simulateQ_inv _ (fun s : TrialState C => SeenCached s.1.1 s.1.2)
    (fun q s hs r hr => keyed_seenCached keyOf q s hs r hr) source s hs r hr

/-- A valid trial that leaves its key unsigned must already have been cached. -/
theorem keyed_valid_cached (keyOf : HashInput → Option KeyIndex) (input : HashInput) (e : KeyIndex)
    (hk : keyOf input = some e) (s : TrialState C)
    (hinv : SeenCached s.1.1 s.1.2)
    (hs : s.1.2.state.signed e = none) (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf (.hash input)).run s))
    (hv : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash r.1))
    (hn : r.2.1.2.state.signed e = none) : s.1.1 (.hash input) = some r.1 := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  have hseen : input ∈ s.1.2.seen := by
    by_contra hno
    simp only [trialStep, if_neg hno, trialFresh, hk, Option.bind_some, hs] at hn
    rw [Monitor.fresh_unsigned keyOf s.1.2 input _ true e hk hs, if_pos hv] at hn
    simp [XmssSecurity.EncodingMonitor.State.install] at hn
  obtain ⟨answer, hans⟩ := hinv input hseen
  have hraw := randomOracle_support _ s.1.1 a ha
  have he : answer = a.1 := Option.some.inj ((hraw.1 hans).symm.trans hraw.2.1)
  exact hans.trans (congrArg some he)

/-- A successful unsigned search that installs no target selects an input cached before the search. -/
theorem grind_unsigned_cached (P : PublicParameter) (e : KeyIndex) (message : Message)
    (base : Randomness) : ∀ attempts trial (s : TrialState C),
    SeenCached s.1.1 s.1.2 →
    s.1.2.state.signed e = none → ∀ r,
    r ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? P))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (bytesLE 32 message) base attempts trial))).run s) →
    r.2.1.2.state.signed e = none → ∀ randomness encoding, r.1 = some (randomness, encoding) →
    ∃ answer, s.1.1 (.hash (tweakableHashInput P (.message bottomLayer e)
      (bytesLE 32 message ++ bytesLE 16 randomness))) = some answer ∧
      Codeword.decode (truncateHash answer) = some encoding := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial s hinv hs r hr hn randomness encoding hout
    simp only [grind, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr] at hout
    cases hout
  | succ n ih =>
    intro trial s hinv hs r hr hn randomness encoding hout
    simp [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash] at hr
    obtain ⟨answer, cache, monitor, flags, hquery, hr⟩ := hr
    have hk := SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P e message
      (base + BitVec.ofNat digestBits trial)
    have hmon := keyed_trial_forget _ _ s (answer, (cache, monitor), flags) hquery
    cases hdec : Codeword.decode (truncateHash answer) with
    | some codeword =>
      simp only [hdec, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      rw [hr] at hout hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hout)
      have hv : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) :=
        (validDigest_iff_decode _).2 ⟨codeword, hdec⟩
      exact ⟨answer, keyed_valid_cached _ _ e hk s hinv hs _ hquery hv hn, hdec⟩
    | none =>
      simp only [hdec] at hr
      have hv : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) := by
        rw [validDigest_iff_decode]
        change ¬∃ encoding, Codeword.decode (truncateHash answer) = some encoding
        simp [hdec]
      have hnext := keyed_seenCached _ _ s hinv (answer, (cache, monitor), flags) hquery
      have hunsigned := keyed_trial_invalid _ _ e hk s hs (answer, (cache, monitor), flags) hquery hv
      obtain ⟨selectedAnswer, hselected, hdecode⟩ := ih (trial + 1) ((cache, monitor), flags)
        hnext hunsigned r hr hn randomness encoding hout
      simp only [monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hmon
      obtain ⟨raw, hraw, heq⟩ := hmon
      have hc : raw.2 = cache := congrArg (fun p : HashOutput × HashCache C × Monitor => p.2.1) heq
      have ho : raw.1 = answer := congrArg Prod.fst heq
      have hrandom := randomOracle_support _ s.1.1 raw hraw
      rw [hc, ho] at hrandom
      dsimp only at hselected
      refine ⟨selectedAnswer, ?_, hdecode⟩
      by_cases he : Query.hash (C := C) (tweakableHashInput P (.message bottomLayer e)
          (bytesLE 32 message ++ bytesLE 16 randomness)) =
          .hash (tweakableHashInput P (.message bottomLayer e)
            (bytesLE 32 message ++ bytesLE 16 (base + BitVec.ofNat digestBits trial)))
      · rw [he, hrandom.2.1] at hselected
        have ho' := Option.some.inj hselected
        rw [← ho', hdec] at hdecode
        cases hdecode
      · exact (hrandom.2.2 _ he).symm.trans hselected

/-- A newly raised per-key flag identifies a cached valid trial and leaves that key unsigned. -/
theorem keyed_flag_new (keyOf : HashInput → Option KeyIndex) (input : HashInput) (e : KeyIndex)
    (s : TrialState C) (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf (.hash input)).run s))
    (hs : s.2 e = false) (hf : r.2.2 e = true) :
    keyOf input = some e ∧ s.1.2.state.signed e = none ∧ input ∈ s.1.2.seen ∧
      XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash r.1) ∧
      r.2.1.2.state.signed e = none := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  simp only [cachedTrialAt, cachedTrial, hs, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at hf
  obtain ⟨⟨hseen, key, hk, hunsigned, hvalid⟩, he⟩ := hf
  have heq : key = e := Option.some.inj (hk.symm.trans he)
  subst key
  refine ⟨he, hunsigned, hseen, hvalid, ?_⟩
  simp only [trialStep, if_pos hseen]
  exact hunsigned

/-- Invalid trials cannot raise a per-key cached-selection flag. -/
theorem keyed_flag_invalid (keyOf : HashInput → Option KeyIndex) (input : HashInput) (e : KeyIndex)
    (s : TrialState C) (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf (.hash input)).run s))
    (hv : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash r.1)) : r.2.2 e = s.2 e := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  simp [cachedTrialAt, cachedTrial, hv]

/-- A grind raising a flag raises its own key's flag at its successful stopping trial. -/
theorem grind_raised (P : PublicParameter) (key : KeyIndex) (message : Message) (base : Randomness) :
    ∀ attempts trial (s : TrialState C) r,
    r ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? P))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer key (bytesLE 32 message) base attempts trial))).run s) →
    ∀ e, s.2 e = false → r.2.2 e = true → key = e ∧
      ∃ randomness encoding, r.1 = some (randomness, encoding) ∧ r.2.1.2.state.signed e = none := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial s r hr e hs hf
    simp only [grind, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr, hs] at hf
    cases hf
  | succ n ih =>
    intro trial s r hr e hs hf
    simp [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash] at hr
    obtain ⟨answer, cache, monitor, flags, hquery, hr⟩ := hr
    have hk := SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P key message
      (base + BitVec.ofNat digestBits trial)
    cases hdec : Codeword.decode (truncateHash answer) with
    | some encoding =>
      simp only [hdec, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      rw [hr] at hf ⊢
      obtain ⟨he, _, _, _, hn⟩ := keyed_flag_new _ _ e s (answer, (cache, monitor), flags) hquery hs hf
      exact ⟨Option.some.inj (hk.symm.trans he), _, encoding, rfl, hn⟩
    | none =>
      simp only [hdec] at hr
      have hv : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) := by
        rw [validDigest_iff_decode]
        change ¬∃ encoding, Codeword.decode (truncateHash answer) = some encoding
        simp [hdec]
      have he := keyed_flag_invalid _ _ e s (answer, (cache, monitor), flags) hquery hv
      exact ih (trial + 1) ((cache, monitor), flags) r hr e (he.trans hs) hf

open SigningLane2BridgeProof SigningLane2FlatProof

/-- The counted base call retains a supported lazy-oracle answer and the resulting cache. -/
theorem base_called_support (prims : Primitives)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (called : (WorldSpec C).Range t × FlatJointState C)
    (hc : called ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (s.1.1.1, s.2)))
    (input : HashInput) (ht : HashCallAt input t) :
    ∃ answer, (answer, called.2.1.1.1) ∈ support
      (((Query C →ₒ HashOutput).randomOracle (.hash input)).run s.1.1.1.1.1) := by
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc
  obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc
  have hproject : (counted.2.1, counted.2.2) ∈ support
      ((fun w => (w.2.1, w.2.2)) <$> (SigningCacheProof.countImpl prims t).run s.1.1.1.1) :=
    by rw [support_map]; exact ⟨counted, hcounted, rfl⟩
  rw [countImpl_hashCallAt prims ht, support_map] at hproject
  obtain ⟨raw, hraw, he⟩ := hproject
  have hcache := congrArg Prod.fst he
  rw [← heq, ← hcache]
  exact ⟨raw.1, hraw⟩

/-- A canonical base step exposes its actual lazy base query and full keyed grind,
including the cache, monitor and flags after the same step. -/
theorem world_base_data (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (r : (WorldSpec C).Range t × SigningReleasedLinkProof.SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t)
    (hbound : s.2.1.1.bound e = some message) :
    ∃ (called : (WorldSpec C).Range t × FlatJointState C) (answer : HashOutput)
      (ground : Option (Randomness × Encoding) × TrialState C),
      called ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (s.1.1.1, s.2)) ∧
      (answer, called.2.1.1.1) ∈ support (((Query C →ₒ HashOutput).randomOracle
        (.hash (randomizerInput x.1 bottomLayer e
          (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message)))).run s.1.1.1.1.1) ∧
      ground ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1))
        (foundGrind x.1 e message answer)).run
          ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
            s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2)) ∧
      ground.2 = ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  obtain ⟨answer, ha⟩ := base_called_support prims t s called hc _
    (hashCallAt_of_baseCall hbase hbound)
  have hanswer := (randomOracle_support _ s.1.1.1.1.1 (answer, called.2.1.1.1) ha).2.1
  rw [SigningReleasedLinkProof.jointCachedExtra_base x (s.1.1.1, s.2) called.2 t e message answer
    hprf hbase hbound hanswer] at hg
  obtain ⟨g, hgrind, he⟩ := baseGrind_subrun x.1 e message answer _ ground hg
  exact ⟨called, answer, g, hc, ha, hgrind, he⟩

/-- The base-returning signer projects to the ordinary signer on the same cache. -/
theorem signWithBase_run_map (key : XmssSecurity.SecretKey) (request : XmssSecurity.SignRequest)
    (initial : XmssSecurity.HashSpec.QueryCache) :
    (simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.scheme.sign key request.leafIndex request.message)).run initial =
      (fun r => (r.1.2, r.2)) <$> (simulateQ XmssSecurity.romImpl
        (SigningLane2Proof.signWithBase key request.leafIndex request.message)).run initial := by
  rw [← SigningLane2Proof.snd_signWithBase, simulateQ_map, StateT.run_map]

set_option backward.isDefEq.respectTransparency true in
/-- Forgetting a sign step's sampled base retains its signing support. -/
theorem signWithBaseStep_sign_support (key : XmssSecurity.SecretKey)
    (request : XmssSecurity.SignRequest) (initial completed : XmssSecurity.HashSpec.QueryCache)
    (base : XmssSecurity.Randomness) (signature : Option XmssSecurity.Signature)
    (h : ((base, signature), ((completed, [⟨request, signature, initial, completed⟩]), 0)) ∈ support
      ((SigningLane2Proof.signWithBaseStep key request).run ((initial, []), 0))) :
    (signature, completed) ∈ support ((simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.scheme.sign key request.leafIndex request.message)).run initial) := by
  have hrun : (fun r => (r.1.2, r.2.1.1)) <$>
      (SigningLane2Proof.signWithBaseStep key request).run ((initial, []), 0) =
      (simulateQ XmssSecurity.romImpl
        (XmssSecurity.Concrete.scheme.sign key request.leafIndex request.message)).run initial := by
    rw [SigningLane2Proof.signWithBaseStep, StateT.run_mk, Functor.map_map, signWithBase_run_map]
  rw [← hrun, support_map]
  exact ⟨_, h, rfl⟩

/-- A supported fresh lazy base query followed by its grind gives a supported leanVM signature. -/
theorem raw_fresh_sign_support (prims : Primitives) (P : PublicParameter) (e : KeyIndex)
    (rho : Digest) (message : Message) (initial afterBase completed : HashCache C)
    (answer : HashOutput) (found : Option (Randomness × Encoding))
    (hfresh : initial (.hash (randomizerInput P bottomLayer e rho (bytesLE 32 message))) = none)
    (ha : (answer, afterBase) ∈ support (((Query C →ₒ HashOutput).randomOracle
      (.hash (randomizerInput P bottomLayer e rho (bytesLE 32 message)))).run initial))
    (hg : (found, completed) ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (foundGrind P e message answer)).run afterBase)) :
    (signOf (laneKey P) e found, keptView IsMsg completed) ∈ support ((simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.scheme.sign (laneKey P) e message)).run (keptView IsMsg initial)) := by
  let result : (XmssSecurity.Randomness × Option XmssSecurity.Signature) × XmssSecurity.Ghost.State :=
    ((truncateHash answer, signOf (laneKey P) e found),
      ((keptView IsMsg completed, [⟨⟨e, message⟩, signOf (laneKey P) e found,
        keptView IsMsg initial, keptView IsMsg completed⟩]), 0))
  have hstep : result ∈ support ((SigningLane2Proof.signWithBaseStep (laneKey P) ⟨e, message⟩).run
      ((keptView IsMsg initial, []), 0)) := by
    apply (mem_support_iff_of_evalDist_eq
      (eagerBase_signWithBaseStep prims P rho ⟨e, message⟩ initial hfresh [] 0) result).mp
    rw [support_map]
    refine ⟨((truncateHash answer, found), completed), ?_, rfl⟩
    rw [mem_support_bind_iff]
    refine ⟨(answer, afterBase), ha, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨(found, completed), hg, by simp⟩
  exact signWithBaseStep_sign_support (laneKey P) ⟨e, message⟩ _ _ _ _ hstep

/-- The fresh dynamic canonical base step gives the actual leanVM signing support
for the signature and the two caches stored in its trace entry. -/
theorem world_fresh_sign_support (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (r : (WorldSpec C).Range t × SigningReleasedLinkProof.SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t)
    (hbound : s.2.1.1.bound e = some message)
    (hfresh : s.1.1.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message))) = none) :
    (signOf (laneKey x.1) e (cachedFound r.2.1.1.1.1.1 x.1 e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) message),
      keptView IsMsg r.2.1.1.1.1.1) ∈ support ((simulateQ XmssSecurity.romImpl
        (XmssSecurity.Concrete.scheme.sign (laneKey x.1) e message)).run
          (keptView IsMsg s.1.1.1.1.1)) := by
  obtain ⟨called, answer, ground, hc, ha, hg, he⟩ :=
    world_base_data prims x t s r hr e message hprf hbase hbound
  have hraw := keyed_run_support _ _ _ ground (by with_reducible exact hg)
  simp only [foundGrind] at hraw
  have hcache : ground.2.1.1 = r.2.1.1.1.1.1 := congrArg (fun p => p.1.1) he
  have hanswer := (randomOracle_support _ s.1.1.1.1.1 (answer, called.2.1.1.1) ha).2.1
  obtain ⟨hle, hev⟩ := randomOracle_run_evalTh
    (grind x.1 bottomLayer e (bytesLE 32 message) (truncateHash answer) randomizerAttemptLimit 0)
    called.2.1.1.1 (ground.1, ground.2.1.1) (by with_reducible exact hraw)
  have hpost := hle hanswer
  dsimp only at hpost
  have hfound : cachedFound r.2.1.1.1.1.1 x.1 e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) message = ground.1 := by
    rw [← hcache, cachedFound, hpost, Option.getD_some]
    exact (hev ground.2.1.1 le_rfl).symm
  rw [hfound, ← hcache]
  exact raw_fresh_sign_support prims x.1 e _ message _ _ _ answer ground.1 hfresh ha hraw

/-- Restriction to message inputs preserves cache extension. -/
theorem keptView_le {initial completed : HashCache C} (h : initial ≤ completed) :
    keptView IsMsg initial ≤ keptView IsMsg completed := by
  intro input answer ha
  simp only [keptView] at ha ⊢
  split_ifs at ha ⊢ with hi
  exact h ha

/-- Each entry is a supported leanVM signing run, whose final cache survives. -/
def EntryRuns (P : PublicParameter) (cache : HashCache C) (trace : XmssSecurity.SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace,
    (entry.signature, entry.finalCache) ∈ support ((simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.scheme.sign (laneKey P) entry.request.leafIndex entry.request.message)).run
        entry.initialCache) ∧ entry.finalCache ≤ keptView IsMsg cache

/-- Extending the current cache preserves the recorded signing runs. -/
theorem EntryRuns.mono {P : PublicParameter} {cache cache' : HashCache C}
    {trace : XmssSecurity.SigningCacheTrace} (h : EntryRuns P cache trace) (hc : cache ≤ cache') :
    EntryRuns P cache' trace := fun entry he => ⟨(h entry he).1, (h entry he).2.trans (keptView_le hc)⟩

/-- Every actual trace append retains a supported leanVM signing run. -/
theorem traceWorld_entryRuns (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : TraceState C)
    (hs : EntryRuns x.1 s.1.1.1.1.1.1 s.1.2.1)
    (r : (WorldSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceWorld prims x t).run s)) :
    EntryRuns x.1 r.2.1.1.1.1.1.1 r.2.1.2.1 := by
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  have hcache := world_cache_le prims x t (s.1.1, s.2) step hstep
  have hold := hs.mono hcache
  change EntryRuns x.1 step.2.1.1.1.1.1
    (traceStepAt x.2.1 x.1 s.1.1.1.1.1.1 s.2.1.1 t step.2.1.1.1.1.1 s.1.2).1
  unfold traceStepAt
  split
  · rename_i h
    cases hb : s.2.1.1.bound h.choose with
    | none => exact hold
    | some message =>
      simp only
      split
      · rename_i hfresh
        intro entry he
        rcases List.mem_append.mp he with he | he
        · exact hold entry he
        · simp only [List.mem_singleton] at he
          subst entry
          exact ⟨world_fresh_sign_support prims x t (s.1.1, s.2) step hstep h.choose message
            h.choose_spec.1 h.choose_spec.2 hb hfresh, le_rfl⟩
      · exact hold
  · exact hold

/-- Any invariant on the world-side state, preserved by a traced world call,
is preserved through setup, the adversary and verification. -/
theorem traceRun_worldInvariant (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (I : TraceState C → Prop)
    (hcarried : ∀ s carried, I s → I (s.1, carried))
    (hstep : ∀ t s, I s → ∀ r, r ∈ support ((traceWorld prims x t).run s) → I r.2)
    (hi : I (((SigningOneRunProof.monitoredInit.1, fun _ => false), ([], false)),
      SigningOneRunProof.monitoredInit.2))
    (z : TraceOutcome C) (hz : z ∈ support (traceRun prims A x)) : I z.2 := by
  have hworld {α : Type} (source : OracleComp (WorldSpec C) α) (s : TraceState C)
      (hs : I s) (r : α × TraceState C)
      (hr : r ∈ support ((simulateQ (traceWorld prims x) source).run s)) : I r.2 :=
    SeedHitProof.support_simulateQ_inv _ I hstep source s hs r hr
  have hforger (top : TopTree) {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
      (s : TraceState C) (hs : I s) (r : α × TraceState C)
      (hr : r ∈ support ((simulateQ (traceForger prims x top) source).run s)) : I r.2 := by
    refine SeedHitProof.support_simulateQ_inv _ I ?_ source s hs r hr
    intro t p hp w hw
    simp only [traceForger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨middle, hm, rfl⟩ := hw
    exact hcarried middle.2 _ (hworld _ p hp middle hm)
  unfold traceRun traceGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hset : I setup.2 := hworld _ _ hi setup (by with_reducible exact hsetup)
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hset
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hset
    | top top =>
      simp only [hout, StateT.run_bind, getCarried, StateT.run_mk, pure_bind, mem_support_bind_iff] at hz
      obtain ⟨middle, hmiddle, finished, hfinished, hz⟩ := hz
      have hm : I middle.2 := hforger top _ setup.2 hset middle (by with_reducible exact hmiddle)
      have hf : I finished.2 := hworld _ middle.2 hm finished (by with_reducible exact hfinished)
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hf

/-- All entries in the actual trace retain their supported signing run and surviving cache. -/
theorem traceRun_entryRuns (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C)
    (hz : z ∈ support (traceRun prims A x)) : EntryRuns x.1 z.2.1.1.1.1.1.1 z.2.1.2.1 := by
  exact traceRun_worldInvariant prims A x (fun s => EntryRuns x.1 s.1.1.1.1.1.1 s.1.2.1)
    (fun _ _ h => h) (fun t s hs r hr => traceWorld_entryRuns prims x t s hs r hr)
    (fun _ h => (List.not_mem_nil h).elim) z (by with_reducible exact hz)

/-- Supported signing entries have the cache properties used by leanVM's collision split.
The preservation case split follows pinned `CappedSigningCacheTrace`'s
`cappedCacheTracedMappedAdversaryImpl_query_preservesOtherValidEncodingInputs`. -/
theorem EntryRuns.properties {P : PublicParameter} {cache : HashCache C}
    {trace : XmssSecurity.SigningCacheTrace} (h : EntryRuns P cache trace) :
    trace.CachesLe (keptView IsMsg cache) ∧ trace.SelectedValid (laneKey P) ∧
      trace.PreservesOtherValidEncodingInputs (laneKey P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro entry he
    obtain ⟨hr, hle⟩ := h entry he
    exact ⟨(XmssSecurity.xmssRom_cache_le _ _ _ hr).trans hle, hle⟩
  · intro entry he signature hs answer ha
    exact XmssSecurity.Ghost.sign_selected_valid (laneKey P)
      (r := (entry.signature, entry.finalCache)) (h entry he).1 hs ha
  · intro entry he signature hs targetKey targetPair encoding hd hne hn
    obtain ⟨hr, _⟩ := h entry he
    rw [hs] at hr
    by_cases hk : entry.request.leafIndex = targetKey
    · exact XmssSecurity.Concrete.precomputedCappedSign_preserves_later_valid_other_encodingInput
        (laneKey P) entry.request.leafIndex targetKey entry.request.message targetPair
        entry.initialCache entry.finalCache entry.finalCache (some signature) hr le_rfl encoding hd
        (by intro candidate hc; cases Option.some.inj hc.symm; exact hne) hn rfl
    · exact XmssSecurity.Concrete.precomputedCappedSign_preserves_other_leafIndex_encodingInput
        (laneKey P) entry.request.leafIndex targetKey entry.request.message targetPair
        entry.initialCache entry.finalCache (some signature) hr hk hn

open SigningDescentProof SigningCacheProof

/-- A successful final selection is the canonical cached grind at its bound message. -/
theorem selected_cachedFound (prims : Primitives) (z : FinalState C)
    (pair : Message × Randomness) (hs : z.selected prims = some pair) :
    z.state.bound z.key = some pair.1 ∧ ∃ encoding,
      cachedFound z.cache z.keys.1 z.key (SigningGuessProof.cachedRandomizer z.keys.2.1 z.cache z.key)
        pair.1 = some (pair.2, encoding) := by
  cases hb : z.state.bound z.key with
  | none => simp [FinalState.selected, hb] at hs
  | some message =>
    cases htree : z.bottomTree prims with
    | none => simp [FinalState.selected, hb, htree] at hs
    | some tree =>
      cases hsc : D prims z.answers (signCodeword z.keys.1 (tree.commitment z.key) z.key message
          (D prims z.answers (prfValue z.keys.2.1 (.randomizer bottomLayer z.key)))) with
      | none => simp [FinalState.selected, hb, htree, hsc] at hs
      | some selected =>
        obtain ⟨randomness, encoding⟩ := selected
        have hp : (message, randomness) = pair := by
          simpa [FinalState.selected, hb, htree, hsc] using hs
        subst pair
        refine ⟨rfl, encoding, ?_⟩
        have hc := SigningGuessProof.signCodeword_some_commitment prims z.answers z.keys.1
          (tree.commitment z.key) z.key message _ _ hsc
        rw [D_signCodeword (prims := prims) _ _ _ _ _ hc.symm] at hsc
        change E prims (answersOf z.cache) (grind _ _ _ _
          (truncateHash (answersOf z.cache (.hash (randomizerInput _ _ _
            (D prims (answersOf z.cache) (prfValue _ _)) _)))) _ _) = _ at hsc
        rw [SigningGuessProof.cachedRandomizer_eq, E_eval] at hsc
        exact hsc

/-- The message-only cache view retains every encoding input. -/
theorem keptView_encodingInput (cache : HashCache C) (P : PublicParameter) (e : KeyIndex)
    (pair : Message × Randomness) :
    keptView IsMsg cache (XmssSecurity.Concrete.CacheView.encodingInput P e pair) =
      thView cache (XmssSecurity.Concrete.CacheView.encodingInput P e pair) := by
  obtain ⟨message, randomness⟩ := pair
  have hi : IsMsg (XmssSecurity.Concrete.CacheView.encodingInput P e (message, randomness)) := by
    change IsMsg (XmssSecurity.Partner.input P e (message, randomness))
    rw [← messageInput_eq_partnerInput]
    exact byte23_msg _ _ _ _
  simp only [keptView, if_pos hi]
  rfl

/-- The final partner equality becomes a collision for a trace entry whose initial cache
contains the same selected pair. -/
theorem entry_collision_of_partner (P : PublicParameter) (cache : HashCache C)
    (entry : XmssSecurity.SigningCacheEntry) (signature : XmssSecurity.Signature)
    (hs : entry.signature = some signature) (answer : HashOutput)
    (ha : entry.initialCache (XmssSecurity.Concrete.CacheView.encodingInput P entry.request.leafIndex
      (entry.request.message, signature.randomness)) = some answer)
    (hle : entry.initialCache ≤ keptView IsMsg cache)
    (other : Message × Randomness)
    (hne : (entry.request.message, signature.randomness) ≠ other)
    (hvalid : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer))
    (heq : XmssSecurity.Concrete.CacheView.encodingHash (thView cache) P entry.request.leafIndex
      (entry.request.message, signature.randomness) =
      XmssSecurity.Concrete.CacheView.encodingHash (thView cache) P entry.request.leafIndex other) :
    entry.CachedSelectionCollision (laneKey P) (keptView IsMsg cache) := by
  have hcurrent := hle ha
  rw [keptView_encodingInput] at hcurrent
  have hselected := XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hcurrent
  obtain ⟨encoding, hd⟩ := hvalid
  have hother : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (thView cache) P entry.request.leafIndex other) =
      some encoding := by rw [← heq, XmssSecurity.Concrete.CacheView.encodingHash, hselected]; exact hd
  obtain ⟨otherAnswer, ho⟩ := XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some
    (thView cache) P entry.request.leafIndex other.1 other.2 encoding hother
  refine ⟨signature, answer, other, otherAnswer, hs, ha, ?_, Ne.symm hne, ?_⟩
  · rw [keptView_encodingInput]
    exact ho
  · exact hselected.symm.trans (heq.trans (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some ho))

/-- A hash entry in the world log identifies the hash call that produced it. -/
theorem hashEntry_call (t : (WorldSpec C).Domain) (answer : (WorldSpec C).Range t)
    (entry : HashInput × Digest × Bool) (he : hashEntry ⟨t, answer⟩ = some entry) : HashCallAt entry.1 t := by
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  all_goals try (cases he)
  all_goals cases q <;> simp only [hashEntry] at he
  all_goals try (cases he)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The counted call and its query monitor keep every seen input cached. -/
theorem called_seenCached (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (hs : SeenCached s.1.1.1.1.1 s.1.1.2)
    (called : (WorldSpec C).Range t × FlatJointState C)
    (hc : called ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (s.1.1.1, s.2))) :
    SeenCached called.2.1.1.1 (queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)) := by
  have hc' := hc
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc'
  obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc'
  have hle : s.1.1.1.1.1 ≤ called.2.1.1.1 := by
    rw [← heq]
    exact SigningCacheProof.countImpl_grows prims t s.1.1.1.1 counted hcounted
  have hold := hs.mono hle
  cases he : hashEntry ⟨t, called.1⟩ with
  | none => simpa only [queryEntryStep, he] using hold
  | some entry =>
    obtain ⟨answer, ha⟩ := base_called_support prims t s called hc entry.1 (hashEntry_call t called.1 entry he)
    have hself := (randomOracle_support _ s.1.1.1.1.1 (answer, called.2.1.1.1) ha).2.1
    intro input hi
    simp only [queryEntryStep, Monitor.step] at hi
    split_ifs at hi with hseen
    · exact hold input hi
    · rw [Monitor.fresh_seen] at hi
      rcases Set.mem_insert_iff.mp hi with rfl | hi
      · exact ⟨answer, hself⟩
      · exact hold input hi

/-- All seen monitor inputs stay cached through the actual dynamic extra grind. -/
theorem world_seenCached (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (hs : SeenCached s.1.1.1.1.1 s.1.1.2)
    (r : (WorldSpec C).Range t × SigningReleasedLinkProof.SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) :
    SeenCached r.2.1.1.1.1.1 r.2.1.1.2 := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  exact keyed_run_seenCached _ _ _ (called_seenCached prims x t s hs called hc) ground
    (by with_reducible exact hg)

/-- The actual trace run retains every monitor-seen input in its hash cache. -/
theorem traceRun_seenCached (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C)
    (hz : z ∈ support (traceRun prims A x)) : SeenCached z.2.1.1.1.1.1.1 z.2.1.1.1.2 := by
  apply traceRun_worldInvariant prims A x (fun s => SeenCached s.1.1.1.1.1.1 s.1.1.1.2)
    (fun _ _ h => h) ?_ (fun _ h => h.elim) z (by with_reducible exact hz)
  intro t s hs r hr
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  exact world_seenCached prims x t (s.1.1, s.2) hs step hstep

/-- The completed canonical search is stable under every future cache extension. -/
theorem world_cachedFound_stable (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (r : (WorldSpec C).Range t × SigningReleasedLinkProof.SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t)
    (hbound : s.2.1.1.bound e = some message)
    (cache : HashCache C) (hle : r.2.1.1.1.1.1 ≤ cache) :
    cachedFound r.2.1.1.1.1.1 x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) message =
      cachedFound cache x.1 e (SigningGuessProof.cachedRandomizer x.2.1 cache e) message := by
  obtain ⟨called, answer, ground, hc, ha, hg, he⟩ :=
    world_base_data prims x t s r hr e message hprf hbase hbound
  have hraw := keyed_run_support _ _ _ ground (by with_reducible exact hg)
  simp only [foundGrind] at hraw
  have hcache : ground.2.1.1 = r.2.1.1.1.1.1 := congrArg (fun p => p.1.1) he
  have hanswer := (randomOracle_support _ s.1.1.1.1.1 (answer, called.2.1.1.1) ha).2.1
  obtain ⟨hgrow, hev⟩ := randomOracle_run_evalTh
    (grind x.1 bottomLayer e (bytesLE 32 message) (truncateHash answer) randomizerAttemptLimit 0)
    called.2.1.1.1 (ground.1, ground.2.1.1) (by with_reducible exact hraw)
  have hpost := hgrow hanswer
  dsimp only at hpost
  rw [hcache] at hpost
  have htotal := (world_cache_le prims x t s r hr).trans hle
  rw [← SigningGuessProof.cachedRandomizer_stable x.2.1 s.1.1.1.1.1 cache e htotal hprf]
  simp only [cachedFound, hpost, hle hpost, Option.getD_some]
  exact (hev _ (le_of_eq hcache)).symm.trans (hev cache ((le_of_eq hcache).trans hle))

/-- Every recorded signature is the canonical selection in every later cache. -/
def EntryStable (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (trace : XmssSecurity.SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, ∀ cache', cache ≤ cache' → entry.signature =
    signOf (laneKey x.1) entry.request.leafIndex
      (cachedFound cache' x.1 entry.request.leafIndex
        (SigningGuessProof.cachedRandomizer x.2.1 cache' entry.request.leafIndex) entry.request.message)

theorem EntryStable.mono {x : SigningSecurityProof.Keys3 C} {cache cache' : HashCache C}
    {trace : XmssSecurity.SigningCacheTrace} (h : EntryStable x cache trace) (hle : cache ≤ cache') :
    EntryStable x cache' trace := fun entry he later hlater => h entry he later (hle.trans hlater)

/-- The actual trace preserves canonical selection through cache extension. -/
theorem traceWorld_entryStable (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : TraceState C)
    (hs : EntryStable x s.1.1.1.1.1.1 s.1.2.1)
    (r : (WorldSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceWorld prims x t).run s)) :
    EntryStable x r.2.1.1.1.1.1.1 r.2.1.2.1 := by
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  have hold := hs.mono (world_cache_le prims x t (s.1.1, s.2) step hstep)
  change EntryStable x step.2.1.1.1.1.1
    (traceStepAt x.2.1 x.1 s.1.1.1.1.1.1 s.2.1.1 t step.2.1.1.1.1.1 s.1.2).1
  unfold traceStepAt
  split
  · rename_i h
    cases hb : s.2.1.1.bound h.choose with
    | none => exact hold
    | some message =>
      simp only
      split
      · intro entry he cache hle
        rcases List.mem_append.mp he with he | he
        · exact hold entry he cache hle
        · simp only [List.mem_singleton] at he
          subst entry
          exact congrArg (signOf (laneKey x.1) h.choose)
            (world_cachedFound_stable prims x t (s.1.1, s.2) step hstep h.choose message
              h.choose_spec.1 h.choose_spec.2 hb cache hle)
      · exact hold
  · exact hold

theorem traceRun_entryStable (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C)
    (hz : z ∈ support (traceRun prims A x)) : EntryStable x z.2.1.1.1.1.1.1 z.2.1.2.1 := by
  exact traceRun_worldInvariant prims A x (fun s => EntryStable x s.1.1.1.1.1.1 s.1.2.1)
    (fun _ _ h => h) (fun t s hs r hr => traceWorld_entryStable prims x t s hs r hr)
    (fun _ h => (List.not_mem_nil h).elim) z (by with_reducible exact hz)

/-- The actual lazy base query and grind determine the cached canonical search. -/
theorem foundGrind_cachedFound (P : PublicParameter) (e : KeyIndex) (rho : Digest) (message : Message)
    (initial afterBase completed : HashCache C) (answer : HashOutput) (found : Option (Randomness × Encoding))
    (ha : (answer, afterBase) ∈ support (((Query C →ₒ HashOutput).randomOracle
      (.hash (randomizerInput P bottomLayer e rho (bytesLE 32 message)))).run initial))
    (hg : (found, completed) ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (foundGrind P e message answer)).run afterBase)) : cachedFound completed P e rho message = found := by
  have hanswer := (randomOracle_support _ initial (answer, afterBase) ha).2.1
  obtain ⟨hle, hev⟩ := randomOracle_run_evalTh
    (grind P bottomLayer e (bytesLE 32 message) (truncateHash answer) randomizerAttemptLimit 0)
    afterBase (found, completed) (by simpa only [foundGrind] using hg)
  have hpost := hle hanswer
  dsimp only at hpost
  rw [cachedFound, hpost, Option.getD_some]
  exact (hev completed le_rfl).symm

/-- A canonical search ending unsigned selected an input already present before the base call. -/
theorem world_unsigned_selection (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (hs : SeenCached s.1.1.1.1.1 s.1.1.2)
    (r : (WorldSpec C).Range t × SigningReleasedLinkProof.SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t)
    (hbound : s.2.1.1.bound e = some message)
    (hn : r.2.1.1.2.state.signed e = none) (signature : XmssSecurity.Signature)
    (hsel : signOf (laneKey x.1) e (cachedFound r.2.1.1.1.1.1 x.1 e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) message) = some signature) :
    ∃ answer, keptView IsMsg s.1.1.1.1.1
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 e (message, signature.randomness)) = some answer := by
  obtain ⟨called, answer, ground, hc, ha, hg, he⟩ :=
    world_base_data prims x t s r hr e message hprf hbase hbound
  have hraw := keyed_run_support _ _ _ ground (by with_reducible exact hg)
  have hcache : ground.2.1.1 = r.2.1.1.1.1.1 := congrArg (fun p => p.1.1) he
  have hm : ground.2.1.2 = r.2.1.1.2 := congrArg (fun p => p.1.2) he
  rw [← hcache, foundGrind_cachedFound _ _ _ _ _ _ _ _ _ ha hraw] at hsel
  simp only [signOf, Option.map_eq_some_iff] at hsel
  obtain ⟨⟨randomness, encoding⟩, hfound, hsig⟩ := hsel
  have hunsigned : (queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)).state.signed e = none := by
    cases hbefore : (queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
        s.1.1.2 (hashEntry ⟨t, called.1⟩)).state.signed e with
    | none => rfl
    | some target =>
      have hp := keyed_run_signed _ e target _ _ hbefore ground (by with_reducible exact hg)
      rw [hm, hn] at hp
      cases hp
  obtain ⟨selectedAnswer, hselected, _⟩ := grind_unsigned_cached x.1 e message (truncateHash answer)
    randomizerAttemptLimit 0
    ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2)
    (called_seenCached prims x t s hs called hc) hunsigned ground
    (by simpa only [foundGrind] using hg) (hm ▸ hn) randomness encoding hfound
  have hne : Query.hash (C := C) (tweakableHashInput x.1 (.message bottomLayer e)
      (bytesLE 32 message ++ bytesLE 16 randomness)) ≠
      .hash (randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message)) := by
    intro h
    have hi := byte23_msg x.1 bottomLayer e (bytesLE 32 message ++ bytesLE 16 randomness)
    rw [Query.hash.inj h] at hi
    exact not_isMsg_randomizerInput _ _ _ _ _ hi
  have hbefore := ((randomOracle_support _ s.1.1.1.1.1 (answer, called.2.1.1.1) ha).2.2 _ hne).symm.trans hselected
  have hrandom : randomness = signature.randomness := congrArg (fun sig => sig.randomness) hsig
  rw [hrandom, messageInput_eq_partnerInput] at hbefore
  refine ⟨selectedAnswer, ?_⟩
  rw [keptView_encodingInput]
  exact hbefore

/-- An entry whose key is still unsigned has its selected input in its initial cache. -/
def EntryUnsigned (P : PublicParameter) (monitor : Monitor) (trace : XmssSecurity.SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, monitor.state.signed entry.request.leafIndex = none →
    ∀ signature, entry.signature = some signature → ∃ answer,
      entry.initialCache (XmssSecurity.Concrete.CacheView.encodingInput P entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some answer

/-- The trace preserves unsigned selections through every actual world step. -/
theorem traceWorld_entryUnsigned (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : TraceState C)
    (hs : SeenCached s.1.1.1.1.1.1 s.1.1.1.2)
    (hu : EntryUnsigned x.1 s.1.1.1.2 s.1.2.1)
    (r : (WorldSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceWorld prims x t).run s)) :
    EntryUnsigned x.1 r.2.1.1.1.2 r.2.1.2.1 := by
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  have hold : EntryUnsigned x.1 step.2.1.1.2 s.1.2.1 := by
    intro entry he hn signature hsig
    apply hu entry he ?_ signature hsig
    cases hb : s.1.1.1.2.state.signed entry.request.leafIndex with
    | none => rfl
    | some target =>
      have hp := world_signed prims x t entry.request.leafIndex target (s.1.1, s.2) hb step hstep
      rw [hn] at hp
      cases hp
  change EntryUnsigned x.1 step.2.1.1.2
    (traceStepAt x.2.1 x.1 s.1.1.1.1.1.1 s.2.1.1 t step.2.1.1.1.1.1 s.1.2).1
  unfold traceStepAt
  split
  · rename_i h
    cases hb : s.2.1.1.bound h.choose with
    | none => exact hold
    | some message =>
      simp only
      split
      · intro entry he hn signature hsig
        rcases List.mem_append.mp he with he | he
        · exact hold entry he hn signature hsig
        · simp only [List.mem_singleton] at he
          subst entry
          exact world_unsigned_selection prims x t (s.1.1, s.2) hs step hstep h.choose message
            h.choose_spec.1 h.choose_spec.2 hb hn signature hsig
      · exact hold
  · exact hold

/-- Every still-unsigned signed trace entry selected an initially cached input. -/
theorem traceRun_entryUnsigned (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C)
    (hz : z ∈ support (traceRun prims A x)) : EntryUnsigned x.1 z.2.1.1.1.2 z.2.1.2.1 := by
  have h := traceRun_worldInvariant prims A x
    (fun s => SeenCached s.1.1.1.1.1.1 s.1.1.1.2 ∧ EntryUnsigned x.1 s.1.1.1.2 s.1.2.1)
    (fun _ _ h => h) ?_ ⟨fun _ h => h.elim, fun _ h => (List.not_mem_nil h).elim⟩ z
    (by with_reducible exact hz)
  · exact h.2
  intro t s hs r hr
  refine ⟨?_, traceWorld_entryUnsigned prims x t s hs.1 hs.2 r hr⟩
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  exact world_seenCached prims x t (s.1.1, s.2) hs.1 step hstep

/-- A newly raised flag identifies its own guarded canonical base call. -/
theorem world_raised_trigger (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (r : (WorldSpec C).Range t × SigningReleasedLinkProof.SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (hs : s.1.2 e = false) (hf : r.2.1.2 e = true) :
    SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e ∧
      BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  change ground.2.2 e = true at hf
  have hpure (h : ground ∈ support ((simulateQ
      (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1)) (pure ())).run
      ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
        s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2))) : False := by
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at h
    rw [h, hs] at hf
    cases hf
  by_cases hG : ∃ g, SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 g ∧
      BaseCall x.1 g (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 g) s.2.1.1 t
  · simp only [jointCachedExtra, SigningR1FixedProof.cachedExtra, if_pos hG] at hg
    unfold grindExtra at hg
    split_ifs at hg with hb
    · cases hbound : s.2.1.1.bound hb.choose with
      | none =>
        simp only [hbound] at hg
        exact (hpure hg).elim
      | some message =>
        cases hanswer : called.2.1.1.1 (.hash (randomizerInput x.1 bottomLayer hb.choose
            (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 hb.choose) (bytesLE 32 message))) with
        | none =>
          simp only [hbound, hanswer] at hg
          exact (hpure hg).elim
        | some answer =>
          simp only [hbound, hanswer] at hg
          obtain ⟨g, hgrind, he⟩ := baseGrind_subrun x.1 hb.choose message answer _ ground hg
          have hf' : g.2.2 e = true := by rw [he]; exact hf
          obtain ⟨hkey, _⟩ := grind_raised x.1 hb.choose message (truncateHash answer)
            randomizerAttemptLimit 0 _ g hgrind e hs hf'
          obtain ⟨key, hprf, hbase⟩ := hG
          have hke : key = e := (SigningR1FixedProof.baseCall_key_eq hbase hb.choose_spec).trans hkey
          subst key
          exact ⟨hprf, hbase⟩
    · exact (hpure hg).elim
  · simp only [jointCachedExtra, SigningR1FixedProof.cachedExtra, if_neg hG] at hg
    exact (hpure hg).elim

/-- Raising a flag gives a successful canonical selection and leaves its key unsigned. -/
theorem world_raised_selection (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SigningReleasedLinkProof.SplitState C)
    (r : (WorldSpec C).Range t × SigningReleasedLinkProof.SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (hs : s.1.2 e = false) (hf : r.2.1.2 e = true) :
    SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e ∧
    BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t ∧
    ∃ message randomness encoding, s.2.1.1.bound e = some message ∧
      cachedFound r.2.1.1.1.1.1 x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) message =
        some (randomness, encoding) ∧ r.2.1.1.2.state.signed e = none := by
  obtain ⟨hprf, hbase⟩ := world_raised_trigger prims x t s r hr e hs hf
  obtain ⟨input, hb, hcall⟩ := hbase
  simp only [baseInput, Option.map_eq_some_iff] at hb
  obtain ⟨message, hbound, hinput⟩ := hb
  have hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t :=
    ⟨input, by simp only [baseInput, hbound, Option.map_some]; exact congrArg some hinput, hcall⟩
  obtain ⟨called, answer, ground, hc, ha, hg, he⟩ :=
    world_base_data prims x t s r hr e message hprf hbase hbound
  have hf' : ground.2.2 e = true := by rw [he]; exact hf
  obtain ⟨_, randomness, encoding, hfound, hn⟩ := grind_raised x.1 e message (truncateHash answer)
    randomizerAttemptLimit 0
    ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2) ground (by simpa only [foundGrind] using hg) e hs hf'
  have hraw := keyed_run_support _ _ _ ground (by with_reducible exact hg)
  have hcache : ground.2.1.1 = r.2.1.1.1.1.1 := congrArg (fun p => p.1.1) he
  have hm : ground.2.1.2 = r.2.1.1.2 := congrArg (fun p => p.1.2) he
  refine ⟨hprf, hbase, message, randomness, encoding, hbound, ?_, hm ▸ hn⟩
  rw [← hcache, foundGrind_cachedFound _ _ _ _ _ _ _ _ _ ha hraw]
  exact hfound

/-- A trace step keeps every old entry and never clears the stale bit. -/
theorem traceStepAt_mono (seeds : C.Term → HashOutput) (P : PublicParameter)
    (cache cache' : HashCache C) (st : TsigState C) (t : (WorldSpec C).Domain)
    (aux : XmssSecurity.SigningCacheTrace × Bool) :
    aux.1 ⊆ (traceStepAt seeds P cache st t cache' aux).1 ∧
      (aux.2 = true → (traceStepAt seeds P cache st t cache' aux).2 = true) := by
  unfold traceStepAt
  split
  · split
    · split
      · exact ⟨List.subset_append_left _ _, id⟩
      · exact ⟨fun _ h => h, by intro h; simp [h]⟩
    · exact ⟨fun _ h => h, id⟩
  · exact ⟨fun _ h => h, id⟩

/-- A flagged key has a successful cached-selection trace entry, unless the base was stale. -/
def FlaggedEntries (P : PublicParameter) (s : TraceState C) : Prop :=
  ∀ e, s.1.1.2 e = true → s.1.2.2 = true ∨ ∃ entry ∈ s.1.2.1,
    entry.request.leafIndex = e ∧ ∃ signature, entry.signature = some signature ∧ ∃ answer,
      entry.initialCache (XmssSecurity.Concrete.CacheView.encodingInput P e
        (entry.request.message, signature.randomness)) = some answer

/-- At the first flag, the trace entry is new, already present, or the base is stale. -/
theorem traceWorld_flaggedEntries (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : TraceState C)
    (hbases : EntryBases x.2.1 x.1 s.1.1.1.1.1.1 s.2.1.1 s.1.2.1)
    (hstable : EntryStable x s.1.1.1.1.1.1 s.1.2.1)
    (hflag : FlaggedEntries x.1 s)
    (r : (WorldSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceWorld prims x t).run s))
    (hunsigned : EntryUnsigned x.1 r.2.1.1.1.2 r.2.1.2.1) : FlaggedEntries x.1 r.2 := by
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  have hmono := traceStepAt_mono x.2.1 x.1 s.1.1.1.1.1.1 step.2.1.1.1.1.1 s.2.1.1 t s.1.2
  intro e hf
  cases hs : s.1.1.2 e with
  | true =>
    rcases hflag e hs with hstale | ⟨entry, he, hkey, signature, hsig, answer, ha⟩
    · exact Or.inl (hmono.2 hstale)
    · exact Or.inr ⟨entry, hmono.1 he, hkey, signature, hsig, answer, ha⟩
  | false =>
    obtain ⟨hprf, hbase, message, randomness, encoding, hbound, hfound, hn⟩ :=
      world_raised_selection prims x t (s.1.1, s.2) step hstep e hs hf
    dsimp only at hprf hbase hbound hfound hn
    let signature := XmssSecurity.Concrete.precomputedSignWithEncoding (laneKey x.1) e randomness encoding
    have hsig : signOf (laneKey x.1) e (cachedFound step.2.1.1.1.1.1 x.1 e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1.1 e) message) = some signature := by
      simp only [hfound, signOf, Option.map_some, signature]
    have hG : ∃ key, SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1.1 key ∧
        BaseCall x.1 key (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1.1 key) s.2.1.1 t :=
      ⟨e, hprf, hbase⟩
    have hkey : hG.choose = e := SigningR1FixedProof.baseCall_key_eq hG.choose_spec.2 hbase
    simp only [traceStepAt, dif_pos hG, hkey, hbound]
    split
    · let entry : XmssSecurity.SigningCacheEntry := ⟨⟨e, message⟩,
        signOf (laneKey x.1) e (cachedFound step.2.1.1.1.1.1 x.1 e
          (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1.1 e) message),
        keptView IsMsg s.1.1.1.1.1.1, keptView IsMsg step.2.1.1.1.1.1⟩
      have he : entry ∈ (traceStepAt x.2.1 x.1 s.1.1.1.1.1.1 s.2.1.1 t step.2.1.1.1.1.1 s.1.2).1 := by
        simp only [traceStepAt, dif_pos hG, hkey, hbound]
        split <;> simp_all [entry]
      exact Or.inr ⟨entry, by simp [entry], rfl, signature, hsig,
        hunsigned entry he hn signature hsig⟩
    · by_cases hmem : e ∈ s.1.2.1.leafIndices
      · obtain ⟨entry, he, hentry⟩ := List.mem_map.mp hmem
        have hb := (hbases entry he).1
        rw [hentry, hbound] at hb
        have hm : entry.request.message = message := (Option.some.inj hb).symm
        have hle := world_cache_le prims x t (s.1.1, s.2) step hstep
        have heval := hstable entry he step.2.1.1.1.1.1 hle
        rw [hentry, hm, ← SigningGuessProof.cachedRandomizer_stable x.2.1
          s.1.1.1.1.1.1 step.2.1.1.1.1.1 e hle hprf, hsig] at heval
        have hu := hunsigned entry (hmono.1 he) (hentry ▸ hn) signature heval
        rw [hentry] at hu
        exact Or.inr ⟨entry, he, hentry, signature, heval, hu⟩
      · exact Or.inl (by simp [hmem])

/-- Prefix invariants identifying the cached selection for every flagged key. -/
def TraceAlignment (x : SigningSecurityProof.Keys3 C) (s : TraceState C) : Prop :=
  TraceBases x s ∧ SeenCached s.1.1.1.1.1.1 s.1.1.1.2 ∧
    EntryUnsigned x.1 s.1.1.1.2 s.1.2.1 ∧ EntryStable x s.1.1.1.1.1.1 s.1.2.1 ∧ FlaggedEntries x.1 s

/-- The first-flag trace invariant is preserved by one actual world step. -/
theorem traceWorld_alignment (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : TraceState C) (hs : TraceAlignment x s)
    (r : (WorldSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceWorld prims x t).run s)) : TraceAlignment x r.2 := by
  have hu := traceWorld_entryUnsigned prims x t s hs.2.1 hs.2.2.1 r hr
  refine ⟨traceWorld_bases prims x t s hs.1 r hr, ?_, hu,
    traceWorld_entryStable prims x t s hs.2.2.2.1 r hr,
    traceWorld_flaggedEntries prims x t s hs.1.1 hs.2.2.2.1 hs.2.2.2.2 r hr hu⟩
  simp only [traceWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  exact world_seenCached prims x t (s.1.1, s.2) hs.2.1 step hstep

theorem traceWorld_run_alignment (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    {α : Type} (source : OracleComp (WorldSpec C) α) (s : TraceState C)
    (hs : TraceAlignment x s) (r : α × TraceState C)
    (hr : r ∈ support ((simulateQ (traceWorld prims x) source).run s)) : TraceAlignment x r.2 :=
  SeedHitProof.support_simulateQ_inv _ (TraceAlignment x)
    (fun t s hs r hr => traceWorld_alignment prims x t s hs r hr) source s hs r hr

/-- The outer handler changes message bindings only compatibly with the retained entries. -/
theorem traceForger_alignment (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TraceState C) (hs : TraceAlignment x s)
    (r : (LocalSpec C + TsigSpec C).Range t × TraceState C)
    (hr : r ∈ support ((traceForger prims x top t).run s)) : TraceAlignment x r.2 := by
  have hb := (SigningSupportProof.gameOracles_stateGrows (dealtOf x top) t _ _
    (SigningReleasedLinkProof.forger_source prims x top t (s.1.1, s.2) (r.1, (r.2.1.1, r.2.2))
      (traceForger_split prims x top t s r hr))).1
  simp only [traceForger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  have hi := traceWorld_run_alignment prims x _ s hs w hw
  have hc := traceWorld_run_carried prims x _ s w hw
  refine ⟨⟨?_, hi.1.2⟩, hi.2⟩
  have he := hi.1.1
  rw [hc] at he
  exact he.mono le_rfl hb

theorem traceForger_run_alignment (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : TraceState C)
    (hs : TraceAlignment x s) (r : α × TraceState C)
    (hr : r ∈ support ((simulateQ (traceForger prims x top) source).run s)) : TraceAlignment x r.2 :=
  SeedHitProof.support_simulateQ_inv _ (TraceAlignment x)
    (fun t s hs r hr => traceForger_alignment prims x top t s hs r hr) source s hs r hr

/-- Every actual trace run identifies an initially cached selection for each flagged key. -/
theorem traceRun_alignment (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C)
    (hz : z ∈ support (traceRun prims A x)) : TraceAlignment x z.2 := by
  unfold traceRun traceGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hi : TraceAlignment x
      (((SigningOneRunProof.monitoredInit.1, fun _ => false), ([], false)), SigningOneRunProof.monitoredInit.2) := by
    refine ⟨⟨fun _ h => (List.not_mem_nil h).elim, List.nodup_nil⟩,
      (fun _ h => h.elim), (fun _ h => (List.not_mem_nil h).elim),
      (fun _ h => (List.not_mem_nil h).elim), ?_⟩
    intro e he
    cases he
  have hset : TraceAlignment x setup.2 :=
    traceWorld_run_alignment prims x _ _ hi setup (by with_reducible exact hsetup)
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hset
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hset
    | top top =>
      simp only [hout, StateT.run_bind, getCarried, StateT.run_mk, pure_bind, mem_support_bind_iff] at hz
      obtain ⟨middle, hmiddle, finished, hfinished, hz⟩ := hz
      have hm : TraceAlignment x middle.2 := traceForger_run_alignment prims x top _ setup.2 hset middle
        (by with_reducible exact hmiddle)
      have hf : TraceAlignment x finished.2 := traceWorld_run_alignment prims x _ middle.2 hm finished
        (by with_reducible exact hfinished)
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hf

/-- On the actual trace run, the lane-2 row is a stale base or leanVM's ghost event. -/
theorem lane2TraceLink (prims : Primitives) : Lane2TraceLink prims (C := C) := by
  intro A x z hz hrow
  have halign := traceRun_alignment prims A x z (by with_reducible exact hz)
  have hruns := traceRun_entryRuns prims A x z (by with_reducible exact hz)
  obtain ⟨hle, hvalid, hpreserves⟩ := hruns.properties
  obtain ⟨_, hpartner, _, hcached⟩ := hrow
  obtain ⟨top, state, forgery, hm, selected, hsel, hne, heq⟩ := hpartner
  obtain ⟨top', state', forgery', hm', hflag⟩ := hcached
  rw [hm] at hm'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
  have hsplit : splitOf z ∈ support (splitRunAt prims A x) := by
    rw [← traceRun_forget, support_map]
    exact ⟨z, (by with_reducible exact hz), rfl⟩
  have hstate := splitRun_state prims A x (splitOf z) (by with_reducible exact hsplit) top state forgery hm
  have hs : (FinalState.mk x top state forgery z.2.1.1.1.1.1.1 false).selected prims = some selected := hsel
  obtain ⟨hbound, encoding, hfound⟩ := selected_cachedFound prims _ selected hs
  change state.bound forgery.signature.leafIndex = some selected.1 at hbound
  change cachedFound z.2.1.1.1.1.1.1 x.1 forgery.signature.leafIndex
    (SigningGuessProof.cachedRandomizer x.2.1 z.2.1.1.1.1.1.1 forgery.signature.leafIndex) selected.1 =
      some (selected.2, encoding) at hfound
  rcases halign.2.2.2.2 forgery.signature.leafIndex hflag with hstale |
      ⟨entry, hentry, hkey, signature, hsig, answer, ha⟩
  · exact Or.inl hstale
  · have hb := (halign.1.1 entry hentry).1
    change z.2.2.1.1 = state at hstate
    rw [hstate, hkey, hbound] at hb
    have hmessage : entry.request.message = selected.1 := (Option.some.inj hb).symm
    have hselection := halign.2.2.2.1 entry hentry z.2.1.1.1.1.1.1 le_rfl
    rw [hkey, hmessage, hfound, signOf, Option.map_some] at hselection
    have hrandom : signature.randomness = selected.2 :=
      congrArg (fun sig => sig.randomness) (Option.some.inj (hsig.symm.trans hselection))
    have hpair : (entry.request.message, signature.randomness) = selected := Prod.ext hmessage hrandom
    have ha' : entry.initialCache (XmssSecurity.Concrete.CacheView.encodingInput x.1 entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some answer := by rw [hkey]; exact ha
    have hcollision := entry_collision_of_partner x.1 z.2.1.1.1.1.1.1 entry signature hsig answer ha'
      (hle entry hentry).1 (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness)
      (by rw [hpair]; exact hne) (hvalid entry hentry signature hsig answer ha') (by
        rw [hpair, hkey]
        exact heq)
    exact Or.inr (ghost_of_cachedCollision (laneKey x.1) z.2.1.2.1
      (keptView IsMsg z.2.1.1.1.1.1.1) halign.1.2 hle hvalid hpreserves entry hentry hcollision)

end ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.lane2TraceLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.lane2TraceLink

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.traceRun_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.traceRun_nodup

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.traceRun_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.traceRun_alignment

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.world_fresh_sign_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2TraceLinkProof.world_fresh_sign_support

