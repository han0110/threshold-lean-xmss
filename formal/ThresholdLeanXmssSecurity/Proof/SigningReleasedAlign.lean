import ThresholdLeanXmssSecurity.Proof.SigningReleasedLink
import ThresholdLeanXmssSecurity.Proof.SigningPartnerCompare

/-!
# Released selections and the actual trial monitor

The stopping rule of the signing grind agrees with the monitor's valid-digest test.
A successful grind at an unsigned key either records a cached selection at that key
or installs the digest returned by the grind. Every installed target retains its
actual completed canonical search, so it agrees with any selected replay.

An honest computation on the actual split run has a counted replay in its completed
cache. This preserves stored-tree provenance and supplies the cached randomizer
entries before each successful round-two codeword search. Outside alternative
commitment openings, that search reaches the actual canonical base trigger. Its
mark persists through the adversary continuation and verification. The final
theorem states the original ReleasedSelectionAlignment for every ledger key.
-/

open OracleComp OracleSpec
noncomputable section

namespace ThresholdLeanXmssSecurity.SigningReleasedAlignProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningPartnerBoundProof SigningFlatEagerProof SigningOneRunProof

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

variable {C : Committee}

/-- The protocol and leanVM decode the same digests. -/
theorem validDigest_iff_decode (digest : Digest) :
    XmssSecurity.TargetSum.ValidDigest digest ↔ ∃ encoding, Codeword.decode digest = some encoding := by
  simp only [XmssSecurity.TargetSum.ValidDigest, XmssSecurity.Bridge.decode_eq]
  rfl

abbrev TrialState (C : Committee) :=
  (HashCache C × Monitor) × (XmssSecurity.LeafIndex → Bool)

/-- At an unsigned key, a valid trial is either recorded as cached or installed. -/
theorem keyed_trial_valid (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (input : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (hk : keyOf input = some e) (s : TrialState C) (hs : s.1.2.state.signed e = none)
    (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf (.hash input)).run s))
    (hv : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash r.1)) :
    r.2.2 e = true ∨ r.2.1.2.state.signed e = some (XmssSecurity.truncateHash r.1) := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  by_cases hseen : input ∈ s.1.2.seen
  · left
    simp [cachedTrialAt, cachedTrial, hseen, hk, hs, hv]
  · right
    simp only [trialStep, if_neg hseen, trialFresh, hk, Option.bind_some, hs]
    rw [Monitor.fresh_unsigned keyOf s.1.2 input _ true e hk hs, if_pos hv]
    simp [XmssSecurity.EncodingMonitor.State.install]

/-- If this trial installs a target, that target is exactly its returned digest. -/
theorem keyed_trial_installed_value (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (input : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (hk : keyOf input = some e) (s : TrialState C) (hs : s.1.2.state.signed e = none)
    (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf (.hash input)).run s))
    (target : XmssSecurity.Digest) (ht : r.2.1.2.state.signed e = some target) :
    target = XmssSecurity.truncateHash r.1 := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  by_cases hseen : input ∈ s.1.2.seen
  · simp only [trialStep, if_pos hseen, hs] at ht
    contradiction
  · simp only [trialStep, if_neg hseen, trialFresh, hk, Option.bind_some, hs] at ht
    rw [Monitor.fresh_unsigned keyOf s.1.2 input _ true e hk hs] at ht
    by_cases hv : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash a.1)
    · rw [if_pos hv, if_pos rfl] at ht
      have h : some (XmssSecurity.truncateHash a.1) = some target := by
        simpa only [XmssSecurity.EncodingMonitor.State.install, Function.update_self] using ht
      exact (Option.some.inj h).symm
    · rw [if_neg hv] at ht
      have h : (none : Option XmssSecurity.Digest) = some target := hs.symm.trans ht
      contradiction

/-- An invalid trial leaves an unsigned key unsigned. -/
theorem keyed_trial_invalid (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (input : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (hk : keyOf input = some e) (s : TrialState C) (hs : s.1.2.state.signed e = none)
    (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf (.hash input)).run s))
    (hv : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash r.1)) :
    r.2.1.2.state.signed e = none := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  by_cases hseen : input ∈ s.1.2.seen
  · simpa only [trialStep, if_pos hseen] using hs
  · simp only [trialStep, if_neg hseen, trialFresh, hk, Option.bind_some, hs]
    rw [Monitor.fresh_unsigned keyOf s.1.2 input _ true e hk hs, if_neg hv]
    exact hs

/-- A fresh query or trial never replaces an installed target. -/
theorem fresh_signed_preserved
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (m : Monitor) (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest)
    (honest : Bool) (e : XmssSecurity.LeafIndex) (target : XmssSecurity.Digest)
    (hs : m.state.signed e = some target) :
    (m.fresh keyOf input digest honest).state.signed e = some target := by
  cases hk : keyOf input with
  | none => rw [Monitor.fresh_none keyOf m input digest honest hk]; exact hs
  | some f =>
    by_cases he : f = e
    · subst f
      rw [Monitor.fresh_signed keyOf m input digest honest e hk target hs]
      exact hs
    · rw [(SigningUnchargedLoggedProof.fresh_state_at keyOf e m input digest honest
        (by rw [hk]; exact fun h => he (Option.some.inj h))).1]
      exact hs

theorem trialStep_signed_preserved
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (m : Monitor) (q : Query C) (output : HashOutput)
    (e : XmssSecurity.LeafIndex) (target : XmssSecurity.Digest)
    (hs : m.state.signed e = some target) :
    (trialStep keyOf m q output).state.signed e = some target := by
  cases q with
  | hash input =>
    simp only [trialStep]
    split_ifs
    · exact hs
    · unfold trialFresh
      split
      · exact hs
      · exact fresh_signed_preserved keyOf m input _ true e target hs
  | _ => exact hs

/-- Either way of recording the selected digest is persistent. -/
def Marked (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest) (s : TrialState C) : Prop :=
  s.2 e = true ∨ s.1.2.state.signed e = some digest

theorem keyed_step_marked
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (q : Query C) (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest)
    (s : TrialState C) (hs : Marked e digest s) (r : HashOutput × TrialState C)
    (hr : r ∈ support ((keyedSplitOracle keyOf q).run s)) : Marked e digest r.2 := by
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  rcases hs with hs | hs
  · left
    simp [hs]
  · exact Or.inr (trialStep_signed_preserved keyOf s.1.2 q a.1 e digest hs)

theorem keyed_run_marked
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest) {α : Type}
    (source : OracleComp (Query C →ₒ HashOutput) α) (s : TrialState C)
    (hs : Marked e digest s) (r : α × TrialState C)
    (hr : r ∈ support ((simulateQ (keyedSplitOracle keyOf) source).run s)) :
    Marked e digest r.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (Marked e digest)
    (fun q s hs r hr => keyed_step_marked keyOf q e digest s hs r hr) source s hs r hr

/-- A successful grind begun at an unsigned key records its actual selected digest. -/
theorem grind_unsigned (P : PublicParameter) (e : KeyIndex) (message : Message)
    (base : Randomness) : ∀ attempts trial (s : TrialState C),
    s.1.2.state.signed e = none → ∀ r,
    r ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? P))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (bytesLE 32 message) base attempts trial))).run s) →
    ∀ randomness encoding, r.1 = some (randomness, encoding) →
    ∃ answer, r.2.1.1 (.hash (tweakableHashInput P (.message bottomLayer e)
      (bytesLE 32 message ++ bytesLE 16 randomness))) = some answer ∧
      Marked e (XmssSecurity.truncateHash answer) r.2 := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial s hs r hr randomness encoding hout
    simp only [grind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hout
    contradiction
  | succ n ih =>
    intro trial s hs r hr randomness encoding hout
    simp [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash] at hr
    obtain ⟨answer, cache, monitor, flags, hquery, hr⟩ := hr
    cases hdec : Codeword.decode (truncateHash answer) with
    | some codeword =>
      simp only [hdec, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst r
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hout)
      have hvalid : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) :=
        (validDigest_iff_decode _).2 ⟨codeword, hdec⟩
      have hm := keyed_trial_valid (XmssSecurity.encodingInputLeafIndex? P) _ e
        (SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P e message _) s hs
        (answer, (cache, monitor), flags) hquery hvalid
      refine ⟨answer, ?_, hm⟩
      simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hquery
      obtain ⟨w, ⟨a, ha, rfl⟩, heq⟩ := hquery
      have hself := (randomOracle_support _ s.1.1 a ha).2.1
      have ha : a.1 = answer := congrArg Prod.fst heq
      have hc : a.2 = cache := congrArg (fun p : HashOutput × TrialState C => p.2.1.1) heq
      rw [ha, hc] at hself
      exact hself
    | none =>
      simp only [hdec] at hr
      have hinvalid : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) := by
        rw [validDigest_iff_decode]
        change ¬∃ codeword, Codeword.decode (truncateHash answer) = some codeword
        simp only [hdec, reduceCtorEq, exists_false, not_false_eq_true]
      have hm := keyed_trial_invalid (XmssSecurity.encodingInputLeafIndex? P) _ e
        (SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P e message _) s hs
        (answer, (cache, monitor), flags) hquery hinvalid
      exact ih (trial + 1) ((cache, monitor), flags) hm r hr randomness encoding hout

/-- A newly signed key has a successful grind output and its cached selected digest. -/
theorem grind_newly_signed (P : PublicParameter) (e : KeyIndex) (message : Message)
    (base : Randomness) : ∀ attempts trial (s : TrialState C),
    s.1.2.state.signed e = none → ∀ r,
    r ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? P))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (bytesLE 32 message) base attempts trial))).run s) →
    ∀ target, r.2.1.2.state.signed e = some target →
    ∃ randomness encoding answer, r.1 = some (randomness, encoding) ∧
      r.2.1.1 (.hash (tweakableHashInput P (.message bottomLayer e)
        (bytesLE 32 message ++ bytesLE 16 randomness))) = some answer ∧
      XmssSecurity.truncateHash answer = target := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial s hs r hr target ht
    simp only [grind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at ht
    cases hs.symm.trans ht
  | succ n ih =>
    intro trial s hs r hr target ht
    simp [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash] at hr
    obtain ⟨answer, cache, monitor, flags, hquery, hr⟩ := hr
    cases hdec : Codeword.decode (truncateHash answer) with
    | some codeword =>
      simp only [hdec, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst r
      have hvalue := keyed_trial_installed_value (XmssSecurity.encodingInputLeafIndex? P) _ e
        (SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P e message _) s hs
        (answer, (cache, monitor), flags) hquery target ht
      refine ⟨_, codeword, answer, rfl, ?_, hvalue.symm⟩
      simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hquery
      obtain ⟨w, ⟨a, ha, rfl⟩, heq⟩ := hquery
      have hself := (randomOracle_support _ s.1.1 a ha).2.1
      have ha : a.1 = answer := congrArg Prod.fst heq
      have hc : a.2 = cache := congrArg (fun p : HashOutput × TrialState C => p.2.1.1) heq
      rw [ha, hc] at hself
      exact hself
    | none =>
      simp only [hdec] at hr
      have hinvalid : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) := by
        rw [validDigest_iff_decode]
        change ¬∃ codeword, Codeword.decode (truncateHash answer) = some codeword
        simp only [hdec, reduceCtorEq, exists_false, not_false_eq_true]
      have hm := keyed_trial_invalid (XmssSecurity.encodingInputLeafIndex? P) _ e
        (SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P e message _) s hs
        (answer, (cache, monitor), flags) hquery hinvalid
      exact ih (trial + 1) ((cache, monitor), flags) hm r hr target ht

/-- Forgetting the trial monitor and flags retains the actual lazy-oracle execution. -/
theorem keyed_run_support
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {α : Type}
    (source : OracleComp (Query C →ₒ HashOutput) α) (s : TrialState C) (r : α × TrialState C)
    (hr : r ∈ support ((simulateQ (keyedSplitOracle keyOf) source).run s)) :
    (r.1, r.2.1.1) ∈ support
      ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput)) source).run s.1.1) := by
  rw [← monitoredOracle_run_forget keyOf source s.1.1 s.1.2, support_map]
  refine ⟨(r.1, r.2.1), ?_, rfl⟩
  rw [← keyedSplitOracle_run_forget keyOf source s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

theorem keyed_run_cache_le
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {α : Type}
    (source : OracleComp (Query C →ₒ HashOutput) α) (s : TrialState C) (r : α × TrialState C)
    (hr : r ∈ support ((simulateQ (keyedSplitOracle keyOf) source).run s)) :
    s.1.1 ≤ r.2.1.1 := by
  exact SeedHitProof.support_simulateQ_inv (randomOracle (spec := Query C →ₒ HashOutput))
    (fun cache => s.1.1 ≤ cache)
    (fun q cache hcache r hr => hcache.trans (randomOracle_support q cache r hr).1)
    source s.1.1 le_rfl (r.1, r.2.1.1) (keyed_run_support keyOf source s r hr)

/-- The installed value itself, independently of cached-selection flags, persists. -/
theorem keyed_run_signed
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (e : XmssSecurity.LeafIndex) (target : XmssSecurity.Digest) {α : Type}
    (source : OracleComp (Query C →ₒ HashOutput) α) (s : TrialState C)
    (hs : s.1.2.state.signed e = some target) (r : α × TrialState C)
    (hr : r ∈ support ((simulateQ (keyedSplitOracle keyOf) source).run s)) :
    r.2.1.2.state.signed e = some target := by
  refine SeedHitProof.support_simulateQ_inv _
    (fun s : TrialState C => s.1.2.state.signed e = some target) ?_ source s hs r hr
  intro q s hs r hr
  simp only [keyedSplitOracle, monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hr
  exact trialStep_signed_preserved keyOf s.1.2 q a.1 e target hs

/-- Mapping away a grind's result retains that result as a same-run witness. -/
theorem baseGrind_subrun (P : PublicParameter) (e : KeyIndex) (message : Message) (answer : HashOutput)
    (s : TrialState C) (r : Unit × TrialState C)
    (hr : r ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? P))
      (baseGrind P e message answer)).run s)) :
    ∃ g, g ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? P))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (bytesLE 32 message) (truncateHash answer) randomizerAttemptLimit 0))).run s) ∧
      g.2 = r.2 := by
  simp only [baseGrind, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨g, hg, rfl⟩ := hr
  exact ⟨g, hg, rfl⟩

open SigningReleasedLinkProof SigningJointEagerProof

/-- The actual split world only extends its hash cache. -/
theorem world_cache_le (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SplitState C) (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) :
    s.1.1.1.1.1 ≤ r.2.1.1.1.1.1 := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  have hground : called.2.1.1.1 ≤ ground.2.1.1 := by
    apply keyed_run_cache_le (XmssSecurity.encodingInputLeafIndex? x.1)
      (jointCachedExtra x.2.1 x.1 (s.1.1.1, s.2) t called.2)
      ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
        s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2) ground
    with_reducible exact hg
  change s.1.1.1.1.1 ≤ ground.2.1.1
  refine le_trans ?_ hground
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc
  obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc
  rw [← heq]
  exact SigningCacheProof.countImpl_grows prims t s.1.1.1.1 counted hcounted

/-- A supported signing search that produced the monitor's target. Its base uses the
cached randomizer and bound message, and its completed cache survives in the current cache. -/
def SelectionWitness (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (state : TsigState C) (e : KeyIndex) (target : Digest) : Prop :=
  SigningGuessProof.RandomizerCached x.2.1 cache e ∧
  ∃ message baseAnswer randomness encoding answer initial completed,
    state.bound e = some message ∧
    cache (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 cache e) (bytesLE 32 message))) = some baseAnswer ∧
    (some (randomness, encoding), completed) ∈ support
      ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
        (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
          (grind x.1 bottomLayer e (bytesLE 32 message) (truncateHash baseAnswer)
            randomizerAttemptLimit 0))).run initial) ∧
    completed ≤ cache ∧
    completed (.hash (tweakableHashInput x.1 (.message bottomLayer e)
      (bytesLE 32 message ++ bytesLE 16 randomness))) = some answer ∧
    XmssSecurity.truncateHash answer = target

/-- Cache extension and write-once message binding preserve a selection witness. -/
theorem SelectionWitness.mono (x : SigningSecurityProof.Keys3 C)
    {cache cache' : HashCache C} {state state' : TsigState C} {e : KeyIndex} {target : Digest}
    (hcache : cache ≤ cache') (hstate : SigningGuessProof.BoundExtends state state')
    (h : SelectionWitness x cache state e target) : SelectionWitness x cache' state' e target := by
  obtain ⟨hprf, message, baseAnswer, randomness, encoding, answer, initial, completed,
    hb, hbase, hrun, hle, hanswer, ht⟩ := h
  refine ⟨SigningR1FixedProof.randomizerCached_mono hcache hprf,
    message, baseAnswer, randomness, encoding, answer, initial, completed,
    hstate e message hb, ?_, hrun, hle.trans hcache, hanswer, ht⟩
  rw [← SigningGuessProof.cachedRandomizer_stable x.2.1 cache cache' e hcache hprf]
  exact hcache hbase

/-- A newly installed target comes from the guarded canonical base call of its own key. -/
theorem world_newly_signed_trigger (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SplitState C)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (target : Digest) (hs : s.1.1.2.state.signed e = none)
    (ht : r.2.1.1.2.state.signed e = some target) :
    SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e ∧
      BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  change ground.2.1.2.state.signed e = some target at ht
  have hpure (h : ground ∈ support ((simulateQ
      (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1)) (pure ())).run
      ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
        s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2))) : False := by
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
    rw [h] at ht
    change (queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)).state.signed e = some target at ht
    with_reducible rw [SigningR1FixedProof.queryEntryStep_signed, hs] at ht
    cases ht
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
          by_cases he : e = hb.choose
          · obtain ⟨g, hcache, hbase⟩ := hG
            have hge : g = e := (SigningR1FixedProof.baseCall_key_eq hbase hb.choose_spec).trans he.symm
            subst g
            exact ⟨hcache, hbase⟩
          · have hm : (ground.1, ground.2.1) ∈ support ((simulateQ
                (monitoredOracle (XmssSecurity.encodingInputLeafIndex? x.1))
                (baseGrind x.1 hb.choose message answer)).run
                (called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
                  s.1.1.2 (hashEntry ⟨t, called.1⟩))) := by
              rw [← keyedSplitOracle_run_forget _ _ _ s.1.2, support_map]
              exact ⟨ground, hg, rfl⟩
            have hn := SigningR1FixedProof.baseGrind_signed_ne x.1 hb.choose message answer
              _ (ground.1, ground.2.1) hm e he
            rw [hn, SigningR1FixedProof.queryEntryStep_signed, hs] at ht
            contradiction
    · exact (hpure hg).elim
  · simp only [jointCachedExtra, SigningR1FixedProof.cachedExtra, if_neg hG] at hg
    exact (hpure hg).elim

/-- A new installation retains the successful canonical search that produced its digest. -/
theorem world_newly_signed_witness (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SplitState C)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (target : Digest) (hs : s.1.1.2.state.signed e = none)
    (ht : r.2.1.1.2.state.signed e = some target) :
    SelectionWitness x r.2.1.1.1.1.1 r.2.2.1.1 e target := by
  obtain ⟨hprf, hbase⟩ := world_newly_signed_trigger prims x t s r hr e target hs ht
  have hle := world_cache_le prims x t s r hr
  have hcarried := world_carried prims x t s r hr
  obtain ⟨input, hinput, hcall⟩ := hbase
  simp only [baseInput, Option.map_eq_some_iff] at hinput
  obtain ⟨message, hbound, hinput⟩ := hinput
  have hbound' : r.2.2.1.1.bound e = some message := by rw [hcarried]; exact hbound
  have hcall' : HashCallAt (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message)) t :=
    hinput.symm ▸ hcall
  have hbase' : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t :=
    ⟨input, by simp only [baseInput, hbound, Option.map_some]; exact congrArg some hinput, hcall⟩
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  change ground.2.1.2.state.signed e = some target at ht
  change s.1.1.1.1.1 ≤ ground.2.1.1 at hle
  have hc' := hc
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc'
  obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc'
  obtain ⟨baseAnswer, hanswer⟩ := countImpl_hash_cached prims _ t hcall' _ counted hcounted
  have hanswer' : called.2.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message))) = some baseAnswer := by
    rw [← heq]
    exact hanswer
  rw [jointCachedExtra_base x (s.1.1.1, s.2) called.2 t e message baseAnswer
    hprf hbase' hbound hanswer'] at hg
  obtain ⟨g, hgrind, hgstate⟩ := baseGrind_subrun x.1 e message baseAnswer _ ground hg
  have hunsigned : (queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)).state.signed e = none := by
    rw [SigningR1FixedProof.queryEntryStep_signed]
    exact hs
  obtain ⟨randomness, encoding, answer, hout, hselected, htarget⟩ :=
    grind_newly_signed x.1 e message (truncateHash baseAnswer) randomizerAttemptLimit 0
      _ hunsigned g hgrind target (by rw [hgstate]; exact ht)
  have hrun := keyed_run_support (XmssSecurity.encodingInputLeafIndex? x.1) _ _ g hgrind
  have hgrow := keyed_run_cache_le (XmssSecurity.encodingInputLeafIndex? x.1) _ _ ground hg
  rw [hout] at hrun
  refine ⟨SigningR1FixedProof.randomizerCached_mono hle hprf,
    message, baseAnswer, randomness, encoding, answer, called.2.1.1.1, g.2.1.1,
    hbound', ?_, hrun, ?_, hselected, htarget⟩
  · change ground.2.1.1 (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 ground.2.1.1 e) (bytesLE 32 message))) = some baseAnswer
    rw [← SigningGuessProof.cachedRandomizer_stable x.2.1 s.1.1.1.1.1 ground.2.1.1 e hle hprf]
    exact hgrow hanswer'
  · change g.2.1.1 ≤ ground.2.1.1
    rw [hgstate]

/-- The signed-target or cached-trial record survives every actual split-world call. -/
theorem world_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest)
    (s : SplitState C) (hs : Marked e digest ((s.1.1.1.1.1, s.1.1.2), s.1.2))
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) :
    Marked e digest ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk, mem_support_bind_iff,
    support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  change Marked e digest ground.2
  refine keyed_run_marked (XmssSecurity.encodingInputLeafIndex? x.1) e digest
    (jointCachedExtra x.2.1 x.1 (s.1.1.1, s.2) t called.2)
    ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2) ?_ ground ?_
  · rcases hs with hs | hs
    · exact Or.inl hs
    · right
      rw [SigningR1FixedProof.queryEntryStep_signed]
      exact hs
  · with_reducible exact hg

theorem world_run_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest) {α : Type}
    (source : OracleComp (WorldSpec C) α) (s : SplitState C)
    (hs : Marked e digest ((s.1.1.1.1.1, s.1.1.2), s.1.2)) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x) source).run s)) :
    Marked e digest ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  exact SeedHitProof.support_simulateQ_inv _
    (fun s : SplitState C => Marked e digest ((s.1.1.1.1.1, s.1.1.2), s.1.2))
    (fun t s hs r hr => world_marked prims x t e digest s hs r hr) source s hs r hr

theorem forger_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest)
    (s : SplitState C) (hs : Marked e digest ((s.1.1.1.1.1, s.1.1.2), s.1.2))
    (r : (LocalSpec C + TsigSpec C).Range t × SplitState C)
    (hr : r ∈ support ((forger prims x top t).run s)) :
    Marked e digest ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  simp only [forger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact world_run_marked prims x e digest _ s hs w hw

theorem forger_run_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : SplitState C)
    (hs : Marked e digest ((s.1.1.1.1.1, s.1.1.2), s.1.2)) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s)) :
    Marked e digest ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  exact SeedHitProof.support_simulateQ_inv _
    (fun s : SplitState C => Marked e digest ((s.1.1.1.1.1, s.1.1.2), s.1.2))
    (fun t s hs r hr => forger_marked prims x top t e digest s hs r hr) source s hs r hr

/-- No actual world call overwrites a signed target. -/
theorem world_signed (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (e : KeyIndex) (target : Digest)
    (s : SplitState C) (hs : s.1.1.2.state.signed e = some target)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) :
    r.2.1.1.2.state.signed e = some target := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk, mem_support_bind_iff,
    support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  change ground.2.1.2.state.signed e = some target
  refine keyed_run_signed (XmssSecurity.encodingInputLeafIndex? x.1) e target
    (jointCachedExtra x.2.1 x.1 (s.1.1.1, s.2) t called.2)
    ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2) ?_ ground ?_
  · rw [SigningR1FixedProof.queryEntryStep_signed]
    exact hs
  · with_reducible exact hg

/-- Every signed target has its own completed canonical search. -/
def SelectionWitnesses (x : SigningSecurityProof.Keys3 C) (s : SplitState C) : Prop :=
  ∀ e target, s.1.1.2.state.signed e = some target →
    SelectionWitness x s.1.1.1.1.1 s.2.1.1 e target

theorem world_witnesses (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SplitState C) (hs : SelectionWitnesses x s)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) :
    SelectionWitnesses x r.2 := by
  intro e target ht
  cases hbefore : s.1.1.2.state.signed e with
  | none => exact world_newly_signed_witness prims x t s r hr e target hbefore ht
  | some old =>
    have hstable := world_signed prims x t e old s hbefore r hr
    have heq : old = target := Option.some.inj (hstable.symm.trans ht)
    subst old
    apply SelectionWitness.mono x (world_cache_le prims x t s r hr) _ (hs e target hbefore)
    rw [world_carried prims x t s r hr]
    exact SigningGuessProof.boundExtends_refl _

theorem world_run_witnesses (prims : Primitives) (x : SigningSecurityProof.Keys3 C) {α : Type}
    (source : OracleComp (WorldSpec C) α) (s : SplitState C) (hs : SelectionWitnesses x s)
    (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x) source).run s)) :
    SelectionWitnesses x r.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (SelectionWitnesses x)
    (fun t s hs r hr => world_witnesses prims x t s hs r hr) source s hs r hr

/-- The signing handler may bind new messages, but cannot change the bound message of a signed key. -/
theorem forger_witnesses (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : SplitState C) (hs : SelectionWitnesses x s)
    (r : (LocalSpec C + TsigSpec C).Range t × SplitState C)
    (hr : r ∈ support ((forger prims x top t).run s)) : SelectionWitnesses x r.2 := by
  have hbound := (SigningSupportProof.gameOracles_stateGrows (dealtOf x top) t _ _
    (forger_source prims x top t s r hr)).1
  simp only [forger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  have hwit := world_run_witnesses prims x _ s hs w hw
  have hc := world_run_carried prims x _ s w hw
  intro e target ht
  have h := hwit e target ht
  rw [hc] at h
  exact SelectionWitness.mono x le_rfl hbound h

theorem forger_run_witnesses (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (s : SplitState C) (hs : SelectionWitnesses x s) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s)) : SelectionWitnesses x r.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (SelectionWitnesses x)
    (fun t s hs r hr => forger_witnesses prims x top t s hs r hr) source s hs r hr

/-- All keys signed by the actual split run retain their canonical completed searches. -/
theorem splitRun_witnesses (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C)
    (hz : z ∈ support (splitRunAt prims A x)) : SelectionWitnesses x z.2 := by
  unfold splitRunAt SigningOneRunProof.splitGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hi : SelectionWitnesses x
      ((SigningOneRunProof.monitoredInit.1, fun _ => false), SigningOneRunProof.monitoredInit.2) := by
    intro e target ht
    change (none : Option Digest) = some target at ht
    cases ht
  have hset : SelectionWitnesses x setup.2 := by
    apply world_run_witnesses prims x _ _ hi setup
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
      have hm : SelectionWitnesses x middle.2 := by
        apply forger_run_witnesses prims x top _ setup.2 hset middle
        with_reducible exact hmiddle
      have hf : SelectionWitnesses x finished.2 := by
        apply world_run_witnesses prims x _ middle.2 hm finished
        with_reducible exact hfinished
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hf

open SigningDescentProof SigningCacheProof

/-- A supported hash computation replays under every extension of its completed cache. -/
theorem hash_run_eval (prims : Primitives) {α : Type} (oa : OracleComp HashSpec α)
    (initial completed cache : HashCache C) (value : α)
    (hr : (value, completed) ∈ support
      ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
        (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa)).run initial))
    (hle : completed ≤ cache) : E prims (answersOf cache) oa = value := by
  have hresolved := DeterministicSigning.resolves_of_run _ initial (value, completed) hr
  have heval := (hresolved.mono hle).eval
    (answersOf cache) (fun input answer ha => by simp [answersOf, ha])
  rw [E_eval]
  change simulateQ (r := Id) (fun input => answersOf cache (.hash input) : QueryImpl HashSpec Id) oa = value
  change simulateQ (r := Id) (answersOf cache : QueryImpl (Query C →ₒ HashOutput) Id)
    (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa) = value at heval
  rw [← QueryImpl.simulateQ_compose] at heval
  exact heval

/-- Any successful selected replay agrees with a previously installed target. -/
theorem SelectionWitness.selected_digest (prims : Primitives) (z : FinalState C)
    (target : Digest) (h : SelectionWitness z.keys z.cache z.state z.key target)
    (pair : Message × Randomness) (hsel : z.selected prims = some pair) :
    XmssSecurity.Concrete.CacheView.encodingHash (thView z.cache) z.keys.1 z.key pair = target := by
  obtain ⟨hprf, message, baseAnswer, randomness, encoding, answer, initial, completed,
    hb, hbase, hrun, hle, hanswer, ht⟩ := h
  have hgrind := hash_run_eval prims _ initial completed z.cache _ hrun hle
  cases htree : z.bottomTree prims with
  | none => simp [FinalState.selected, hb, htree] at hsel
  | some tree =>
    cases hsc : D prims z.answers (signCodeword z.keys.1 (tree.commitment z.key) z.key message
        (D prims z.answers (prfValue z.keys.2.1 (.randomizer bottomLayer z.key)))) with
    | none => simp [FinalState.selected, hb, htree, hsc] at hsel
    | some selected =>
      obtain ⟨randomness', encoding'⟩ := selected
      have hp : (message, randomness') = pair := by
        simpa [FinalState.selected, hb, htree, hsc] using hsel
      have hc := SigningGuessProof.signCodeword_some_commitment prims z.answers z.keys.1
        (tree.commitment z.key) z.key message _ _ hsc
      rw [D_signCodeword (prims := prims) _ _ _ _ _ hc.symm] at hsc
      change E prims (answersOf z.cache) (grind _ _ _ _
        (truncateHash (answersOf z.cache (.hash (randomizerInput _ _ _
          (D prims (answersOf z.cache) (prfValue _ _)) _)))) _ _) = _ at hsc
      rw [SigningGuessProof.cachedRandomizer_eq] at hsc
      simp only [answersOf, hbase, Option.getD_some] at hsc
      rw [hgrind] at hsc
      have hr : randomness = randomness' := congrArg (fun v => v.1) (Option.some.inj hsc)
      subst randomness'
      subst pair
      rw [← ht]
      have ha := hle hanswer
      rw [SigningLane2BridgeProof.messageInput_eq_partnerInput] at ha
      exact XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some ha

/-- The metadata signing state is the carried state after verification. -/
theorem splitRun_state (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C)
    (hz : z ∈ support (splitRunAt prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : z.1.1.2 = some (top, state, forgery)) : z.2.2.1.1 = state := by
  obtain ⟨start, middle, _, _, _, hstate, finished, hfinished, hf⟩ :=
    splitRun_subruns prims A x z (by with_reducible exact hz) top state forgery hm
  have hc := world_run_carried prims x _ middle.2 finished hfinished
  rw [← hf, hc, hstate]

/-- A signed key in the actual run already satisfies selection alignment for every forgery at it. -/
theorem splitRun_signed_selected (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C)
    (hz : z ∈ support (splitRunAt prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : z.1.1.2 = some (top, state, forgery)) (keyForgery : Forgery)
    (target : Digest) (hs : z.2.1.1.2.state.signed keyForgery.signature.leafIndex = some target)
    (pair : Message × Randomness)
    (hsel : (FinalState.mk x top state keyForgery z.2.1.1.1.1.1 false).selected prims = some pair) :
    target = XmssSecurity.Concrete.CacheView.encodingHash (thView z.2.1.1.1.1.1)
      x.1 keyForgery.signature.leafIndex pair := by
  have hw := splitRun_witnesses prims A x z (by with_reducible exact hz) _ _ hs
  rw [splitRun_state prims A x z (by with_reducible exact hz) top state forgery hm] at hw
  exact (hw.selected_digest prims _ target pair hsel).symm

/-- A canonical base call whose search succeeds in an extending cache records its key. -/
theorem world_base_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SplitState C)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s))
    (e : KeyIndex) (message : Message) (cache : HashCache C)
    (hle : r.2.1.1.1.1.1 ≤ cache)
    (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t)
    (hb : s.2.1.1.bound e = some message)
    (randomness : Randomness) (encoding : Encoding)
    (hsuccess : E prims (answersOf cache)
      (grind x.1 bottomLayer e (bytesLE 32 message)
        (truncateHash (answersOf cache (.hash (randomizerInput x.1 bottomLayer e
          (SigningGuessProof.cachedRandomizer x.2.1 cache e) (bytesLE 32 message)))))
        randomizerAttemptLimit 0) = some (randomness, encoding)) :
    ∃ target, Marked e target ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  cases hs : s.1.1.2.state.signed e with
  | some target =>
    exact ⟨target, Or.inr (world_signed prims x t e target s hs r hr)⟩
  | none =>
    have hstart := (world_cache_le prims x t s r hr).trans hle
    have hcall : HashCallAt (randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message)) t := by
      obtain ⟨input, hi, hc⟩ := hbase
      have hi' : randomizerInput x.1 bottomLayer e
          (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message) = input := by
        unfold baseInput at hi
        rw [hb] at hi
        exact Option.some.inj hi
      exact hi'.symm ▸ hc
    simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
      mem_support_bind_iff, support_map, Set.mem_image] at hr
    obtain ⟨called, hc, ground, hg, rfl⟩ := hr
    have hc' := hc
    simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc'
    obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc'
    obtain ⟨baseAnswer, hanswer⟩ := countImpl_hash_cached prims _ t hcall _ counted hcounted
    have ha : called.2.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message))) = some baseAnswer := by
      rw [← heq]
      exact hanswer
    rw [jointCachedExtra_base x (s.1.1.1, s.2) called.2 t e message baseAnswer hprf hbase hb ha] at hg
    obtain ⟨g, hgrind, hgstate⟩ := baseGrind_subrun x.1 e message baseAnswer _ ground hg
    have hgrow := keyed_run_cache_le (XmssSecurity.encodingInputLeafIndex? x.1) _ _ ground hg
    have hgle : g.2.1.1 ≤ cache := by
      rw [hgstate]
      exact hle
    have hraw := keyed_run_support (XmssSecurity.encodingInputLeafIndex? x.1) _ _ g hgrind
    have heval := hash_run_eval prims _ called.2.1.1.1 g.2.1.1 cache g.1 hraw hgle
    have hbaseFinal := hle (hgrow ha)
    rw [← SigningGuessProof.cachedRandomizer_stable x.2.1 s.1.1.1.1.1 cache e hstart hprf] at hsuccess
    simp only [answersOf, hbaseFinal, Option.getD_some] at hsuccess
    have hout : g.1 = some (randomness, encoding) := heval.symm.trans hsuccess
    have hunsigned : (queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
        s.1.1.2 (hashEntry ⟨t, called.1⟩)).state.signed e = none := by
      rw [SigningR1FixedProof.queryEntryStep_signed, hs]
    obtain ⟨answer, _, hmark⟩ := grind_unsigned x.1 e message (truncateHash baseAnswer)
      randomizerAttemptLimit 0 _ hunsigned g hgrind randomness encoding hout
    refine ⟨XmssSecurity.truncateHash answer, ?_⟩
    change Marked e (XmssSecurity.truncateHash answer) ground.2
    rw [← hgstate]
    exact hmark

/-- Replaying one random-oracle/PRG query from an extending completed cache is pure. -/
theorem roStep_replay (prims : Primitives) (t : (RoSpec C).Domain)
    (initial : HashCache C) (r : (RoSpec C).Range t × HashCache C)
    (hr : r ∈ support ((((Query C →ₒ HashOutput).randomOracle + prgAnswer (C := C) prims) t).run initial))
    (cache : HashCache C) (hle : r.2 ≤ cache) :
    (((Query C →ₒ HashOutput).randomOracle + prgAnswer (C := C) prims) t).run cache =
      pure (r.1, cache) := by
  rcases t with q | input
  · obtain ⟨_, hq, _⟩ := randomOracle_support q initial r hr
    exact QueryImpl.withCaching_run_some _ (hle hq)
  · change r ∈ support ((prgAnswer prims input).run initial) at hr
    unfold prgAnswer at hr ⊢
    rw [StateT.run_bind] at hr
    simp only [support_bind] at hr
    obtain ⟨step, hstep, hr⟩ := Set.mem_iUnion₂.mp hr
    simp only [StateT.run_pure, support_pure] at hr
    subst r
    rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hstep
    obtain ⟨_, hq, _⟩ := randomOracle_support _ initial step hstep
    change (do
      let key ← (hashAnswer prims (.streamKey input.2.1)).run cache
      pure (prims.aes.eval (truncateHash key.1) input.2.2, key.2)) = _
    rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h),
      QueryImpl.withCaching_run_some _ (hle hq), pure_bind]
    rfl

/-- A counted honest query can be replayed from any extension of its completed cache. -/
theorem count_ro_replay (prims : Primitives) (t : (RoSpec C).Domain)
    (initial : HashCache C × ℕ) (r : (RoSpec C).Range t × HashCache C × ℕ)
    (hr : r ∈ support ((countImpl prims (.inr (.inr t))).run initial))
    (cache : HashCache C) (hle : r.2.1 ≤ cache) (count : ℕ) :
    ∃ count', (r.1, cache, count') ∈ support
      ((countImpl prims (.inr (.inr t))).run (cache, count)) := by
  simp only [countImpl, SeedHitProof.withCount, StateT.run_mk, support_map] at hr ⊢
  obtain ⟨step, hstep, rfl⟩ := hr
  have he := roStep_replay prims t initial.1 step hstep cache hle
  refine ⟨count + SeedHitProof.signCost (.inr (.inr t)), (step.1, cache), ?_, rfl⟩
  change (step.1, cache) ∈ support
    ((((Query C →ₒ HashOutput).randomOracle + prgAnswer (C := C) prims) t).run cache)
  rw [he]
  simp

/-- Every actual world call grows the cache throughout an arbitrary source computation. -/
theorem world_run_cache_le (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    {α : Type} (source : OracleComp (WorldSpec C) α) (s : SplitState C)
    (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x) source).run s)) :
    s.1.1.1.1.1 ≤ r.2.1.1.1.1.1 := by
  exact SeedHitProof.support_simulateQ_inv _ (fun p : SplitState C => s.1.1.1.1.1 ≤ p.1.1.1.1.1)
    (fun t p hp r hr => hp.trans (world_cache_le prims x t p r hr)) source s le_rfl r hr

set_option backward.isDefEq.respectTransparency false

/-- The original counted call remains an actual subrun of the monitored world step. -/
theorem world_counted_step (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (s : SplitState C) (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) :
    ∃ counted, counted ∈ support ((countImpl prims t).run s.1.1.1.1) ∧
      counted.1 = r.1 ∧ counted.2.1 ≤ r.2.1.1.1.1.1 := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  have hgrow : called.2.1.1.1 ≤ ground.2.1.1 := by
    apply keyed_run_cache_le (XmssSecurity.encodingInputLeafIndex? x.1)
      (jointCachedExtra x.2.1 x.1 (s.1.1.1, s.2) t called.2)
      ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
        s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2) ground
    with_reducible exact hg
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc
  obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc
  exact ⟨counted, hcounted, by rw [← heq], by simpa only [← heq, ofRest] using hgrow⟩

/-- An actual honest world query can be repeated in the final cache without extra work. -/
theorem world_ro_replay (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (RoSpec C).Domain) (s : SplitState C)
    (r : (RoSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x (.inr (.inr t))).run s))
    (cache : HashCache C) (hle : r.2.1.1.1.1.1 ≤ cache) (count : ℕ) :
    ∃ count', (r.1, cache, count') ∈ support
      ((countImpl prims (.inr (.inr t))).run (cache, count)) := by
  obtain ⟨called, hc, hv, hcache⟩ := world_counted_step prims x (.inr (.inr t)) s r
    (by exact hr)
  rw [← hv]
  exact count_ro_replay prims t _ called hc cache (hcache.trans hle) count

/-- An honest computation of the actual split run has a counted replay in its completed cache. -/
theorem world_liftFree_replay (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    {α : Type} (source : OracleComp (RoSpec C) α) (s : SplitState C)
    (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      (SigningSecurityProof.liftFree source)).run s))
    (cache : HashCache C) (hle : r.2.1.1.1.1.1 ≤ cache) (count : ℕ) :
    ∃ count', (r.1, cache, count') ∈ support
      ((simulateQ (countImpl prims) (SigningSecurityProof.liftFree source)).run (cache, count)) := by
  induction source using OracleComp.inductionOn generalizing s r count with
  | pure value =>
    simp [SigningSecurityProof.liftFree, free] at hr
    subst r
    refine ⟨count, ?_⟩
    change (value, cache, count) ∈ support (pure (value, cache, count) : ProbComp _)
    simp
  | query_bind t next ih =>
    simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind, simulateQ_bind,
      StateT.run_bind, mem_support_bind_iff] at hr ⊢
    obtain ⟨step, hstep, htail⟩ := hr
    have hs : step ∈ support ((SigningReleasedLinkProof.world prims x (.inr (.inr t))).run s) := by
      rw [free] at hstep
      erw [liftComp_query, simulateQ_query] at hstep
      simp at hstep
      exact hstep
    have hstepLe : step.2.1.1.1.1.1 ≤ cache :=
      (world_run_cache_le prims x _ step.2 r htail).trans hle
    obtain ⟨count', hquery⟩ := world_ro_replay prims x t s step hs cache hstepLe count
    obtain ⟨count'', hnext⟩ := ih step.1 step.2 r htail hle count'
    refine ⟨count'', (step.1, cache, count'), ?_, hnext⟩
    rw [free]
    erw [liftComp_query, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact hquery

/-- Replayed honest handlers preserve the stored-tree witnesses in the actual cache. -/
theorem world_tsig_stored (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (t : (TsigSpec C).Domain) (st : TsigState C) (s : SplitState C)
    (hs : SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 st)
    (r : ((TsigSpec C).Range t × TsigState C) × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) (dealtOf x top) t).run st)).run s)) :
    SigningGuessProof.StoredTreeRuns prims x top r.2.1.1.1.1.1 r.1.2 := by
  have hle := world_run_cache_le prims x _ s r hr
  have hr' := hr
  rw [SigningGuessProof.signing_tsigOracles_free] at hr'
  obtain ⟨count, hcount⟩ := world_liftFree_replay prims x _ s r hr' r.2.1.1.1.1.1 le_rfl 0
  rw [← SigningGuessProof.signing_tsigOracles_free] at hcount
  exact SigningSelectionProof.gameOracles_storedTreeRuns prims x top (.inr t) st
    (r.2.1.1.1.1.1, 0) (SigningGuessProof.StoredTreeRuns.mono prims x top hle hs)
    (r.1, r.2.1.1.1.1.1, count) hcount

/-- Stored-tree provenance is an invariant of every actual adversary handler. -/
theorem forger_stored (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : SplitState C)
    (hs : SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 s.2.1.1)
    (r : (LocalSpec C + TsigSpec C).Range t × SplitState C)
    (hr : r ∈ support ((forger prims x top t).run s)) :
    SigningGuessProof.StoredTreeRuns prims x top r.2.1.1.1.1.1 r.2.2.1.1 := by
  simp only [forger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  cases t with
  | inl t =>
    simp only [SigningOpeningProof.openingOracles, StateT.run_mk, SigningCoreProof.flaggedOracles,
      Functor.map_map, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hw
    obtain ⟨answer, ha, rfl⟩ := hw
    exact SigningGuessProof.StoredTreeRuns.mono prims x top (world_run_cache_le prims x _ s answer ha) hs
  | inr t =>
    simp only [SigningOpeningProof.openingOracles, StateT.run_mk, SigningCoreProof.flaggedOracles,
      Functor.map_map, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hw
    obtain ⟨answer, ha, rfl⟩ := hw
    exact world_tsig_stored prims x top t s.2.1.1 s hs answer ha

theorem forger_run_stored (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : SplitState C)
    (hs : SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 s.2.1.1) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s)) :
    SigningGuessProof.StoredTreeRuns prims x top r.2.1.1.1.1.1 r.2.2.1.1 := by
  exact SeedHitProof.support_simulateQ_inv _
    (fun p : SplitState C => SigningGuessProof.StoredTreeRuns prims x top p.1.1.1.1.1 p.2.1.1)
    (fun t p hp r hr => forger_stored prims x top t p hp r hr) source s hs r hr

/-- An execution invariant holds before every retained occurrence. -/
theorem occurrence_before_inv {ι σ α : Type} {spec : OracleSpec ι}
    (V : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop)
    (hstep : ∀ t s, Inv s → ∀ r ∈ support ((V t).run s), Inv r.2)
    {t : spec.Domain} {before : σ} {after : spec.Range t × σ}
    {source : OracleComp spec α} {initial : σ} {result : α × σ}
    (h : QueryOccurrence V t before after source initial result) (hi : Inv initial) : Inv before := by
  induction h with
  | here => exact hi
  | later q next initial middle result hhead htail ih =>
    exact ih (hstep q initial hi middle hhead)

/-- A record established at a retained occurrence survives its actual continuation. -/
theorem occurrence_after_inv {ι σ α : Type} {spec : OracleSpec ι}
    (V : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop)
    (hstep : ∀ t s, Inv s → ∀ r ∈ support ((V t).run s), Inv r.2)
    {t : spec.Domain} {before : σ} {after : spec.Range t × σ}
    {source : OracleComp spec α} {initial : σ} {result : α × σ}
    (h : QueryOccurrence V t before after source initial result) (ha : Inv after.2) : Inv result.2 := by
  induction h with
  | here next result hhead htail =>
    exact SeedHitProof.support_simulateQ_inv V Inv hstep _ _ ha _ htail
  | later q next initial middle result hhead htail ih => exact ih

/-- A successful canonical signing computation necessarily runs the guarded base grind. -/
theorem world_codeword_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (e : KeyIndex) (message : Message) (commitment candidate : Digest) (s : SplitState C)
    (r : Option (Randomness × Encoding) × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      (SigningSecurityProof.liftFree (signCodeword x.1 commitment e message candidate))).run s))
    (randomness : Randomness) (encoding : Encoding) (hout : r.1 = some (randomness, encoding))
    (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hb : s.2.1.1.bound e = some message)
    (hcanonical : candidate = SigningGuessProof.cachedRandomizer x.2.1 r.2.1.1.1.1.1 e) :
    ∃ target, Marked e target ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  obtain ⟨count, hcount⟩ := world_liftFree_replay prims x _ s r hr r.2.1.1.1.1.1 le_rfl 0
  have hD : D prims (answersOf r.2.1.1.1.1.1)
      (signCodeword x.1 commitment e message candidate) = some (randomness, encoding) :=
    (run_liftFree prims _ _ (r.1, r.2.1.1.1.1.1, count) hcount _ (agrees_answersOf le_rfl)).symm.trans hout
  have hc := SigningGuessProof.signCodeword_some_commitment prims _ x.1 commitment e message _ _ hD
  rw [D_signCodeword (prims := prims) _ _ _ _ _ hc.symm, hcanonical] at hD
  change r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
    (freeHom (signCodeword x.1 commitment e message candidate))).run s) at hr
  rw [signCodeword, tweakable_bind, tweakable_oracleHash, MonadHom.mmap_bind] at hr
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨opened, hopened, hr⟩ := hr
  have hopenedGrow := world_run_cache_le prims x _ s opened hopened
  have hopenedCarried := world_run_carried prims x _ s opened hopened
  by_cases hbad : truncateHash opened.1 ≠ commitment
  · rw [if_pos hbad] at hr
    simp only [tweakable_pure, MonadHom.mmap_pure,
      simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr] at hout
    cases hout
  · simp only [hbad, ↓reduceIte, tweakable_bind, tweakable_oracleHash, MonadHom.mmap_bind,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨base, hbase, htail⟩ := hr
    have hbaseGrow := world_run_cache_le prims x _ opened.2 base hbase
    have htailGrow := world_run_cache_le prims x _ base.2 r htail
    have hprf' := SigningR1FixedProof.randomizerCached_mono hopenedGrow hprf
    have hb' : opened.2.2.1.1.bound e = some message := by rw [hopenedCarried]; exact hb
    have hcandidate : candidate = SigningGuessProof.cachedRandomizer x.2.1 opened.2.1.1.1.1.1 e :=
      hcanonical.trans (SigningGuessProof.cachedRandomizer_stable x.2.1 opened.2.1.1.1.1.1
        r.2.1.1.1.1.1 e (hbaseGrow.trans htailGrow) hprf').symm
    have hquery : base ∈ support ((SigningReleasedLinkProof.world prims x
        (.inr (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e candidate
          (bytesLE 32 message))))))).run opened.2) := by
      change base ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
        (SigningSecurityProof.liftFree (hashQuery (.hash (randomizerInput x.1 bottomLayer e candidate
          (bytesLE 32 message)))))).run opened.2) at hbase
      rw [SigningSecurityProof.liftFree, hashQuery, free] at hbase
      erw [liftComp_query, simulateQ_query] at hbase
      simpa using hbase
    have hcall : BaseCall x.1 e
        (SigningGuessProof.cachedRandomizer x.2.1 opened.2.1.1.1.1.1 e) opened.2.2.1.1
        (.inr (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e candidate (bytesLE 32 message)))))) := by
      refine ⟨randomizerInput x.1 bottomLayer e candidate (bytesLE 32 message), ?_, Or.inr rfl⟩
      simp only [baseInput, hb', Option.map_some, hcandidate]
    obtain ⟨target, hmarked⟩ := world_base_marked prims x
      (.inr (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e candidate (bytesLE 32 message))))))
      opened.2 base hquery e message
      r.2.1.1.1.1.1 htailGrow hprf' hcall hb' randomness encoding hD
    exact ⟨target, world_run_marked prims x e target _ base.2 hmarked r htail⟩

private theorem run_liftM_comp {ι σ α : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (s : σ) :
    (liftM oa : StateT σ (OracleComp spec) α).run s = (fun a => (a, s)) <$> oa := by
  rfl

/-- A successful cached-or-new bottom request retains its actual construction before signing. -/
theorem world_bottomOnce_tree (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (st : TsigState C) (s : SplitState C)
    (hs : SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 st)
    (r : (Option BottomTree × TsigState C) × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      ((bottomOnce (dealtOf x top) b).run st)).run s))
    (tree : BottomTree) (hout : r.1.1 = some tree) :
    ∃ (initial : HashCache C × ℕ) (built : Option TreeOutput × HashCache C × ℕ),
      built ∈ support ((simulateQ (countImpl prims)
        (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b)))).run initial) ∧
      built.1 = some (.bottom tree) ∧ built.2.1 ≤ r.2.1.1.1.1.1 := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases hstored : st.trees b with
  | some stored =>
    simp only [hstored, StateT.run_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hs b tree (hstored.trans (congrArg some hout))
  | none =>
    simp only [hstored, StateT.run_bind, run_liftM_comp, bind_map_left,
      StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨built, hbuilt, hr⟩ := hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr] at hout ⊢
    clear hr
    change built ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      ((SigningGuessProof.receiptDealt x top).bottom b)).run s) at hbuilt
    rw [SigningGuessProof.receiptDealt_bottom] at hbuilt
    simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hbuilt
    obtain ⟨raw, hraw, rfl⟩ := hbuilt
    obtain ⟨count, hcount⟩ := world_liftFree_replay prims x _ s raw (by with_reducible exact hraw) raw.2.1.1.1.1.1 le_rfl 0
    refine ⟨(raw.2.1.1.1.1.1, 0), (raw.1, raw.2.1.1.1.1.1, count), (by with_reducible exact hcount), ?_, le_rfl⟩
    cases ho : raw.1 with
    | none => simp [ho] at hout
    | some value =>
      cases value with
      | top _ => simp [ho] at hout
      | bottom _ => simpa [ho] using hout

/-- An accepted codeword after an actual bottom construction is canonical unless a commitment opens twice. -/
theorem world_tree_codeword_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (e : KeyIndex) (message : Message) (candidate : Digest)
    (tree : BottomTree) (initial : HashCache C × ℕ) (built : Option TreeOutput × HashCache C × ℕ)
    (hbuilt : built ∈ support ((simulateQ (countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1
        top (.bottom (treeOf e))))).run initial))
    (hbtree : built.1 = some (.bottom tree)) (s : SplitState C)
    (hble : built.2.1 ≤ s.1.1.1.1.1) (hb : s.2.1.1.bound e = some message)
    (r : Option (Randomness × Encoding) × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      (SigningSecurityProof.liftFree (signCodeword x.1 (tree.commitment e) e message candidate))).run s))
    (randomness : Randomness) (encoding : Encoding) (hout : r.1 = some (randomness, encoding))
    (htop : TopFacts prims (answersOf r.2.1.1.1.1.1) x.2.1 x.1 top)
    (hn : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1.1.1.1.1) :
    ∃ target, Marked e target ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  have hgrow := world_run_cache_le prims x _ s r hr
  have htreeFinal := hble.trans hgrow
  obtain ⟨hterms, canonicalOutput, hcanonical⟩ := SigningGuessProof.run_bottom_commitment_cached
    prims x.2.1 x.1 top e initial built (by with_reducible exact hbuilt) (answersOf r.2.1.1.1.1.1) (agrees_answersOf htreeFinal)
  have hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e := by
    intro T
    obtain ⟨answer, ha⟩ := hterms T
    exact ⟨answer, hble ha⟩
  have ht := SigningGuessProof.run_bottom_commitment_eq prims x.2.1 x.1 top e initial built (by with_reducible exact hbuilt)
    (answersOf r.2.1.1.1.1.1) (agrees_answersOf htreeFinal) htop tree hbtree
  obtain ⟨count, hcount⟩ := world_liftFree_replay prims x _ s r hr r.2.1.1.1.1.1 le_rfl 0
  obtain ⟨candidateOutput, hcandidate⟩ := SigningGuessProof.caches_signCodeword prims x.1
    (tree.commitment e) e message candidate (r.2.1.1.1.1.1, 0) (r.1, r.2.1.1.1.1.1, count) hcount
  change r.2.1.1.1.1.1 (.hash (commitmentInput x.1 e candidate)) = some candidateOutput at hcandidate
  have hd := (run_liftFree prims _ _ (r.1, r.2.1.1.1.1.1, count) hcount _
    (agrees_answersOf le_rfl)).symm.trans hout
  have hc := SigningGuessProof.signCodeword_some_commitment prims _ x.1 (tree.commitment e)
    e message candidate _ hd
  have hcanonical' := htreeFinal hcanonical
  rw [SigningGuessProof.cachedRandomizer_eq] at hcanonical' ht
  have heq : candidate = SigningGuessProof.cachedRandomizer x.2.1 r.2.1.1.1.1.1 e := by
    by_contra hne
    apply hn
    refine ⟨e, candidate, canonicalOutput, candidateOutput,
      SigningR1FixedProof.randomizerCached_mono hgrow hprf, hcanonical', hcandidate, hne, ?_⟩
    have he := hc.trans ht
    simpa only [answersOf, hcandidate, hcanonical', Option.getD_some] using he
  exact world_codeword_marked prims x e message (tree.commitment e) candidate s r hr
    randomness encoding hout hprf hb heq

/-- The generated top tree has a counted construction already resolved by this cache. -/
def TopRun (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (cache : HashCache C) : Prop :=
  ∃ initial built, built ∈ support ((simulateQ (countImpl prims)
    (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top))).run initial) ∧
    built.1 = some (.top top) ∧ built.2.1 ≤ cache

theorem TopRun.mono {prims : Primitives} {x : SigningSecurityProof.Keys3 C} {top : TopTree}
    {cache cache' : HashCache C} (h : TopRun prims x top cache) (hle : cache ≤ cache') :
    TopRun prims x top cache' := by
  obtain ⟨initial, built, hr, ht, hc⟩ := h
  exact ⟨initial, built, (by with_reducible exact hr), ht, hc.trans hle⟩

theorem TopRun.facts {prims : Primitives} {x : SigningSecurityProof.Keys3 C} {top : TopTree}
    {cache : HashCache C} (h : TopRun prims x top cache) :
    TopFacts prims (answersOf cache) x.2.1 x.1 top := by
  obtain ⟨initial, built, hr, ht, hc⟩ := h
  have hv := run_liftFree prims _ initial built (by with_reducible exact hr) (answersOf cache) (agrees_answersOf hc)
  rw [ht] at hv
  obtain ⟨generated, hgen, hchain, hroot⟩ :=
    D_refTop (prims := prims) (h := answersOf cache) x.1 x.2.1 emptyTop
  have he : generated = top := TreeOutput.top.inj (Option.some.inj (hgen.symm.trans hv.symm))
  rw [← he]
  exact ⟨hchain, hroot⟩

/-- Every successful actual round-two handler records its key unless a commitment opens twice. -/
theorem world_round2_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (s : SplitState C)
    (htop : TopRun prims x top s.1.1.1.1.1)
    (hstored : SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 s.2.1.1)
    (r : ((Option (ChainIndex → Option Digest)) × TsigState C) × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) (dealtOf x top)
        (.round2 i J e message parts)).run s.2.1.1)).run s))
    (values : ChainIndex → Option Digest) (hout : r.1.1 = some values)
    (hn : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1.1.1.1.1) :
    ∃ target, Marked e target ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · simp only [StateT.run_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr] at hout
    cases hout
  · rename_i hguard
    have hb : s.2.1.1.bound e = some message := by tauto
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨rTree, hTree, hr⟩ := hr
    have hTreeGrow := world_run_cache_le prims x _ s rTree hTree
    have hTreeCarried := world_run_carried prims x _ s rTree hTree
    cases ht : rTree.1.1 with
    | none =>
      simp only [ht, StateT.run_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      rw [hr] at hout
      cases hout
    | some tree =>
      simp only [ht, StateT.run_bind, run_liftM_comp, bind_map_left, simulateQ_bind,
        StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨own, hown, hr⟩ := hr
      obtain ⟨selected, hselected, hfinish⟩ := hr
      have hownGrow := world_run_cache_le prims x _ rTree.2 own hown
      have hownCarried := world_run_carried prims x _ rTree.2 own hown
      have hfinishGrow := world_run_cache_le prims x _ selected.2 r hfinish
      cases hselectedOut : selected.1 with
      | none =>
        simp only [hselectedOut, StateT.run_pure, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at hfinish
        rw [hfinish] at hout
        cases hout
      | some selectedValues =>
        simp only [signRound2With, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hselected
        obtain ⟨code, hcode, hafter⟩ := hselected
        have hcodeGrow := world_run_cache_le prims x _ own.2 code hcode
        have hafterGrow := world_run_cache_le prims x _ code.2 selected hafter
        cases hcodeOut : code.1 with
        | none =>
          simp only [hcodeOut, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hafter
          rw [hafter] at hselectedOut
          cases hselectedOut
        | some selection =>
          obtain ⟨randomness, encoding⟩ := selection
          obtain ⟨initial, built, hbuilt, hbtree, hble⟩ :=
            world_bottomOnce_tree prims x top (treeOf e) s.2.1.1 s hstored rTree (by with_reducible exact hTree) tree ht
          have hbOwn : own.2.2.1.1.bound e = some message := by
            rw [hownCarried, hTreeCarried]
            exact hb
          have htopCode := (htop.mono ((hTreeGrow.trans hownGrow).trans hcodeGrow)).facts
          have hnCode : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 code.2.1.1.1.1.1 :=
            fun h => hn (SigningGuessProof.alternativeCommitment_mono x.2.1 x.1 _ _
              (hafterGrow.trans hfinishGrow) h)
          obtain ⟨target, hmark⟩ := world_tree_codeword_marked prims x top e message
            (combine J (Function.update parts i own.1)) tree initial built (by with_reducible exact hbuilt) hbtree own.2
            (hble.trans hownGrow) hbOwn code hcode randomness encoding hcodeOut htopCode hnCode
          have hmarkSelected := world_run_marked prims x e target _ code.2 hmark selected hafter
          exact ⟨target, world_run_marked prims x e target _ selected.2 hmarkSelected r hfinish⟩

theorem forger_cache_le (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : SplitState C)
    (r : (LocalSpec C + TsigSpec C).Range t × SplitState C)
    (hr : r ∈ support ((forger prims x top t).run s)) : s.1.1.1.1.1 ≤ r.2.1.1.1.1.1 := by
  simp only [forger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact world_run_cache_le prims x _ s w hw

theorem forger_run_cache_le (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : SplitState C)
    (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s)) : s.1.1.1.1.1 ≤ r.2.1.1.1.1.1 := by
  exact SeedHitProof.support_simulateQ_inv _ (fun p : SplitState C => s.1.1.1.1.1 ≤ p.1.1.1.1.1)
    (fun t p hp r hr => hp.trans (forger_cache_le prims x top t p r hr)) source s le_rfl r hr

/-- The full signing handler inherits the actual round-two marking fact. -/
theorem forger_round2_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (s : SplitState C)
    (htop : TopRun prims x top s.1.1.1.1.1)
    (hstored : SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 s.2.1.1)
    (values : ChainIndex → Option Digest) (after : SplitState C)
    (hr : (some values, after) ∈ support ((forger prims x top (.inr (.round2 i J e message parts))).run s))
    (hn : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 after.1.1.1.1.1) :
    ∃ target, Marked e target ((after.1.1.1.1.1, after.1.1.2), after.1.2) := by
  simp only [forger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, heq⟩ := hr
  simp only [SigningOpeningProof.openingOracles, StateT.run_mk, SigningCoreProof.flaggedOracles,
    Functor.map_map, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hw
  obtain ⟨answer, ha, rfl⟩ := hw
  have hout : answer.1.1 = some values := congrArg Prod.fst heq
  have hcache : answer.2.1.1.1.1.1 = after.1.1.1.1.1 := congrArg (fun p => p.2.1.1.1.1.1) heq
  have hn' : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 answer.2.1.1.1.1.1 := by rwa [hcache]
  obtain ⟨target, hmark⟩ := world_round2_marked prims x top i J e message parts s htop hstored
    answer ha values hout hn'
  refine ⟨target, ?_⟩
  have hstate := congrArg (fun p => p.2.1) heq
  change answer.2.1 = after.1 at hstate
  rw [← hstate]
  exact hmark

/-- Every ledger addition on the actual adversary execution marks its key, outside commitment collisions. -/
theorem forger_run_released_marked (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (s : SplitState C) (htop : TopRun prims x top s.1.1.1.1.1)
    (hstored : SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 s.2.1.1)
    (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s))
    (e : KeyIndex) (message : Message) (i : C.Party)
    (hi : (e, message, i) ∉ s.2.1.1.released) (ho : (e, message, i) ∈ r.2.2.1.1.released)
    (hn : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1.1.1.1.1) :
    ∃ target, Marked e target ((r.2.1.1.1.1.1, r.2.1.1.2), r.2.1.2) := by
  obtain ⟨J, parts, values, before, after, hocc⟩ :=
    forger_release_occurrence prims x top source s r hr e message i hi ho
  have ht : TopRun prims x top before.1.1.1.1.1 := occurrence_before_inv _
    (fun p : SplitState C => TopRun prims x top p.1.1.1.1.1)
    (fun t p hp r hr => hp.mono (forger_cache_le prims x top t p r hr)) hocc htop
  have hs : SigningGuessProof.StoredTreeRuns prims x top before.1.1.1.1.1 before.2.1.1 :=
    occurrence_before_inv _
      (fun p : SplitState C => SigningGuessProof.StoredTreeRuns prims x top p.1.1.1.1.1 p.2.1.1)
      (fun t p hp r hr => forger_stored prims x top t p hp r hr) hocc hstored
  have hle : after.1.1.1.1.1 ≤ r.2.1.1.1.1.1 := occurrence_after_inv _
    (fun p : SplitState C => after.1.1.1.1.1 ≤ p.1.1.1.1.1)
    (fun t p hp r hr => hp.trans (forger_cache_le prims x top t p r hr)) hocc le_rfl
  obtain ⟨target, hm⟩ := forger_round2_marked prims x top i J e message parts before ht hs values after
    hocc.head_support (fun h => hn (SigningGuessProof.alternativeCommitment_mono x.2.1 x.1 _ _ hle h))
  refine ⟨target, occurrence_after_inv _
    (fun p : SplitState C => Marked e target ((p.1.1.1.1.1, p.1.1.2), p.1.2))
    (fun t p hp r hr => forger_marked prims x top t e target p hp r hr) hocc hm⟩

/-- Every released ledger key in the actual split run has a persistent mark outside commitment collisions. -/
theorem splitRun_released_marked (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C)
    (hz : z ∈ support (splitRunAt prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hmeta : z.1.1.2 = some (top, state, forgery))
    (e : KeyIndex) (message : Message) (i : C.Party) (hrel : (e, message, i) ∈ state.released)
    (hn : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1) :
    ∃ target, Marked e target ((z.2.1.1.1.1.1, z.2.1.1.2), z.2.1.2) := by
  unfold splitRunAt SigningOneRunProof.splitGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hs := world_run_carried prims x _ _ setup (by with_reducible exact hsetup)
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hmeta
    cases hmeta
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz] at hmeta
      cases hmeta
    | top actualTop =>
      simp only [hout, StateT.run_bind, getCarried, StateT.run_mk, pure_bind,
        mem_support_bind_iff] at hz
      obtain ⟨middle, hmiddle, finished, hfinished, hz⟩ := hz
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      have hf := SigningSelectionProof.tsigFinishLogged_state (dealtOf x actualTop)
        middle.2.2.2.1 middle.1 middle.2.2.1.1 finished.1
        (by
          apply support_simulateQ_run'_subset (SigningReleasedLinkProof.world prims x) _ middle.2
          rw [StateT.run'_eq, support_map]
          exact ⟨finished, (by with_reducible exact hfinished), rfl⟩)
      rw [hz] at hmeta hn ⊢
      have he : (middle.2.2.1.1, middle.1) = (state, forgery) := by
        rw [← hf]
        exact congrArg Prod.snd (Option.some.inj hmeta)
      have hstate := congrArg Prod.fst he
      have hfinishedGrow := world_run_cache_le prims x _ middle.2 finished
        (by with_reducible exact hfinished)
      have hnMiddle : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 middle.2.1.1.1.1.1 :=
        fun h => hn (SigningGuessProof.alternativeCommitment_mono x.2.1 x.1 _ _ hfinishedGrow h)
      rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
          (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
          SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
        referenceTree_φ _ _ _ _] at hsetup
      obtain ⟨count, hcount⟩ := world_liftFree_replay prims x _ _ setup
        (by with_reducible exact hsetup) setup.2.1.1.1.1.1 le_rfl 0
      have htop : TopRun prims x actualTop setup.2.1.1.1.1.1 :=
        ⟨(setup.2.1.1.1.1.1, 0), (setup.1, setup.2.1.1.1.1.1, count),
          (by with_reducible exact hcount), hout, le_rfl⟩
      have hstored : SigningGuessProof.StoredTreeRuns prims x actualTop setup.2.1.1.1.1.1 setup.2.2.1.1 := by
        rw [hs]
        simp [SigningGuessProof.StoredTreeRuns, SigningCoreProof.tsigInit, SigningOneRunProof.monitoredInit]
      have hi : (e, message, i) ∉ setup.2.2.1.1.released := by
        rw [hs]
        simp [SigningCoreProof.tsigInit, SigningOneRunProof.monitoredInit]
      obtain ⟨target, hm⟩ := forger_run_released_marked prims x actualTop _ setup.2 htop hstored middle
        (by with_reducible exact hmiddle) e message i hi (by rw [hstate]; exact hrel) hnMiddle
      exact ⟨target, world_run_marked prims x e target _ middle.2 hm finished
        (by with_reducible exact hfinished)⟩

/-- The original released-selection alignment, for every released key of the same actual run. -/
theorem releasedSelectionAlignment (prims : Primitives) : ReleasedSelectionAlignment prims (C := C) := by
  intro A x z hz top state forgery hmeta keyForgery message i hrel selected hsel
  by_cases hflag : z.2.1.2 keyForgery.signature.leafIndex = true
  · exact Or.inl hflag
  by_cases halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1
  · exact Or.inr (Or.inl halt)
  obtain ⟨target, hm⟩ := splitRun_released_marked prims A x z (by with_reducible exact hz)
    top state forgery hmeta keyForgery.signature.leafIndex message i hrel halt
  rcases hm with hm | hm
  · exact (hflag hm).elim
  have he := splitRun_signed_selected prims A x z (by with_reducible exact hz)
    top state forgery hmeta keyForgery target hm selected hsel
  exact Or.inr (Or.inr (he ▸ hm))

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.grind_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms grind_unsigned

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.world_newly_signed_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_newly_signed_witness

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.world_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_witnesses

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.splitRun_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitRun_witnesses

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.SelectionWitness.selected_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SelectionWitness.selected_digest

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.world_liftFree_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_liftFree_replay

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.forger_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forger_stored

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.world_codeword_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_codeword_marked

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.world_round2_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_round2_marked

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.forger_run_released_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forger_run_released_marked

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.splitRun_released_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitRun_released_marked

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedAlignProof.releasedSelectionAlignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms releasedSelectionAlignment

end ThresholdLeanXmssSecurity.SigningReleasedAlignProof
