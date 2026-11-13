import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRelease

/-! # Local trigger and control synchronization

The explicit no-hit branch aligns the cached grind and trace update. Chain
preloads either appear in the visible cache or expose an unrevealed candidate.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] hiddenCandidate grind SigningFlatEagerProof.baseGrind

/-- Both actual hash routes carry exactly the same base-input predicate. -/
theorem baseCall_hash_route (P : PublicParameter) (e : KeyIndex) (rho : Digest)
    (signing : TsigState C) (input : HashInput) (call : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input call) :
    SigningFlatProof.BaseCall P e rho signing call =
      SigningFlatProof.BaseCall P e rho signing (.inr (.inr (.inl (.hash input)))) := by
  apply propext
  rw [baseCall_hash_iff]
  constructor
  · rintro ⟨other, hb, hc⟩
    have he : other = input := by
      rcases hcall with rfl | rfl <;> rcases hc with h | h <;> cases h <;> rfl
    subst other
    obtain ⟨message, hm, hi⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨message, hm, hi.symm⟩
  · rintro ⟨message, hm, hi⟩
    refine ⟨input, ?_, hcall⟩
    simp only [SigningFlatProof.baseInput, hm, Option.map_some, ← hi]

theorem baseCall_hashAt_iff (P : PublicParameter) (e : KeyIndex) (rho : Digest)
    (signing : TsigState C) (input : HashInput) (call : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input call) :
    SigningFlatProof.BaseCall P e rho signing call ↔
      ∃ message, signing.bound e = some message ∧
        input = randomizerInput P bottomLayer e rho (bytesLE 32 message) := by
  rw [baseCall_hash_route P e rho signing input call hcall]
  exact baseCall_hash_iff P e rho signing input

/-- Base calls depend only on the authorization map, including when the two
signing states have different memoized tree stores. -/
theorem baseCall_bound_congr (P : PublicParameter) (e : KeyIndex) (rho : Digest)
    (signing signing' : TsigState C) (hbound : signing.bound = signing'.bound)
    (call : (WorldSpec C).Domain) :
    SigningFlatProof.BaseCall P e rho signing call =
      SigningFlatProof.BaseCall P e rho signing' call := by
  unfold SigningFlatProof.BaseCall SigningFlatProof.baseInput
  rw [hbound]

/-- One-step port of `runSource_hashInput_ready`: the input branch supplies
no-hit directly, without a premise about a supported continuation. -/
theorem hashInput_ready_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (input : HashInput) (call : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input call) (source : SourceState C)
    (data : DeferredState C) (actual : HashCache C)
    (hopening : OpeningRelation seeds s source data actual)
    (hno : ∀ k, hiddenCandidate P input = some (k, s k) → source.revealed k ≠ none)
    (e : KeyIndex) (hactual : SigningGuessProof.RandomizerCached seeds actual e)
    (hbase : SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds actual e)
      source.signing call) :
    SigningGuessProof.RandomizerCached seeds data.cache e := by
  apply hopening.released e
  apply hno
  obtain ⟨message, _, hi⟩ := (baseCall_hashAt_iff P e _ source.signing input call hcall).mp hbase
  rw [hi, hiddenCandidate_randomizerInput, hopening.actualValue e hactual]

/-- One-step port of `runSource_hashInput_trigger_iff`. -/
theorem trigger_iff_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (input : HashInput) (call otherCall : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input call)
    (hotherCall : SigningFlatProof.HashCallAt input otherCall) (source : SourceState C)
    (data : DeferredState C) (actual : HashCache C) (signing : TsigState C)
    (hcache : CacheRelation P seeds s data actual)
    (hopening : OpeningRelation seeds s source data actual)
    (hbound : source.signing.bound = signing.bound)
    (hno : ∀ k, hiddenCandidate P input = some (k, s k) → source.revealed k ≠ none)
    (e : KeyIndex) :
    (SigningGuessProof.RandomizerCached seeds actual e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds actual e)
        source.signing call) ↔
    (SigningGuessProof.RandomizerCached seeds data.cache e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds data.cache e)
        signing otherCall) := by
  constructor
  · rintro ⟨ha, hb⟩
    have hc := hashInput_ready_step P seeds s input call hcall source data actual hopening hno e ha hb
    refine ⟨hc, ?_⟩
    rw [baseCall_hashAt_iff P e _ source.signing input call hcall] at hb
    rw [baseCall_hashAt_iff P e _ signing input otherCall hotherCall]
    rwa [hbound, (hcache.randomizer e hc).2] at hb
  · rintro ⟨hc, hb⟩
    obtain ⟨ha, hv⟩ := hcache.randomizer e hc
    refine ⟨ha, ?_⟩
    rw [baseCall_hashAt_iff P e _ signing input otherCall hotherCall] at hb
    rw [baseCall_hashAt_iff P e _ source.signing input call hcall]
    rwa [hbound, hv]

theorem hashInput_not_suspended (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (input : HashInput) (source : SourceState C)
    (data : DeferredState C) (hreleased : ReleasedPending P s source data)
    (hno : ∀ k, hiddenCandidate P input = some (k, s k) → source.revealed k ≠ none) :
    ¬SuspendedQuery P seeds s data (.hash input) := by
  intro h
  obtain ⟨k, hk, hr⟩ := suspendedHash_candidate P seeds s source data hreleased input h
  exact hno k hk hr

/-- Every private preload is an installed chain input. -/
theorem realCache_some_chain (x : Keys3 C) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (query : Query C) (value : HashOutput) (h : realCache x s pads noise query = some value) :
    ∃ edge, query = .hash ((chainPending edge).input x.1 (s (chainPending edge).key)) := by
  cases query <;> simp only [realCache, embedHashCache, reduceCtorEq] at h
  case hash input =>
    change chainTableCache x.1 (installed s pads noise).2 (noiseHigh noise) input = some value at h
    unfold chainTableCache at h
    split at h
    · rename_i he
      obtain ⟨edge, hedge⟩ := he
      exact ⟨edge, congrArg Query.hash (hedge.symm.trans (installed_input x s pads noise edge))⟩
    · cases h

/-- On the non-hit branch, a raw hash is unsuspended; a visible miss is quiet. -/
theorem hash_dichotomy (x : Keys3 C) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (source : SourceState C) (data : DeferredState C) (actual : HashCache C)
    (hcache : CacheRelation x.1 x.2.1 s data actual)
    (hreleased : ReleasedPending x.1 s source data)
    (hfrontier : ∀ edge, data.pending (chainPending edge) = none →
      source.revealed (chainPending edge).key = none) (input : HashInput) :
    (∃ k, hiddenCandidate x.1 input = some (k, s k) ∧ source.revealed k = none) ∨
    (¬SuspendedQuery x.1 x.2.1 s data (.hash input) ∧
      ((∃ value, actual (.hash input) = some value) ∨ Quiet x s pads noise (.hash input))) := by
  by_cases hhit : ∃ k, hiddenCandidate x.1 input = some (k, s k) ∧ source.revealed k = none
  · exact Or.inl hhit
  have hno : ∀ k, hiddenCandidate x.1 input = some (k, s k) → source.revealed k ≠ none :=
    fun k hk hr => hhit ⟨k, hk, hr⟩
  refine Or.inr ⟨hashInput_not_suspended x.1 x.2.1 s input source data hreleased hno, ?_⟩
  cases hv : actual (.hash input) with
  | some value => exact Or.inl ⟨value, rfl⟩
  | none =>
    refine Or.inr ⟨?_, ?_⟩
    · exact not_isSlot_hash x input
    · cases hp : realCache x s pads noise (.hash input) with
      | none => rfl
      | some value =>
        obtain ⟨edge, hedge⟩ := realCache_some_chain x s pads noise (.hash input) value hp
        have hi := Query.hash.inj hedge
        have hr := hno (chainPending edge).key (hi ▸ PendingInput.hiddenCandidate x.1 _ _)
        cases he : data.pending (chainPending edge) with
        | none => exact (hr (hfrontier edge he)).elim
        | some answer =>
          have ha := hcache.pending (chainPending edge) answer he
          rw [← hi, hv] at ha
          cases ha

theorem _root_.ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.SyncFields.mark (x : Keys3 C) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (h : SyncFields x s pads noise g rest a (src, st)) (mark : Bool) :
    SyncFields x s pads noise g rest a (src, ((st.1.1, mark), st.2)) := by
  exact {
    corrupt := h.corrupt, bound := h.bound, released := h.released,
    exposed := h.exposed, candidates := h.candidates, flag := h.flag,
    reveal := h.reveal, releasedPending := h.releasedPending, opening := h.opening,
    pendingValid := h.pendingValid, allocated := h.allocated, virtualSeen := h.virtualSeen,
    compilerBound := h.compilerBound, trace := h.trace, bad := h.bad, share := h.share,
    restAgree := h.restAgree, restFree := h.restFree, realPrivate := h.realPrivate,
    frontier := h.frontier, candidatesPaid := h.candidatesPaid, doneCached := h.doneCached }

theorem _root_.ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.LocalFrame.trans {x : Keys3 C} {a a' a'' : RealState C}
    {b b' b'' : SourceState C × CompState C}
    (h : LocalFrame x a a' b b') (h' : LocalFrame x a' a'' b' b'') :
    LocalFrame x a a'' b b'' := by
  exact ⟨h'.realSigning.trans h.realSigning, h'.realExposed.trans h.realExposed,
    h.visible.trans h'.visible, h'.signing.trans h.signing, h'.trees.trans h.trees,
    h'.exposed.trans h.exposed, h'.allocated.trans h.allocated,
    h'.pending.trans h.pending, h'.virtual.trans h.virtual, h.cache.trans h'.cache,
    fun k hk => (h'.revealed k hk).trans (h.revealed k hk)⟩


/-- The flat trigger ignores counters, logs and the hidden-hit flag. -/
theorem cachedExtra_at (P : PublicParameter) (seeds : C.Term → HashOutput)
    (before after : SigningFlatProof.FlatState C) (input : HashInput)
    (call : (WorldSpec C).Domain) (hroute : SigningFlatProof.HashCallAt input call)
    (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached seeds before.1.1.1 e)
    (hcall : SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds before.1.1.1 e)
      before.2.1 call)
    (hm : before.2.1.bound e = some message) :
    SigningR1FixedProof.cachedExtra seeds P before call after =
      match after.1.1.1 (.hash input) with
      | some answer => SigningFlatEagerProof.baseGrind P e message answer
      | none => pure () := by
  have base : ∃ e, SigningFlatProof.BaseCall P e
      (SigningGuessProof.cachedRandomizer seeds before.1.1.1 e) before.2.1
      call := ⟨e, hcall⟩
  have chosen := SigningR1FixedProof.baseCall_key_eq base.choose_spec hcall
  obtain ⟨m, hb, hi⟩ := (baseCall_hashAt_iff P e _ before.2.1 input call hroute).mp hcall
  have he : m = message := Option.some.inj (hb.symm.trans hm)
  subst m
  have hc : after.1.1.1 (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds before.1.1.1 e) (bytesLE 32 message))) =
      after.1.1.1 (.hash input) := by rw [hi]
  rw [SigningR1FixedProof.cachedExtra, if_pos ⟨e, hprf, hcall⟩,
    SigningFlatEagerProof.grindExtra, dif_pos base, chosen]
  simp only [hm, hc]
  cases after.1.1.1 (.hash input) <;> rfl

/-- Equal triggering data produces the same cached-extra program. The
post-read premise concerns only the raw input that has just been answered. -/
theorem cachedExtra_sync (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (input : HashInput) (call otherCall : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input call)
    (hotherCall : SigningFlatProof.HashCallAt input otherCall) (source : SourceState C)
    (data : DeferredState C) (before after otherBefore otherAfter : SigningFlatProof.FlatState C)
    (hsource : before.2.1.bound = source.signing.bound) (hdata : otherBefore.1.1.1 = data.cache)
    (hcache : CacheRelation P seeds s data before.1.1.1)
    (hopening : OpeningRelation seeds s source data before.1.1.1)
    (hbound : source.signing.bound = otherBefore.2.1.bound)
    (hno : ∀ k, hiddenCandidate P input = some (k, s k) → source.revealed k ≠ none)
    (hpost : after.1.1.1 (.hash input) = otherAfter.1.1.1 (.hash input)) :
    SigningR1FixedProof.cachedExtra seeds P before call after =
      SigningR1FixedProof.cachedExtra seeds P otherBefore otherCall otherAfter := by
  have ht (e : KeyIndex) := trigger_iff_step P seeds s input call otherCall hcall hotherCall
    source data before.1.1.1 otherBefore.2.1 hcache hopening hbound hno e
  rw [← hdata] at ht
  simp only [baseCall_bound_congr P _ _ source.signing before.2.1 hsource.symm call] at ht
  by_cases h : ∃ e, SigningGuessProof.RandomizerCached seeds before.1.1.1 e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds before.1.1.1 e)
        before.2.1 call
  · obtain ⟨e, hp, hb⟩ := h
    obtain ⟨hc, hd⟩ := (ht e).mp ⟨hp, hb⟩
    obtain ⟨message, hm, _⟩ := (baseCall_hashAt_iff P e _ before.2.1 input call hcall).mp hb
    have hm' : otherBefore.2.1.bound e = some message := by rw [← hbound, ← hsource]; exact hm
    rw [cachedExtra_at P seeds before after input call hcall e message hp hb hm,
      cachedExtra_at P seeds otherBefore otherAfter input otherCall hotherCall e message hc hd hm', hpost]
  · have h' : ¬∃ e, SigningGuessProof.RandomizerCached seeds otherBefore.1.1.1 e ∧
        SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds otherBefore.1.1.1 e)
          otherBefore.2.1 otherCall := by
      rintro ⟨e, he⟩
      exact h ⟨e, (ht e).mpr he⟩
    simp only [SigningR1FixedProof.cachedExtra, if_neg h, if_neg h']

/-- Deterministic replay of a grind depends only on its message-trial cells.
This is the cache-relative form of the recursion in `relTriple_grind`. -/
theorem grind_eval_sync (P : PublicParameter) (actual cache : HashCache C)
    (h : ∀ i, IsMsg i → actual (.hash i) = cache (.hash i))
    (lay : Layer) (e : KeyIndex) (message : HashInput) (base : Digest) (attempts trial : ℕ) :
    evalTh (fun i => (actual (.hash i)).getD 0) (grind P lay e message base attempts trial) =
      evalTh (fun i => (cache (.hash i)).getD 0) (grind P lay e message base attempts trial) := by
  induction attempts generalizing trial with
  | zero => simp only [grind, evalTh, simulateQ_pure]
  | succ attempts ih =>
    simp only [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash,
      HasQuery.instOfMonadLift_query, evalTh, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, pure_bind]
    have hv := h _ (SigningLane2BridgeProof.isMsg_trialInput P lay e message base trial)
    change actual (.hash (tweakableHashInput P (.message lay e)
      (message ++ bytesLE 16 (base + BitVec.ofNat digestBits trial)))) = _ at hv
    rw [hv]
    simp only [simulateQ_pure, pure_bind]
    cases Codeword.decode (truncateHash
      ((cache (.hash (trialInput P lay e message base trial))).getD 0)) with
    | none => exact ih (trial + 1)
    | some encoding => rfl

/-- `cachedFound` reads one base cell and otherwise only message-trial cells. -/
theorem cachedFound_sync (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) (e : KeyIndex) (rho : Digest) (message : Message)
    (hb : actual (.hash (randomizerInput P bottomLayer e rho (bytesLE 32 message))) =
      data.cache (.hash (randomizerInput P bottomLayer e rho (bytesLE 32 message)))) :
    SigningLane2FlatProof.cachedFound actual P e rho message =
      SigningLane2FlatProof.cachedFound data.cache P e rho message := by
  unfold SigningLane2FlatProof.cachedFound
  rw [hb]
  exact grind_eval_sync P actual data.cache h.message bottomLayer e (bytesLE 32 message) _ _ _


/-- At a triggering hash, the freshness test reads the just-queried input. -/
theorem traceStepAt_at (P : PublicParameter) (seeds : C.Term → HashOutput)
    (cache after : HashCache C) (signing : TsigState C) (input : HashInput)
    (call : (WorldSpec C).Domain) (hroute : SigningFlatProof.HashCallAt input call)
    (aux : XmssSecurity.SigningCacheTrace × Bool) (e : KeyIndex) (message : Message)
    (hp : SigningGuessProof.RandomizerCached seeds cache e)
    (hb : SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e)
      signing call) (hm : signing.bound e = some message) :
    SigningLaneUnionProof.traceStepAt seeds P cache signing
      call after aux =
      if cache (.hash input) = none then
        (aux.1 ++ [⟨⟨e, message⟩,
          SigningLane2BridgeProof.signOf (SigningLane2FlatProof.laneKey P) e
            (SigningLane2FlatProof.cachedFound after P e
              (SigningGuessProof.cachedRandomizer seeds cache e) message),
          SigningLane2BridgeProof.keptView IsMsg cache,
          SigningLane2BridgeProof.keptView IsMsg after⟩], aux.2)
      else (aux.1, aux.2 || decide (e ∉ aux.1.leafIndices)) := by
  have ht : ∃ e, SigningGuessProof.RandomizerCached seeds cache e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e)
        signing call := ⟨e, hp, hb⟩
  have he := SigningR1FixedProof.baseCall_key_eq ht.choose_spec.2 hb
  obtain ⟨m, hm', hi⟩ := (baseCall_hashAt_iff P e _ signing input call hroute).mp hb
  have hm'' : m = message := Option.some.inj (hm'.symm.trans hm)
  subst m
  rw [SigningLaneUnionProof.traceStepAt, dif_pos ht, he, hm]
  simp only []
  rw [hi]

/-- The synchronized trace includes its stale bit and both message-cache views. -/
theorem traceStepAt_sync (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (input : HashInput) (call otherCall : (WorldSpec C).Domain)
    (hcall : SigningFlatProof.HashCallAt input call)
    (hotherCall : SigningFlatProof.HashCallAt input otherCall) (source : SourceState C)
    (data postData : DeferredState C) (actual postActual : HashCache C) (actualSigning signing : TsigState C)
    (hcache : CacheRelation P seeds s data actual)
    (hpostCache : CacheRelation P seeds s postData postActual)
    (hopening : OpeningRelation seeds s source data actual)
    (hreleased : ReleasedPending P s source data)
    (hsource : actualSigning.bound = source.signing.bound)
    (hbound : source.signing.bound = signing.bound)
    (hno : ∀ k, hiddenCandidate P input = some (k, s k) → source.revealed k ≠ none)
    (hpost : postActual (.hash input) = postData.cache (.hash input))
    (aux : XmssSecurity.SigningCacheTrace × Bool) :
    SigningLaneUnionProof.traceStepAt seeds P actual actualSigning
      call postActual aux =
    SigningLaneUnionProof.traceStepAt seeds P data.cache signing
      otherCall postData.cache aux := by
  have ht (e : KeyIndex) := trigger_iff_step P seeds s input call otherCall hcall hotherCall
    source data actual signing hcache hopening hbound hno e
  simp only [baseCall_bound_congr P _ _ source.signing actualSigning hsource.symm call] at ht
  by_cases h : ∃ e, SigningGuessProof.RandomizerCached seeds actual e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds actual e)
        actualSigning call
  · obtain ⟨e, hp, hb⟩ := h
    obtain ⟨hc, hd⟩ := (ht e).mp ⟨hp, hb⟩
    obtain ⟨message, hm, hi⟩ := (baseCall_hashAt_iff P e _ actualSigning input call hcall).mp hb
    have hm' : signing.bound e = some message := by rw [← hbound, ← hsource]; exact hm
    have hpre := hcache.agree (.hash input)
      (hashInput_not_suspended P seeds s input source data hreleased hno)
    have hrho := (hcache.randomizer e hc).2
    have hfound := cachedFound_sync P seeds s postData postActual hpostCache e
      (SigningGuessProof.cachedRandomizer seeds actual e) message (hi ▸ hpost)
    rw [traceStepAt_at P seeds actual postActual actualSigning input call hcall aux e message hp hb hm,
      traceStepAt_at P seeds data.cache postData.cache signing input otherCall hotherCall aux e message hc hd hm',
      hpre, hfound, hcache.keptView, hpostCache.keptView, hrho]
  · have h' : ¬∃ e, SigningGuessProof.RandomizerCached seeds data.cache e ∧
        SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds data.cache e)
          signing otherCall := by
      rintro ⟨e, he⟩
      exact h ⟨e, (ht e).mpr he⟩
    simp only [SigningLaneUnionProof.traceStepAt, dif_neg h, dif_neg h']


/-- A raw hash takes the ordinary branch, preserving the entire share state.
The existing capped-hit lemma therefore gives the exact `Stuck` event. -/
theorem capHit_stuck (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (input : HashInput) (k : HiddenKey) (source : SourceState C) (st : CompState C)
    (hcandidate : hiddenCandidate x.1 input = some (k, s k))
    (hreveal : RevealRelation s source st.1.1) (hunreleased : source.revealed k = none)
    (hcap : st.1.1.1.2 < q) (hbad : st.2.bad = none)
    (r : HashOutput × CompState C)
    (hr : r ∈ support ((shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.hash (.hash input)))))).run st)) : Stuck r.2 := by
  have hrout : route x.2.1 (.hash input) = none := by
    apply dif_neg
    rintro ⟨z, hz⟩
    cases hz
  have hrest : restRoute x.2.1 x.2.2 (.hash input) = none := by
    apply dif_neg
    rintro ⟨z, hz⟩
    exact not_isSlot_hash x input ⟨z.val, hz⟩
  simp only [shareBackendTagT, StateT.run, backendRaw, hrout, ordinaryFullRaw,
    ordinaryRaw, hrest, simulateQ_bind, simulateQ_pure,
    resolvePrivateTable_lift, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  refine ⟨?_, Or.inl hbad⟩
  exact cappedCompiler_hash_hit x.1 x.2.1 q s input k (s k) hcandidate
    (merged x.2.1 st.1.1 st.2.cache)
    ((congrFun hreveal.1 k).symm.trans hunreleased) rfl hcap a ha

/-- The released-key predicate reads only the bound map and exposed trees. -/
theorem released_congr (signing signing' : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (hb : signing.bound = signing'.bound)
    (k : HiddenKey) : Released signing trees k = Released signing' trees k := by
  cases k <;> simp only [Released, hb]

/-- The existing local candidate filter with its parser and release predicate
abstracted. This normal form keeps reduction away from the concrete parser. -/
def candidateList (parse : HashInput → Option (HiddenKey × Digest))
    (released : HiddenKey → Prop) : (LocalSpec C).Domain → List (HiddenKey × Digest)
  | .inr (.inl (.hash input)) => match parse input with
    | some c => if released c.1 then [] else [c]
    | none => []
  | _ => []

theorem unreleasedCandidates_eq_candidateList (P : PublicParameter) (signing : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) :
    unreleasedCandidates P signing trees =
      candidateList (hiddenCandidate P) (Released signing trees) := rfl

theorem candidateList_congr (parse : HashInput → Option (HiddenKey × Digest))
    (released released' : HiddenKey → Prop) (h : released = released')
    (t : (LocalSpec C).Domain) :
    candidateList parse released t = candidateList parse released' t :=
  congrArg (fun f => candidateList parse f t) h

/-- Every element of a candidate list came from the one raw hash input. -/
theorem candidateList_mem (parse : HashInput → Option (HiddenKey × Digest))
    (released : HiddenKey → Prop) (t : (LocalSpec C).Domain) (c : HiddenKey × Digest)
    (hc : c ∈ candidateList parse released t) :
    ∃ input, t = .inr (.inl (.hash input)) ∧ parse input = some c := by
  rcases t with n | (q | inp)
  · cases hc
  · cases q with
    | hash input =>
      refine ⟨input, rfl, ?_⟩
      simp only [candidateList] at hc
      cases hh : parse input with
      | none => simp only [hh] at hc; cases hc
      | some candidate =>
        simp only [hh] at hc
        by_cases hr : released candidate.1
        · simp only [if_pos hr] at hc
          cases hc
        · simp only [if_neg hr] at hc
          exact congrArg some (List.mem_singleton.mp hc).symm
    | _ => cases hc
  · cases hc

/-- The candidate filter depends only on the authorization map and exposed trees. -/
theorem unreleasedCandidates_congr (P : PublicParameter) (signing signing' : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (t : (LocalSpec C).Domain)
    (hb : signing.bound = signing'.bound) :
    unreleasedCandidates P signing trees t = unreleasedCandidates P signing' trees t := by
  rw [unreleasedCandidates_eq_candidateList, unreleasedCandidates_eq_candidateList]
  exact candidateList_congr (hiddenCandidate P) (Released signing trees) (Released signing' trees)
    (funext (released_congr signing signing' trees hb)) t

/-- Membership in the hash branch records its parsed candidate. -/
theorem unreleasedCandidates_hash_mem (P : PublicParameter) (signing : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (input : HashInput) (c : HiddenKey × Digest)
    (hc : c ∈ unreleasedCandidates P signing trees (.inr (.inl (.hash input)))) :
    hiddenCandidate P input = some c := by
  rw [unreleasedCandidates_eq_candidateList] at hc
  obtain ⟨other, he, hh⟩ := candidateList_mem (hiddenCandidate P) (Released signing trees) _ c hc
  cases he
  exact hh

/-- C1/C2 make the two pre-call control updates identical. -/
theorem control_sync (x : Keys3 C) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (a : RealState C) (b : SourceState C × CompState C)
    (h : SyncFields x s pads noise g rest a b) (t : (LocalSpec C).Domain) :
    (b.1.hiddenFlag || SigningCoreProof.hiddenHit x b.1.signing.corrupt t) =
      (a.1.2.1.2 || SigningCoreProof.hiddenHit x a.1.2.1.1.corrupt t) ∧
    b.1.candidates ++ unreleasedCandidates x.1 b.1.signing b.1.exposed t =
      a.1.2.2.2 ++ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t := by
  constructor
  · rw [h.flag, h.corrupt]
  · rw [h.candidates, h.exposed, unreleasedCandidates_congr x.1 _ _ _ t h.bound]

/-- Every newly logged exact candidate is covered by the one-input no-hit branch. -/
theorem candidatesPaid_append (P : PublicParameter) (s : HiddenKey → Digest)
    (source : SourceState C) (t : (LocalSpec C).Domain)
    (hpaid : ∀ c ∈ source.candidates, c.2 = s c.1 → source.revealed c.1 ≠ none)
    (hno : ∀ input k, t = .inr (.inl (.hash input)) →
      hiddenCandidate P input = some (k, s k) → source.revealed k ≠ none) :
    ∀ c ∈ source.candidates ++ unreleasedCandidates P source.signing source.exposed t,
      c.2 = s c.1 → source.revealed c.1 ≠ none := by
  intro c hc he
  rcases List.mem_append.mp hc with hc | hc
  · exact hpaid c hc he
  · rw [unreleasedCandidates_eq_candidateList] at hc
    obtain ⟨input, ht, hh⟩ := candidateList_mem (hiddenCandidate P)
      (Released source.signing source.exposed) t c hc
    exact hno input c.1 ht (hh.trans (congrArg some (Prod.ext rfl he)))

end ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.hashInput_ready_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.hashInput_ready_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.trigger_iff_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.trigger_iff_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.cachedExtra_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.cachedExtra_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.traceStepAt_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.traceStepAt_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.realCache_some_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.realCache_some_chain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.hash_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.hash_dichotomy

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.capHit_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.capHit_stuck

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.control_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.control_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.candidatesPaid_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTrigger.candidatesPaid_append

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.SyncFields.mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.SyncFields.mark

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.LocalFrame.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRelease.LocalFrame.trans
