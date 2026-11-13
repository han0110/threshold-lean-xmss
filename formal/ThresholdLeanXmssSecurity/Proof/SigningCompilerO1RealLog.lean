import ThresholdLeanXmssSecurity.Proof.SigningLaneUnion
import ThresholdLeanXmssSecurity.Proof.SigningReleasedLink
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncHonestRead

/-! # The real log of the O1 coupling

`hashEmbed_codewordForest` states that the codeword search of round 2 is a hash-only computation.
`resolves_countRun` states that a hash-only computation that its cache resolves has a counted run
that starts and ends at that cache. `traceRun_flag` states that the flag of the result of the trace
run is the flag of its final opening state. `honest_resolves` states that a hash-only honest
computation resolves on the log cache after its real run.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1RealLog
open SigningOpeningProof SigningSecurityProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable

section Bridge
variable (prims : Primitives) (x : Keys3 C)

/-- The codeword search of round 2 as a hash-only computation. -/
def codewordForest (P : PublicParameter) (commitment : Digest) (e : KeyIndex) (message : Message)
    (ρ : Digest) : OracleComp (Query C →ₒ HashOutput) (Option (Randomness × Encoding)) :=
  SigningHitProof.forestHash (do
    let opened := truncateHash (← Concrete.oracleHash (commitmentInput P e ρ))
    if opened ≠ commitment then pure none else
    let base := truncateHash (← Concrete.oracleHash
      (randomizerInput P bottomLayer e ρ (bytesLE 32 message)))
    grind P bottomLayer e (bytesLE 32 message) base randomizerAttemptLimit 0)

/-- The hash-only form is `signCodeword`. -/
theorem hashEmbed_codewordForest (P : PublicParameter) (commitment : Digest) (e : KeyIndex)
    (message : Message) (ρ : Digest) :
    SigningHitProof.hashEmbed (codewordForest (C := C) P commitment e message ρ) =
      signCodeword P commitment e message ρ := by
  rw [codewordForest, SigningHitProof.hashEmbed_forestHash]
  rfl

set_option maxRecDepth 100000 in
/-- The flag of the real result is the flag of the final real state. -/
theorem traceRun_flag (A : TsigAdversary C) (z : SigningLaneUnionProof.TraceOutcome C)
    (hz : z ∈ support (SigningLaneUnionProof.traceRun prims A x)) :
    z.1.1.1.2 = z.2.2.1.2 := by
  have hw : SigningLaneUnionProof.splitOf z ∈ support (SigningOneRunProof.splitRunAt prims A x) := by
    rw [← SigningLaneUnionProof.traceRun_forget, support_map]
    exact ⟨z, hz, rfl⟩
  change (SigningLaneUnionProof.splitOf z).1.1.1.2 = (SigningLaneUnionProof.splitOf z).2.2.1.2
  generalize SigningLaneUnionProof.splitOf z = w at hw
  unfold SigningOneRunProof.splitRunAt SigningOneRunProof.splitGame
    SigningJointEagerProof.jointGameWith at hw
  simp only [StateT.run_bind, mem_support_bind_iff] at hw
  obtain ⟨setup, hsetup, hw⟩ := hw
  have hs := SigningReleasedLinkProof.world_run_carried prims x _ _ setup hsetup
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    rw [hs]
    rfl
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      rw [hs]
      rfl
    | top top =>
      simp only [hout, StateT.run_bind, SigningFlatEagerProof.getCarried, StateT.run_mk, pure_bind,
        mem_support_bind_iff] at hw
      obtain ⟨middle, -, finished, hfinished, hw⟩ := hw
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      have hf := SigningReleasedLinkProof.world_run_carried prims x _ _ finished hfinished
      subst hw
      rw [hf]

/-- A resolved hash-only computation has a counted run that starts and ends at its cache. -/
theorem resolves_countRun {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (cache : HashCache C) (v : α) (h : DeterministicSigning.Resolves cache oa v) (n : ℕ) :
    ∃ m, (v, (cache, m)) ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (SigningHitProof.hashEmbed oa))).run (cache, n)) := by
  induction h generalizing n with
  | pure value =>
    refine ⟨n, ?_⟩
    change (value, cache, n) ∈ support (pure (value, cache, n) : ProbComp _)
    simp
  | query input answer hanswer next value _ ih =>
    obtain ⟨m, hm⟩ := ih (n + SeedHitProof.signCost (.inr (.inr (.inl input)) : (WorldSpec C).Domain))
    refine ⟨m, ?_⟩
    have he : SigningHitProof.hashEmbed (liftM ((Query C →ₒ HashOutput).query input) >>= next) =
        hashQuery input >>= fun answer => SigningHitProof.hashEmbed (next answer) := by
      simp [SigningHitProof.hashEmbed, simulateQ_bind]
    rw [he, SigningSecurityProof.liftFree, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff]
    refine ⟨(answer, cache, n + SeedHitProof.signCost (.inr (.inr (.inl input)) : (WorldSpec C).Domain)),
      ?_, hm⟩
    rw [hashQuery, free]
    erw [liftComp_query, simulateQ_query]
    simp
    change _ ∈ support ((fun z => (z.1, (z.2,
      n + SeedHitProof.signCost (.inr (.inr (.inl input)) : (WorldSpec C).Domain)))) <$>
        (SeedHitProof.signImpl prims (.inr (.inr (.inl input)))).run cache)
    rw [support_map]
    refine ⟨(answer, cache), ?_, rfl⟩
    change (answer, cache) ∈ support (((Query C →ₒ HashOutput).randomOracle input).run cache)
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hanswer]
    simp

end Bridge

section Honest
open SigningLaneHybridCapProof SigningCompilerCouplingProof SigningCompilerRealTables
open SigningCompilerShare SigningCompilerSyncReal SigningCompilerSyncStop SigningCompilerSyncRelease
open SigningCompilerSyncRealRead SigningCompilerSyncLocalRead SigningCompilerSyncHonestRead
open SigningCompilerO1Sync SigningCompilerUntil SigningCompilerO1Frame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  SigningLaneUnionProof.traceStepAt
variable (prims : Primitives) (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
  (noise : ChainNoiseIndex → HashOutput)

/-- A grind on the private oracle keeps the private relation at its visible cache. -/
theorem realPrivate_keyedSplit {β : Type} (g : C.Term × CPoint → HashOutput)
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (oa : OracleComp (Query C →ₒ HashOutput) β)
    (st : (HashCache C × SigningPartnerBoundProof.Monitor) × (XmssSecurity.LeafIndex → Bool))
    (priv : HashCache C) (h : RealPrivate x s pads noise g rest priv st.1.1)
    (r : (β × ((HashCache C × SigningPartnerBoundProof.Monitor) ×
      (XmssSecurity.LeafIndex → Bool))) × HashCache C)
    (hr : r ∈ support ((simulateQ (realImpl x g rest)
      ((simulateQ (rawKeyedSplitOracle keyOf) oa).run st)).run priv)) :
    RealPrivate x s pads noise g rest r.2 r.1.2.1.1 := by
  induction oa using OracleComp.inductionOn generalizing st priv r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨w, hw, hr⟩ := hr
    simp only [rawKeyedSplitOracle, StateT.run_mk, simulateQ_map, StateT.run_map,
      support_map, Set.mem_image] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ih _ _ _ (realPrivate_observe h (.inr t) v hv) r hr

/-- The observed answer of a private read is a lazy read of the visible cache. -/
theorem realRead_observed (g : C.Term × CPoint → HashOutput) (priv vis : HashCache C)
    (h : RealPrivate x s pads noise g rest priv vis) (input : Query C)
    (z : HashOutput × HashCache C)
    (hz : z ∈ support (((realImpl x g rest) (.inr input)).run priv)) :
    (z.1, vis.cacheQuery input z.1) ∈
      support (((Query C →ₒ HashOutput).randomOracle input).run vis) := by
  cases hv : vis input with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hv]
    simp [uniformSampleImpl]
  | some value =>
    rw [realRead_hit x s pads noise g rest priv vis h input value hv, mem_support_pure_iff] at hz
    subst z
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hv,
      observe_same vis input value hv]
    simp

/-- One honest call of `H` logs its answer and keeps the log agreement, the private relation and
the carried state. -/
theorem honest_call (input : Query C) (a : RealState C)
    (hlog : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1)
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (r : HashOutput × RealState C)
    (hr : r ∈ support ((realCall prims x s pads u rest input).run a)) :
    realLog r.2 input = some r.1 ∧
      SigningPartnerCompareProof.LogAgreement x.1 r.2.1.1.1.1.1 ∧
      RealPrivate x s pads noise (gOf s pads u) rest r.2.2 (visibleOf r.2) ∧
      realLog a ≤ realLog r.2 ∧ r.2.1.2 = a.1.2 := by
  change r ∈ support ((ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) (.inr (.inr (.inl input)))).run a) at hr
  rw [rawTraceWorld_read_honest prims x (gOf s pads u) rest (.inl input) a.1 a.2] at hr
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨z, hz, y, hy, rfl⟩ := hr
  simp only [readInput, readAnswer] at hz hy ⊢
  have hpz : RealPrivate x s pads noise (gOf s pads u) rest z.2
      ((visibleOf a).cacheQuery input z.1) := by
    by_cases hs : IsSlot x input
    · rw [realImpl_slot x _ rest input hs, mem_support_pure_iff] at hz
      rw [hz]
      exact hpriv.observe_slot input hs
    · rw [realImpl_other x _ rest input hs] at hz
      exact hpriv.observe_other input hs z hz
  have hw := realRead_observed x s pads rest noise (gOf s pads u) a.2 (visibleOf a) hpriv input z hz
  have hpy := realPrivate_keyedSplit x s pads rest noise (gOf s pads u) _ _ _ _ hpz y hy
  rw [grind_quiet_transport x s pads noise (gOf s pads u) rest _ _ _ _ _ hpz.quiet,
    support_map] at hy
  obtain ⟨y', hy'', hyy⟩ := hy
  have hy1 : y.1 = y' := by rw [← hyy]
  have hro := Set.mem_image_of_mem (fun r => (r.1, r.2.1.1)) hy''
  rw [← support_map, keyedSplit_cache_forget] at hro
  have hf := SigningReleasedTransferProof.cachedExtra_frame x.2.1 x.1 _ _ _ _ hro
  have hl := SigningPartnerCompareProof.logAgreement_hash x.1 input a.1.1.1.1.1 hlog _ hw
    (a.1.1.1.1.1.2.logQuery (.inr (.inr (.inl input))) z.1)
    (fun _ => by rw [SigningCacheLogProof.logCache_logQuery]; rfl) 0
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · change SigningCacheLogProof.logCache (a.1.1.1.1.1.2.logQuery (.inr (.inr (.inl input))) z.1)
      input = some z.1
    rw [SigningCacheLogProof.logCache_logQuery]
    cases hc : SigningCacheLogProof.logCache a.1.1.1.1.1.2 input with
    | none => simp [SigningCacheLogProof.hashCall]
    | some v =>
      have hv : visibleOf a input = some v := hlog.1 hc
      rw [realRead_hit x s pads noise _ rest a.2 (visibleOf a) hpriv input v hv,
        mem_support_pure_iff] at hz
      rw [hz]
      rfl
  · rw [hy1]
    exact ⟨hl.1.trans hf.1, fun q hq => (hf.2 q hq).trans (hl.2 q hq)⟩
  · exact hpy
  · intro q v hq
    change SigningCacheLogProof.logCache (a.1.1.1.1.1.2.logQuery (.inr (.inr (.inl input))) z.1)
      q = some v
    rw [SigningCacheLogProof.logCache_logQuery,
      show SigningCacheLogProof.logCache a.1.1.1.1.1.2 q = some v from hq]
    rfl

/-- A hash-only honest computation resolves on the log cache after its real run. The run keeps the
log agreement, the private relation and the carried state. -/
theorem honest_resolves {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) (a : RealState C)
    (hlog : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1)
    (hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a))
    (r : α × RealState C)
    (hr : r ∈ support ((realHonest prims x s pads u rest (SigningHitProof.hashEmbed oa)).run a)) :
    DeterministicSigning.Resolves (realLog r.2) oa r.1 ∧
      SigningPartnerCompareProof.LogAgreement x.1 r.2.1.1.1.1.1 ∧
      RealPrivate x s pads noise (gOf s pads u) rest r.2.2 (visibleOf r.2) ∧
      realLog a ≤ realLog r.2 ∧ r.2.1.2 = a.1.2 := by
  induction oa using OracleComp.inductionOn generalizing a r with
  | pure v =>
    simp only [realHonest, SigningHitProof.hashEmbed, simulateQ_pure, SigningSecurityProof.liftFree,
      liftComp_pure, free, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨.pure v, hlog, hpriv, le_rfl, rfl⟩
  | query_bind input next ih =>
    have he : SigningHitProof.hashEmbed (liftM ((Query C →ₒ HashOutput).query input) >>= next) =
        hashQuery input >>= fun answer => SigningHitProof.hashEmbed (next answer) := by
      simp [SigningHitProof.hashEmbed, simulateQ_bind]
    rw [realHonest, he, SigningSecurityProof.liftFree, liftComp_bind, free_bind, simulateQ_bind,
      StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨w, hw, hr⟩ := hr
    rw [hashQuery, free] at hw
    erw [liftComp_query, simulateQ_query] at hw
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map] at hw
    change w ∈ support ((realCall prims x s pads u rest input).run a) at hw
    obtain ⟨hanswer, hlog', hpriv', hle, hcarried⟩ :=
      honest_call prims x s pads u rest noise input a hlog hpriv w (by with_reducible exact hw)
    obtain ⟨hres, hlog'', hpriv'', hle', hcarried'⟩ :=
      ih w.1 w.2 hlog' hpriv' r (by with_reducible exact hr)
    exact ⟨.query input w.1 (hle' hanswer) next r.1 hres, hlog'', hpriv'', hle.trans hle',
      hcarried'.trans hcarried⟩

end Honest

end ThresholdLeanXmssSecurity.SigningCompilerO1RealLog

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.hashEmbed_codewordForest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.hashEmbed_codewordForest

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.traceRun_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.traceRun_flag

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.resolves_countRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.resolves_countRun

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.realPrivate_keyedSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.realPrivate_keyedSplit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.realRead_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.realRead_observed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.honest_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.honest_call

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.honest_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1RealLog.honest_resolves
