import ThresholdLeanXmssSecurity.Proof.SigningGuardedFlag

/-!
# The top opening at the verification prefix

The condition used here is a successful bottom-tree computation already resolved in the cache
at the actual verification prefix. Its structural reads fix the honest bottom root, and its
successful top grind supplies the selected digest input. The final cache may contain more reads.

The argument reuses the resolved bottom-tree lemmas of `SigningHitProof` and the pinned leanVM
cache-read lemmas. A request recorded in the released-tree set alone is not a success certificate:
`openingOracles` records the request even when the bottom-tree computation returns no tree.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningTopCacheProof

open SigningDescentProof

variable {C : Committee}

/-- The honest bottom-root inputs read on `final` are already present in `cache`. -/
structure RootReads (cache final : HashCache C) (P : XmssSecurity.PublicParameter)
    (e : XmssSecurity.LeafIndex) (hk : HonestKey) : Prop where
  chain : ∀ l k, k < XmssSecurity.chainLength - 1 →
    bottomStepCached cache P e l k (honestValue (bottomStep final P e) hk.secret l k)
  leaf : bottomLeafCached cache P e (honestEnds (bottomStep final P e) hk.secret)
  node : ∀ level, level < XmssSecurity.treeHeight →
    bottomNodeCached cache P e level
      (honestNode (bottomStep final P e)
        (XmssSecurity.Concrete.CacheView.leafHash (thView final) P e)
        (XmssSecurity.Concrete.CacheView.nodeHash (thView final) P e) hk.secret hk.path level)
      (hk.path level)

/-- A cached hash read has the same truncated answer in an extension. -/
theorem digestAt_eq_of_cached {cache final : HashCache C} (hle : cache ≤ final)
    (input : XmssSecurity.HashInput) (hc : (thView cache input).isSome) :
    XmssSecurity.Concrete.CacheView.digestAt (thView cache) input =
      XmssSecurity.Concrete.CacheView.digestAt (thView final) input := by
  obtain ⟨output, ho⟩ := Option.isSome_iff_exists.mp hc
  exact (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some ho).trans
    (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some (hle ho)).symm

/-- The cached chain inputs fix every honest chain value up to its end. -/
theorem rootReads_walk {cache final : HashCache C} (hle : cache ≤ final)
    (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex) (hk : HonestKey)
    (reads : RootReads cache final P e hk) (l : XmssSecurity.ChainIndex)
    (n : ℕ) (hn : n ≤ XmssSecurity.chainLength - 1) :
    honestValue (bottomStep cache P e) hk.secret l n =
      honestValue (bottomStep final P e) hk.secret l n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < XmssSecurity.chainLength - 1 := by omega
    obtain ⟨_, hc⟩ := reads.chain l n hn'
    have hi := ih (by omega)
    unfold honestValue at hi ⊢
    simp only [XmssSecurity.Wots.walk, Nat.zero_add]
    rw [hi]
    simpa only [bottomStep, XmssSecurity.Concrete.CacheView.chainStep_eq _ _ _ _ _ _ hn',
      honestValue] using digestAt_eq_of_cached hle _ hc

/-- The cached leaf and authentication-path reads fix the honest root. -/
theorem rootReads_honestRoot {cache final : HashCache C} (hle : cache ≤ final)
    (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex) (hk : HonestKey)
    (reads : RootReads cache final P e hk) :
    honestRoot cache P e hk = honestRoot final P e hk := by
  have hends : honestEnds (bottomStep cache P e) hk.secret =
      honestEnds (bottomStep final P e) hk.secret := by
    funext l
    exact rootReads_walk hle P e hk reads l _ le_rfl
  have hleaf : XmssSecurity.Concrete.CacheView.leafHash (thView cache) P e
      (honestEnds (bottomStep cache P e) hk.secret) =
      XmssSecurity.Concrete.CacheView.leafHash (thView final) P e
        (honestEnds (bottomStep final P e) hk.secret) := by
    rw [hends]
    exact digestAt_eq_of_cached hle _ reads.leaf
  have hnode : ∀ n, n ≤ XmssSecurity.treeHeight →
      honestNode (bottomStep cache P e)
        (XmssSecurity.Concrete.CacheView.leafHash (thView cache) P e)
        (XmssSecurity.Concrete.CacheView.nodeHash (thView cache) P e) hk.secret hk.path n =
      honestNode (bottomStep final P e)
        (XmssSecurity.Concrete.CacheView.leafHash (thView final) P e)
        (XmssSecurity.Concrete.CacheView.nodeHash (thView final) P e) hk.secret hk.path n := by
    intro n hn
    induction n with
    | zero => exact hleaf
    | succ n ih =>
      have hn' : n < XmssSecurity.treeHeight := by omega
      obtain ⟨_, hc⟩ := reads.node n hn'
      have hi := ih (by omega)
      unfold honestNode at hi ⊢
      simp only [XmssSecurity.Merkle.ascend, Nat.zero_add]
      rw [hi]
      simpa only [XmssSecurity.Concrete.CacheView.nodeHash_eq _ _ _ _ _ _ hn', honestNode]
        using digestAt_eq_of_cached hle _ hc
  exact hnode _ le_rfl

/-- A completed bottom computation has read every structural input used by the final honest
root. This remains true when that computation returned no tree. -/
theorem rootReads_of_resolvedBottom (prims : Primitives) (z : FinalState C)
    (cache : HashCache C) (hle : cache ≤ z.cache) (output : Option TreeOutput)
    (resolved : DeterministicSigning.Resolves cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue z.keys.2.1)
        z.keys.1 z.top (.bottom (treeOf z.key))) output) :
    RootReads cache z.cache z.keys.1 z.key (z.honestKey prims) := by
  have target : ∀ domain, SigningHitProof.BottomDomain (treeOf z.key) domain →
      (cache (.hash (XmssSecurity.tweakableHashInput z.keys.1 domain
        (SigningHitProof.forestPayload prims z.keys z.cache domain)))).isSome := by
    intro domain hd
    obtain ⟨hc, hs⟩ := SigningHitProof.resolves_referenceBottom_targets prims z.keys cache
      z.top (treeOf z.key) output resolved domain hd
    rw [hs z.cache hle]
    exact hc
  constructor
  · intro l k hk
    refine ⟨hk, ?_⟩
    exact target (.chain z.key l ⟨k, hk⟩) rfl
  · exact target (.leaf z.key) rfl
  · intro level hl
    refine ⟨hl, ?_⟩
    have hd : SigningHitProof.BottomDomain (treeOf z.key)
        (.merkle ⟨level, hl⟩ (XmssSecurity.Concrete.CacheView.nodeIndex z.key level)) := by
      change (z.key.val / 2 ^ (level + 1)) / 2 ^ (16 - (level + 1)) = z.key.val / 2 ^ 16
      rw [Nat.div_div_eq_div_mul, ← pow_add, show level + 1 + (16 - (level + 1)) = 16 by
        have hh : level < 16 := hl
        omega]
    have hp := SigningHitProof.forestPayload_bottomNode prims z.keys z.cache z.key ⟨level, hl⟩
    have hn : honestNode (bottomStep z.cache z.keys.1 z.key)
        (XmssSecurity.Concrete.CacheView.leafHash (thView z.cache) z.keys.1 z.key)
        (XmssSecurity.Concrete.CacheView.nodeHash (thView z.cache) z.keys.1 z.key)
        (z.honestKey prims).secret (z.honestKey prims).path level =
      XmssSecurity.Concrete.CacheReplay.treeNode (thView z.cache) z.keys.1
        (SigningHitProof.replayStarts prims z.keys z.cache bottomLayer) level
        (SigningCacheProof.pathNode z.key level) :=
      SigningCacheProof.path_ascends_to_treeNode _ _ _ z.key level (Nat.le_of_lt hl)
    have hpath : (z.honestKey prims).path level =
        XmssSecurity.Concrete.CacheReplay.treeNode (thView z.cache) z.keys.1
          (SigningHitProof.replayStarts prims z.keys z.cache bottomLayer) level
          (XmssSecurity.Concrete.authenticationPathNode z.key ⟨level, hl⟩) := by
      simp only [FinalState.honestKey, hl, ↓reduceDIte]
      rfl
    rw [← hn, ← hpath] at hp
    have hc := target (.merkle ⟨level, hl⟩ (XmssSecurity.Concrete.CacheView.nodeIndex z.key level)) hd
    rw [hp] at hc
    exact hc

set_option backward.isDefEq.respectTransparency false in
/-- A successful top grind in a resolved bottom tree has its selected digest in that cache. -/
theorem resolvedBottom_topDigest (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (top : TopTree) (b : XmssSecurity.TopIndex) (tree : BottomTree)
    (resolved : DeterministicSigning.Resolves cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
        x.1 top (.bottom b)) (some (.bottom tree))) :
    (thView cache (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 b
      (tree.root, tree.topSignature.randomness))).isSome := by
  obtain ⟨encoding, hc⟩ := SigningGuessProof.resolves_referenceBottom_topGrind_some x cache top b tree resolved
  unfold SigningGuessProof.canonicalTopGrind SigningGuessProof.topGrindAfter at hc
  obtain ⟨before, _, hs⟩ := hc.of_bind
  obtain ⟨selected, hs, he⟩ := hs.of_map
  obtain ⟨hroot, hselected⟩ := Prod.mk.inj he
  rw [hselected, SigningGuessProof.grind_top_eq] at hs
  have hscan := SigningHitProof.resolves_forestHash _ _ _ hs
  have hrun : (some (tree.topSignature.randomness, encoding), thView cache) ∈ support
      ((simulateQ randomOracle
        (XmssSecurity.Concrete.topSignFrom x.1 b before.1 before.2 randomizerAttemptLimit 0)).run
          (thView cache)) := by
    rw [hscan.run_eq_pure]
    simp
  obtain ⟨output, ho, _⟩ := XmssSecurity.topSignFrom_some_cached x.1 b before.1 before.2
    randomizerAttemptLimit 0 (thView cache) (thView cache) tree.topSignature.randomness encoding hrun
  rw [hroot] at ho
  exact Option.isSome_iff_exists.mpr ⟨output, ho⟩

/-- A successful bottom computation in the smaller cache supplies both hypotheses of
`topOpened_cache_eq` for the final honest key. -/
theorem top_cache_conditions (prims : Primitives) (z : FinalState C)
    (cache : HashCache C) (hle : cache ≤ z.cache)
    (htop : D prims z.answers
      (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 emptyTop .top) = some (.top z.top))
    (tree : BottomTree)
    (resolved : DeterministicSigning.Resolves cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue z.keys.2.1)
        z.keys.1 z.top (.bottom (treeOf z.key))) (some (.bottom tree))) :
    honestRoot cache z.keys.1 z.key (z.honestKey prims) =
        honestRoot z.cache z.keys.1 z.key (z.honestKey prims) ∧
      SigningReleasedProof.TopSignedCached cache z.keys.1 z.key (z.honestKey prims) := by
  have hroot := rootReads_honestRoot hle z.keys.1 z.key (z.honestKey prims)
    (rootReads_of_resolvedBottom prims z cache hle _ resolved)
  refine ⟨hroot, ?_⟩
  have hi := SigningGuessProof.resolved_bottom_topSignedInput prims z tree htop (resolved.mono hle)
  have hi' : topSignedInput cache z.keys.1 z.key (z.honestKey prims) =
      (tree.root, tree.topSignature.randomness) := by
    rw [topSignedInput, hroot]
    exact hi
  unfold SigningReleasedProof.TopSignedCached
  rw [hi']
  exact resolvedBottom_topDigest z.keys cache z.top (treeOf z.key) tree resolved

open SigningGuardedFlagProof in
set_option maxRecDepth 100000 in
/-- The top tree replays correctly on the final cache of every actual verification prefix. -/
theorem verificationPrefix_top_replay (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) :
    D prims (SigningCacheProof.answersOf r.2.1)
      (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) = some (.top top) := by
  obtain ⟨top', p, f, hp, hp1, hq, hv, hf, rfl⟩ := hpre
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  have hle : p.2.1 ≤ f.2.1 :=
    ((SigningCacheProof.countRun_grows prims _ _ q hq).trans
      (SigningCacheProof.countRun_grows prims _ _ v hv)).trans
        (SigningCacheProof.countRun_grows prims _ _ f hf)
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _] at hp
  exact (SigningCacheProof.run_liftFree prims _ _ p hp (SigningCacheProof.answersOf f.2.1)
    (SigningCacheProof.agrees_answersOf hle)).symm.trans hp1

/-- The operational condition needed at the prefix: its cache already resolves a successful
bottom tree for the forged key. It names an actual computation, not a cache equality. -/
def PrefixBottomSuccess (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (forgery : Forgery) (cache : HashCache C) : Prop :=
  ∃ tree : BottomTree, DeterministicSigning.Resolves cache
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
      x.1 top (.bottom (treeOf forgery.signature.leafIndex))) (some (.bottom tree))

set_option maxRecDepth 100000 in
/-- Any successful bottom subrun ending before the verification prefix supplies the condition. -/
theorem prefixBottomSuccess_of_run (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (forgery : Forgery) (tree : BottomTree)
    (initial final : HashCache C × ℕ) (cache : HashCache C)
    (hsub : (some (TreeOutput.bottom tree), final) ∈ support
      ((simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree
          (referenceTree tweakable (prfValue x.2.1) x.1 top
            (.bottom (treeOf forgery.signature.leafIndex))))).run initial))
    (hle : final.1 ≤ cache) : PrefixBottomSuccess x top forgery cache := by
  refine ⟨tree, ?_⟩
  apply DeterministicSigning.Resolves.mono ?_ hle
  apply SigningHitProof.run_hashEmbed_resolves prims
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
      x.1 top (.bottom (treeOf forgery.signature.leafIndex))) initial
      (some (TreeOutput.bottom tree), final)
  simpa only [SigningHitProof.hashEmbed_referenceTree] using hsub

open SigningGuardedFlagProof in
/-- The top opening is stable at the actual verification prefix whenever its bottom ceremony
has already succeeded there. No win or absence-of-collision hypothesis is needed. -/
theorem verificationPrefix_topOpened_eq (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery))
    (hs : PrefixBottomSuccess x top forgery q.2.1) :
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    topOpened q.2.1 x.1 z.key (z.honestKey prims) =
      topOpened r.2.1 x.1 z.key (z.honestKey prims) := by
  intro z
  obtain ⟨tree, htree⟩ := hs
  have hle := verificationPrefix_le prims A x r q v hpre
  have htop := verificationPrefix_top_replay prims A x r q v hpre top state forgery hm
  obtain ⟨hroot, hcached⟩ := top_cache_conditions prims z q.2.1 hle htop tree htree
  exact SigningReleasedProof.topOpened_cache_eq hle x.1 z.key (z.honestKey prims) hroot hcached

open SigningGuardedFlagProof in
set_option maxRecDepth 100000 in
/-- The `verifyRun` form: the actual prefix has a stable top opening when a successful bottom
computation is already resolved there. Membership of `releasedTrees` alone does not assert success. -/
theorem verifyRun_topOpened_eq (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (hr : r ∈ support (SigningGuessLinkProof.verifyRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) :
    ∃ q v, VerificationPrefix prims A x r q v ∧
      (PrefixBottomSuccess x top forgery q.2.1 →
        let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
        topOpened q.2.1 x.1 z.key (z.honestKey prims) =
          topOpened r.2.1 x.1 z.key (z.honestKey prims)) := by
  obtain ⟨q, v, hpre⟩ := verificationPrefix_exists prims A x r hr top state forgery hm
  exact ⟨q, v, hpre, verificationPrefix_topOpened_eq prims A x r q v hpre top state forgery hm⟩

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.rootReads_honestRoot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rootReads_honestRoot

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.rootReads_of_resolvedBottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rootReads_of_resolvedBottom

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.resolvedBottom_topDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resolvedBottom_topDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.top_cache_conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms top_cache_conditions

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.verificationPrefix_top_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationPrefix_top_replay

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.prefixBottomSuccess_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefixBottomSuccess_of_run

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.verificationPrefix_topOpened_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationPrefix_topOpened_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningTopCacheProof.verifyRun_topOpened_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyRun_topOpened_eq

end SigningTopCacheProof
end ThresholdLeanXmssSecurity
