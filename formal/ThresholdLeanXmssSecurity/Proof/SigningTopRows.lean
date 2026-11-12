import ThresholdLeanXmssSecurity.Proof.SigningAssembly

/-!
# The rows of the unopened top key

This module links the two rows of `SigningAssembly` with no payer, `TopRow` and `AbsentRow`, to an
input-side hit on a hidden top chain value. Neither row needs D17.

## The test against the no-tree adversary

The adversary of review P5 makes no tree call and returns a fixed forgery. `ForgedStartAbsent`
holds with probability one, but a win must also verify at the top layer.

* The top setup caches every top chain start (`topStarts_cached`). So the absent start of
  `AbsentRow` is a bottom start.
* A bottom ceremony reads all its chain starts (`SigningHitProof.resolves_referenceBottom_chains`).
  So an absent bottom start means that no bottom ceremony of the tree resolves (`TopUnopened`).
* In `TopRow`, a resolved bottom ceremony makes the partner a `ResolvedTopPartner`
  (`SigningGuessProof.topPartner_resolved`), which is charged. So `TopRow` also gives `TopUnopened`.
* The game releases top chain values only through `.tree b` with a returned tree (`Ideal.lean`,
  `tsigOracles`). `.round2` returns bottom values only.
* At an unopened top key, the top descent has no opened position (`SigningDescentProof.fresh_layer`).
  A win gives a top hit, which is `WinHit` and charged, or a forged top value equal to the honest
  value below the chain end.
* The verification calls `H` on that value. `verifyRun` logs this call as a candidate, and the count
  holds it (`SigningGuessLinkProof.verifyRun_verification`).

## The target

`unopenedTopTarget` is the honest value at every position below the end of the forged top key,
when that key is unopened and its chain start is cached. The replayed codeword of `topOpened` is
not used, because in `TopRow` it is the forged codeword.

## The cap interface

* The cap `q / 2^128` on `HiddenInputHit` for `unopenedTopTarget`. It needs that a returned tree
  resolves its bottom ceremony on the cache, so that `TopUnopened` at the end means no release.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningTopRowsProof

open LeanXmss ThresholdLeanXmss SigningOpeningProof SigningUnchargedLoggedProof SigningAssemblyProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The bottom ceremony of tree `b` does not resolve to a tree in the cache. The game releases the
top signature of `b` only with a returned tree, so the chain values of top key `b` below the end
stay hidden. -/
def TopUnopened (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : Prop :=
  ¬∃ tree, DeterministicSigning.Resolves cache
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b))
    (some (.bottom tree))

/-- The chain target at an unopened top key. At the top key of the forgery, when its bottom
ceremony is unopened and the chain start is cached, every position below the end has the honest
value as its target. Every other key has none. -/
def unopenedTopTarget (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C) :
    HiddenKey → Option Digest :=
  match r.1.1.2 with
  | none => fun _ => none
  | some (top, state, forgery) =>
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    let hk := z.honestKey prims
    fun
    | .topChain b l p =>
      if b = XmssSecurity.topKeyOf z.key ∧ TopUnopened x r.2.1 top (treeOf z.key) ∧
          SigningGuardedFlagProof.StartsCached x r.2.1 topLayer (topKey b) l then
        some (SigningDescentProof.honestValue (SigningDescentProof.topStep z.cache x.1 z.key) hk.topSecret l p.val)
      else none
    | _ => none

/-- A resolved threshold PRF value has read the entry of each term. -/
theorem resolves_forestValue_cached (cache : HashCache C) (seeds : C.Term → HashOutput) (p : Point)
    (value : Digest) (h : DeterministicSigning.Resolves cache (SigningHitProof.forestValue seeds p) value) :
    ∀ T ∈ C.terms, (cache (.prf (seeds T) p)).isSome := by
  intro T hT
  unfold SigningHitProof.forestValue at h
  obtain ⟨values, hvalues, _⟩ := h.of_bind
  obtain ⟨b, hb⟩ := SigningHitProof.resolves_mapM_member _ _ values hvalues T hT
  obtain ⟨v, hv, _⟩ := hb.of_map
  rw [← bind_pure (OracleComp.lift _)] at hv
  obtain ⟨a, ha, _⟩ := hv.query_inv
  simp [ha]

set_option maxRecDepth 100000 in
/-- The top setup of a winning run has cached every top chain start. -/
theorem topStarts_cached (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningCostProof.Outcome C) (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false)) (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery)) (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    SigningGuardedFlagProof.StartsCached x r.2.1 topLayer (topKey b) l := by
  obtain ⟨start, _, hs, _⟩ := SigningHitProof.resolves_referenceTop_chains x r.2.1 top
    (SigningHitProof.exposedRun_top_resolves prims A x r hr hwin top state forgery hsome) b l
  exact resolves_forestValue_cached _ _ _ _ hs

set_option maxRecDepth 100000 in
/-- A bottom chain start with an absent PRF entry leaves its tree unopened. Each bottom ceremony
reads all its chain starts, even when its grind fails. -/
theorem topUnopened_of_bottomStart (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (top : TopTree) (e : KeyIndex) (l : ChainIndex)
    (h : ¬SigningGuardedFlagProof.StartsCached x cache bottomLayer e l) :
    TopUnopened x cache top (treeOf e) := by
  rintro ⟨tree, hres⟩
  let k : Fin (2 ^ layerHeight) := ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
  have hek : bottomKey (treeOf e) k = e := by
    apply Fin.ext
    simp only [bottomKey, k, treeOf]
    exact Nat.div_add_mod _ _
  obtain ⟨start, _, hs, _⟩ := SigningHitProof.resolves_referenceBottom_chains x cache top (treeOf e) k _ hres l
  rw [hek] at hs
  exact h (resolves_forestValue_cached _ _ _ _ hs)

set_option maxRecDepth 100000 in
/-- A win without a charged event at an unopened top key is an input-side hit on the unopened
target. The descent at the top layer has no opened position, so it gives a hit or a guess
(`SigningDescentProof.fresh_layer`). The verification of the forgery calls `H` on the guessed value. -/
theorem unopened_hit (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hwin : Win w) (hc : ¬Charged prims x w)
    (hopen : ∀ top state forgery, w.1.1.2 = some (top, state, forgery) →
      TopUnopened x w.2.1.1 top (treeOf forgery.signature.leafIndex)) :
    HiddenInputHit x (unopenedTopTarget prims x (w.1, w.2.1)) (w.1, w.2.1) := by
  have ho := mem_exposedRun_of_joint prims A x w hw
  obtain ⟨top, state, forgery, hsome, hwins, hcons⟩ :=
    SigningCacheProof.runHasFinalState prims C A x _ ho hwin
  obtain ⟨htopRoot, hcached, _⟩ := hcons
  have hverify := (SigningDescentProof.D_verify prims _ _ _ _).symm.trans hwins.1
  obtain ⟨encoding, hencoding, htop⟩ :=
    (XmssSecurity.Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).mp hverify
  obtain ⟨topCodeword, htopCodeword, htopRoot'⟩ :=
    (XmssSecurity.Concrete.verifyTopFromCache_eq_true_iff _ _ _ _ _).mp htop
  have hcachedTop := (hcached encoding hencoding).2 topCodeword htopCodeword
  rcases SigningDescentProof.fresh_layer _ _ _ _ _ _ _ _ topCodeword
      (XmssSecurity.TargetSum.decodeDigest_eq_some_iff.mp htopCodeword).2 _ _
      (htopRoot'.trans htopRoot.symm) hcachedTop with h | ⟨l, hl, hvalue⟩
  · exact (hc (Or.inl ⟨hwin, top, state, forgery, hsome, Or.inr h⟩)).elim
  have hm : (w.1, w.2.1).1.1.2 = some (top, state, forgery) := hsome
  obtain ⟨trees, adversaryLog, s, v, hv, hlog, hle⟩ :=
    SigningGuessLinkProof.verifyRun_verification prims A x (w.1, w.2.1)
      (mem_verifyRun_of_joint prims A x w hw) top state forgery hm
  have hreads := SigningGuessLinkProof.reads_verify_topChain (SigningDescentProof.thView w.2.1.1)
    (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩) forgery.signature.leafIndex forgery.message
    (XmssSecurity.Bridge.toModelSig forgery.signature) encoding hencoding topCodeword htopCodeword l hl
  have hmem := SigningGuessLinkProof.verification_reads prims x.1 state trees top.root forgery s v hv
    w.2.1.1 hle hreads
  have hcand : ((.topChain (XmssSecurity.topKeyOf forgery.signature.leafIndex) l ⟨_, hl⟩ : HiddenKey),
      (XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue l) ∈ v.1.2 := by
    refine hmem _ ?_
    rw [show (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩).parameter = x.1 from rfl,
      SigningGuessLinkProof.callCandidates_topChainInput]
    exact List.mem_singleton_self _
  refine ⟨_, hlog ▸ List.mem_append_right adversaryLog hcand, ?_⟩
  have hm' : w.1.1.2 = some (top, state, forgery) := hsome
  simp only [hiddenTarget, unopenedTopTarget, hm']
  rw [if_pos ⟨rfl, hopen top state forgery hsome,
    topStarts_cached prims A x _ ho hwin top state forgery hsome _ l⟩]
  exact congrArg some hvalue.symm

set_option maxRecDepth 100000 in
/-- `TopRow` is an input-side hit on the unopened target. A resolved bottom ceremony would make
its top partner resolved (`SigningGuessProof.topPartner_resolved`). -/
theorem topRow_hit (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hrow : TopRow prims x w) :
    HiddenInputHit x (unopenedTopTarget prims x (w.1, w.2.1)) (w.1, w.2.1) := by
  obtain ⟨hwin, hc, hpartner, hnone⟩ := hrow
  refine unopened_hit prims A x w hw hwin hc fun top state forgery hm => ?_
  rintro ⟨tree, hres⟩
  exact hnone ⟨_, SigningGuessProof.topPartner_resolved prims A x (w.1.1, w.2.1)
    (mem_exposedRun_of_joint prims A x w hw) hwin hpartner top state forgery hm tree hres⟩

set_option maxRecDepth 100000 in
/-- `AbsentRow` is an input-side hit on the unopened target. The absent start is a bottom start,
because the top setup caches every top start, and it leaves the bottom tree unopened. -/
theorem absentRow_hit (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hrow : AbsentRow prims x w) :
    HiddenInputHit x (unopenedTopTarget prims x (w.1, w.2.1)) (w.1, w.2.1) := by
  obtain ⟨hwin, hc, top, state, forgery, hm, l, hbottom | htop⟩ := hrow
  · refine unopened_hit prims A x w hw hwin hc fun top' state' forgery' hm' => ?_
    have he : (top, state, forgery) = (top', state', forgery') := Option.some.inj (hm.symm.trans hm')
    cases he
    exact topUnopened_of_bottomStart x w.2.1.1 top _ l hbottom
  · exact (htop (topStarts_cached prims A x _ (mem_exposedRun_of_joint prims A x w hw) hwin top state
      forgery hm _ l)).elim

end SigningTopRowsProof

/-- info: 'ThresholdLeanXmssSecurity.SigningTopRowsProof.topRow_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningTopRowsProof.topRow_hit

/-- info: 'ThresholdLeanXmssSecurity.SigningTopRowsProof.absentRow_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningTopRowsProof.absentRow_hit

end ThresholdLeanXmssSecurity
