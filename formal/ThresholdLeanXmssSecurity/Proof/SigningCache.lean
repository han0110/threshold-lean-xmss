import ThresholdLeanXmssSecurity.Proof.SigningDescent

/-!
# The final cache of the signing run

`RunHasFinalState` of `Proof/SigningDescent.lean`, by the lazy cache. The cache only grows, so each
computation of the run gives its value again on the final cache.

* `run_liftFree` and `run_liftFree_tweakable` read a computation of the run on the final cache.
* `exposedRun_facts` gives the top tree of `KeyGen`, the resolved verification and the freshness check.
* `verifyCached_of_resolves` gives `VerifyCached` from the resolved verification.
* `topRootReplay` and `honestSignatureReplay` are the dealer correctness of `referenceTree` on any
  cache (items 1 and 3 of `CacheConsistent`). The trees of `KeyGen` are the trees that leanVM replays.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningCacheProof

open SigningDescentProof

variable {C : Committee} (prims : Primitives)

/-! ## The authentication paths of the cache replay

Copied from leanVM `formal/lean_xmss/XmssSecurity/Proof/ConcreteCorrectness.lean`, which this
module does not import, with the names qualified. -/

section Replay

def pathNode (leafIndex : XmssSecurity.LeafIndex) (level : Nat) : XmssSecurity.MerkleNode :=
  XmssSecurity.Concrete.merkleNodeOfNat (leafIndex.val / 2 ^ level)

@[simp]
theorem pathNode_zero (leafIndex : XmssSecurity.LeafIndex) : pathNode leafIndex 0 = leafIndex := by
  apply Fin.ext
  simp only [pathNode, XmssSecurity.Concrete.merkleNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt leafIndex.isLt

theorem testBit_div_pow (value level : Nat) :
    (value / 2 ^ level).testBit 0 = value.testBit level := by
  simpa only [Nat.zero_add] using (Nat.testBit_add value 0 level).symm

theorem div_pow_succ (value level : Nat) :
    value / 2 ^ (level + 1) = (value / 2 ^ level) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem even_parts (value : Nat) (hbit : value.testBit 0 = false) :
    value = 2 * (value / 2) ∧ value ^^^ 1 = 2 * (value / 2) + 1 := by
  have heven : Even value := Nat.even_iff.mpr
    (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_even heven]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact congrArg (fun current => current + 1) h.symm

theorem odd_parts (value : Nat) (hbit : value.testBit 0 = true) :
    value = 2 * (value / 2) + 1 ∧ value ^^^ 1 = 2 * (value / 2) := by
  have hodd : Odd value := Nat.odd_iff.mpr
    (Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_odd hodd]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    calc
      value - 1 = (2 * (value / 2) + 1) - 1 :=
        congrArg (fun current => current - 1) h.symm
      _ = 2 * (value / 2) := by omega

theorem nodeIndex_eq_pathNode_succ (leafIndex : XmssSecurity.LeafIndex) (level : Nat) :
    XmssSecurity.Concrete.CacheView.nodeIndex leafIndex level = pathNode leafIndex (level + 1) := by
  apply Fin.ext
  simp only [XmssSecurity.Concrete.CacheView.nodeIndex, XmssSecurity.Concrete.nodeIndex, pathNode, XmssSecurity.Concrete.merkleNodeOfNat]
  exact (Nat.mod_eq_of_lt
    ((Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt)).symm

theorem pathNode_children (leafIndex : XmssSecurity.LeafIndex) (level : Nat) (hlevel : level < XmssSecurity.treeHeight) :
    if leafIndex.val.testBit level then
      XmssSecurity.Concrete.childNode (pathNode leafIndex (level + 1)) false =
          XmssSecurity.Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩ ∧
        XmssSecurity.Concrete.childNode (pathNode leafIndex (level + 1)) true = pathNode leafIndex level
    else
      XmssSecurity.Concrete.childNode (pathNode leafIndex (level + 1)) false = pathNode leafIndex level ∧
        XmssSecurity.Concrete.childNode (pathNode leafIndex (level + 1)) true =
          XmssSecurity.Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩ := by
  let quotient := leafIndex.val / 2 ^ level
  have hquotient : quotient < XmssSecurity.lifetime :=
    (Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt
  have hparent : (pathNode leafIndex (level + 1)).val = quotient / 2 := by
    simp only [pathNode, XmssSecurity.Concrete.merkleNodeOfNat]
    rw [div_pow_succ]
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self (leafIndex.val / 2 ^ level) _).trans_lt hquotient)
  have hcurrent : (pathNode leafIndex level).val = quotient := by
    simp [pathNode, XmssSecurity.Concrete.merkleNodeOfNat, quotient,
      Nat.mod_eq_of_lt hquotient]
  have hauth :
      (XmssSecurity.Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩).val =
        (quotient ^^^ 1) % XmssSecurity.lifetime := by
    rfl
  have hquotientBit : quotient.testBit 0 = leafIndex.val.testBit level := by
    exact testBit_div_pow leafIndex.val level
  by_cases hbit : leafIndex.val.testBit level = true
  · simp only [hbit, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := odd_parts quotient (hquotientBit.trans hbit)
    constructor
    · apply Fin.ext
      rw [hauth]
      simp only [XmssSecurity.Concrete.childNode, XmssSecurity.Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      exact congrArg (fun value => value % XmssSecurity.lifetime) hauthParts.symm

    · apply Fin.ext
      rw [hcurrent]
      simp only [XmssSecurity.Concrete.childNode, XmssSecurity.Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 1) % XmssSecurity.lifetime = quotient % XmssSecurity.lifetime :=
          congrArg (fun value => value % XmssSecurity.lifetime) hcurrentParts.symm
        _ = quotient := Nat.mod_eq_of_lt hquotient
  · have hbitFalse : leafIndex.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := even_parts quotient
      (hquotientBit.trans hbitFalse)
    constructor
    · apply Fin.ext
      rw [hcurrent]
      simp only [XmssSecurity.Concrete.childNode, XmssSecurity.Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 0) % XmssSecurity.lifetime = quotient % XmssSecurity.lifetime :=
          congrArg (fun value => value % XmssSecurity.lifetime) (by omega :
            2 * (quotient / 2) + 0 = quotient)
        _ = quotient := Nat.mod_eq_of_lt hquotient
    · apply Fin.ext
      rw [hauth]
      simp only [XmssSecurity.Concrete.childNode, XmssSecurity.Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      exact congrArg (fun value => value % XmssSecurity.lifetime) hauthParts.symm

theorem authentication_step_eq_treeNode (cache : QueryCache XmssSecurity.HashSpec)
    (parameter : XmssSecurity.PublicParameter) (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (leafIndex : XmssSecurity.LeafIndex) (level : Nat) (hlevel : level < XmssSecurity.treeHeight) :
    XmssSecurity.Concrete.CacheView.nodeHash cache parameter leafIndex level
        (XmssSecurity.Concrete.CacheReplay.treeNode cache parameter secret level (pathNode leafIndex level))
        (XmssSecurity.Concrete.CacheReplay.treeNode cache parameter secret level
          (XmssSecurity.Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩)) =
      XmssSecurity.Concrete.CacheReplay.treeNode cache parameter secret (level + 1) (pathNode leafIndex (level + 1)) := by
  have hnode := nodeIndex_eq_pathNode_succ leafIndex level
  have hchildren := pathNode_children leafIndex level hlevel
  by_cases hbit : leafIndex.val.testBit level = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [XmssSecurity.Concrete.CacheView.nodeHash, hlevel, XmssSecurity.Concrete.CacheView.nodeInput,
      XmssSecurity.Concrete.CacheView.authenticationNodePayload, XmssSecurity.Concrete.CacheView.merkleHash,
      XmssSecurity.Concrete.CacheView.merkleInput, XmssSecurity.Concrete.CacheReplay.treeNode_succ_eq, hbit, hnode, hleft, hright]
  · have hbitFalse : leafIndex.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [XmssSecurity.Concrete.CacheView.nodeHash, hlevel, XmssSecurity.Concrete.CacheView.nodeInput,
      XmssSecurity.Concrete.CacheView.authenticationNodePayload, XmssSecurity.Concrete.CacheView.merkleHash,
      XmssSecurity.Concrete.CacheView.merkleInput, XmssSecurity.Concrete.CacheReplay.treeNode_succ_eq, hbitFalse, hnode, hleft, hright]


def topPathNodeAt (key : XmssSecurity.TopIndex) (level : Nat) : XmssSecurity.TopNode :=
  XmssSecurity.Concrete.topNodeOfNat (key.val / 2 ^ level)

@[simp]
theorem topPathNodeAt_zero (key : XmssSecurity.TopIndex) : topPathNodeAt key 0 = key := by
  apply Fin.ext
  simp only [topPathNodeAt, XmssSecurity.Concrete.topNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt key.isLt

theorem topNodeIndex_eq_topPathNodeAt_succ (key : XmssSecurity.TopIndex) (level : Nat) :
    XmssSecurity.Concrete.topNodeIndex key level = topPathNodeAt key (level + 1) := by
  apply Fin.ext
  simp only [XmssSecurity.Concrete.topNodeIndex, topPathNodeAt, XmssSecurity.Concrete.topNodeOfNat]
  exact (Nat.mod_eq_of_lt ((Nat.div_le_self key.val _).trans_lt key.isLt)).symm

theorem topPathNode_children (key : XmssSecurity.TopIndex) (level : Nat) (hlevel : level < XmssSecurity.treeHeight) :
    if key.val.testBit level then
      XmssSecurity.Concrete.topChildNode (topPathNodeAt key (level + 1)) false =
          XmssSecurity.Concrete.topPathNode key ⟨level, hlevel⟩ ∧
        XmssSecurity.Concrete.topChildNode (topPathNodeAt key (level + 1)) true = topPathNodeAt key level
    else
      XmssSecurity.Concrete.topChildNode (topPathNodeAt key (level + 1)) false = topPathNodeAt key level ∧
        XmssSecurity.Concrete.topChildNode (topPathNodeAt key (level + 1)) true =
          XmssSecurity.Concrete.topPathNode key ⟨level, hlevel⟩ := by
  let quotient := key.val / 2 ^ level
  have hquotient : quotient < XmssSecurity.topLifetime := (Nat.div_le_self key.val _).trans_lt key.isLt
  have hparent : (topPathNodeAt key (level + 1)).val = quotient / 2 := by
    simp only [topPathNodeAt, XmssSecurity.Concrete.topNodeOfNat]
    rw [div_pow_succ]
    exact Nat.mod_eq_of_lt ((Nat.div_le_self (key.val / 2 ^ level) _).trans_lt hquotient)
  have hcurrent : (topPathNodeAt key level).val = quotient := by
    simp [topPathNodeAt, XmssSecurity.Concrete.topNodeOfNat, quotient, Nat.mod_eq_of_lt hquotient]
  have hauth : (XmssSecurity.Concrete.topPathNode key ⟨level, hlevel⟩).val = (quotient ^^^ 1) % XmssSecurity.topLifetime :=
    rfl
  have hquotientBit : quotient.testBit 0 = key.val.testBit level := testBit_div_pow key.val level
  by_cases hbit : key.val.testBit level = true
  · simp only [hbit, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := odd_parts quotient (hquotientBit.trans hbit)
    constructor
    · apply Fin.ext
      rw [hauth]
      simp only [XmssSecurity.Concrete.topChildNode, XmssSecurity.Concrete.topNodeOfNat, Bool.false_eq_true, ↓reduceIte,
        hparent]
      exact congrArg (fun value => value % XmssSecurity.topLifetime) hauthParts.symm
    · apply Fin.ext
      rw [hcurrent]
      simp only [XmssSecurity.Concrete.topChildNode, XmssSecurity.Concrete.topNodeOfNat, ↓reduceIte, hparent]
      rw [← hcurrentParts]
      exact Nat.mod_eq_of_lt hquotient
  · have hbitFalse : key.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := even_parts quotient (hquotientBit.trans hbitFalse)
    constructor
    · apply Fin.ext
      rw [hcurrent]
      simp only [XmssSecurity.Concrete.topChildNode, XmssSecurity.Concrete.topNodeOfNat, Bool.false_eq_true, ↓reduceIte,
        hparent, Nat.add_zero]
      rw [← hcurrentParts]
      exact Nat.mod_eq_of_lt hquotient
    · apply Fin.ext
      rw [hauth]
      simp only [XmssSecurity.Concrete.topChildNode, XmssSecurity.Concrete.topNodeOfNat, ↓reduceIte, hparent]
      exact congrArg (fun value => value % XmssSecurity.topLifetime) hauthParts.symm

theorem top_authentication_step_eq_topTreeNode (cache : QueryCache XmssSecurity.HashSpec)
    (parameter : XmssSecurity.PublicParameter) (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (key : XmssSecurity.TopIndex) (level : Nat) (hlevel : level < XmssSecurity.treeHeight) :
    XmssSecurity.Concrete.CacheView.topNodeHash cache parameter key level
        (XmssSecurity.Concrete.CacheReplay.topTreeNode cache parameter topSecret level (topPathNodeAt key level))
        (XmssSecurity.Concrete.CacheReplay.topTreeNode cache parameter topSecret level (XmssSecurity.Concrete.topPathNode key ⟨level, hlevel⟩)) =
      XmssSecurity.Concrete.CacheReplay.topTreeNode cache parameter topSecret (level + 1) (topPathNodeAt key (level + 1)) := by
  have hnode := topNodeIndex_eq_topPathNodeAt_succ key level
  have hchildren := topPathNode_children key level hlevel
  by_cases hbit : key.val.testBit level = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [XmssSecurity.Concrete.CacheView.topNodeHash, hlevel, XmssSecurity.Concrete.CacheView.topNodeInput,
      XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload, XmssSecurity.Concrete.CacheView.topMerkleHash,
      XmssSecurity.Concrete.CacheView.topMerkleInput, XmssSecurity.Concrete.CacheReplay.topTreeNode_succ_eq, hbit, hnode, hleft, hright]
  · have hbitFalse : key.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [XmssSecurity.Concrete.CacheView.topNodeHash, hlevel, XmssSecurity.Concrete.CacheView.topNodeInput,
      XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload, XmssSecurity.Concrete.CacheView.topMerkleHash,
      XmssSecurity.Concrete.CacheView.topMerkleInput, XmssSecurity.Concrete.CacheReplay.topTreeNode_succ_eq, hbitFalse, hnode, hleft, hright]

theorem topPath_ascends_to_topTreeNode (cache : QueryCache XmssSecurity.HashSpec)
    (parameter : XmssSecurity.PublicParameter)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (key : XmssSecurity.TopIndex) (levels : Nat) (hlevels : levels ≤ XmssSecurity.treeHeight) :
    XmssSecurity.Merkle.ascend (XmssSecurity.Concrete.CacheView.topNodeHash cache parameter key)
        (fun level => if hlevel : level < XmssSecurity.treeHeight then
          XmssSecurity.Concrete.CacheReplay.topTreeNode cache parameter topSecret level
            (XmssSecurity.Concrete.topPathNode key ⟨level, hlevel⟩) else 0) 0 levels
        (XmssSecurity.Concrete.CacheReplay.topLeafAt cache parameter topSecret key) =
      XmssSecurity.Concrete.CacheReplay.topTreeNode cache parameter topSecret levels
        (topPathNodeAt key levels) := by
  induction levels with
  | zero => simp [XmssSecurity.Merkle.ascend, XmssSecurity.Concrete.CacheReplay.topTreeNode_zero_eq]
  | succ level ih =>
      have hlevel : level < XmssSecurity.treeHeight := Nat.lt_of_succ_le hlevels
      rw [XmssSecurity.Merkle.ascend, ih (Nat.le_of_succ_le hlevels)]
      simp only [Nat.zero_add, hlevel, ↓reduceDIte]
      exact top_authentication_step_eq_topTreeNode cache parameter topSecret key level hlevel


theorem path_ascends_to_treeNode (cache : QueryCache XmssSecurity.HashSpec)
    (parameter : XmssSecurity.PublicParameter)
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (leafIndex : XmssSecurity.LeafIndex) (levels : Nat) (hlevels : levels ≤ XmssSecurity.treeHeight) :
    XmssSecurity.Merkle.ascend (XmssSecurity.Concrete.CacheView.nodeHash cache parameter leafIndex)
        (fun level => if hlevel : level < XmssSecurity.treeHeight then
          XmssSecurity.Concrete.CacheReplay.treeNode cache parameter secret level
            (XmssSecurity.Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩) else 0) 0 levels
        (XmssSecurity.Concrete.CacheReplay.leafAt cache parameter secret leafIndex) =
      XmssSecurity.Concrete.CacheReplay.treeNode cache parameter secret levels (pathNode leafIndex levels) := by
  induction levels with
  | zero => simp [XmssSecurity.Merkle.ascend, XmssSecurity.Concrete.CacheReplay.treeNode_zero_eq]
  | succ level ih =>
      have hlevel : level < XmssSecurity.treeHeight := Nat.lt_of_succ_le hlevels
      rw [XmssSecurity.Merkle.ascend, ih (Nat.le_of_succ_le hlevels)]
      simp only [Nat.zero_add, hlevel, ↓reduceDIte]
      exact authentication_step_eq_treeNode cache parameter secret leafIndex level hlevel


end Replay

/-! ## The lazy cache of the signing world -/

/-- The oracles of the signing world with the count. -/
abbrev countImpl : QueryImpl (WorldSpec C) (StateT (HashCache C × ℕ) ProbComp) :=
  SeedHitProof.withCount (SeedHitProof.signImpl prims)

/-- One query of the random-oracle computations of the signing world. -/
theorem roStep_support (t : (RoSpec C).Domain) (s : HashCache C) (p : (RoSpec C).Range t × HashCache C)
    (hp : p ∈ support ((((Query C →ₒ HashOutput).randomOracle + prgAnswer (C := C) prims) t).run s)) :
    s ≤ p.2 ∧ ∀ h, Agrees h p.2 → Id.run (fixedImpl prims h t) = p.1 := by
  rcases t with q | x
  · obtain ⟨hle, hself, -⟩ := randomOracle_support q s p hp
    exact ⟨hle, fun h ha => ha q p.1 hself⟩
  · change p ∈ support ((prgAnswer prims x).run s) at hp
    unfold prgAnswer at hp
    rw [StateT.run_bind] at hp
    simp only [support_bind] at hp
    obtain ⟨p', hp', hp⟩ := Set.mem_iUnion₂.mp hp
    simp only [StateT.run_pure, support_pure] at hp
    subst hp
    rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hp'
    obtain ⟨hle, hself, -⟩ := randomOracle_support _ s p' hp'
    exact ⟨hle, fun h ha => by
      change prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2 = _
      rw [ha _ _ hself]⟩

/-- Each query of the signing world only adds entries to the cache. -/
theorem countImpl_grows (t : (WorldSpec C).Domain) (s : HashCache C × ℕ)
    (z : (WorldSpec C).Range t × HashCache C × ℕ) (hz : z ∈ support ((countImpl prims t).run s)) :
    s.1 ≤ z.2.1 := by
  have hlocal : ∀ (u : (LocalSpec C).Domain) (c : HashCache C) (p : (LocalSpec C).Range u × HashCache C),
      p ∈ support ((signingLocalAnswer prims u).run c) → c ≤ p.2 := by
    rintro (n | u) c p hp
    · change p ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run c) at hp
      simp [unifFwdImpl] at hp
      obtain ⟨a, rfl⟩ := hp
      exact le_rfl
    · exact (roStep_support prims u c p hp).1
  obtain ⟨c, k⟩ := s
  simp only [countImpl, SeedHitProof.withCount, StateT.run_mk, support_map] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  rcases t with (u | x) | u
  · exact hlocal u c p hp
  · change p ∈ support ((programAnswer x).run c) at hp
    unfold programAnswer at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp with hx
    · simp at hp
      subst hp
      exact le_rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure] at hp
      subst hp
      have hnone : c x.1 = none := by
        simpa using (not_or.mp hx).2
      exact QueryCache.le_cacheQuery _ hnone
  · exact hlocal u c p hp

/-- A run of the signing world only adds entries to the cache. -/
theorem countRun_grows {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ s, ∀ z ∈ support ((simulateQ (countImpl prims) oa).run s), s.1 ≤ z.2.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | query_bind t k ih =>
    intro s z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact (countImpl_grows prims t s p hp).trans (ih p.1 p.2 z hz)

/-- A random-oracle computation on the free copy gives its value with `H` fixed to any function that
agrees with the final cache. -/
theorem run_liftFree {α : Type} (oa : OracleComp (RoSpec C) α) :
    ∀ s, ∀ z ∈ support ((simulateQ (countImpl prims) (SigningSecurityProof.liftFree oa)).run s),
      ∀ h, Agrees h z.2.1 → z.1 = D prims h oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz h _
    simp [SigningSecurityProof.liftFree, free] at hz
    subst hz
    rfl
  | query_bind t k ih =>
    intro s z hz h ha
    simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind,
      support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    have hp' : p ∈ support ((countImpl prims (.inr (.inr t))).run s) := by
      rw [free] at hp
      erw [liftComp_query, simulateQ_query] at hp
      simp at hp
      exact hp
    simp only [countImpl, SeedHitProof.withCount, StateT.run_mk, support_map] at hp'
    obtain ⟨p', hp', rfl⟩ := hp'
    obtain ⟨hle, hd⟩ := roStep_support prims t s.1 p' hp'
    have hgrow := countRun_grows prims _ _ z hz
    rw [ih p'.1 _ z hz h ha, ← hd h (ha.mono hgrow)]
    simp [D, simulateQ_bind]

theorem run_bind_support {α β : Type} (oa : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β)
    (s : HashCache C × ℕ) (z : β × HashCache C × ℕ)
    (hz : z ∈ support ((simulateQ (countImpl prims) (oa >>= f)).run s)) :
    ∃ p ∈ support ((simulateQ (countImpl prims) oa).run s), z ∈ support ((simulateQ (countImpl prims) (f p.1)).run p.2) := by
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨p, hp, hz⟩ := hz
  exact ⟨p, hp, hz⟩

/-- A query of `H` on the free copy leaves its answer in the cache. -/
theorem run_hashQuery (q : Query C) (s : HashCache C × ℕ) (p : HashOutput × HashCache C × ℕ)
    (hp : p ∈ support ((simulateQ (countImpl prims) (SigningSecurityProof.liftFree (hashQuery q))).run s)) :
    p.2.1 q = some p.1 := by
  have hp' : p ∈ support ((countImpl prims (.inr (.inr (.inl q)))).run s) := by
    rw [SigningSecurityProof.liftFree, hashQuery, free] at hp
    erw [liftComp_query, simulateQ_query] at hp
    simp at hp
    exact hp
  simp only [countImpl, SeedHitProof.withCount, StateT.run_mk, support_map] at hp'
  obtain ⟨p', hp', rfl⟩ := hp'
  exact (randomOracle_support q s.1 p' hp').2.1

/-- A computation of leanVM under `tweakable` on the free copy resolves on the final cache. -/
theorem run_liftFree_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    ∀ s, ∀ z ∈ support ((simulateQ (countImpl prims) (SigningSecurityProof.liftFree (tweakable (C := C) oa))).run s),
      DeterministicSigning.Resolves (thView z.2.1) oa z.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz
    simp [SigningSecurityProof.liftFree, free, tweakable] at hz
    subst hz
    exact .pure _
  | query_bind x k ih =>
    intro s z hz
    have htw : tweakable (C := C) (liftM (OracleSpec.query x) >>= k) = hashQuery (.hash x) >>= fun a => tweakable (k a) := by
      simp [tweakable, simulateQ_bind]
    rw [htw, SigningSecurityProof.liftFree, liftComp_bind, free_bind] at hz
    obtain ⟨p, hp, hz⟩ := run_bind_support prims _ _ s z hz
    have hgrow := countRun_grows prims _ _ z hz
    exact .query x p.1 (hgrow (run_hashQuery prims (.hash x) s p hp)) k z.1 (ih p.1 p.2 z hz)

/-! ## The signature of `KeyGen` under a monad map -/

section Hom

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] (hom : m →ᵐ n)

theorem hom_honestSignature (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (P : PublicParameter)
    (keys : C.Party → Keys C) (top : TopTree) (value : Point → m Digest) (e : KeyIndex) (message : Message) :
    hom (honestSignature lift (dealtWith lift P keys top value) e message) =
      honestSignature (fun oa => hom (lift oa)) (dealtWith (fun oa => hom (lift oa)) P keys top
        (fun x => hom (value x))) e message := by
  simp only [honestSignature, dealtWith, MonadHom.mmap_bind, SeedHitProof.hom_map,
    SeedHitProof.hom_referenceTree]
  congr 1; funext tree
  rcases tree with _ | tree
  · exact hom.toFun_pure' _
  simp only [MonadHom.mmap_bind]
  congr 1; funext ρ
  congr 1; funext r
  rcases r with _ | ⟨randomness, encoding⟩
  · exact hom.toFun_pure' _
  simp only [MonadHom.mmap_bind, SeedHitProof.hom_sequenceFin, MonadHom.mmap_pure]
  congr 2
  funext l
  split
  · rfl
  · exact hom.toFun_pure' _
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure]

end Hom

/-- The free copy as a monad map. -/
def freeHom : OracleComp (RoSpec C) →ᵐ OracleComp (WorldSpec C) where
  toFun _ oa := SigningSecurityProof.liftFree oa
  toFun_pure' a := φ_pure a
  toFun_bind' oa f := φ_bind oa f

/-- `H` fixed to `h` as a monad map. -/
def fixedHom (h : Query C → HashOutput) : OracleComp (RoSpec C) →ᵐ Id where
  toFun _ oa := D prims h oa
  toFun_pure' a := D_pure (prims := prims) h a
  toFun_bind' oa f := D_bind (prims := prims) h oa f

set_option maxRecDepth 100000 in
theorem liftFree_honestSignature (P : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (e : KeyIndex) (message : Message) :
    honestSignature (fun oa => SigningSecurityProof.liftFree oa)
        (dealtWith (fun oa => SigningSecurityProof.liftFree oa) P keys top
          (fun x => SigningSecurityProof.liftFree (prfValue seeds x))) e message =
      SigningSecurityProof.liftFree (honestSignature (fun oa => oa)
        (dealtWith (fun oa => oa) P keys top (prfValue seeds)) e message) :=
  (hom_honestSignature freeHom (fun oa => oa) P keys top (prfValue seeds) e message).symm

set_option maxRecDepth 100000 in
theorem D_honestSignature (h : Query C → HashOutput) (P : PublicParameter) (keys : C.Party → Keys C)
    (top : TopTree) (seeds : C.Term → HashOutput) (e : KeyIndex) (message : Message) :
    honestSignature (m := Id) (fun oa => D prims h oa)
        (dealtWith (fun oa => D prims h oa) P keys top (fun x => D prims h (prfValue seeds x))) e message =
      D prims h (honestSignature (fun oa => oa) (dealtWith (fun oa => oa) P keys top (prfValue seeds)) e message) :=
  (hom_honestSignature (fixedHom prims h) (fun oa => oa) P keys top (prfValue seeds) e message).symm

/-- `H` fixed to a cache. -/
abbrev answersOf (c : HashCache C) : Query C → HashOutput := fun q => (c q).getD 0

theorem agrees_answersOf {c c' : HashCache C} (hle : c ≤ c') : Agrees (answersOf c') c := by
  intro q v hq
  simp [answersOf, hle hq]

theorem thView_mono {c c' : HashCache C} (hle : c ≤ c') : thView c ≤ thView c' :=
  fun _ _ h => hle h

/-! ## The inputs that a resolved verification evaluates -/

section Resolved

open DeterministicSigning

variable {K : QueryCache XmssSecurity.HashSpec}

theorem resolves_value {α : Type} {oa : OracleComp XmssSecurity.HashSpec α} {v : α} (h : Resolves K oa v) :
    evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn K) oa = v :=
  h.eval _ fun x a hx => by
    simp [XmssSecurity.Concrete.CacheReplay.answerFn, XmssSecurity.Concrete.CacheReplay.answer, hx]

theorem resolves_tweakableHash {P : XmssSecurity.PublicParameter} {domain : XmssSecurity.HashDomain}
    {payload : XmssSecurity.HashInput} {v : XmssSecurity.Digest}
    (h : Resolves K (XmssSecurity.Concrete.tweakableHash P domain payload : OracleComp XmssSecurity.HashSpec _) v) :
    (K (XmssSecurity.tweakableHashInput P domain payload)).isSome := by
  unfold XmssSecurity.Concrete.tweakableHash XmssSecurity.Concrete.oracleHash at h
  obtain ⟨a, ha, -⟩ := h.query_inv
  simp [ha]

theorem resolves_chainWalk {P : XmssSecurity.PublicParameter} {e : XmssSecurity.LeafIndex}
    {l : XmssSecurity.ChainIndex} (pos : ℕ) (v : XmssSecurity.Digest) :
    ∀ (n : ℕ) (w : XmssSecurity.Digest),
      Resolves K (XmssSecurity.Concrete.chainWalk P e l pos n v : OracleComp XmssSecurity.HashSpec _) w →
      ∀ k, pos ≤ k → k < pos + n → ∀ hk : k < XmssSecurity.chainLength - 1,
        (K (XmssSecurity.Concrete.CacheView.chainInput P e l ⟨k, hk⟩
          (XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.chainStep K P e l) pos (k - pos) v))).isSome := by
  intro n
  induction n with
  | zero => intro w _ k h1 h2; omega
  | succ n ih =>
    intro w h k h1 h2 hk
    simp only [XmssSecurity.Concrete.chainWalk] at h
    obtain ⟨prev, hprev, hrest⟩ := h.of_bind
    rcases Nat.lt_or_ge k (pos + n) with hlt | hge
    · exact ih prev hprev k h1 hlt hk
    have hkeq : k = pos + n := by omega
    subst hkeq
    rw [dif_pos hk] at hrest
    have hval := resolves_value hprev
    rw [XmssSecurity.Concrete.CacheReplay.eval_chainWalk] at hval
    rw [show pos + n - pos = n by omega, hval]
    exact resolves_tweakableHash hrest

theorem resolves_topChainWalk {P : XmssSecurity.PublicParameter} {e : XmssSecurity.TopIndex}
    {l : XmssSecurity.ChainIndex} (pos : ℕ) (v : XmssSecurity.Digest) :
    ∀ (n : ℕ) (w : XmssSecurity.Digest),
      Resolves K (XmssSecurity.Concrete.topChainWalk P e l pos n v : OracleComp XmssSecurity.HashSpec _) w →
      ∀ k, pos ≤ k → k < pos + n → ∀ hk : k < XmssSecurity.chainLength - 1,
        (K (XmssSecurity.Concrete.CacheView.topChainInput P e l ⟨k, hk⟩
          (XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.topChainStep K P e l) pos (k - pos) v))).isSome := by
  intro n
  induction n with
  | zero => intro w _ k h1 h2; omega
  | succ n ih =>
    intro w h k h1 h2 hk
    simp only [XmssSecurity.Concrete.topChainWalk] at h
    obtain ⟨prev, hprev, hrest⟩ := h.of_bind
    rcases Nat.lt_or_ge k (pos + n) with hlt | hge
    · exact ih prev hprev k h1 hlt hk
    have hkeq : k = pos + n := by omega
    subst hkeq
    rw [dif_pos hk] at hrest
    have hval := resolves_value hprev
    rw [XmssSecurity.Concrete.CacheReplay.eval_topChainWalk] at hval
    rw [show pos + n - pos = n by omega, hval]
    exact resolves_tweakableHash hrest

theorem resolves_authenticationRoot {P : XmssSecurity.PublicParameter} {e : XmssSecurity.LeafIndex}
    {σ : XmssSecurity.Signature} (leaf : XmssSecurity.Digest) :
    ∀ (n : ℕ) (w : XmssSecurity.Digest),
      Resolves K (XmssSecurity.Concrete.authenticationRoot P e σ n leaf : OracleComp XmssSecurity.HashSpec _) w →
      ∀ level < n, ∀ hlevel : level < XmssSecurity.treeHeight,
        (K (XmssSecurity.Concrete.CacheView.nodeInput P e ⟨level, hlevel⟩
          (XmssSecurity.Merkle.ascend (XmssSecurity.Concrete.CacheView.nodeHash K P e)
            (XmssSecurity.Concrete.signaturePath σ) 0 level leaf)
          (XmssSecurity.Concrete.signaturePath σ level))).isSome := by
  intro n
  induction n with
  | zero => intro w _ level h; omega
  | succ n ih =>
    intro w h level h1 hlevel
    simp only [XmssSecurity.Concrete.authenticationRoot] at h
    obtain ⟨current, hcurrent, hrest⟩ := h.of_bind
    rcases Nat.lt_or_ge level n with hlt | hge
    · exact ih current hcurrent level hlt hlevel
    have hleq : level = n := by omega
    subst hleq
    have hval := resolves_value hcurrent
    rw [XmssSecurity.Concrete.CacheReplay.eval_authenticationRoot] at hval
    rw [hval]
    unfold XmssSecurity.Concrete.authenticationNodeHash at hrest
    rw [dif_pos hlevel] at hrest
    unfold XmssSecurity.Concrete.nodeHash at hrest
    unfold XmssSecurity.Concrete.CacheView.nodeInput XmssSecurity.Concrete.CacheView.authenticationNodePayload
    by_cases hb : (e : ℕ).testBit level = true
    · rw [if_pos hb] at hrest
      rw [if_pos hb]
      exact resolves_tweakableHash hrest
    · rw [if_neg hb] at hrest
      rw [if_neg hb]
      exact resolves_tweakableHash hrest


theorem resolves_topAuthenticationRoot {P : XmssSecurity.PublicParameter} {key : XmssSecurity.TopIndex}
    {part : XmssSecurity.LayerSignature} (leaf : XmssSecurity.Digest) :
    ∀ (n : ℕ) (w : XmssSecurity.Digest),
      Resolves K (XmssSecurity.Concrete.topAuthenticationRoot P key part.authPath n leaf :
        OracleComp XmssSecurity.HashSpec _) w →
      ∀ level < n, ∀ hlevel : level < XmssSecurity.treeHeight,
        (K (XmssSecurity.Concrete.CacheView.topNodeInput P key ⟨level, hlevel⟩
          (XmssSecurity.Merkle.ascend (XmssSecurity.Concrete.CacheView.topNodeHash K P key)
            (XmssSecurity.Concrete.layerPath part) 0 level leaf)
          (XmssSecurity.Concrete.layerPath part level))).isSome := by
  intro n
  induction n with
  | zero => intro w _ level h; omega
  | succ n ih =>
    intro w h level h1 hlevel
    simp only [XmssSecurity.Concrete.topAuthenticationRoot] at h
    obtain ⟨current, hcurrent, hrest⟩ := h.of_bind
    rcases Nat.lt_or_ge level n with hlt | hge
    · exact ih current hcurrent level hlt hlevel
    have hleq : level = n := by omega
    subst hleq
    have hval := resolves_value hcurrent
    rw [XmssSecurity.Concrete.CacheReplay.eval_topAuthenticationRoot] at hval
    rw [show XmssSecurity.Concrete.layerPath ⟨0, fun _ => 0, part.authPath⟩ = XmssSecurity.Concrete.layerPath part
      from rfl] at hval
    rw [hval]
    rw [dif_pos hlevel] at hrest
    unfold XmssSecurity.Concrete.topNodeHash at hrest
    have hpath : XmssSecurity.Concrete.layerPath part level = part.authPath ⟨level, hlevel⟩ := by
      simp [XmssSecurity.Concrete.layerPath, hlevel]
    rw [hpath]
    unfold XmssSecurity.Concrete.CacheView.topNodeInput XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload
    by_cases hb : (key : ℕ).testBit level = true
    · rw [if_pos hb] at hrest
      rw [if_pos hb]
      exact resolves_tweakableHash hrest
    · rw [if_neg hb] at hrest
      rw [if_neg hb]
      exact resolves_tweakableHash hrest


/-- A verification that resolves on the final cache evaluates only cached inputs. -/
theorem verifyCached_of_resolves (c : HashCache C) (pk : XmssSecurity.PublicKey) (e : XmssSecurity.LeafIndex)
    (message : XmssSecurity.Message) (σ : XmssSecurity.Signature) (b : Bool)
    (h : DeterministicSigning.Resolves (thView c) (XmssSecurity.Concrete.verify pk e message σ : OracleComp XmssSecurity.HashSpec _) b) :
    VerifyCached c pk.parameter e message σ := by
  intro encoding hdec
  unfold XmssSecurity.Concrete.verify at h
  obtain ⟨d, hd, h⟩ := h.of_bind
  have hdv := resolves_value hd
  rw [XmssSecurity.Concrete.CacheReplay.eval_encodingHash] at hdv
  rw [← hdv, hdec] at h
  obtain ⟨ends, hends, h⟩ := h.of_bind
  have hendsv := resolves_value hends
  rw [XmssSecurity.Concrete.CacheReplay.eval_recoverEndpoints] at hendsv
  obtain ⟨leaf, hleaf, h⟩ := h.of_bind
  have hleafv := resolves_value hleaf
  rw [XmssSecurity.Concrete.CacheReplay.eval_leafHash] at hleafv
  unfold XmssSecurity.Concrete.verifyAfterLeaf at h
  obtain ⟨root, hroot, h⟩ := h.of_bind
  have hrootv := resolves_value hroot
  rw [XmssSecurity.Concrete.CacheReplay.eval_authenticationRoot] at hrootv
  subst hendsv hleafv hrootv
  unfold XmssSecurity.Concrete.recoverEndpoints at hends
  refine ⟨⟨fun l k h1 h2 => ?_, ?_, fun level hlevel => ⟨hlevel, ?_⟩⟩, fun topCodeword htop => ?_⟩
  · have hl := DeterministicSigning.Resolves.of_sequenceFin hends l
    unfold XmssSecurity.Concrete.recoverChain at hl
    exact ⟨h2, resolves_chainWalk _ _ _ _ hl k h1 (by have := (encoding l).isLt; omega) h2⟩
  · unfold XmssSecurity.Concrete.leafHash at hleaf
    exact resolves_tweakableHash hleaf
  · exact resolves_authenticationRoot _ _ _ hroot level hlevel hlevel
  unfold XmssSecurity.Concrete.verifyTop at h
  obtain ⟨d2, hd2, h⟩ := h.of_bind
  have hd2v := resolves_value hd2
  have htopHash : evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn (thView c))
      (XmssSecurity.Concrete.topEncodingHash pk.parameter (XmssSecurity.topKeyOf e) (forgedRoot c pk.parameter e encoding σ)
        σ.top.randomness : OracleComp XmssSecurity.HashSpec _) =
      XmssSecurity.Concrete.CacheView.topEncodingHash (thView c) pk.parameter (XmssSecurity.topKeyOf e)
        (forgedRoot c pk.parameter e encoding σ, σ.top.randomness) := by
    simp [XmssSecurity.Concrete.topEncodingHash, XmssSecurity.Concrete.CacheView.topEncodingHash, XmssSecurity.Concrete.CacheView.topEncodingInput, XmssSecurity.Concrete.CacheView.tweakableHash]
  have hd2v' := htopHash.symm.trans hd2v
  rw [← hd2v', htop] at h
  obtain ⟨ends, hends, h⟩ := h.of_bind
  have hendsv := resolves_value hends
  rw [XmssSecurity.Concrete.CacheReplay.eval_sequenceFin] at hendsv
  obtain ⟨leaf, hleaf, h⟩ := h.of_bind
  have hleafv := resolves_value hleaf
  have htopLeaf : ∀ endpoints, evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn (thView c))
      (XmssSecurity.Concrete.topLeafHash pk.parameter (XmssSecurity.topKeyOf e) endpoints : OracleComp XmssSecurity.HashSpec _) =
      XmssSecurity.Concrete.CacheView.topLeafHash (thView c) pk.parameter (XmssSecurity.topKeyOf e) endpoints := by
    intro endpoints
    simp [XmssSecurity.Concrete.topLeafHash, XmssSecurity.Concrete.CacheView.topLeafHash, XmssSecurity.Concrete.CacheView.topLeafInput, XmssSecurity.Concrete.CacheView.tweakableHash]
  rw [htopLeaf] at hleafv
  obtain ⟨root, hroot, -⟩ := h.of_bind
  have hendsv' : XmssSecurity.recoveredEndpoints (topStep c pk.parameter e) topCodeword σ.top.chainValue = ends := by
    rw [← hendsv]
    funext i
    simp [XmssSecurity.Concrete.CacheReplay.eval_topChainWalk, XmssSecurity.recoveredEndpoints, XmssSecurity.Wots.recoverChain]
  subst hendsv' hleafv
  refine ⟨fun l k h1 h2 => ?_, ?_, fun level hlevel => ⟨hlevel, ?_⟩⟩
  · have hl := DeterministicSigning.Resolves.of_sequenceFin hends l
    exact ⟨h2, resolves_topChainWalk _ _ _ _ hl k h1 (by have := (topCodeword l).isLt; omega) h2⟩
  · unfold XmssSecurity.Concrete.topLeafHash at hleaf
    exact resolves_tweakableHash hleaf
  · exact resolves_topAuthenticationRoot _ _ _ hroot level hlevel hlevel

end Resolved

/-! ## The run of the game -/

set_option maxRecDepth 100000 in
theorem exposedRun_facts (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × HashCache C × ℕ)
    (hr : r ∈ support (exposedRun prims A x)) (hwin : r.1.1 = (true, false)) :
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      D prims (answersOf r.2.1) (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) = some (.top top) ∧
      DeterministicSigning.Resolves (thView r.2.1)
        (XmssSecurity.Concrete.verify (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩) forgery.signature.leafIndex
          forgery.message (XmssSecurity.Bridge.toModelSig forgery.signature)) true ∧
      ((signersAt state forgery.signature.leafIndex forgery.message).card < C.t ∨
        D prims (answersOf r.2.1) (honestSignature (fun oa => oa)
          (dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1))
          forgery.signature.leafIndex forgery.message) ≠ some forgery.signature) := by
  unfold exposedRun finalRun at hr
  dsimp only at hr
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _] at hr
  obtain ⟨p, hp, hr⟩ := run_bind_support prims _ _ _ r hr
  have hval := run_liftFree prims _ _ p hp (answersOf r.2.1) (agrees_answersOf (countRun_grows prims _ _ r hr))
  rcases hp1 : p.1 with _ | (top | tree)
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hwin
  swap
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hwin
  rw [hp1] at hr hval
  obtain ⟨q, hq, hr⟩ := run_bind_support prims _ _ _ r hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  simp only [Prod.mk.injEq] at hwin
  unfold SigningCoreProof.tsigFinish at hw
  obtain ⟨v, hv, hw⟩ := run_bind_support prims _ _ _ w hw
  dsimp only at hw
  split_ifs at hw with hlt
  · simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    have hres := run_liftFree_tweakable prims _ _ v hv
    simp only [Bool.and_true] at hwin
    obtain ⟨hv1, -⟩ := hwin
    refine ⟨top, q.1.2.1, q.1.1, rfl, hval.symm, ?_, Or.inl hlt⟩
    rw [hv1] at hres
    rwa [XmssSecurity.Bridge.verify_real] at hres
  · rw [show honestSignature (fun oa => SigningCoreProof.honestLift oa)
        (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top
          fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) q.1.1.signature.leafIndex q.1.1.message =
        SigningSecurityProof.liftFree (honestSignature (fun oa => oa)
          (dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1))
          q.1.1.signature.leafIndex q.1.1.message) from liftFree_honestSignature _ _ _ _ _ _] at hw
    obtain ⟨f, hf, hw⟩ := run_bind_support prims _ _ _ w hw
    simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    have hres := run_liftFree_tweakable prims _ _ v hv
    have hgv := countRun_grows prims _ _ f hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
    obtain ⟨⟨hv1, hne⟩, -⟩ := hwin
    refine ⟨top, q.1.2.1, q.1.1, rfl, hval.symm, ?_, Or.inr ?_⟩
    · rw [hv1] at hres
      have hres' := hres.mono (thView_mono hgv)
      rwa [XmssSecurity.Bridge.verify_real] at hres'
    · rw [← run_liftFree prims _ _ f hf _ (agrees_answersOf le_rfl)]
      exact hne



/-! ## The trees of `KeyGen` on a cache -/

theorem leafKey_top (j : ℕ) (hj : j < 2 ^ 16) :
    (⟨j % lifetime, Nat.mod_lt _ (by decide)⟩ : KeyIndex) =
      XmssSecurity.Bridge.topKey (XmssSecurity.Concrete.topNodeOfNat j) := by
  apply Fin.ext
  simp only [XmssSecurity.Bridge.topKey, XmssSecurity.Concrete.topNodeOfNat, lifetime, numLayers, layerHeight,
    XmssSecurity.topLifetime, XmssSecurity.treeHeight]
  omega

theorem eval_merkleNode_top (K : QueryCache XmssSecurity.HashSpec) (P : PublicParameter)
    (chainEnd : KeyIndex → ChainIndex → Digest) (S : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (hS : ∀ b l, chainEnd (XmssSecurity.Bridge.topKey b) l =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.topChainStep K P b l) 0 (XmssSecurity.chainLength - 1)
        (S b l)) :
    ∀ level ≤ 16, ∀ j < 2 ^ (16 - level),
      evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn K) (merkleNode P topLayer chainEnd level j) =
        XmssSecurity.Concrete.CacheReplay.topTreeNode K P S level (XmssSecurity.Concrete.topNodeOfNat j) := by
  intro level
  induction level with
  | zero =>
    intro _ j hj
    rw [merkleNode, leafKey_top j (by simpa using hj), XmssSecurity.Bridge.leafHash_top,
      XmssSecurity.Concrete.CacheReplay.topTreeNode_zero_eq, show chainEnd _ = _ from funext (hS _)]
    erw [XmssSecurity.Concrete.CacheReplay.eval_tweakableHash]
    rfl
  | succ level ih =>
    intro hlevel j hj
    have hlt : level < XmssSecurity.treeHeight := by simp only [XmssSecurity.treeHeight]; omega
    have hj2 : 2 * j + 1 < 2 ^ (16 - level) := by
      rw [show 16 - level = 16 - (level + 1) + 1 by omega, pow_succ]
      omega
    have hjlt : j < 65536 := by
      have := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (show 16 - (level + 1) ≤ 16 by omega))
      simpa using this
    have hval : (XmssSecurity.Concrete.topNodeOfNat j).val = j := by
      simp [XmssSecurity.Concrete.topNodeOfNat, XmssSecurity.topLifetime, XmssSecurity.treeHeight,
        Nat.mod_eq_of_lt hjlt]
    have hleft : XmssSecurity.Concrete.topChildNode (XmssSecurity.Concrete.topNodeOfNat j) false =
        XmssSecurity.Concrete.topNodeOfNat (2 * j) := by
      apply Fin.ext
      simp [XmssSecurity.Concrete.topChildNode, XmssSecurity.Concrete.topNodeOfNat, XmssSecurity.topLifetime,
        XmssSecurity.treeHeight, Nat.mod_eq_of_lt hjlt]
    have hright : XmssSecurity.Concrete.topChildNode (XmssSecurity.Concrete.topNodeOfNat j) true =
        XmssSecurity.Concrete.topNodeOfNat (2 * j + 1) := by
      apply Fin.ext
      simp [XmssSecurity.Concrete.topChildNode, XmssSecurity.Concrete.topNodeOfNat, XmssSecurity.topLifetime,
        XmssSecurity.treeHeight, Nat.mod_eq_of_lt hjlt]
    have hnode : ∀ left right : Digest,
        (Concrete.tweakableHash P (.node topLayer (level + 1) j) (Concrete.nodePayload left right) :
          OracleComp HashSpec Digest) =
        (XmssSecurity.Concrete.topNodeHash P ⟨level, hlt⟩ (XmssSecurity.Concrete.topNodeOfNat j) left right :
          OracleComp XmssSecurity.HashSpec _) := by
      intro left right
      have h := XmssSecurity.Bridge.nodeHash_top P ⟨level, hlt⟩ (XmssSecurity.Concrete.topNodeOfNat j) left right
      rw [hval] at h
      exact h
    rw [merkleNode, XmssSecurity.Concrete.CacheReplay.topTreeNode_succ_eq, dif_pos hlt, hleft, hright]
    simp only [hnode]
    erw [evalWithAnswerFn_bind, ih (by omega) (2 * j) (by omega), evalWithAnswerFn_bind,
      ih (by omega) (2 * j + 1) hj2]
    erw [XmssSecurity.Concrete.CacheReplay.eval_tweakableHash]
    rfl


theorem leafKey_bottom (j : ℕ) :
    (⟨j % lifetime, Nat.mod_lt _ (by decide)⟩ : KeyIndex) = XmssSecurity.Concrete.merkleNodeOfNat j := by
  apply Fin.ext
  simp [XmssSecurity.Concrete.merkleNodeOfNat, lifetime, XmssSecurity.lifetime, numLayers, layerHeight,
    XmssSecurity.treeHeight]

theorem eval_merkleNode_bottom (K : QueryCache XmssSecurity.HashSpec) (P : PublicParameter)
    (chainEnd : KeyIndex → ChainIndex → Digest) (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest) :
    ∀ level ≤ 16, ∀ j < 2 ^ (32 - level),
      (∀ i : XmssSecurity.LeafIndex, i.val / 2 ^ level = j → ∀ l, chainEnd i l =
        XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.chainStep K P i l) 0 (XmssSecurity.chainLength - 1)
          (secret i l)) →
      evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn K) (merkleNode P bottomLayer chainEnd level j) =
        XmssSecurity.Concrete.CacheReplay.treeNode K P secret level (XmssSecurity.Concrete.merkleNodeOfNat j) := by
  intro level
  induction level with
  | zero =>
    intro _ j hj hS
    have hjlt : j < 4294967296 := by simpa using hj
    have hval : (XmssSecurity.Concrete.merkleNodeOfNat j).val = j := by
      simp [XmssSecurity.Concrete.merkleNodeOfNat, XmssSecurity.lifetime, XmssSecurity.treeHeight,
        Nat.mod_eq_of_lt hjlt]
    have hends := funext (hS (XmssSecurity.Concrete.merkleNodeOfNat j) (by simpa using hval))
    rw [merkleNode, leafKey_bottom j, XmssSecurity.Bridge.leafHash_bottom,
      XmssSecurity.Concrete.CacheReplay.treeNode_zero_eq, hends]
    erw [XmssSecurity.Concrete.CacheReplay.eval_tweakableHash]
    rfl
  | succ level ih =>
    intro hlevel j hj hS
    have hlt : level < XmssSecurity.treeHeight := by simp only [XmssSecurity.treeHeight]; omega
    have hj2 : 2 * j + 1 < 2 ^ (32 - level) := by
      rw [show 32 - level = 32 - (level + 1) + 1 by omega, pow_succ]
      omega
    have hjlt : j < 4294967296 := by
      have := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (show 32 - (level + 1) ≤ 32 by omega))
      simpa using this
    have hval : (XmssSecurity.Concrete.merkleNodeOfNat j).val = j := by
      simp [XmssSecurity.Concrete.merkleNodeOfNat, XmssSecurity.lifetime, XmssSecurity.treeHeight,
        Nat.mod_eq_of_lt hjlt]
    have hleft : XmssSecurity.Concrete.childNode (XmssSecurity.Concrete.merkleNodeOfNat j) false =
        XmssSecurity.Concrete.merkleNodeOfNat (2 * j) := by
      apply Fin.ext
      simp [XmssSecurity.Concrete.childNode, XmssSecurity.Concrete.merkleNodeOfNat, XmssSecurity.lifetime,
        XmssSecurity.treeHeight, Nat.mod_eq_of_lt hjlt]
    have hright : XmssSecurity.Concrete.childNode (XmssSecurity.Concrete.merkleNodeOfNat j) true =
        XmssSecurity.Concrete.merkleNodeOfNat (2 * j + 1) := by
      apply Fin.ext
      simp [XmssSecurity.Concrete.childNode, XmssSecurity.Concrete.merkleNodeOfNat, XmssSecurity.lifetime,
        XmssSecurity.treeHeight, Nat.mod_eq_of_lt hjlt]
    have hnode : ∀ left right : Digest,
        (Concrete.tweakableHash P (.node bottomLayer (level + 1) j) (Concrete.nodePayload left right) :
          OracleComp HashSpec Digest) =
        (XmssSecurity.Concrete.nodeHash P ⟨level, hlt⟩ (XmssSecurity.Concrete.merkleNodeOfNat j) left right :
          OracleComp XmssSecurity.HashSpec _) := by
      intro left right
      have h := XmssSecurity.Bridge.nodeHash_bottom P ⟨level, hlt⟩ (XmssSecurity.Concrete.merkleNodeOfNat j) left right
      rw [hval] at h
      exact h
    have hchild : ∀ c < 2, ∀ i : XmssSecurity.LeafIndex, i.val / 2 ^ level = 2 * j + c → i.val / 2 ^ (level + 1) = j := by
      intro c hc i hi
      rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]
      omega
    rw [merkleNode, XmssSecurity.Concrete.CacheReplay.treeNode_succ_eq, dif_pos hlt, hleft, hright]
    simp only [hnode]
    erw [evalWithAnswerFn_bind, ih (by omega) (2 * j) (by omega) (fun i hi => hS i (hchild 0 (by omega) i hi)),
      evalWithAnswerFn_bind, ih (by omega) (2 * j + 1) hj2 (fun i hi => hS i (hchild 1 (by omega) i hi))]
    erw [XmssSecurity.Concrete.CacheReplay.eval_tweakableHash]
    rfl


/-- `D_refBottom` with the top signature of the bottom tree in the clear. -/
theorem D_refBottom_topSignature (h : Query C → HashOutput) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree)
    (htopChain : ∀ b l, top.chainEnd (topKey b) l = E prims h (Concrete.chainWalk P topLayer (topKey b) l 0 3
        (D prims h (prfValue seeds (.chain topLayer (topKey b) l (digit 0))))))
    (htopRoot : top.root = E prims h (merkleNode P topLayer top.chainEnd layerHeight 0))
    (b : Fin (2 ^ layerHeight)) :
    D prims h (referenceTree tweakable (prfValue seeds) P top (.bottom b)) = none ∨
      ∃ tree, D prims h (referenceTree tweakable (prfValue seeds) P top (.bottom b)) = some (.bottom tree) ∧
        ∃ encoding, Codeword.decode (E prims h (Concrete.messageDigest P topLayer (topKey b)
            (bytesLE 16 tree.root) tree.topSignature.randomness)) = some encoding ∧
          tree.topSignature = ⟨tree.topSignature.randomness, fun l => digestAt
            (((signJobs b encoding).map fun job => D prims h (referenceJob tweakable (prfValue seeds) P job)).getD
              l.val []) 0, E prims h (merklePath P topLayer top.chainEnd (topKey b))⟩ := by
  unfold referenceTree ceremonyOutput
  simp only [D_bind, D_map, D_mapM]
  split
  next r1 e1 hG =>
    simp only [D_bind, D_map, D_mapM]
    rw [D_ite]
    have hT := topRoot_eq (prims := prims) (h := h) seeds P top htopChain htopRoot b _ r1 e1
      (E_grind_spec _ _ _ _ _ _ _ _ _ hG)
    unfold E at hT
    rw [hT, if_neg (not_not.mpr rfl), D_pure]
    refine Or.inr ⟨_, rfl, e1, ?_, ?_⟩
    · dsimp only
      have hd := E_grind_spec (prims := prims) (h := h) _ _ _ _ _ _ _ _ _ hG
      exact hd
    · dsimp only
  next hG =>
    exact Or.inl rfl


set_option maxRecDepth 100000 in
/-- The signature of `KeyGen` with `H` fixed, when the bottom tree and the codeword exist. -/
theorem D_honestSignature_some (h : Query C → HashOutput) (P : PublicParameter) (keys : C.Party → Keys C)
    (top : TopTree) (seeds : C.Term → HashOutput) (e : KeyIndex) (message : Message) (tree : BottomTree)
    (randomness : Randomness) (encoding : Encoding)
    (htree : D prims h (referenceTree tweakable (prfValue seeds) P top (.bottom (treeOf e))) = some (.bottom tree))
    (hsc : D prims h (signCodeword P (tree.commitment e) e message
      (D prims h (prfValue seeds (.randomizer bottomLayer e)))) = some (randomness, encoding))
    (hcpk : ∀ l, let value := fun p => D prims h (prfValue seeds (.chain bottomLayer e l p))
      tree.cpk e l =
        (E prims h (Concrete.chainWalk P bottomLayer e l 0 1 (value (digit 0))) ^^^ value (digit 1),
          E prims h (Concrete.chainWalk P bottomLayer e l 0 2 (value (digit 0))) ^^^ value (digit 2),
          E prims h (Concrete.chainWalk P bottomLayer e l 0 3 (value (digit 0))))) :
    D prims h (honestSignature (fun oa => oa) (dealtWith (fun oa => oa) P keys top (prfValue seeds)) e message) =
      some ⟨e, fun lay => if lay = bottomLayer then ⟨randomness, fun l => E prims h (Concrete.chainWalk P bottomLayer
        e l 0 (encoding l).val (D prims h (prfValue seeds (.chain bottomLayer e l (digit 0))))),
        E prims h (merklePath P bottomLayer (fun e l => (tree.cpk e l).2.2) e)⟩ else tree.topSignature⟩ := by
  simp only [honestSignature, dealtWith, D_bind, D_map, htree]
  rw [hsc]
  simp only [D_bind, D_sequenceFin, D_pure]
  congr 2
  funext lay
  split_ifs
  · congr 1
    funext l
    have hl := hcpk l
    generalize encoding l = d at *
    obtain ⟨v, hv⟩ := d
    have hv' : v < 4 := hv
    simp only at hl
    interval_cases v
    · exact (E_chainWalk_zero (prims := prims) (h := h) P bottomLayer e l 0 _).symm
    · show D prims h (do
          let f ← prfValue seeds (.chain bottomLayer e l ⟨1, hv⟩)
          pure ((if 1 = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ f)) = _
      rw [D_bind, D_pure, if_pos rfl, hl]
      rw [BitVec.xor_assoc, show (⟨1, hv⟩ : Digit) = digit 1 from rfl, BitVec.xor_self, BitVec.xor_zero]
      rfl
    · show D prims h (do
          let f ← prfValue seeds (.chain bottomLayer e l ⟨2, hv⟩)
          pure ((if 2 = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ f)) = _
      rw [D_bind, D_pure, if_neg (by decide), hl]
      rw [BitVec.xor_assoc, show (⟨2, hv⟩ : Digit) = digit 2 from rfl, BitVec.xor_self, BitVec.xor_zero]
      rfl
    · show D prims h (pure (tree.cpk e l).2.2) = _
      rw [D_pure, hl]
  · rfl


theorem E_eval (h : Query C → HashOutput) {α : Type} (oa : OracleComp HashSpec α) :
    E prims h oa = evalWithAnswerFn (fun x => h (.hash x) : QueryImpl HashSpec Id) oa :=
  D_tweakable prims h oa

theorem E_chainWalk_bottom (c : HashCache C) (P : PublicParameter) (e : KeyIndex) (l : ChainIndex) (start n : ℕ)
    (v : Digest) :
    E prims (answersOf c) (Concrete.chainWalk P bottomLayer e l start n v) =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.chainStep (thView c) P e l) start n v := by
  rw [E_eval]
  erw [XmssSecurity.Bridge.chainWalk_bottom]
  exact XmssSecurity.Concrete.CacheReplay.eval_chainWalk (thView c) _ _ _ _ _ _

theorem E_chainWalk_top (c : HashCache C) (P : PublicParameter) (b : XmssSecurity.TopIndex) (l : ChainIndex)
    (start n : ℕ) (v : Digest) :
    E prims (answersOf c) (Concrete.chainWalk P topLayer (XmssSecurity.Bridge.topKey b) l start n v) =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.topChainStep (thView c) P b l) start n v := by
  rw [E_eval]
  erw [XmssSecurity.Bridge.chainWalk_top]
  exact XmssSecurity.Concrete.CacheReplay.eval_topChainWalk (thView c) _ _ _ _ _ _

theorem xor_one_div_two (n : ℕ) : (n ^^^ 1) / 2 = n / 2 := by
  cases hb : n.testBit 0
  · rw [(even_parts n hb).2]
    omega
  · rw [(odd_parts n hb).2]
    omega

theorem xor_one_div_pow (n m : ℕ) : (n ^^^ 1) / 2 ^ (m + 1) = n / 2 ^ (m + 1) := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, xor_one_div_two]


theorem div_pow_of_xor (n i : ℕ) (hi : i < 16) : ((n / 2 ^ i) ^^^ 1) / 2 ^ (16 - i) = n / 2 ^ 16 := by
  rw [show 16 - i = (15 - i) + 1 by omega, xor_one_div_pow, Nat.div_div_eq_div_mul, ← pow_add,
    show i + (15 - i + 1) = 16 by omega]

theorem xor_lt_pow (n i k : ℕ) (hik : i < k) (hn : n / 2 ^ i < 2 ^ (k - i)) : (n / 2 ^ i) ^^^ 1 < 2 ^ (k - i) := by
  have h1 := xor_one_div_two (n / 2 ^ i)
  have h2 : 2 ^ (k - i) = 2 * 2 ^ (k - i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem E_merklePath_bottom (c : HashCache C) (P : PublicParameter) (chainEnd : KeyIndex → ChainIndex → Digest)
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest) (e : KeyIndex)
    (hS : ∀ i : XmssSecurity.LeafIndex, i.val / 2 ^ 16 = e.val / 2 ^ 16 → ∀ l, chainEnd i l =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.chainStep (thView c) P i l) 0
        (XmssSecurity.chainLength - 1) (secret i l)) :
    E prims (answersOf c) (merklePath P bottomLayer chainEnd e) = fun i =>
      XmssSecurity.Concrete.CacheReplay.treeNode (thView c) P secret i.val
        (XmssSecurity.Concrete.merkleNodeOfNat ((e.val / 2 ^ i.val) ^^^ 1)) := by
  unfold merklePath
  rw [E_sequenceFin]
  funext i
  have hi : i.val < 16 := i.isLt
  have he : e.val / 2 ^ i.val < 2 ^ (32 - i.val) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 32 - i.val + i.val = 32 by omega]
    exact e.isLt
  rw [E_eval]
  exact eval_merkleNode_bottom (thView c) P chainEnd secret i.val (by omega) _
    (xor_lt_pow e.val i.val 32 (by omega) he) fun i' hi' => hS i' (by
      rw [← div_pow_of_xor e.val i.val hi, show (e.val / 2 ^ i.val) ^^^ 1 = i'.val / 2 ^ i.val from hi'.symm,
        Nat.div_div_eq_div_mul, ← pow_add,
        show i.val + (16 - i.val) = 16 by omega])

theorem E_merklePath_top (c : HashCache C) (P : PublicParameter) (chainEnd : KeyIndex → ChainIndex → Digest)
    (S : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest) (b : XmssSecurity.TopIndex)
    (hS : ∀ b l, chainEnd (XmssSecurity.Bridge.topKey b) l =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.topChainStep (thView c) P b l) 0
        (XmssSecurity.chainLength - 1) (S b l)) :
    E prims (answersOf c) (merklePath P topLayer chainEnd (XmssSecurity.Bridge.topKey b)) = fun i =>
      XmssSecurity.Concrete.CacheReplay.topTreeNode (thView c) P S i.val
        (XmssSecurity.Concrete.topNodeOfNat ((b.val / 2 ^ i.val) ^^^ 1)) := by
  unfold merklePath
  rw [E_sequenceFin]
  funext i
  have hi : i.val < 16 := i.isLt
  have hb : b.val / 2 ^ i.val < 2 ^ (16 - i.val) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 16 - i.val + i.val = 16 by omega]
    exact b.isLt
  rw [E_eval]
  exact eval_merkleNode_top (thView c) P chainEnd S hS i.val (by omega) _ (xor_lt_pow b.val i.val 16 (by omega) hb)

/-! ## The final state -/

/-- Item 1 of `CacheConsistent`. When `KeyGen` with `H` fixed to the final cache gives the top tree
of the run, its root is the root that leanVM replays from the cache. -/
def TopRootReplay (prims : Primitives) (C : Committee) : Prop :=
  ∀ z : FinalState C,
    D prims z.answers (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 emptyTop .top) = some (.top z.top) →
    honestNode (topStep z.cache z.keys.1 z.key)
        (XmssSecurity.Concrete.CacheView.topLeafHash (thView z.cache) z.keys.1 (XmssSecurity.topKeyOf z.key))
        (XmssSecurity.Concrete.CacheView.topNodeHash (thView z.cache) z.keys.1 (XmssSecurity.topKeyOf z.key))
        (z.honestKey prims).topSecret (z.honestKey prims).topPath XmssSecurity.treeHeight = z.top.root

/-- Item 3 of `CacheConsistent`. When `KeyGen` with `H` fixed to the final cache gives the top tree
of the run, its signature at the bound message is the honest signature that leanVM replays. -/
def HonestSignatureReplay (prims : Primitives) (C : Committee) : Prop :=
  ∀ z : FinalState C,
    D prims z.answers (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 emptyTop .top) = some (.top z.top) →
    ∀ message, z.state.bound z.key = some message →
      honestSignature (m := Id) (fun oa => D prims z.answers oa) (z.dealt prims) z.key message =
        (honestSig z.cache z.keys.1 z.key (z.honestKey prims)).map (XmssSecurity.Bridge.toRealSig z.key)



theorem topRootReplay : TopRootReplay prims C := by
  intro z hdealt
  obtain ⟨top, href, hchain, hroot⟩ := D_refTop (prims := prims) (h := z.answers) z.keys.1 z.keys.2.1 emptyTop
  rw [href] at hdealt
  have htop : top = z.top := by
    have := Option.some.inj hdealt
    cases this
    rfl
  subst htop
  let K := thView z.cache
  let S : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest :=
    fun b => z.chainStarts prims topLayer (topKey b)
  have hS : ∀ b l, z.top.chainEnd (XmssSecurity.Bridge.topKey b) l =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.topChainStep K z.keys.1 b l) 0
        (XmssSecurity.chainLength - 1) (S b l) := by
    intro b l
    have h := hchain b l
    rw [E_eval] at h
    erw [XmssSecurity.Bridge.chainWalk_top] at h
    exact h.trans (XmssSecurity.Concrete.CacheReplay.eval_topChainWalk K _ _ _ 0 3 _)
  have hroot' : z.top.root = XmssSecurity.Concrete.CacheReplay.topTreeNode K z.keys.1 S 16
      (XmssSecurity.Concrete.topNodeOfNat 0) := by
    rw [hroot, E_eval]
    exact eval_merkleNode_top K z.keys.1 z.top.chainEnd S hS 16 le_rfl 0 (by norm_num)
  rw [hroot']
  have hasc := topPath_ascends_to_topTreeNode K z.keys.1 S (XmssSecurity.topKeyOf z.key) 16 le_rfl
  have hnode : topPathNodeAt (XmssSecurity.topKeyOf z.key) 16 = XmssSecurity.Concrete.topNodeOfNat 0 := by
    have hlt : (XmssSecurity.topKeyOf z.key).val < 2 ^ 16 := (XmssSecurity.topKeyOf z.key).isLt
    unfold topPathNodeAt
    rw [Nat.div_eq_of_lt hlt]
  rw [hnode] at hasc
  exact hasc


/-- The bottom tree of the output of a ceremony. -/
def bottomOf : Option TreeOutput → Option BottomTree
  | some (.bottom tree) => some tree
  | _ => none

set_option maxRecDepth 100000 in
theorem dealt_bottom (z : FinalState C) (b : Fin (2 ^ layerHeight)) (o : Option TreeOutput)
    (ho : D prims z.answers (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 z.top (.bottom b)) = o) :
    (z.dealt prims).bottom b = bottomOf o := by
  have h : referenceTree (m := Id) (fun oa => D prims z.answers (tweakable oa))
      (fun p => D prims z.answers (prfValue z.keys.2.1 p)) z.keys.1 z.top (.bottom b) =
      D prims z.answers (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 z.top (.bottom b)) :=
    (SeedHitProof.hom_referenceTree (fixedHom prims z.answers) (fun oa => tweakable oa)
      (prfValue z.keys.2.1) z.keys.1 z.top (.bottom b)).symm
  simp only [FinalState.dealt, dealtWith]
  erw [h, ho]
  rcases o with _ | (_ | _) <;> rfl

set_option maxRecDepth 100000 in
theorem honestSignatureReplay : HonestSignatureReplay prims C := by
  intro z hdealt message hbound
  obtain ⟨top, href, hchain, hroot⟩ := D_refTop (prims := prims) (h := z.answers) z.keys.1 z.keys.2.1 emptyTop
  rw [href] at hdealt
  have htop : top = z.top := by
    have := Option.some.inj hdealt
    cases this
    rfl
  subst htop
  rcases D_refBottom_topSignature prims z.answers z.keys.1 z.keys.2.1 z.top hchain hroot (treeOf z.key) with
    hnone | ⟨tree, htree, topCodeword, hdec, hsig⟩
  · have hbottom := dealt_bottom prims z (treeOf z.key) _ hnone
    have hsel : (z.honestKey prims).selected = none := by
      simp [FinalState.honestKey, FinalState.selected, FinalState.bottomTree, hbottom, bottomOf, hbound]
      rfl
    have hlhs : honestSignature (m := Id) (fun oa => D prims z.answers oa) (z.dealt prims) z.key message = none := by
      simp only [honestSignature, hbottom, bottomOf]
      rfl
    rw [hlhs]
    simp [honestSig, hsel]
  have hbottom : (z.dealt prims).bottom (treeOf z.key) = some tree := dealt_bottom prims z _ _ htree
  have hspec : BottomSpec prims z.answers z.keys.2.1 z.keys.1 z.top (treeOf z.key) tree := by
    rcases D_refBottom (prims := prims) (h := z.answers) z.keys.1 z.keys.2.1 z.top hchain hroot (treeOf z.key) with
      hn | ⟨tree', htree', hspec'⟩
    · rw [htree] at hn
      cases hn
    · rw [htree] at htree'
      cases htree'
      exact hspec'
  have hek := bottomKey_treeOf z.key
  have hcpk : ∀ l, let value := fun p => D prims z.answers (prfValue z.keys.2.1 (.chain bottomLayer z.key l p))
      tree.cpk z.key l =
        (E prims z.answers (Concrete.chainWalk z.keys.1 bottomLayer z.key l 0 1 (value (digit 0))) ^^^ value (digit 1),
          E prims z.answers (Concrete.chainWalk z.keys.1 bottomLayer z.key l 0 2 (value (digit 0))) ^^^ value (digit 2),
          E prims z.answers (Concrete.chainWalk z.keys.1 bottomLayer z.key l 0 3 (value (digit 0)))) := by
    intro l
    have h := hspec.cpk ⟨z.key.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ l
    rw [hek] at h
    exact h
  have hcomm : tree.commitment z.key = truncateHash (z.answers (.hash (commitmentInput z.keys.1 z.key
      (D prims z.answers (prfValue z.keys.2.1 (.randomizer bottomLayer z.key)))))) := by
    have h := hspec.commitment ⟨z.key.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
    rw [hek] at h
    exact h
  rcases hsc : D prims z.answers (signCodeword z.keys.1 (tree.commitment z.key) z.key message
      (D prims z.answers (prfValue z.keys.2.1 (.randomizer bottomLayer z.key)))) with _ | ⟨randomness, encoding⟩
  · have hsel : (z.honestKey prims).selected = none := by
      simp [FinalState.honestKey, FinalState.selected, FinalState.bottomTree, hbottom, hbound, hsc]
      rfl
    have hlhs : honestSignature (m := Id) (fun oa => D prims z.answers oa) (z.dealt prims) z.key message = none := by
      rw [FinalState.dealt, D_honestSignature]
      simp only [honestSignature, dealtWith, D_bind, D_map, htree]
      rw [hsc]
      rfl
    rw [hlhs]
    simp [honestSig, hsel]
  have hlhs := D_honestSignature_some prims z.answers z.keys.1 (dealtKeys z.keys.1 z.keys.2.1 z.keys.2.2) z.top
    z.keys.2.1 z.key message tree randomness encoding htree hsc hcpk
  rw [← D_honestSignature] at hlhs
  rw [show honestSignature (m := Id) (fun oa => D prims z.answers oa) (z.dealt prims) z.key message = _ from hlhs]
  have hsel : (z.honestKey prims).selected = some (message, randomness) := by
    simp [FinalState.honestKey, FinalState.selected, FinalState.bottomTree, hbottom, hbound, hsc]
  have htopRandomness : (z.honestKey prims).topRandomness = tree.topSignature.randomness := by
    simp [FinalState.honestKey, FinalState.bottomTree, hbottom]
  have hgrind := hsc
  rw [D_signCodeword (prims := prims) _ _ _ _ _ hcomm] at hgrind
  have hdecB := E_grind_spec (prims := prims) (h := z.answers) _ _ _ _ _ _ _ _ _ hgrind
  have hencB : XmssSecurity.TargetSum.decodeDigest (XmssSecurity.Concrete.CacheView.encodingHash (thView z.cache)
      z.keys.1 z.key (message, randomness)) = some encoding := by
    rw [E_eval] at hdecB
    erw [XmssSecurity.Bridge.messageDigest_bottom, XmssSecurity.Concrete.CacheReplay.eval_encodingHash,
      XmssSecurity.Bridge.decode_eq] at hdecB
    exact hdecB
  have hbottomEnds : ∀ i : XmssSecurity.LeafIndex, i.val / 2 ^ 16 = (treeOf z.key).val → ∀ l,
      (tree.cpk i l).2.2 = XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.chainStep (thView z.cache) z.keys.1 i l) 0 (XmssSecurity.chainLength - 1)
        (z.chainStarts prims bottomLayer i l) := by
    intro i hi l
    have hik : bottomKey (treeOf z.key) ⟨i.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ = i := by
      apply Fin.ext
      simp only [bottomKey, ← hi, layerHeight]
      exact Nat.div_add_mod _ _
    have h := hspec.cpk ⟨i.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ l
    rw [hik] at h
    rw [h]
    dsimp only
    rw [show z.answers = answersOf z.cache from rfl, E_chainWalk_bottom]
    rfl
  have hroot' : honestRoot z.cache z.keys.1 z.key (z.honestKey prims) = tree.root := by
    rw [hspec.root, E_eval]
    have hm := eval_merkleNode_bottom (thView z.cache) z.keys.1 (fun e l => (tree.cpk e l).2.2)
      (z.chainStarts prims bottomLayer) 16 le_rfl (treeOf z.key).val
      (lt_of_lt_of_le (treeOf z.key).isLt (by decide)) hbottomEnds
    refine Eq.trans ?_ hm.symm
    exact path_ascends_to_treeNode (thView z.cache) z.keys.1 (z.chainStarts prims bottomLayer) z.key 16 le_rfl
  have htopEnc : topEncoding z.cache z.keys.1 z.key (z.honestKey prims) = some topCodeword := by
    unfold topEncoding topSignedInput
    rw [hroot', htopRandomness]
    rw [E_eval] at hdec
    erw [XmssSecurity.Bridge.messageDigest_top (key := XmssSecurity.topKeyOf z.key),
      XmssSecurity.Bridge.decode_eq] at hdec
    rw [← hdec]
    exact congrArg _ (XmssSecurity.Concrete.CacheReplay.eval_tweakableHash (thView z.cache) _ _ _).symm
  have hse : selectedEncoding z.cache z.keys.1 z.key (z.honestKey prims) = some encoding := by
    simp only [selectedEncoding, hsel]
    exact hencB
  have hhonest : honestSig z.cache z.keys.1 z.key (z.honestKey prims) = some ⟨randomness,
      signedValues (bottomStep z.cache z.keys.1 z.key) (z.honestKey prims).secret encoding,
      fun i => (z.honestKey prims).path i, ⟨(z.honestKey prims).topRandomness,
        signedValues (topStep z.cache z.keys.1 z.key) (z.honestKey prims).topSecret topCodeword,
        fun i => (z.honestKey prims).topPath i⟩⟩ := by
    simp only [honestSig, hsel, hse, htopEnc]
    rfl
  have hv : (fun l => E prims z.answers (Concrete.chainWalk z.keys.1 bottomLayer z.key l 0 (encoding l).val
      (D prims z.answers (prfValue z.keys.2.1 (.chain bottomLayer z.key l (digit 0)))))) =
      signedValues (bottomStep z.cache z.keys.1 z.key) (z.honestKey prims).secret encoding := by
    funext l
    rw [show z.answers = answersOf z.cache from rfl, E_chainWalk_bottom]
    rfl
  have hp : E prims z.answers (merklePath z.keys.1 bottomLayer (fun e l => (tree.cpk e l).2.2) z.key) =
      fun i : Fin layerHeight => (z.honestKey prims).path i := by
    refine (E_merklePath_bottom prims z.cache z.keys.1 _
      (z.chainStarts prims bottomLayer) z.key (fun i hi l => hbottomEnds i hi l)).trans ?_
    funext i
    have hi : i.val < XmssSecurity.treeHeight := i.isLt
    simp only [FinalState.honestKey, hi, ↓reduceDIte]
    rfl
  have hS : ∀ b l, z.top.chainEnd (XmssSecurity.Bridge.topKey b) l =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.topChainStep (thView z.cache) z.keys.1 b l) 0
        (XmssSecurity.chainLength - 1) (z.chainStarts prims topLayer (topKey b) l) := by
    intro b l
    have h := hchain b l
    rw [E_eval] at h
    erw [XmssSecurity.Bridge.chainWalk_top] at h
    exact h.trans (XmssSecurity.Concrete.CacheReplay.eval_topChainWalk (thView z.cache) _ _ _ 0 3 _)
  have hvt : (fun l : ChainIndex => digestAt (((signJobs (treeOf z.key) topCodeword).map fun job =>
      D prims z.answers (referenceJob tweakable (prfValue z.keys.2.1) z.keys.1 job)).getD l.val []) 0) =
      signedValues (topStep z.cache z.keys.1 z.key) (z.honestKey prims).topSecret topCodeword := by
    funext l
    rw [signOutputs_value]
    exact E_chainWalk_top prims z.cache z.keys.1 (XmssSecurity.topKeyOf z.key) l 0 _ _
  have hpt : E prims z.answers (merklePath z.keys.1 topLayer z.top.chainEnd (topKey (treeOf z.key))) =
      fun i : Fin layerHeight => (z.honestKey prims).topPath i := by
    refine (E_merklePath_top prims z.cache z.keys.1 z.top.chainEnd (fun b => z.chainStarts prims topLayer (topKey b))
      (XmssSecurity.topKeyOf z.key) hS).trans ?_
    funext i
    have hi : i.val < XmssSecurity.treeHeight := i.isLt
    simp only [FinalState.honestKey, hi, ↓reduceDIte]
    rfl
  rw [hhonest, Option.map_some, hv, hp, hsig, hvt, hpt, htopRandomness]
  rfl

set_option maxRecDepth 100000 in
theorem runHasFinalState (prims : Primitives) (C : Committee) : RunHasFinalState prims C := by
  intro A x r hr hwin
  obtain ⟨top, state, forgery, hsome, hdealt, hres, hfresh⟩ := exposedRun_facts prims A x r hr hwin
  refine ⟨top, state, forgery, hsome, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact (D_verify prims _ _ _ _).trans
        ((XmssSecurity.Concrete.CacheReplay.eval_verify _ _ _ _ _).symm.trans (resolves_value hres))
    · rw [← D_honestSignature prims (answersOf r.2.1) x.1 (dealtKeys x.1 x.2.1 x.2.2) top x.2.1] at hfresh
      exact hfresh
  · refine ⟨?_, ?_, ?_⟩
    · exact topRootReplay prims ⟨x, top, state, forgery, r.2.1, false⟩ hdealt
    · exact verifyCached_of_resolves r.2.1 (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩)
        forgery.signature.leafIndex forgery.message (XmssSecurity.Bridge.toModelSig forgery.signature) true hres
    · exact honestSignatureReplay prims ⟨x, top, state, forgery, r.2.1, false⟩ hdealt


set_option maxRecDepth 100000 in
/-- `signing_run_badEvent` with `RunHasFinalState` discharged. -/
theorem signing_run_badEvent_closed (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × HashCache C × ℕ)
    (hr : r ∈ support (exposedRun prims A x)) (hwin : r.1.1 = (true, false)) :
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      let z : FinalState C := ⟨x, top, state, forgery, r.2.1, false⟩
      Hit z.cache z.keys.1 z.key (z.honestKey prims) ∨
        Guess z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
          (XmssSecurity.Bridge.toModelSig z.forgery.signature) ∨
        Partner z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
          (XmssSecurity.Bridge.toModelSig z.forgery.signature) :=
  signing_run_badEvent prims (runHasFinalState prims C) A x r hr hwin

end SigningCacheProof

/-- info: 'ThresholdLeanXmssSecurity.SigningCacheProof.runHasFinalState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCacheProof.runHasFinalState

/-- info: 'ThresholdLeanXmssSecurity.SigningCacheProof.signing_run_badEvent_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCacheProof.signing_run_badEvent_closed

end ThresholdLeanXmssSecurity
