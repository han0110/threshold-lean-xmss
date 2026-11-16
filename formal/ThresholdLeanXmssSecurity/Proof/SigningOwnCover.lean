import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SeedHit
import XmssSecurity.Proof.Bridge.Resolution

/-!
# The forest completion covers the honest ceremonies

Each structural input that the top tree or a bottom tree reads after the forest completion
is an input that the completion reads. So a block of such reads does not raise the completion
potential.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SigningOwnCover

open SigningHitProof

variable {C : Committee}

/-- A fixed value of the primitives. The replay of a chain start reads only the cache, so each
value gives the same replay. -/
def anyPrims : Primitives := ⟨fun _ => 0, ⟨pure 0, fun _ _ => 0⟩⟩

/-- A completion records only inputs of a cache in which it resolves, when that cache is below the
final cache of its run. -/
theorem recordReads_le_of_resolves {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) :
    ∀ (record cache bound : HashCache C) (v : α), record ≤ bound →
    DeterministicSigning.Resolves bound oa v →
    ∀ w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads oa record)).run cache), bound ≤ w.2 → w.1.2 ≤ bound := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro record cache bound v hle _ w hw _
      change w ∈ ({((a, record), cache)} : Set _) at hw
      rcases hw with rfl
      exact hle
  | query_bind input k ih =>
      intro record cache bound v hle hres w hw hbw
      change w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input) >>=
          fun answer => recordReads (k answer) (record.cacheQuery input answer))).run cache) at hw
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hw
      obtain ⟨r, hr, hw⟩ := hw
      obtain ⟨a, ha, htail⟩ := hres.query_inv
      have hro := randomOracle_support input cache r hr
      have hgrow := DeterministicSigning.cache_le_of_run _ r.2 w hw
      have hsame : a = r.1 := Option.some.inj ((hbw ha).symm.trans (hgrow hro.2.1))
      subst a
      refine ih r.1 (record.cacheQuery input r.1) r.2 bound v ?_ htail w hw hbw
      intro other value hv
      by_cases he : other = input
      · subst other
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv
        rw [← hv]
        exact ha
      · rw [QueryCache.cacheQuery_of_ne _ _ he] at hv
        exact hle hv

/-- A run that resolves in one cache resolves with the same value in a larger cache in which
another run of the same computation resolves, when all caches agree. -/
theorem resolves_transfer {D R : Type} [DecidableEq D] {α : Type} {oa : OracleComp (D →ₒ R) α}
    {source target other bound : QueryCache (D →ₒ R)} {u v : α}
    (hsource : DeterministicSigning.Resolves source oa u)
    (hother : DeterministicSigning.Resolves other oa v)
    (hst : source ≤ target) (hsb : source ≤ bound) (hob : other ≤ bound) :
    DeterministicSigning.Resolves target oa v := by
  have he := (hsource.mono hsb).unique (hother.mono hob)
  subst he
  exact hsource.mono hst

/-- The converse of `resolves_forestHash`. -/
theorem forestHash_resolves {α : Type} (record : HashCache C) (oa : OracleComp HashSpec α) (v : α)
    (h : DeterministicSigning.Resolves (SigningDescentProof.thView record) oa v) :
    DeterministicSigning.Resolves record (forestHash oa) v := by
  induction h with
  | pure value =>
      simp only [forestHash, simulateQ_pure]
      exact .pure value
  | query input answer hanswer next value _ ih =>
      simp only [forestHash, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map] at ih ⊢
      exact .query (Query.hash input) answer hanswer _ value ih

/-- Each run of a list resolves in a cache when each job does. -/
theorem resolves_mapM_lift {α β : Type} {source target : HashCache C}
    (f : α → OracleComp (Query C →ₒ HashOutput) β) (xs : List α)
    (hf : ∀ a ∈ xs, ∀ b, DeterministicSigning.Resolves source (f a) b →
      DeterministicSigning.Resolves target (f a) b) :
    ∀ ys, DeterministicSigning.Resolves source (xs.mapM f) ys →
      DeterministicSigning.Resolves target (xs.mapM f) ys := by
  induction xs with
  | nil =>
      intro ys h
      simp only [List.mapM_nil] at h ⊢
      rw [← h.pure_inv]
      exact .pure _
  | cons a xs ih =>
      intro ys h
      simp only [List.mapM_cons] at h ⊢
      obtain ⟨b, hb, h⟩ := h.of_bind
      obtain ⟨bs, hbs, h⟩ := h.of_bind
      rw [← h.pure_inv]
      exact (hf a (by simp) b hb).bind
        ((ih (fun a ha => hf a (by simp [ha])) bs hbs).bind (.pure _))

/-- The first value of a resolved run of a list is the value of its first job. -/
theorem resolves_mapM_head {α β : Type} {cache : HashCache C}
    {f : α → OracleComp (Query C →ₒ HashOutput) β} {a : α} {as : List α} {ys : List β} {d : β}
    (h : DeterministicSigning.Resolves cache ((a :: as).mapM f) ys) :
    ∃ y, DeterministicSigning.Resolves cache (f a) y ∧ ys.getD 0 d = y := by
  simp only [List.mapM_cons] at h
  obtain ⟨y, hy, h⟩ := h.of_bind
  obtain ⟨ys', _, h⟩ := h.of_bind
  rw [← h.pure_inv]
  exact ⟨y, hy, rfl⟩

theorem topNodeOfNat_val_of_lt (j : ℕ) (hj : j < 2 ^ 16) : (XmssSecurity.Concrete.topNodeOfNat j).val = j := by
  have hjlt : j < 65536 := by simpa using hj
  simp [XmssSecurity.Concrete.topNodeOfNat, XmssSecurity.topLifetime, XmssSecurity.treeHeight,
    Nat.mod_eq_of_lt hjlt]

/-- The sibling index of an authentication path is a node of its level. -/
theorem topPath_index_lt (b : Fin (2 ^ layerHeight)) (level : ℕ) (hl : level < 16) :
    Nat.xor ((topKey b).val / 2 ^ level) 1 < 2 ^ (16 - level) := by
  have hb : (topKey b).val < 2 ^ 16 := by
    simpa [topKey, layerHeight] using b.isLt
  have hd : (topKey b).val / 2 ^ level < 2 ^ (16 - level) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 16 - level + level = 16 by omega]
    exact hb
  have h1 : 1 < 2 ^ (16 - level) := Nat.one_lt_two_pow (by omega)
  exact Nat.xor_lt_two_pow hd h1

open Classical in
theorem topEncodingHash_irrelevant (P P' : PublicParameter) (key : XmssSecurity.TopIndex) (root : Digest)
    (randomness : Randomizer) :
    (XmssSecurity.Concrete.topEncodingHash P' key root randomness :
      OracleComp XmssSecurity.HashSpec _).IsQueryBoundP
      (fun input => forestRelevant (C := C) P (.hash input)) 0 := by
  unfold XmssSecurity.Concrete.topEncodingHash XmssSecurity.Concrete.tweakableHash
    XmssSecurity.Concrete.oracleHash
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => by simp)
  exact (isQueryBoundP_query_iff _ _ _).2 (fun hf =>
    (SigningGuessProof.forestRelevant_not_digest P _ hf (Or.inr ⟨P', key, (root, _), rfl⟩)).elim)

theorem xor_one_even (n : ℕ) : Nat.xor (2 * n) 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i <;> simp [Nat.testBit_succ, Nat.testBit_zero]

theorem xor_one_odd (n : ℕ) : Nat.xor (2 * n + 1) 1 = 2 * n := by
  change (2 * n + 1) ^^^ 1 = 2 * n
  rw [← xor_one_even n]
  change (2 * n) ^^^ 1 ^^^ 1 = 2 * n
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- A fold of a top key along the authentication path of the forest resolves where the nodes of the
forest resolve, with the value of the node of its level. -/
theorem resolves_topAuthenticationRoot (S : QueryCache XmssSecurity.HashSpec) (P : PublicParameter)
    (secret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest) (key : XmssSecurity.TopIndex)
    (path : Fin XmssSecurity.treeHeight → Digest) (leaf : Digest)
    (hleaf : ∀ u, DeterministicSigning.Resolves S
      (XmssSecurity.Concrete.topTreeNode P secret 0 key : OracleComp XmssSecurity.HashSpec _) u → u = leaf)
    (hpath : ∀ i : Fin XmssSecurity.treeHeight, ∀ u, DeterministicSigning.Resolves S
      (XmssSecurity.Concrete.topTreeNode P secret i.val
        (XmssSecurity.Concrete.topNodeOfNat (Nat.xor (key.val / 2 ^ i.val) 1)) :
          OracleComp XmssSecurity.HashSpec _) u → path i = u) :
    ∀ levels ≤ 16, ∀ u, DeterministicSigning.Resolves S
      (XmssSecurity.Concrete.topTreeNode P secret levels
        (XmssSecurity.Concrete.topNodeOfNat (key.val / 2 ^ levels)) : OracleComp XmssSecurity.HashSpec _) u →
      DeterministicSigning.Resolves S
        (XmssSecurity.Concrete.topAuthenticationRoot P key path levels leaf :
          OracleComp XmssSecurity.HashSpec _) u := by
  have hkey : key.val < 2 ^ 16 := by
    simpa [XmssSecurity.topLifetime, XmssSecurity.treeHeight] using key.isLt
  intro levels
  induction levels with
  | zero =>
    intro _ u hu
    have hk : XmssSecurity.Concrete.topNodeOfNat (key.val / 2 ^ 0) = key := by
      apply Fin.ext
      rw [pow_zero, Nat.div_one, topNodeOfNat_val_of_lt _ hkey]
    rw [hk] at hu
    rw [hleaf u hu]
    exact .pure _
  | succ levels ih =>
    intro hlevels u hu
    have hlt : levels < XmssSecurity.treeHeight := by simp only [XmssSecurity.treeHeight]; omega
    set n := key.val / 2 ^ (levels + 1) with hn
    have hnlt : n < 2 ^ 16 := lt_of_le_of_lt (Nat.div_le_self _ _) hkey
    have h2n : 2 * n + 1 < 2 ^ 16 := by
      have : key.val / 2 ^ levels < 2 ^ 16 := lt_of_le_of_lt (Nat.div_le_self _ _) hkey
      have hd : key.val / 2 ^ levels = 2 * n + key.val / 2 ^ levels % 2 := by
        rw [hn, pow_succ, ← Nat.div_div_eq_div_mul]
        omega
      have hd2 : key.val / 2 ^ levels / 2 < 2 ^ 15 := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
        calc key.val < 2 ^ 16 := hkey
          _ ≤ 2 ^ (15 + (levels + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hval : (XmssSecurity.Concrete.topNodeOfNat n).val = n := topNodeOfNat_val_of_lt n hnlt
    have hleft : XmssSecurity.Concrete.topChildNode (XmssSecurity.Concrete.topNodeOfNat n) false =
        XmssSecurity.Concrete.topNodeOfNat (2 * n) := by
      apply Fin.ext
      simp only [XmssSecurity.Concrete.topChildNode, hval]
      rfl
    have hright : XmssSecurity.Concrete.topChildNode (XmssSecurity.Concrete.topNodeOfNat n) true =
        XmssSecurity.Concrete.topNodeOfNat (2 * n + 1) := by
      apply Fin.ext
      simp only [XmssSecurity.Concrete.topChildNode, hval]
      rfl
    have hindex : XmssSecurity.Concrete.topNodeIndex key levels = XmssSecurity.Concrete.topNodeOfNat n := by
      apply Fin.ext
      rw [hval]
      rfl
    have hd : key.val / 2 ^ levels = 2 * n + key.val / 2 ^ levels % 2 := by
      rw [hn, pow_succ, ← Nat.div_div_eq_div_mul]
      omega
    erw [XmssSecurity.Concrete.topTreeNode.eq_def] at hu
    simp only at hu
    rw [hleft, hright] at hu
    obtain ⟨left, hl, hu⟩ := hu.of_bind
    obtain ⟨right, hr, hu⟩ := hu.of_bind
    rw [dif_pos hlt] at hu
    erw [XmssSecurity.Concrete.topAuthenticationRoot.eq_def]
    simp only
    by_cases hbit : key.val.testBit levels = true
    · have hodd : key.val / 2 ^ levels = 2 * n + 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
        simp only [decide_eq_true_eq] at hbit
        omega
      have hcur := ih (by omega) right (by rw [hodd]; exact hr)
      have hsib := hpath ⟨levels, hlt⟩ left (by
        change DeterministicSigning.Resolves S (XmssSecurity.Concrete.topTreeNode P secret levels
          (XmssSecurity.Concrete.topNodeOfNat (Nat.xor (key.val / 2 ^ levels) 1))) left
        rw [hodd, xor_one_odd]
        exact hl)
      refine hcur.bind ?_
      simp only [hlt, ↓reduceDIte, hbit, if_true, hsib, hindex]
      exact hu
    · have heven : key.val / 2 ^ levels = 2 * n := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
        simp only [decide_eq_true_eq] at hbit
        omega
      have hcur := ih (by omega) left (by rw [heven]; exact hl)
      have hsib := hpath ⟨levels, hlt⟩ right (by
        change DeterministicSigning.Resolves S (XmssSecurity.Concrete.topTreeNode P secret levels
          (XmssSecurity.Concrete.topNodeOfNat (Nat.xor (key.val / 2 ^ levels) 1))) right
        rw [heven, xor_one_even]
        exact hr)
      refine hcur.bind ?_
      simp only [hlt, ↓reduceDIte, hbit, Bool.false_eq_true, if_false, hsib, hindex]
      exact hu

/-- A successful top search reads the digest of its selected trial, and that digest decodes to the
selected codeword. -/
theorem resolves_topSignFrom_some (S : QueryCache XmssSecurity.HashSpec) (P : PublicParameter)
    (key : XmssSecurity.TopIndex) (root : Digest) (base : Randomizer) :
    ∀ attempts trial randomness encoding, DeterministicSigning.Resolves S
      (XmssSecurity.Concrete.topSignFrom P key root base attempts trial : OracleComp XmssSecurity.HashSpec _)
      (some (randomness, encoding)) →
    ∃ digest, DeterministicSigning.Resolves S
      (XmssSecurity.Concrete.topEncodingHash P key root randomness : OracleComp XmssSecurity.HashSpec _)
      digest ∧ XmssSecurity.TargetSum.decodeDigest digest = some encoding := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial randomness encoding h
    cases h.pure_inv
  | succ attempts ih =>
    intro trial randomness encoding h
    erw [XmssSecurity.Concrete.topSignFrom.eq_def] at h
    simp only at h
    obtain ⟨digest, hdigest, h⟩ := h.of_bind
    cases hdec : XmssSecurity.TargetSum.decodeDigest digest with
    | none =>
      rw [hdec] at h
      exact ih _ _ _ h
    | some found =>
      rw [hdec] at h
      have he := h.pure_inv
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨digest, hdigest, hdec⟩

/-- Each value of a resolved run of a list is the value of its job. -/
theorem resolves_mapM_getD {α β : Type} {cache : HashCache C}
    {f : α → OracleComp (Query C →ₒ HashOutput) β} (d : β) :
    ∀ (xs : List α) (ys : List β), DeterministicSigning.Resolves cache (xs.mapM f) ys →
      ∀ i (hi : i < xs.length), DeterministicSigning.Resolves cache (f xs[i]) (ys.getD i d) := by
  intro xs
  induction xs with
  | nil => intro ys _ i hi; simp at hi
  | cons a as ih =>
    intro ys h i hi
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := h.of_bind
    obtain ⟨ys', hys', h⟩ := h.of_bind
    rw [← h.pure_inv]
    cases i with
    | zero => exact hy
    | succ i => exact ih ys' hys' i (by simpa using hi)

/-- A top Merkle node with the chain ends of a top tree resolves where the node of that tree
resolves, with the same value. -/
theorem resolves_merkleNode_top (S : QueryCache XmssSecurity.HashSpec) (P : PublicParameter)
    (secret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (chainEnd : KeyIndex → ChainIndex → Digest)
    (hends : ∀ b ends, DeterministicSigning.Resolves S
      (XmssSecurity.Concrete.topOneTimePublicKey P secret b : OracleComp XmssSecurity.HashSpec _) ends →
      chainEnd (XmssSecurity.Bridge.topKey b) = ends) :
    ∀ level ≤ 16, ∀ j < 2 ^ (16 - level), ∀ u, DeterministicSigning.Resolves S
      (XmssSecurity.Concrete.topTreeNode P secret level (XmssSecurity.Concrete.topNodeOfNat j) :
        OracleComp XmssSecurity.HashSpec _) u →
      DeterministicSigning.Resolves S (merkleNode P topLayer chainEnd level j) u := by
  intro level
  induction level with
  | zero =>
    intro _ j hj u hu
    erw [XmssSecurity.Concrete.topTreeNode.eq_def] at hu
    simp only at hu
    erw [XmssSecurity.Concrete.topLeafAt.eq_def] at hu
    obtain ⟨ends, hends', hleaf⟩ := hu.of_bind
    rw [merkleNode, SigningCacheProof.leafKey_top j (by simpa using hj)]
    erw [XmssSecurity.Bridge.leafHash_top, hends _ _ hends']
    exact hleaf
  | succ level ih =>
    intro hlevel j hj u hu
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
        (Verification.tweakableHashWithHash P (.node topLayer (level + 1) j) (OverPermutation.nodePayload left right) :
          OracleComp HashSpec Digest) =
        (XmssSecurity.Concrete.topNodeHash P ⟨level, hlt⟩ (XmssSecurity.Concrete.topNodeOfNat j) left right :
          OracleComp XmssSecurity.HashSpec _) := by
      intro left right
      have h := XmssSecurity.Bridge.nodeHash_top P ⟨level, hlt⟩ (XmssSecurity.Concrete.topNodeOfNat j) left right
      rw [hval] at h
      exact h
    erw [XmssSecurity.Concrete.topTreeNode.eq_def] at hu
    simp only at hu
    rw [hleft, hright] at hu
    obtain ⟨left, hl, hu⟩ := hu.of_bind
    obtain ⟨right, hr, hu⟩ := hu.of_bind
    rw [dif_pos hlt] at hu
    rw [merkleNode]
    simp only [hnode]
    exact (ih (by omega) (2 * j) (by omega) left hl).bind
      ((ih (by omega) (2 * j + 1) hj2 right hr).bind hu)

/-- A bottom Merkle node with the chain ends of the forest resolves where the node of the forest
resolves, with the same value. -/
theorem resolves_merkleNode_bottom (S : QueryCache XmssSecurity.HashSpec) (P : PublicParameter)
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (chainEnd : KeyIndex → ChainIndex → Digest) :
    ∀ level ≤ 16, ∀ j < 2 ^ (32 - level),
      (∀ i : XmssSecurity.LeafIndex, i.val / 2 ^ level = j → ∀ ends, DeterministicSigning.Resolves S
        (XmssSecurity.Concrete.oneTimePublicKey P secret i : OracleComp XmssSecurity.HashSpec _) ends →
        chainEnd i = ends) →
      ∀ u, DeterministicSigning.Resolves S
        (XmssSecurity.Concrete.treeNode P secret level (XmssSecurity.Concrete.merkleNodeOfNat j) :
          OracleComp XmssSecurity.HashSpec _) u →
      DeterministicSigning.Resolves S (merkleNode P bottomLayer chainEnd level j) u := by
  intro level
  induction level with
  | zero =>
    intro _ j hj hS u hu
    have hjlt : j < 4294967296 := by simpa using hj
    have hval : (XmssSecurity.Concrete.merkleNodeOfNat j).val = j := by
      simp [XmssSecurity.Concrete.merkleNodeOfNat, XmssSecurity.lifetime, XmssSecurity.treeHeight,
        Nat.mod_eq_of_lt hjlt]
    erw [XmssSecurity.Concrete.treeNode_zero_eq, XmssSecurity.Concrete.leafAt] at hu
    obtain ⟨ends, hends', hleaf⟩ := hu.of_bind
    rw [merkleNode, SigningCacheProof.leafKey_bottom j]
    erw [XmssSecurity.Bridge.leafHash_bottom, hS _ (by simpa using hval) _ hends']
    exact hleaf
  | succ level ih =>
    intro hlevel j hj hS u hu
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
        (Verification.tweakableHashWithHash P (.node bottomLayer (level + 1) j) (OverPermutation.nodePayload left right) :
          OracleComp HashSpec Digest) =
        (XmssSecurity.Concrete.nodeHash P ⟨level, hlt⟩ (XmssSecurity.Concrete.merkleNodeOfNat j) left right :
          OracleComp XmssSecurity.HashSpec _) := by
      intro left right
      have h := XmssSecurity.Bridge.nodeHash_bottom P ⟨level, hlt⟩ (XmssSecurity.Concrete.merkleNodeOfNat j) left right
      rw [hval] at h
      exact h
    have hchild : ∀ c < 2, ∀ i : XmssSecurity.LeafIndex, i.val / 2 ^ level = 2 * j + c →
        i.val / 2 ^ (level + 1) = j := by
      intro c hc i hi
      rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]
      omega
    erw [XmssSecurity.Concrete.treeNode_succ_eq] at hu
    rw [hleft, hright] at hu
    obtain ⟨left, hl, hu⟩ := hu.of_bind
    obtain ⟨right, hr, hu⟩ := hu.of_bind
    rw [dif_pos hlt] at hu
    rw [merkleNode]
    simp only [hnode]
    exact (ih (by omega) (2 * j) (by omega) (fun i hi => hS i (hchild 0 (by omega) i hi)) left hl).bind
      ((ih (by omega) (2 * j + 1) hj2 (fun i hi => hS i (hchild 1 (by omega) i hi)) right hr).bind hu)

/-- The chain ends of the resolved top tree are the ends of the top chains of the forest. -/
theorem topCeremony_ends (x : SigningSecurityProof.Keys3 C) (resolved record bound : HashCache C)
    (top : TopTree)
    (htop : DeterministicSigning.Resolves resolved
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (hresolved : resolved ≤ bound) (hrecord : record ≤ bound)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (htopSecret : ∀ b l, DeterministicSigning.Resolves record
      (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) (topSecret b l)) :
    ∀ b ends, DeterministicSigning.Resolves (SigningDescentProof.thView record)
      (XmssSecurity.Concrete.topOneTimePublicKey x.1 topSecret b : OracleComp XmssSecurity.HashSpec _) ends →
      top.chainEnd (XmssSecurity.Bridge.topKey b) = ends := by
  intro b ends hends
  funext l
  unfold XmssSecurity.Concrete.topOneTimePublicKey at hends
  have hE := hends.of_sequenceFin l
  have hm := resolves_referenceTop_modelChains anyPrims x resolved _ htop b l
  have hs : replayStarts anyPrims x resolved topLayer (topKey b) l = topSecret b l :=
    (resolves_referenceTop_starts anyPrims x resolved bound hresolved _ htop b l).symm.trans
      (resolves_forestValue anyPrims record bound hrecord _ _ _ (htopSecret b l))
  rw [hs] at hm
  exact (hm.mono (SigningCacheProof.thView_mono hresolved)).unique
    (hE.mono (SigningCacheProof.thView_mono hrecord))

open Classical in
/-- The cache `bound` on the inputs that are not relevant to the forest or that `record` holds. -/
def coverCache (P : PublicParameter) (record bound : HashCache C) : HashCache C :=
  QueryCache.ofFn fun input => if forestRelevant P input → (record input).isSome then bound input else none

theorem coverCache_le (P : PublicParameter) (record bound : HashCache C) :
    coverCache P record bound ≤ bound := by
  intro input value h
  simp only [coverCache, QueryCache.ofFn_apply] at h
  split_ifs at h
  · exact h

theorem record_le_coverCache (P : PublicParameter) {record bound : HashCache C} (hle : record ≤ bound) :
    record ≤ coverCache P record bound := by
  intro input value h
  simp only [coverCache, QueryCache.ofFn_apply]
  rw [if_pos (fun _ => by simp [h])]
  exact hle h

theorem coverCache_irrelevant {P : PublicParameter} {record bound : HashCache C} {input : Query C}
    {value : HashOutput} (hrel : ¬forestRelevant P input) (h : bound input = some value) :
    coverCache P record bound input = some value := by
  simp only [coverCache, QueryCache.ofFn_apply]
  rw [if_pos (fun h' => absurd h' hrel)]
  exact h

theorem isSome_of_coverCache {P : PublicParameter} {record bound : HashCache C} {input : Query C}
    (h : (coverCache P record bound input).isSome) (hrel : forestRelevant P input) :
    (record input).isSome := by
  simp only [coverCache, QueryCache.ofFn_apply] at h
  split_ifs at h with hc
  · exact hc hrel
  · simp at h

/-- A resolution moves to another cache through a bind, when each part moves. -/
theorem resolves_lift_bind {D R : Type} [DecidableEq D] {α β : Type} {source target : QueryCache (D →ₒ R)}
    {oa : OracleComp (D →ₒ R) α} {f : α → OracleComp (D →ₒ R) β}
    (hoa : ∀ a, DeterministicSigning.Resolves source oa a → DeterministicSigning.Resolves target oa a)
    (hf : ∀ a, DeterministicSigning.Resolves source oa a → ∀ v,
      DeterministicSigning.Resolves source (f a) v → DeterministicSigning.Resolves target (f a) v) :
    ∀ v, DeterministicSigning.Resolves source (oa >>= f) v →
      DeterministicSigning.Resolves target (oa >>= f) v := by
  intro v h
  obtain ⟨a, ha, hfa⟩ := h.of_bind
  exact (hoa a ha).bind (hf a ha v hfa)

/-- A computation that makes no query in `p` resolves in each cache that agrees outside `p`. -/
theorem resolves_lift_bound {D R : Type} [DecidableEq D] {α : Type} (p : D → Prop) [DecidablePred p]
    {source target : QueryCache (D →ₒ R)} (oa : OracleComp (D →ₒ R) α) (hb : oa.IsQueryBoundP p 0)
    (htarget : ∀ input value, ¬p input → source input = some value → target input = some value)
    (v : α) (h : DeterministicSigning.Resolves source oa v) :
    DeterministicSigning.Resolves target oa v := by
  induction h with
  | pure value => exact .pure value
  | query input answer hanswer next value _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    have hp : ¬p input := by simpa using hb.1
    exact .query input answer (htarget _ _ hp hanswer) next value (ih (by simpa [hp] using hb.2 answer))

open Classical in
theorem forestValue_irrelevant (P : PublicParameter) (seeds : C.Term → HashOutput) (p : Point) :
    (forestValue seeds p).IsQueryBoundP (forestRelevant P) 0 := by
  unfold forestValue
  apply isQueryBoundP_bind (m := 0)
  · apply mapM_bound_zero
    intro T
    simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff, forestRelevant_prf]
  · intro _ _
    simp

open Classical in
theorem forestHash_irrelevant {α : Type} (P : PublicParameter) (oa : OracleComp HashSpec α)
    (h : oa.IsQueryBoundP (fun input => forestRelevant (C := C) P (.hash input)) 0) :
    (forestHash (C := C) oa).IsQueryBoundP (forestRelevant P) 0 := by
  let : OracleSpec.UniformAnswerMeasure (Query C →ₒ HashOutput) :=
    OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _
  apply h.simulateQ_of_step
  · intro input _
    simp only [isQueryBoundP_query_iff]
    omega
  · intro input hn
    simp only [isQueryBoundP_query_iff]
    exact fun hp => (hn hp).elim

theorem randomizer_not_forestRelevant (P P' : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest)
    (message : HashInput) : ¬forestRelevant (C := C) P (.hash (randomizerInput P' lay e ρ message)) := by
  rintro ⟨domain, payload, _, _, he, _⟩
  have h := Query.hash.inj he
  have heq :
      XmssSecurity.bytesLE 16 P' ++ XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 0 (layerHi lay 0) e.val) ++
        (HashSig.littleEndianBytes 16 ρ ++ message) =
      XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes (XmssSecurity.hashDomainFields domain) ++
        (payload ++ XmssSecurity.domainSuffix domain) := by
    rw [← XmssSecurity.Bridge.tweakableHashInput_eq P domain payload, ← h]
    simp only [randomizerInput, List.append_assoc]
    rfl
  have ht := congrArg (fun fields => fields.tag.toNat) (XmssSecurity.Bridge.prefix_inj heq).2.1
  cases domain <;> norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] at ht

open Classical in
theorem topSignFrom_irrelevant (P P' : PublicParameter) (key : XmssSecurity.TopIndex) (root : Digest)
    (base : Randomizer) : ∀ attempts trial,
    (XmssSecurity.Concrete.topSignFrom P' key root base attempts trial :
      OracleComp XmssSecurity.HashSpec _).IsQueryBoundP
      (fun input => forestRelevant (C := C) P (.hash input)) 0 := by
  intro attempts
  induction attempts with
  | zero => intro trial; simp [XmssSecurity.Concrete.topSignFrom]
  | succ attempts ih =>
    intro trial
    erw [XmssSecurity.Concrete.topSignFrom.eq_def]
    simp only
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun digest _ => ?_)
    · unfold XmssSecurity.Concrete.topEncodingHash XmssSecurity.Concrete.tweakableHash
        XmssSecurity.Concrete.oracleHash
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => by simp)
      exact (isQueryBoundP_query_iff _ _ _).2 (fun hf =>
        (SigningGuessProof.forestRelevant_not_digest P _ hf (Or.inr ⟨P', key, (root, _), rfl⟩)).elim)
    · split
      · simp
      · exact ih _

attribute [local irreducible] XmssSecurity.Concrete.topTreeNode merkleNode

/-- The forest completion resolves the chain starts and the model forest in its record. -/
theorem forestRun_model (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache)) :
    ∃ (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
      (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
      (result : Digest × (XmssSecurity.TopIndex → Option (Randomizer × Encoding))),
      (∀ e l, DeterministicSigning.Resolves z.1.2
        (forestValue x.2.1 (.chain bottomLayer e l (digit 0))) (secret e l)) ∧
      (∀ b l, DeterministicSigning.Resolves z.1.2
        (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) (topSecret b l)) ∧
      (result, SigningDescentProof.thView z.1.2) ∈ support
        ((simulateQ XmssSecurity.HashSpec.randomOracle
          (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
            OracleComp XmssSecurity.HashSpec _)).run (SigningDescentProof.thView z.1.2)) := by
  obtain ⟨secret, topSecret, result, hsecret, htopSecret, hmodel⟩ := forestRun_resolves x cache z hz
  refine ⟨secret, topSecret, result, hsecret, htopSecret, ?_⟩
  rw [hmodel.run_eq_pure]
  simp only [support_pure]
  exact Set.mem_singleton _

/-- A job of the ceremony of the top tree reads only inputs of the forest completion. -/
theorem topJob_lift (x : SigningSecurityProof.Keys3 C) {forest record target bound : HashCache C}
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (result : Digest × (XmssSecurity.TopIndex → Option (Randomizer × Encoding)))
    (hmem : (result, SigningDescentProof.thView forest) ∈ support
      ((simulateQ XmssSecurity.HashSpec.randomOracle
        (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
          OracleComp XmssSecurity.HashSpec _)).run (SigningDescentProof.thView forest)))
    (htopSecret : ∀ b l, DeterministicSigning.Resolves forest
      (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) (topSecret b l))
    (hft : forest ≤ target) (hfb : forest ≤ bound) (hrb : record ≤ bound)
    (job : Job) (hjob : job ∈ topJobs) :
    ∀ bits, DeterministicSigning.Resolves record (referenceJob forestHash (forestValue x.2.1) x.1 job) bits →
      DeterministicSigning.Resolves target (referenceJob forestHash (forestValue x.2.1) x.1 job) bits := by
  intro bits hbits
  obtain ⟨b, l, rfl⟩ := by
    simpa only [topJobs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] using hjob
  obtain ⟨before, after, value, hrun, hafter⟩ :=
    XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topChainWalk hmem b l 3 (by decide)
  have hwalk := (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter
  refine resolves_transfer (u := bitsOfDigest value) ?_ hbits hft hfb hrb
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc]
  refine (htopSecret b l).bind ?_
  refine DeterministicSigning.Resolves.map (forestHash_resolves _ _ _ ?_) _
  erw [XmssSecurity.Bridge.chainWalk_top]
  exact hwalk

/-- A job of the signature ceremony of a bottom tree reads only inputs of the forest completion. -/
theorem signJob_lift (x : SigningSecurityProof.Keys3 C) {forest record target bound : HashCache C}
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (result : Digest × (XmssSecurity.TopIndex → Option (Randomizer × Encoding)))
    (hmem : (result, SigningDescentProof.thView forest) ∈ support
      ((simulateQ XmssSecurity.HashSpec.randomOracle
        (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
          OracleComp XmssSecurity.HashSpec _)).run (SigningDescentProof.thView forest)))
    (htopSecret : ∀ b l, DeterministicSigning.Resolves forest
      (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) (topSecret b l))
    (hft : forest ≤ target) (hfb : forest ≤ bound) (hrb : record ≤ bound)
    (b : Fin (2 ^ layerHeight)) (encoding : Encoding) (job : Job) (hjob : job ∈ signJobs b encoding) :
    ∀ bits, DeterministicSigning.Resolves record (referenceJob forestHash (forestValue x.2.1) x.1 job) bits →
      DeterministicSigning.Resolves target (referenceJob forestHash (forestValue x.2.1) x.1 job) bits := by
  intro bits hbits
  simp only [signJobs, List.mem_map, List.mem_finRange, true_and] at hjob
  obtain ⟨l, rfl⟩ := hjob
  obtain ⟨before, after, value, hrun, hafter⟩ :=
    XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topChainWalk hmem b l (encoding l).val
      (by have := (encoding l).isLt; norm_num [XmssSecurity.chainLength, chainLength,
        XmssSecurity.winternitzBits, winternitzBits] at this ⊢; omega)
  have hwalk := (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter
  refine resolves_transfer (u := bitsOfDigest value) ?_ hbits hft hfb hrb
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc]
  refine (htopSecret b l).bind ?_
  refine DeterministicSigning.Resolves.map (forestHash_resolves _ _ _ ?_) _
  erw [XmssSecurity.Bridge.chainWalk_top]
  exact hwalk

/-- A job of the ceremony of a bottom tree reads only inputs of the forest completion and
inputs that are not relevant to the forest. -/
theorem bottomJob_lift (x : SigningSecurityProof.Keys3 C) {forest record target bound : HashCache C}
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (result : Digest × (XmssSecurity.TopIndex → Option (Randomizer × Encoding)))
    (hmem : (result, SigningDescentProof.thView forest) ∈ support
      ((simulateQ XmssSecurity.HashSpec.randomOracle
        (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
          OracleComp XmssSecurity.HashSpec _)).run (SigningDescentProof.thView forest)))
    (hsecret : ∀ e l, DeterministicSigning.Resolves forest
      (forestValue x.2.1 (.chain bottomLayer e l (digit 0))) (secret e l))
    (hft : forest ≤ target) (hfb : forest ≤ bound) (hrb : record ≤ bound)
    (hT : ∀ input value, ¬forestRelevant x.1 input → record input = some value →
      target input = some value)
    (b : Fin (2 ^ layerHeight)) (job : Job) (hjob : job ∈ bottomJobs b) :
    ∀ bits, DeterministicSigning.Resolves record (referenceJob forestHash (forestValue x.2.1) x.1 job) bits →
      DeterministicSigning.Resolves target (referenceJob forestHash (forestValue x.2.1) x.1 job) bits := by
  classical
  intro bits hbits
  simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_singleton] at hjob
  rcases hjob with (⟨k, l, rfl⟩ | ⟨k, rfl⟩) | rfl
  · refine resolves_lift_bind (fun vs hvs => resolves_lift_bound _ _
      (mapM_bound_zero _ _ _ fun _ => forestValue_irrelevant _ _ _) hT vs hvs) ?_ bits hbits
    intro vs hvs
    obtain ⟨start, hstart, hhead⟩ := resolves_mapM_head (d := 0) hvs
    have hs : start = secret (bottomKey b k) l := (hstart.mono hrb).unique ((hsecret _ l).mono hfb)
    have hwalk : ∀ n ≤ 3, ∀ v, DeterministicSigning.Resolves record
        (forestHash (Verification.chainWalkWithHash x.1 bottomLayer (bottomKey b k) l 0 n (vs.getD 0 0))) v →
        DeterministicSigning.Resolves target
          (forestHash (Verification.chainWalkWithHash x.1 bottomLayer (bottomKey b k) l 0 n (vs.getD 0 0))) v := by
      intro n hn v hv
      obtain ⟨before, after, value, hrun, hafter⟩ :=
        XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_chainWalk hmem (bottomKey b k) l n hn
      have hf := (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter
      refine resolves_transfer (u := value) (forestHash_resolves _ _ _ ?_) hv hft hfb hrb
      rw [hhead, hs]
      erw [XmssSecurity.Bridge.chainWalk_bottom]
      exact hf
    refine resolves_lift_bind (hwalk 1 (by decide)) (fun _ _ => ?_)
    refine resolves_lift_bind (hwalk 2 (by decide)) (fun _ _ => ?_)
    refine resolves_lift_bind (hwalk 3 (by decide)) (fun _ _ v h => ?_)
    rw [← h.pure_inv]
    exact .pure _
  · refine resolves_lift_bound _ _ ?_ hT bits hbits
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (mapM_bound_zero _ _ _ fun _ => forestValue_irrelevant _ _ _) (fun vs _ => ?_)
    rw [isQueryBoundP_map_iff]
    refine forestHash_irrelevant _ _ ?_
    exact (isQueryBoundP_query_iff _ _ _).2 (fun hf =>
      (SigningGuessProof.forestRelevant_not_commitment _ _ hf ⟨_, _, _, rfl⟩).elim)
  · refine resolves_lift_bound _ _ ?_ hT bits hbits
    exact isQueryBoundP_bind (n := 0) (m := 0)
      (mapM_bound_zero _ _ _ fun _ => forestValue_irrelevant _ _ _) (fun vs _ => by simp)

/-- The Merkle tree of a bottom tree reads only inputs of the forest completion. -/
theorem bottomMerkle_lift (x : SigningSecurityProof.Keys3 C) {forest record target bound : HashCache C}
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (result : Digest × (XmssSecurity.TopIndex → Option (Randomizer × Encoding)))
    (hmem : (result, SigningDescentProof.thView forest) ∈ support
      ((simulateQ XmssSecurity.HashSpec.randomOracle
        (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
          OracleComp XmssSecurity.HashSpec _)).run (SigningDescentProof.thView forest)))
    (hsecret : ∀ e l, DeterministicSigning.Resolves forest
      (forestValue x.2.1 (.chain bottomLayer e l (digit 0))) (secret e l))
    (hft : forest ≤ target) (hfb : forest ≤ bound) (hrb : record ≤ bound)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (output : Option TreeOutput)
    (hR : DeterministicSigning.Resolves record
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) output)
    (values : List (List Bit))
    (hvalues : DeterministicSigning.Resolves record
      ((bottomJobs b).mapM (referenceJob forestHash (forestValue x.2.1) x.1)) values) :
    ∀ root, DeterministicSigning.Resolves record (forestHash (merkleNode x.1 bottomLayer
        (fun e l => digestAt (values.getD (((List.finRange (2 ^ layerHeight)).flatMap fun k =>
          (List.finRange chainCount).map fun l => (bottomKey b k, l)).idxOf (e, l)) []) 2)
        layerHeight b.val)) root →
      DeterministicSigning.Resolves target (forestHash (merkleNode x.1 bottomLayer
        (fun e l => digestAt (values.getD (((List.finRange (2 ^ layerHeight)).flatMap fun k =>
          (List.finRange chainCount).map fun l => (bottomKey b k, l)).idxOf (e, l)) []) 2)
        layerHeight b.val)) root := by
  intro root hroot
  have hvalid : XmssSecurity.TreeSubtreeValid 16 (XmssSecurity.Concrete.merkleNodeOfNat b.val) := by
    have hb := b.isLt
    simp only [XmssSecurity.TreeSubtreeValid, XmssSecurity.Concrete.merkleNodeOfNat,
      XmssSecurity.lifetime, XmssSecurity.treeHeight, layerHeight] at hb ⊢
    omega
  obtain ⟨before, after, value, hrun, hafter⟩ :=
    XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_treeNode hmem 16
      (XmssSecurity.Concrete.merkleNodeOfNat b.val) le_rfl hvalid
  have htree := (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter
  have hvs := hvalues.eval (SigningCacheProof.answersOf record)
    (fun input output ho => by simp [SigningCacheProof.answersOf, ho])
  rw [eval_mapM] at hvs
  simp_rw [← eval_hashEmbed anyPrims, hashEmbed_referenceJob] at hvs
  change bottomOutputs anyPrims (SigningCacheProof.answersOf record) x.2.1 x.1 b = values at hvs
  refine resolves_transfer (u := value) (forestHash_resolves _ _ _ ?_) hroot hft hfb hrb
  refine resolves_merkleNode_bottom _ x.1 secret _ 16 le_rfl b.val
    (lt_of_lt_of_le b.isLt (by decide)) ?_ value htree
  intro i hi ends hends
  funext l
  let k : Fin (2 ^ layerHeight) := ⟨i.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
  have hek : bottomKey b k = i := by
    apply Fin.ext
    simp only [bottomKey, k, ← hi, layerHeight]
    exact Nat.div_add_mod _ _
  obtain ⟨start, finish, hs, hwk⟩ := resolves_referenceBottom_chains x record top b k output hR l
  have h1 := resolves_forestValue anyPrims record record le_rfl _ _ _ hs
  change replayStarts anyPrims x record bottomLayer (bottomKey b k) l = start at h1
  have hv := SigningCacheProof.resolves_value hwk
  erw [XmssSecurity.Concrete.CacheReplay.eval_chainWalk] at hv
  have hst : start = secret (bottomKey b k) l := (hs.mono hrb).unique ((hsecret _ l).mono hfb)
  unfold XmssSecurity.Concrete.oneTimePublicKey at hends
  have hE := hends.of_sequenceFin l
  rw [← hek, ← hst] at hE
  have hend := (hwk.mono (SigningCacheProof.thView_mono hrb)).unique
    (hE.mono (SigningCacheProof.thView_mono hfb))
  rw [← hend, ← hv, ← h1, ← hek, ← hvs]
  exact (bottomOutputs_cpk (prims := anyPrims) (h := SigningCacheProof.answersOf record)
    x.2.1 x.1 b k l).2.2.trans (SigningCacheProof.E_chainWalk_bottom anyPrims record x.1
      (bottomKey b k) l 0 3 _)

/-- The authentication path of a top signature reads only inputs of the forest completion, when the
top tree is resolved. -/
theorem topPath_lift (x : SigningSecurityProof.Keys3 C) {forest record target bound : HashCache C}
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (result : Digest × (XmssSecurity.TopIndex → Option (Randomizer × Encoding)))
    (hmem : (result, SigningDescentProof.thView forest) ∈ support
      ((simulateQ XmssSecurity.HashSpec.randomOracle
        (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
          OracleComp XmssSecurity.HashSpec _)).run (SigningDescentProof.thView forest)))
    (htopSecret : ∀ b l, DeterministicSigning.Resolves forest
      (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) (topSecret b l))
    (hft : forest ≤ target) (hfb : forest ≤ bound) (hrb : record ≤ bound)
    (cache : HashCache C) (top : TopTree)
    (htop : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (hcb : cache ≤ bound) (b : Fin (2 ^ layerHeight)) :
    ∀ path, DeterministicSigning.Resolves record
        (forestHash (merklePath x.1 topLayer top.chainEnd (topKey b))) path →
      DeterministicSigning.Resolves target
        (forestHash (merklePath x.1 topLayer top.chainEnd (topKey b))) path := by
  intro path hpath
  have hends := topCeremony_ends x cache forest bound top htop hcb hfb topSecret htopSecret
  have hlev : ∀ level : Fin layerHeight, ∃ u, DeterministicSigning.Resolves
      (SigningDescentProof.thView forest)
      (merkleNode x.1 topLayer top.chainEnd level.val (Nat.xor ((topKey b).val / 2 ^ level.val) 1)) u := by
    intro level
    have hl : level.val < 16 := level.isLt
    have hj : Nat.xor ((topKey b).val / 2 ^ level.val) 1 < 2 ^ (16 - level.val) :=
      topPath_index_lt b level.val hl
    obtain ⟨before, after, value, hrun, hafter⟩ :=
      XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hmem level.val
        (XmssSecurity.Concrete.topNodeOfNat (Nat.xor ((topKey b).val / 2 ^ level.val) 1))
        (by simp only [XmssSecurity.treeHeight]; omega) (by
          rw [topNodeOfNat_val_of_lt _ (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (by omega)))]
          simpa only [XmssSecurity.treeHeight] using hj)
    exact ⟨value, resolves_merkleNode_top _ x.1 topSecret _ hends level.val (by omega) _ hj value
      ((DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter)⟩
  choose us hus using hlev
  have hall : DeterministicSigning.Resolves (SigningDescentProof.thView forest)
      (merklePath x.1 topLayer top.chainEnd (topKey b)) us := by
    unfold merklePath
    rw [XmssSecurity.Bridge.sequenceFin_eq]
    exact DeterministicSigning.Resolves.sequenceFin hus
  exact resolves_transfer (forestHash_resolves _ _ _ hall) hpath hft hfb hrb

/-- The check of a top signature reads only inputs of the forest completion and inputs that are not
relevant to the forest, when the top tree is resolved. -/
theorem topCheck_lift (x : SigningSecurityProof.Keys3 C) {forest record target bound : HashCache C}
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (result : Digest × (XmssSecurity.TopIndex → Option (Randomizer × Encoding)))
    (hmem : (result, SigningDescentProof.thView forest) ∈ support
      ((simulateQ XmssSecurity.HashSpec.randomOracle
        (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
          OracleComp XmssSecurity.HashSpec _)).run (SigningDescentProof.thView forest)))
    (htopSecret : ∀ b l, DeterministicSigning.Resolves forest
      (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) (topSecret b l))
    (hft : forest ≤ target) (hfb : forest ≤ bound) (hrb : record ≤ bound)
    (hT : ∀ input value, ¬forestRelevant x.1 input → record input = some value →
      target input = some value)
    (cache : HashCache C) (top : TopTree)
    (htop : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (hcb : cache ≤ bound) (b : Fin (2 ^ layerHeight)) (root : Digest) (base : Randomizer)
    (randomness : Randomizer) (encoding : Encoding)
    (hselected : DeterministicSigning.Resolves record (forestHash (grind x.1 topLayer (topKey b)
      (littleEndianBytes 16 root) base randomizerAttemptLimit 0)) (some (randomness, encoding)))
    (values : List (List Bit))
    (hvalues : DeterministicSigning.Resolves record
      ((signJobs b encoding).mapM (referenceJob forestHash (forestValue x.2.1) x.1)) values)
    (path : Fin layerHeight → Digest)
    (hpath : DeterministicSigning.Resolves record
      (forestHash (merklePath x.1 topLayer top.chainEnd (topKey b))) path) :
    ∀ topRoot, DeterministicSigning.Resolves record (forestHash (Verification.layerRootWithHash x.1 topLayer (topKey b)
        (littleEndianBytes 16 root) ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) topRoot →
      DeterministicSigning.Resolves target (forestHash (Verification.layerRootWithHash x.1 topLayer (topKey b)
        (littleEndianBytes 16 root) ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) topRoot := by
  intro topRoot htopRoot
  refine forestHash_resolves _ _ _ ?_
  have hS := resolves_forestHash _ _ _ htopRoot
  have hSW := SigningCacheProof.thView_mono hrb
  have hS0W := SigningCacheProof.thView_mono hfb
  have hS0T := SigningCacheProof.thView_mono hft
  have hsel := resolves_forestHash _ _ _ hselected
  erw [SigningGuessProof.grind_top_eq] at hsel
  obtain ⟨digest, hdigest, hdec⟩ := resolves_topSignFrom_some _ _ _ _ _ _ _ _ _ hsel
  have hchain : ∀ l : ChainIndex, ∃ finish,
      DeterministicSigning.Resolves (SigningDescentProof.thView forest)
        (XmssSecurity.Concrete.topChainWalk x.1 b l 0 3 (topSecret b l) :
          OracleComp XmssSecurity.HashSpec _) finish ∧
      DeterministicSigning.Resolves (SigningDescentProof.thView forest)
        (XmssSecurity.Concrete.topChainWalk x.1 b l (encoding l).val (3 - (encoding l).val)
          (digestAt (values.getD l.val []) 0) : OracleComp XmssSecurity.HashSpec _) finish := by
    intro l
    have hp : (encoding l).val ≤ 3 := by
      have := (encoding l).isLt
      norm_num [XmssSecurity.chainLength, chainLength, XmssSecurity.winternitzBits, winternitzBits] at this ⊢
      omega
    have hjob := resolves_mapM_getD [] (signJobs b encoding) values hvalues l.val (by simp [signJobs])
    simp only [signJobs, List.getElem_map, List.getElem_finRange, referenceJob, List.mapM_cons,
      List.mapM_nil, pure_bind, bind_assoc] at hjob
    obtain ⟨start, hstart, hjob⟩ := hjob.of_bind
    obtain ⟨cv, hcv, hbits⟩ := hjob.of_map
    have hst : start = topSecret b l := (hstart.mono hrb).unique ((htopSecret b l).mono hfb)
    have hcv' := resolves_forestHash _ _ _ hcv
    erw [XmssSecurity.Bridge.chainWalk_top] at hcv'
    obtain ⟨before, after, value, hrun, hafter⟩ :=
      XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topChainWalk hmem b l 3 (by decide)
    have hfull := (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter
    refine ⟨value, hfull, ?_⟩
    rw [show (3 : ℕ) = (encoding l).val + (3 - (encoding l).val) by omega] at hfull
    erw [XmssSecurity.Bridge.topChainWalk_split] at hfull
    obtain ⟨u, hu, hrest⟩ := hfull.of_bind
    rw [hst] at hcv'
    have hcu : u = cv := (hu.mono hS0W).unique (hcv'.mono hSW)
    have hd : digestAt (bitsOfDigest cv) 0 = cv := by simpa using digestAt_zero cv []
    rw [← hbits, hd, ← hcu]
    simpa only [Nat.zero_add] using hrest
  choose fin hfin using hchain
  have hrecover : DeterministicSigning.Resolves (SigningDescentProof.thView forest)
      (OverPermutation.sequenceFin fun l => Verification.recoverChainWithHash x.1 topLayer (topKey b) l (encoding l)
        (digestAt (values.getD l.val []) 0) : OracleComp HashSpec _) fin := by
    rw [XmssSecurity.Bridge.sequenceFin_eq]
    refine DeterministicSigning.Resolves.sequenceFin (fun l => ?_)
    unfold Verification.recoverChainWithHash
    erw [XmssSecurity.Bridge.chainWalk_top]
    exact (hfin l).2
  obtain ⟨before, after, lf, hrun, hafter⟩ :=
    XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hmem 0 b (by omega)
      (by simp [XmssSecurity.topLifetime, XmssSecurity.treeHeight]; exact b.isLt)
  have hlf := (DeterministicSigning.resolves_of_run _ before (lf, after) hrun).mono hafter
  erw [XmssSecurity.Concrete.topTreeNode.eq_def] at hlf
  simp only at hlf
  erw [XmssSecurity.Concrete.topLeafAt.eq_def] at hlf
  obtain ⟨E, hE, hlfHash⟩ := hlf.of_bind
  have hEfin : E = fin := by
    funext l
    unfold XmssSecurity.Concrete.topOneTimePublicKey at hE
    exact (hE.of_sequenceFin l).unique (hfin l).1
  subst hEfin
  have hots : ∀ leaf, DeterministicSigning.Resolves (SigningDescentProof.thView record)
      (Verification.otsLeafWithHash x.1 topLayer (topKey b) (littleEndianBytes 16 root) randomness
        (fun l => digestAt (values.getD l.val []) 0) : OracleComp HashSpec _) leaf → leaf = some lf := by
    intro leaf hleaf
    unfold Verification.otsLeafWithHash at hleaf
    erw [XmssSecurity.Bridge.messageDigest_top] at hleaf
    obtain ⟨d, hd, hleaf⟩ := hleaf.of_bind
    have hdd : d = digest := hd.unique hdigest
    subst hdd
    erw [XmssSecurity.Bridge.decode_eq, hdec] at hleaf
    obtain ⟨ends, hends, hleaf⟩ := hleaf.of_bind
    have hef : ends = E := (hends.mono hSW).unique (hrecover.mono hS0W)
    subst hef
    obtain ⟨lv, hlv, hleaf⟩ := hleaf.of_bind
    erw [XmssSecurity.Bridge.leafHash_top] at hlv
    rw [← hleaf.pure_inv, (hlv.mono hSW).unique (hlfHash.mono hS0W)]
    rfl
  unfold Verification.layerRootWithHash at hS ⊢
  refine resolves_lift_bind ?_ ?_ _ hS
  · intro leaf hleaf
    unfold Verification.otsLeafWithHash at hleaf ⊢
    erw [XmssSecurity.Bridge.messageDigest_top] at hleaf ⊢
    classical
    refine resolves_lift_bind (fun d hd => resolves_lift_bound _ _ (topEncodingHash_irrelevant _ _ _ _ _)
      (fun i a hp h => hT _ _ hp h) d hd) ?_ _ hleaf
    intro d hd
    have hdd : d = digest := hd.unique hdigest
    subst hdd
    rw [XmssSecurity.Bridge.decode_eq, hdec]
    refine resolves_lift_bind (fun ends hends => resolves_transfer hrecover hends hS0T hS0W hSW) ?_
    intro ends hends
    have hef : ends = E := (hends.mono hSW).unique (hrecover.mono hS0W)
    subst hef
    refine resolves_lift_bind (fun lv hlv => ?_) (fun _ _ v h => by rw [← h.pure_inv]; exact .pure _)
    erw [XmssSecurity.Bridge.leafHash_top] at hlv ⊢
    exact resolves_transfer hlfHash hlv hS0T hS0W hSW
  · intro leaf hleaf v h
    rw [hots leaf hleaf] at h ⊢
    refine resolves_lift_bind (fun r hr => ?_) (fun _ _ v h => by rw [← h.pure_inv]; exact .pure _) _ h
    erw [XmssSecurity.Bridge.treeFold_top x.1 b path lf 16 le_rfl] at hr ⊢
    have hends := topCeremony_ends x cache forest bound top htop hcb hfb topSecret htopSecret
    have hpath' := resolves_forestHash _ _ _ hpath
    unfold merklePath at hpath'
    rw [XmssSecurity.Bridge.sequenceFin_eq] at hpath'
    obtain ⟨before, after, rv, hrun, hafter⟩ :=
      XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hmem 16
        (XmssSecurity.Concrete.topNodeOfNat (b.val / 2 ^ 16)) le_rfl (by
          have hb : (b : ℕ) < 65536 := by simpa [layerHeight] using b.isLt
          simp [XmssSecurity.Concrete.topNodeOfNat, XmssSecurity.treeHeight, Nat.div_eq_of_lt hb])
    have hroot := (DeterministicSigning.resolves_of_run _ before (rv, after) hrun).mono hafter
    refine resolves_transfer (resolves_topAuthenticationRoot _ x.1 topSecret b path lf
      (fun u hu => (hu.unique ?_)) (fun i u hu => ?_) 16 le_rfl rv hroot) hr hS0T hS0W hSW
    · erw [XmssSecurity.Concrete.topTreeNode.eq_def]
      simp only
      erw [XmssSecurity.Concrete.topLeafAt.eq_def]
      exact hE.bind hlfHash
    · have hp := hpath'.of_sequenceFin i
      have hm := resolves_merkleNode_top _ x.1 topSecret _ hends i.val
        (by have := i.isLt; simp only [XmssSecurity.treeHeight] at this; omega) _
        (topPath_index_lt b i.val i.isLt) u hu
      exact (hp.mono hSW).unique (hm.mono hS0W)

set_option maxRecDepth 100000 in
/-- The forest completion reads each structural input of the ceremony of the top tree. -/
theorem forestRun_covers_top (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (w : (Option TreeOutput × HashCache C) × HashCache C)
    (hw : w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) ∅)).run z.2))
    (input : Query C) (hrel : forestRelevant x.1 input) (hread : (w.1.2 input).isSome) :
    (z.1.2 input).isSome := by
  obtain ⟨hzw, -, hwrec, hR⟩ := recordReads_resolves _ ∅ z.2 (by intro i v h; cases h) w hw
  obtain ⟨-, -, hzrec, -⟩ := recordReads_resolves (forestRun x) ∅ cache (by intro i v h; cases h) z hz
  have hzfin : z.1.2 ≤ w.2 := hzrec.trans hzw
  obtain ⟨secret, topSecret, result, -, htopSecret, hmem⟩ := forestRun_model x cache z hz
  have hforest : DeterministicSigning.Resolves z.1.2
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) w.1.1 := by
    have hR' := hR
    unfold referenceTree ceremonyOutput at hR' ⊢
    obtain ⟨outputs, houtputs, htail⟩ := hR'.of_bind
    obtain ⟨values, hvalues, rfl⟩ := houtputs.of_map
    obtain ⟨root, hroot, hfinal⟩ := htail.of_bind
    have hvaluesF := resolves_mapM_lift _ _ (topJob_lift x secret topSecret result hmem htopSecret
      le_rfl hzfin hwrec) values hvalues
    have hrootF : DeterministicSigning.Resolves z.1.2 (forestHash (merkleNode x.1 topLayer
        (fun e l => digestAt (values.getD (((List.finRange (2 ^ layerHeight)).flatMap fun b =>
          (List.finRange chainCount).map fun l => (topKey b, l)).idxOf (e, l)) []) 0) layerHeight 0)) root := by
      have htopR := hR
      rw [← hfinal.pure_inv] at htopR
      clear hR' htail hfinal hvalues
      obtain ⟨before, after, value, hrun, hafter⟩ :=
        XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hmem 16
          (XmssSecurity.Concrete.topNodeOfNat 0) le_rfl (by decide)
      have htree := (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter
      refine resolves_transfer (u := value) (forestHash_resolves _ _ _ ?_) hroot le_rfl hzfin hwrec
      exact resolves_merkleNode_top _ x.1 topSecret _
        (topCeremony_ends x w.1.2 z.1.2 w.2 _ htopR hwrec hzfin topSecret htopSecret)
        16 le_rfl 0 (by decide) value htree
    rw [← hfinal.pure_inv]
    exact (hvaluesF.map some).bind (hrootF.bind (.pure _))
  have hle := recordReads_le_of_resolves _ ∅ z.2 z.1.2 w.1.1 (fun _ _ h => by cases h) hforest w hw hzfin
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hread
  simp [hle hv]

set_option maxRecDepth 100000 in
/-- The forest completion reads each structural input of a bottom tree, when the top
tree is resolved in the cache at the start. -/
theorem forestRun_covers_bottom (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (cache : HashCache C)
    (htop : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (w : (Option TreeOutput × HashCache C) × HashCache C)
    (hw : w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) ∅)).run z.2))
    (input : Query C) (hrel : forestRelevant x.1 input) (hread : (w.1.2 input).isSome) :
    (z.1.2 input).isSome := by
  classical
  obtain ⟨hzw, -, hwrec, hR⟩ := recordReads_resolves _ ∅ z.2 (by intro i v h; cases h) w hw
  obtain ⟨hcz, -, hzrec, -⟩ := recordReads_resolves (forestRun x) ∅ cache (by intro i v h; cases h) z hz
  have hzfin : z.1.2 ≤ w.2 := hzrec.trans hzw
  have hcfin : cache ≤ w.2 := hcz.trans hzw
  obtain ⟨secret, topSecret, result, hsecret, htopSecret, hmem⟩ := forestRun_model x cache z hz
  have hzc : z.1.2 ≤ coverCache x.1 z.1.2 w.2 := record_le_coverCache x.1 hzfin
  have hT : ∀ input value, ¬forestRelevant x.1 input → w.1.2 input = some value →
      coverCache x.1 z.1.2 w.2 input = some value :=
    fun _ _ hp hv => coverCache_irrelevant hp (hwrec hv)
  have hcover : DeterministicSigning.Resolves (coverCache x.1 z.1.2 w.2)
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) w.1.1 := by
    have hR' := hR
    unfold referenceTree ceremonyOutput at hR' ⊢
    refine resolves_lift_bind ?_ ?_ _ hR'
    · intro outputs houtputs
      obtain ⟨values, hvalues, rfl⟩ := houtputs.of_map
      exact (resolves_mapM_lift _ _ (bottomJob_lift x secret topSecret result hmem hsecret hzc hzfin hwrec
        hT b) values hvalues).map some
    intro outputs houtputs
    obtain ⟨values, hvalues, rfl⟩ := houtputs.of_map
    refine resolves_lift_bind
      (bottomMerkle_lift x secret topSecret result hmem hsecret hzc hzfin hwrec top b w.1.1 hR values hvalues) ?_
    intro root hroot
    refine resolves_lift_bind (fun base hbase => resolves_lift_bound _ _ ?_ hT base hbase) ?_
    · refine forestHash_irrelevant _ _ ?_
      rw [isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff _ _ _).2 (fun hf => (randomizer_not_forestRelevant _ _ _ _ _ _ hf).elim)
    intro base hbase
    refine resolves_lift_bind (fun selected hselected => resolves_lift_bound _ _ ?_ hT selected hselected) ?_
    · refine forestHash_irrelevant _ _ ?_
      erw [SigningGuessProof.grind_top_eq]
      exact topSignFrom_irrelevant _ _ _ _ _ _ _
    intro selected hselected
    rcases selected with _ | ⟨randomness, encoding⟩
    · intro v h
      rw [← h.pure_inv]
      exact .pure _
    refine resolves_lift_bind ?_ ?_
    · intro outs houts
      obtain ⟨vals, hvals, rfl⟩ := houts.of_map
      exact (resolves_mapM_lift _ _ (signJob_lift x secret topSecret result hmem htopSecret hzc hzfin hwrec
        b encoding) vals hvals).map some
    intro outputs' houtputs'
    obtain ⟨values', hvalues', rfl⟩ := houtputs'.of_map
    refine resolves_lift_bind
      (topPath_lift x secret topSecret result hmem htopSecret hzc hzfin hwrec cache top htop hcfin b) ?_
    intro path hpath
    refine resolves_lift_bind (topCheck_lift x secret topSecret result hmem htopSecret hzc hzfin hwrec hT
      cache top htop hcfin b root base randomness encoding hselected values' hvalues' path hpath) ?_
    intro topRoot _ v h
    split_ifs at h ⊢ <;> (rw [← h.pure_inv]; exact .pure _)
  have hle := recordReads_le_of_resolves _ ∅ z.2 _ w.1.1 (fun _ _ h => by cases h) hcover w hw
    (coverCache_le _ _ _)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hread
  exact isSome_of_coverCache (by rw [hle hv]; rfl) hrel

end SigningOwnCover

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.recordReads_le_of_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.recordReads_le_of_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_transfer

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.forestHash_resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.forestHash_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_mapM_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_mapM_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_mapM_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_mapM_head

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topNodeOfNat_val_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topNodeOfNat_val_of_lt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topPath_index_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topPath_index_lt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topEncodingHash_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topEncodingHash_irrelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.xor_one_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.xor_one_even

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.xor_one_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.xor_one_odd

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_topAuthenticationRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_topAuthenticationRoot

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_topSignFrom_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_topSignFrom_some

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_mapM_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_mapM_getD

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_merkleNode_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_merkleNode_top

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_merkleNode_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_merkleNode_bottom

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topCeremony_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topCeremony_ends

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.coverCache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.coverCache_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.record_le_coverCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.record_le_coverCache

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.coverCache_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.coverCache_irrelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.isSome_of_coverCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.isSome_of_coverCache

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_lift_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_lift_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.resolves_lift_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.resolves_lift_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.forestValue_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.forestValue_irrelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.forestHash_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.forestHash_irrelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.randomizer_not_forestRelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.randomizer_not_forestRelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topSignFrom_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topSignFrom_irrelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.forestRun_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.forestRun_model

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topJob_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topJob_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.signJob_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.signJob_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.bottomJob_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.bottomJob_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.bottomMerkle_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.bottomMerkle_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topPath_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topPath_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.topCheck_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.topCheck_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.forestRun_covers_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.forestRun_covers_top

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCover.forestRun_covers_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCover.forestRun_covers_bottom
