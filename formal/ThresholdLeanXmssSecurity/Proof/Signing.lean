import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import Mathlib.Data.Nat.Bitwise

/-!
# The signing

`SigningCorrectnessStatement` follows from the honest run of `KeyGen` and of the signing (PRAWNS,
Section 3.1). `SigningSecurityStatement` is open.
-/

open OracleComp OracleSpec LeanXmss ENNReal Finset

noncomputable section

set_option linter.constructorNameAsVariable false

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

variable {C : Committee} (prims : Primitives)

def roImpl : QueryImpl (RoSpec C) (StateT (HashCache C) ProbComp) :=
  hashAnswer (C := C) prims + prgAnswer (C := C) prims

def roRun {α : Type} (oa : OracleComp (RoSpec C) α) (s : HashCache C) : ProbComp (α × HashCache C) :=
  (simulateQ (roImpl prims) oa).run s

theorem roImpl_support (t : (RoSpec C).Domain) (s : HashCache C) (p : (RoSpec C).Range t × HashCache C)
    (hp : p ∈ support ((roImpl prims t).run s)) :
    s ≤ p.2 ∧ (NoMpc s → NoMpc p.2) ∧ ∀ h, Good prims h → Agrees h p.2 → Id.run (fixedImpl prims h t) = p.1 := by
  rcases t with q | x
  · exact hashAnswer_support q s p hp
  · change p ∈ support ((prgAnswer prims x).run s) at hp
    unfold prgAnswer at hp
    rw [StateT.run_bind] at hp
    simp only [support_bind] at hp
    obtain ⟨p', hp', hp⟩ := Set.mem_iUnion₂.mp hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    obtain ⟨hle, hn, hd⟩ := hashAnswer_support _ s p' hp'
    exact ⟨hle, hn, fun h hg ha => by
      change prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2 = _
      rw [hd h hg ha]⟩

/-- Every run of a random-oracle computation is the computation with `H` fixed to any `h` that
agrees with the final cache. -/
theorem roRun_support {α : Type} (oa : OracleComp (RoSpec C) α) :
    ∀ s z, z ∈ support (roRun prims oa s) →
      s ≤ z.2 ∧ (NoMpc s → NoMpc z.2) ∧ ∀ h, Good prims h → Agrees h z.2 → z.1 = D prims h oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s z hz
    simp [roRun] at hz
    subst hz
    exact ⟨le_refl _, id, fun _ _ _ => rfl⟩
  | query_bind t k ih =>
    intro s z hz
    simp only [roRun, simulateQ_bind, simulateQ_query, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map] at hp
    obtain ⟨hle1, hn1, hd1⟩ := roImpl_support prims t s p hp
    obtain ⟨hle2, hn2, hd2⟩ := ih p.1 p.2 z hz
    refine ⟨hle1.trans hle2, fun h => hn2 (hn1 h), fun h hg ha => ?_⟩
    rw [hd2 h hg ha, ← hd1 h hg (ha.mono hle2)]
    simp [D, simulateQ_bind]

/-! ## Computations with a fixed `H` -/

section Fixed

variable {prims} {h : Query C → HashOutput}

theorem D_sequenceFin {α : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp (RoSpec C) α),
    D prims h (Concrete.sequenceFin f) = fun i => D prims h (f i)
  | 0, f => by funext i; exact i.elim0
  | n + 1, f => by
    rw [Concrete.sequenceFin, D_bind, D_bind, D_sequenceFin, D_pure]
    funext i
    cases i using Fin.cases <;> rfl

theorem tweakable_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    tweakable (C := C) (oa >>= f) = tweakable oa >>= fun a => tweakable (f a) := by
  simp [tweakable, simulateQ_bind]

theorem tweakable_pure {α : Type} (a : α) : tweakable (C := C) (pure a : OracleComp HashSpec α) = pure a := by
  simp [tweakable]

theorem tweakable_map {α β : Type} (f : α → β) (oa : OracleComp HashSpec α) :
    tweakable (C := C) (f <$> oa) = f <$> tweakable oa := by
  simp [tweakable]

theorem tweakable_oracleHash (x : HashInput) :
    tweakable (C := C) (Concrete.oracleHash x : OracleComp HashSpec HashOutput) = hashQuery (.hash x) := by
  simp [tweakable, Concrete.oracleHash, hashQuery]

theorem tweakable_sequenceFin {α : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp HashSpec α),
    tweakable (C := C) (Concrete.sequenceFin f) = Concrete.sequenceFin fun i => tweakable (f i)
  | 0, f => by simp [Concrete.sequenceFin, tweakable_pure]
  | n + 1, f => by
    simp only [Concrete.sequenceFin, tweakable_bind, tweakable_pure, tweakable_sequenceFin]

/-- A leanVM computation with `H` fixed to `h`. -/
abbrev E (prims : Primitives) (h : Query C → HashOutput) {α : Type} (oa : OracleComp HashSpec α) : α :=
  D prims h (tweakable oa)

theorem E_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    E prims h (oa >>= f) = E prims h (f (E prims h oa)) := by
  rw [E, tweakable_bind, D_bind]

theorem E_pure {α : Type} (a : α) : E prims h (pure a : OracleComp HashSpec α) = a := by
  rw [E, tweakable_pure, D_pure]

theorem E_oracleHash (x : HashInput) : E prims h (Concrete.oracleHash x : OracleComp HashSpec HashOutput) = h (.hash x) := by
  rw [E, tweakable_oracleHash, D_hashQuery]

theorem E_tweakableHash (P : PublicParameter) (dom : HashDomain) (payload : HashInput) :
    E prims h (Concrete.tweakableHash P dom payload : OracleComp HashSpec Digest) =
      truncateHash (h (.hash (tweakableHashInput P dom payload))) := by
  unfold Concrete.tweakableHash
  rw [E_bind, E_oracleHash, E_pure]

theorem E_sequenceFin {α : Type} {n : ℕ} (f : Fin n → OracleComp HashSpec α) :
    E prims h (Concrete.sequenceFin f) = fun i => E prims h (f i) := by
  rw [E, tweakable_sequenceFin, D_sequenceFin]

theorem E_chainWalk_zero (P : PublicParameter) (lay : Layer) (key : KeyIndex) (l : ChainIndex) (s : ℕ)
    (v : Digest) : E prims h (Concrete.chainWalk P lay key l s 0 v) = v := by
  rw [Concrete.chainWalk, E_pure]

theorem E_chainWalk_succ (P : PublicParameter) (lay : Layer) (key : KeyIndex) (l : ChainIndex) (s n : ℕ)
    (v : Digest) : E prims h (Concrete.chainWalk P lay key l s (n + 1) v) =
      if hs : s + n < chainLength - 1 then
        truncateHash (h (.hash (tweakableHashInput P (.chain lay key ⟨s + n, hs⟩)
          (Concrete.chainPayload l (E prims h (Concrete.chainWalk P lay key l s n v))))))
      else 0 := by
  rw [Concrete.chainWalk, E_bind]
  split_ifs
  · rw [E_tweakableHash]
  · rw [E_pure]

theorem E_chainWalk_add (P : PublicParameter) (lay : Layer) (key : KeyIndex) (l : ChainIndex) (s a : ℕ)
    (v : Digest) : ∀ b, E prims h (Concrete.chainWalk P lay key l s (a + b) v) =
      E prims h (Concrete.chainWalk P lay key l (s + a) b (E prims h (Concrete.chainWalk P lay key l s a v)))
  | 0 => by rw [E_chainWalk_zero, Nat.add_zero]
  | b + 1 => by
    rw [← Nat.add_assoc, E_chainWalk_succ, E_chainWalk_succ, E_chainWalk_add P lay key l s a v b]
    simp only [Nat.add_assoc]

theorem E_grind_spec (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput) (base : Randomness) :
    ∀ attempts trial randomness encoding,
    E prims h (grind P lay key message base attempts trial) = some (randomness, encoding) →
      Codeword.decode (E prims h (Concrete.messageDigest P lay key message randomness)) = some encoding
  | 0, trial, randomness, encoding, hg => by rw [grind, E_pure] at hg; cases hg
  | attempts + 1, trial, randomness, encoding, hg => by
    rw [grind, E_bind] at hg
    revert hg
    rcases hd : Codeword.decode (E prims h (Concrete.messageDigest P lay key message
      (base + BitVec.ofNat digestBits trial))) with _ | enc
    · intro hg
      exact E_grind_spec P lay key message base attempts (trial + 1) randomness encoding hg
    · intro hg
      simp only [E_pure] at hg
      cases hg
      exact hd

theorem E_merkleNode_succ (P : PublicParameter) (lay : Layer) (f : KeyIndex → ChainIndex → Digest) (n idx : ℕ) :
    E prims h (merkleNode P lay f (n + 1) idx) =
      truncateHash (h (.hash (tweakableHashInput P (.node lay (n + 1) idx) (Concrete.nodePayload
        (E prims h (merkleNode P lay f n (2 * idx))) (E prims h (merkleNode P lay f n (2 * idx + 1))))))) := by
  rw [merkleNode, E_bind, E_bind, E_tweakableHash]

theorem E_treeFold_succ (P : PublicParameter) (lay : Layer) (key : KeyIndex) (path : Fin layerHeight → Digest)
    (n : ℕ) (v : Digest) :
    E prims h (Concrete.treeFold P lay key path (n + 1) v) =
      if key.val.testBit n then
        truncateHash (h (.hash (tweakableHashInput P (.node lay (n + 1) (key.val / 2 ^ (n + 1))) (Concrete.nodePayload
          (if hn : n < layerHeight then path ⟨n, hn⟩ else 0) (E prims h (Concrete.treeFold P lay key path n v))))))
      else
        truncateHash (h (.hash (tweakableHashInput P (.node lay (n + 1) (key.val / 2 ^ (n + 1))) (Concrete.nodePayload
          (E prims h (Concrete.treeFold P lay key path n v)) (if hn : n < layerHeight then path ⟨n, hn⟩ else 0))))) := by
  rw [Concrete.treeFold, E_bind]
  split_ifs <;> rw [E_tweakableHash]

theorem E_merkle_ascent (P : PublicParameter) (lay : Layer) (f : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    ∀ n ≤ layerHeight, E prims h (Concrete.treeFold P lay key
        (fun level => E prims h (merkleNode P lay f level.val (Nat.xor (key.val / 2 ^ level.val) 1))) n
        (E prims h (merkleNode P lay f 0 key.val))) =
      E prims h (merkleNode P lay f n (key.val / 2 ^ n))
  | 0, _ => by rw [Concrete.treeFold, E_pure, pow_zero, Nat.div_one]
  | n + 1, hn => by
    rw [E_treeFold_succ, E_merkle_ascent P lay f key n (by omega), E_merkleNode_succ, dif_pos (by omega)]
    have hdiv : key.val / 2 ^ (n + 1) = key.val / 2 ^ n / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hbit : key.val.testBit n = (key.val / 2 ^ n).testBit 0 := by
      rw [Nat.testBit_div_two_pow, Nat.zero_add]
    rw [hbit, hdiv]
    set q := key.val / 2 ^ n
    rcases Nat.even_or_odd q with hq | hq
    · have h0 : q.testBit 0 = false := by
        rw [Nat.testBit_zero]; simp [Nat.even_iff.mp hq]
      have hx : Nat.xor q 1 = 2 * (q / 2) + 1 := by
        rw [show Nat.xor q 1 = q ^^^ 1 from rfl, Nat.xor_one_of_even hq]; have := Nat.even_iff.mp hq; omega
      rw [h0, if_neg (by simp), hx, show 2 * (q / 2) = q by have := Nat.even_iff.mp hq; omega]
    · have h1 : q.testBit 0 = true := by
        rw [Nat.testBit_zero]; simp [Nat.odd_iff.mp hq]
      have hx : Nat.xor q 1 = 2 * (q / 2) := by
        rw [show Nat.xor q 1 = q ^^^ 1 from rfl, Nat.xor_one_of_odd hq]; have := Nat.odd_iff.mp hq; omega
      rw [h1, if_pos rfl, hx, show 2 * (q / 2) + 1 = q by have := Nat.odd_iff.mp hq; omega]

theorem E_merkleNode_zero (P : PublicParameter) (lay : Layer) (f : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    E prims h (merkleNode P lay f 0 key.val) = E prims h (Concrete.leafHash P lay key (f key)) := by
  have : (⟨key.val % lifetime, Nat.mod_lt _ (by decide)⟩ : KeyIndex) = key := Fin.ext (Nat.mod_eq_of_lt key.isLt)
  rw [merkleNode, this]

theorem E_layerRoot (P : PublicParameter) (lay : Layer) (f : KeyIndex → ChainIndex → Digest) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) (encoding : Encoding)
    (hdec : Codeword.decode (E prims h (Concrete.messageDigest P lay key message part.randomness)) = some encoding)
    (hends : ∀ l, E prims h (Concrete.recoverChain P lay key l (encoding l) (part.chainValues l)) = f key l)
    (hpath : part.path = E prims h (merklePath P lay f key)) :
    E prims h (Concrete.layerRoot P lay key message part) =
      some (E prims h (merkleNode P lay f layerHeight (key.val / 2 ^ layerHeight))) := by
  unfold Concrete.layerRoot Concrete.otsLeaf
  rw [E_bind, E_bind, hdec]
  dsimp only
  rw [E_bind, E_sequenceFin, E_bind, E_pure]
  dsimp only
  rw [E_bind, E_pure]
  have hf : (fun l => E prims h (Concrete.recoverChain P lay key l (encoding l) (part.chainValues l))) = f key :=
    funext hends
  rw [hf, ← E_merkleNode_zero, hpath, merklePath, E_sequenceFin, E_merkle_ascent P lay f key _ le_rfl]

end Fixed

theorem sum_testBit_mul_two_pow : ∀ (n N : ℕ), N < 2 ^ n →
    ∑ k ∈ range n, (if N.testBit k then 1 else 0) * 2 ^ k = N
  | 0, N, hN => by simp at hN; simp [hN]
  | n + 1, N, hN => by
    rw [Finset.sum_range_succ']
    have ih := sum_testBit_mul_two_pow n (N / 2) (by rw [pow_succ] at hN; omega)
    have hs : ∀ k, N.testBit (k + 1) = (N / 2).testBit k := fun k => by
      rw [Nat.testBit_succ]
    simp only [hs, pow_succ, ← mul_assoc]
    rw [← Finset.sum_mul, ih, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [h] <;> omega

theorem digestOfBits_append (d : Digest) (rest : List Bit) : digestOfBits (bitsOfDigest d ++ rest) = d := by
  unfold digestOfBits
  have hlen : (bitsOfDigest d).length = digestBits := by simp [bitsOfDigest]
  have hget : ∀ k ∈ range digestBits, ((bitsOfDigest d ++ rest).getD k 0).val =
      if d.toNat.testBit k then 1 else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hk)]
    simp only [bitsOfDigest, List.getElem?_ofFn]
    simp [hk, BitVec.getLsbD]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun k hk => by rw [hget k hk], sum_testBit_mul_two_pow _ _ d.isLt]
  simp

theorem digestAt_zero (d : Digest) (rest : List Bit) : digestAt (bitsOfDigest d ++ rest) 0 = d := by
  simp [digestAt, digestOfBits_append]

theorem digestAt_succ (d : Digest) (rest : List Bit) (k : ℕ) :
    digestAt (bitsOfDigest d ++ rest) (k + 1) = digestAt rest k := by
  unfold digestAt
  rw [show digestBits * (k + 1) = digestBits + digestBits * k by ring, ← List.drop_drop,
    List.drop_left' (length_bitsOfDigest d)]

theorem digestAt_bits (d : Digest) : digestAt (bitsOfDigest d) 0 = d := by
  simpa using digestAt_zero d []

theorem getD_map_idxOf_of_mem {α β : Type} [BEq α] [LawfulBEq α] (L : List α) (g : α → β) (k : α) (hk : k ∈ L) (d : β) :
    (L.map g).getD (L.idxOf k) d = g k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hk)]
  simp [List.getElem_idxOf]

theorem getD_map_finRange {β : Type} {n : ℕ} (g : Fin n → β) (k : Fin n) (d : β) :
    ((List.finRange n).map g).getD k.val d = g k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp

theorem bottomKey_mod (b k : Fin (2 ^ layerHeight)) : (bottomKey b k).val % 2 ^ layerHeight = k.val := by
  simp only [bottomKey]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt k.isLt

theorem bottomKey_treeOf (e : KeyIndex) :
    bottomKey (treeOf e) ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ = e := by
  apply Fin.ext
  simp only [bottomKey, treeOf]
  exact Nat.div_add_mod _ _

theorem keyAt_bottom (e : KeyIndex) : keyAt e bottomLayer = e := by
  apply Fin.ext; simp [keyAt, bottomLayer]

theorem keyAt_top (e : KeyIndex) : keyAt e topLayer = topKey (treeOf e) := by
  apply Fin.ext; simp [keyAt, topKey, treeOf, topLayer]

/-! ## The threshold PRF combines -/

/-- `Digest` with `^^^` as the addition, so that a fold of `^^^` is a sum. -/
def XorDigest := Digest

instance : Zero XorDigest := ⟨0#digestBits⟩

instance : Add XorDigest := ⟨fun a b => BitVec.xor a b⟩

instance : Neg XorDigest := ⟨id⟩

instance : AddCommGroup XorDigest where
  add_assoc a b c := BitVec.xor_assoc a b c
  zero_add a := BitVec.zero_xor (x := a)
  add_zero a := BitVec.xor_zero (x := a)
  add_comm a b := BitVec.xor_comm a b
  neg_add_cancel a := BitVec.xor_self (x := a)
  nsmul := nsmulRec
  zsmul := zsmulRec

def toXor (d : Digest) : XorDigest := d

theorem toXor_injective : Function.Injective toXor := fun _ _ h => h

theorem toXor_xor (a b : Digest) : toXor (a ^^^ b) = toXor a + toXor b := rfl

theorem toXor_zero : toXor 0#digestBits = 0 := rfl

theorem toXor_foldl {α : Type} (f : α → Digest) (a : Digest) (l : List α) :
    toXor (l.foldl (fun acc x => acc ^^^ f x) a) = toXor a + (l.map (toXor ∘ f)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, toXor_xor, add_assoc]

theorem toXor_foldl_eq_sum {α : Type} [DecidableEq α] (f : α → Digest) (a : Digest) (l : List α) (hl : l.Nodup) :
    toXor (l.foldl (fun acc x => acc ^^^ f x) a) = toXor a + ∑ x ∈ l.toFinset, toXor (f x) := by
  rw [toXor_foldl, List.sum_toFinset _ hl]
  rfl

theorem parties_nodup : C.parties.Nodup := List.nodup_finRange _

theorem toXor_combine (J : C.Quorum) (parts : C.Party → Digest) :
    toXor (combine J parts) = ∑ i ∈ J.1, toXor (parts i) := by
  rw [combine, toXor_foldl_eq_sum _ _ _ (parties_nodup.filter _)]
  simp [toXor_zero, Committee.parties]

theorem combine_congr (J : C.Quorum) {f g : C.Party → Digest} (hfg : ∀ i ∈ J.1, f i = g i) :
    combine J f = combine J g := by
  apply toXor_injective
  rw [toXor_combine, toXor_combine]
  exact Finset.sum_congr rfl fun i hi => by rw [hfg i hi]

section Fixed

variable {prims} {h : Query C → HashOutput}

theorem toXor_prfValue (seeds : C.Term → HashOutput) (x : Point) :
    toXor (D prims h (prfValue seeds x)) = ∑ T, toXor (truncateHash (h (.prf (seeds T) x))) := by
  rw [prfValue, D_bind, D_mapM, D_pure]
  simp only [prf, D_map, D_hashQuery]
  rw [List.foldl_map, toXor_foldl_eq_sum _ _ _ terms_nodup]
  simp [toXor_zero, Committee.terms]

theorem toXor_eval (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (m : Message) :
    toXor (D prims h (eval keys i J x m)) =
      ∑ T ∈ L J i, toXor (truncateHash (h (.prf (keys.seed T) x))) +
        ∑ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i), toXor (truncateHash (h (.mask (keys.pairKey j) x m J))) := by
  rw [eval, D_bind, D_bind, D_mapM, D_mapM, D_pure]
  simp only [prf, D_map, D_hashQuery]
  rw [List.foldl_append, List.foldl_map, List.foldl_map, toXor_foldl_eq_sum _ _ _ (parties_nodup.filter _),
    toXor_foldl_eq_sum _ _ _ (terms_nodup.filter _)]
  simp [toXor_zero, Committee.terms, Committee.parties]

end Fixed

theorem XorDigest.add_self (a : XorDigest) : a + a = 0 := BitVec.xor_self (x := a)

theorem sum_pairs_symm_eq_zero (s : Finset C.Party) (N : C.Party → C.Party → XorDigest)
    (hN : ∀ i j, N i j = N j i) :
    ∑ i ∈ s, ∑ j ∈ univ.filter (fun j => j ∈ s ∧ j ≠ i), N i j = 0 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) (fun p _ => by rw [hN]; exact XorDigest.add_self _)
    (fun p hp _ => ?_) (fun p hp => ?_) (fun p _ => rfl)
  · simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    intro hswap
    exact hp.2.2.2 (congrArg Sigma.fst hswap)
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩

theorem mem_holders_of_mem_L {J : C.Quorum} {i : C.Party} {T : C.Term} (h : T ∈ L J i) : i ∈ C.holders T := by
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have := Finset.mem_of_min h
  simp only [Finset.mem_sdiff] at this
  simpa [Committee.holders] using this.2

theorem sum_L (J : C.Quorum) (g : C.Term → XorDigest) : ∑ i ∈ J.1, ∑ T ∈ L J i, g T = ∑ T, g T := by
  simp only [L, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hne := quorum_sdiff_term_nonempty J T
  rw [← Finset.coe_min' hne]
  simp only [WithTop.coe_eq_coe]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_sdiff.mp (Finset.min'_mem _ hne)).1]

section Fixed

variable {prims} {h : Query C → HashOutput}

/-- The parts of a quorum combine to `F(x)` for every fixed `H`, since each mask appears twice
(PRAWNS, Definition 2.1). -/
theorem D_combine (P : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (J : C.Quorum) (x : Point) (m : Message) (parts : C.Party → Digest)
    (hparts : ∀ i ∈ J.1, parts i = D prims h (eval (dealtKeys P seeds pairKeys i) i J x m)) :
    combine J parts = D prims h (prfValue seeds x) := by
  rw [combine_congr J hparts]
  apply toXor_injective
  rw [toXor_combine, toXor_prfValue]
  simp only [toXor_eval, Finset.sum_add_distrib]
  have hseed : ∀ i ∈ J.1, ∑ T ∈ L J i, toXor (truncateHash (h (.prf ((dealtKeys P seeds pairKeys i).seed T) x))) =
      ∑ T ∈ L J i, toXor (truncateHash (h (.prf (seeds T) x))) :=
    fun i _ => Finset.sum_congr rfl fun T hT => by simp [dealtKeys, mem_holders_of_mem_L hT]
  rw [Finset.sum_congr rfl hseed, sum_L, sum_pairs_symm_eq_zero, add_zero]
  intro i j
  by_cases hij : i = j
  · rw [hij]
  · simp only [dealtKeys, dif_neg hij, dif_neg (Ne.symm hij), pairOf_comm i j hij]

end Fixed

/-! ## The trees with a fixed `H` -/

section Fixed

variable {prims} {h : Query C → HashOutput}

theorem D_referenceJob (seeds : C.Term → HashOutput) (P : PublicParameter) (job : Job) :
    D prims h (referenceJob tweakable (prfValue seeds) P job) =
      let value := fun k => (job.points.map fun x => D prims h (prfValue seeds x)).getD k 0
      match job.kind with
      | .chainEnd e l => bitsOfDigest (E prims h (Concrete.chainWalk P topLayer e l 0 3 (value 0)))
      | .chainRow e l =>
          bitsOfDigest (E prims h (Concrete.chainWalk P bottomLayer e l 0 1 (value 0)) ^^^ value 1) ++
          bitsOfDigest (E prims h (Concrete.chainWalk P bottomLayer e l 0 2 (value 0)) ^^^ value 2) ++
          bitsOfDigest (E prims h (Concrete.chainWalk P bottomLayer e l 0 3 (value 0)))
      | .chainValue e l p => bitsOfDigest (E prims h (Concrete.chainWalk P topLayer e l 0 p.val (value 0)))
      | .commitment e => bitsOfDigest (truncateHash (h (.hash (commitmentInput P e (value 0)))))
      | .randomizer => bitsOfDigest (value 0) := by
  obtain ⟨kind, points⟩ := job
  unfold referenceJob
  rw [D_bind, D_mapM]
  cases kind
  · exact D_map _ _ _
  · rw [D_bind, D_bind, D_bind, D_pure]
  · exact D_map _ _ _
  · rw [D_map]
    exact congrArg (bitsOfDigest ∘ truncateHash) (E_oracleHash _)
  · rfl

theorem D_refTop (P : PublicParameter) (seeds : C.Term → HashOutput) (top0 : TopTree) :
    ∃ top : TopTree, D prims h (referenceTree tweakable (prfValue seeds) P top0 .top) = some (.top top) ∧
      (∀ b l, top.chainEnd (topKey b) l = E prims h (Concrete.chainWalk P topLayer (topKey b) l 0 3
        (D prims h (prfValue seeds (.chain topLayer (topKey b) l (digit 0)))))) ∧
      top.root = E prims h (merkleNode P topLayer top.chainEnd layerHeight 0) := by
  unfold referenceTree ceremonyOutput
  rw [D_bind, D_map, D_mapM]
  dsimp only
  rw [D_bind, D_pure]
  refine ⟨_, rfl, fun b l => ?_, ?_⟩
  swap
  · dsimp only
  dsimp only
  have htop : topJobs = ((List.finRange (2 ^ layerHeight)).flatMap fun b =>
      (List.finRange numChains).map fun l => (topKey b, l)).map
        fun el => (⟨.chainEnd el.1 el.2, [.chain topLayer el.1 el.2 (digit 0)]⟩ : Job) := by
    simp only [topJobs, List.map_flatMap, List.map_map]
    rfl
  rw [htop, List.map_map, getD_map_idxOf_of_mem _ _ _ (by simp [List.mem_flatMap])]
  simp [D_referenceJob, digestAt_bits]

/-- The outputs of the first run of bottom tree `b` with a fixed `H`. -/
abbrev bottomOutputs (prims : Primitives) (h : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (P : PublicParameter) (b : Fin (2 ^ layerHeight)) : List (List Bit) :=
  (bottomJobs b).map fun job => D prims h (referenceJob tweakable (prfValue seeds) P job)

theorem bottomJobs_eq (b : Fin (2 ^ layerHeight)) : bottomJobs b =
    (bottomKeys b).map (fun el => (⟨.chainRow el.1 el.2, [.chain bottomLayer el.1 el.2 (digit 0),
      .chain bottomLayer el.1 el.2 (digit 1), .chain bottomLayer el.1 el.2 (digit 2)]⟩ : Job)) ++
    ((List.finRange (2 ^ layerHeight)).map fun k =>
      (⟨.commitment (bottomKey b k), [.randomizer bottomLayer (bottomKey b k)]⟩ : Job)) ++
    [⟨.randomizer, [.randomizer topLayer (topKey b)]⟩] := by
  simp only [bottomJobs, bottomKeys, List.map_flatMap, List.map_map]
  rfl

theorem bottomOutputs_cpk (seeds : C.Term → HashOutput) (P : PublicParameter) (b k : Fin (2 ^ layerHeight))
    (l : ChainIndex) :
    let bits := (bottomOutputs prims h seeds P b).getD ((bottomKeys b).idxOf (bottomKey b k, l)) []
    let value := fun p => D prims h (prfValue seeds (.chain bottomLayer (bottomKey b k) l p))
    digestAt bits 0 = E prims h (Concrete.chainWalk P bottomLayer (bottomKey b k) l 0 1 (value (digit 0))) ^^^
        value (digit 1) ∧
      digestAt bits 1 = E prims h (Concrete.chainWalk P bottomLayer (bottomKey b k) l 0 2 (value (digit 0))) ^^^
        value (digit 2) ∧
      digestAt bits 2 = E prims h (Concrete.chainWalk P bottomLayer (bottomKey b k) l 0 3 (value (digit 0))) := by
  have hmem : (bottomKey b k, l) ∈ bottomKeys b := by simp [List.mem_flatMap]
  simp only [bottomOutputs, bottomJobs_eq, List.append_assoc, List.map_append]
  rw [List.getD_append _ _ _ _ (by simpa using List.idxOf_lt_length_iff.mpr hmem), List.map_map,
    getD_map_idxOf_of_mem _ _ _ hmem]
  simp only [Function.comp, D_referenceJob]
  simp [List.append_assoc, digestAt_zero, digestAt_succ, digestAt_bits]

theorem bottomOutputs_commitment (seeds : C.Term → HashOutput) (P : PublicParameter) (b k : Fin (2 ^ layerHeight)) :
    digestAt ((bottomOutputs prims h seeds P b).getD ((bottomKeys b).length + (bottomKey b k).val % 2 ^ layerHeight) [])
      0 = truncateHash (h (.hash (commitmentInput P (bottomKey b k)
        (D prims h (prfValue seeds (.randomizer bottomLayer (bottomKey b k))))))) := by
  have hk := (bottomKey b k).isLt
  simp only [bottomOutputs, bottomJobs_eq, List.map_append]
  rw [List.getD_append _ _ _ _ (by simp [bottomKey_mod]), List.getD_append_right _ _ _ _ (by simp),
    bottomKey_mod]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [List.map_map, getD_map_finRange]
  simp only [Function.comp, D_referenceJob]
  simp [digestAt_bits]

/-- The chain values of the top signature of bottom tree `b` with a fixed `H`. -/
theorem signOutputs_value (seeds : C.Term → HashOutput) (P : PublicParameter) (b : Fin (2 ^ layerHeight))
    (encoding : Encoding) (l : ChainIndex) :
    digestAt (((signJobs b encoding).map fun job => D prims h (referenceJob tweakable (prfValue seeds) P job)).getD l.val [])
      0 = E prims h (Concrete.chainWalk P topLayer (topKey b) l 0 (encoding l).val
        (D prims h (prfValue seeds (.chain topLayer (topKey b) l (digit 0))))) := by
  simp only [signJobs, List.map_map]
  rw [getD_map_finRange]
  simp [D_referenceJob, digestAt_bits]

/-- The top signature of a bottom tree leads to the root of the top tree. -/
theorem topRoot_eq (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree)
    (htopChain : ∀ b l, top.chainEnd (topKey b) l = E prims h (Concrete.chainWalk P topLayer (topKey b) l 0 3
        (D prims h (prfValue seeds (.chain topLayer (topKey b) l (digit 0))))))
    (htopRoot : top.root = E prims h (merkleNode P topLayer top.chainEnd layerHeight 0))
    (b : Fin (2 ^ layerHeight)) (message : HashInput) (randomness : Randomness) (encoding : Encoding)
    (hdec : Codeword.decode (E prims h (Concrete.messageDigest P topLayer (topKey b) message randomness)) =
      some encoding) :
    E prims h (Concrete.layerRoot P topLayer (topKey b) message ⟨randomness, fun l => digestAt
      (((signJobs b encoding).map fun job => D prims h (referenceJob tweakable (prfValue seeds) P job)).getD l.val [])
      0, E prims h (merklePath P topLayer top.chainEnd (topKey b))⟩) = some top.root := by
  have hends : ∀ l, E prims h (Concrete.recoverChain P topLayer (topKey b) l (encoding l) (digestAt
      (((signJobs b encoding).map fun job => D prims h (referenceJob tweakable (prfValue seeds) P job)).getD l.val [])
      0)) = top.chainEnd (topKey b) l := by
    intro l
    have hp : (encoding l).val < chainLength := (encoding l).isLt
    have hadd := E_chainWalk_add (prims := prims) (h := h) P topLayer (topKey b) l 0 (encoding l).val
      (D prims h (prfValue seeds (.chain topLayer (topKey b) l (digit 0)))) (chainLength - 1 - (encoding l).val)
    rw [Nat.zero_add, show (encoding l).val + (chainLength - 1 - (encoding l).val) = 3 by
      simp only [chainLength, winternitzBits] at hp ⊢; omega] at hadd
    unfold Concrete.recoverChain
    rw [signOutputs_value, htopChain, hadd]
  have key := E_layerRoot (prims := prims) (h := h) P topLayer top.chainEnd (topKey b) message ⟨randomness,
      fun l => digestAt
      (((signJobs b encoding).map fun job => D prims h (referenceJob tweakable (prfValue seeds) P job)).getD l.val [])
      0, E prims h (merklePath P topLayer top.chainEnd (topKey b))⟩ encoding hdec hends (by simp only)
  rw [key, htopRoot, show (topKey b).val / 2 ^ layerHeight = 0 from Nat.div_eq_of_lt b.isLt]

end Fixed

/-- The honest signing after `KeyGen'`, on the random oracle alone. -/
def honestRo (P : PublicParameter) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C) (J : C.Quorum)
    (e : KeyIndex) (m : Message) : OracleComp (RoSpec C) (Option Bool) := do
  let some (.top top) ← referenceTree tweakable (prfValue seeds) P emptyTop .top | pure none
  let some tree ← (fun | some (.bottom tree) => some tree | _ => none) <$>
      referenceTree tweakable (prfValue seeds) P top (.bottom (treeOf e)) | pure none
  let parts ← Concrete.sequenceFin fun i =>
    if i ∈ J.1 then eval (keys i) i J (.randomizer bottomLayer e) m else pure 0
  let some _ ← signCodeword P (tree.commitment e) e m (combine J parts) | pure none
  let chainParts ← Concrete.sequenceFin fun i => do
    let values ← signRound2With (fun oa => oa) (fun x => eval (keys i) i J x m) P J (tree.commitment e) e m parts
    pure fun l => ((values.bind (· l)).getD 0)
  let some signature ← assemble P tree e m J parts chainParts | pure (some false)
  some <$> tweakable (Concrete.verify ⟨top.root, P⟩ m signature)

section Fixed

variable {prims} {h : Query C → HashOutput}

/-- The public outputs of bottom tree `b` with a fixed `H`. -/
structure BottomSpec (prims : Primitives) (h : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (P : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight)) (tree : BottomTree) : Prop where
  cpk : ∀ k l, let value := fun p => D prims h (prfValue seeds (.chain bottomLayer (bottomKey b k) l p))
    tree.cpk (bottomKey b k) l =
      (E prims h (Concrete.chainWalk P bottomLayer (bottomKey b k) l 0 1 (value (digit 0))) ^^^ value (digit 1),
        E prims h (Concrete.chainWalk P bottomLayer (bottomKey b k) l 0 2 (value (digit 0))) ^^^ value (digit 2),
        E prims h (Concrete.chainWalk P bottomLayer (bottomKey b k) l 0 3 (value (digit 0))))
  commitment : ∀ k, tree.commitment (bottomKey b k) = truncateHash (h (.hash (commitmentInput P (bottomKey b k)
    (D prims h (prfValue seeds (.randomizer bottomLayer (bottomKey b k)))))))
  root : tree.root = E prims h (merkleNode P bottomLayer (fun e l => (tree.cpk e l).2.2) layerHeight b.val)
  topSignature : E prims h (Concrete.layerRoot P topLayer (topKey b) (bytesLE 16 tree.root) tree.topSignature) =
    some top.root

theorem D_refBottom (P : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (htopChain : ∀ b l, top.chainEnd (topKey b) l = E prims h (Concrete.chainWalk P topLayer (topKey b) l 0 3
        (D prims h (prfValue seeds (.chain topLayer (topKey b) l (digit 0))))))
    (htopRoot : top.root = E prims h (merkleNode P topLayer top.chainEnd layerHeight 0))
    (b : Fin (2 ^ layerHeight)) :
    D prims h (referenceTree tweakable (prfValue seeds) P top (.bottom b)) = none ∨
      ∃ tree, D prims h (referenceTree tweakable (prfValue seeds) P top (.bottom b)) = some (.bottom tree) ∧
        BottomSpec prims h seeds P top b tree := by
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
    refine Or.inr ⟨_, rfl, ⟨fun k l => ?_, fun k => ?_, ?_, ?_⟩⟩
    rotate_left 2
    · dsimp only
    · dsimp only; exact hT
    · obtain ⟨h0, h1, h2⟩ := bottomOutputs_cpk (prims := prims) (h := h) seeds P b k l
      exact Prod.ext h0 (Prod.ext h1 h2)
    · exact bottomOutputs_commitment seeds P b k
  next hG =>
    exact Or.inl rfl

theorem D_signCodeword (P : PublicParameter) (commitment : Digest) (e : KeyIndex) (message : Message) (ρ : Digest)
    (hc : commitment = truncateHash (h (.hash (commitmentInput P e ρ)))) :
    D prims h (signCodeword P commitment e message ρ) =
      E prims h (grind P bottomLayer e (bytesLE 32 message)
        (truncateHash (h (.hash (randomizerInput P bottomLayer e ρ (bytesLE 32 message))))) randomizerAttemptLimit 0) := by
  unfold signCodeword
  change E prims h _ = _
  rw [E_bind, E_oracleHash, if_neg (by rw [hc]; exact not_not.mpr rfl), E_bind, E_oracleHash]

theorem D_signRound2With (part : Point → OracleComp (RoSpec C) Digest) (P : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) (randomness : Randomness)
    (encoding : Encoding)
    (hsc : D prims h (signCodeword P commitment e message (combine J parts)) = some (randomness, encoding)) :
    D prims h (signRound2With (fun oa => oa) part P J commitment e message parts) =
      some (fun l => if (encoding l).val < chainLength - 1 then
        some (D prims h (part (.chain bottomLayer e l (encoding l)))) else none) := by
  unfold signRound2With
  rw [D_bind, hsc]
  dsimp only
  rw [D_bind, D_sequenceFin, D_pure]
  congr 1
  funext l
  split_ifs
  · rw [D_map]
  · rfl

/-- The chain value that `assemble` reveals. -/
def assembledValue (tree : BottomTree) (e : KeyIndex) (J : C.Quorum) (chainParts : C.Party → ChainIndex → Digest)
    (encoding : Encoding) (l : ChainIndex) : Digest :=
  match (encoding l).val with
  | 0 => combine J (chainParts · l)
  | 3 => (tree.cpk e l).2.2
  | p => (if p = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ combine J (chainParts · l)

theorem D_assemble (P : PublicParameter) (tree : BottomTree) (e : KeyIndex) (message : Message) (J : C.Quorum)
    (parts : C.Party → Digest) (chainParts : C.Party → ChainIndex → Digest) (randomness : Randomness)
    (encoding : Encoding)
    (hsc : D prims h (signCodeword P (tree.commitment e) e message (combine J parts)) = some (randomness, encoding))
    (hends : ∀ l, E prims h (Concrete.recoverChain P bottomLayer e l (encoding l)
      (assembledValue tree e J chainParts encoding l)) = (tree.cpk e l).2.2) :
    D prims h (assemble P tree e message J parts chainParts) =
      some ⟨e, fun lay => if lay = bottomLayer then
        ⟨randomness, assembledValue tree e J chainParts encoding,
          E prims h (merklePath P bottomLayer (fun e l => (tree.cpk e l).2.2) e)⟩
        else tree.topSignature⟩ := by
  unfold assemble
  rw [D_bind, hsc]
  dsimp only
  change E prims h _ = _
  rw [E_bind, E_sequenceFin]
  rw [if_neg (by push Not; exact hends)]
  rw [E_bind, E_pure]
  rfl

theorem assembled_ends (P : PublicParameter) (tree : BottomTree) (e : KeyIndex) (J : C.Quorum)
    (chainParts : C.Party → ChainIndex → Digest) (encoding : Encoding) (l : ChainIndex) (value : Digit → Digest)
    (hcpk : tree.cpk e l =
      (E prims h (Concrete.chainWalk P bottomLayer e l 0 1 (value (digit 0))) ^^^ value (digit 1),
        E prims h (Concrete.chainWalk P bottomLayer e l 0 2 (value (digit 0))) ^^^ value (digit 2),
        E prims h (Concrete.chainWalk P bottomLayer e l 0 3 (value (digit 0)))))
    (hcomb : ∀ p, p < chainLength - 1 → (encoding l).val = p → combine J (chainParts · l) = value (encoding l)) :
    E prims h (Concrete.recoverChain P bottomLayer e l (encoding l) (assembledValue tree e J chainParts encoding l)) =
      (tree.cpk e l).2.2 := by
  have hlt : (encoding l).val < chainLength := (encoding l).isLt
  simp only [chainLength, winternitzBits] at hlt
  unfold Concrete.recoverChain assembledValue
  rw [hcpk]
  dsimp only
  obtain h0 | h1 | h2 | h3 : (encoding l).val = 0 ∨ (encoding l).val = 1 ∨ (encoding l).val = 2 ∨
      (encoding l).val = 3 := by omega
  · have he : encoding l = digit 0 := Fin.ext h0
    rw [hcomb 0 (by decide) h0, he]
    rfl
  · have he : encoding l = digit 1 := Fin.ext h1
    rw [hcomb 1 (by decide) h1, he]
    show E prims h (Concrete.chainWalk P bottomLayer e l 1 2 ((E prims h (Concrete.chainWalk P bottomLayer e l 0 1
      (value (digit 0))) ^^^ value (digit 1)) ^^^ value (digit 1))) = _
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact (E_chainWalk_add _ _ _ _ 0 1 _ 2).symm
  · have he : encoding l = digit 2 := Fin.ext h2
    rw [hcomb 2 (by decide) h2, he]
    show E prims h (Concrete.chainWalk P bottomLayer e l 2 1 ((E prims h (Concrete.chainWalk P bottomLayer e l 0 2
      (value (digit 0))) ^^^ value (digit 2)) ^^^ value (digit 2))) = _
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact (E_chainWalk_add _ _ _ _ 0 2 _ 1).symm
  · have he : encoding l = digit 3 := Fin.ext h3
    rw [he]
    exact E_chainWalk_zero _ _ _ _ _ _

theorem D_honestRo (P : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (J : C.Quorum) (e : KeyIndex) (m : Message) :
    D prims h (honestRo P seeds (dealtKeys P seeds pairKeys) J e m) ≠ some false := by
  obtain ⟨top, htop, hchain, hroot⟩ := D_refTop (prims := prims) (h := h) P seeds emptyTop
  rw [honestRo, D_bind, htop]
  dsimp only
  rw [D_bind, D_map]
  rcases D_refBottom (prims := prims) (h := h) P seeds top hchain hroot (treeOf e) with hb | ⟨tree, hb, hspec⟩
  · rw [hb]; simp [D_pure]
  rw [hb]
  dsimp only
  rw [D_bind, D_sequenceFin]
  set parts := fun i => D prims h (if i ∈ J.1 then eval (dealtKeys P seeds pairKeys i) i J
    (.randomizer bottomLayer e) m else pure 0) with hparts
  have hρ : combine J parts = D prims h (prfValue seeds (.randomizer bottomLayer e)) :=
    D_combine P seeds pairKeys J _ m parts fun i hi => by rw [hparts]; dsimp only; rw [if_pos hi]
  have hc : tree.commitment e = truncateHash (h (.hash (commitmentInput P e (combine J parts)))) := by
    have := hspec.commitment ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
    rw [bottomKey_treeOf] at this
    rw [this, hρ]
  rw [D_bind, D_signCodeword _ _ _ _ _ hc]
  rcases hG : E prims h (grind P bottomLayer e (bytesLE 32 m)
    (truncateHash (h (.hash (randomizerInput P bottomLayer e (combine J parts) (bytesLE 32 m)))))
    randomizerAttemptLimit 0) with _ | ⟨randB, encB⟩
  · dsimp only; rw [D_pure]; simp
  have hsc := (D_signCodeword (prims := prims) (h := h) _ _ _ m _ hc).trans hG
  dsimp only
  rw [D_bind, D_sequenceFin]
  simp only [D_bind, D_pure, D_signRound2With (hsc := hsc), Option.bind_some]
  set chainParts : C.Party → ChainIndex → Digest := fun i l =>
    (if (encB l).val < chainLength - 1 then
      some (D prims h (eval (dealtKeys P seeds pairKeys i) i J (.chain bottomLayer e l (encB l)) m)) else none).getD 0
    with hchainParts
  have hends : ∀ l, E prims h (Concrete.recoverChain P bottomLayer e l (encB l)
      (assembledValue tree e J chainParts encB l)) = (tree.cpk e l).2.2 := by
    intro l
    have hcpk' := hspec.cpk ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ l
    rw [bottomKey_treeOf] at hcpk'
    refine assembled_ends P tree e J chainParts encB l
      (fun p => D prims h (prfValue seeds (.chain bottomLayer e l p))) hcpk' fun p hp hep => ?_
    refine D_combine P seeds pairKeys J _ m _ fun i _ => ?_
    simp only [hchainParts, hep, if_pos hp, Option.getD_some]
  have hdecB := E_grind_spec (prims := prims) (h := h) _ _ _ _ _ _ _ _ _ hG
  rw [D_assemble _ _ _ _ _ _ _ randB encB hsc hends]
  dsimp only
  rw [D_map]
  change some (E prims h (Concrete.verify _ m _)) ≠ some false
  unfold Concrete.verify
  dsimp only
  rw [if_pos rfl, if_neg (by decide), keyAt_bottom, keyAt_top, E_bind]
  have hroot' : tree.root = E prims h (merkleNode P bottomLayer
      (fun e l => (tree.cpk e l).2.2) layerHeight (e.val / 2 ^ layerHeight)) := by
    rw [hspec.root, show ((treeOf e) : ℕ) = e.val / 2 ^ layerHeight from rfl]
  rw [E_layerRoot (prims := prims) (h := h) P bottomLayer (fun e l => (tree.cpk e l).2.2) e (bytesLE 32 m)
    ⟨randB, assembledValue tree e J chainParts encB,
      E prims h (merklePath P bottomLayer (fun e l => (tree.cpk e l).2.2) e)⟩ encB hdecB hends (by simp only)]
  dsimp only
  rw [← hroot', E_bind, hspec.topSignature]
  dsimp only
  rw [E_pure]
  simp

end Fixed

/-! ## The world of the honest signing -/

theorem withAddCost_zero_run {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) :
    (simulateQ (impl.withAddCost fun _ => (0 : ℕ)) oa).run =
      (fun a => (a, (1 : Multiplicative ℕ))) <$> simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, WriterT.run_bind, ih, QueryImpl.withAddCost_apply]
    simp [AddWriterT.addTell]

theorem world_free_eq :
    (world (C := C) prims ∘ₛ fun t => query (spec := WorldSpec C) (.inr t)) =
      ((unifFwdImpl (Query C →ₒ HashOutput)).withAddCost fun _ => (0 : ℕ)) + ((roImpl (C := C) prims).withAddCost fun _ => (0 : ℕ)) := by
  funext t
  rcases t with t | t
  · rfl
  · simp only [QueryImpl.apply_compose]
    simp [world, roImpl, localAnswer, QueryImpl.withAddCost_apply]

theorem world_lift_run {α : Type} (oa : OracleComp (RoSpec C) α) (s : HashCache C) :
    (simulateQ (world prims) (free (liftComp oa _))).run.run s =
      (fun p => ((p.1, (1 : Multiplicative ℕ)), p.2)) <$> roRun prims oa s := by
  rw [free, ← QueryImpl.simulateQ_compose, world_free_eq]
  have h := QueryImpl.simulateQ_add_liftComp_right
    ((unifFwdImpl (Query C →ₒ HashOutput)).withAddCost fun _ => (0 : ℕ))
    ((roImpl (C := C) prims).withAddCost fun _ => (0 : ℕ)) oa
  erw [h, withAddCost_zero_run, roRun]
  simp

/-- The lift of a random-oracle computation to the free copy of the world. -/
abbrev φ {α : Type} (oa : OracleComp (RoSpec C) α) : OracleComp (WorldSpec C) α := free (liftComp oa _)

theorem φ_pure {α : Type} (a : α) : φ (pure a : OracleComp (RoSpec C) α) = pure a := by
  rw [φ, liftComp_pure, free]
  exact simulateQ_pure _ _

theorem φ_bind {α β : Type} (oa : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β) :
    φ (oa >>= f) = φ oa >>= fun a => φ (f a) := by
  rw [φ, liftComp_bind, free]
  exact simulateQ_bind _ _ _

theorem φ_map {α β : Type} (f : α → β) (oa : OracleComp (RoSpec C) α) : φ (f <$> oa) = f <$> φ oa := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, φ_bind]
  simp only [Function.comp_def, φ_pure]

theorem φ_sequenceFin {α : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp (RoSpec C) α),
    φ (Concrete.sequenceFin f) = Concrete.sequenceFin fun i => φ (f i)
  | 0, f => by simp [Concrete.sequenceFin, φ_pure]
  | n + 1, f => by
    simp only [Concrete.sequenceFin, φ_bind, φ_pure]
    congr 1; funext a; rw [φ_sequenceFin]

theorem φ_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) :
    ∀ l : List α, φ (l.mapM f) = l.mapM fun a => φ (f a)
  | [] => by simp [φ_pure]
  | a :: l => by simp only [List.mapM_cons, φ_bind, φ_pure, φ_mapM f l]

theorem referenceJob_φ (F : Point → OracleComp (RoSpec C) Digest) (P : PublicParameter) (job : Job) :
    referenceJob (fun oa => φ (tweakable oa)) (fun x => φ (F x)) P job = φ (referenceJob tweakable F P job) := by
  unfold referenceJob
  rw [φ_bind, ← φ_mapM]
  congr 1; funext values
  split <;> simp [φ_bind, φ_map, φ_pure]

theorem ceremonyOutput_φ (P : PublicParameter) (run : List Job → OracleComp (RoSpec C) (Option (List (List Bit))))
    (top : TopTree) (tree : Tree) :
    ceremonyOutput (fun oa => φ (tweakable oa)) P (fun jobs => φ (run jobs)) top tree =
      φ (ceremonyOutput tweakable P run top tree) := by
  cases tree with
  | top =>
    simp only [ceremonyOutput, φ_bind]
    congr 1; funext r
    rcases r with _ | outputs
    · simp [φ_pure]
    · simp [φ_bind, φ_pure, φ_map]
  | bottom b =>
    simp only [ceremonyOutput, φ_bind]
    congr 1; funext r
    rcases r with _ | outputs
    · simp [φ_pure]
    · simp only [φ_bind]
      congr 1; funext root
      congr 1; funext base
      congr 1; funext g
      rcases g with _ | ⟨randomness, encoding⟩
      · simp [φ_pure]
      · simp only [φ_bind]
        congr 1; funext v
        rcases v with _ | values
        · simp [φ_pure]
        · simp only [φ_bind]
          congr 1; funext path
          congr 1; funext topRoot
          split_ifs <;> simp [φ_pure]

theorem referenceTree_φ (F : Point → OracleComp (RoSpec C) Digest) (P : PublicParameter) (top : TopTree)
    (tree : Tree) :
    referenceTree (fun oa => φ (tweakable oa)) (fun x => φ (F x)) P top tree = φ (referenceTree tweakable F P top tree) := by
  unfold referenceTree
  rw [← ceremonyOutput_φ]
  congr 1; funext jobs
  rw [φ_map, φ_mapM]
  congr 2; funext job
  exact referenceJob_φ F P job

theorem signRound2With_φ (part : Point → OracleComp (RoSpec C) Digest) (P : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    signRound2With (fun oa => φ oa) (fun x => φ (part x)) P J commitment e message parts =
      φ (signRound2With (fun oa => oa) part P J commitment e message parts) := by
  unfold signRound2With
  rw [φ_bind]
  congr 1; funext r
  rcases r with _ | ⟨_, encoding⟩
  · simp [φ_pure]
  · simp only [φ_bind, φ_sequenceFin, φ_pure]
    congr 2
    funext l; split_ifs <;> simp [φ_map, φ_pure]

theorem honestSigning_eq (J : C.Quorum) (e : KeyIndex) (m : Message) :
    honestSigning J e m = free (liftComp prawnsKeyGen _) >>= fun x => φ (honestRo x.1 x.2.1 x.2.2 J e m) := by
  unfold honestSigning dealerKeyGen dealerKeyGenWith
  rw [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨P, seeds, keys⟩
  simp only [honestRo, referenceTree_φ, bind_assoc, φ_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp [φ_pure]
  swap
  · simp [φ_pure]
  simp only [pure_bind, dealtWith, referenceTree_φ, φ_bind, φ_map, bind_map_left]
  refine bind_congr (m := OracleComp (WorldSpec C)) fun r => ?_
  rcases r with _ | (top' | tree)
  · simp [φ_pure]
  · simp [φ_pure]
  simp only [φ_bind, φ_sequenceFin]
  rw [show (fun i => φ (if i ∈ J.1 then eval (keys i) i J (Point.randomizer bottomLayer e) m else pure 0)) =
    fun i => if i ∈ J.1 then φ (eval (keys i) i J (Point.randomizer bottomLayer e) m) else pure 0 from
    funext fun i => by split_ifs <;> simp [φ_pure]]
  refine bind_congr (m := OracleComp (WorldSpec C)) fun parts => ?_
  refine bind_congr (m := OracleComp (WorldSpec C)) fun sc => ?_
  rcases sc with _ | sc
  · simp [φ_pure]
  simp only [φ_bind, φ_sequenceFin, signRound2With_φ, φ_pure]
  refine bind_congr (m := OracleComp (WorldSpec C)) fun chainParts => ?_
  refine bind_congr (m := OracleComp (WorldSpec C)) fun sig => ?_
  rcases sig with _ | sig
  · simp [φ_pure]
  · rw [φ_map]

theorem world_sample_run {α : Type} (pk : ProbComp α) (s : HashCache C) :
    (simulateQ (world prims) (free (liftComp pk (LocalSpec C)))).run.run s =
      (fun a => ((a, (1 : Multiplicative ℕ)), s)) <$> pk := by
  rw [free, ← QueryImpl.simulateQ_compose, world_free_eq]
  have h := QueryImpl.simulateQ_add_liftComp_left
    ((unifFwdImpl (Query C →ₒ HashOutput)).withAddCost fun _ => (0 : ℕ))
    ((roImpl (C := C) prims).withAddCost fun _ => (0 : ℕ)) pk
  erw [h, withAddCost_zero_run]
  simp [unifFwdImpl.simulateQ_run]

theorem fst_runWorld_honest (J : C.Quorum) (e : KeyIndex) (m : Message) :
    Prod.fst <$> runWorld prims (honestSigning J e m) =
      prawnsKeyGen >>= fun x => Prod.fst <$> roRun prims (honestRo x.1 x.2.1 x.2.2 J e m) ∅ := by
  rw [honestSigning_eq, runWorld, simulateQ_bind]
  simp only [WriterT.run_bind, StateT.run'_eq, StateT.run_bind, world_sample_run]
  have hw : ∀ x : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C),
      (WriterT.run (simulateQ (world prims) (φ (honestRo x.1 x.2.1 x.2.2 J e m)))).run ∅ =
        (fun p => ((p.1, (1 : Multiplicative ℕ)), p.2)) <$> roRun prims (honestRo x.1 x.2.1 x.2.2 J e m) ∅ :=
    fun x => world_lift_run prims _ ∅
  simp only [StateT.run_map, bind_map_left, hw, map_bind, Functor.map_map]
  erw [map_bind]
  refine bind_congr (m := ProbComp) fun x => ?_
  exact Functor.map_map _ _ _

/-! ## Every output signature verifies -/

theorem prawnsKeyGen_support (x : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C))
    (hx : x ∈ support (prawnsKeyGen (C := C))) :
    ∃ pairKeys, x.2.2 = dealtKeys x.1 x.2.1 pairKeys := by
  simp only [prawnsKeyGen, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
  obtain ⟨P, -, seeds, -, pairKeys, -, rfl⟩ := hx
  exact ⟨pairKeys, rfl⟩

set_option maxRecDepth 100000 in
theorem honestSigning_verifies (J : C.Quorum) (e : KeyIndex) (m : Message) :
    ∀ r ∈ support (runWorld prims (honestSigning J e m)), r.1 ≠ some false := by
  intro r hr
  have h1 : r.1 ∈ support (Prod.fst <$> runWorld prims (honestSigning J e m)) := by
    rw [support_map]; exact ⟨r, hr, rfl⟩
  rw [fst_runWorld_honest] at h1
  simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at h1
  obtain ⟨x, hx, z, hz, hzr⟩ := h1
  obtain ⟨pairKeys, hkeys⟩ := prawnsKeyGen_support x hx
  obtain ⟨-, hn, hd⟩ := roRun_support prims (honestRo x.1 x.2.1 x.2.2 J e m) ∅ z hz
  have hn' := hn noMpc_empty
  rw [← hzr, hd _ (good_hashOf prims z.2) (agrees_hashOf prims hn'), hkeys]
  exact D_honestRo _ _ _ _ _ _

/-! ## Bytes and codewords -/

theorem bytesLE_injective' {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) : x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem ofNat_inj_of_lt' {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)

theorem sum_digits_eq (B : Nat) (hB : 0 < B) :
    ∀ (k n : Nat), n < B ^ k → ∑ j ∈ range k, (n / B ^ j % B) * B ^ j = n := by
  intro k
  induction k with
  | zero => intro n hn; simp at hn; simp [hn]
  | succ k ih =>
      intro n hn
      rw [Finset.sum_range_succ']
      have hdiv : n / B < B ^ k := by
        rw [Nat.div_lt_iff_lt_mul hB]; rwa [pow_succ] at hn
      have hrest : ∑ j ∈ range k, (n / B ^ (j + 1) % B) * B ^ (j + 1) = B * (n / B) := by
        rw [← ih (n / B) hdiv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm (B ^ j) B,
          ← Nat.div_div_eq_div_mul]
        ring
      rw [hrest]
      simp only [pow_zero, Nat.div_one, mul_one]
      have := Nat.div_add_mod n B
      omega

/-- The value of digit `j` of a word, `0` past `v`. -/
def wordDigit (x : Encoding) (j : Nat) : Nat :=
  if h : j < numChains then (x ⟨j, h⟩).val else 0

theorem wordDigit_lt (x : Encoding) (j : Nat) : wordDigit x j < 4 := by
  unfold wordDigit
  split
  · exact (x _).isLt
  · decide

def packNat (x : Encoding) : Nat := ∑ j ∈ range numChains, wordDigit x j * 4 ^ j

theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 116 := by
  have hlt : ∀ n, ∑ j ∈ range n, wordDigit x j * 4 ^ j < 4 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have h3 : wordDigit x n * 4 ^ n ≤ 3 * 4 ^ n :=
          Nat.mul_le_mul_right _ (by have := wordDigit_lt x n; omega)
        omega
  have := hlt numChains
  simpa [packNat, numChains, show (4 : Nat) ^ 58 = 2 ^ 116 by norm_num] using this

def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, digestBits,
    Nat.mod_eq_of_lt (lt_trans (packNat_lt x) (by norm_num))]

theorem digit_val (d : Digest) (i : Nat) : (Codeword.digit d i).val = d.toNat / 4 ^ i % 4 := by
  simp [Codeword.digit, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow, pow_mul]

theorem encoding_pack (x : Encoding) : Codeword.encoding (pack x) = x := by
  funext i
  apply Fin.ext
  rw [Codeword.encoding, digit_val, toNat_pack, packNat,
    digit_of_sum 4 (by decide) (wordDigit x) (wordDigit_lt x) numChains i.val i.isLt,
    wordDigit, dif_pos i.isLt]

theorem valid_pack {x : Encoding} (hx : Codeword.sum x = targetSum) : Codeword.Valid (pack x) := by
  refine ⟨?_, by rw [encoding_pack]; exact hx⟩
  rw [toNat_pack]
  exact Nat.div_eq_of_lt (by simpa [winternitzBits, numChains] using packNat_lt x)

theorem pack_encoding {d : Digest} (hd : Codeword.Valid d) : pack (Codeword.encoding d) = d := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_pack]
  have hlt : d.toNat < 4 ^ numChains := by
    have h0 := hd.1
    simp only [winternitzBits, numChains] at h0
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h0
    simpa [numChains, show (4 : Nat) ^ 58 = 2 ^ 116 by norm_num] using this
  rw [← sum_digits_eq 4 (by decide) numChains d.toNat hlt, packNat]
  apply Finset.sum_congr rfl
  intro j hj
  rw [wordDigit, dif_pos (Finset.mem_range.mp hj), Codeword.encoding, digit_val]

set_option maxRecDepth 100000 in
theorem card_valid (p : Encoding → Prop) [DecidablePred p] (hp : ∀ x, p x ↔ Codeword.sum x = targetSum) :
    (Finset.univ.filter fun d : Digest => Codeword.Valid d).card = (Finset.univ.filter p).card := by
  apply Finset.card_bij' (fun d _ => Codeword.encoding d) (fun x _ => pack x)
  · intro d hd; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hp _).mpr (Finset.mem_filter.mp hd).2.2⟩
  · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid_pack ((hp x).mp (Finset.mem_filter.mp hx).2)⟩
  · intro d hd; exact pack_encoding (Finset.mem_filter.mp hd).2
  · intro x _; exact encoding_pack x

/-! ## The randomizer search fails rarely -/

theorem card_valid_trunc :
    (univ.filter fun u : HashOutput => Codeword.Valid (truncateHash u)).card =
      2 ^ 128 * (univ.filter fun d : Digest => Codeword.Valid d).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  have e : {u : HashOutput // Codeword.Valid (truncateHash u)} ≃ BitVec 128 × {d : Digest // Codeword.Valid d} :=
    { toFun := fun u => (u.1.extractLsb' 128 128, ⟨truncateHash u.1, u.2⟩)
      invFun := fun p => ⟨(p.1 ++ p.2.1 : BitVec (128 + 128)), by
        have h : (p.1 ++ p.2.1 : BitVec (128 + 128)).extractLsb' 0 128 = p.2.1 :=
          BitVec.extractLsb'_append_eq_right
        exact (congrArg Codeword.Valid h).mpr p.2.2⟩
      left_inv := fun u => Subtype.ext (BitVec.extractLsb'_append_extractLsb' (w := 128) (len := 128) (x := u.1))
      right_inv := fun p => Prod.ext (BitVec.extractLsb'_append_eq_left (w := 128) (w' := 128))
        (Subtype.ext (BitVec.extractLsb'_append_eq_right (w := 128) (w' := 128))) }
  rw [Fintype.card_congr e, Fintype.card_prod]
  simp

/-- The probability that a uniform digest is a codeword. -/
def codewordP : ℝ≥0∞ := ((univ.filter fun d : Digest => Codeword.Valid d).card : ℝ≥0∞) / 2 ^ 128

theorem probEvent_valid_trunc :
    Pr[fun u : HashOutput => Codeword.Valid (truncateHash u) | $ᵗ HashOutput] = codewordP := by
  rw [probEvent_uniformSample, card_valid_trunc, codewordP]
  have hcard : Fintype.card HashOutput = 2 ^ 128 * 2 ^ 128 := by simp [hashOutputBits]
  rw [hcard]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

theorem codewordP_le_one : codewordP ≤ 1 := by
  rw [← probEvent_valid_trunc]; exact probEvent_le_one

theorem probEvent_invalid_trunc :
    Pr[fun u : HashOutput => ¬Codeword.Valid (truncateHash u) | $ᵗ HashOutput] = 1 - codewordP := by
  have h := probEvent_compl ($ᵗ HashOutput) fun u : HashOutput => Codeword.Valid (truncateHash u)
  rw [probEvent_valid_trunc, probFailure_eq_zero, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top ((add_comm _ _).trans h)

theorem roRun_bind {α β : Type} (oa : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β)
    (s : HashCache C) : roRun prims (oa >>= f) s = roRun prims oa s >>= fun p => roRun prims (f p.1) p.2 := by
  simp [roRun, simulateQ_bind, StateT.run_bind]

theorem roRun_pure {α : Type} (a : α) (s : HashCache C) : roRun prims (pure a : OracleComp (RoSpec C) α) s =
    pure (a, s) := by
  simp [roRun]

theorem roRun_fresh (x : HashInput) (hx : ¬MpcInput x) (s : HashCache C) (hs : s (.hash x) = none) :
    roRun prims (hashQuery (.hash x)) s = (fun u => (u, s.cacheQuery (.hash x) u)) <$> ($ᵗ HashOutput) := by
  have h1 : roRun prims (hashQuery (C := C) (.hash x)) s = (roImpl prims (Sum.inl (Query.hash x))).run s := by
    unfold roRun hashQuery
    exact congrArg (fun y => StateT.run y s) (simulateQ_spec_query (roImpl prims) (Sum.inl (Query.hash x)))
  rw [h1]
  change (hashAnswer prims (.hash x)).run s = _
  dsimp only [hashAnswer]
  rw [if_neg hx, OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs]
  rfl

/-- The `t`-th trial input of a randomizer search. -/
abbrev trialInput (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput) (base : Randomness)
    (t : ℕ) : HashInput :=
  tweakableHashInput P (.message lay key) (message ++ bytesLE 16 (base + BitVec.ofNat digestBits t))

theorem trialInput_inj {P : PublicParameter} {lay : Layer} {key : KeyIndex} {message : HashInput}
    {base : Randomness} {t t' : ℕ} (ht : t < 2 ^ 128) (ht' : t' < 2 ^ 128)
    (h : trialInput P lay key message base t = trialInput P lay key message base t') : t = t' := by
  unfold trialInput tweakableHashInput at h
  have h1 := List.append_cancel_left (List.append_cancel_left h)
  have h2 := bytesLE_injective' (n := 16) h1
  exact ofNat_inj_of_lt' ht ht' ((BitVec.add_right_inj base).mp h2)

theorem probEvent_bind_le_mul_of_cases {α β : Type} {mx : ProbComp α} {f : α → ProbComp β} {P : β → Prop}
    {Q : α → Prop} {ε : ℝ≥0∞} (h1 : ∀ x ∈ support mx, Q x → Pr[P | f x] ≤ ε)
    (h0 : ∀ x ∈ support mx, ¬Q x → Pr[P | f x] = 0) : Pr[P | mx >>= f] ≤ Pr[Q | mx] * ε := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · by_cases hq : Q x
    · rw [if_pos hq]; exact mul_le_mul' le_rfl (h1 x hx hq)
    · rw [if_neg hq, h0 x hx hq]; simp
  · simp [probOutput_eq_zero_of_not_mem_support hx]

set_option maxRecDepth 100000 in
theorem grind_fail (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput) (base : Randomness) :
    ∀ attempts trial (s : HashCache C), trial + attempts ≤ 2 ^ 128 →
      (∀ t, trial ≤ t → t < trial + attempts →
        ¬MpcInput (trialInput P lay key message base t) ∧ s (.hash (trialInput P lay key message base t)) = none) →
      Pr[fun z => z.1 = none | roRun prims (tweakable (grind P lay key message base attempts trial)) s] ≤
        (1 - codewordP) ^ attempts
  | 0, trial, s, _, _ => by rw [pow_zero]; exact probEvent_le_one
  | attempts + 1, trial, s, hlen, hfresh => by
    obtain ⟨hmpc, hs⟩ := hfresh trial le_rfl (by omega)
    rw [grind, tweakable_bind, roRun_bind]
    unfold Concrete.messageDigest Concrete.tweakableHash
    rw [tweakable_bind, tweakable_oracleHash, roRun_bind, roRun_fresh prims _ hmpc s hs]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind, tweakable_pure, roRun_pure]
    rw [pow_succ']
    conv_rhs => arg 1; rw [← probEvent_invalid_trunc]
    refine probEvent_bind_le_mul_of_cases (fun u _ hu => ?_) (fun u _ hu => ?_)
    · simp only [Codeword.decode, if_neg hu]
      refine grind_fail P lay key message base attempts (trial + 1) _ (by omega) fun t ht1 ht2 => ?_
      obtain ⟨hm, hn⟩ := hfresh t (by omega) (by omega)
      refine ⟨hm, ?_⟩
      have hne : trialInput P lay key message base t ≠ trialInput P lay key message base trial :=
        fun heq => by have := trialInput_inj (by omega) (by omega) heq; omega
      rw [QueryCache.cacheQuery_of_ne _ _ (fun heq => hne (Query.hash.inj heq))]
      exact hn
    · simp only [Codeword.decode, if_pos (not_not.mp hu), tweakable_pure, roRun_pure]
      simp

theorem byte23 (P : PublicParameter) (f : TweakFields) (rest : HashInput) :
    (bytesLE 16 P ++ fieldBytes f ++ rest)[23]? = (bytesLE 1 (f.step ++ f.tag))[0]? := by
  simp [fieldBytes, List.getElem?_append, bytesLE]

theorem byte23_msg (P : PublicParameter) (lay : Layer) (key : KeyIndex) (payload : HashInput) :
    (tweakableHashInput P (.message lay key) payload)[23]? = some 12 := by
  rw [tweakableHashInput, tweakBytes, byte23]
  simp [hashDomainFields, tweakFields]
  decide

theorem byte23_leaf (P : PublicParameter) (lay : Layer) (key : KeyIndex) (payload : HashInput) :
    (tweakableHashInput P (.leaf lay key) payload)[23]? = some 2 := by
  rw [tweakableHashInput, tweakBytes, byte23]
  simp [hashDomainFields, tweakFields]
  decide

theorem byte23_node (P : PublicParameter) (lay : Layer) (level idx : ℕ) (payload : HashInput) :
    (tweakableHashInput P (.node lay level idx) payload)[23]? = some 3 := by
  rw [tweakableHashInput, tweakBytes, byte23]
  simp [hashDomainFields, tweakFields]
  decide

theorem byte23_chain (P : PublicParameter) (lay : Layer) (key : KeyIndex) (step : ChainStep) (payload : HashInput) :
    (tweakableHashInput P (.chain lay key step) payload)[23]? ≠ some 12 := by
  rw [tweakableHashInput, tweakBytes, byte23]
  simp only [hashDomainFields, tweakFields]
  revert step
  decide

theorem byte23_commitment (P : PublicParameter) (e : KeyIndex) (ρ : Digest) :
    (commitmentInput P e ρ)[23]? = some 39 := by
  rw [commitmentInput, List.append_assoc, byte23]
  simp only [tweakFields]
  decide

theorem byte23_randomizer (P : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest) (message : HashInput) :
    (randomizerInput P lay e ρ message)[23]? = some 7 := by
  rw [randomizerInput, List.append_assoc, byte23]
  simp only [tweakFields]
  decide

/-- A message digest input of `Th`. -/
def IsMsg (x : HashInput) : Prop := x[23]? = some 12

/-- A message digest input of `Th` on a 32-byte message. -/
def IsMsg80 (x : HashInput) : Prop := x[23]? = some 12 ∧ x.length = 80

theorem not_isMsg_of_mpc {x : HashInput} (hx : MpcInput x) : ¬IsMsg x := by
  rcases hx with ⟨P, lay, key, step, l, v, rfl⟩ | ⟨P, e, ρ, rfl⟩
  · exact byte23_chain P lay key step _
  · unfold IsMsg; rw [byte23_commitment]; decide

theorem length_tweakableHashInput (P : PublicParameter) (dom : HashDomain) (payload : HashInput) :
    (tweakableHashInput P dom payload).length = 32 + payload.length := by
  simp [tweakableHashInput, tweakBytes, fieldBytes, bytesLE]
  omega

/-! ## Fresh message digests -/

/-- No input that `B` selects is in the cache. -/
def NoB (B : HashInput → Prop) (s : HashCache C) : Prop := ∀ x, B x → s (.hash x) = none

/-- A computation keeps every input that `B` selects out of the cache. -/
def Pres (B : HashInput → Prop) {α : Type} (oa : OracleComp (RoSpec C) α) : Prop :=
  ∀ s z, NoB B s → z ∈ support (roRun prims oa s) → NoB B z.2

theorem roRun_hashQuery (q : Query C) (s : HashCache C) :
    roRun prims (hashQuery q) s = (hashAnswer prims q).run s := by
  unfold roRun hashQuery
  exact congrArg (fun y => StateT.run y s) (simulateQ_spec_query (roImpl prims) (Sum.inl q))

theorem Pres_hashQuery (B : HashInput → Prop) (q : Query C) (hq : ∀ x, q = .hash x → B x → MpcInput x) :
    Pres prims B (hashQuery q) := by
  intro s z hs hz
  rw [roRun_hashQuery] at hz
  have hro : z ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s) → (∀ x, MpcInput x → q ≠ .hash x) →
      NoB B z.2 := by
    intro hz hq'
    obtain ⟨-, -, hother⟩ := randomOracle_support q s z hz
    intro x hx
    rw [hother _ (fun heq => hq' x (hq x heq.symm hx) heq.symm)]
    exact hs x hx
  cases q with
  | hash input =>
    dsimp only [hashAnswer] at hz
    split_ifs at hz with hmx
    · simp at hz
      subst hz
      exact hs
    · exact hro hz fun x hmx' heq => hmx (by cases heq; exact hmx')
  | _ => exact hro hz fun x _ heq => by cases heq

theorem Pres_pure (B : HashInput → Prop) {α : Type} (a : α) : Pres prims B (pure a : OracleComp (RoSpec C) α) := by
  intro s z hs hz
  rw [roRun_pure] at hz
  simp at hz
  subst hz
  exact hs

theorem Pres_bind (B : HashInput → Prop) {α β : Type} {oa : OracleComp (RoSpec C) α}
    {f : α → OracleComp (RoSpec C) β} (ha : Pres prims B oa) (hf : ∀ a, Pres prims B (f a)) :
    Pres prims B (oa >>= f) := by
  intro s z hs hz
  rw [roRun_bind, support_bind] at hz
  obtain ⟨p, hp, hz⟩ := Set.mem_iUnion₂.mp hz
  exact hf p.1 p.2 z (ha s p hs hp) hz

theorem Pres_map (B : HashInput → Prop) {α β : Type} {oa : OracleComp (RoSpec C) α} (f : α → β)
    (ha : Pres prims B oa) : Pres prims B (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact Pres_bind prims B ha fun _ => Pres_pure prims B _

theorem Pres_mapM (B : HashInput → Prop) {α β : Type} (f : α → OracleComp (RoSpec C) β)
    (hf : ∀ a, Pres prims B (f a)) : ∀ l : List α, Pres prims B (l.mapM f)
  | [] => by simpa using Pres_pure prims B ([] : List β)
  | a :: l => by
    rw [List.mapM_cons]
    exact Pres_bind prims B (hf a) fun _ => Pres_bind prims B (Pres_mapM B f hf l) fun _ => Pres_pure prims B _

theorem Pres_sequenceFin (B : HashInput → Prop) {α : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp (RoSpec C) α),
    (∀ i, Pres prims B (f i)) → Pres prims B (Concrete.sequenceFin f)
  | 0, f, _ => by rw [Concrete.sequenceFin]; exact Pres_pure prims B _
  | n + 1, f, hf => by
    rw [Concrete.sequenceFin]
    exact Pres_bind prims B (hf 0) fun _ =>
      Pres_bind prims B (Pres_sequenceFin B _ fun i => hf i.succ) fun _ => Pres_pure prims B _

theorem Pres_ite (B : HashInput → Prop) {α : Type} (c : Prop) [Decidable c] {a b : OracleComp (RoSpec C) α}
    (ha : Pres prims B a) (hb : Pres prims B b) : Pres prims B (if c then a else b) := by
  split_ifs
  · exact ha
  · exact hb

theorem Pres_oracleHash (B : HashInput → Prop) (x : HashInput) (hx : B x → MpcInput x) :
    Pres prims B (tweakable (C := C) (Concrete.oracleHash x)) := by
  rw [tweakable_oracleHash]
  exact Pres_hashQuery prims B _ fun y hy hb => by cases hy; exact hx hb

theorem Pres_tweakableHash (B : HashInput → Prop) (P : PublicParameter) (dom : HashDomain) (payload : HashInput)
    (hx : B (tweakableHashInput P dom payload) → MpcInput (tweakableHashInput P dom payload)) :
    Pres prims B (tweakable (C := C) (Concrete.tweakableHash P dom payload)) := by
  unfold Concrete.tweakableHash
  rw [tweakable_bind]
  exact Pres_bind prims B (Pres_oracleHash prims B _ hx) fun _ => by
    rw [tweakable_pure]; exact Pres_pure prims B _

theorem Pres_chainWalk (B : HashInput → Prop) (P : PublicParameter) (lay : Layer) (key : KeyIndex) (l : ChainIndex)
    (s : ℕ) : ∀ n v, Pres prims B (tweakable (C := C) (Concrete.chainWalk P lay key l s n v))
  | 0, v => by rw [Concrete.chainWalk, tweakable_pure]; exact Pres_pure prims B _
  | n + 1, v => by
    rw [Concrete.chainWalk, tweakable_bind]
    refine Pres_bind prims B (Pres_chainWalk B P lay key l s n v) fun w => ?_
    split
    · exact Pres_tweakableHash prims B _ _ _ fun _ => Or.inl ⟨_, _, _, _, _, _, rfl⟩
    · rw [tweakable_pure]; exact Pres_pure prims B _

section Msg

variable (B : HashInput → Prop) (hB : ∀ x, B x → IsMsg x)
include hB

theorem Pres_merkleNode (P : PublicParameter) (lay : Layer) (f : KeyIndex → ChainIndex → Digest) :
    ∀ level idx, Pres prims B (tweakable (C := C) (merkleNode P lay f level idx))
  | 0, idx => by
    rw [merkleNode]
    exact Pres_tweakableHash prims B _ _ _ fun h => absurd (byte23_leaf _ _ _ _) (by
      rw [hB _ h]; decide)
  | level + 1, idx => by
    rw [merkleNode, tweakable_bind]
    refine Pres_bind prims B (Pres_merkleNode P lay f level _) fun _ => ?_
    rw [tweakable_bind]
    refine Pres_bind prims B (Pres_merkleNode P lay f level _) fun _ => ?_
    exact Pres_tweakableHash prims B _ _ _ fun h => absurd (byte23_node _ _ _ _ _) (by
      rw [hB _ h]; decide)

theorem Pres_merklePath (P : PublicParameter) (lay : Layer) (f : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    Pres prims B (tweakable (C := C) (merklePath P lay f key)) := by
  rw [merklePath, tweakable_sequenceFin]
  exact Pres_sequenceFin prims B _ fun _ => Pres_merkleNode prims B hB _ _ _ _ _

theorem Pres_treeFold (P : PublicParameter) (lay : Layer) (key : KeyIndex) (path : Fin layerHeight → Digest) :
    ∀ n v, Pres prims B (tweakable (C := C) (Concrete.treeFold P lay key path n v))
  | 0, v => by rw [Concrete.treeFold, tweakable_pure]; exact Pres_pure prims B _
  | n + 1, v => by
    rw [Concrete.treeFold, tweakable_bind]
    refine Pres_bind prims B (Pres_treeFold P lay key path n v) fun _ => ?_
    dsimp only
    by_cases hb : key.val.testBit n = true
    · rw [if_pos hb]
      exact Pres_tweakableHash prims B _ _ _ fun h => absurd (byte23_node _ _ _ _ _) (by rw [hB _ h]; decide)
    · rw [if_neg hb]
      exact Pres_tweakableHash prims B _ _ _ fun h => absurd (byte23_node _ _ _ _ _) (by rw [hB _ h]; decide)

end Msg

theorem Pres_query_ne_hash (B : HashInput → Prop) (q : Query C) (hq : ∀ x, q ≠ .hash x) :
    Pres prims B (hashQuery q) :=
  Pres_hashQuery prims B q fun x h => absurd h (hq x)

theorem Pres_prfValue (B : HashInput → Prop) (seeds : C.Term → HashOutput) (x : Point) :
    Pres prims B (prfValue seeds x) := by
  unfold prfValue
  refine Pres_bind prims B (Pres_mapM prims B _ (fun T => ?_) _) fun _ => Pres_pure prims B _
  exact Pres_map prims B _ (Pres_query_ne_hash prims B _ fun _ h => by cases h)

theorem Pres_eval (B : HashInput → Prop) (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (m : Message) :
    Pres prims B (eval keys i J x m) := by
  unfold eval
  refine Pres_bind prims B (Pres_mapM prims B _ (fun T => ?_) _) fun _ =>
    Pres_bind prims B (Pres_mapM prims B _ (fun j => ?_) _) fun _ => Pres_pure prims B _
  · exact Pres_map prims B _ (Pres_query_ne_hash prims B _ fun _ h => by cases h)
  · exact Pres_map prims B _ (Pres_query_ne_hash prims B _ fun _ h => by cases h)

theorem isMsg_of_isMsg80 {x : HashInput} (hx : IsMsg80 x) : IsMsg x := hx.1

theorem Pres_referenceJob (B : HashInput → Prop) (seeds : C.Term → HashOutput) (P : PublicParameter) (job : Job) :
    Pres prims B (referenceJob tweakable (prfValue seeds) P job) := by
  obtain ⟨kind, points⟩ := job
  unfold referenceJob
  refine Pres_bind prims B (Pres_mapM prims B _ (fun x => Pres_prfValue prims B seeds x) _) fun values => ?_
  cases kind
  · exact Pres_map prims B _ (Pres_chainWalk prims B _ _ _ _ _ _ _)
  · exact Pres_bind prims B (Pres_chainWalk prims B _ _ _ _ _ _ _) fun _ =>
      Pres_bind prims B (Pres_chainWalk prims B _ _ _ _ _ _ _) fun _ =>
      Pres_bind prims B (Pres_chainWalk prims B _ _ _ _ _ _ _) fun _ => Pres_pure prims B _
  · exact Pres_map prims B _ (Pres_chainWalk prims B _ _ _ _ _ _ _)
  · exact Pres_map prims B _ (Pres_oracleHash prims B _ fun _ => Or.inr ⟨_, _, _, rfl⟩)
  · exact Pres_pure prims B _

theorem Pres_refTop (B : HashInput → Prop) (hB : ∀ x, B x → IsMsg x) (seeds : C.Term → HashOutput)
    (P : PublicParameter) (top : TopTree) :
    Pres prims B (referenceTree tweakable (prfValue seeds) P top .top) := by
  unfold referenceTree ceremonyOutput
  refine Pres_bind prims B (Pres_map prims B _ (Pres_mapM prims B _ (Pres_referenceJob prims B seeds P) _))
    fun o => ?_
  rcases o with _ | outputs
  · exact Pres_pure prims B _
  · exact Pres_bind prims B (Pres_merkleNode prims B hB _ _ _ _ _) fun _ => Pres_pure prims B _

theorem Pres_messageDigest80 (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (hm : message.length = 16) (r : Randomness) :
    Pres prims IsMsg80 (tweakable (C := C) (Concrete.messageDigest P lay key message r)) := by
  unfold Concrete.messageDigest
  refine Pres_tweakableHash prims _ _ _ _ fun h => absurd h.2 ?_
  rw [length_tweakableHashInput, List.length_append, hm]
  simp [bytesLE]

theorem Pres_grind80 (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (hm : message.length = 16) (base : Randomness) :
    ∀ attempts trial, Pres prims IsMsg80 (tweakable (C := C) (grind P lay key message base attempts trial))
  | 0, trial => by rw [grind, tweakable_pure]; exact Pres_pure prims _ _
  | attempts + 1, trial => by
    rw [grind, tweakable_bind]
    refine Pres_bind prims _ (Pres_messageDigest80 prims P lay key message hm _) fun d => ?_
    split
    · rw [tweakable_pure]; exact Pres_pure prims _ _
    · exact Pres_grind80 P lay key message hm base attempts (trial + 1)

theorem Pres_layerRoot80 (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (hm : message.length = 16) (part : LayerSignature) :
    Pres prims IsMsg80 (tweakable (C := C) (Concrete.layerRoot P lay key message part)) := by
  unfold Concrete.layerRoot Concrete.otsLeaf
  rw [tweakable_bind, tweakable_bind]
  refine Pres_bind prims _ (Pres_bind prims _ (Pres_messageDigest80 prims P lay key message hm _) fun d => ?_)
    fun o => ?_
  · split
    · rw [tweakable_bind, tweakable_sequenceFin]
      refine Pres_bind prims _ (Pres_sequenceFin prims _ _ fun l => Pres_chainWalk prims _ _ _ _ _ _ _ _)
        fun ends => ?_
      rw [tweakable_bind]
      refine Pres_bind prims _ (Pres_tweakableHash prims _ _ _ _ fun h =>
        absurd (byte23_leaf P lay key (Concrete.leafPayload ends)) (by rw [h.1]; decide)) fun _ => ?_
      rw [tweakable_pure]; exact Pres_pure prims _ _
    · rw [tweakable_pure]; exact Pres_pure prims _ _
  · rcases o with _ | leaf
    · rw [tweakable_pure]; exact Pres_pure prims _ _
    · rw [tweakable_bind]
      exact Pres_bind prims _ (Pres_treeFold prims _ (fun _ h => h.1) _ _ _ _ _ _) fun _ => by
        rw [tweakable_pure]; exact Pres_pure prims _ _

/-! ## The honest quorum fails rarely -/

theorem pr_bind_le {α β : Type} {mx : ProbComp α} {my : α → ProbComp β} {q : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[q | my x] ≤ ε) : Pr[q | mx >>= my] ≤ ε :=
  probEvent_bind_le_of_forall_le h

theorem pr_bind_le_add {α β : Type} {mx : ProbComp α} {my : α → ProbComp β} {q : β → Prop} {p : α → Prop}
    {ε : ℝ≥0∞} (h : ∀ x ∈ support mx, ¬p x → Pr[q | my x] ≤ ε) : Pr[q | mx >>= my] ≤ Pr[p | mx] + ε :=
  probEvent_bind_le_probEvent_add h

theorem exists_good (s : HashCache C) (hs : NoMpc s) : ∃ h, Good prims h ∧ Agrees h s :=
  ⟨hashOf prims s, good_hashOf prims s, agrees_hashOf prims hs⟩

theorem noB_empty (B : HashInput → Prop) : NoB B (∅ : HashCache C) := fun _ _ => rfl

/-- The facts about a top tree under `h`. -/
def TopFacts (prims : Primitives) (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (P : PublicParameter)
    (top : TopTree) : Prop :=
  (∀ b l, top.chainEnd (topKey b) l = E prims h (Concrete.chainWalk P topLayer (topKey b) l 0 3
    (D prims h (prfValue seeds (.chain topLayer (topKey b) l (digit 0)))))) ∧
  top.root = E prims h (merkleNode P topLayer top.chainEnd layerHeight 0)

/-- The first run of bottom tree `b` after its outputs, as `ceremonyOutput` gives it. -/
def referenceBottomRest (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) : OracleComp (RoSpec C) (Option TreeOutput) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
    let bits := outputs.getD (keys.idxOf (e, l)) []
    (digestAt bits 0, digestAt bits 1, digestAt bits 2)
  let commitment := fun (e : KeyIndex) => digestAt (outputs.getD (keys.length + e.val % 2 ^ layerHeight) []) 0
  let ρ := digestAt (outputs.getD (keys.length + 2 ^ layerHeight) []) 0
  let root ← tweakable (merkleNode P bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val)
  let message := bytesLE 16 root
  let base ← tweakable (truncateHash <$> Concrete.oracleHash (randomizerInput P topLayer (topKey b) ρ message))
  let some (randomness, encoding) ← tweakable (grind P topLayer (topKey b) message base
      randomizerAttemptLimit 0) | pure none
  let some values ← some <$> (signJobs b encoding).mapM (referenceJob tweakable (prfValue seeds) P) | pure none
  let path ← tweakable (merklePath P topLayer top.chainEnd (topKey b))
  let signature : LayerSignature := ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← tweakable (Concrete.layerRoot P topLayer (topKey b) message signature)
  if topRoot ≠ some top.root then pure none else
  pure (some (.bottom ⟨cpk, commitment, root, signature⟩))

theorem refBottom_eq (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    referenceTree tweakable (prfValue seeds) P top (.bottom b) =
      (bottomJobs b).mapM (referenceJob tweakable (prfValue seeds) P) >>= referenceBottomRest seeds P top b := by
  unfold referenceTree ceremonyOutput referenceBottomRest
  dsimp only
  rw [bind_map_left]
  exact bind_congr fun a => rfl

/-- One step of a run, with what the step tells about its result and its cache. -/
theorem step {α β : Type} (oa : OracleComp (RoSpec C) α) (k : α → OracleComp (RoSpec C) β) (P : β × HashCache C → Prop)
    (s : HashCache C) (ε : ℝ≥0∞) (hn : NoMpc s)
    (H : ∀ a s', s ≤ s' → NoMpc s' → (∀ h, Good prims h → Agrees h s' → a = D prims h oa) →
      (∀ B, Pres prims B oa → NoB B s → NoB B s') → Pr[P | roRun prims (k a) s'] ≤ ε) :
    Pr[P | roRun prims (oa >>= k) s] ≤ ε := by
  rw [roRun_bind]
  refine pr_bind_le fun p hp => ?_
  obtain ⟨hle, hn', hd⟩ := roRun_support prims oa s p hp
  exact H p.1 p.2 hle (hn' hn) hd fun B hB hs => hB s p hs hp

/-- One step of a run that charges the runs whose result satisfies `Q`. -/
theorem step_add {α β : Type} (oa : OracleComp (RoSpec C) α) (k : α → OracleComp (RoSpec C) β)
    (P : β × HashCache C → Prop) (Q : α → Prop) (s : HashCache C) (δ : ℝ≥0∞) (hn : NoMpc s)
    (H : ∀ a s', ¬Q a → s ≤ s' → NoMpc s' → (∀ h, Good prims h → Agrees h s' → a = D prims h oa) →
      (∀ B, Pres prims B oa → NoB B s → NoB B s') → Pr[P | roRun prims (k a) s'] ≤ δ) :
    Pr[P | roRun prims (oa >>= k) s] ≤ Pr[fun z => Q z.1 | roRun prims oa s] + δ := by
  rw [roRun_bind]
  refine pr_bind_le_add fun p hp hq => ?_
  obtain ⟨hle, hn', hd⟩ := roRun_support prims oa s p hp
  exact H p.1 p.2 hq hle (hn' hn) hd fun B hB hs => hB s p hs hp

theorem bottomRest_fail (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (s : HashCache C) (hn : NoMpc s) (hm : NoB IsMsg s)
    (htop : ∀ h, Good prims h → Agrees h s → TopFacts prims h seeds P top) :
    Pr[fun z => z.1 = none | roRun prims (referenceBottomRest seeds P top b outputs) s] ≤
      (1 - codewordP) ^ randomizerAttemptLimit := by
  unfold referenceBottomRest
  dsimp only
  refine step prims _ _ _ _ _ hn fun root s3 hle3 hn3 hd3 hp3 => ?_
  have hm3 := hp3 IsMsg (Pres_merkleNode prims IsMsg (fun _ h => h) _ _ _ _ _) hm
  refine step prims _ _ _ _ _ hn3 fun base s4 hle4 hn4 hd4 hp4 => ?_
  have hm4 := hp4 IsMsg (Pres_map prims IsMsg _ (Pres_oracleHash prims IsMsg _ fun h => absurd h (by
    unfold IsMsg; rw [byte23_randomizer]; decide))) hm3
  refine (step_add prims _ _ _ (fun g => g = none) _ 0 hn4 fun g s5 hg5 hle5 hn5 hd5 hp5 => ?_).trans
    (by rw [add_zero]; exact grind_fail prims _ _ _ _ _ _ 0 _ (by simp [randomizerAttemptLimit]) fun t _ _ =>
      ⟨fun hmpc => not_isMsg_of_mpc hmpc (byte23_msg _ _ _ _), hm4 _ (byte23_msg _ _ _ _)⟩)
  rcases g with _ | ⟨r1, e1⟩
  · exact absurd rfl hg5
  dsimp only
  refine step prims _ _ _ _ _ hn5 fun v s6 hle6 hn6 hd6 hp6 => ?_
  obtain ⟨h6, hg6, ha6⟩ := exists_good prims s6 hn6
  have hv : v = some ((signJobs b e1).map fun job => D prims h6 (referenceJob tweakable (prfValue seeds) P job)) := by
    rw [hd6 h6 hg6 ha6, D_map, D_mapM]
  obtain ⟨vals, rfl⟩ : ∃ vals, v = some vals := ⟨_, hv⟩
  have hvals : ∀ h, Good prims h → Agrees h s6 →
      vals = (signJobs b e1).map fun job => D prims h (referenceJob tweakable (prfValue seeds) P job) := by
    intro h hg ha
    have := hd6 h hg ha
    rw [D_map, D_mapM] at this
    exact Option.some.inj this
  dsimp only
  refine step prims _ _ _ _ _ hn6 fun path s7 hle7 hn7 hd7 hp7 => ?_
  refine step prims _ _ _ _ _ hn7 fun topRoot s8 hle8 hn8 hd8 hp8 => ?_
  obtain ⟨h, hg, ha⟩ := exists_good prims s8 hn8
  have ha7 := ha.mono hle8
  have ha6 := ha7.mono hle7
  have ha5 := ha6.mono hle6
  have ha4 := ha5.mono hle5
  have ha3 := ha4.mono hle4
  obtain ⟨hchain, hroot⟩ := htop h hg (((ha3.mono hle3)))
  have hT := topRoot_eq (prims := prims) (h := h) seeds P top hchain hroot b (bytesLE 16 root) r1 e1
    (E_grind_spec _ _ _ _ _ _ _ _ _ (hd5 h hg ha5).symm)
  have htr : topRoot = some top.root := by
    rw [hd8 h hg ha, hd7 h hg ha7, hvals h hg ha6]
    exact hT
  rw [if_neg (by rw [htr]; exact not_not.mpr rfl), roRun_pure]
  simp

theorem refBottom_fail (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (s : HashCache C) (hn : NoMpc s) (hm : NoB IsMsg s)
    (htop : ∀ h, Good prims h → Agrees h s → TopFacts prims h seeds P top) :
    Pr[fun z => z.1 = none | roRun prims (referenceTree tweakable (prfValue seeds) P top (.bottom b)) s] ≤
      (1 - codewordP) ^ randomizerAttemptLimit := by
  rw [refBottom_eq]
  refine step prims _ _ _ _ _ hn fun outputs s2 hle2 hn2 _ hp2 => ?_
  exact bottomRest_fail prims seeds P top b outputs s2 hn2
    (hp2 IsMsg (Pres_mapM prims IsMsg _ (Pres_referenceJob prims IsMsg seeds P) _) hm)
    fun h hg ha => htop h hg (ha.mono hle2)

theorem length_trial80 (P : PublicParameter) (lay : Layer) (key : KeyIndex) (m : Message) (base : Randomness) (t : ℕ) :
    (trialInput P lay key (bytesLE 32 m) base t).length = 80 := by
  rw [trialInput, length_tweakableHashInput]
  simp [bytesLE]

theorem signCodeword_fail (P : PublicParameter) (commitment : Digest) (e : KeyIndex) (m : Message) (ρ : Digest)
    (s : HashCache C) (hn : NoMpc s) (hm : NoB IsMsg80 s)
    (hc : ∀ h, Good prims h → Agrees h s → commitment = truncateHash (h (.hash (commitmentInput P e ρ)))) :
    Pr[fun z => z.1 = none | roRun prims (signCodeword P commitment e m ρ) s] ≤
      (1 - codewordP) ^ randomizerAttemptLimit := by
  unfold signCodeword
  rw [tweakable_bind]
  refine step prims _ _ _ _ _ hn fun o s1 hle1 hn1 hd1 hp1 => ?_
  have hm1 := hp1 IsMsg80 (Pres_oracleHash prims IsMsg80 _ fun _ => Or.inr ⟨_, _, _, rfl⟩) hm
  obtain ⟨h, hg, ha⟩ := exists_good prims s1 hn1
  have ho : truncateHash o = commitment := by
    rw [hd1 h hg ha, hc h hg (ha.mono hle1), tweakable_oracleHash, D_hashQuery]
  dsimp only
  rw [if_neg (by rw [ho]; exact not_not.mpr rfl), tweakable_bind]
  refine step prims _ _ _ _ _ hn1 fun base s2 hle2 hn2 hd2 hp2 => ?_
  have hm2 := hp2 IsMsg80 (Pres_oracleHash prims IsMsg80 _ fun h => absurd h.1 (by
    rw [byte23_randomizer]; decide)) hm1
  exact grind_fail prims _ _ _ _ _ _ 0 _ (by simp [randomizerAttemptLimit]) fun t _ _ =>
    ⟨fun hmpc => not_isMsg_of_mpc hmpc (byte23_msg _ _ _ _), hm2 _ ⟨byte23_msg _ _ _ _, length_trial80 _ _ _ _ _ _⟩⟩

theorem length_bytesLE (n : ℕ) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by simp [bytesLE]

theorem Pres_refBottom80 (seeds : C.Term → HashOutput) (P : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) :
    Pres prims IsMsg80 (referenceTree tweakable (prfValue seeds) P top (.bottom b)) := by
  rw [refBottom_eq]
  refine Pres_bind prims _ (Pres_mapM prims _ _ (Pres_referenceJob prims _ seeds P) _) fun outputs => ?_
  unfold referenceBottomRest
  dsimp only
  refine Pres_bind prims _ (Pres_merkleNode prims _ (fun _ h => h.1) _ _ _ _ _) fun root => ?_
  refine Pres_bind prims _ (Pres_map prims _ _ (Pres_oracleHash prims _ _ fun h => absurd h.1 (by
    rw [byte23_randomizer]; decide))) fun base => ?_
  refine Pres_bind prims _ (Pres_grind80 prims _ _ _ _ (length_bytesLE 16 root) _ _ _) fun g => ?_
  rcases g with _ | ⟨r1, e1⟩
  · exact Pres_pure prims _ _
  refine Pres_bind prims _ (Pres_map prims _ _ (Pres_mapM prims _ _ (Pres_referenceJob prims _ seeds P) _))
    fun v => ?_
  rcases v with _ | vals
  · exact Pres_pure prims _ _
  refine Pres_bind prims _ (Pres_merklePath prims _ (fun _ h => h.1) _ _ _ _) fun path => ?_
  refine Pres_bind prims _ (Pres_layerRoot80 prims _ _ _ _ (length_bytesLE 16 root) _) fun topRoot => ?_
  exact Pres_ite prims _ _ (Pres_pure prims _ _) (Pres_pure prims _ _)

theorem honestRo_fail (P : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (J : C.Quorum) (e : KeyIndex) (m : Message) :
    Pr[fun z => z.1 = none | roRun prims (honestRo P seeds (dealtKeys P seeds pairKeys) J e m) ∅] ≤
      (1 - codewordP) ^ randomizerAttemptLimit + (1 - codewordP) ^ randomizerAttemptLimit := by
  unfold honestRo
  refine step prims _ _ _ ∅ _ noMpc_empty fun r1 s1 hle1 hn1 hd1 hp1 => ?_
  have hm1 := hp1 IsMsg (Pres_refTop prims IsMsg (fun _ h => h) seeds P emptyTop) (noB_empty _)
  have hm1' := hp1 IsMsg80 (Pres_refTop prims IsMsg80 (fun _ h => h.1) seeds P emptyTop) (noB_empty _)
  obtain ⟨h0, hg0, ha0⟩ := exists_good prims s1 hn1
  obtain ⟨top, htop, -, -⟩ := D_refTop (prims := prims) (h := h0) P seeds emptyTop
  have hr1 : r1 = some (.top top) := (hd1 h0 hg0 ha0).trans htop
  have htopf : ∀ h, Good prims h → Agrees h s1 → TopFacts prims h seeds P top := by
    intro h hg ha
    obtain ⟨top', htop', hc', hr'⟩ := D_refTop (prims := prims) (h := h) P seeds emptyTop
    have : some (TreeOutput.top top') = some (.top top) := htop'.symm.trans ((hd1 h hg ha).symm.trans hr1)
    cases this
    exact ⟨hc', hr'⟩
  subst hr1
  dsimp only
  rw [bind_map_left]
  refine (step_add prims _ _ _ (fun r => r = none) s1 ((1 - codewordP) ^ randomizerAttemptLimit) hn1
    fun r2 s2 hr2 hle2 hn2 hd2 hp2 => ?_).trans
    (add_le_add (refBottom_fail prims seeds P top (treeOf e) s1 hn1 hm1 htopf) le_rfl)
  have hm2 := hp2 IsMsg80 (Pres_refBottom80 prims seeds P top (treeOf e)) hm1'
  obtain ⟨h0, hg0, ha0⟩ := exists_good prims s2 hn2
  obtain ⟨hc0, hrt0⟩ := htopf h0 hg0 (ha0.mono hle2)
  rcases D_refBottom (prims := prims) (h := h0) P seeds top hc0 hrt0 (treeOf e) with hb | ⟨tree, hb, -⟩
  · exact absurd ((hd2 h0 hg0 ha0).trans hb) hr2
  have hr2' : r2 = some (.bottom tree) := (hd2 h0 hg0 ha0).trans hb
  have hspec : ∀ h, Good prims h → Agrees h s2 → BottomSpec prims h seeds P top (treeOf e) tree := by
    intro h hg ha
    obtain ⟨hc, hrt⟩ := htopf h hg (ha.mono hle2)
    rcases D_refBottom (prims := prims) (h := h) P seeds top hc hrt (treeOf e) with hb' | ⟨tree', hb', hs'⟩
    · exact absurd ((hd2 h hg ha).trans hb') (by rw [hr2']; simp)
    · have : some (TreeOutput.bottom tree') = some (.bottom tree) := hb'.symm.trans ((hd2 h hg ha).symm.trans hr2')
      cases this
      exact hs'
  subst hr2'
  dsimp only
  refine step prims _ _ _ _ _ hn2 fun parts s3 hle3 hn3 hd3 hp3 => ?_
  have hm3 := hp3 IsMsg80 (Pres_sequenceFin prims _ _ fun i =>
    Pres_ite prims _ _ (Pres_eval prims _ _ _ _ _ _) (Pres_pure prims _ _)) hm2
  refine (step_add prims _ _ _ (fun r => r = none) s3 0 hn3 fun r4 s4 hr4 hle4 hn4 hd4 hp4 => ?_).trans
    (by
      rw [add_zero]
      refine signCodeword_fail prims P _ e m _ s3 hn3 hm3 fun h hg ha => ?_
      have hc := (hspec h hg (ha.mono hle3)).commitment ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
      rw [bottomKey_treeOf] at hc
      rw [hc, D_combine P seeds pairKeys J _ m parts fun i hi => by
        rw [hd3 h hg ha, D_sequenceFin]; dsimp only; rw [if_pos hi]])
  rcases r4 with _ | sc
  · exact absurd rfl hr4
  dsimp only
  refine step prims _ _ _ _ _ hn4 fun chainParts s5 _ hn5 _ _ => ?_
  refine step prims _ _ _ _ _ hn5 fun sig s6 _ _ _ _ => ?_
  rcases sig with _ | sig
  · rw [roRun_pure]; simp
  · dsimp only
    rw [map_eq_bind_pure_comp, roRun_bind]
    refine pr_bind_le fun p _ => ?_
    rw [Function.comp, roRun_pure]
    simp

theorem honestSigning_fail (J : C.Quorum) (e : KeyIndex) (m : Message) :
    Pr[fun r => r.1 = none | runWorld prims (honestSigning J e m)] ≤
      (1 - codewordP) ^ randomizerAttemptLimit + (1 - codewordP) ^ randomizerAttemptLimit := by
  have h1 : Pr[fun r => r.1 = none | runWorld prims (honestSigning J e m)] =
      Pr[fun r => r = none | Prod.fst <$> runWorld prims (honestSigning J e m)] := by
    rw [probEvent_map]; rfl
  rw [h1, fst_runWorld_honest]
  refine pr_bind_le fun x hx => ?_
  obtain ⟨pairKeys, hkeys⟩ := prawnsKeyGen_support x hx
  rw [probEvent_map, hkeys]
  exact honestRo_fail prims _ _ _ _ _ _

theorem toReal_codewordP : codewordP.toReal = codewordProbability := by
  unfold codewordP codewordProbability
  rw [card_valid (fun x : Encoding => Codeword.sum x = targetSum) fun _ => Iff.rfl, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  rfl

theorem toReal_failure : ((1 - codewordP) ^ randomizerAttemptLimit).toReal = searchFailure := by
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le codewordP_le_one ENNReal.one_ne_top, toReal_codewordP,
    ENNReal.toReal_one, searchFailure]

/-- Every signature of an honest quorum verifies, and the quorum fails with probability at most
`2 · searchFailure`, from the two randomizer searches. -/
theorem signingCorrectness (prims : Primitives) (C : Committee) : SigningCorrectnessStatement prims C := by
  intro J e m
  refine ⟨honestSigning_verifies prims J e m, ?_⟩
  have hfin : (1 - codewordP) ^ randomizerAttemptLimit ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  calc (Pr[fun r => r.1 = none | runWorld prims (honestSigning J e m)]).toReal
      ≤ ((1 - codewordP) ^ randomizerAttemptLimit + (1 - codewordP) ^ randomizerAttemptLimit).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, hfin⟩) (honestSigning_fail prims J e m)
    _ = 2 * searchFailure := by rw [ENNReal.toReal_add hfin hfin, toReal_failure]; ring

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

end ThresholdLeanXmssSecurity
