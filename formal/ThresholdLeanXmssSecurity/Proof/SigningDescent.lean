import ThresholdLeanXmssSecurity.Proof.SeedHit
import XmssSecurity.Proof.ForgeryCases
import XmssSecurity.Proof.CacheReplayEval
import XmssSecurity.Proof.Bridge.Translate

/-!
# The descent of the signing core

Step 4 of the signing plan of `formal/PROOF.md` on the final cache, with no probability. A verified
fresh forgery forces a bad event, by the descent of leanVM over two layers.

The bad events use the cache of `Th` inside the cache of `H` (`thView`) and the honest data of the
key of the forgery (`HonestKey`).

* In a `Hit`, a cached input at a position of the key gives the output of the honest input there.
* In a `Guess`, a forged chain value is the honest value at its digit, below the opened position.
* In a `Partner`, the forged digest input gives the digest of the honest selected input.

The component lemmas.

* `fresh_layer` and `same_layer` do one layer. They use `classify_sameLeafIndex_forgery` of leanVM
  and a walk split (`walk_meets`), which turns a backward chain into a guess or a hit.
* `descent` does both layers on a cache in which the forgery verifies (`verifyFromCache`).
* `D_verify` turns the verification of the game with `H` fixed to the cache into `verifyFromCache`.
* `signing_win_badEvent` gives a bad event for a winning final state with no flag.
* `runSigningWorld_flaggedAfter` exposes the final state and the cache of the run (`exposedRun`).

The interfaces, as named `Prop`s.

* `CacheConsistent` says that the trees of `KeyGen` replay from the cache, and that the cache holds
  the inputs that the verification evaluates.
* `RunHasFinalState` says that each winning outcome of `exposedRun` with no flag ends in a
  consistent final state.

The guess of a commitment input before round 1 needs the order of the calls, which a final cache
does not hold.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningDescentProof

variable {C : Committee}

/-- The cache of `Th` inside the cache of `H`, as a cache of leanVM. -/
def thView (c : HashCache C) : XmssSecurity.HashSpec.QueryCache := fun x => c (.hash x)

/-- A computation of leanVM under `tweakable` with `H` fixed is its value with the answers of `Th`. -/
theorem D_tweakable (prims : Primitives) (h : Query C → HashOutput) {α : Type}
    (oa : OracleComp HashSpec α) :
    D prims h (tweakable oa) = evalWithAnswerFn (fun x => h (.hash x) : QueryImpl HashSpec Id) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    unfold tweakable at ih ⊢
    rw [simulateQ_bind, D_bind, simulateQ_query]
    simp only [evalWithAnswerFn, simulateQ_bind, simulateQ_query] at ih ⊢
    exact ih _

/-- The verification of the game with `H` fixed to the cache is `verifyFromCache` of leanVM. -/
theorem D_verify (prims : Primitives) (c : HashCache C) (pk : PublicKey) (message : Message)
    (signature : Signature) :
    D prims (fun q => (c q).getD 0) (tweakable (Concrete.verify pk message signature)) =
      XmssSecurity.Concrete.verifyFromCache (thView c) (XmssSecurity.Bridge.toModelPk pk)
        signature.leafIndex message (XmssSecurity.Bridge.toModelSig signature) := by
  rw [D_tweakable, XmssSecurity.Bridge.verify_real, ← XmssSecurity.Concrete.CacheReplay.eval_verify]
  rfl

/-! ## The bad events of one layer

A layer is one XMSS tree of leanVM with abstract hash functions, as in `XmssSecurity.ForgeryCases`.
Its honest data are the chain starts `secret` and the authentication path `path` of one key. -/

section Layer

variable (step : XmssSecurity.ChainIndex → ℕ → XmssSecurity.Digest → XmssSecurity.Digest)
  (leafHash : (XmssSecurity.ChainIndex → XmssSecurity.Digest) → XmssSecurity.Digest)
  (nodeHash : ℕ → XmssSecurity.Digest → XmssSecurity.Digest → XmssSecurity.Digest)
  (secret : XmssSecurity.ChainIndex → XmssSecurity.Digest) (path : ℕ → XmssSecurity.Digest)
  (stepCached : XmssSecurity.ChainIndex → ℕ → XmssSecurity.Digest → Prop)
  (leafCached : (XmssSecurity.ChainIndex → XmssSecurity.Digest) → Prop)
  (nodeCached : ℕ → XmssSecurity.Digest → XmssSecurity.Digest → Prop)

/-- The honest value of chain `l` at position `k`. -/
def honestValue (l : XmssSecurity.ChainIndex) (k : ℕ) : XmssSecurity.Digest :=
  XmssSecurity.Wots.walk (step l) 0 k (secret l)

/-- The honest chain ends of the key. -/
def honestEnds : XmssSecurity.ChainIndex → XmssSecurity.Digest :=
  fun l => XmssSecurity.Wots.publicChain (step l) (secret l)

/-- The honest node of the key at `level`, below its root. -/
def honestNode (level : ℕ) : XmssSecurity.Digest :=
  XmssSecurity.Merkle.ascend nodeHash path 0 level (leafHash (honestEnds step secret))

/-- A hit (step 4 of the plan). A cached input at a position of the key gives the output of the
honest input there. The position is a chain step, the leaf or a node of the path. -/
def LayerHit : Prop :=
  (∃ l k a, k < XmssSecurity.chainLength - 1 ∧ stepCached l k a ∧ a ≠ honestValue step secret l k ∧
    step l k a = step l k (honestValue step secret l k)) ∨
  (∃ ends, leafCached ends ∧ ends ≠ honestEnds step secret ∧
    leafHash ends = leafHash (honestEnds step secret)) ∨
  (∃ level < XmssSecurity.treeHeight, ∃ node sibling, nodeCached level node sibling ∧
    (node, sibling) ≠ (honestNode step leafHash nodeHash secret path level, path level) ∧
    nodeHash level node sibling = nodeHash level (honestNode step leafHash nodeHash secret path level)
      (path level))

/-- The verification of a forged signature evaluates these inputs, so they are cached. They are
the chain steps from each forged digit, the leaf and the nodes of the path. -/
def LayerCached (forgedEncoding : XmssSecurity.Encoding)
    (forgedValue : XmssSecurity.ChainIndex → XmssSecurity.Digest) (forgedPath : ℕ → XmssSecurity.Digest) : Prop :=
  (∀ l k, (forgedEncoding l).val ≤ k → k < XmssSecurity.chainLength - 1 →
    stepCached l k (XmssSecurity.Wots.walk (step l) (forgedEncoding l).val (k - (forgedEncoding l).val)
      (forgedValue l))) ∧
  leafCached (XmssSecurity.recoveredEndpoints step forgedEncoding forgedValue) ∧
  ∀ level < XmssSecurity.treeHeight, nodeCached level
    (XmssSecurity.Merkle.ascend nodeHash forgedPath 0 level
      (leafHash (XmssSecurity.recoveredEndpoints step forgedEncoding forgedValue))) (forgedPath level)

/-- A guess (step 4 of the plan). The forged value of a chain is the honest value at the forged
digit, and this digit is below the opened position of the chain. The verification queries this hidden honest input. -/
def LayerGuess (opened : XmssSecurity.ChainIndex → ℕ) (forgedEncoding : XmssSecurity.Encoding)
    (forgedValue : XmssSecurity.ChainIndex → XmssSecurity.Digest) : Prop :=
  ∃ l, (forgedEncoding l).val < opened l ∧
    forgedValue l = honestValue step secret l (forgedEncoding l).val

/-- A walk from position `p` that ends on the honest chain starts on it, or meets it at a step from
another input. -/
theorem walk_meets {α : Type} (stepAt : ℕ → α → α) (start x : α) (p : ℕ) :
    ∀ n, XmssSecurity.Wots.walk stepAt p n x = XmssSecurity.Wots.walk stepAt 0 (p + n) start →
      x = XmssSecurity.Wots.walk stepAt 0 p start ∨
        ∃ k, p ≤ k ∧ k < p + n ∧
          XmssSecurity.Wots.walk stepAt p (k - p) x ≠ XmssSecurity.Wots.walk stepAt 0 k start ∧
          stepAt k (XmssSecurity.Wots.walk stepAt p (k - p) x) =
            stepAt k (XmssSecurity.Wots.walk stepAt 0 k start)
  | 0, h => Or.inl (by simpa [XmssSecurity.Wots.walk] using h)
  | n + 1, h => by
    rcases Classical.em (XmssSecurity.Wots.walk stepAt p n x =
        XmssSecurity.Wots.walk stepAt 0 (p + n) start) with hn | hn
    · rcases walk_meets stepAt start x p n hn with h0 | ⟨k, hk, hk', ha⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, hk, by omega, ha⟩
    · refine Or.inr ⟨p + n, by omega, by omega, ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact ⟨hn, by simpa [XmssSecurity.Wots.walk, Nat.add_assoc] using h⟩

/-- A codeword has a digit below the top, because `58 * 3 > 106`. -/
theorem exists_digit_lt_top (x : XmssSecurity.Encoding) (hx : XmssSecurity.TargetSum.Valid x) :
    ∃ l, (x l).val < XmssSecurity.chainLength - 1 := by
  by_contra h
  push Not at h
  have hsum := Finset.card_nsmul_le_sum Finset.univ (fun l => (x l).val) _ fun l _ => h l
  unfold XmssSecurity.TargetSum.Valid XmssSecurity.TargetSum.sum at hx
  rw [hx] at hsum
  simp [XmssSecurity.chainLength, XmssSecurity.winternitzBits, XmssSecurity.numChains,
    XmssSecurity.targetSum] at hsum

/-- If the recovered end of a chain is the honest end, then the forged value is the honest value at
its digit, or a chain step above it is a hit. -/
theorem guess_or_hit_of_end (l : XmssSecurity.ChainIndex) (digit : XmssSecurity.Digit)
    (value : XmssSecurity.Digest)
    (hend : XmssSecurity.Wots.recoverChain (step l) digit value = honestEnds step secret l)
    (hcached : ∀ k, digit.val ≤ k → k < XmssSecurity.chainLength - 1 →
      stepCached l k (XmssSecurity.Wots.walk (step l) digit.val (k - digit.val) value)) :
    value = honestValue step secret l digit.val ∨
      LayerHit step leafHash nodeHash secret path stepCached leafCached nodeCached := by
  have hle : digit.val ≤ XmssSecurity.chainLength - 1 := Nat.le_pred_of_lt digit.isLt
  have hwalk : XmssSecurity.Wots.walk (step l) digit.val (XmssSecurity.chainLength - 1 - digit.val) value =
      XmssSecurity.Wots.walk (step l) 0 (digit.val + (XmssSecurity.chainLength - 1 - digit.val)) (secret l) := by
    rw [Nat.add_sub_cancel' hle]
    exact hend
  rcases walk_meets (step l) (secret l) value digit.val _ hwalk with h | ⟨k, hk, hk', ha, hstep⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨l, k, _, by omega, hcached k hk (by omega), ha, hstep⟩)

/-- The descent at a key with no honest codeword, as `classify_freshLeafIndex_forgery` of leanVM.
a hit, or a guess below the chain end, the only opened position. -/
theorem fresh_layer (forgedEncoding : XmssSecurity.Encoding)
    (hvalid : XmssSecurity.TargetSum.Valid forgedEncoding)
    (forgedValue : XmssSecurity.ChainIndex → XmssSecurity.Digest) (forgedPath : ℕ → XmssSecurity.Digest)
    (hroot : XmssSecurity.Merkle.ascend nodeHash forgedPath 0 XmssSecurity.treeHeight
        (leafHash (XmssSecurity.recoveredEndpoints step forgedEncoding forgedValue)) =
      XmssSecurity.Merkle.ascend nodeHash path 0 XmssSecurity.treeHeight
        (leafHash (honestEnds step secret)))
    (hcached : LayerCached step leafHash nodeHash stepCached leafCached nodeCached forgedEncoding forgedValue
      forgedPath) :
    LayerHit step leafHash nodeHash secret path stepCached leafCached nodeCached ∨
      LayerGuess step secret (fun _ => XmssSecurity.chainLength - 1) forgedEncoding forgedValue := by
  rcases XmssSecurity.Merkle.sameXmssPath_or_hasCollision nodeHash forgedPath path _ _ hroot with
    ⟨hleaf, -⟩ | ⟨level, hne, heq⟩
  · rcases XmssSecurity.Wots.eq_or_hasLeafCollision leafHash _ _ hleaf with hends | ⟨hne, heq⟩
    · obtain ⟨l, hl⟩ := exists_digit_lt_top forgedEncoding hvalid
      rcases guess_or_hit_of_end step leafHash nodeHash secret path stepCached leafCached nodeCached l
          (forgedEncoding l) (forgedValue l) (congrFun hends l) (hcached.1 l) with h | h
      · exact Or.inr ⟨l, hl, h⟩
      · exact Or.inl h
    · exact Or.inl (Or.inr (Or.inl ⟨_, hcached.2.1, hne, heq⟩))
  · exact Or.inl (Or.inr (Or.inr ⟨level.val, level.isLt, _, _, hcached.2.2 _ level.isLt, hne, heq⟩))

/-- The honest values at the digits of a codeword, the chain values of its honest signature. -/
def signedValues (encoding : XmssSecurity.Encoding) : XmssSecurity.ChainIndex → XmssSecurity.Digest :=
  fun l => XmssSecurity.Wots.signChain (step l) (encoding l) (secret l)

theorem recovered_signedValues (encoding : XmssSecurity.Encoding) :
    XmssSecurity.recoveredEndpoints step encoding (signedValues step secret encoding) =
      honestEnds step secret := by
  funext l
  exact XmssSecurity.Wots.recover_signChain_eq_publicChain (step l) (encoding l) (secret l)

/-- The descent at a key with an honest codeword, by `classify_sameLeafIndex_forgery` of leanVM.
a digest partner, a hit, or a guess below the honest digit. -/
theorem same_layer {EncodingInput : Type} (encodingHash : EncodingInput → XmssSecurity.Digest)
    (signedInput forgedInput : EncodingInput) (signedEncoding forgedEncoding : XmssSecurity.Encoding)
    (hsigned : XmssSecurity.TargetSum.decodeDigest (encodingHash signedInput) = some signedEncoding)
    (hforged : XmssSecurity.TargetSum.decodeDigest (encodingHash forgedInput) = some forgedEncoding)
    (forgedValue : XmssSecurity.ChainIndex → XmssSecurity.Digest) (forgedPath : ℕ → XmssSecurity.Digest)
    (hroot : XmssSecurity.Merkle.ascend nodeHash forgedPath 0 XmssSecurity.treeHeight
        (leafHash (XmssSecurity.recoveredEndpoints step forgedEncoding forgedValue)) =
      XmssSecurity.Merkle.ascend nodeHash path 0 XmssSecurity.treeHeight
        (leafHash (honestEnds step secret)))
    (hstrong : signedInput ≠ forgedInput ∨ signedValues step secret signedEncoding ≠ forgedValue ∨
      ¬XmssSecurity.Merkle.SamePathSegment path forgedPath 0 XmssSecurity.treeHeight)
    (hcached : LayerCached step leafHash nodeHash stepCached leafCached nodeCached forgedEncoding forgedValue
      forgedPath) :
    (signedInput ≠ forgedInput ∧ encodingHash signedInput = encodingHash forgedInput) ∨
      LayerHit step leafHash nodeHash secret path stepCached leafCached nodeCached ∨
      LayerGuess step secret (fun l => (signedEncoding l).val) forgedEncoding forgedValue := by
  have hends := recovered_signedValues step secret signedEncoding
  rcases XmssSecurity.classify_sameLeafIndex_forgery encodingHash step leafHash nodeHash signedInput
      forgedInput signedEncoding forgedEncoding (signedValues step secret signedEncoding) forgedValue path
      forgedPath hsigned hforged (by rw [hends]; exact hroot) hstrong with
    hpartner | ⟨i, hlt, hwalk⟩ | ⟨⟨i, offset⟩, hle, hne, heq⟩ | hleaf | ⟨level, hne, heq⟩
  · exact Or.inl hpartner
  · have hwalk' : XmssSecurity.Wots.walk (step i) (forgedEncoding i).val
          ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i) =
        XmssSecurity.Wots.walk (step i) 0
          ((forgedEncoding i).val + ((signedEncoding i).val - (forgedEncoding i).val)) (secret i) := by
      rw [Nat.add_sub_cancel' (Fin.le_iff_val_le_val.mp hlt.le)]
      exact hwalk
    rcases walk_meets (step i) (secret i) (forgedValue i) _ _ hwalk' with h | ⟨k, hk, hk', ha, hstep⟩
    · exact Or.inr (Or.inr ⟨i, hlt, h⟩)
    · have := (signedEncoding i).isLt
      have hlt' := Fin.lt_def.mp hlt
      exact Or.inr (Or.inl (Or.inl ⟨i, k, _, by omega, hcached.1 i k hk (by omega), ha, hstep⟩))
  · have hoff := offset.isLt
    have hhonest : XmssSecurity.Wots.walk (step i) (signedEncoding i).val offset.val
        (signedValues step secret signedEncoding i) =
          honestValue step secret i ((signedEncoding i).val + offset.val) := by
      have h := XmssSecurity.Wots.walk_signChain_to_later (step i) (signedEncoding i).val
        ((signedEncoding i).val + offset.val) (secret i) (Nat.le_add_right _ _)
      rw [Nat.add_sub_cancel_left] at h
      exact h
    rw [hhonest] at hne heq
    have hforged : XmssSecurity.Wots.walk (step i) (signedEncoding i).val offset.val
        (XmssSecurity.Wots.walk (step i) (forgedEncoding i).val
          ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i)) =
        XmssSecurity.Wots.walk (step i) (forgedEncoding i).val
          ((signedEncoding i).val + offset.val - (forgedEncoding i).val) (forgedValue i) := by
      have h := (XmssSecurity.Wots.walk_split (step i) (forgedEncoding i).val (signedEncoding i).val
        ((signedEncoding i).val + offset.val) (forgedValue i) hle (Nat.le_add_right _ _)).symm
      rw [Nat.add_sub_cancel_left] at h
      exact h
    have hle' : (forgedEncoding i).val ≤ (signedEncoding i).val := hle
    refine Or.inr (Or.inl (Or.inl ⟨i, _, _, by omega, ?_, hne, heq⟩))
    rw [hforged]
    exact hcached.1 i _ (by omega) (by omega)
  · rw [hends] at hleaf
    exact Or.inr (Or.inl (Or.inr (Or.inl ⟨_, hcached.2.1, hleaf⟩)))
  · rw [hends] at hne heq
    exact Or.inr (Or.inl (Or.inr (Or.inr ⟨level.val, level.isLt, _, _, hcached.2.2 _ level.isLt, hne, heq⟩)))

/-- The honest signature of a codeword guesses a hidden value when nothing is opened. -/
theorem guess_of_signed (encoding : XmssSecurity.Encoding) (hvalid : XmssSecurity.TargetSum.Valid encoding) :
    LayerGuess step secret (fun _ => XmssSecurity.chainLength - 1) encoding
      (signedValues step secret encoding) := by
  obtain ⟨l, hl⟩ := exists_digit_lt_top encoding hvalid
  exact ⟨l, hl, rfl⟩

end Layer

/-! ## The bad events of the final cache -/

/-- The honest data at the key `e` of a forgery and at its top key `topKeyOf e`.

* `secret` and `path` are the chain starts and the authentication path of `e`.
* `topSecret` and `topPath` are the same for the top key, and `topRandomness` is the randomness of
  the top signature of the tree of `e`.
* `selected` is the selected digest input of the honest signers at `e`, the bound message and its
  randomness, if they signed there.
* `released` tells that at least `t` operators can give the chain parts at `e` for the bound message.
-/
structure HonestKey where
  secret : XmssSecurity.ChainIndex → XmssSecurity.Digest
  path : ℕ → XmssSecurity.Digest
  topSecret : XmssSecurity.ChainIndex → XmssSecurity.Digest
  topPath : ℕ → XmssSecurity.Digest
  topRandomness : XmssSecurity.Randomness
  selected : Option (XmssSecurity.Message × XmssSecurity.Randomness)
  released : Bool

section Cache

variable (c : HashCache C) (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex) (hk : HonestKey)

/-- The chain step of the bottom layer at `e`, read from the cache. -/
abbrev bottomStep (l : XmssSecurity.ChainIndex) : ℕ → XmssSecurity.Digest → XmssSecurity.Digest :=
  XmssSecurity.Concrete.CacheView.chainStep (thView c) P e l

/-- The chain step of the top layer at `topKeyOf e`, read from the cache. -/
abbrev topStep (l : XmssSecurity.ChainIndex) : ℕ → XmssSecurity.Digest → XmssSecurity.Digest :=
  XmssSecurity.Concrete.CacheView.topChainStep (thView c) P (XmssSecurity.topKeyOf e) l

/-- The honest root of the bottom tree of `e`. -/
def honestRoot : XmssSecurity.Digest :=
  honestNode (bottomStep c P e) (XmssSecurity.Concrete.CacheView.leafHash (thView c) P e)
    (XmssSecurity.Concrete.CacheView.nodeHash (thView c) P e) hk.secret hk.path XmssSecurity.treeHeight

/-- The digest input of the honest top signature of the tree of `e`. -/
def topSignedInput : XmssSecurity.Digest × XmssSecurity.Randomness := (honestRoot c P e hk, hk.topRandomness)

/-- The honest selected codeword at `e`. -/
def selectedEncoding : Option XmssSecurity.Encoding :=
  hk.selected.bind fun s => XmssSecurity.TargetSum.decodeDigest
    (XmssSecurity.Concrete.CacheView.encodingHash (thView c) P e s)

/-- The codeword of the honest top signature of the tree of `e`. -/
def topEncoding : Option XmssSecurity.Encoding :=
  XmssSecurity.TargetSum.decodeDigest
    (XmssSecurity.Concrete.CacheView.topEncodingHash (thView c) P (XmssSecurity.topKeyOf e) (topSignedInput c P e hk))

/-- The opened position of each chain at `e`. It is the honest digit once the signature is
released, and the chain end before. -/
def bottomOpened (l : XmssSecurity.ChainIndex) : ℕ :=
  match hk.released, selectedEncoding c P e hk with
  | true, some encoding => (encoding l).val
  | _, _ => XmssSecurity.chainLength - 1

/-- The opened position of each chain at the top key, the digit of the public top signature. -/
def topOpened (l : XmssSecurity.ChainIndex) : ℕ :=
  match topEncoding c P e hk with
  | some encoding => (encoding l).val
  | none => XmssSecurity.chainLength - 1

/-- The honest signature at `e` for the selected input. -/
def honestSig : Option XmssSecurity.Signature := do
  let s ← hk.selected
  let encoding ← selectedEncoding c P e hk
  let topCodeword ← topEncoding c P e hk
  pure ⟨s.2, signedValues (bottomStep c P e) hk.secret encoding, fun i => hk.path i,
    ⟨hk.topRandomness, signedValues (topStep c P e) hk.topSecret topCodeword, fun i => hk.topPath i⟩⟩

/-- The bottom root that a forged signature reaches with the codeword `encoding`. -/
def forgedRoot (encoding : XmssSecurity.Encoding) (σ : XmssSecurity.Signature) : XmssSecurity.Digest :=
  XmssSecurity.Merkle.ascend (XmssSecurity.Concrete.CacheView.nodeHash (thView c) P e)
    (XmssSecurity.Concrete.signaturePath σ) 0 XmssSecurity.treeHeight
    (XmssSecurity.Concrete.CacheView.leafHash (thView c) P e
      (XmssSecurity.recoveredEndpoints (bottomStep c P e) encoding σ.chainValue))

/-- A chain step of the bottom layer at `e` is in the cache. -/
def bottomStepCached (l : XmssSecurity.ChainIndex) (k : ℕ) (value : XmssSecurity.Digest) : Prop :=
  ∃ hk : k < XmssSecurity.chainLength - 1,
    (thView c (XmssSecurity.Concrete.CacheView.chainInput P e l ⟨k, hk⟩ value)).isSome

/-- A leaf input of the bottom layer at `e` is in the cache. -/
def bottomLeafCached (ends : XmssSecurity.ChainIndex → XmssSecurity.Digest) : Prop :=
  (thView c (XmssSecurity.Concrete.CacheView.leafInput P e ends)).isSome

/-- A node input of the bottom path of `e` is in the cache. -/
def bottomNodeCached (level : ℕ) (node sibling : XmssSecurity.Digest) : Prop :=
  ∃ hlevel : level < XmssSecurity.treeHeight,
    (thView c (XmssSecurity.Concrete.CacheView.nodeInput P e ⟨level, hlevel⟩ node sibling)).isSome

/-- A chain step of the top layer at `topKeyOf e` is in the cache. -/
def topStepCached (l : XmssSecurity.ChainIndex) (k : ℕ) (value : XmssSecurity.Digest) : Prop :=
  ∃ hk : k < XmssSecurity.chainLength - 1,
    (thView c (XmssSecurity.Concrete.CacheView.topChainInput P (XmssSecurity.topKeyOf e) l ⟨k, hk⟩ value)).isSome

/-- A leaf input of the top layer at `topKeyOf e` is in the cache. -/
def topLeafCached (ends : XmssSecurity.ChainIndex → XmssSecurity.Digest) : Prop :=
  (thView c (XmssSecurity.Concrete.CacheView.topLeafInput P (XmssSecurity.topKeyOf e) ends)).isSome

/-- A node input of the top path of `topKeyOf e` is in the cache. -/
def topNodeCached (level : ℕ) (node sibling : XmssSecurity.Digest) : Prop :=
  ∃ hlevel : level < XmssSecurity.treeHeight,
    (thView c (XmssSecurity.Concrete.CacheView.topNodeInput P (XmssSecurity.topKeyOf e) ⟨level, hlevel⟩ node
      sibling)).isSome

/-- A hit (step 4 of the plan) at the bottom key or at the top key. -/
def Hit : Prop :=
  LayerHit (bottomStep c P e) (XmssSecurity.Concrete.CacheView.leafHash (thView c) P e)
      (XmssSecurity.Concrete.CacheView.nodeHash (thView c) P e) hk.secret hk.path
      (bottomStepCached c P e) (bottomLeafCached c P e) (bottomNodeCached c P e) ∨
    LayerHit (topStep c P e) (XmssSecurity.Concrete.CacheView.topLeafHash (thView c) P (XmssSecurity.topKeyOf e))
      (XmssSecurity.Concrete.CacheView.topNodeHash (thView c) P (XmssSecurity.topKeyOf e)) hk.topSecret hk.topPath
      (topStepCached c P e) (topLeafCached c P e) (topNodeCached c P e)

/-- The inputs that the verification of the forgery of `m` evaluates are in the cache, at both
layers. -/
def VerifyCached (m : XmssSecurity.Message) (σ : XmssSecurity.Signature) : Prop :=
  ∀ encoding, XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (thView c) P e (m, σ.randomness)) = some encoding →
    LayerCached (bottomStep c P e) (XmssSecurity.Concrete.CacheView.leafHash (thView c) P e)
        (XmssSecurity.Concrete.CacheView.nodeHash (thView c) P e) (bottomStepCached c P e)
        (bottomLeafCached c P e) (bottomNodeCached c P e) encoding σ.chainValue
        (XmssSecurity.Concrete.signaturePath σ) ∧
      ∀ topCodeword, XmssSecurity.TargetSum.decodeDigest
          (XmssSecurity.Concrete.CacheView.topEncodingHash (thView c) P (XmssSecurity.topKeyOf e)
            (forgedRoot c P e encoding σ, σ.top.randomness)) = some topCodeword →
        LayerCached (topStep c P e)
          (XmssSecurity.Concrete.CacheView.topLeafHash (thView c) P (XmssSecurity.topKeyOf e))
          (XmssSecurity.Concrete.CacheView.topNodeHash (thView c) P (XmssSecurity.topKeyOf e))
          (topStepCached c P e) (topLeafCached c P e) (topNodeCached c P e) topCodeword σ.top.chainValue
          (XmssSecurity.Concrete.layerPath σ.top)

/-- A guess (step 4 of the plan) of the forgery of `m` at the bottom key or at the top key. -/
def Guess (m : XmssSecurity.Message) (σ : XmssSecurity.Signature) : Prop :=
  ∃ encoding, XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (thView c) P e (m, σ.randomness)) = some encoding ∧
    (LayerGuess (bottomStep c P e) hk.secret (bottomOpened c P e hk) encoding σ.chainValue ∨
      ∃ topCodeword, XmssSecurity.TargetSum.decodeDigest
          (XmssSecurity.Concrete.CacheView.topEncodingHash (thView c) P (XmssSecurity.topKeyOf e)
            (forgedRoot c P e encoding σ, σ.top.randomness)) = some topCodeword ∧
        LayerGuess (topStep c P e) hk.topSecret (topOpened c P e hk) topCodeword σ.top.chainValue)

/-- A digest partner (step 4 of the plan). The forged digest input of `m` at the bottom key or at
the top key gives the digest of the honest selected input there. -/
def Partner (m : XmssSecurity.Message) (σ : XmssSecurity.Signature) : Prop :=
  (∃ s, hk.selected = some s ∧ s ≠ (m, σ.randomness) ∧
    XmssSecurity.Concrete.CacheView.encodingHash (thView c) P e s =
      XmssSecurity.Concrete.CacheView.encodingHash (thView c) P e (m, σ.randomness)) ∨
  ∃ encoding, XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (thView c) P e (m, σ.randomness)) = some encoding ∧
    topSignedInput c P e hk ≠ (forgedRoot c P e encoding σ, σ.top.randomness) ∧
    XmssSecurity.Concrete.CacheView.topEncodingHash (thView c) P (XmssSecurity.topKeyOf e) (topSignedInput c P e hk) =
      XmssSecurity.Concrete.CacheView.topEncodingHash (thView c) P (XmssSecurity.topKeyOf e)
        (forgedRoot c P e encoding σ, σ.top.randomness)

theorem topOpened_of {topCodeword : XmssSecurity.Encoding} (h : topEncoding c P e hk = some topCodeword) :
    topOpened c P e hk = fun l => (topCodeword l).val := by
  funext l
  simp [topOpened, h]

theorem bottomOpened_of_released {encoding : XmssSecurity.Encoding} (hr : hk.released = true)
    (h : selectedEncoding c P e hk = some encoding) : bottomOpened c P e hk = fun l => (encoding l).val := by
  funext l
  simp [bottomOpened, hr, h]

theorem bottomOpened_of_not_released (hr : hk.released = false) :
    bottomOpened c P e hk = fun _ => XmssSecurity.chainLength - 1 := by
  funext l
  simp [bottomOpened, hr]

theorem bottomOpened_of_none (h : selectedEncoding c P e hk = none) :
    bottomOpened c P e hk = fun _ => XmssSecurity.chainLength - 1 := by
  funext l
  cases hr : hk.released <;> simp [bottomOpened, hr, h]

theorem topOpened_of_none (h : topEncoding c P e hk = none) :
    topOpened c P e hk = fun _ => XmssSecurity.chainLength - 1 := by
  funext l
  simp [topOpened, h]

/-- The descent of leanVM over two layers on the final cache. A forgery that verifies in the cache
and is fresh gives a hit, a guess or a digest partner. The top layer goes first. If the forged top
signature is the honest one, the bottom layer follows, with the honest codeword at `e` if there is
one, and as a fresh key otherwise. -/
theorem descent (pk : XmssSecurity.PublicKey) (m : XmssSecurity.Message) (σ : XmssSecurity.Signature)
    (hverify : XmssSecurity.Concrete.verifyFromCache (thView c) pk e m σ = true)
    (htopRoot : honestNode (topStep c pk.parameter e)
        (XmssSecurity.Concrete.CacheView.topLeafHash (thView c) pk.parameter (XmssSecurity.topKeyOf e))
        (XmssSecurity.Concrete.CacheView.topNodeHash (thView c) pk.parameter (XmssSecurity.topKeyOf e))
        hk.topSecret hk.topPath XmssSecurity.treeHeight = pk.root)
    (hcached : VerifyCached c pk.parameter e m σ)
    (hfresh : hk.released = true → hk.selected.map Prod.fst = some m →
      honestSig c pk.parameter e hk ≠ some σ) :
    Hit c pk.parameter e hk ∨ Guess c pk.parameter e hk m σ ∨ Partner c pk.parameter e hk m σ := by
  obtain ⟨encoding, hencoding, htop⟩ :=
    (XmssSecurity.Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).mp hverify
  obtain ⟨topCodeword, htopCodeword, htopRoot'⟩ :=
    (XmssSecurity.Concrete.verifyTopFromCache_eq_true_iff _ _ _ _ _).mp htop
  have hcachedBottom := (hcached encoding hencoding).1
  have hcachedTop := (hcached encoding hencoding).2 topCodeword htopCodeword
  cases hsignedTop : topEncoding c pk.parameter e hk with
  | none =>
    rcases fresh_layer (topStep c pk.parameter e)
        (XmssSecurity.Concrete.CacheView.topLeafHash (thView c) pk.parameter (XmssSecurity.topKeyOf e))
        (XmssSecurity.Concrete.CacheView.topNodeHash (thView c) pk.parameter (XmssSecurity.topKeyOf e))
        hk.topSecret hk.topPath _ _ _ topCodeword
        (XmssSecurity.TargetSum.decodeDigest_eq_some_iff.mp htopCodeword).2 σ.top.chainValue
        (XmssSecurity.Concrete.layerPath σ.top) (htopRoot'.trans htopRoot.symm) hcachedTop with h | h
    · exact Or.inl (Or.inr h)
    · refine Or.inr (Or.inl ⟨encoding, hencoding, Or.inr ⟨topCodeword, htopCodeword, ?_⟩⟩)
      rw [topOpened_of_none c pk.parameter e hk hsignedTop]
      exact h
  | some signedTop =>
  rcases Classical.em (topSignedInput c pk.parameter e hk ≠ (forgedRoot c pk.parameter e encoding σ, σ.top.randomness) ∨
      signedValues (topStep c pk.parameter e) hk.topSecret signedTop ≠ σ.top.chainValue ∨
      ¬XmssSecurity.Merkle.SamePathSegment hk.topPath (XmssSecurity.Concrete.layerPath σ.top) 0
        XmssSecurity.treeHeight) with hstrong | hsame
  · rcases same_layer (topStep c pk.parameter e)
        (XmssSecurity.Concrete.CacheView.topLeafHash (thView c) pk.parameter (XmssSecurity.topKeyOf e))
        (XmssSecurity.Concrete.CacheView.topNodeHash (thView c) pk.parameter (XmssSecurity.topKeyOf e))
        hk.topSecret hk.topPath _ _ _
        (XmssSecurity.Concrete.CacheView.topEncodingHash (thView c) pk.parameter (XmssSecurity.topKeyOf e))
        _ _ signedTop topCodeword hsignedTop htopCodeword σ.top.chainValue
        (XmssSecurity.Concrete.layerPath σ.top) (htopRoot'.trans htopRoot.symm) hstrong hcachedTop with
      h | h | h
    · exact Or.inr (Or.inr (Or.inr ⟨encoding, hencoding, h⟩))
    · exact Or.inl (Or.inr h)
    · refine Or.inr (Or.inl ⟨encoding, hencoding, Or.inr ⟨topCodeword, htopCodeword, ?_⟩⟩)
      rw [topOpened_of c pk.parameter e hk hsignedTop]
      exact h
  · push Not at hsame
    obtain ⟨hinput, hvalues, hpath⟩ := hsame
    have hroot : forgedRoot c pk.parameter e encoding σ = honestRoot c pk.parameter e hk :=
      (congrArg Prod.fst hinput).symm
    have hvalid := (XmssSecurity.TargetSum.decodeDigest_eq_some_iff.mp hencoding).2
    cases hsigned : selectedEncoding c pk.parameter e hk with
    | none =>
      rcases fresh_layer (bottomStep c pk.parameter e) (XmssSecurity.Concrete.CacheView.leafHash (thView c) pk.parameter e)
          (XmssSecurity.Concrete.CacheView.nodeHash (thView c) pk.parameter e) hk.secret hk.path _ _ _ encoding hvalid
          σ.chainValue (XmssSecurity.Concrete.signaturePath σ) hroot hcachedBottom with h | h
      · exact Or.inl (Or.inl h)
      · refine Or.inr (Or.inl ⟨encoding, hencoding, Or.inl ?_⟩)
        rw [bottomOpened_of_none c pk.parameter e hk hsigned]
        exact h
    | some signed =>
      obtain ⟨s, hsel, hdecode⟩ := Option.bind_eq_some_iff.mp hsigned
      rcases Classical.em (s ≠ (m, σ.randomness) ∨
          signedValues (bottomStep c pk.parameter e) hk.secret signed ≠ σ.chainValue ∨
          ¬XmssSecurity.Merkle.SamePathSegment hk.path (XmssSecurity.Concrete.signaturePath σ) 0
            XmssSecurity.treeHeight) with hstrong | hidentical
      · rcases same_layer (bottomStep c pk.parameter e)
            (XmssSecurity.Concrete.CacheView.leafHash (thView c) pk.parameter e)
            (XmssSecurity.Concrete.CacheView.nodeHash (thView c) pk.parameter e) hk.secret hk.path _ _ _
            (XmssSecurity.Concrete.CacheView.encodingHash (thView c) pk.parameter e) _ _ signed encoding
            hdecode hencoding σ.chainValue (XmssSecurity.Concrete.signaturePath σ) hroot hstrong
            hcachedBottom with
          h | h | ⟨l, hl, hvalue⟩
        · exact Or.inr (Or.inr (Or.inl ⟨s, hsel, h⟩))
        · exact Or.inl (Or.inl h)
        · refine Or.inr (Or.inl ⟨encoding, hencoding, Or.inl ⟨l, ?_, hvalue⟩⟩)
          cases hr : hk.released
          · rw [bottomOpened_of_not_released c pk.parameter e hk hr]
            have := (signed l).isLt
            simp only at hl ⊢
            omega
          · rw [bottomOpened_of_released c pk.parameter e hk hr hsigned]
            exact hl
      · push Not at hidentical
        obtain ⟨hs, hvaluesBottom, hpathBottom⟩ := hidentical
        subst hs
        obtain rfl : encoding = signed := Option.some.inj (hencoding.symm.trans hdecode)
        cases hr : hk.released
        · refine Or.inr (Or.inl ⟨encoding, hencoding, Or.inl ?_⟩)
          rw [bottomOpened_of_not_released c pk.parameter e hk hr, ← hvaluesBottom]
          exact guess_of_signed _ _ encoding hvalid
        · exfalso
          refine hfresh hr (by simp [hsel]) ?_
          simp only [honestSig, hsel, hsigned, hsignedTop]
          refine congrArg some ?_
          rcases σ with ⟨randomness, chainValue, authPath, ⟨topRandomness, topChainValue, topAuthPath⟩⟩
          have hauth : (fun i : Fin XmssSecurity.treeHeight => hk.path i) = authPath := funext fun i => by
            simpa [XmssSecurity.Concrete.signaturePath, i.isLt] using hpathBottom i.val i.isLt
          have htopAuth : (fun i : Fin XmssSecurity.treeHeight => hk.topPath i) = topAuthPath := funext fun i => by
            simpa [XmssSecurity.Concrete.layerPath, i.isLt] using hpath i.val i.isLt
          have htopRandomness : hk.topRandomness = topRandomness := congrArg Prod.snd hinput
          rw [hvaluesBottom, hvalues, hauth, htopAuth, htopRandomness]

end Cache

/-! ## The final state of the signing game -/

/-- The end of a run of `flaggedAfter`. It holds the keys, the top tree, the state of the oracles,
the forgery, the cache of `H` and the flag of a call on a hidden key. -/
structure FinalState (C : Committee) where
  keys : SigningSecurityProof.Keys3 C
  top : TopTree
  state : TsigState C
  forgery : Forgery
  cache : HashCache C
  flag : Bool

namespace FinalState

variable (prims : Primitives) (z : FinalState C)

/-- `H` fixed to the cache. -/
def answers : Query C → HashOutput := fun q => (z.cache q).getD 0

/-- `KeyGen` of the game with `H` fixed to the cache. -/
def dealt : Dealt C Id :=
  dealtWith (fun oa => D prims z.answers oa) z.keys.1 (dealtKeys z.keys.1 z.keys.2.1 z.keys.2.2) z.top
    (fun p => D prims z.answers (prfValue z.keys.2.1 p))

/-- The key of the forgery. -/
abbrev key : KeyIndex := z.forgery.signature.leafIndex

/-- The win of `tsigFinish` with `H` fixed to the cache. The forgery verifies, and fewer than `t`
operators can give its chain parts or it differs from the signature of `KeyGen`. -/
def Wins : Prop :=
  D prims z.answers (tweakable (Concrete.verify ⟨z.top.root, z.keys.1⟩ z.forgery.message z.forgery.signature)) =
      true ∧
    ((signersAt z.state z.key z.forgery.message).card < C.t ∨
      honestSignature (m := Id) (fun oa => D prims z.answers oa) (z.dealt prims) z.key z.forgery.message ≠
        some z.forgery.signature)

/-- The chain starts `F(x_{l, 0})` of a layer. -/
def chainStarts (lay : Layer) (e : KeyIndex) (l : ChainIndex) : Digest :=
  D prims z.answers (prfValue z.keys.2.1 (.chain lay e l (digit 0)))

/-- The bottom tree of the key of the forgery. -/
def bottomTree : Option BottomTree := (z.dealt prims).bottom (treeOf z.key)

/-- The selected digest input of the honest signers at the key of the forgery, for the bound
message, with `ρ_e` and `c_e`. -/
def selected : Option (Message × Randomness) := do
  let message ← z.state.bound z.key
  let tree ← z.bottomTree prims
  let ρ := D prims z.answers (prfValue z.keys.2.1 (.randomizer bottomLayer z.key))
  let (randomness, _) ← D prims z.answers (signCodeword z.keys.1 (tree.commitment z.key) z.key message ρ)
  pure (message, randomness)

/-- The honest data of the final state at the key of the forgery, replayed from the cache. -/
def honestKey : HonestKey where
  secret := z.chainStarts prims bottomLayer z.key
  path level := if hlevel : level < XmssSecurity.treeHeight then
    XmssSecurity.Concrete.CacheReplay.treeNode (thView z.cache) z.keys.1 (z.chainStarts prims bottomLayer) level
      (XmssSecurity.Concrete.authenticationPathNode z.key ⟨level, hlevel⟩) else 0
  topSecret := z.chainStarts prims topLayer (topKey (XmssSecurity.topKeyOf z.key))
  topPath level := if hlevel : level < XmssSecurity.treeHeight then
    XmssSecurity.Concrete.CacheReplay.topTreeNode (thView z.cache) z.keys.1
      (fun b => z.chainStarts prims topLayer (topKey b)) level
      (XmssSecurity.Concrete.topPathNode (XmssSecurity.topKeyOf z.key) ⟨level, hlevel⟩) else 0
  topRandomness := ((z.bottomTree prims).map fun tree => tree.topSignature.randomness).getD 0
  selected := z.selected prims
  released := match z.state.bound z.key with
    | some message => decide (C.t ≤ (signersAt z.state z.key message).card)
    | none => false

end FinalState

/-- The open link from the game to the cache.

* The top root is the root that leanVM replays from the cache.
* The inputs that the verification of the forgery evaluates are in the cache.
* The signature of `KeyGen` at the bound message is the honest signature that leanVM replays.

The first and the last are the dealer correctness of `referenceTree` on the cache of the run. -/
def CacheConsistent (prims : Primitives) (z : FinalState C) : Prop :=
  let hk := z.honestKey prims
  let P := z.keys.1
  honestNode (topStep z.cache P z.key)
      (XmssSecurity.Concrete.CacheView.topLeafHash (thView z.cache) P (XmssSecurity.topKeyOf z.key))
      (XmssSecurity.Concrete.CacheView.topNodeHash (thView z.cache) P (XmssSecurity.topKeyOf z.key))
      hk.topSecret hk.topPath XmssSecurity.treeHeight = z.top.root ∧
    VerifyCached z.cache P z.key z.forgery.message (XmssSecurity.Bridge.toModelSig z.forgery.signature) ∧
    ∀ message, z.state.bound z.key = some message →
      honestSignature (m := Id) (fun oa => D prims z.answers oa) (z.dealt prims) z.key message =
        (honestSig z.cache P z.key hk).map (XmssSecurity.Bridge.toRealSig z.key)

/-- Step 4 of the signing plan on the final cache. A final state in which the forgery wins and the
flag of a call on a hidden key is not set holds a hit, a guess or a digest partner, given
`CacheConsistent`. The descent does not use the flag. The flag matters only for the costs of step 5. -/
theorem signing_win_badEvent (prims : Primitives) (z : FinalState C) (hconsistent : CacheConsistent prims z)
    (hwin : z.Wins prims) (_hflag : z.flag = false) :
    let hk := z.honestKey prims
    let σ := XmssSecurity.Bridge.toModelSig z.forgery.signature
    Hit z.cache z.keys.1 z.key hk ∨ Guess z.cache z.keys.1 z.key hk z.forgery.message σ ∨
      Partner z.cache z.keys.1 z.key hk z.forgery.message σ := by
  obtain ⟨htopRoot, hcached, hhonest⟩ := hconsistent
  obtain ⟨hverified, hfresh⟩ := hwin
  have hverify := (D_verify prims z.cache _ _ _).symm.trans hverified
  refine descent z.cache z.key (z.honestKey prims) (XmssSecurity.Bridge.toModelPk ⟨z.top.root, z.keys.1⟩)
    z.forgery.message _ hverify htopRoot hcached ?_
  intro hreleased hbound heq
  have hb : z.state.bound z.key = some z.forgery.message := by
    cases hb : z.state.bound z.key with
    | none => simp [FinalState.honestKey, FinalState.selected, hb] at hbound
    | some message =>
      simp [FinalState.honestKey, FinalState.selected, hb] at hbound
      obtain ⟨_, hx⟩ := hbound
      obtain ⟨_, -, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨_, -, hx⟩ := Option.bind_eq_some_iff.mp hx
      exact congrArg some (Prod.mk.inj (Option.some.inj hx)).1
  have hsigners : C.t ≤ (signersAt z.state z.key z.forgery.message).card := by
    simpa [FinalState.honestKey, hb] using hreleased
  apply hfresh.resolve_left (not_lt.mpr hsigners)
  rw [hhonest _ hb]
  change honestSig z.cache z.keys.1 z.key (z.honestKey prims) = _ at heq
  rw [heq, Option.map_some, XmssSecurity.Bridge.toRealSig_toModelSig]

/-! ## The run of the game -/

/-- `flaggedAfter` that also returns the top tree, the state of the oracles and the forgery. -/
def finalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) := do
  let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa)) value x.1 emptyTop .top
    | pure ((false, false), none)
  let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
  let r ← (simulateQ (SigningCoreProof.flaggedOracles x dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run
    (SigningCoreProof.tsigInit, false)
  (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$> SigningCoreProof.tsigFinish dealt (r.1, r.2.1)

theorem finalRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Prod.fst <$> finalRun A x = SigningCoreProof.flaggedAfter A x := by
  unfold finalRun SigningCoreProof.flaggedAfter
  rw [map_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp
  · simp only [map_bind, Functor.map_map]
  · simp
/-- The run of `finalRun` in `runSigningWorld` with its cache exposed. -/
def exposedRun (prims : Primitives) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × HashCache C × ℕ) :=
  (simulateQ (SeedHitProof.withCount (SeedHitProof.signImpl prims)) (finalRun A x)).run ((∅ : HashCache C), 0)

/-- The run of `flaggedAfter` in `runSigningWorld` forgets the final state and the cache of
`exposedRun`. -/
theorem runSigningWorld_flaggedAfter (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    runSigningWorld prims (SigningCoreProof.flaggedAfter A x) =
      (fun w => (w.1.1, w.2.2)) <$> exposedRun prims A x := by
  rw [← finalRun_forget, SeedHitProof.runSigningWorld_eq_withCount, simulateQ_map, StateT.run_map,
    Functor.map_map]
  rfl

/-- The open link from the run to the cache. Each outcome of `exposedRun` with a win and no flag
ends in a final state with its cache. In it the forgery wins with `H` fixed to the cache, and the
cache is consistent. The lazy cache only grows, so each computation of the run gives its value again
on the final cache. -/
def RunHasFinalState (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × HashCache C × ℕ),
    r ∈ support (exposedRun prims A x) → r.1.1 = (true, false) →
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      (FinalState.mk x top state forgery r.2.1 false).Wins prims ∧
      CacheConsistent prims (FinalState.mk x top state forgery r.2.1 false)

set_option maxRecDepth 100000 in
/-- Each outcome of `exposedRun` with a win and no flag holds a hit, a guess or a digest partner in
its final cache, given `RunHasFinalState`. -/
theorem signing_run_badEvent (prims : Primitives) (hrun : RunHasFinalState prims C) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × HashCache C × ℕ)
    (hr : r ∈ support (exposedRun prims A x)) (hwin : r.1.1 = (true, false)) :
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      let z : FinalState C := ⟨x, top, state, forgery, r.2.1, false⟩
      Hit z.cache z.keys.1 z.key (z.honestKey prims) ∨
        Guess z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
          (XmssSecurity.Bridge.toModelSig z.forgery.signature) ∨
        Partner z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
          (XmssSecurity.Bridge.toModelSig z.forgery.signature) := by
  obtain ⟨top, state, forgery, hsome, hwins, hconsistent⟩ := hrun A x r hr hwin
  exact ⟨top, state, forgery, hsome, signing_win_badEvent prims _ hconsistent hwins rfl⟩

end SigningDescentProof

/-- info: 'ThresholdLeanXmssSecurity.SigningDescentProof.signing_win_badEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningDescentProof.signing_win_badEvent

/-- info: 'ThresholdLeanXmssSecurity.SigningDescentProof.signing_run_badEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningDescentProof.signing_run_badEvent

/-- info: 'ThresholdLeanXmssSecurity.SigningDescentProof.runSigningWorld_flaggedAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningDescentProof.runSigningWorld_flaggedAfter

end ThresholdLeanXmssSecurity
