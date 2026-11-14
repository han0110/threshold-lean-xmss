import ThresholdLeanXmss.Scheme

/-!
# The leanXMSS functions of leanVM `1acdff19` and their form at `f5f3672f`

The namespace `OldLeanXmss` holds the definitions of
https://github.com/leanEthereum/leanVM/blob/1acdff19/formal/lean_xmss/LeanXmss/Scheme.lean
that `ThresholdLeanXmss/Scheme.lean` reads and that have a new form at `f5f3672f`. Each definition
is the old text on the types of `f5f3672f`. A comment gives its lines in the old file. After each
definition, one theorem proves that it is equal to the new form.

The old text has these three changes.

* `LayerSignature` has the fields `randomizer` and `authenticationPath`. Their old names are
  `randomness` and `path`.
* `Codeword.Valid` is an `abbrev`. The old text has a `def` and a `DecidablePred` instance.
* `verify` has no `irreducible` attribute.

The types `HashDomain`, `LayerSignature`, `Signature`, `PublicKey` and `TweakFields` are the types
of `f5f3672f`. This file does not compare a type with its old text.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss

namespace ThresholdLeanXmss.OldLeanXmss

/-! ## The parameters and the hash-input layout -/

-- Lines 32 to 34.
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128

theorem hashOutputBits_eq : BitVec hashOutputBits = HashOutput := rfl
theorem messageBits_eq : BitVec messageBits = Message := rfl
theorem publicParameterBits_eq : BitVec publicParameterBits = PublicParameter := rfl

-- Lines 38 and 43.
/-- `v`, the chains of a one-time key. -/
def numChains : Nat := 58
def numLayers : Nat := 2

theorem numChains_eq : numChains = chainCount := rfl
theorem numLayers_eq : numLayers = layerCount := rfl

-- Lines 56 and 66.
abbrev Randomness := Digest
abbrev Digit := Fin chainLength

theorem randomness_eq : Randomness = Randomizer := rfl
theorem digit_eq : Digit = WinternitzDigit := rfl

-- Lines 74 to 77.
/-- The key of layer `l` a leaf index signs with: `idx` at the bottom, `idx / 2^16` at the top. -/
def keyAt (index : LeafIndex) (lay : Layer) : KeyIndex :=
  ⟨index.val / 2 ^ (layerHeight * lay.val),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

theorem keyAt_eq (index : LeafIndex) (lay : Layer) : keyAt index lay = keyIndexOnLayer index lay :=
  rfl

-- Lines 110 to 113.
/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

theorem bytesLE_eq (byteCount : Nat) (value : BitVec (8 * byteCount)) :
    bytesLE byteCount value = littleEndianBytes byteCount value :=
  rfl

-- Lines 124 to 126.
/-- The 16 address bytes `lo || hi || (tag + 32 * step) || 0^8`. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++ bytesLE 8 0

theorem fieldBytes_eq (fields : TweakFields) : fieldBytes fields = addressBytes fields := rfl

-- Lines 132 and 133.
/-- `hi` on layer `l`: the top layer sets bit 23 (`layer_hi`). -/
def layerHi (lay : Layer) (field : Nat) : Nat := field + 2 ^ 23 * lay.val

theorem layerHi_eq (lay : Layer) (field : Nat) : layerHi lay field = LeanXmss.layerHi lay field :=
  rfl

-- Lines 144 to 149.
/-- Types `TWEAK_CHAIN = 1`, `TWEAK_LEAF = 2`, `TWEAK_NODE = 3`, `TWEAK_MSG = 12`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay key step => tweakFields 1 step (layerHi lay 0) key
  | .leaf lay key => tweakFields 2 0 (layerHi lay 0) key
  | .node lay level nodeIdx => tweakFields 3 0 (layerHi lay level) nodeIdx
  | .message lay key => tweakFields 12 0 (layerHi lay 0) key

theorem hashDomainFields_eq (domain : HashDomain) :
    hashDomainFields domain = LeanXmss.hashDomainFields domain := by
  cases domain <;> rfl

-- Lines 151 to 158.
/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `P || A || payload` of every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ payload

theorem tweakBytes_eq (domain : HashDomain) : tweakBytes domain = LeanXmss.tweakBytes domain := by
  rw [LeanXmss.tweakBytes, ← hashDomainFields_eq]
  rfl

theorem tweakableHashInput_eq (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    tweakableHashInput parameter domain payload =
      LeanXmss.tweakableHashInput parameter domain payload := by
  rw [LeanXmss.tweakableHashInput, ← tweakBytes_eq]
  rfl

/-! ## The codeword -/

namespace Codeword

-- Lines 198 to 217.
/-- `x_i`, digit `i < 64` of a digest read as a little-endian integer. -/
def digit (digest : Digest) (i : Nat) : Digit :=
  (digest.extractLsb' (winternitzBits * i) winternitzBits).toFin

/-- The first `v` digits. -/
def encoding (digest : Digest) : Encoding := fun i => digit digest i.val

/-- The sum of a word's digits. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- A codeword: the last `64 - v` digits are zero and the first `v` sum to `T`. -/
abbrev Valid (digest : Digest) : Prop :=
  digest.toNat / 2 ^ (winternitzBits * numChains) = 0 ∧ sum (encoding digest) = targetSum

/-- The word a digest encodes, if it is a codeword. -/
def decode (digest : Digest) : Option Encoding :=
  if Valid digest then some (encoding digest) else none

theorem digit_eq {n : Nat} (digest : Digest) (i : Fin n) :
    digit digest i.val = digestDigits digest i :=
  rfl

theorem encoding_eq (digest : Digest) : encoding digest = digestDigits digest := rfl

theorem sum_eq (x : Encoding) : sum x = LeanXmss.Codeword.sum x := rfl

theorem valid_eq (digest : Digest) : Valid digest = LeanXmss.Codeword.Valid digest := rfl

theorem decode_eq (digest : Digest) : decode digest = LeanXmss.Codeword.decode digest := rfl

end Codeword

/-! ## The hash and the verification -/

namespace Concrete

-- Lines 234 to 242.
/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

theorem sequenceFin_eq {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) :
    sequenceFin computation = OverPermutation.sequenceFin computation := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sequenceFin, OverPermutation.sequenceFin, ih]

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

-- Lines 246 to 254.
/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, A, M) = Truncate_n(H(P || A || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

omit [Monad m] in
theorem oracleHash_eq (input : HashInput) :
    oracleHash (m := m) input = Verification.oracleHashWithHash input :=
  rfl

theorem tweakableHash_eq (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    tweakableHash (m := m) parameter domain payload =
      Verification.tweakableHashWithHash parameter domain payload := by
  rw [tweakableHash, tweakableHashInput_eq]
  rfl

-- Lines 258 to 271.
/-- `value || LE_16(i)`, the payload of a chain step of chain `i`. -/
def chainPayload (chainIdx : ChainIndex) (value : Digest) : HashInput :=
  bytesLE 16 value ++ bytesLE 16 (BitVec.ofNat 128 chainIdx.val)

/-- `steps` chain steps from position `start`; the step leaving position `s` carries step `s`. -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay key chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay key ⟨start + steps, hstep⟩) (chainPayload chainIdx previous)
      else
        pure 0

theorem chainPayload_eq (chainIdx : ChainIndex) (value : Digest) :
    chainPayload chainIdx value = Verification.chainPayload chainIdx value :=
  rfl

theorem chainWalk_eq (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    chainWalk (m := m) parameter lay key chainIdx start steps value =
      Verification.chainWalkWithHash parameter lay key chainIdx start steps value := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [chainWalk, Verification.chainWalkWithHash, OverPermutation.walkChain, ih,
      tweakableHash_eq, chainPayload_eq]

-- Lines 273 to 301.
/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay key chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay key) (leafPayload endpoints)

/-- `D = Th(P, A_msg(l, e), M || rho)` (`message_digest`). -/
def messageDigest (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.message lay key) (message ++ bytesLE 16 randomness)

/-- `Ots.leaf` (`wots_leaf`): the leaf a claimed one-time signature recovers, or nothing if its
digest is not a codeword. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (randomness : Randomness) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigest parameter lay key message randomness
  let some encoding := Codeword.decode digest | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay key chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay key endpoints
  return some value

theorem recoverChain_eq (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) :
    recoverChain (m := m) parameter lay key chainIdx digit value =
      Verification.recoverChainWithHash parameter lay key chainIdx digit value :=
  chainWalk_eq ..

theorem leafPayload_eq (endpoints : ChainIndex → Digest) :
    leafPayload endpoints = digestsPayload endpoints :=
  rfl

theorem leafHash_eq (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) :
    leafHash (m := m) parameter lay key endpoints =
      Verification.leafHashWithHash parameter lay key endpoints :=
  tweakableHash_eq ..

theorem messageDigest_eq (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomness) :
    messageDigest (m := m) parameter lay key message randomness =
      Verification.messageDigestWithHash parameter lay key message randomness :=
  tweakableHash_eq ..

theorem otsLeaf_eq (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomness) (values : ChainIndex → Digest) :
    otsLeaf (m := m) parameter lay key message randomness values =
      Verification.otsLeafWithHash parameter lay key message randomness values := by
  simp only [otsLeaf, Verification.otsLeafWithHash, messageDigest_eq, Codeword.decode_eq,
    sequenceFin_eq, recoverChain_eq, leafHash_eq]
  rfl

-- Lines 305 to 327.
/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- `Tree.fold`: fold a key's leaf and path into its tree's root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay key path levels value
      let sibling := if hlevel : levels < layerHeight then path ⟨levels, hlevel⟩ else 0
      let nodeIdx := key.val / 2 ^ (levels + 1)
      if key.val.testBit levels then
        tweakableHash parameter (.node lay (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay (levels + 1) nodeIdx) (nodePayload current sibling)

/-- The root a layer's signature by key `e` reaches from `message`, or nothing (`layer_root`). -/
def layerRoot (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (part : LayerSignature) : m (Option Digest) := do
  let some leaf ← otsLeaf parameter lay key message part.randomizer part.chainValues | return none
  let root ← treeFold parameter lay key part.authenticationPath layerHeight leaf
  return some root

theorem nodePayload_eq (left right : Digest) :
    nodePayload left right = OverPermutation.nodePayload left right :=
  rfl

theorem treeFold_eq (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : Nat) (value : Digest) :
    treeFold (m := m) parameter lay key path levels value =
      Verification.treeFoldWithHash parameter lay key path levels value := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
    simp only [treeFold, Verification.treeFoldWithHash, OverPermutation.foldPath, ih,
      tweakableHash_eq, nodePayload_eq]
    refine congrArg _ (funext fun current => ?_)
    split <;> rfl

theorem layerRoot_eq (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) :
    layerRoot (m := m) parameter lay key message part =
      Verification.layerRootWithHash parameter lay key message part := by
  simp only [layerRoot, Verification.layerRootWithHash, otsLeaf_eq, treeFold_eq]
  rfl

-- Lines 333 to 339.
/-- `Ver(pk, m, sigma)`: recover the bottom root from the message, then the top root from the bottom
root, and compare it with the public key. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let index := signature.leafIndex
  let some bottomRoot ← layerRoot publicKey.parameter bottomLayer (keyAt index bottomLayer)
      (bytesLE 32 message) (signature.layers bottomLayer) | return false
  let some root ← layerRoot publicKey.parameter topLayer (keyAt index topLayer)
      (bytesLE 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

theorem verify_eq (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify (m := m) publicKey message signature =
      Verification.verifyWithHash publicKey message signature := by
  simp only [verify, Verification.verifyWithHash, layerRoot_eq, keyAt_eq, bytesLE_eq]
  rfl

end Concrete

/-! The build fails if the axioms of a theorem of this file change. -/

/-- info: 'ThresholdLeanXmss.OldLeanXmss.hashOutputBits_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hashOutputBits_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.messageBits_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms messageBits_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.publicParameterBits_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms publicParameterBits_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.numChains_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms numChains_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.numLayers_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms numLayers_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.randomness_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms randomness_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.digit_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms digit_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.keyAt_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms keyAt_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.bytesLE_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms bytesLE_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.fieldBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldBytes_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.layerHi_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms layerHi_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.hashDomainFields_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms hashDomainFields_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.tweakBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tweakBytes_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.tweakableHashInput_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tweakableHashInput_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.digit_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.digit_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.encoding_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.encoding_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.sum_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.valid_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.valid_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.decode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.decode_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.sequenceFin_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.sequenceFin_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.oracleHash_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.oracleHash_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.tweakableHash_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.tweakableHash_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.chainPayload_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.chainPayload_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.chainWalk_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.chainWalk_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.recoverChain_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.recoverChain_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.leafPayload_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.leafPayload_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.leafHash_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.leafHash_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.messageDigest_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.messageDigest_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.otsLeaf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.otsLeaf_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.nodePayload_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.nodePayload_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.treeFold_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.treeFold_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.layerRoot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.layerRoot_eq

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.verify_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.verify_eq

end ThresholdLeanXmss.OldLeanXmss
