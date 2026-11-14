import LeanXmss.Scheme

/-!
# The copies of the leanXMSS functions of leanVM `1acdff19` and the pinned functions

The namespace `OldLeanXmss` holds a copy of each leanXMSS function that
`ThresholdLeanXmss/Scheme.lean` reads and that has a new form at leanVM `f5f3672f`. The text of
each copy is the text of
https://github.com/leanEthereum/leanVM/blob/1acdff19/formal/lean_xmss/LeanXmss/Scheme.lean, and a
comment gives its lines in that file. This file is for leanVM `1acdff19`, the pinned leanVM, on
Lean 4.31. For each copy, one theorem with the suffix `_old` proves that the copy is equal to the
pinned definition.

The branch that moves the proof to leanVM `f5f3672f` and Lean 4.35 has a file at this same path.
That file holds the same copies. For each copy, it proves an equation with the definitions of
`f5f3672f`.

The text of the copies has one difference from the text in that file. `layerRoot` reads the fields
`randomness` and `path` of `LayerSignature`. The names of these fields at `f5f3672f` are
`randomizer` and `authenticationPath`.

The text of the copies has two differences from the pinned text. The theorems `Codeword.valid_old`,
`Codeword.decode_old` and `Concrete.verify_old` prove that these differences keep the values.

* `Codeword.Valid` is an `abbrev`. The pinned text has a `def` and a `DecidablePred` instance.
* `verify` has no `irreducible` attribute.

A copy reads each name that has no copy, for example `Digest` and `tweakFields`, from the pinned
leanVM. `ThresholdLeanXmssSecurity/Bridge/Ambient.lean` fixes these names.

The script `tools/bridge_compare.py` compares the copies of the two files, the equations of the two
files, and the copies with the pinned text. Run it from the root of the repository.

```sh
python3 formal/tools/bridge_compare.py \
  --old formal/ThresholdLeanXmssSecurity/Bridge \
  --new <branch>/formal/ThresholdLeanXmssSecurity/Bridge
```
-/

set_option autoImplicit false

open OracleComp OracleSpec LeanXmss

namespace ThresholdLeanXmss.OldLeanXmss

/-! ## The parameters and the hash-input layout -/

-- Lines 32 to 34.
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128

theorem hashOutputBits_old : hashOutputBits = LeanXmss.hashOutputBits := rfl
theorem messageBits_old : messageBits = LeanXmss.messageBits := rfl
theorem publicParameterBits_old : publicParameterBits = LeanXmss.publicParameterBits := rfl

-- Lines 38 and 43.
/-- `v`, the chains of a one-time key. -/
def numChains : Nat := 58
def numLayers : Nat := 2

theorem numChains_old : numChains = LeanXmss.numChains := rfl
theorem numLayers_old : numLayers = LeanXmss.numLayers := rfl

-- Lines 56 and 66.
abbrev Randomness := Digest
abbrev Digit := Fin chainLength

theorem randomness_old : Randomness = LeanXmss.Randomness := rfl
theorem digit_old : Digit = LeanXmss.Digit := rfl

-- Lines 74 to 77.
/-- The key of layer `l` a leaf index signs with: `idx` at the bottom, `idx / 2^16` at the top. -/
def keyAt (index : LeafIndex) (lay : Layer) : KeyIndex :=
  ⟨index.val / 2 ^ (layerHeight * lay.val),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

theorem keyAt_old : keyAt = LeanXmss.keyAt := rfl

-- Lines 110 to 113.
/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

theorem bytesLE_old : bytesLE = LeanXmss.bytesLE := rfl

-- Lines 124 to 126.
/-- The 16 address bytes `lo || hi || (tag + 32 * step) || 0^8`. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++ bytesLE 8 0

theorem fieldBytes_old : fieldBytes = LeanXmss.fieldBytes := rfl

-- Lines 132 and 133.
/-- `hi` on layer `l`: the top layer sets bit 23 (`layer_hi`). -/
def layerHi (lay : Layer) (field : Nat) : Nat := field + 2 ^ 23 * lay.val

theorem layerHi_old : layerHi = LeanXmss.layerHi := rfl

-- Lines 144 to 149.
/-- Types `TWEAK_CHAIN = 1`, `TWEAK_LEAF = 2`, `TWEAK_NODE = 3`, `TWEAK_MSG = 12`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay key step => tweakFields 1 step (layerHi lay 0) key
  | .leaf lay key => tweakFields 2 0 (layerHi lay 0) key
  | .node lay level nodeIdx => tweakFields 3 0 (layerHi lay level) nodeIdx
  | .message lay key => tweakFields 12 0 (layerHi lay 0) key

theorem hashDomainFields_old : hashDomainFields = LeanXmss.hashDomainFields := rfl

-- Lines 151 to 158.
/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `P || A || payload` of every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ payload

theorem tweakBytes_old : tweakBytes = LeanXmss.tweakBytes := rfl

theorem tweakableHashInput_old : tweakableHashInput = LeanXmss.tweakableHashInput := rfl

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

theorem digit_old : digit = LeanXmss.Codeword.digit := rfl

theorem encoding_old : encoding = LeanXmss.Codeword.encoding := rfl

theorem sum_old : sum = LeanXmss.Codeword.sum := rfl

theorem valid_old : Valid = LeanXmss.Codeword.Valid := rfl

theorem decode_old : decode = LeanXmss.Codeword.decode := rfl

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

theorem sequenceFin_old : @sequenceFin = @LeanXmss.Concrete.sequenceFin := by
  funext m _ α n computation
  induction n with
  | zero => rfl
  | succ n ih => simp only [sequenceFin, LeanXmss.Concrete.sequenceFin, ih]

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
theorem oracleHash_old : oracleHash (m := m) = LeanXmss.Concrete.oracleHash := rfl

theorem tweakableHash_old : tweakableHash (m := m) = LeanXmss.Concrete.tweakableHash := rfl

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

theorem chainPayload_old : chainPayload = LeanXmss.Concrete.chainPayload := rfl

theorem chainWalk_old : chainWalk (m := m) = LeanXmss.Concrete.chainWalk := by
  funext parameter lay key chainIdx start steps value
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [chainWalk, LeanXmss.Concrete.chainWalk, ih, tweakableHash_old, chainPayload_old]

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

theorem recoverChain_old : recoverChain (m := m) = LeanXmss.Concrete.recoverChain := by
  funext parameter lay key chainIdx digit value
  simp only [recoverChain, LeanXmss.Concrete.recoverChain, chainWalk_old]

theorem leafPayload_old : leafPayload = LeanXmss.Concrete.leafPayload := rfl

theorem leafHash_old : leafHash (m := m) = LeanXmss.Concrete.leafHash := rfl

theorem messageDigest_old : messageDigest (m := m) = LeanXmss.Concrete.messageDigest := rfl

theorem otsLeaf_old : otsLeaf (m := m) = LeanXmss.Concrete.otsLeaf := by
  funext parameter lay key message randomness values
  simp only [otsLeaf, LeanXmss.Concrete.otsLeaf, messageDigest_old, Codeword.decode_old,
    sequenceFin_old, recoverChain_old, leafHash_old]
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
  let some leaf ← otsLeaf parameter lay key message part.randomness part.chainValues | return none
  let root ← treeFold parameter lay key part.path layerHeight leaf
  return some root

theorem nodePayload_old : nodePayload = LeanXmss.Concrete.nodePayload := rfl

theorem treeFold_old : treeFold (m := m) = LeanXmss.Concrete.treeFold := by
  funext parameter lay key path levels value
  induction levels with
  | zero => rfl
  | succ levels ih =>
    simp only [treeFold, LeanXmss.Concrete.treeFold, ih, tweakableHash_old, nodePayload_old]

theorem layerRoot_old : layerRoot (m := m) = LeanXmss.Concrete.layerRoot := by
  funext parameter lay key message part
  simp only [layerRoot, LeanXmss.Concrete.layerRoot, otsLeaf_old, treeFold_old]
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

theorem verify_old : verify (m := m) = LeanXmss.Concrete.verify := by
  funext publicKey message signature
  simp only [verify, LeanXmss.Concrete.verify, layerRoot_old, keyAt_old, bytesLE_old]
  rfl

end Concrete

/-! The check fails if the axioms of a theorem of this file change. -/

/-- info: 'ThresholdLeanXmss.OldLeanXmss.hashOutputBits_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hashOutputBits_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.messageBits_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms messageBits_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.publicParameterBits_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms publicParameterBits_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.numChains_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms numChains_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.numLayers_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms numLayers_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.randomness_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms randomness_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.digit_old' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms digit_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.keyAt_old' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms keyAt_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.bytesLE_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms bytesLE_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.fieldBytes_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldBytes_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.layerHi_old' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms layerHi_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.hashDomainFields_old' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms hashDomainFields_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.tweakBytes_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tweakBytes_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.tweakableHashInput_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tweakableHashInput_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.digit_old' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.digit_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.encoding_old' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.encoding_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.sum_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.sum_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.valid_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.valid_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Codeword.decode_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Codeword.decode_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.sequenceFin_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.sequenceFin_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.oracleHash_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.oracleHash_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.tweakableHash_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.tweakableHash_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.chainPayload_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.chainPayload_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.chainWalk_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.chainWalk_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.recoverChain_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.recoverChain_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.leafPayload_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.leafPayload_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.leafHash_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.leafHash_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.messageDigest_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.messageDigest_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.otsLeaf_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.otsLeaf_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.nodePayload_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.nodePayload_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.treeFold_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.treeFold_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.layerRoot_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.layerRoot_old

/-- info: 'ThresholdLeanXmss.OldLeanXmss.Concrete.verify_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.verify_old

end ThresholdLeanXmss.OldLeanXmss
