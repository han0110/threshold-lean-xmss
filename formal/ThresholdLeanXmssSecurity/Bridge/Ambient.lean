import ThresholdLeanXmss.Scheme

/-!
# The leanVM names that the copies of the leanXMSS functions read

The copies of `ThresholdLeanXmssSecurity/Bridge/LeanXmss.lean` read constants, types, functions and
structures of leanVM that have no copy. This file states what each of these names is, with numbers,
with types of Lean and of Mathlib, and with products and sums.

The import lines and the part `Dictionary` are the only text that names a definition of one leanVM
revision. Each theorem after the dictionary uses the names of the dictionary, or a name that the
two revisions share. The same theorem text, with the dictionary of the other revision, states the
same fact about that revision.

`HashDomain` is an inductive type with four constructors. Its fact is an equivalence with a sum of
four products. Each of the four structures has an equivalence with the product of the types of its
fields, in the order of the fields.
-/

set_option autoImplicit false

namespace ThresholdLeanXmss.Ambient

/-! ## Dictionary -/

open OracleComp OracleSpec HashSig LeanXmss

/-- The randomizer of the signature of one layer. -/
abbrev layerRandomizer (part : LayerSignature) : Digest := part.randomizer

/-- The authentication path of the signature of one layer. -/
abbrev layerPath (part : LayerSignature) : Fin layerHeight → Digest := part.authenticationPath

/-! ## The numeric constants -/

theorem digestBits_eq : digestBits = 128 := rfl
theorem winternitzBits_eq : winternitzBits = 2 := rfl
theorem chainLength_eq : chainLength = 4 := rfl
theorem targetSum_eq : targetSum = 106 := rfl
theorem layerHeight_eq : layerHeight = 16 := rfl
theorem lifetime_eq : lifetime = 2 ^ 32 := rfl
theorem randomizerAttemptLimit_eq : randomizerAttemptLimit = 2 ^ 32 := rfl

/-! ## The type abbreviations -/

theorem digest_eq : Digest = BitVec 128 := rfl
theorem layer_eq : Layer = Fin 2 := rfl
theorem leafIndex_eq : LeafIndex = Fin (2 ^ 32) := rfl
theorem keyIndex_eq : KeyIndex = Fin (2 ^ 32) := rfl
theorem chainIndex_eq : ChainIndex = Fin 58 := rfl
theorem chainStep_eq : ChainStep = Fin 3 := rfl
theorem encoding_eq : Encoding = (Fin 58 → Fin 4) := rfl
theorem hashInput_eq : HashInput = List UInt8 := rfl
theorem hashOutput_eq : HashOutput = BitVec 256 := rfl
theorem message_eq : Message = BitVec 256 := rfl
theorem publicParameter_eq : PublicParameter = BitVec 128 := rfl
theorem hashSpec_eq : HashSpec = (List UInt8 →ₒ BitVec 256) := rfl

/-! ## The functions -/

theorem bottomLayer_val : bottomLayer.val = 0 := rfl
theorem topLayer_val : topLayer.val = 1 := rfl

theorem truncateHash_eq (output : HashOutput) :
    truncateHash output = output.extractLsb' 0 digestBits :=
  rfl

theorem tweakFields_eq (tag step hi lo : Nat) :
    tweakFields tag step hi lo =
      ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩ :=
  rfl

/-! ## The structures -/

/-- `HashDomain` has the constructors `chain`, `leaf`, `node` and `message`. The equivalence gives
the arguments of each constructor, in their order. -/
theorem hashDomain_equiv :
    ∃ e : HashDomain ≃
        (Layer × KeyIndex × ChainStep) ⊕ (Layer × KeyIndex) ⊕ (Layer × ℕ × ℕ) ⊕ (Layer × KeyIndex),
      (∀ lay key step, e (.chain lay key step) = .inl (lay, key, step)) ∧
        (∀ lay key, e (.leaf lay key) = .inr (.inl (lay, key))) ∧
        (∀ lay level nodeIdx,
          e (.node lay level nodeIdx) = .inr (.inr (.inl (lay, level, nodeIdx)))) ∧
        ∀ lay key, e (.message lay key) = .inr (.inr (.inr (lay, key))) :=
  ⟨⟨fun
      | .chain lay key step => .inl (lay, key, step)
      | .leaf lay key => .inr (.inl (lay, key))
      | .node lay level nodeIdx => .inr (.inr (.inl (lay, level, nodeIdx)))
      | .message lay key => .inr (.inr (.inr (lay, key))),
    fun
      | .inl (lay, key, step) => .chain lay key step
      | .inr (.inl (lay, key)) => .leaf lay key
      | .inr (.inr (.inl (lay, level, nodeIdx))) => .node lay level nodeIdx
      | .inr (.inr (.inr (lay, key))) => .message lay key,
    fun domain => by cases domain <;> rfl,
    fun x => by rcases x with ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;> rfl⟩,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- `TweakFields` is the product of its fields `tag`, `step`, `hi` and `lo`, in this order. -/
theorem tweakFields_equiv :
    ∃ e : TweakFields ≃ BitVec 5 × BitVec 3 × BitVec 24 × BitVec 32,
      (∀ fields, e fields = (fields.tag, fields.step, fields.hi, fields.lo)) ∧
        ∀ tag step hi lo, e.symm (tag, step, hi, lo) = ⟨tag, step, hi, lo⟩ :=
  ⟨⟨fun fields => (fields.tag, fields.step, fields.hi, fields.lo),
      fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩,
    fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- `PublicKey` is the product of its fields `root` and `parameter`, in this order. -/
theorem publicKey_equiv :
    ∃ e : PublicKey ≃ Digest × PublicParameter,
      (∀ publicKey, e publicKey = (publicKey.root, publicKey.parameter)) ∧
        ∀ root parameter, e.symm (root, parameter) = ⟨root, parameter⟩ :=
  ⟨⟨fun publicKey => (publicKey.root, publicKey.parameter), fun x => ⟨x.1, x.2⟩, fun _ => rfl,
      fun _ => rfl⟩,
    fun _ => rfl, fun _ _ => rfl⟩

/-- `LayerSignature` is the product of its three fields, namely the randomizer, the chain values
and the authentication path, in this order. -/
theorem layerSignature_equiv :
    ∃ e : LayerSignature ≃ Digest × (ChainIndex → Digest) × (Fin layerHeight → Digest),
      (∀ part, e part = (layerRandomizer part, part.chainValues, layerPath part)) ∧
        ∀ randomizer chainValues path,
          e.symm (randomizer, chainValues, path) = ⟨randomizer, chainValues, path⟩ :=
  ⟨⟨fun part => (layerRandomizer part, part.chainValues, layerPath part),
      fun x => ⟨x.1, x.2.1, x.2.2⟩, fun _ => rfl, fun _ => rfl⟩,
    fun _ => rfl, fun _ _ _ => rfl⟩

/-- `Signature` is the product of its fields `leafIndex` and `layers`, in this order. -/
theorem signature_equiv :
    ∃ e : Signature ≃ LeafIndex × (Layer → LayerSignature),
      (∀ signature, e signature = (signature.leafIndex, signature.layers)) ∧
        ∀ leafIndex layers, e.symm (leafIndex, layers) = ⟨leafIndex, layers⟩ :=
  ⟨⟨fun signature => (signature.leafIndex, signature.layers), fun x => ⟨x.1, x.2⟩, fun _ => rfl,
      fun _ => rfl⟩,
    fun _ => rfl, fun _ _ => rfl⟩

/-! The build fails if the axioms of a theorem of this file change. -/

/-- info: 'ThresholdLeanXmss.Ambient.digestBits_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms digestBits_eq

/-- info: 'ThresholdLeanXmss.Ambient.winternitzBits_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms winternitzBits_eq

/-- info: 'ThresholdLeanXmss.Ambient.chainLength_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms chainLength_eq

/-- info: 'ThresholdLeanXmss.Ambient.targetSum_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms targetSum_eq

/-- info: 'ThresholdLeanXmss.Ambient.layerHeight_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms layerHeight_eq

/-- info: 'ThresholdLeanXmss.Ambient.lifetime_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetime_eq

/-- info: 'ThresholdLeanXmss.Ambient.randomizerAttemptLimit_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms randomizerAttemptLimit_eq

/-- info: 'ThresholdLeanXmss.Ambient.digest_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms digest_eq

/-- info: 'ThresholdLeanXmss.Ambient.layer_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms layer_eq

/-- info: 'ThresholdLeanXmss.Ambient.leafIndex_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms leafIndex_eq

/-- info: 'ThresholdLeanXmss.Ambient.keyIndex_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms keyIndex_eq

/-- info: 'ThresholdLeanXmss.Ambient.chainIndex_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms chainIndex_eq

/-- info: 'ThresholdLeanXmss.Ambient.chainStep_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms chainStep_eq

/-- info: 'ThresholdLeanXmss.Ambient.encoding_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_eq

/-- info: 'ThresholdLeanXmss.Ambient.hashInput_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hashInput_eq

/-- info: 'ThresholdLeanXmss.Ambient.hashOutput_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hashOutput_eq

/-- info: 'ThresholdLeanXmss.Ambient.message_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms message_eq

/-- info: 'ThresholdLeanXmss.Ambient.publicParameter_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms publicParameter_eq

/-- info: 'ThresholdLeanXmss.Ambient.hashSpec_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hashSpec_eq

/-- info: 'ThresholdLeanXmss.Ambient.bottomLayer_val' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms bottomLayer_val

/-- info: 'ThresholdLeanXmss.Ambient.topLayer_val' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms topLayer_val

/-- info: 'ThresholdLeanXmss.Ambient.truncateHash_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms truncateHash_eq

/-- info: 'ThresholdLeanXmss.Ambient.tweakFields_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms tweakFields_eq

/-- info: 'ThresholdLeanXmss.Ambient.hashDomain_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hashDomain_equiv

/-- info: 'ThresholdLeanXmss.Ambient.tweakFields_equiv' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tweakFields_equiv

/-- info: 'ThresholdLeanXmss.Ambient.publicKey_equiv' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicKey_equiv

/-- info: 'ThresholdLeanXmss.Ambient.layerSignature_equiv' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layerSignature_equiv

/-- info: 'ThresholdLeanXmss.Ambient.signature_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signature_equiv

end ThresholdLeanXmss.Ambient
