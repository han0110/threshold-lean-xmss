import ThresholdLeanXmss.Scheme

/-!
# Tag blocks are not tweakable hash inputs

`thInput_ne_of_nonzero_tail` states that no input `thInput parameter fields payload` of the
tweakable hash starts with a block of 32 bytes that has a nonzero byte at an index from 24 to 31.
`thInput_ne_of_no_zero_byte` applies it to a block with no zero byte, which is the form of a tag
block.

These are facts on the byte model of leanVM. They do not connect the tags of the Rust code to the
model.
-/

set_option autoImplicit false

open LeanXmss HashSig

namespace ThresholdLeanXmssSecurity

/-- Bytes 24 to 31 of a tweakable hash input are zero. -/
theorem thInput_getElem?_eq_zero (parameter : PublicParameter) (fields : TweakFields)
    (payload : HashInput) (index : Nat) (hlow : 24 ≤ index) (hhigh : index < 32) :
    (thInput parameter fields payload)[index]? = some 0 := by
  interval_cases index <;>
    simp [thInput, hasherInput, addressBytes, littleEndianBytes, List.ofFn_succ]

/-- No tweakable hash input starts with a block of 32 bytes that has a nonzero byte at an index
from 24 to 31. -/
theorem thInput_ne_of_nonzero_tail (parameter : PublicParameter) (fields : TweakFields)
    (payload block rest : HashInput) (hlength : block.length = 32) (index : Nat)
    (hlow : 24 ≤ index) (hhigh : index < 32) (hnonzero : block[index]'(by omega) ≠ 0) :
    thInput parameter fields payload ≠ block ++ rest := by
  intro hequal
  have hbyte := thInput_getElem?_eq_zero parameter fields payload index hlow hhigh
  rw [hequal, List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)] at hbyte
  exact hnonzero (Option.some.inj hbyte)

/-- No tweakable hash input starts with a block of 32 bytes with no zero byte. -/
theorem thInput_ne_of_no_zero_byte (parameter : PublicParameter) (fields : TweakFields)
    (payload block rest : HashInput) (hlength : block.length = 32)
    (hnonzero : ∀ byte ∈ block, byte ≠ 0) :
    thInput parameter fields payload ≠ block ++ rest :=
  thInput_ne_of_nonzero_tail parameter fields payload block rest hlength 24 (by decide) (by decide)
    (hnonzero _ (List.getElem_mem _))

end ThresholdLeanXmssSecurity
