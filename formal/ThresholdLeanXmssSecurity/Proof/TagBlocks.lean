import ThresholdLeanXmss.Scheme

/-!
# Tag blocks are not tweakable hash inputs

`thInput_ne_of_nonzero_tail` states that no input `thInput parameter fields payload` of the
tweakable hash starts with a block of 32 bytes that has a nonzero byte at an index from 24 to 31.
`thInput_ne_of_no_zero_byte` applies it to a block with no zero byte, which is the form of a tag
block.

`tagNames` is a copy of the tag constants of the Rust code, and a person keeps the two equal.
`tagBlocks_nodup` and `tagged_ne_of_ne` state that hash inputs with different tags differ, and
`thInput_ne_tagged` states that no `Th` input starts with a tag block.

These are facts on byte lists and on the byte model of leanVM. They do not state that the encoding
of one use is injective, because the code joins the parts of an input with no length.
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

/-- The tag block of `name`, the ASCII bytes of `name` padded on the right with `_` to 32 bytes. -/
def tagBlock (name : String) : HashInput :=
  let bytes := name.toList.map fun c => UInt8.ofNat c.toNat
  bytes ++ List.replicate (32 - bytes.length) 0x5F

/-- The tag names of the Rust code, in the order of the tag table of `doc/dkg.md` 1.1.4. -/
def tagNames : List String :=
  ["thlxmss-history", "thlxmss-copy", "thlxmss-coin", "thlxmss-expand", "thlxmss-digest",
    "rss-prss", "thlxmss-keygen-parameter", "thlxmss-keygen-term", "thlxmss-prss-term",
    "thlxmss-keygen-pair", "thlxmss-prss-pair", "thlxmss-keygen-echo", "thlxmss-prss-echo",
    "thlxmss-commit", "thlxmss-prss-commit", "thlxmss-prf", "thlxmss-mask"]

/-- Each tag block has 32 bytes. -/
theorem tagBlock_length : ∀ name ∈ tagNames, (tagBlock name).length = 32 := by
  decide

/-- No tag block has a zero byte. -/
theorem tagBlock_no_zero_byte : ∀ name ∈ tagNames, ∀ byte ∈ tagBlock name, byte ≠ 0 := by
  decide +kernel

/-- The tag blocks are pairwise different. -/
theorem tagBlocks_nodup : (tagNames.map tagBlock).Nodup := by
  decide

/-- Two hash inputs with different tags are different. -/
theorem tagged_ne_of_ne (s t : String) (hs : s ∈ tagNames) (ht : t ∈ tagNames) (hne : s ≠ t)
    (x y : HashInput) : tagBlock s ++ x ≠ tagBlock t ++ y := by
  intro hequal
  have hblock := (List.append_inj hequal
    ((tagBlock_length s hs).trans (tagBlock_length t ht).symm)).1
  exact hne (List.inj_on_of_nodup_map tagBlocks_nodup hs ht hblock)

/-- No tweakable hash input starts with a tag block. -/
theorem thInput_ne_tagged (parameter : PublicParameter) (fields : TweakFields)
    (payload : HashInput) (name : String) (hname : name ∈ tagNames) (rest : HashInput) :
    thInput parameter fields payload ≠ tagBlock name ++ rest :=
  thInput_ne_of_no_zero_byte parameter fields payload (tagBlock name) rest
    (tagBlock_length name hname) (tagBlock_no_zero_byte name hname)

end ThresholdLeanXmssSecurity
