import ThresholdLeanXmssSecurity.Proof.SigningLaneHybridCap
import ThresholdLeanXmssSecurity.Proof.Dealer

/-!
# The reference job on one bottom chain row

`referenceJob_row_of_walks` evaluates `referenceJob` on one chain row. The result is the two public pads
and the endpoint, when the PRF values are the masked values of the chain walk.

This declaration is in the namespace `SigningLaneHybridCapProof`. It uses `Dealer`, and
`SigningLaneHybridCap` does not import this module.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningLaneHybridCapProof

open SigningOpeningProof SigningSecurityProof

variable {C : Committee}

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- The real `referenceJob` row evaluates to the public pads and endpoint when the
PRF targets are the corresponding masked symbolic chain values. -/
theorem referenceJob_row_of_walks (P : PublicParameter) (H : HashInput → HashOutput)
    (F : Point → Digest) (e : KeyIndex) (l : ChainIndex)
    (s₀ s₁ s₂ cpk₁ cpk₂ endpoint : Digest)
    (hF₀ : F (.chain bottomLayer e l (digit 0)) = s₀)
    (hF₁ : F (.chain bottomLayer e l (digit 1)) = s₁ ^^^ cpk₁)
    (hF₂ : F (.chain bottomLayer e l (digit 2)) = s₂ ^^^ cpk₂)
    (hwalk : evalTh H (Verification.chainWalkWithHash P bottomLayer e l 0 1 s₀) = s₁ ∧
      evalTh H (Verification.chainWalkWithHash P bottomLayer e l 0 2 s₀) = s₂ ∧
      evalTh H (Verification.chainWalkWithHash P bottomLayer e l 0 3 s₀) = endpoint) :
    referenceJob (m := Id) (fun oa => evalTh H oa) F P
      ⟨.chainRow e l, [.chain bottomLayer e l (digit 0),
        .chain bottomLayer e l (digit 1), .chain bottomLayer e l (digit 2)]⟩ =
      bitsOfDigest cpk₁ ++ bitsOfDigest cpk₂ ++ bitsOfDigest endpoint := by
  rw [referenceJob_id]
  simp [refCore, hF₀, hF₁, hF₂, hwalk.1, hwalk.2.1, hwalk.2.2,
    ← BitVec.xor_assoc]
  change bitsOfDigest (s₁ ^^^ s₁ ^^^ cpk₁) ++
    (bitsOfDigest (s₂ ^^^ s₂ ^^^ cpk₂) ++ bitsOfDigest endpoint) = _
  simp

end SigningLaneHybridCapProof

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.referenceJob_row_of_walks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.referenceJob_row_of_walks

end ThresholdLeanXmssSecurity
