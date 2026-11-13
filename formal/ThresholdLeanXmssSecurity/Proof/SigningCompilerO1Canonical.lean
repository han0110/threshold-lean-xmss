import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncSuffix
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTreeControl
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTrigger
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncBackend
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRealRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Release
import ThresholdLeanXmssSecurity.Proof.SigningReleasedAlign

/-! # The canonical digit and the gate of the O1 coupling

At the key of the forgery, a recorded digit is the selected digit of the final cache, unless the
final cache holds an alternative commitment opening. So a bottom chain position with `t` signers
and a recorded digit at or below it is no chain target. The same holds at the top layer for a
position at or above the top digit of a resolved bottom ceremony.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Canonical
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable

section Canonical
variable (prims : Primitives) (x : Keys3 C)

set_option maxRecDepth 100000 in
/-- The canonical digit. A successful codeword search below the final cache, at the key of
the forgery and at its bound message, gives the selected codeword, unless the final cache holds an
alternative commitment opening. -/
theorem canonical_digit (r : SigningCostProof.Outcome C) (top : TopTree) (state : TsigState C)
    (forgery : Forgery) (hm : r.1.2 = some (top, state, forgery))
    (htop : TopFacts prims (SigningCacheProof.answersOf r.2.1) x.2.1 x.1 top)
    (hn : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1)
    (receipt : SigningGuessProof.Round2Receipt C)
    (hr : SigningGuessProof.ReceiptRuns prims x top r.2.1 receipt)
    (he : receipt.key = forgery.signature.leafIndex)
    (hb : state.bound receipt.key = some receipt.message) :
    SigningDescentProof.selectedEncoding r.2.1 x.1 forgery.signature.leafIndex
      ((SigningCostProof.finalOf x r top state forgery).honestKey prims) = some receipt.encoding := by
  have hnm : ¬SigningGuessProof.OpeningMatch prims x r := fun h =>
    hn (SigningGuessProof.openingMatch_alternativeCommitment prims x r h)
  obtain ⟨hc, hgrind⟩ := SigningGuessProof.ReceiptRuns.canonical prims x r top state forgery hm htop
    receipt hr he hnm
  have hsel := SigningGuessProof.ReceiptRuns.selected prims
    (SigningCostProof.finalOf x r top state forgery) receipt hr he hb hc
  have hdecode := E_grind_spec (prims := prims) _ _ _ _ _ _ _ _ _ hgrind
  rw [SigningGuessProof.E_messageDigest_cache, XmssSecurity.Bridge.decode_eq] at hdecode
  unfold SigningDescentProof.selectedEncoding
  change ((SigningCostProof.finalOf x r top state forgery).selected prims).bind _ = _
  rw [hsel, Option.bind_some, ← he]
  exact hdecode

set_option maxRecDepth 100000 in
/-- The gate. At the key of the forgery, a position with `t` signers and a recorded digit
at or below it is not a chain target. Each recorded digit has a successful codeword search below
the final cache. -/
theorem covered_not_target (r : SigningGuessLinkProof.LoggedOutcome C) (top : TopTree)
    (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (htop : TopFacts prims (SigningCacheProof.answersOf r.2.1) x.2.1 x.1 top)
    (hn : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1)
    (starts : ChainIndex → Finset Digit)
    (htraced : ∀ l d, d ∈ starts l → ∃ receipt : SigningGuessProof.Round2Receipt C,
      receipt.key = forgery.signature.leafIndex ∧
      state.bound forgery.signature.leafIndex = some receipt.message ∧ receipt.encoding l = d ∧
      SigningGuessProof.ReceiptRuns prims x top r.2.1 receipt)
    (l : ChainIndex) (p : XmssSecurity.ChainStep)
    (hcov : ∃ m, state.bound forgery.signature.leafIndex = some m ∧
      C.t ≤ (signersAt state forgery.signature.leafIndex m).card ∧ ∃ d ∈ starts l, d.val ≤ p.val) :
    SigningGuessLinkProof.chainTarget prims x r (.bottomChain forgery.signature.leafIndex l p) = none := by
  obtain ⟨m, hbound, hcard, d, hd, hle⟩ := hcov
  obtain ⟨receipt, he, hb, henc, hruns⟩ := htraced l d hd
  have hsel := canonical_digit prims x (r.1.1, r.2) top state forgery hm htop hn receipt hruns he
    (by rw [he]; exact hb)
  have hrel : ((SigningCostProof.finalOf x (r.1.1, r.2) top state forgery).honestKey prims).released
      = true := by
    rw [SigningSupportProof.honestKey_released]
    unfold SigningSupportProof.releasedAt
    change (match state.bound forgery.signature.leafIndex with
      | some message => decide (C.t ≤ (signersAt state forgery.signature.leafIndex message).card)
      | none => false) = true
    rw [hbound]
    exact decide_eq_true hcard
  have hopen := SigningDescentProof.bottomOpened_of_released r.2.1 x.1
    forgery.signature.leafIndex _ hrel hsel
  simp only [SigningGuessLinkProof.chainTarget, hm]
  rw [if_neg]
  rintro ⟨-, hlt⟩
  change p.val < SigningDescentProof.bottomOpened r.2.1 x.1 forgery.signature.leafIndex _ l at hlt
  rw [hopen] at hlt
  have hlt' : p.val < (receipt.encoding l).val := hlt
  rw [henc] at hlt'
  omega

set_option maxRecDepth 100000 in
/-- The gate at the top layer. A resolved bottom ceremony of the tree of the forgery gives
the top digit. A position at or above it is no target of either kind. -/
theorem top_covered_not_target (r : SigningGuessLinkProof.LoggedOutcome C) (top : TopTree)
    (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (htop : D prims (SigningCacheProof.answersOf r.2.1)
      (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) = some (.top top))
    (tree : BottomTree)
    (hres : DeterministicSigning.Resolves r.2.1
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
        x.1 top (.bottom (treeOf forgery.signature.leafIndex))) (some (.bottom tree)))
    (encoding : XmssSecurity.Encoding)
    (hdec : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView r.2.1) x.1
        (XmssSecurity.topKeyOf forgery.signature.leafIndex)
        (tree.root, tree.topSignature.randomness)) = some encoding)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (hle : (encoding l).val ≤ p.val) :
    SigningGuessLinkProof.chainTarget prims x r
        (.topChain (XmssSecurity.topKeyOf forgery.signature.leafIndex) l p) = none ∧
      SigningTopRowsProof.unopenedTopTarget prims x r
        (.topChain (XmssSecurity.topKeyOf forgery.signature.leafIndex) l p) = none := by
  have hinput := SigningGuessProof.resolved_bottom_topSignedInput prims
    (SigningCostProof.finalOf x (r.1.1, r.2) top state forgery) tree htop hres
  have henc : SigningDescentProof.topEncoding r.2.1 x.1 forgery.signature.leafIndex
      ((SigningCostProof.finalOf x (r.1.1, r.2) top state forgery).honestKey prims) = some encoding := by
    unfold SigningDescentProof.topEncoding
    have hi : SigningDescentProof.topSignedInput r.2.1 x.1 forgery.signature.leafIndex
        ((SigningCostProof.finalOf x (r.1.1, r.2) top state forgery).honestKey prims) =
        (tree.root, tree.topSignature.randomness) := hinput
    rw [hi]
    exact hdec
  have hopen := SigningDescentProof.topOpened_of r.2.1 x.1 forgery.signature.leafIndex _ henc
  constructor
  · simp only [SigningGuessLinkProof.chainTarget, hm]
    rw [if_neg]
    rintro ⟨-, hlt⟩
    change p.val < SigningDescentProof.topOpened r.2.1 x.1 forgery.signature.leafIndex _ l at hlt
    rw [hopen] at hlt
    have hlt' : p.val < (encoding l).val := hlt
    omega
  · simp only [SigningTopRowsProof.unopenedTopTarget, hm]
    rw [if_neg]
    rintro ⟨-, hun, -⟩
    exact hun ⟨tree, hres⟩

end Canonical

end ThresholdLeanXmssSecurity.SigningCompilerO1Canonical

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Canonical.canonical_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Canonical.canonical_digit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Canonical.covered_not_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Canonical.covered_not_target

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Canonical.top_covered_not_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Canonical.top_covered_not_target
