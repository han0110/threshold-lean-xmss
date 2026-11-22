import ThresholdLeanXmssSecurity.Proof.SigningReleasedAlign
import ThresholdLeanXmssSecurity.Proof.SigningSignedSeparation
import ThresholdLeanXmssSecurity.Proof.SigningLaneInputLogged
import ThresholdLeanXmssSecurity.Proof.SigningLane2TraceLink

/-!
# Signing from the single capped lane

Actual released-selection alignment and signed-cache separation give the
released-partner link. Together with the logged-input and trace links, they
reduce `HiddenCoreAt` to the original `LaneTraceCap` on the same trace run.
-/

open ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningLaneFinal

variable {C : Committee} (prims : Primitives)

/-- The released-partner link for the actual signing game. -/
theorem releasedLink : SigningLinkPaidProof.ReleasedLink prims (C := C) :=
  SigningReleasedLinkProof.releasedLink_of_alignment_separation prims
    (SigningReleasedAlignProof.releasedSelectionAlignment prims)
    (SigningSignedSeparationProof.signedCacheSeparation prims)

/-- The one capped-lane estimate supplies the original hidden-core bound. -/
theorem hiddenCoreAt_of_laneTraceCap (cap : SigningLaneUnionProof.LaneTraceCap prims (C := C)) :
    SigningCoreProof.HiddenCoreAt prims C :=
  SigningLaneUnionProof.hiddenCoreAt_of_laneUnion prims (releasedLink prims)
    (SigningLaneInputLoggedProof.laneInputLogged prims)
    (SigningLane2TraceLinkProof.lane2TraceLink prims) cap

end ThresholdLeanXmssSecurity.SigningLaneFinal

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneFinal.releasedLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneFinal.releasedLink

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneFinal.hiddenCoreAt_of_laneTraceCap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneFinal.hiddenCoreAt_of_laneTraceCap
