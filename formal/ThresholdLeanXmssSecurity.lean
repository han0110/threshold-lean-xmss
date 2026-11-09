import ThresholdLeanXmss.Statement
import ThresholdLeanXmssSecurity.Proof.Lemmas

namespace ThresholdLeanXmssSecurity

/-- Threshold leanXMSS meets its security claim. -/
theorem thresholdLeanXmss_security : ThresholdLeanXmss.ThresholdLeanXmssSecurityStatement := by
  sorry

/-! The build fails if the axiom footprint changes. Until the proofs merge, it holds `sorryAx`. When
no `sorry` remains, the footprint is `propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.thresholdLeanXmss_security' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdLeanXmss_security

end ThresholdLeanXmssSecurity
