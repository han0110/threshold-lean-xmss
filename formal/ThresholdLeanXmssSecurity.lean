import ThresholdLeanXmss.Statement
import ThresholdLeanXmssSecurity.Proof.Gadgets
import ThresholdLeanXmssSecurity.Proof.Tprf
import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.Tree

namespace ThresholdLeanXmssSecurity

/-- Threshold leanXMSS meets its security claim. -/
theorem thresholdLeanXmss_security : ThresholdLeanXmss.ThresholdLeanXmssSecurityStatement := by
  intro C E _ _ _ _ K prims circuits settings
  letI : SampleableType E := SampleableType.ofFintype E
  exact ⟨keygenCompleteness prims, keygenSecurity prims, treeCompleteness prims K circuits settings,
    treeSecurity prims K circuits settings, dealerTree prims circuits settings,
    treeSuccess prims circuits settings, coinSecurity prims K, coinCompleteness prims K, multStatement prims K,
    extendMultSecurity prims K, multVerifyStatement prims K, multVerifyCompleteness prims K,
    mainStatement prims K, mainCompleteness prims K, tprfCorrectness prims C, tprfSecurity prims C,
    signingCorrectness prims C, signingSecurity prims C⟩

/-! The build fails if the axiom footprint changes. The open claims hold `sorryAx`. When no `sorry`
remains, the footprint is `propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.thresholdLeanXmss_security' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdLeanXmss_security

/-! The proved claims depend only on `propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.keygenCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenCompleteness

/-- info: 'ThresholdLeanXmssSecurity.treeCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCompleteness

/-- info: 'ThresholdLeanXmssSecurity.coinSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinSecurity

/-- info: 'ThresholdLeanXmssSecurity.coinCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinCompleteness

/-- info: 'ThresholdLeanXmssSecurity.multStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multStatement

/-- info: 'ThresholdLeanXmssSecurity.extendMultSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extendMultSecurity

/-- info: 'ThresholdLeanXmssSecurity.multVerifyCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multVerifyCompleteness

/-- info: 'ThresholdLeanXmssSecurity.mainCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainCompleteness

/-- info: 'ThresholdLeanXmssSecurity.tprfCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tprfCorrectness

/-- info: 'ThresholdLeanXmssSecurity.tprfSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tprfSecurity

/-- info: 'ThresholdLeanXmssSecurity.signingCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCorrectness

end ThresholdLeanXmssSecurity
