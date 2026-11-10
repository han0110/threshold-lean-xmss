import ThresholdLeanXmss.Statement
import ThresholdLeanXmssSecurity.Proof.Gadgets
import ThresholdLeanXmssSecurity.Proof.Tprf
import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.MainStages
import ThresholdLeanXmssSecurity.Proof.CheckFinish
import ThresholdLeanXmssSecurity.Proof.KeygenFinish
import ThresholdLeanXmssSecurity.Proof.TreeKey
import ThresholdLeanXmssSecurity.Proof.HiddenCore
import ThresholdLeanXmssSecurity.Proof.KeygenKnown
import ThresholdLeanXmssSecurity.Proof.TreeKeyAfter
import ThresholdLeanXmssSecurity.Proof.CheckLast
import ThresholdLeanXmssSecurity.Proof.SigningCache
import ThresholdLeanXmssSecurity.Proof.SigningHitLane
import ThresholdLeanXmssSecurity.Proof.SigningGuessLane

namespace ThresholdLeanXmssSecurity

/-- Threshold leanXMSS meets its security claim. -/
theorem thresholdLeanXmss_security : ThresholdLeanXmss.ThresholdLeanXmssSecurityStatement := by
  intro C E _ _ _ _ K prims circuits settings
  letI : SampleableType E := SampleableType.ofFintype E
  exact ⟨keygenCompleteness prims, keygenSecurityDone_of_programAlias prims (by sorry), treeCompleteness prims K circuits settings,
    treeSecurityOfSimAimed prims K circuits settings (by sorry) (by sorry),
    dealerTreeProof prims circuits settings C,
    treeSuccessProof prims circuits settings C, coinSecurity prims K, coinCompleteness prims K, multStatement prims K,
    extendMultSecurity prims K, multVerifyOfSplitRoute prims K (by sorry) (by sorry), multVerifyCompleteness prims K,
    mainStatementFull prims K, mainCompleteness prims K, tprfCorrectness prims C, tprfSecurity prims C,
    signingCorrectness prims C, signingSecurityFull prims C (by sorry)⟩

/-! The build fails if the axiom footprint changes. The open claims hold `sorryAx`. When no `sorry`
remains, the footprint is `propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.thresholdLeanXmss_security' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdLeanXmss_security

/-! The proved claims depend only on `propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.dealerTreeProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerTreeProof

/-- info: 'ThresholdLeanXmssSecurity.treeSuccessProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSuccessProof

/-- info: 'ThresholdLeanXmssSecurity.mainStatementFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainStatementFull

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
