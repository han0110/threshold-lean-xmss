import ThresholdLeanXmssSecurity.Proof.SeedHit
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The hidden core of the signing security

`HiddenCoreAt` of `Proof/SigningCore.lean` (steps 2 to 6 of the signing plan of `formal/PROOF.md`)
and the full signing claim `signingSecurityFull`.

Open stage, the hypothesis of `signingSecurityFull`:

* `HiddenCoreAt`: for fixed distinct keys, a win without the flag costs `signingHashError q`.

What it still needs, in the order of the plan:

1. A logged run of `runSigningWorld` (every call with its copy and its answer), equal to the run
   after the log is forgotten, as `simulateQ_run_forget`.
2. The positions of the inputs of `Th` and the honest input of each position. A digest position has
   several honest trials of `grind`, and only the selected one is a target.
3. The descent over two layers: a verified fresh forgery without the flag gives a hit, a guess or a
   partner in the log. leanVM does this in `OutcomeClassification` and `ConcreteForgery`, which this
   project does not build.
4. The costs. The digest partner bound is one unit for each digest call, because `ρ_e` stays hidden
   until round 1 binds the message, so `R_0` is fresh and the selected output is uniform over the
   codewords. A bound of one unit for each pair is false.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

/-- `SigningSecurityStatement` from the open stage `HiddenCoreAt`, with `seedHitBound` proved. -/
theorem signingSecurityFull (prims : Primitives) (C : Committee) (hiddenCoreAt : HiddenCoreAt prims C) :
    SigningSecurityStatement prims C :=
  signingSecurityProof prims C (signingCoreBound prims C (seedHitBound prims C) hiddenCoreAt)

/-- info: 'ThresholdLeanXmssSecurity.signingSecurityFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingSecurityFull

end ThresholdLeanXmssSecurity
