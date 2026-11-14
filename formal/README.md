# formal

Lean 4 statements and proofs of security claims of threshold leanXMSS. The root theorem proves the bundle `Theorems`. Its claims are these. The keygen is secure with selective abort against a static coalition. The threshold PRF is secure against an adaptive coalition. The signing is strongly unforgeable with adaptive corruption. The gadgets of the DKG are secure, and each honest run gives its output, except with the failure probability that its claim names. The claim that each tree ceremony is secure with selective abort is stated as `TreeSecurityStatement`. No theorem proves it, and it is no part of the bundle. The claims are stated in the paper model of the protocol, in the random-oracle model, and the keygen and ceremony claims fix `Th` to the function that the MPC circuits compute. What is claimed, and what is not, is [statement.tex](./statement.tex). The axiom guard of the root theorem lists only `propext`, `Classical.choice` and `Quot.sound`, and it covers the claims of the bundle only.

Key files: [Statement/Theorems.lean](./ThresholdLeanXmss/Statement/Theorems.lean) (the bundle of the claims and the model, the entry file of the folder `Statement/` that a reviewer reads) and [ThresholdLeanXmssSecurity.lean](./ThresholdLeanXmssSecurity.lean) (the root theorem and the route of its proof).

```sh
cd formal
lake build   # build every module and check the axiom guards of the root file
```
