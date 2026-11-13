# formal

Lean 4 statements and proofs of the security claims of threshold leanXMSS: the DKG and each tree ceremony are secure with selective abort against a static coalition, the threshold PRF and the signing are secure against an adaptive coalition, and the signing is strongly unforgeable. The claims are stated in the paper model of the protocol, in the random-oracle model, and the keygen and ceremony claims fix `Th` to the function that the MPC circuits compute. What is claimed, and what is not, is [statement.tex](./statement.tex). A claim counts as proved when the axiom guard of the root theorem lists only `propext`, `Classical.choice` and `Quot.sound`.

Key files: [Statement.lean](./ThresholdLeanXmss/Statement.lean) (the claims, the one Lean file a reviewer reads) and [ThresholdLeanXmssSecurity.lean](./ThresholdLeanXmssSecurity.lean) (the root theorem and the route of its proof).

```sh
cd formal
lake build   # build every module and check the axiom guards of the root file
```
