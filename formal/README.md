# formal

Lean 4 proofs of the security claims of threshold leanXMSS. The claims are those of [Statement.lean](./ThresholdLeanXmss/Statement.lean). The DKG and each tree ceremony are secure with selective abort against a static coalition, and the signing is strongly unforgeable against an adaptive coalition. They hold in the paper model of the protocol, in the random-oracle model. The keygen, ceremony and lifetime claims fix `Th` to the function that the MPC circuits compute. `Statement.lean` is the one file a reviewer reads.

Key file: [ThresholdLeanXmssSecurity.lean](./ThresholdLeanXmssSecurity.lean)

```sh
cd formal
lake build   # build every module and check the axiom guards of the root file
```
