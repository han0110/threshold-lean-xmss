# formal

Lean 4 statements and proofs of security claims of threshold leanXMSS.

## The two main claims

The root theorem proves the bundle `Theorems`. Its 17 fields serve two main claims.

| Main claim | Fields of the bundle | State |
| --- | --- | --- |
| The DKG acts as a trusted dealer of the keys and the trees | `keygenSecurity` and `keygenCompleteness` for the keygen. `treeCompleteness`, `dealerTree` and `treeSuccess` for a tree ceremony. | **Not complete.** The keygen part is proved. The security of a tree ceremony is not. |
| The signing with that dealer is correct and strongly unforgeable | `signingCorrectness` and `stronglyUnforgeable`, with the threshold PRF (`tprfCorrectness`, `tprfSecurity`) | Proved |

The other eight fields are lemmas on the gadgets of the DKG. They are `coin`, `mult`, `extendMult`, `multVerify` and `main`, and the honest runs `coinCompleteness`, `multVerifyCompleteness` and `mainCompleteness`.

## What is proved

- The keygen is secure with selective abort against a static coalition.
- The threshold PRF is secure against an adaptive coalition.
- The signing is strongly unforgeable with adaptive corruption.
- The gadgets of the DKG are secure, and each honest run gives its output, except with the failure probability that its claim names.
- An honest tree ceremony gives the tree of its dealer, except with the failure probability that its claim names. When the circuits compute `Th`, that dealer gives the trees of the signing claim.

The claims are stated in the paper model of the protocol, in the random-oracle model, and the keygen and ceremony claims fix `Th` to the function that the MPC circuits compute. The axiom guard of the root theorem lists only `propext`, `Classical.choice` and `Quot.sound`, and it covers the claims of the bundle only.

## What is not proved

One important claim has no proof. `TreeSecurityStatement` says that each tree ceremony of the DKG is secure with selective abort. It is stated in Lean, no theorem proves it, and it is no part of the bundle. So the first main claim is proved for the keygen and for the gadgets, and it is not proved for a full ceremony that builds a tree.

No claim composes the keygen, the ceremonies and the signing. Each claim covers one protocol or one gadget alone. So no single theorem states a main claim of the table, or the two together.

What is claimed, and what is not, is [statement.tex](./statement.tex).

## Key files

- [Statement/Theorems.lean](./ThresholdLeanXmss/Statement/Theorems.lean) is the bundle of the claims and the model. It is the entry file of the folder `Statement/` that a reviewer reads.
- [ThresholdLeanXmssSecurity.lean](./ThresholdLeanXmssSecurity.lean) is the root theorem and the route of its proof.

```sh
cd formal
lake build   # build every module and check the axiom guards of the root file
```
