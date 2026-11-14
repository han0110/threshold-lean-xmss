# formal

Lean 4 statements and proofs of security claims of threshold leanXMSS. The root theorem proves the bundle `Theorems`. Its claims are these. The keygen is secure with selective abort against a static coalition. The threshold PRF is secure against an adaptive coalition. The signing is strongly unforgeable with adaptive corruption. The gadgets of the DKG are secure, and each honest run gives its output. The claim that each tree ceremony is secure with selective abort is stated as `TreeSecurityStatement`. No theorem proves it, and it is no part of the bundle. The claims are stated in the paper model of the protocol, in the random-oracle model, and the keygen and ceremony claims fix `Th` to the function that the MPC circuits compute. What is claimed, and what is not, is [statement.tex](./statement.tex). The axiom guard of the root theorem lists only `propext`, `Classical.choice` and `Quot.sound`, and it covers the claims of the bundle only.

Key files: [Statement/Theorems.lean](./ThresholdLeanXmss/Statement/Theorems.lean) (the bundle of the claims and the model, the entry file of the folder `Statement/` that a reviewer reads) and [ThresholdLeanXmssSecurity.lean](./ThresholdLeanXmssSecurity.lean) (the root theorem and the route of its proof).

```sh
cd formal
lake build   # build every module and check the axiom guards of the root file
```

## The bridge

The proof moved from Lean 4.31, VCVio `cbd4144` and leanVM `1acdff19` to Lean 4.35, VCVio `5f9baf12` and leanVM `f5f3672f`. The bridge shows that each claim of the statement layer kept its meaning in this move. The folder [ThresholdLeanXmssSecurity/Bridge](./ThresholdLeanXmssSecurity/Bridge) holds four files. They state in elementary terms what the probability terms, the handlers, the leanVM names and the leanXMSS functions of the statement layer are. This folder is the new side, for the present revisions. The old side is at the same paths at commit `fddaa63`, with the same statements proved for the old revisions. The root file does not import the bridge. `lake build` builds its four modules, because the project builds every module.

The script [tools/bridge_compare.py](./tools/bridge_compare.py) compares the text of the two sides. It prints each difference, and its exit code is 1 if a difference exists. The two sides differ by design only in the rows of the three tables in the script and in the bodies of the dictionaries that the script prints. A person must read these parts. The script also compares the copies of `LeanXmss.lean` of the old side with the source of leanVM `1acdff19`. With the option `--old-commit`, it reads the old side from that commit of this repository, and it reads the old source of leanVM from the git history of the package in the folder `.lake`. The second command runs the tests of the script.

```sh
cd formal
python3 tools/bridge_compare.py --old-commit fddaa63 --new ThresholdLeanXmssSecurity/Bridge
python3 tools/bridge_compare_test.py --old-commit fddaa63 --new ThresholdLeanXmssSecurity/Bridge
```

The bridge covers the move of the upstream definitions only. After the move, the model got two changes of meaning that the bridge does not cover, so that it agrees with the code. The check field has `2^128` elements, and the key of a coin hashes two opened values.
