# formal

Lean 4 statements and proofs of the security claims of threshold leanXMSS: the DKG and each tree ceremony are secure with selective abort against a static coalition, the threshold PRF and the signing are secure against an adaptive coalition, and the signing is strongly unforgeable. The claims are stated in the paper model of the protocol, in the random-oracle model, and the keygen and ceremony claims fix `Th` to the function that the MPC circuits compute. What is claimed, and what is not, is [statement.tex](./statement.tex). A claim counts as proved when the axiom guard of the root theorem lists only `propext`, `Classical.choice` and `Quot.sound`.

Key files: [Statement/Theorems.lean](./ThresholdLeanXmss/Statement/Theorems.lean) (the bundle of the claims and the model, the entry file of the folder `Statement/` that a reviewer reads) and [ThresholdLeanXmssSecurity.lean](./ThresholdLeanXmssSecurity.lean) (the root theorem and the route of its proof).

```sh
cd formal
lake build   # build every module and check the axiom guards of the root file
```

## The bridge

The proof moves from Lean 4.31, VCVio `cbd4144` and leanVM `1acdff19` to Lean 4.35, VCVio `5f9baf12` and leanVM `f5f3672f`. The bridge shows that each claim of the statement layer keeps its meaning in this move. The folder [ThresholdLeanXmssSecurity/Bridge](./ThresholdLeanXmssSecurity/Bridge) holds four files. They state in elementary terms what the probability terms, the handlers, the leanVM names and the leanXMSS functions of the statement layer are. This folder is the old side, for the old revisions. The branch of the move has the new side at the same paths, with the same statements proved for the new revisions. The root file does not import the bridge, so build its four modules by name.

```sh
cd formal
lake build ThresholdLeanXmssSecurity.Bridge.Characterization ThresholdLeanXmssSecurity.Bridge.Handlers \
  ThresholdLeanXmssSecurity.Bridge.Ambient ThresholdLeanXmssSecurity.Bridge.LeanXmss
```

The script [tools/bridge_compare.py](./tools/bridge_compare.py) compares the text of the two sides. It prints each difference, and its exit code is 1 if a difference exists. The two sides differ by design only in the rows of the three tables in the script and in the bodies of the dictionaries that the script prints. A person must read these parts. The script also compares the copies of `LeanXmss.lean` with the source of leanVM `1acdff19`, and it reads that source from the folder `.lake` of the project that holds the old side. The second command runs the tests of the script.

```sh
python3 formal/tools/bridge_compare.py --old formal/ThresholdLeanXmssSecurity/Bridge --new <branch>/formal/ThresholdLeanXmssSecurity/Bridge
python3 formal/tools/bridge_compare_test.py --old formal/ThresholdLeanXmssSecurity/Bridge --new <branch>/formal/ThresholdLeanXmssSecurity/Bridge
```
