# formal

The claims are [`ThresholdLeanXmss/Statement.lean`](ThresholdLeanXmss/Statement.lean), the one file a reviewer reads. This file is for contributors and agents. The root module `ThresholdLeanXmssSecurity.lean` and the module docstrings say how each proof goes.

## The repository

- One Lake project with two libraries.
  - `ThresholdLeanXmss/` is the statement layer. `Scheme.lean` holds the protocol and the world, `Ideal.lean` the functionalities and the games, `Reductions.lean` the simulators and the reductions, and `Statement.lean` the claims as named `Prop`s.
  - `ThresholdLeanXmssSecurity/` holds the proofs, under `Proof/`. The root `ThresholdLeanXmssSecurity.lean` proves `thresholdLeanXmss_security : ThresholdLeanXmssSecurityStatement` and holds the axiom guards.
- `lakefile.toml` pins the leanVM proof `formal/lean_xmss` (package `lean-xmss-security`) and VCVio. PolyFun comes in as a dependency of these packages, at the revision of `lake-manifest.json`.
- The structure and the style follow leanVM `formal/lean_xmss`.

## Hard rules

- No `sorry`, `axiom`, `admit` or `native_decide`.
- Each new proof file ends with `#guard_msgs` checks on `#print axioms` that list only `propext`, `Classical.choice` and `Quot.sound`.
- `Statement.lean` changes only after the owner agrees. Every bound in it is a fixed expression. The prover never chooses an error, an adversary class or an advantage.
- Never weaken a claim. Prove at least the strongest property that each source paper proves.
- The DKG follows Goyal and Song (GS20) with static corruption, secure with selective abort in the simulation framework of Canetti 2000 and Goldwasser and Lindell 2005. The signing follows PRAWNS, Definition 2.2 and Definition 3.2, with adaptive corruption and strong unforgeability.
- Never invent a definition, a model or an argument. Bound each hash-dependent term by a counted oracle as `q / 2^bits`.
- Before a proof, check that the target is true and that the route is clear. If the target is false, write a concrete counterexample in the module doc and stop.
- A named remainder must be strictly smaller than the target. The lemmas of the file must reduce the target to it. It is never a restatement, a projection with its own witness, or a `Prop` that a dummy witness satisfies.
- Module docs say what a lemma or a `Prop` states. They never record progress.

## Reuse

Search before you write a lemma. Import or port it instead of proving it again.

- leanVM. Import from the pin `.lake/packages/lean-xmss-security/formal/lean_xmss/XmssSecurity` with qualified names, never `open XmssSecurity`. Read ideas from the newer checkout `/home/han/playground/arg/leanVM/formal/lean_xmss`.
- VCVio, pinned in `.lake/packages/VCVio`, newer checkout `/home/han/playground/arg/VCVio`. It holds `ProgramLogic` (relational triples, identical-until-bad), `CryptoFoundations` (hybrids, random-oracle and PRF lemmas), `StateSeparating` (package-style hybrids), and `OracleComp` and `EvalDist` (query bounds, probability).
- PolyFun, pinned in `.lake/packages/PolyFun`, checkout `/home/han/playground/arg/PolyFun`.
- Ideas only from `/home/han/playground/arg/ArkLib` and `/home/han/playground/arg/CompPoly` (each with `blueprint/`), for polynomial and field facts, oracle reductions and soundness arguments.
- Import only from the pinned packages. Port a missing lemma verbatim with a source comment. Do not bump a pin.

## Commands

Run from `formal/`.

```sh
lake env lean -M8192 -j1 <file>   # check one file
lake build <Module>               # build one module and what it imports
lake build                        # build every module, the full gate
```
