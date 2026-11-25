# formal

Lean 4 statements and proofs of the security claims of threshold leanXMSS. Four of the five claims are proved. The fifth, `dkgSecurityPreservation`, has a proof of its cost bound and of twelve of the 13 hops of its win bound.

## The claims

The structure `Theorems` in [Statement/Theorems.lean](./ThresholdLeanXmss/Statement/Theorems.lean) has five fields. Each field is a game with a fixed bound. [statement.tex](./statement.tex) is the guide to the claims.

| Field | Claim | Model in the papers | State |
| --- | --- | --- | --- |
| `stronglyUnforgeable` | Signing with a trusted dealer is strongly unforgeable with adaptive corruption. | PRAWNS, Definition 3.2 | Proved |
| `signingCorrectness` | An honest quorum signs, except for a failed search. | PRAWNS, Section 3.1 | Proved |
| `dkgSecurityPreservation` | The real DKG gives an adversary no more than the dealer gives the named forger `dkgReduction`, up to a fixed error. | Gurkan and others, Definition 8 | Cost bound proved, win bound open |
| `dkgCorrectness` | Against an adversary, honest operators hold consistent seeds, each tree output is right or absent, and the honest operators keep the output of a run together or not at all. | Gurkan and others, Definition 6, and Goldwasser and Lindell, Definition 3 | Proved |
| `dkgCompleteness` | With no corrupt operator, the DKG gives outputs that are near the outputs of the dealer. | None | Proved |

- Each proved field has a theorem with its name, in the namespace `ThresholdLeanXmssSecurity`.
- The one exception is `SigningStronglyUnforgeable.stronglyUnforgeable`.
- The coalition of the DKG is static, and the signing game has adaptive corruption.
- The seed generation and each run of a tree end with one vote on a broadcast channel, so the abort of the DKG is unanimous.
- The claims of the DKG fix the function `Th`, and `stronglyUnforgeable` has `Th` in the random oracle.

## The state of `dkgSecurityPreservation`

| Part | Proof | State |
| --- | --- | --- |
| The cost bound of the forger | `dkgReduction_cost` | Proved |
| Twelve hops of the chain, with the hop to the forger | `tableHop` and eleven more | Proved |
| The hop `SharedStep`, in which one real run of a tree becomes an emulated run | None | Open |
| The field from `SharedStep` | `dkgSecurityPreservation_of_leaves` | Proved |
| All five claims from `SharedStep` | `theorems_of_sharedStep` | Proved |

- The win bound is a target until `SharedStep` has a proof, so a proof can change it.
- The error `dkgError` is the sum of the errors of the 13 hops.
- [doc/model.md](./doc/model.md), Section 4, lists the hops.

## Map of the claims

<!-- Update this map when a field of the bundle changes or a claim is proved. -->

- Green is proved in this tree.
- Orange is stated with a target bound.
- Grey is an assumption.
- The dashed box has no Lean statement.

```mermaid
flowchart TB
  classDef proved fill:#d4edda,stroke:#2e7d32,color:#000
  classDef target fill:#ffe0b2,stroke:#e65100,color:#000
  classDef assumed fill:#e9ecef,stroke:#6c757d,color:#000
  classDef remark fill:#ffffff,stroke:#6c757d,stroke-dasharray:5 5,color:#000

  subgraph SIG["Signing with the trusted dealer"]
    SUF["stronglyUnforgeable<br/>tsigGame in signingWorld,<br/>adaptive corruption"]:::proved
    SCOR["signingCorrectness<br/>honest quorum in world"]:::proved
  end

  subgraph DKG["Setup by DKG on the real network, static coalition"]
    DSEC["dkgSecurityPreservation<br/>dkgTsigGame to tsigGame for dkgReduction,<br/>both in world with the fixed Th"]:::target
    DCOR["dkgCorrectness<br/>dkgTreeGame"]:::proved
    DCOMP["dkgCompleteness<br/>honestDkg near dealerDkg"]:::proved
  end

  E2E["Bound of dkgTsigGame<br/>the end-to-end remark of statement.tex"]:::remark
  DELTA["A bound of tsigGame in world for dkgReduction,<br/>with the fixed Th"]:::assumed
  HEUR["Random-oracle heuristic for Th<br/>used one time"]:::assumed
  RULES["Deployment contract<br/>the 4 rules of statement.tex"]:::assumed

  style SIG fill:none,stroke:#999999
  style DKG fill:none,stroke:#999999

  E2E --> DSEC
  E2E -->|premise| DELTA
  DELTA -.->|no theorem| HEUR
  HEUR -.-> SUF
  DSEC -->|rules are code of the game| RULES
  SUF -->|rules 1 and 4| RULES
```

The dashed box is the end-to-end bound of `dkgTsigGame`.

- A bound δ on the success of `dkgReduction` in `tsigGame`, in `world` with the fixed `Th`, gives δ plus `dkgError` plus `streamAdvantage`.
- No field gives such a δ. No small δ holds for each query-bounded adversary with a fixed `Th`.
- To take the bound of `stronglyUnforgeable` for δ is the random-oracle heuristic for `Th`. It applies to an adversary that makes no search on `Th`.

## Files

| File | Content |
| --- | --- |
| [ThresholdLeanXmss/Statement/Theorems.lean](./ThresholdLeanXmss/Statement/Theorems.lean) | The bundle `Theorems` and the model. The entry file. |
| [ThresholdLeanXmss/Statement/Signing.lean](./ThresholdLeanXmss/Statement/Signing.lean) | `tsigGame` and the two signing claims |
| [ThresholdLeanXmss/Statement/DkgGame.lean](./ThresholdLeanXmss/Statement/DkgGame.lean) | `dkgTsigGame`, `dkgTreeGame`, `honestDkg` and `dealerDkg` |
| [ThresholdLeanXmss/Statement/Dkg.lean](./ThresholdLeanXmss/Statement/Dkg.lean) | `CircuitsCompute` and the three claims of the DKG, with their adaptations of the papers |
| [ThresholdLeanXmss/Statement/DkgErrors.lean](./ThresholdLeanXmss/Statement/DkgErrors.lean) | The error and cost terms of the three claims of the DKG |
| [ThresholdLeanXmss/Statement/DkgReduction.lean](./ThresholdLeanXmss/Statement/DkgReduction.lean) | `dkgReduction`, the named forger of `dkgSecurityPreservation` |
| [ThresholdLeanXmss/Statement/RandomOracle.lean](./ThresholdLeanXmss/Statement/RandomOracle.lean) | `world`, `signingWorld` and the count of the calls |
| [ThresholdLeanXmss/Statement/Execution.lean](./ThresholdLeanXmss/Statement/Execution.lean) | The execution of a protocol on the network |
| [ThresholdLeanXmss/Scheme.lean](./ThresholdLeanXmss/Scheme.lean) | The protocol, the oracles and the dealer `dealerKeyGen` |
| [ThresholdLeanXmss/Ideal.lean](./ThresholdLeanXmss/Ideal.lean) | The oracles of the signing game and its win test |
| [ThresholdLeanXmss/Reductions.lean](./ThresholdLeanXmss/Reductions.lean) | `prgReduction`, the fixed reduction of the PRF term |
| [ThresholdLeanXmssSecurity.lean](./ThresholdLeanXmssSecurity.lean) | The root of the proof library. It has `theorems_of_sharedStep`, and it checks the axioms of that theorem and of the four proved field theorems. |
| [ThresholdLeanXmssSecurity/Proof/](./ThresholdLeanXmssSecurity/Proof/) | The proofs |
| [ThresholdLeanXmssSecurity/Base/](./ThresholdLeanXmssSecurity/Base/) | The definitions that the proofs use and that the statement layer does not hold |
| [statement.tex](./statement.tex) | The guide to the claims |
| [doc/model.md](./doc/model.md) | The model of the five claims |
| [doc/differences.md](./doc/differences.md) | Each difference to GS20, PRAWNS, the note, leanXMSS and Gurkan and others |

## Build

```sh
cd formal
lake build   # build both default targets, ThresholdLeanXmss and ThresholdLeanXmssSecurity
```

The root module fails the build unless the four proved field theorems and `theorems_of_sharedStep` depend only on `propext`, `Classical.choice` and `Quot.sound`.
