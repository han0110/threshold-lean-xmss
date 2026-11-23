# The game model

This file describes the model of the five claims of the bundle `Theorems`. Each claim is a game with a fixed error expression. No claim uses a simulation definition or a composition theorem. The two signing claims, `dkgCorrectness` and `dkgCompleteness` are proved in this tree. The claim `dkgSecurityPreservation` is stated. Its cost bound is proved, and no proof of its bound on the win probability is in this tree.

[statement.tex](../statement.tex) has the tables of the claims, of their worlds, preconditions and trivial cases (Section 1 and Section 3.2), of the state of each bound (the first table and Section 3.2), and of the error terms with their Lean names (Appendix B). The adaptations of the published definitions are in [differences.md](./differences.md), Table B.3, and in the doc comment of each claim.

## 1. The worlds and the place of the heuristic

`RandomOracle.lean` has two worlds, `world` and `signingWorld`. Each world has a counted copy and a free copy of the oracles on one cache. The adversary calls the counted copy, and the honest operators and the dealer call the free copy. Each constructor of `Query` is one domain of $H$. In `world`, $\mathrm{Th}$ is the fixed function `prims.Th` on the inputs that the MPC evaluates (`MpcInput`), and a call of it costs nothing. In `signingWorld`, all of $H$ is a lazy random oracle.

The inner counter of `signingWorld` counts the calls on both copies. The claim `stronglyUnforgeable` does not read that counter. Its budget $q$ counts only the own calls and the round-2 requests of the forger (`adversaryCost`, `QueryCostAtMost`).

Each field of the setup has the premise `CircuitsCompute circuits prims.Th` for the `prims` of the bundle, and `ThresholdLeanXmssSecurityStatement` quantifies over each `prims`. The MPC evaluates $\mathrm{Th}$ by a circuit, and a random oracle has no circuit. So the claims of the setup need the fixed $\mathrm{Th}$.

`dkgSecurityPreservation` names its reduction, the forger `dkgReduction` of `Statement/DkgReduction.lean`. It reads only `prims.aes` from `prims`. It runs the adversary and plays the honest operators, with the coalition keys from `corrupt` and an own table for the domains of $H$ that only the setup uses. Its openings are shifted, and outside the bad events of consistency and soundness they give the outputs of the dealer. It sends the tree requests to the dealer.

Its emulated operators make no randomizer search. They take the randomizer of the top signature from the answer of `tree b` and get the codeword from one hash.

The forger forwards a signing request when the emulated operator holds keys, a top tree and an output of the bottom tree. It runs the forger of the adversary when an honest operator holds a top tree and outputs `idleForgery` if not.

The claim names the forger because $\mathrm{Th}$ is fixed and an adversary has no bound on its computation. A search on $\mathrm{Th}$ costs no call, so a claim that some forger exists is empty.

With the named forger, the claim says that the real setup gives an adversary no more than `tsigGame` gives `dkgReduction`, up to the stated errors `dkgError` and `streamAdvantage`. It is a relative claim and no bound on a forgery. [statement.tex](../statement.tex), Section 3.2, lists what a reader checks in its code.

The code of the forger differs from the game in five points. Each point is an obligation of the proof, and it needs a coupling or a bad event with a bound.

| Point | Difference |
| --- | --- |
| The key of `forge` | The forger gives `forge` the public key and the top tree of the dealer, not those of the first honest holder of a top tree. |
| A failed search of the dealer | `tree b` gives no tree and the forger runs no tree run, but the state of the dealer game changed. |
| An early tree request | The forger asks `tree b` also when no run is allowed, so the dealer builds that bottom tree earlier than the game does. |
| No randomizer search | The emulated operators of a bottom run make no randomizer search. They take the result of the dealer. |
| A wrong emulated output | A signing request to an emulated operator with an output of the bottom tree goes to the dealer, also when that emulated output is wrong. |

- The chain of hops covers all five points, on the condition that `SharedStep` holds at `privacyStepError` (Section 4).
- For the second point, the bound must cover the first divergence that the adversary can see.
- For the fourth point, take the same public parameter and the same hash oracle, and outputs of the first ceremony that are those of the dealer.
- Then the result of the dealer is the result that the search of the game gives.

Let $\delta$ bound the probability that `dkgReduction` of an adversary $A$ wins `tsigGame` in `world` with the fixed $\mathrm{Th}$. Then `dkgSecurityPreservation` gives a bound of `dkgTsigGame`.

$$\Pr[A \text{ wins } \mathsf{dkgTsigGame}] \le \delta + \mathsf{dkgError}(q) + \mathsf{streamAdvantage}$$

No field of `Theorems` gives such a $\delta$. No small $\delta$ holds for each query-bounded adversary with a fixed $\mathrm{Th}$, because a search on $\mathrm{Th}$ costs no call. `stronglyUnforgeable` bounds `tsigGame` in `signingWorld`. To take its bound for $\delta$, for an adversary that makes no search on $\mathrm{Th}$, is the random-oracle heuristic for $\mathrm{Th}$. So no theorem joins `dkgSecurityPreservation` and `stronglyUnforgeable`.

The next numbers illustrate the bound and are no claim. Take $t=3$, $n=5$ and a run limit of 1. Then `dkgOverhead` is 75 248 651 468 795, about $2^{46.10}$.

- The first term of the signing bound, $(q+2^{15}+384)/2^{127}$, is linear in the cost.
- At the cost of the forger, $q$ plus `dkgOverhead`, the term is about $2^{-80.9}$ for an adversary with few calls.
- At $2^{64}$ calls the overhead has no weight, and the term is $2^{-63.0}$.
- The floor near $2^{-81}$ is a property of the bound and no attack.
- Its cause is that the signing claim counts each hash call of the forger, also its honest PRF calls.

## 2. The game with the real setup

`dkgTsigGame` (`Statement/DkgGame.lean`) is the signing game of PRAWNS, Figure 3, with the real setup in the place of `dealerKeyGen`.

| Point | Model |
| --- | --- |
| The adversary | One adversary `DkgTsigAdversary` with one state plays a static coalition `D` of fewer than $t$ operators. `net` plays the corrupt operators in each run on the network. `forge` is the forger of the signing phase. It reads and writes the state of `net` by `StateSpec`. |
| The setup | The seed generation, the top tree and each bottom tree run as the real protocols on the network (`realExecution`, `executePhase`). No functionality is on the real side. |
| The inputs | The code of the game makes the inputs of each run from the outputs of the earlier runs. Each operator runs `newTree` on its own keys and its own top tree (`treeProgram`). |
| An abort | Each honest operator keeps its own keys and the first output of its own runs of each tree (`OperatorState`). A run of the top tree needs local keys, and a run of a bottom tree also needs a local top tree. The game has no agreement step. |
| The runs of a tree | The top tree runs at most `runLimit` times, while an honest operator has no top tree. The adversary asks for each run of a bottom tree by `tree b`. A bottom tree runs at most `runLimit` times, and the first signing request on it ends its runs (`mayRun`). |
| The signing phase | The public key and the top tree are those of the first honest operator that holds a top tree. With no such operator, the adversary does not win. `corrupt` gives nothing, because the coalition is corrupt from the start. Each honest operator answers `round1` and `round2` only with its own keys and trees (`operatorAnswer`). |
| The win | `forgeryWins` of the signing game on `canonicalDealt`, which has the keys of each operator, $F$ on the seeds of the game and the first held output of each bottom tree. |
| The count | The budget $q$ counts the own calls of the adversary (`DkgTsigBounded`). The honest operators call the free copy of $H$. The adversary has no bound on its computation. |

`DkgTsigBounded A q` asks for three numbers `start`, `step` and `forge`, with `start + dkgTsigRounds * step + forge ≤ q`. The start of `net` makes at most `start` calls of $H$ and PRG, each round of `net` at most `step`, and `forge` has cost at most `forge` on every path. A round-2 request of `forge` costs one, as in `stronglyUnforgeable`. `dkgTsigRounds` is the most rounds of one game, namely `setupRounds + runLimit * (1 + 2 ^ layerHeight) * treeFuel`.

`dkgTreeGame` runs the same game with a monitor. Its output is a flag. The flag holds when two honest operators hold inconsistent seeds after the seed generation (`seedsDiffer`), or when an honest operator ends a run of a tree with an output that is not the output of `referenceTree` on the seeds and the parameter of the game (`wrongOutput`). An abort sets no flag.

## 3. The honest run and the dealer

`honestDkg b` runs the seed generation and then at most `runLimit` runs of the top tree and at most `runLimit` runs of bottom tree `b`, with no corrupt operator and an adversary that sends nothing. The runs of a tree stop when each operator holds an output of it. `dealerDkg b` runs `dealerKeyGen` and gives bottom tree `b` of its trees to each operator. Both give `SetupOutputs`, the keys, the top tree and bottom tree `b` of each operator. `dkgCompleteness` bounds the probability that an operator of `honestDkg b` holds no such output, and the statistical distance of the two output laws. It has no adversary and no budget, and it adds no PRF advantage.

## 4. The state of the bounds

The theorem `dkgCorrectness` proves the bound `dkgCorrectnessError` plus `streamAdvantage` of `dkgTreeGame` for the whole game. No proof accounts for the whole game for the bound of `dkgSecurityPreservation` on the win probability yet.

The proof of `dkgSecurityPreservation` is a chain of 13 hops (`Proof/DkgSecurity/Shared/Hops.lean`). Twelve hops are theorems. The theorem `DkgSecurityProof.dkgSecurityPreservation_of_leaves` gives the field from the open hop `SharedStep`.

The theorem `theorems_of_sharedStep` of the root module gives the bundle `Theorems` from the same hop.

| Hop | Content | State |
| --- | --- | --- |
| `MonitorErase` | The stream-key event of `dkgTsigGame` is at most as likely as the one of `dkgTreeGame`. | Proved |
| `UsedHitHop` | The bound `setupHybridError` of the stream-key event of `dkgTreeGame`, in the world with the joint keys. | Proved |
| `SharedStart` | The records and the log of the shared event change no result of the real game. | Proved |
| `SharedBadBound` | The bound of the shared event in the real game, with one check term for each batch of each run. | Proved |
| `SharedRefDealer` | With no flag, each kept output is the output of `referenceTree`. | Proved |
| `SharedSeedBound`, `SharedSeedReal`, `SharedSeedIdeal` | The budget, the real end and the ideal end of the seed generation claim, with the shared event. | Proved |
| `SharedSearch` | The skip of a run of a bottom tree after a failed search of the dealer costs at most `2 ^ layerHeight * searchFailure`. | Proved |
| `SharedHit` | The bound of a first hit, one time, in the game with no emulated run. | Proved |
| `SharedStep` | The next real run of a tree becomes an emulated run, at the cost `privacyStepError`. | Open |
| `SharedEnd` | The records and the log change no result in the last game. | Proved |
| `TableHop` | The game with each run emulated wins at most as often as `dkgReduction` wins `tsigGame`. | Proved |

- The error `dkgError` is the sum of the errors of the 13 hops. So it is the error of this proof and no tight bound.
- Its first parts are `dkgCorrectnessError` and one more hash error of the seed generation.
- Its other parts are one failed search of the dealer for each bottom tree and the two privacy terms.
- It grows with the third power of the run limit, through the PRSS setup term of `dkgCorrectnessError`.
- The privacy term `privacyStepError` belongs to the open hop, so a proof can change it.
- Its last term is four times `copyError`, and it is quadratic in the budget $q$.

## 5. What the model does not cover

| Point | Effect |
| --- | --- |
| Adaptive corruption during or after the setup | The coalition of `dkgTsigGame` is static. No claim covers adaptive corruption of the system with the real setup, and the erasure of the state does not give it. |
| A random-oracle $\mathrm{Th}$ in the setup | The claims of the setup fix $\mathrm{Th}$. The step to `signingWorld` is the heuristic of Section 1. |
| A signing request during a run of a tree | Each run is atomic. |
| More than `runLimit` runs of a tree | The game stops the runs at `runLimit`. |
| Concurrent runs or batches | The model has no concurrent run and no concurrent batch. The implementation runs batches concurrently. |
| Liveness | A corrupt operator can stop each run. `dkgCompleteness` has no corrupt operator. |
| The Rust code | No theorem connects the Rust proof of concept to the model. |
| The random-permutation model | No claim is in it. The end statement of leanXMSS is in that model. |
