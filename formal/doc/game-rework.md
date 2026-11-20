# A game-based form of the statement. Design

This file is the design of a rework. The Lean code for it is in `formal/Sketch/`, outside the build targets, until its statements are accepted. The 22 proved fields of `Theorems` stay as the lemma layer.

## 1. The goal

The top has five claims in one game-based model.

| Claim | Content | Source | State |
| --- | --- | --- | --- |
| `stronglyUnforgeable` | The signing with a trusted dealer is strongly unforgeable, with adaptive corruption | PRAWNS, Definition 3.2 | Proved in the library |
| `signingCorrectness` | An honest signing run gives a valid signature, except for a failed search | PRAWNS | Proved in the library |
| `dkgSecurity` | The real setup keeps the security of the signing game. A forger against the game with the real setup gives a forger against the game with the dealer. | Gurkan and others, Definition 8. The explicit forger with an additive term is the form of their proofs (Appendix C of the full version, Lemmas 3 to 5). The fixed bound is an addition of this design. | Stated in `Sketch/DkgGame.lean`. No reduction code exists. |
| `dkgCorrectness` | Against an adversary, an honest operator ends a tree with the right output or with no output | Correctness with abort. Gurkan and others, Definition 6, has no clause on an abort. | Stated in `Sketch/DkgGame.lean`. The proof work is in progress. The final error term is not fixed. |
| `dkgCompleteness` | With no corrupt operator, the setup gives an output that is near the output of the dealer | The completeness of this library. The papers of this project state no such property. | Proved in `Sketch/AbortOrCorrect.lean` |

A claim is a game with an adversary, a bound on its calls, and an explicit error. A simulator is code inside a game. No composition theorem is used. No claim fixes an input before the game starts.

## 2. The three shapes of a claim

| Shape | Form | Use |
| --- | --- | --- |
| (a) A win game | $\Pr[G(A) = 1] \le \varepsilon(q)$, or $\Pr[G(A) = 1] \le \Pr[G'(B_A) = 1] + \varepsilon(q)$ with $B_A$ as code | The top claims with an adversary. `dkgCompleteness` is a distance of two honest runs. |
| (b) A left and a right game | $\lvert \Pr[L(A) = 1] - \Pr[R(A) = 1] \rvert \le \varepsilon(q)$, with the simulator as code of $R$ | A hop of a proof |
| (c) A bad event in a game | $\Pr[\mathit{bad}] \le \varepsilon(q)$ | A hop of a proof, by the Difference Lemma of Shoup |

The three kinds of a hop are the ones of Shoup. The match of his kinds with these shapes is a choice of this design.

## 3. The world, and the place of the heuristic

- The world of the three DKG claims is the present `world`. $\mathrm{Th}$ is a fixed function on the inputs that the MPC evaluates. Each other domain of $H$ is a lazy random oracle with one cache for the whole game.
- The three DKG claims hold for each fixed $\mathrm{Th}$ and each circuit family that computes it. They use no heuristic.
- `stronglyUnforgeable` holds in the world where all of $H$ is a random oracle, as PRAWNS proves it.
- The reduction $B_A$ plays the honest operators of the MPC, so it needs the circuits. The circuits depend on $\mathrm{Th}$. A forger that depends on $\mathrm{Th}$ is not a forger of the world with $\mathrm{Th}$ as an oracle. So no proof joins `dkgSecurity` and `stronglyUnforgeable`.
- The corollary `dkgTsigGame_le` has the bound of the dealer game for the fixed $\mathrm{Th}$ as a premise. That premise is the random-oracle heuristic for $\mathrm{Th}$, used one time.

## 4. The real game

`dkgTsigGame` is the signing game of PRAWNS with the real setup in the place of the dealer.

| Point | Model |
| --- | --- |
| The adversary | One adversary with one state plays a static coalition of fewer than $t$ operators through all phases. It calls $H$ from its first step. |
| The setup | The seed generation, the top tree and each bottom tree run as the real protocols. No functionality is on the real side. |
| The inputs | The code of the game makes the inputs of each run from the outputs of the earlier runs |
| An abort | Each honest operator has its own keys and trees. It acts only on what it holds. The game has no agreement step. |
| The runs of a tree | Each tree has a fixed limit of runs on the same seeds. One run is active at a time. All runs of a tree end before the first signing request on it. |
| The count | The budget $q$ counts the own calls of the adversary. The honest operators call the free copy of $H$. |

The game restricts the real system in these points. $\mathrm{Th}$ and the circuits are fixed. A run is atomic, so no signing request arrives during a run. The coalition is static, and the dealer game of PRAWNS has adaptive corruption.

## 5. The hops of `dkgSecurity`

The sequence goes from `dkgTsigGame D A` to `tsigGame (reduction D A)`. The marks are REUSE-THEOREM (a proved field applies), REUSE-LEMMA (proved lemmas help, the claim needs a new form) and NEW. No mark is checked in Lean yet.

| # | Change of the code | Shape | Error term | Source | Mark |
| --- | --- | --- | --- | --- | --- |
| 1 | The real seed generation becomes `FseedGen` with `seedGenSimulator` | (b) | `seedGenHashError` | `seedGenSecurity` | REUSE-LEMMA. It is the first phase, so the cache is empty and the claim has no input. The field does not apply as it is. Its distinguisher runs on the counted copy, so the rest of the game as the distinguisher charges each later honest call. The hop needs a new form with one count for the adversary and one for the honest calls of each domain. |
| 2 | The keys of `FseedGen` become the keys of the dealer | bridging | 0 | `FseedGen` samples the keys with `prawnsKeyGen` | NEW, small. It is an exact rearrangement, with the bookkeeping of the operators that got no keys. |
| 3 | In each run, the real PRSS setup and its streams become ideal keys and ideal streams | (b) | `prssRealRandHashError`, `streamKeyError`, the PRF advantage of AES | `prssRealRandSecurity`, CDI05 | NEW for a start cache that is not empty, for calls that the run chooses, and for rounds between the calls |
| 4 | In each batch, the real multiplication, the coins and the check become their functionalities | (b), (c) | `checkErrorOf`, `checkHashError` | `multSecurity`, `extendMultSecurity`, `coinSecurity`, `multVerifySecurity`, GS20 | NEW for the join. The direct proof has the real check and a part of the core of a batch. |
| 5 | The run in the hybrid model becomes `Ftree` with `treeHybridSimulator` | (b) | `treeHybridError` | `treeHybridSecurity`, GS20 Theorem 2 | REUSE-LEMMA. The inputs come from the game, and the claim binds them outside. |
| 6 | The output of `Ftree` becomes the tree of the dealer | bridging | 0 | `dealerTreeCorrectness` | REUSE-THEOREM for the output and the cache. It holds from each cache. It does not cover what a run leaks to the adversary. |
| 6a | The leak of a run with a good search is computed from the answers of the dealer game (`tree b`, the top tree) | bridging | 0 | none | NEW |
| 7 | A bottom run with a failed search leaks openings that the dealer game does not give | (c) | `searchFailure` for each run | none | NEW |
| 8 | The signing phase with operators that hold no output, and the runs after the first one | bridging | 0 | `realOracles_round_run` for the case where each operator holds each tree | NEW. It needs a relation of the two games with the tree of the dealer below, a refusal for each operator that holds no output, the same record of the sent parts, the keys of the coalition from `corrupt`, and the same test of a new signature. |
| 9 | The reduction answers the domains that only the setup uses from its own table, for its own calls and for the calls of `A`. Its cost is the cost of `A` plus a small term. | bridging | 0 | none | NEW. It needs a lemma that the honest code of the dealer game reads no cell of those domains. The reduction gets AES as an argument for the streams. `.hash` and `.prf` are used by both phases and go to the oracle. |
| 10 | A call of the adversary hits a seed or a PRF value before the setup uses it | (c) | a hit term in $q$ | `SeedHit`, `Tprf` | REUSE-LEMMA. The exact event and its place in the error are not fixed yet. |

## 6. The hops of `dkgCorrectness` and of `dkgCompleteness`

The rows C1 to C4 are the first plan of `dkgCorrectness`. The proof now has more hops, on a ghost run with a record. Row C5 is `dkgCompleteness`, which is proved.

| # | Claim | Shape | Source | Mark |
| --- | --- | --- | --- | --- |
| C1 | Honest holders of a term hold the same seed, and honest operators of a pair hold the same pair key | (c) | The agreement part of the seed generation proof | REUSE-LEMMA |
| C2 | A check accepts a wrong tuple in a batch | (c) | `CheckSound` 1307, the real check of the direct proof, GS20 | REUSE-LEMMA. This is the pilot with one batch. The bound is conditional on coins that the adversary cannot predict. |
| C2a | The coins of a check are near uniform for the adversary, with all that it saw before | (b) | `prssRealRandSecurity` for a fixed list of calls, CDI05 | NEW for calls that the run chooses. It is hop 3 in the form that part 1 needs. A PRF advantage alone does not give it, because the keys of the streams come from hashes. |
| C3 | A tree output with accepted checks is the output of `referenceTree`, also after a partial abort | bridging | `dealerTreeCorrectness`, `CircuitsCompute`, the correctness of the opening | REUSE-LEMMA |
| C4 | The union over the batches, the runs and the trees | arithmetic | none | NEW, small |
| C5 | The honest run gives an output and is near the dealer | (b) with no adversary | `seedGenCompleteness`, `treeCompleteness`, `dealerTreeCorrectness`, `dealerTreeSuccess` | REUSE-LEMMA. Each field starts from an empty cache with fixed inputs. The join needs a frame lemma for a start cache and the rule of the first kept output. It needs no secrecy of the PRSS. |

`dkgCorrectness` needs no simulator of a whole run. `dkgCompleteness` (hop C5) needs no secrecy. `dkgCorrectness` needs hop C2a, which is a form of hop 3.

## 7. What the games do not remove

The games remove the composition theorem and the inputs that are fixed before $H$ answers. Each point below stays as a hop with its own proof.

| Point | Hop | State of the direct proof |
| --- | --- | --- |
| A batch with no tuple | 4 | Its batch simulator is wrong for this case |
| The round after a partial abort | 4 | Open |
| The PRSS keys that a simulator programs, and the streams of a key that a corrupt holder has | 3 | One setup with a fixed list of calls is proved |
| The challenge search with its cap of $2^{64}$ tries | 4, 9, C2 | The search lemmas exist. Hop 9 keeps the search out of the cost of the reduction. |
| The bottom tree | 3 to 7 | No route was found |
| The hash term of the bound | 1, 3, 4, 5 | Each term has the form $q^2 / 2^{256}$. A count that charges the honest searches gives about $2^{-51}$. A count for each domain is necessary. |

### The join of the real check has two forms

The real check reads its PRSS streams by calls under its keys. The check on drawn values reads the known rows first and takes the hidden values from tables. The join says that the two runs agree.

| Form | What it states | Which claim needs it |
| --- | --- | --- |
| The output form, `PilotJoinOut` | The honest outputs and the state of the adversary have the same law, from one start cache | A bound of an event. `dkgCorrectness` bounds a wrong accept before the opening, so this form is enough there. |
| The strong form, `CheckJoinStatement` of the direct proof | The result and the next cache have the same law, from each start cache | A replacement of the check inside a run that goes on. Hop 4 of `dkgSecurity` needs it. |

A proof of the output form is no proof of the strong form. The rows of the output form are stated with the next cache where a row has one, so that the strong form can use them.

## 8. What is assumed, what is open, what can fail

- The error and cost terms of `dkgSecurity` and `dkgCorrectness` in `Sketch/DkgGame.lean` are targets. The terms of `dkgCompleteness` are derived.
- Definition 8 of Gurkan and others has one adversary on both sides and a negligible term. Their proofs (Appendix C of the full version) build an explicit forger with an additive term, as `dkgSecurity` does. Their paper has games with one key only. It has no threshold use of the key, no static setup before an adaptive dealer game, no fixed bound, no selective abort and no fixed $\mathrm{Th}$. Each of these points is an addition of this design. Their proof route needs a key with a group operation, which a hash root does not have.
- The hops 3 and 4 are the work that the direct proof did not finish. The games do not make them smaller.
- The dealer game stays adaptive, and the game with the real setup is static. An adaptive setup has no source in the papers of this project.
- A proof of a hop can show that a statement of the sketch is false. Then the statement changes.
