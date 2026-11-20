import ThresholdLeanXmss.Statement.Dkg
import ThresholdLeanXmss.Statement.DkgReduction

/-!
# The theorems

Each field of `Theorems` is one end claim about the protocol of `Scheme.lean`. The five claims are
stated with games. `Signing.lean` holds the signing game and the two signing claims. `DkgGame.lean`
holds the games of the setup, `DkgErrors.lean` their error terms, `Dkg.lean` the three claims of
the setup with their adaptations of the papers, and `DkgReduction.lean` the reduction of
`dkgSecurity`.

* Signing with a trusted dealer is strongly unforgeable with adaptive corruption
  (`stronglyUnforgeable`). The game is `tsigGame`, the game of PRAWNS, Figure 3, with the dealer
  `dealerKeyGen`. An honest quorum signs (`signingCorrectness`). Its experiment is `honestSigning`,
  not `tsigGame`.
* The setup by DKG preserves the security of the signing (`dkgSecurity`). The game `dkgTsigGame`
  is `tsigGame` with the real seed generation and the real runs of the trees in the place of the
  dealer. `dkgCorrectness` bounds inconsistent seeds and wrong trees against the adversary, and
  `dkgCompleteness` bounds the abort of an honest run and its distance to the dealer.

The reduction of `dkgSecurity` is the named forger `dkgReduction`. It reads only `prims.aes` from
`prims`. A reviewer reads its code to see that it simulates the honest operators and makes no search
for a secret. It forwards a signing request when the emulated operator holds what it needs. It
runs `A.forge` when an honest operator holds a top tree, and it outputs `idleForgery` if not. The
claim then says that the real setup gives an adversary no more than `tsigGame` gives that forger,
up to the stated errors `dkgError` and `streamAdvantage`.

Let `δ` bound the probability that the forger `dkgReduction` of an adversary `A` with budget `q`
wins `tsigGame` in `runWorld`, with the fixed `Th`. Then `δ + dkgError C q + streamAdvantage` bounds
the probability that `A` wins `dkgTsigGame`. No field gives such a `δ`. No small `δ` holds for each
query-bounded adversary with a fixed `Th`, because a search on `Th` costs no call.
`stronglyUnforgeable` bounds `tsigGame` in the signing world, where `Th` is a random oracle.

## The world and the preconditions of each claim

`runWorld` answers `Th` with the fixed function `prims.Th` on the inputs that the MPC evaluates,
and every other input of `H` with a lazy random oracle. The signing world answers all of `H`,
`Th` included, with a lazy random oracle. A coalition has at most `t - 1` operators
(`Committee.Coalition`), and the empty coalition is one of them.

| Claim | World | Preconditions | Trivial cases |
| --- | --- | --- | --- |
| `stronglyUnforgeable` | signing world (`signingAccepts`) | own cost of the forger at most `q` | none |
| `signingCorrectness` | `runWorld` | none, for each quorum, key and message | none |
| `dkgSecurity` | `runWorld` (`accepts`) | `0 < batchSize`, `CircuitsCompute circuits prims.Th`, budget `q` of the adversary | vacuous at `batchSize = 0`, and `A` never wins at `runLimit = 0`, because no top tree exists |
| `dkgCorrectness` | `runWorld` (`accepts`) | `0 < batchSize`, `0 < runLimit`, `CircuitsCompute circuits prims.Th`, budget `q` of the adversary | vacuous at `batchSize = 0` and at `runLimit = 0` |
| `dkgCompleteness` | `runWorld`, no corrupt operator | `0 < batchSize`, `0 < runLimit`, `CircuitsCompute circuits prims.Th` | vacuous at `batchSize = 0` and at `runLimit = 0` |

For circuits that compute no `Th`, the three claims of the setup say nothing. A bound of `1` or more
says nothing for the inequality on the probability. The cost bound of the reduction and the validity
of an output signature stay meaningful.

## Model

* There are `n = 2t - 1` operators, synchronous rounds and private authenticated links (GS20,
  Section 3.1). At most `t - 1` operators are corrupt.
* The coalition of the setup is static, as in GS20 and in Gurkan and others. In `dkgTsigGame` it is
  corrupt from the start and stays the same for the whole life of the keys. The adversary of
  `tsigGame` corrupts adaptively, and a corruption gives only the keys of an operator (PRAWNS).
* Honest operators sign at most one message at each key over all quorums
  (`breaksOneMessagePerKey`). The signing games enforce it. The PoC has the exchange of
  acknowledgements of `doc/sign.md` 4.1 for it, and a deployment must enforce it too.
* `H` is one lazy random oracle on `Query`, with one domain for each constructor, except `Th` on
  the inputs of the MPC in `runWorld`. `PRG` is AES-128 under a hash of the key. `dkgSecurity` and `dkgCorrectness` pay its
  multi-key PRF advantage.
* In the claims of the setup, the circuits compute the fixed `Th` (`CircuitsCompute`) on the chain
  steps and the commitment `c_e`. The gap between `runWorld` and the signing world is the
  random-oracle heuristic for Keccak.
* In `dkgTsigGame` each run of a tree is atomic, and each tree has at most `runLimit` runs.
* A budget `q` counts the calls of `H` and `PRG` of the adversary on every path of its program, for
  every answer of the oracles. A forger also pays one unit for each round-2 request. An adversary
  has no bound on its computation.
* Each bound is a fixed expression of `q`, of the committee and of the settings. The bounds of
  `dkgSecurity` and `dkgCorrectness` add the PRF advantage of `prgReduction` (`Reductions.lean`).
  `dkgCompleteness` adds no PRF advantage.

These claims also use `Scheme.lean` and `Ideal.lean`, because they name their definitions. They hold
the protocol with its oracles, its network and its honest runs, and the dealer with the oracles of
the signing game.

## What no field states

* No field states a bound of `dkgTsigGame` alone. It follows from `dkgSecurity` only with a bound of
  `tsigGame` for the fixed `Th`.
* No field states security of the setup against adaptive corruption.
* No field fixes the basis or the bit encoding of the check field. The claims take every value of
  `Constants`. Its field `encode` gives `E` exactly `2 ^ 128` elements (`Constants.card`), so `E` is
  isomorphic to `GF(2^128)`. No field states that the constants of the implementation are such a
  value.
* No field connects the model to the Rust code.
* No field is in the random-permutation model. The end statement of leanXMSS is in that model at the
  pinned revision of leanVM.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The end claims, for one committee, one check field with its constants, one `Th` with AES-128
for the signing claims, one circuit family, one setting and one run limit. The claims of the setup
hold for each `Th` that the circuits compute. -/
structure Theorems (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (runLimit : ℕ) : Prop where
  /-- Signing with the trusted dealer is strongly unforgeable with adaptive corruption, in the
  random-oracle model (PRAWNS, Definition 3.2, in the form of leanXMSS). A forger with own cost `q`
  wins `tsigGame` with probability at most `(q + 2^15 + 384) / 2^127` plus two terms of the hidden
  keys. -/
  stronglyUnforgeable : ThresholdLeanXmssStronglyUnforgeable prims C
  /-- An honest quorum fails with probability at most `2 (1 - p)^L`, for the two randomizer
  searches, and each signature that it outputs verifies (PRAWNS, Section 3.1, honest run). -/
  signingCorrectness : SigningCorrectnessStatement prims C
  /-- The setup by DKG preserves the security of the signing (Gurkan and others, Definition 8). The
  named forger `dkgReduction` turns each adversary of `dkgTsigGame` with a static coalition and
  budget `q` into a forger of `tsigGame` with cost `q + dkgOverhead C`. The adversary wins at most
  `dkgError C q` and the PRF advantage of the streams more often than that forger. -/
  dkgSecurity : DkgSecurity K circuits settings runLimit (dkgReduction K circuits settings runLimit)
  /-- Against an adversary with a static coalition and budget `q`, two honest operators hold
  inconsistent seeds, or an honest operator ends a run of a tree with a wrong output, with
  probability at most `dkgCorrectnessError C q` and the PRF advantage of the streams. An abort is no
  win (Gurkan and others, Definition 6, agreement clause, adapted). -/
  dkgCorrectness : DkgCorrectness K circuits settings runLimit
  /-- With no corrupt operator, each operator ends with its keys, the top tree and bottom tree `b`
  except with probability at most `dkgAbortError C b`. The outputs of all operators are within
  `dkgCompletenessError C b` of the outputs of `dealerKeyGen` in statistical distance. -/
  dkgCompleteness : DkgCompleteness K circuits settings runLimit

/-- The security claim, for every committee, every check field of characteristic `2` with its
constants, every `Th` and AES-128, every circuit family, every setting and every run limit. -/
abbrev ThresholdLeanXmssSecurityStatement : Prop :=
  ∀ (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (K : Constants C E) (prims : Primitives) (circuits : Circuits) (settings : Settings) (runLimit : ℕ),
    Theorems prims K circuits settings runLimit

end ThresholdLeanXmss
