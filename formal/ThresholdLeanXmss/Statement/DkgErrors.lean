import ThresholdLeanXmss.Statement.Signing

/-!
# The error and cost terms of the setup

This file holds the error terms of the three claims of `Dkg.lean` and the cost term of the reduction
of `DkgSecurity`. Each term is a fixed expression of the budget `q`, of the committee and of the
settings. The terms count the batches, the ceremonies and the PRSS setups of the protocol of
`Scheme.lean`, which deviates from GS20 in the points below.

## Deviations of the protocol from GS20

* Replicated sharing replaces Shamir sharing (CDI05). A corrupt operator that fills a term can give
  each honest holder its own copy, and the check also checks the copies (KPPS23, `Π_agree`, and
  CGH+18, Protocol 3.3).
* Each operator aborts alone, so the setup has selective abort. GS20 aborts all honest operators
  together.
* The de-linearization weighs tuple `k` by a product of `d` coins in place of the powers of one coin
  of GS20, Protocol 13. The multilinear weights follow the prototype (`crates/rss/src/verify.rs`).
* Bit `q` of a word of tuples has the public weight `x^q` in place of a coin (`src/check.rs`), so the
  six bit coins of the tensor are fixed to `x, x^2, ..., x^32`. This is the partially deterministic
  challenge of Dao and Thaler 2024 (Claim 1), with the geometric weights of Flock (Bünz, Rothblum and
  Wang 2026, Section 4.3). The model takes every family of weights that is linearly independent over
  `F_2` (`Constants.weight`).
* The first seven halving steps fold the slices with the coin kept out of `x` (Gruen 2024) and the
  small-value table of BDDT25. Each step is still a degree-2 claim in its challenge.
* GS20 assumes exactly `(n - 1) / 2` corrupt parties, which is `t - 1` here (GS20, Theorem 1, writes
  `n = 2t + 1`). The claims hold for each coalition of at most `t - 1` operators.
* The model splits each ceremony into batches of `batchSize` jobs. The implementation sizes chain
  batches and commitment batches apart, and it puts the top randomizer value in the last commitment
  batch. The implementation runs the signature ceremony as one batch of all its jobs
  (`top_signature` of `src/dkg.rs`).
* The signature of the root of a bottom tree by its top key is one more ceremony, with its own PRSS
  setup (`new_bottom_tree` of `src/dkg.rs`).
* A ceremony takes the start of its counters as a public input, namely the next round label and the
  tag of the next batch. The signature ceremony continues the counters of the ceremony before it,
  as the channel numbers continue in the implementation (`src/net.rs`). The model counts the labels
  over the ceremonies of a tree, and the implementation counts the rounds of each batch.
* The counters start again for each tree, and each PRSS setup hashes in the same domains of `H`
  with no name of its ceremony. So the model does not separate the hash inputs of two ceremonies
  by a domain.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## Error terms -/

/-- The terms `C(n, t - 1)` of a committee. -/
def termCount (C : Committee) : ℕ := C.n.choose (C.t - 1)

/-- The hashes of two values of each term at each operator, namely the history and the digest of the
check, or the two copy hashes of `OpenRep`. -/
def termHashes (C : Committee) : ℕ := 2 * C.n * termCount C

/-- The checked batches of a tree, of the ceremony of the top tree or of the two ceremonies of a
bottom tree. -/
def treeBatches : Tree → ℕ
  | .top => (chunks settings.batchSize topJobs).length
  | .bottom b => (chunks settings.batchSize (bottomJobs b)).length +
      (chunks settings.batchSize (signJobs b fun _ => digit 0)).length

/-- The soundness error of one check with `d` coins and `R` halving steps, `(d + 2 (R + 1)) / (|E| - 2)`
(GS20, Lemmas 8 to 10). It adds `q / |E|²` for each of the `R + 2` coins, for a counted call that hits
the key input of a coin before `Fcoin` reveals the fresh values. The key input has two opened
values. -/
def checkErrorOf (d R q : ℕ) : ℝ :=
  (d + 2 * (R + 1) : ℕ) / (Fintype.card E - 2 : ℝ) + ((R + 2) * q : ℕ) / (Fintype.card E : ℝ) ^ 2

/-- An upper bound on the probability that the coins of an honest check with `R` halving steps
fail. A slice coin is `0`, or one of the `R + 1` challenges finds no value outside `{0, 1}` within
`challengeTries` values. -/
def coinFailure (R : ℕ) : ℝ :=
  (sliceBits : ℝ) / Fintype.card E + (R + 1 : ℕ) * (2 / Fintype.card E : ℝ) ^ challengeTries

/-- An upper bound on the probability that two of `k` coin keys collide, from `k² / 2` pairs. -/
def coinKeyCollision (k : ℕ) : ℝ := (k ^ 2 : ℕ) / 2 ^ 257

/-- An upper bound on the probability that an honest check of some batch of a tree aborts. Two of the `B (R + 2)`
coin keys of all `B` batches of its ceremonies can collide, because a later check reads the cached
coins of an earlier batch. -/
def treeAbortError (tree : Tree) : ℝ :=
  let batches := treeBatches settings tree
  let halvingCount := maxBatch circuits settings fun jobs => halvings (tupleCount jobs)
  batches * coinFailure (E := E) halvingCount + coinKeyCollision (batches * (halvingCount + 2))

/-- The honest points of `H` in the seed generation that a counted call must not hit, namely the parts of each
operator, the derived keys, and the inputs of the hashes of the shared seeds. -/
def seedGenSecrets (C : Committee) : ℕ :=
  C.n * (1 + termCount C + C.n) + 1 + termCount C + C.n.choose 2 + C.n ^ 2

/-- The birthday bound of the counted calls and the honest points of the seed generation. It is an
upper bound for a guessed secret and for a collision of two secrets. -/
def seedGenHashError (C : Committee) (q : ℕ) : ℝ := ((q + seedGenSecrets C) ^ 2 : ℕ) / 2 ^ 256

/-- The honest points of `H` in the PRSS setup that a counted call must not hit, namely the parts of
each operator, the derived keys, and the inputs of the hashes of the shared keys. -/
def prssSetupSecrets (C : Committee) : ℕ :=
  C.n * (termCount C + C.n) + termCount C + C.n.choose 2 + C.n ^ 2

/-- The birthday bound of the counted calls and the honest points of the PRSS setup. -/
def prssSetupHashError (C : Committee) (q : ℕ) : ℝ := ((q + prssSetupSecrets C) ^ 2 : ℕ) / 2 ^ 256

/-- The birthday bound `k² / 2^129` of the 128-bit AES keys of the `k` PRSS keys of a ceremony
(`doc/dkg.md` 3.3). -/
def streamKeyError (C : Committee) : ℝ := ((termCount C + C.n.choose 2) ^ 2 : ℕ) / 2 ^ 129

/-- An upper bound on the probability that two derived keys of one kind are equal. A derivation
hashes only the tag of its kind and the parts (`src/mpc.rs`). Two derivations have the same input
only when an honest part repeats. Two different inputs give the same key only by a collision of
`H`. The bound has one term for each pair of keys of one kind and pays both cases. -/
def derivedKeyCollision (C : Committee) : ℝ :=
  (termCount C ^ 2 + C.n.choose 2 ^ 2 : ℕ) / 2 ^ 256

/-- The birthday bound of the counted calls and the honest points of a check of `count` tuples,
namely the history and the digest of each term at each operator and the `R + 2` coin keys. -/
def checkHashError (C : Committee) (count q : ℕ) : ℝ :=
  ((q + termHashes C + halvings count + 2) ^ 2 : ℕ) / 2 ^ 256

/-- The PRSS keys of one setup, one for each term and one for each pair. -/
def prssKeyCount (C : Committee) : ℕ := termCount C + C.n.choose 2

/-- An upper bound on the stream-key event, `k (q + k) / 2^256`, with `k = prssKeyCount C`. It
accounts for the counted calls that hit a hidden PRSS key and for two equal dealt keys. -/
def prssRandHashError (C : Committee) (q : ℕ) : ℝ := (prssKeyCount C * (q + prssKeyCount C) : ℕ) / 2 ^ 256

/-- An upper bound on the hash errors of one PRSS setup and the streams of its keys. The first term
is for two honest operators with two keys of one term. The other two are for the stream-key event,
at the budget `q` plus the honest known keys of the setup. -/
def prssRealRandHashError (C : Committee) (q : ℕ) : ℝ :=
  prssSetupHashError C q + prssSetupHashError C (q + C.n * (termCount C + C.n)) / 2 +
    prssRandHashError C (q + C.n * (termCount C + C.n))

/-- The birthday bound of the copy hashes of a tree. A bottom tree pays one bound at the end of each
of its two ceremonies, because the codeword of the signature ceremony comes from the opened outputs
of the first ceremony. -/
def treeHybridError (C : Committee) (tree : Tree) (q : ℕ) : ℝ :=
  match tree with
  | .top => ((q + (chunks settings.batchSize topJobs).length * termHashes C) ^ 2 : ℕ) / 2 ^ 256
  | .bottom b => ((q + (chunks settings.batchSize (bottomJobs b)).length * termHashes C) ^ 2 : ℕ) / 2 ^ 256 +
      ((q + treeBatches settings (.bottom b) * termHashes C) ^ 2 : ℕ) / 2 ^ 256

/-! ## The terms of `DkgSecurity` -/

/-- The PRSS setups of a run of a tree. -/
def treeSetups : Tree → ℕ
  | .top => 1
  | .bottom _ => 2

/-- The searches of a randomizer of a run of a tree. -/
def treeSearches : Tree → ℕ
  | .top => 0
  | .bottom _ => 1

/-- The error of the checks of the batches of a run of `tree`, with the soundness of each check and
the birthday bound of its hashes. -/
def treeCheckError (tree : Tree) (q : ℕ) : ℝ :=
  treeBatches settings tree *
    (checkErrorOf (E := E) (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
      (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q +
     checkHashError C (maxBatch circuits settings tupleCount) q)

/-- The charge for the replacement of one run of `tree` by the dealer of the signing game. A failed
search of a bottom tree leaks openings that `tree b` of `tsigGame` does not give, and
`searchFailure` is the charge for it as a bad event. -/
def treeRunError (tree : Tree) (q : ℕ) : ℝ :=
  treeSetups tree * (prssRealRandHashError C q + streamKeyError C) +
    treeCheckError (E := E) (C := C) circuits settings tree q + treeHybridError settings C tree q +
    treeAbortError (E := E) circuits settings tree + treeSearches tree * searchFailure

/-- The statistical part of the bound of `DkgSecurity`, the charge for the seed generation and for
`runLimit` runs of the top tree and of each bottom tree. -/
def dkgError (C : Committee) (q : ℕ) : ℝ :=
  seedGenHashError C q + derivedKeyCollision C +
    runLimit * (treeRunError (E := E) (C := C) circuits settings .top q +
      ∑ b : Fin (2 ^ layerHeight), treeRunError (E := E) (C := C) circuits settings (.bottom b) q)

/-- The budget that is planned for the calls of a reduction in `.hash` and `.prf` for one run of
`tree`. It counts the input terms that the coalition holds, one `.prf` call for each term and each
point, and for a bottom tree the nodes of the codeword of the root and the randomizer search. The
plan is that a reduction answers each other domain of the setup from its own table. -/
def treeSigningCalls (C : Committee) : Tree → ℕ
  | .top => (topJobs.map (·.points.length)).sum * termCount C
  | .bottom b => (((bottomJobs b).map (·.points.length)).sum + chainCount) * termCount C +
      (2 ^ (layerHeight + 1) + randomizerAttemptLimit)

/-- The budget that is planned for the calls of a reduction beyond the calls of the adversary, for
`runLimit` runs of each tree. The plan is that the requests of a reduction to the oracles of
`tsigGame` are only `corrupt` and `tree`, which cost nothing. -/
def dkgOverhead (C : Committee) : ℕ :=
  runLimit * (treeSigningCalls C .top + ∑ b : Fin (2 ^ layerHeight), treeSigningCalls C (.bottom b))

/-- The multi-key PRF advantage of `prgReduction` against `hiddenStreams` on `game`. It pays the
streams of the PRSS under the keys that `D` lacks, which are AES-128 under a hash of the key. -/
def streamAdvantage (prims : Primitives) (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D game)).toReal


/-! ## The terms of `DkgCorrectness` -/

/-- A bound on the probability that one of `n` new hash cells meets one of `k` earlier cells or
another new cell, `((k + n)² - k²) / 2^257` for outputs of 256 bits. -/
def splitRisk (k n : ℕ) : ℝ :=
  (((k + n : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2) / (2 * 2 ^ 256)

/-- An upper bound on the probability that one of the `R + 2` coin keys of a check of `count`
tuples, with `R = halvings count`, meets one of `q + R + 2` cached expansion keys. The soundness of
the check pays it at each coin. -/
def soundHashError (count q : ℕ) : ℝ :=
  ((halvings count + 2) * (q + halvings count + 2) : ℕ) / 2 ^ 256

/-- The PRSS setups that a game tries, with the aborted tries. -/
def gameSetups : ℕ := runLimit * (1 + 2 * 2 ^ layerHeight)

/-- The checked batches of a game, with the aborted tries. -/
def gameBatches : ℕ :=
  runLimit * (treeBatches settings .top + ∑ b : Fin (2 ^ layerHeight), treeBatches settings (.bottom b))

/-- The coin keys of the honest operators in a game. -/
def gameCoinKeys (C : Committee) : ℕ :=
  gameBatches settings runLimit * C.n * (maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2)

/-- The history and digest cells of a game, namely the calls of the adversary and the honest cells. -/
def splitBudget (C : Committee) (q : ℕ) : ℕ := q + gameBatches settings runLimit * termHashes C

/-- The error of a collision of two echo hashes of the PRSS setups. -/
def echoError (C : Committee) (q : ℕ) : ℝ :=
  ((q + gameSetups runLimit * C.n ^ 2) ^ 2 : ℕ) / 2 ^ 257

/-- The error of a collision of two derived keys of the PRSS setups. -/
def reuseError (C : Committee) (q : ℕ) : ℝ :=
  ((q + gameSetups runLimit * C.n * (termCount C + C.n)) ^ 2 : ℕ) / 2 ^ 257

/-- The error of a run of `tree` whose PRSS setup repeats the derivation input of a hidden key of an
earlier setup of the game. -/
def freshError (C : Committee) (tree : Tree) : ℝ :=
  (treeSetups tree * prssKeyCount C * (gameSetups runLimit + treeSetups tree) : ℕ) / 2 ^ 256

/-- The error of a collision of two copy hashes. -/
def copyError (C : Committee) (q : ℕ) : ℝ := ((splitBudget settings runLimit C q) ^ 2 : ℕ) / 2 ^ 256

/-- The error of a collision of two history and digest cells. -/
def splitError (C : Committee) (q : ℕ) : ℝ := splitRisk 0 (splitBudget settings runLimit C q)

/-- The batch counts of the ceremonies. -/
@[irreducible] def batchCounts : Finset ℕ :=
  Finset.univ.biUnion fun x : PublicParameter × Fin (2 ^ layerHeight) × Encoding =>
    ((([topJobs, bottomJobs x.2.1, signJobs x.2.1 x.2.2].flatMap (chunks settings.batchSize)).map
      fun jobs => tupleCount (runCircuits circuits x.1 jobs)).toFinset)

/-- The error of the check of one batch of `count` tuples in a game. It has the soundness of the check
(`checkErrorOf`), a coin key that meets a cached key (`soundHashError`), and the hiding of the
salted digests of the terms. A check start has the cells of the start of its run and the cells of
the run before it, so each count of the start is taken two times. -/
def batchCheckError (C : Committee) (q count : ℕ) : ℝ :=
  checkErrorOf (E := E) (coins count) (halvings count) (2 * q + 2 * gameCoinKeys circuits settings runLimit C) +
    soundHashError count (2 * q + 4 * gameCoinKeys circuits settings runLimit C) +
    ((C.terms.length * (6 * q + 2 * (gameBatches settings runLimit * termHashes C) + (C.n + 1) * C.terms.length) :
      ℕ) : ℝ) / 2 ^ 256

/-- The error of the check of one batch, at the worst batch count of the ceremonies. -/
def checkErrorMax (C : Committee) (q : ℕ) : ℝ :=
  ((batchCounts circuits settings).sup fun count =>
    (batchCheckError (E := E) circuits settings runLimit C q count).toNNReal : NNReal)

/-- The error of one run of `tree`, from the checks of its batches and the fresh hidden keys. -/
def runError (C : Committee) (q : ℕ) (tree : Tree) : ℝ :=
  treeBatches settings tree * checkErrorMax (E := E) circuits settings runLimit C q + freshError runLimit C tree

/-- The honest calls of `H` in the PRSS setups of a game. In one setup each honest operator makes `n`
commitments, `n` openings, at most `termCount C + n - 1` derivations and `n` echo hashes. -/
def honestSetupCalls (C : Committee) : ℕ := gameSetups runLimit * C.n * (4 * C.n + termCount C)

/-- The honest known keys of the PRSS setups of a game, at most `n (termCount C + n)` in each setup. -/
def honestKnownKeys (C : Committee) : ℕ := gameSetups runLimit * C.n * (termCount C + C.n)

/-- A bound on the stream-key event when each PRSS setup of a game has fresh hidden keys. It is
`gameSetups` times `prssRandHashError` on the counted calls, the honest known keys and the fresh keys
of all setups. -/
def freshKeyError (C : Committee) (q : ℕ) : ℝ :=
  gameSetups runLimit * prssRandHashError C (q + honestKnownKeys runLimit C + gameSetups runLimit * prssKeyCount C)

/-- The error of `DkgCorrectness`, for the seed generation and `runLimit` runs of the top tree and of
each bottom tree. Its terms are the charges for these events.

* `seedGenHashError` is the charge for inconsistent seeds after the seed generation.
* The next two terms are the charge for the stream-key event. In this event the cache of `H` holds
  the AES key hash of a hidden PRSS key in use, or two hidden key names hold the same key. Each PRSS
  setup of the game adds half of `prssSetupHashError` at the budget `2 q + honestSetupCalls`, the
  charge for the step in which its hidden keys become fresh keys. `freshKeyError` is the charge for
  the event with fresh keys.
* `echoError` and `reuseError` are the charges for a collision of two echo hashes or of two derived
  keys of the PRSS setups.
* `copyError` and `splitError` are the charges for a collision of two copy hashes or of two history
  and digest cells.
* `runError` is the charge for a run of a tree with a wrong output, by the checks of its batches and
  a repeated hidden key. -/
def dkgCorrectnessError (C : Committee) (q : ℕ) : ℝ :=
  seedGenHashError C q +
    (gameSetups runLimit * (prssSetupHashError C (2 * q + honestSetupCalls runLimit C) / 2) +
      freshKeyError runLimit C q) +
    echoError runLimit C q + reuseError runLimit C q + copyError settings runLimit C q +
    splitError settings runLimit C q +
    runLimit * (runError (E := E) circuits settings runLimit C q .top +
      ∑ b : Fin (2 ^ layerHeight), runError (E := E) circuits settings runLimit C q (.bottom b))

/-! ## The terms of `DkgCompleteness` -/

/-- An upper bound on the probability that an honest operator has no keys, no top tree or no output
of bottom tree `b` after the honest run. -/
def dkgAbortError (C : Committee) (b : Fin (2 ^ layerHeight)) : ℝ :=
  derivedKeyCollision C + treeAbortError (E := E) circuits settings .top +
    treeAbortError (E := E) circuits settings (.bottom b) + searchFailure

/-- The upper bound on the distance of the honest run of the setup and of bottom tree `b` to
`dealerKeyGen`. A failed search is in both runs, so it is not in this term. -/
def dkgCompletenessError (C : Committee) (b : Fin (2 ^ layerHeight)) : ℝ :=
  derivedKeyCollision C + treeAbortError (E := E) circuits settings .top +
    treeAbortError (E := E) circuits settings (.bottom b)

end ThresholdLeanXmss
