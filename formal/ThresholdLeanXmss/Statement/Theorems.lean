import ThresholdLeanXmss.Statement.Signing

/-!
# The theorems

Each field of `Theorems` is one end claim about the protocol of `Scheme.lean`, at the level at
which GS20 and PRAWNS state them. The file of `Statement/` that defines a claim holds its game, its
error terms and its deviations from the papers. `ThresholdLeanXmssSecurity.lean` holds the root
theorem of `ThresholdLeanXmssSecurityStatement` and the axiom guards.

The two main claims are these.

* The setup by DKG acts as a trusted dealer with selective abort. The fields state this claim for
  the seed generation only. `dealerTree` states that the dealer of a tree gives the trees of the
  signing game.
* Signing with a trusted dealer is strongly unforgeable with adaptive corruption
  (`stronglyUnforgeable`).

## The order of the fields

The fields are in four groups, in the order of the note of leanXMSS. Each field names its item of
a source.

* The threshold PRF `F` is the first group (the note, Section 2, and PRAWNS, Definitions 2.1 and
  2.2). Its fields are `tprfCorrectness` and `tprfSecurity`.
* The setup by DKG is the second group (the note, Section 2.1). Its target is the trusted dealer
  `KeyGen` of PRAWNS. The note has two ceremonies.
  * The keygen ceremony of the note is the seed generation and then the ceremony of the top tree.
    No adversary with a bounded budget distinguishes the seed generation from a trusted dealer with
    selective abort, up to the error that the claim names (`seedGenSecurity`).
    `seedGenCompleteness` is its honest run.
  * The ceremony of a bottom tree of the note is two ceremonies of the model, one for the tree and
    one for the signature of its root by its top key. The fields `treeCompleteness` and
    `dealerTree` cover the top tree and each bottom tree with its signature. `treeSuccess` covers
    a bottom tree on its top tree.
* The MPC protocol of GS20 is the third group. Its fields are `coin`, `mult`, `extendMult`,
  `multVerify`, `main` and `ceremonyHybrid`, and the honest runs `coinCompleteness`,
  `multVerifyCompleteness` and `mainCompleteness`. The note has no section for this group. It names the MPC in Section 2.1.
* The signing is the fourth group (the note, Section 2.3, and PRAWNS, Definition 3.2). Its fields
  are `signingCorrectness` and `stronglyUnforgeable`.

No group is for Section 2.2 of the note, the setup by a trusted dealer with `n = 3f + 1`. Each
claim is for `n = 2t - 1`.

GS20 states no completeness lemma. Security with abort alone allows a protocol that always aborts,
so each completeness field is the honest run of its protocol.

## Model

* There are `n = 2t - 1` operators, synchronous rounds and private authenticated links (GS20,
  Section 3.1). At most `t - 1` operators are corrupt over the lifetime of the key.
* A ceremony is one protocol (`ceremony`). It runs one PRSS setup and then the batches of a public
  job list, and it opens every output. Its public inputs are the job list and the start of its
  counters. It has three uses, namely `topJobs` for the top tree, `bottomJobs b` for a bottom tree,
  and `signJobs b encoding` for the signature of a bottom root by its top key. `newTree` is the
  ceremonies of one tree with the local steps between them, and it passes the counters on.
* The seed generation and each ceremony are separate claims. Each has a rushing malicious adversary
  with its own static coalition. The seed generation claims and `TreeSecurityStatement` run the
  real network with the real PRSS, and `ceremonyHybrid` is in the hybrid model.
* Each building-block claim is in a hybrid model. `coin`, `mult` and `extendMult` are in the
  `F_rand`-hybrid model. `multVerify` is in the `{F_coin, F_extendMult, F_rand}`-hybrid model, and
  `main` and `ceremonyHybrid` are in the `{F_mult, F_multVerify}`-hybrid model. The PRSS outputs
  of one round realize `F_rand` (CDI05).
* The signing adversary corrupts adaptively, and a corruption gives only the keys of an operator.
  After a ceremony, an operator erases its ceremony state.
* Honest operators sign at most one message at each key over all quorums
  (`breaksOneMessagePerKey`). The signing game enforces it. The PoC has the exchange of
  acknowledgements of `doc/sign.md` 4.1 for it, and a deployment must enforce it too.
* `H` is one lazy random oracle on `Query`, with one domain for each constructor. `PRG` is AES-128
  under a hash of the key, and the ceremony claim pays its multi-key PRF advantage.
* In the seed generation and ceremony claims, `Th` is one fixed function on the inputs that the MPC
  evaluates, namely the chain steps and the commitment `c_e`. In the signing claim, all of `H` is a
  lazy random oracle, `Th` included. The gap between the two models is the random-oracle heuristic
  for Keccak.
* `F_ceremony` and `F_tree` run the circuits of the jobs, so the ceremony claims are stated for
  every circuit family.
  `dealerTree` and `treeSuccess` assume that the circuits compute `Th` (`CircuitsCompute`), and they
  link `F_tree` to the trees of the signing claims.
* A budget `q` counts calls of `H` and `PRG` on every path of a program, for every answer of the
  oracles. The simulation claims and `tprfSecurity` count only the calls of the adversary and of the
  distinguisher. `stronglyUnforgeable` counts only the own calls of the forger and its round-2
  requests.
* Each bound is a fixed expression, namely an upper bound of the error of the checks,
  `q / 2 ^ bits` terms, and the advantage of a reduction that `Reductions.lean` defines.

A review also reads `Scheme.lean`, `Ideal.lean` and `Reductions.lean`, because the claims name their
definitions. They hold the protocol with its oracles, its network and its honest runs, the
functionalities with the oracles of the games, and the simulators with the reductions. A bound with
the advantage of a reduction is only as strong as that reduction.

## What no field states

* The field `ceremonyHybrid` states that a ceremony securely computes `F_ceremony` in the hybrid
  model with ideal multiplication and check. No field states it for the real network and the real
  PRSS. `Dkg.lean` has this claim as `TreeSecurityStatement`, with the simulator
  `ceremonySimulator`. It is stated and not proved. It is the claim for one ceremony. The fields on
  a tree are the honest run of its ceremonies (`treeCompleteness`) and the two facts on its dealer (`dealerTree` and `treeSuccess`).
* No claim joins the two ceremonies of a bottom tree against a corrupt coalition.
  `TreeSecurityStatement` has no simulator and no bound for the ceremony of the tree, the
  randomizer search, the signature ceremony and the check of the signature together. It does not
  state that the honest operators of a signature ceremony hold the same encoding, or that each of
  them starts. `statement.tex` holds the contract rule and a sketch of this join, with its open points.
* So no field states that the keygen ceremony of the note is secure as a whole. The fields state
  it for the seed generation. For the top tree, `TreeSecurityStatement` covers the ceremony of
  `topJobs`, which opens the chain ends. The local build of the tree from them is no part of the claim.
* No field composes the seed generation, the ceremonies and the signing. Each field covers one
  protocol or one building block alone. `statement.tex` holds the deployment contract and a sketch of that
  composition, with its open points.
* No field covers a corruption between two ceremonies. The seed generation and ceremony claims
  cover their static coalitions, and the signing claim covers adaptive corruptions.
* No field fixes the basis or the bit encoding of the check field. The claims take every value of
  `Constants`. Its field `encode` gives `E` exactly `2 ^ 128` elements (`Constants.card`), so `E` is
  isomorphic to `GF(2^128)`. `constants_nonempty_of` (`Proof/Constants.lean`) gives a value for each
  committee with fewer than `2 ^ 128` operators. No field states that the constants of the
  implementation are such a value.
* No field connects the model to the Rust code.
* No field is in the random-permutation model. The end statement of leanXMSS is in that model at the
  pinned revision of leanVM.
* The signing claim with the budget of every party, `SigningSecurityStatement`, is no field.
  `SigningBudgets.lean` states it, and `signingSecurityClosed` proves it.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  [SampleableType E]

/-- The end claims, for one committee, one check field with its constants, one `Th` with AES-128, one
circuit family and one setting. -/
structure Theorems (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    Prop where
  -- The threshold PRF `F` (the note, Section 2, and PRAWNS, Definitions 2.1 and 2.2).
  /-- `Combine'` of the parts of a quorum gives `F(msk, x)` (PRAWNS, Definition 2.1). -/
  tprfCorrectness : TprfCorrectnessStatement prims C
  /-- The threshold PRF is adaptively secure, up to `tprfError C q` for `q` counted calls (PRAWNS,
  Definition 2.2 and Theorem 5.1). -/
  tprfSecurity : TprfSecurityStatement prims C

  -- The setup by DKG, with the keygen ceremony and each bottom tree (the note, Section 2.1).
  /-- The seed generation securely computes `F_seedGen` with selective abort, with the simulator
  `seedGenSimulator` and the error `(q + seedGenSecrets C)² / 2^256` (GL05 and CDG+18). -/
  seedGenSecurity : SeedGenSecurityStatement prims C E
  /-- An honest seed generation gives the keys of `F_seedGen`, except when two derived keys collide (the note,
  Section 2.1, honest run). -/
  seedGenCompleteness : SeedGenCompletenessStatement prims C E
  /-- The honest ceremonies of a tree give the tree of `F_tree`, except when an honest check aborts
  (`treeAbortError`) (the note, Section 2.1, honest run). -/
  treeCompleteness : TreeCompletenessStatement prims K circuits settings
  /-- When the circuits compute `Th`, the dealer of `F_tree` gives the trees of `KeyGen` of the
  signing game (PRAWNS, Section 3.1, and `doc/dkg.md` 3.1). -/
  dealerTree : DealerTreeStatement prims circuits settings C
  /-- When the circuits compute `Th`, `F_tree` gives a bottom tree `b` on the top tree of the same
  seeds, except with probability `(1 - p)^L` (the note, Section 2.1, honest run). -/
  treeSuccess : TreeSuccessStatement prims circuits settings C

  -- The MPC protocol of the setup (GS20).
  /-- `Coin` securely computes `F_coin` with selective abort in the `F_rand`-hybrid model, with the
  error `0` (GS20, Lemma 3). -/
  coin : CoinStatement prims K
  /-- `MulRep` and `Reshare` in each mode securely compute `F_mult` up to an additive attack, with
  selective abort and the error `0` (GS20, Lemma 4). -/
  mult : MultStatement prims K
  /-- `MulRep` or `MulSh` and `Reshare` securely compute `F_extendMult` up to an additive attack,
  with selective abort and the error `0` (GS20, Lemma 5). -/
  extendMult : ExtendMultStatement prims K
  /-- The check with its digests securely computes `F_multVerify` with selective abort. The error is
  `checkErrorOf` and a birthday term of the hash (GS20, Lemmas 8 to 11, and CGH+18). -/
  multVerify : MultVerifyStatement prims K
  /-- A batch securely computes `F_main` in the `{F_mult, F_multVerify}`-hybrid model, up to a
  birthday term of the copy hashes (GS20, Theorem 2, for public outputs and pre-shared inputs). -/
  main : MainStatement prims K
  /-- One ceremony securely computes `F_ceremony` in the `{F_mult, F_multVerify}`-hybrid model, up
  to a birthday term of the copy hashes (GS20, Theorem 2, for all batches of a ceremony). -/
  ceremonyHybrid : CeremonyHybridStatement prims K circuits settings
  /-- An honest `Coin` gives the output of `F_coin` (GS20, Protocol 6, honest run). -/
  coinCompleteness : CoinCompletenessStatement prims K
  /-- An honest check accepts correct tuples, except when it aborts on a coin (`abortErrorOf`) (GS20,
  Protocol 17, honest run). -/
  multVerifyCompleteness : MultVerifyCompletenessStatement prims K
  /-- An honest batch gives the outputs of `F_main` (GS20, Protocol 19, honest run). -/
  mainCompleteness : MainCompletenessStatement prims K

  -- The signing (the note, Section 2.3, and PRAWNS, Definition 3.2).
  /-- An honest quorum fails with probability at most `2 (1 - p)^L`, and its signature verifies
  (the note, Section 2.3, honest run). -/
  signingCorrectness : SigningCorrectnessStatement prims C
  /-- Threshold leanXMSS is strongly unforgeable with adaptive corruption, in the random-oracle
  model. A forger that itself makes at most `q` calls of `H` and `PRG` and round-2 requests forges
  with probability at most `(q + 2^15 + 384) / 2^127` plus the two terms of the hidden keys. The
  calls of the dealer, of the honest operators and of the verification are not in `q` (PRAWNS,
  Definition 3.2, in the form of leanXMSS). -/
  stronglyUnforgeable : ThresholdLeanXmssStronglyUnforgeable prims C

/-- The security claim, for every committee, every check field of characteristic `2` with its
constants, every `Th` and AES-128, every circuit family, and every setting. -/
abbrev ThresholdLeanXmssSecurityStatement : Prop :=
  ∀ (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (K : Constants C E) (prims : Primitives) (circuits : Circuits) (settings : Settings),
    letI : SampleableType E := SampleableType.ofFintype E
    Theorems prims K circuits settings

end ThresholdLeanXmss
