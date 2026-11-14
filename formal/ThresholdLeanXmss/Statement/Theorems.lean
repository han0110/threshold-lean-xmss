import ThresholdLeanXmss.Statement.Signing

/-!
# The theorems

Each field of `Theorems` is one end claim about the protocol of `Scheme.lean`, at the level at
which GS20 and PRAWNS state them. The file of `Statement/` that defines a claim holds its game, its
error terms and its deviations from the papers. `ThresholdLeanXmssSecurity.lean` holds the root
theorem of `ThresholdLeanXmssSecurityStatement` and the axiom guards.

The two main claims are these.

* No adversary with a bounded budget distinguishes the keygen from a trusted dealer with selective
  abort, up to the error that the claim names (`keygenSecurity`). `dealerTree` states that the dealer
  of a ceremony gives the trees of the signing game.
* Signing with a trusted dealer is strongly unforgeable with adaptive corruption
  (`stronglyUnforgeable`).

The other fields are the honest runs, the gadgets of GS20 and the threshold PRF of PRAWNS. GS20
states no completeness lemma. Security with abort alone allows a protocol that always aborts, so
each completeness field is the honest run of its protocol.

## Model

* There are `n = 2t - 1` operators, synchronous rounds and private authenticated links (GS20,
  Section 3.1). At most `t - 1` operators are corrupt over the lifetime of the key.
* The keygen and each ceremony are separate claims. Each has a rushing malicious adversary with its
  own static coalition. The gadget claims are in the `F_rand`-hybrid model, and the PRSS outputs of
  one round realize `F_rand` (CDI05). The keygen and ceremony claims run the real network with the
  real PRSS.
* The signing adversary corrupts adaptively, and a corruption gives only the keys of an operator.
  After a ceremony, an operator erases its ceremony state.
* Honest operators sign at most one message at each key over all quorums
  (`breaksOneMessagePerKey`). The signing game enforces it, the PoC does not, and production must.
* `H` is one lazy random oracle on `Query`, with one domain for each constructor. `PRG` is AES-128
  under a hash of the key, and the ceremony claim pays its multi-key PRF advantage.
* In the keygen and ceremony claims, `Th` is one fixed function on the inputs that the MPC
  evaluates, namely the chain steps and the commitment `c_e`. In the signing claim, all of `H` is a
  lazy random oracle, `Th` included. The gap between the two models is the random-oracle heuristic
  for Keccak.
* `F_tree` runs the circuits of the ceremony, so the ceremony claims are stated for every circuit
  family.
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

* No field states that a ceremony securely computes `F_tree`. `Dkg.lean` states this claim as
  `TreeSecurityStatement`, with the simulator `treeSimulator`, and no theorem proves it. The fields
  on a ceremony are its honest run (`treeCompleteness`) and the two facts on its dealer
  (`dealerTree` and `treeSuccess`).
* No field composes the keygen, the ceremonies and the signing. Each field covers one protocol or
  one gadget alone. `statement.tex` holds the deployment contract and the argument of that
  composition.
* No field covers a corruption between two ceremonies. The keygen and ceremony claims cover their
  static coalitions, and the signing claim covers adaptive corruptions.
* No field fixes the basis or the bit encoding of the check field. The claims take every value of
  `Constants`. Its field `encode` gives `E` exactly `2 ^ 192` elements (`Constants.card`), so `E` is
  isomorphic to `GF(2^192)`. `constants_nonempty` gives a value only for the committee of one
  operator, so it does not instantiate the implementation.
* No field connects the model to the Rust code.
* No field is in the random-permutation model. leanXMSS is in that model at the revision `64f80302`
  of leanVM.
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
  /-- An honest keygen gives the keys of `F_keygen`, except when two derived keys collide (the note,
  Section 2.1, honest run). -/
  keygenCompleteness : KeygenCompletenessStatement prims C E
  /-- The keygen securely computes `F_keygen` with selective abort, with the simulator
  `keygenSimulator` and the error `(q + keygenSecrets C)² / 2^256` (GL05 and CDG+18). -/
  keygenSecurity : KeygenSecurityStatement prims C E

  /-- An honest ceremony gives the tree of `F_tree`, except when an honest check aborts
  (`treeAbortError`) (GS20, Theorem 2, honest run). -/
  treeCompleteness : TreeCompletenessStatement prims K circuits settings
  /-- When the circuits compute `Th`, the dealer of `F_tree` gives the trees of `KeyGen` of the
  signing game (PRAWNS, Section 3.1, and `doc/dkg.md` 3.1). -/
  dealerTree : DealerTreeStatement prims circuits settings C
  /-- When the circuits compute `Th`, `F_tree` gives a bottom tree `b` on the top tree of the same
  seeds, except with probability `(1 - p)^L` (PRAWNS, Section 3.1, honest run). -/
  treeSuccess : TreeSuccessStatement prims circuits settings C

  /-- `Coin` securely computes `F_coin` with selective abort in the `F_rand`-hybrid model, with the
  error `0` (GS20, Lemma 3). -/
  coin : CoinStatement prims K
  /-- An honest `Coin` gives the output of `F_coin` (GS20, Protocol 6, honest run). -/
  coinCompleteness : CoinCompletenessStatement prims K
  /-- `MulRep` and `Reshare` in each mode securely compute `F_mult` up to an additive attack, with
  selective abort and the error `0` (GS20, Lemma 4). -/
  mult : MultStatement prims K
  /-- `MulRep` or `MulSh` and `Reshare` securely compute `F_extendMult` up to an additive attack,
  with selective abort and the error `0` (GS20, Lemma 5). -/
  extendMult : ExtendMultStatement prims K
  /-- The check with its digests securely computes `F_multVerify` with selective abort. The error is
  `checkErrorOf` and a birthday term of the hash (GS20, Lemmas 8 to 11, and CGH+18). -/
  multVerify : MultVerifyStatement prims K
  /-- An honest check accepts correct tuples, except when it aborts on a coin (`abortErrorOf`) (GS20,
  Protocol 17, honest run). -/
  multVerifyCompleteness : MultVerifyCompletenessStatement prims K
  /-- A batch securely computes `F_main` in the `{F_mult, F_multVerify}`-hybrid model, up to a
  birthday term of the copy hashes (GS20, Theorem 2, for public outputs and pre-shared inputs). -/
  main : MainStatement prims K
  /-- An honest batch gives the outputs of `F_main` (GS20, Protocol 19, honest run). -/
  mainCompleteness : MainCompletenessStatement prims K

  /-- `Combine'` of the parts of a quorum gives `F(msk, x)` (PRAWNS, Definition 2.1). -/
  tprfCorrectness : TprfCorrectnessStatement prims C
  /-- The threshold PRF is adaptively secure, up to `tprfError C q` for `q` counted calls (PRAWNS,
  Definition 2.2 and Theorem 5.1). -/
  tprfSecurity : TprfSecurityStatement prims C

  /-- An honest quorum fails with probability at most `2 (1 - p)^L`, and its signature verifies
  (PRAWNS, Section 3.1, honest run). -/
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
