# The Threshold leanXMSS proof

The target is `ThresholdLeanXmssSecurityStatement` in `ThresholdLeanXmss/Statement.lean`. It gives sixteen claims about the protocol of `ThresholdLeanXmss/Scheme.lean`, for every setting whose circuits compute `Th`.

No proof is written yet. Every step of the plan below is open, and every proof in `formal/` is a `sorry`.

## Reading order

1. Read `ThresholdLeanXmss/Statement.lean` first. It is the only file that a human reviews.
2. Read `ThresholdLeanXmss/Ideal.lean` for the functionalities and the games that the claims use.
3. Read `ThresholdLeanXmss/Reductions.lean` for the simulators and the reductions that the claims name.
4. Read `ThresholdLeanXmss/Scheme.lean` for the protocol and the execution model.

## Files

Each file in this list imports the file before it.

* `ThresholdLeanXmss/Scheme.lean` holds the operator programs, the oracle world with its counted calls, and the execution model.
* `ThresholdLeanXmss/Ideal.lean` holds the functionalities of GS20, the trusted dealer, and the games of PRAWNS and of the primitives.
* `ThresholdLeanXmss/Reductions.lean` holds `keygenSimulator`, `treeSimulator`, `prgReduction` and the three reductions of PRAWNS, Theorem 3.1.
* `ThresholdLeanXmss/Statement.lean` holds the error terms, the valid inputs and the claims as named `Prop` definitions.
* `ThresholdLeanXmssSecurity/Proof/Lemmas.lean` holds the intermediate results of the papers, each named after its source.
* `ThresholdLeanXmssSecurity.lean` states the main theorem `thresholdLeanXmss_security`.

The execution model defines `SecurelyComputes`, `SimulatedBy` and `Completes`. Every claim except the four signing claims uses one of them.

## Claims

The table of `Statement.lean` gives each statement in one sentence.

| claim | source |
| --- | --- |
| `KeygenCompletenessStatement` | the note, Section 2.1, honest run |
| `KeygenSecurityStatement` | GL05 and CDG+18 |
| `TreeCompletenessStatement` | GS20, Theorem 2, honest run |
| `TreeSecurityStatement` | GS20, Theorem 2, and GL05 |
| `CoinStatement` | GS20, Lemma 3 |
| `CoinCompletenessStatement` | GS20, Protocol 6, honest run |
| `MultStatement` | GS20, Lemma 4 |
| `ExtendMultStatement` | GS20, Lemma 5 |
| `MultVerifyStatement` | GS20, Lemmas 8 to 11, and CGH+18 |
| `MultVerifyCompletenessStatement` | GS20, Protocol 17, honest run |
| `MainStatement` | GS20, Theorem 2, for public outputs and pre-shared inputs |
| `MainCompletenessStatement` | GS20, Protocol 19, honest run |
| `TprfCorrectnessStatement` | PRAWNS, Definition 2.1 |
| `TprfSecurityStatement` | PRAWNS, Definition 2.2 and Theorem 5.1 |
| `SigningCorrectnessStatement` | PRAWNS, Section 3.1, honest run |
| `SigningSecurityStatement` | PRAWNS, Definition 3.2 and Theorem 3.1 |

## Proof plan

Every plan in this section is open. The lemmas that a plan names are in `ThresholdLeanXmssSecurity/Proof/Lemmas.lean`, with no proof yet.

### Key generation

`KeygenCompletenessStatement` follows from the honest run of `keygen`. The run differs from `F_keygen` only when two derived keys collide, and `derivedKeyCollision` bounds this event.

`KeygenSecurityStatement` follows from a sequence of hybrids from the real run to the run of `keygenSimulator`.

1. The simulator extracts the corrupt reveals from the observed `H` calls of the adversary (CDG+18).
2. The simulator programs `H`, so that `P`, the corrupt seeds and the corrupt pair keys are those of `F_keygen`.
3. The bad events are a guessed secret, a collision of two secrets, a failed programming and a failed extraction.
4. The birthday bound `keygenHashError` bounds the bad events.

### Gadgets

`CoinStatement` and `CoinCompletenessStatement` follow GS20, Lemma 3. The coin opens a random sharing from `F_rand`, so the simulation is perfect.

`MultStatement` follows GS20, Lemma 4. It uses `cdi05_pair_has_holder` and `cdi05_mulRep_correct`, and the reshare masks come from `F_rand`.

`ExtendMultStatement` follows GS20, Lemma 5. It adds `cdi05_conv_correct` and `gs20_mulSh_correct` for the Shamir inputs.

### The check

`MultVerifyStatement` follows GS20, Lemmas 8 to 11, and the digests of CGH+18, Protocol 3.3.

1. The digests compare the copies of each term at its honest holders (CGH+18, Protocol 3.3).
2. `check_word_weight_ne_zero` keeps a wrong word of tuples nonzero under the weights `x^q`.
3. `gs20_lemma8_delinearization` keeps a wrong tuple in the weighted sum.
4. `gruen_slice_step` and `gs20_lemma9_halving_step` keep a wrong claim wrong for all but two challenges.
5. `gs20_lemma10_final_step` accepts a wrong claim for at most two challenges.
6. `gs20_lemma11_final_hides` makes the opened values uniform, so the simulator samples them.
7. The sum of these errors is `checkErrorOf`, and a birthday term bounds the histories and the digests.

`MultVerifyCompletenessStatement` follows from the honest run of the check on correct tuples. The check aborts only on a zero slice coin or a failed challenge expansion, which `abortErrorOf` bounds.

### A batch and a ceremony

`MainStatement` follows GS20, Theorem 2, in the `{F_mult, F_multVerify}`-hybrid model.

1. The simulator answers the hybrid calls from the leaks of `F_mult` and `F_multVerify`.
2. After `F_multVerify` accepts, the honest copies of each term agree.
3. The outputs open as in MPClan, Appendix B, with `mpclan_honest_holder`.
4. A counted call that matches the hash of an honest copy is the only bad event.

`MainCompletenessStatement` follows from the honest run of a batch, with `cdi05_mulRep_correct` for each AND gate.

`TreeCompletenessStatement` composes `MainCompletenessStatement` and `MultVerifyCompletenessStatement` over the batches of a ceremony. `CircuitsCompute` makes the outputs those of `Th`, and `treeAbortError` bounds the aborts.

`TreeSecurityStatement` follows from a sequence of hybrids from the real ceremony to the run of `treeSimulator`.

1. The PRSS outputs of one round play `F_rand` (CDI05).
2. `prgReduction` replaces the streams under hidden keys with ideal streams, at the cost of the AES term.
3. `streamKeyError` bounds a collision of two 128-bit AES keys.
4. `MultVerifyStatement` for each batch gives the term `treeCheckError`.
5. `MainStatement` for each batch replaces the batch with `F_main`.
6. `prawns_coalition_lacks_term` gives the lacked term that the opening shifts.
7. `treeHashError` bounds a counted call that hits an honest point of the ceremony.

### Signing

`TprfCorrectnessStatement` follows from `prawns_quorum_holds_term` and `prawns_L_partition`. Each term goes to exactly one signer, so the masks cancel in pairs and the parts combine.

`TprfSecurityStatement` follows PRAWNS, Theorem 5.1.

1. `prawns_coalition_lacks_term` gives a term whose key the coalition does not hold.
2. `prawns_lemma52_guess` guesses the coalition with probability `1 / C(n, t - 1)`.
3. With a right guess, the key of the lacked term stays hidden, so the challenge value is uniform.
4. `tprfError` bounds the guesses of hidden keys and the collisions of keys.

`SigningCorrectnessStatement` follows from the honest run of `KeyGen` and of the signing. Each of the two randomizer searches fails with probability `searchFailure`, and `TprfCorrectnessStatement` makes every output verify.

`SigningSecurityStatement` follows PRAWNS, Theorem 3.1, through its games.

1. Game 1 removes a collision `E_1`, with `collisionReduction` for `Th` and `treeCollisionError` for the random oracle.
2. Game 2 guesses the target layer, key, chain and position, at the cost of the factor `guessCount`.
3. `prawns_cover_free` gives a chain whose forged position lies below the signed position.
4. `tprfReduction` bounds the step to Game 3, which answers the positions below the target from `OChallenge`.
5. `sprReduction` turns the forged chain value into an iterated SPR break.

## The axiom guard

The main theorem still depends on `sorryAx`, so the root file has no axiom guard yet. When no `sorry` remains, `ThresholdLeanXmssSecurity.lean` gets the guard of leanVM.

```lean
/-- info: 'ThresholdLeanXmssSecurity.thresholdLeanXmss_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdLeanXmss_security
```

The build then fails if a `sorry`, a `native_decide` or a new `axiom` enters the proof.
