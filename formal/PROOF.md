# The Threshold leanXMSS proof

The target is `ThresholdLeanXmssSecurityStatement` in `ThresholdLeanXmss/Statement.lean`. It gives eighteen claims about the protocol of `ThresholdLeanXmss/Scheme.lean`, for every setting.

Sixteen claims are proved. Two claims are open. The root theorem passes each open gap as one `sorry` argument for a named `Prop`.

## Reading order

1. Read `ThresholdLeanXmss/Statement.lean` first. It holds the counted world, the notions of secure computation, the games and the claims.
2. Read `ThresholdLeanXmss/Reductions.lean` for the simulators and the reductions that the claims name.
3. Read `ThresholdLeanXmss/Ideal.lean` for the functionalities and the oracles of the games.
4. Read `ThresholdLeanXmss/Scheme.lean` for the protocol, the oracles of the world and the network.

The review boundary is `Statement.lean` and the definitions that it names in the other three files. The simulators and the reductions use the network and the oracles of the games, so these stay before `Reductions.lean` in the import chain. A bound with the advantage of a reduction is only as strong as that reduction, so `Reductions.lean` is in the boundary.

## Files

Each file of `ThresholdLeanXmss/` imports the file before it. Each module of `Proof/` imports `Execution.lean` and
`Lemmas.lean`. `Check.lean` imports `Gadgets.lean`, and `Tree.lean` imports `Main.lean`, `Keygen.lean` and `Check.lean`.

* `ThresholdLeanXmss/Scheme.lean` holds the operator programs, the oracles of the world, the network and the honest runs.
* `ThresholdLeanXmss/Ideal.lean` holds the functionalities of GS20, the trusted dealer, the oracles of the games of PRAWNS and the adversaries of the games of the primitives.
* `ThresholdLeanXmss/Reductions.lean` holds `keygenSimulator`, `treeSimulator`, and `prgReduction`.
* `ThresholdLeanXmss/Statement.lean` holds the counted world, the notions of secure computation, the games, the error terms, the valid inputs and the claims as named `Prop` definitions.
* `ThresholdLeanXmssSecurity/Proof/Lemmas.lean` holds the intermediate results of the papers, each named after its source.
* `ThresholdLeanXmssSecurity/Proof/Execution.lean` holds the lemmas of the execution model that the claim proofs share.
* `Proof/Gadgets.lean`, `Proof/Tprf.lean`, `Proof/Signing.lean`, `Proof/Main.lean`, `Proof/Keygen.lean`,
  `Proof/Check.lean` and `Proof/Tree.lean` hold the claims of their area, with the partial steps of the open claims.
* `Proof/Coupling.lean` holds the round-by-round coupling of two executions, the shift of a uniform mask and the
  bound on a call that hits a secret point. The later modules of each area (`Dealer`, `MainSecurity`, `MainStages`,
  `CheckSecurity` to `CheckLast`, `KeygenSecurity` to `KeygenKnown`, `TreeSecurity` to `TreeKeyAimed`,
  `SigningSecurity` to `HiddenCore`) build on it and end in the theorem that the root uses.
* `Proof/SigningDescent.lean` and `Proof/SigningCache.lean` prove that a winning forgery with no hidden-key hit
  forces a hit, a guess or a digest partner in the cache, with the lemmas of leanVM `XmssSecurity`. `SigningCost`,
  `SigningHitLane` and `SigningGuessLane` split the cost of these events into lanes. `SigningHitProof` proves
  `HitLaneBound`. `GuessPartnerLaneBound` is false, because one commitment call has two targets. A comment in
  `SigningGuessProof` gives the trace.
* The signing gap runs on the log of the run. The root keeps `HiddenCoreAt` as the open gap.
  * `SigningPartnerBound` proves `HiddenCoreAt` from `UnchargedLaneBoundLogged` (`hiddenCoreAt_of_logged`).
  * `SigningSelection` proves `SelectionClassification`. `SigningGuardedFlag` proves `HiddenCoreAt` from the open
    `GuardedFlagCoupling` (`hiddenCoreAt_of_guardedCoupling`). Its flag is guarded by the win, and its chain target
    is partial on PRF entries that the run never computed.
  * Two earlier forms of this coupling are false. `UnchargedFlagCoupling` charges the commitment counterexample
    twice (`SigningHybrid`), and the unguarded flag in `UnchargedFlagSoundCoupling` reaches probability one
    (`SigningGuardedFlag`). A flag decided at one call cannot pay for the cached selection or for the window after
    round 1 (`SigningLanes`). The lane bound itself is not refuted.
  * `SigningFlat`, `SigningFlatEager`, `SigningCappedExpect`, `SigningLane2` and `SigningLane2Bridge` hold the flat
    run, its eager law, the expectation form of the capped bound, and the leanVM lane-2 potential with its bridges.
  * `SigningCacheLog` reconstructs the tracked cache from the call log. `SigningJointEager` proves the eager law
    for the joint result, opening log, world log and count. The eager cache itself is not part of this equality.
  * `SigningAssembly` combines the charged lane, `PartnerTransfer` and `UnchargedLaneCap` into `HiddenCoreAt`,
    assuming `R1Link`. `SigningR1Fixed` proves the cache-derived trigger, eager law, R1 bound and signed-grind
    invariant. Its module doc gives a counterexample to the remaining `R1Link`: a true-opening input hit before
    release needs its own disjunct (A41). `SigningLane2Flat` proves the base-call law and trace transport, but
    its global cached-selection flag does not identify the forged key's selection (A40).
    `SigningPartnerTransfer` transports the lazy row exactly to the split run's reconstructed log cache;
    `PartnerCacheComparison` still compares that event with the eager-cache event.
    `SigningPartnerCompare` proves actual split-run cache growth, agreement at tracked inputs outside bottom-message trials,
    and exact transport of `AlternativeCommitment`. Its bottom-partner transfer requires preservation of
    the selected pair; that preservation is not assumed for every run.
  * `SigningUnchargedCap` proves that the input-hit and lane-2 probabilities share one capped expectation,
    even when the events overlap. Its concrete transports and `InputCachedLaneCap` remain open. `TopRow` and
    `AbsentRow` remain separate D17 obligations. `SigningTopCache` proves top-opening stability at the actual
    verification prefix from `PrefixBottomSuccess`; a recorded tree request alone does not imply success.
  * `SigningOpening`, `SigningPartnerLink`, `SigningGuessLink`, `SigningSupport` and `SigningReleased` hold the
    events and the lemmas of this route. `SigningUncharged` holds an earlier reduction to a leanVM monitor.
* `Proof/TreeSim.lean` reduces `TreeSimulationHop` to three independent `Prop`s. `TreeSimStages`, `TreeSimCheck`
  and `TreeSimHash` hold the partial proofs of these `Prop`s, and their `Finish` modules continue them.
* `TreeCompose` identifies the missing reuse of a hidden digest salt; `TreeEvents` adds it in `treeSimEvents2`.
  The current route is `treeSimulationHop_of_pairs3` in `TreeEvents3`: its bad event also contains the
  budget-domain collision. `TreeTwin3` supplies the corresponding twin-relation assembly. `TreeTwinNext`
  proves collector transitions and leaves `TreeTwinOtherGoal` for entry and the other rounds.
* `TreeSetupKeys` proves `TreeAgreementSetupKeys`. `TreeLockstepRun` proves `TreeLockstepRecordsRunGoal` and
  derives the common schedule from `TreeLockstepOpenedGoal`, using the encoding determined by first-run
  outputs. Opening agreement remains open. `TreeLockstepStages` proves `TreeTwinDigestDrawsGoal` and reduces
  the digest relation to `TreeLockstepStagesGoal`, whose reachable-round bridge remains open.
  `TreeLockstepOpened` proves the synchronized digest and opening boundaries under the budget-collision
  guard: a surviving digest continuation forces honest held histories to agree; given common held copies,
  every accepted joint opening returns their value. Aligning those boundaries with each audited batch
  and carrying the agreed copies through the check remain necessary for `TreeLockstepOpenedGoal`.
* `TreeRawSalt` proves the hidden-block and continuation laws and reduces the raw-salt estimate to
  `TreeRawSaltCeremonyRepresentation`. `TreeCheckBranches` combines the setup branches from the opening
  agreement, `TreeCheckUncountedGuess` and `TreeCheckCountedCut`; it does not close those premises.
* `TreeFromCache` and `TreeKeyFromCache` prove the component prefix bridges with fixed inputs and budgets
  `q0 + q`. `LifetimeMasks` supplies the private mask service and hit bounds, with `PrivateSigningTransport`
  still open. `LifetimeBridge` retains the joint distribution of dealer keys, adaptive selection and cache;
  its adaptive key and simulation hops remain open. `LifetimeJointKey` bounds protected PRSS points in
  the selecting prefix by `q0 * prssKeyCount C / 2^256` and proves the prefix-refresh comparison with a
  common continuation. The adaptive setup and tail remain. These modules do not establish a lifetime statement.
* `ThresholdLeanXmssSecurity.lean` states the main theorem `thresholdLeanXmss_security` and the axiom guards.

`Statement.lean` defines `SecurelyComputes`, `SimulatedBy` and `Completes`. Every claim of the keygen, the ceremonies and the gadgets except `DealerTreeStatement` and `TreeSuccessStatement` uses one of them.

## Model

This is the model of every claim. The header of `Statement.lean` gives it in full.

* Every claim is for a classical adversary. No claim covers quantum queries.
* `Committee` has `n = 2t - 1` operators. The trusted-dealer committees `n = 3f + 1` of the note are out of scope.
* The rounds are synchronous, and the links are private and authenticated (GS20, Section 3.1).
* The keygen and the ceremonies have security with selective abort (GL05). Each operator aborts alone.
* The keygen and each ceremony are separate claims. Each has its own static coalition of at most `t - 1`
  operators, corrupted before it starts, and a rushing malicious adversary.
* The signing adversary corrupts adaptively, at most `t - 1` operators over the lifetime. A corruption gives
  only the keys, because an operator erases its ceremony state at the end of each ceremony.
* The claims cover no concurrent runs. A ceremony runs with no other ceremony and no open signing session.
* The signing game holds the authorization resource `F_auth`, the map `bound` of `tsigOracles`. It fixes one
  message for each key over all honest operators (`doc/sign.md`, Section 4.1).
* `Th` is one fixed function in the keygen and ceremony claims. All of `H` is a random oracle in the signing
  claim. The gap between the two is the random-oracle heuristic for Keccak.
* The signing budget `q` counts the calls of every party (`HasSigningQueryBound`). The other budgets count the
  calls of the adversary and of the distinguisher. No budget is a time bound.
* The claims give no composed end-to-end claim.

## Claims

The table of `Statement.lean` gives each statement in one sentence.

| claim | source | status |
| --- | --- | --- |
| `KeygenCompletenessStatement` | the note, Section 2.1, honest run | proved, `keygenCompleteness` in `Keygen` |
| `KeygenSecurityStatement` | GL05 and CDG+18 | proved, `keygenSecurityClosed` in `KeygenAlias` |
| `TreeCompletenessStatement` | GS20, Theorem 2, honest run | proved, `treeCompleteness` in `Tree` |
| `TreeSecurityStatement` | GS20, Theorem 2, and GL05 | open at `TreeSimulationHop`; current conditional route is `treeSimulationHop_of_pairs3` in `TreeEvents3`, feeding `treeSecurityOfSimClosed` in `TreeKeyAimed` |
| `DealerTreeStatement` | PRAWNS, Section 3.1, and `doc/dkg.md` 3.1 | proved, `dealerTreeProof` in `Dealer` |
| `TreeSuccessStatement` | PRAWNS, Section 3.1, honest run | proved, `treeSuccessProof` in `Dealer` |
| `CoinStatement` | GS20, Lemma 3 | proved, `coinSecurity` in `Gadgets` |
| `CoinCompletenessStatement` | GS20, Protocol 6, honest run | proved, `coinCompleteness` in `Gadgets` |
| `MultStatement` | GS20, Lemma 4 | proved, `multStatement` in `Gadgets` |
| `ExtendMultStatement` | GS20, Lemma 5 | proved, `extendMultSecurity` in `Gadgets` |
| `MultVerifyStatement` | GS20, Lemmas 8 to 11, and CGH+18 | proved, `multVerifyClosed` in `CheckSplit` |
| `MultVerifyCompletenessStatement` | GS20, Protocol 17, honest run | proved, `multVerifyCompleteness` in `Check` |
| `MainStatement` | GS20, Theorem 2, for public outputs and pre-shared inputs | proved, `mainStatementFull` in `MainStages` |
| `MainCompletenessStatement` | GS20, Protocol 19, honest run | proved, `mainCompleteness` in `Main` |
| `TprfCorrectnessStatement` | PRAWNS, Definition 2.1 | proved, `tprfCorrectness` in `Tprf` |
| `TprfSecurityStatement` | PRAWNS, Definition 2.2 and Theorem 5.1 | proved, `tprfSecurity` in `Tprf` |
| `SigningCorrectnessStatement` | PRAWNS, Section 3.1, honest run | proved, `signingCorrectness` in `Signing` |
| `SigningSecurityStatement` | PRAWNS, Definition 3.2, in the random-oracle model | open at `HiddenCoreAt`, feeding `signingSecurityFull` in `HiddenCore`; `SigningAssembly` supplies the conditional row assembly, with the R1 correction and row bounds still open |

The new proof modules marked `pending review` in `TODO.md` compile with their axiom guards, but do not close
either root gap. `TODO.md` records their exact remaining obligations and review status. The lifetime statement
draft still waits for B3 and is not one of the eighteen component claims above.

## Proof plan

The lemmas that a plan names are in `ThresholdLeanXmssSecurity/Proof/Lemmas.lean`, all proved. An open claim reduces to its named goal in the table above, and the plan of this section gives the rest of its proof.

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

`TreeCompletenessStatement` follows from the honest run of a ceremony with the real gadgets, batch by batch, in the steps of `MainCompletenessStatement` and `MultVerifyCompletenessStatement`. `treeAbortError` bounds the aborts, with one birthday term over the coin keys of all batches.

`DealerTreeStatement` follows job by job. `CircuitsCompute` makes each circuit give `referenceJob`. The chain steps and the commitments of `referenceJob` are inputs of the fixed `Th`, so they leave the cache unchanged. The two runs make the same PRF calls in the same order when `batchSize > 0`.

`TreeSuccessStatement` follows from `DealerTreeStatement` and the honest run of `KeyGen`. The check of the top root passes, because the chain values of the top signature walk to the chain ends of the top tree. The randomizer search fails with probability `searchFailure`, as in `SigningCorrectnessStatement`.

`TreeSecurityStatement` follows from a sequence of hybrids from the real ceremony to the run of `treeSimulator`.

1. The PRSS outputs of one round play `F_rand` (CDI05).
2. `prgReduction` replaces the streams under hidden keys with ideal streams, at the cost of its multi-key PRF advantage against `hiddenStreams`.
3. `streamKeyError` bounds a collision of two 128-bit AES keys.
4. `MultVerifyStatement` for each batch gives the term `treeCheckError`.
5. `MainStatement` for each batch replaces the batch with `F_main`.
6. `prawns_coalition_lacks_term` gives the lacked term that the opening shifts.
7. `treeHashError` bounds a counted call that hits an honest point of the ceremony.

The current assembly, `treeSimulationHop_of_pairs3`, requires `TreeSimStagesGoal3`,
`TreeSimHashHonestBudget`, `TreeSimHashRawSaltEstimate`, a `TreeSaltStageSplits` value and its
`TreeSaltStagesPairs` proof, and `TreeSimCheckSetupBranches3`. Setup-key agreement and each successful operator's record schedule are proved.
The synchronized openings, reachable-round invariant, ceremony-to-block representation, and check cut
remain obligations; the conditional assembly does not supply them.

### Signing

`TprfCorrectnessStatement` follows from `prawns_quorum_holds_term` and `prawns_L_partition`. Each term goes to exactly one signer, so the masks cancel in pairs and the parts combine.

`TprfSecurityStatement` follows PRAWNS, Theorem 5.1.

1. `prawns_coalition_lacks_term` gives a term whose key the coalition does not hold.
2. `prawns_lemma52_guess` guesses the coalition with probability `1 / C(n, t - 1)`.
3. With a right guess, the key of the lacked term stays hidden, so the challenge value is uniform.
4. `tprfError` bounds the guesses of hidden keys and the collisions of keys.

`SigningCorrectnessStatement` follows from the honest run of `KeyGen` and of the signing. Each of the two randomizer searches fails with probability `searchFailure`, and `TprfCorrectnessStatement` makes every output verify.

`SigningSecurityStatement` follows the proof of leanVM (`formal/lean_xmss/PROOF.md`). The hidden keys play the seed of leanVM. The game does not reduce to `LeanXmssSecurityStatement` itself, because the forger also sees the top chain ends, the bottom trees, `c_e`, `ρ_e` before round 2 and the parts below the threshold.

1. Hidden keys. At most `t - 1` corrupt operators leave one term seed and the keys of the honest pairs hidden. A call on a hidden key costs `seedHitError`, and two equal keys cost `seedCollisionError`. Without these events, each `F(x)` is a fresh uniform value until `signersAt` reaches `t`, by the lazy-sampling argument of the proof of PRAWNS, Theorem 5.1. This covers `ρ_e` before round 1, the chain starts, the masks and the parts below the threshold.
2. Positions. Every input of `Th` has a position, by `hashDomainFields_injective` of leanVM. A leaf or a node position has one honest input. A digest position has one selected honest input, by `breaksOneMessagePerKey`, and the other trials of its search give no codeword.
3. Opened randomizer. An honest signer that accepts `ρ' ≠ ρ_e` with `Th(P, A_rnd(e, 1), ρ' ‖ 0) = c_e` is a hit on the output `c_e`. Otherwise every honest signer of key `e` uses `ρ_e` and one codeword. This is a proof obligation.
4. Bad events. A win implies a bad event at a call of the forger or of the verification, by the descent of leanVM over two layers. A hit gives an honest output from another input. A guess queries a hidden honest input, namely a chain value below the opened position. A partner meets the output that a later search selects.
5. Costs. A hit and a guess cost `2^-128` for each call. A partner costs `2^-128` for each digest call, as the codeword probability `p` of the earlier output times `1 / #C` for the selected output. A bound of `2^-128` for each pair alone is false, because the search selects one output from several trials. Round 1 opens `ρ_e` before the search, so the lemma of leanVM with a hidden `R_0` does not apply as it is.
6. Sum. Two units for each call give `signingHashError q`. The calls of `KeyGen` count in `q` and are never bad, so they pay the lower-order terms.

`hiddenCoreAt_of_link` in `SigningAssembly` makes this accounting explicit. The charged lane is proved. For the
uncharged lane, `probEvent_lane2_sum_le` in `SigningUnchargedCap` retains the sum of the input-hit and lane-2
probabilities under one `q / 2^128` cap; transporting the actual signing rows to that hybrid remains open.
The top-partner and absent-start rows have separate hypotheses and depend on D17. The partner transfer still
requires `PartnerCacheComparison`. The cache-derived trigger and R1 estimate are proved, but the link needs
the missing true-opening input-side disjunct (A41), and the lane-2 row needs the forged key's cached-selection
flag (A40). Neither correction has been assumed by the row assembly.

## The axiom guard

`ThresholdLeanXmssSecurity.lean` has the axiom guard, with the current footprint. The open claims hold `sorryAx`, so the footprint of the main theorem is `propext`, `sorryAx`, `Classical.choice` and `Quot.sound`. A guard for each proved claim holds its footprint at `propext`, `Classical.choice` and `Quot.sound`. When no `sorry` remains, the guard of the main theorem changes to this form.

```lean
/-- info: 'ThresholdLeanXmssSecurity.thresholdLeanXmss_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdLeanXmss_security
```

The build then fails if a `sorry`, a `native_decide` or a new `axiom` enters the proof.
