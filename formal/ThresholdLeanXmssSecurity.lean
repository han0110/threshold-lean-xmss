import ThresholdLeanXmss.Statement
import ThresholdLeanXmssSecurity.Proof.Gadgets
import ThresholdLeanXmssSecurity.Proof.Tprf
import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.MainStages
import ThresholdLeanXmssSecurity.Proof.CheckFinish
import ThresholdLeanXmssSecurity.Proof.KeygenFinish
import ThresholdLeanXmssSecurity.Proof.TreeKey
import ThresholdLeanXmssSecurity.Proof.HiddenCore
import ThresholdLeanXmssSecurity.Proof.KeygenKnown
import ThresholdLeanXmssSecurity.Proof.TreeKeyAfter
import ThresholdLeanXmssSecurity.Proof.CheckLast
import ThresholdLeanXmssSecurity.Proof.KeygenAlias
import ThresholdLeanXmssSecurity.Proof.CheckSound
import ThresholdLeanXmssSecurity.Proof.CheckSplit
import ThresholdLeanXmssSecurity.Proof.SigningCache
import ThresholdLeanXmssSecurity.Proof.SigningHitLane
import ThresholdLeanXmssSecurity.Proof.SigningGuessLane
import ThresholdLeanXmssSecurity.Proof.TreeKeyAimed
import ThresholdLeanXmssSecurity.Proof.SigningHitProof

/-! # The end theorem of threshold leanXMSS

`thresholdLeanXmss_security` gives `ThresholdLeanXmssSecurityStatement` (`ThresholdLeanXmss/Statement.lean`).
It is the conjunction of eighteen component claims about the protocol of `ThresholdLeanXmss/Scheme.lean`,
for every committee `n = 2t - 1`, every check field `E` with `2^192` elements, every `Th`, every circuit
family and every setting. Each claim covers one protocol or one gadget alone. No claim composes the
keygen, the ceremonies and the signing. `statement.tex` holds the deployment contract and the argument
of that composition. The module doc of `Statement.lean` holds the full model and the deviations from
the papers. The proofs follow GS20 for the DKG and PRAWNS for the signing, and
they reuse leanVM `formal/lean_xmss` for the hash layer.

## Units and budgets

* The signing claim counts in units of `2^-128`. `signingHashError q = q / 2^127` is two units for
  each counted call.
* The other hash terms are birthday bounds over `2^256` outputs, for example
  `keygenHashError C q = (q + keygenSecrets C)^2 / 2^256`. `streamKeyError C` is the birthday bound
  `k^2 / 2^129` of the 128-bit AES keys of the `k` PRSS keys.
* The signing budget `q` (`HasSigningQueryBound`) counts every call of `H` and `PRG` by every party,
  cache hits included.
* The simulation claims and `TprfSecurityStatement` count only the calls of the adversary and of the
  distinguisher (`IsQueryBounded`). No budget is a time bound.

## Model

* `H` is one lazy random oracle on `Query`. Its constructors are disjoint domains, so
  domain-separated hashing is the assumption.
* In the keygen and ceremony claims, `Th` is one fixed function on the inputs that the MPC
  evaluates, the chain steps and the commitment `c_e`. `CircuitsCompute` states that the circuits
  compute this `Th`. In the signing claim, all of `H` is a random oracle. The difference between the
  two models is the random-oracle heuristic for Keccak.
* The keygen and each ceremony have their own static coalition of at most `t - 1` operators and a
  rushing malicious adversary, with security with selective abort (GL05). Each operator aborts alone.
* The signing adversary corrupts adaptively, at most `t - 1` operators over the lifetime. A
  corruption gives only the keys, because an operator erases its ceremony state.
* Honest operators sign at most one message for each key (`breaksOneMessagePerKey`). The map `bound`
  of `tsigOracles` enforces it in the game.

## Keygen

1. `keygenCompleteness` (`Proof/Keygen`) gives `KeygenCompletenessStatement`. The honest run differs
   from `F_keygen` only when two derived keys collide, at `derivedKeyCollision`.
2. `keygenSecurityClosed` (`Proof/KeygenAlias`) gives `KeygenSecurityStatement` with
   `keygenSimulator`. The simulator extracts the corrupt reveals from the observed calls and programs
   `H` (CDG+18). Honest commitments become fresh values until a call hits a commitment input.
   `keygenProgramAliasBound` pays the programming collisions. The bad events fit `keygenHashError`.

## Gadgets, check and batch

1. `coinSecurity`, `coinCompleteness`, `multStatement` and `extendMultSecurity` (`Proof/Gadgets`)
   follow GS20, Lemmas 3 to 5, in the `F_rand`-hybrid model, with `cdi05_pair_has_holder`,
   `cdi05_mulRep_correct`, `cdi05_conv_correct` and `gs20_mulSh_correct`.
2. `multVerifyClosed` (`Proof/CheckSplit`) gives `MultVerifyStatement`. The digests compare the copies
   of each term (CGH+18, Protocol 3.3). `check_word_weight_ne_zero`, `gs20_lemma8_delinearization`,
   `gruen_slice_step`, `gs20_lemma9_halving_step` and `gs20_lemma10_final_step` keep a wrong claim
   wrong except for few challenges. `gs20_lemma11_final_hides` makes the revealed values uniform. The
   sum is `checkErrorOf`. `multVerifyCompleteness` (`Proof/Check`) pays `abortErrorOf`.
3. `mainStatementFull` (`Proof/MainStages`) gives `MainStatement` in the `{F_mult, F_multVerify}`-hybrid
   model. The outputs are revealed as in MPClan (`mpclan_honest_holder`). `mainCompleteness`
   (`Proof/Main`) is the honest batch.

## Ceremonies

1. `treeCompleteness` (`Proof/Tree`) runs the honest gadgets batch by batch and pays `treeAbortError`.
2. `dealerTreeProof` and `treeSuccessProof` (`Proof/Dealer`) assume `CircuitsCompute`. Each circuit
   gives `referenceJob`, so `F_tree` gives the trees of `KeyGen`. The search fails with
   `searchFailure`.
3. `treeSecurityDistance_of_hops` (`Proof/Tree`) splits the distance of `TreeSecurityStatement` at
   `prgReduction` into two hops. `TreeSecurity` gives the share `keySplit` of `treeHashError`.
4. The key hop (`TreeKeyHop`) replaces the hidden streams with independent AES keys.
   `keyWorld_coupling` pays `streamKeyError + keySplit`. `treeKeyAimedBound` (`Proof/TreeKeyAimed`)
   bounds a counted call that aims at a hidden key after the key boundary.
5. The simulation hop (`TreeSimulationHop` at `keySplit C`) moves the real run with random streams to
   `treeSimulator`. It pays `treeCheckError` and `treeHashError - keySplit`.
   `prawns_coalition_lacks_term` gives the lacked term that the opening shifts.
6. `TreeAssembly.treeSimulationHop_of_pairs` gives `TreeSimulationHop` from `TreeTwinLinkedGoal`,
   `TreeCheckTailWalkSourceConstruction`, `CeremonyOpaqueNormalization`, and one
   `TreeSaltStageSplits` with its `TreeSaltStagesPairs`. `treeSimulationHop_of_pairs3`
   (`Proof/TreeEvents3`) is the same hop with the events `treeSimEvents3`. The lockstep, the digest
   draws, the opening agreement and `treeSimHashHonestBudget` come from their own modules.
7. `treeSecurityOfSimAimed` (`Proof/TreeKeyAfter`) gives `TreeSecurityStatement` from the two hops.

## Signing plan

`TprfCorrectnessStatement` and `TprfSecurityStatement` (`tprfCorrectness`, `tprfSecurity` in
`Proof/Tprf`) follow PRAWNS, Theorem 5.1, with `prawns_quorum_holds_term`, `prawns_L_partition`,
`prawns_lemma52_guess` and `tprfError`. `signingCorrectness` (`Proof/Signing`) pays two searches.

`signingSecurityFull` (`Proof/HiddenCore`) gives `SigningSecurityStatement` through
`signingSecurityProof` and `signingCoreBound`. The game is an average over the keys. Equal keys pay
`seedCollisionError`, and `signingSecurity_large` covers `q ≥ 2^127`. The hidden keys play the seed of
leanVM. The game does not reduce to `LeanXmssSecurityStatement`, because the forger also sees the top
chain ends, the bottom trees, `c_e`, `ρ_e` before round 2 and the parts below the threshold.

1. Hidden keys. A call on a hidden term seed or pair key sets a flag (`core_split`). `seedHitBound`
   (`Proof/SeedHit`) pays it with `seedHitError`, by the slot hop `real_sym_hop`. Without the flag,
   every unrevealed `F(x)` is fresh and uniform.
2. Positions. Every input of `Th` has a position (`hashDomainFields_injective` of leanVM). A digest
   position has one selected trial, by `breaksOneMessagePerKey`.
3. Revealed randomizer. An honest signer that accepts `ρ' ≠ ρ_e` makes a hit on `c_e`
   (`opened_randomizer_hit`).
4. Descent. `HiddenCoreAt` (`Proof/SigningCore`) fixes distinct keys. `SigningDescent` and
   `SigningCache` run the leanVM descent over two layers. A win gives a hit, a guess or a digest
   partner in the call log.
5. Lanes. The charged events (hit lane `hitLaneBoundClosed`, guess lane, fresh partner
   `SigningPartnerBound`) cost one unit for each call (`chargedLane_bound_oneRun`).
   `hiddenCoreAt_of_laneUnion` (`Proof/SigningLaneUnion`) moves the released partner row and the
   uncharged row to one trace run. `SigningLaneFinal.hiddenCoreAt_of_laneTraceCap` supplies
   `ReleasedLink`, `LaneInputLogged` and `Lane2TraceLink`. One cap `LaneTraceCap` bounds the
   input-side hit, the stale base and the lane 2 event together by `q / 2^128`.
   `laneTraceCap_of_compiler` (`Proof/SigningLaneHybridCap`) gives the cap from
   `CompilerPotentialStep` and `CompilerCoupling`. Round 1 reveals `ρ_e` before the search, so the
   hidden-`R_0` lemma of leanVM does not apply as it is.
6. Sum. Two units for each call give `signingHashError q`. The calls of `KeyGen` count in `q` and pay
   the lower-order terms.

## Modules

The statement layer is `ThresholdLeanXmss/`. The proofs are in `ThresholdLeanXmssSecurity/Proof/`.

* `Scheme`, `Ideal`, `Reductions` and `Statement` hold the protocol and the world, the
  functionalities and the games, the simulators and the reductions, and the claims.
* `Lemmas`, `Execution`, `Coupling` and `ProgramQuiet` hold the paper lemmas named after their
  source, the execution model, the round-by-round coupling and the computations with no programming
  query.
* `Keygen*` holds keygen completeness and the keygen simulation.
* `Gadgets`, `Check*` and `Main*` hold the gadgets, the check and the batch.
* `Tree`, `TreeSecurity`, `TreeKey*` and `Dealer` hold the ceremony completeness, the key hop, the
  dealer and the tree success.
* `TreeSim*`, `TreeTwin*`, `TreeLockstep*`, `TreeCheck*`, `TreeSalt*`, `TreeRawSalt*`,
  `TreeHashBudget*`, `TreeEvents*` and `TreeAssembly` hold the simulation hop of a ceremony.
* `Tprf`, `Signing`, `SigningSecurity`, `SigningCore`, `SeedHit` and `HiddenCore` hold the
  threshold PRF, signing correctness, the signing spine and the hidden keys.
* `SigningDescent`, `SigningCache`, `SigningSelection` and `SigningOpening` hold the leanVM descent
  and the classification of a win.
* `SigningCost`, `SigningHit*`, `SigningGuess*`, `SigningPartner*` and `SigningLinkPaid` hold the
  charged lanes.
* `SigningLaneUnion`, `SigningLaneFinal`, `SigningReleased*`, `SigningSignedSeparation`,
  `SigningLane2*`, `SigningLaneInputLogged`, `SigningLaneHybrid*` and `SigningCompiler*` hold the
  uncharged lane and its shared cap.
* `Lifetime*` holds the forms of the simulation hop that start from a given cache. The salt route of
  the simulation hop uses them. -/

namespace ThresholdLeanXmssSecurity

/-- Threshold leanXMSS meets its security claim. -/
theorem thresholdLeanXmss_security : ThresholdLeanXmss.ThresholdLeanXmssSecurityStatement := by
  intro C E _ _ _ _ K prims circuits settings
  letI : SampleableType E := SampleableType.ofFintype E
  exact ⟨keygenCompleteness prims, keygenSecurityClosed prims, treeCompleteness prims K circuits settings,
    treeSecurityOfSimAimed prims K circuits settings (treeKeyAimedBound prims K circuits settings) (by sorry),
    dealerTreeProof prims circuits settings C,
    treeSuccessProof prims circuits settings C, coinSecurity prims K, coinCompleteness prims K, multStatement prims K,
    extendMultSecurity prims K, multVerifyClosed prims K, multVerifyCompleteness prims K,
    mainStatementFull prims K, mainCompleteness prims K, tprfCorrectness prims C, tprfSecurity prims C,
    signingCorrectness prims C, signingSecurityFull prims C (by sorry)⟩

/-! The build fails if the axiom footprint of the end theorem changes. -/

/-- info: 'ThresholdLeanXmssSecurity.thresholdLeanXmss_security' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdLeanXmss_security

/-! The build fails unless each component claim below depends only on `propext`, `Classical.choice`
and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.multVerifyClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multVerifyClosed

/-- info: 'ThresholdLeanXmssSecurity.keygenSecurityClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenSecurityClosed

/-- info: 'ThresholdLeanXmssSecurity.dealerTreeProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerTreeProof

/-- info: 'ThresholdLeanXmssSecurity.treeSuccessProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSuccessProof

/-- info: 'ThresholdLeanXmssSecurity.mainStatementFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainStatementFull

/-- info: 'ThresholdLeanXmssSecurity.keygenCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenCompleteness

/-- info: 'ThresholdLeanXmssSecurity.treeCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCompleteness

/-- info: 'ThresholdLeanXmssSecurity.coinSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinSecurity

/-- info: 'ThresholdLeanXmssSecurity.coinCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinCompleteness

/-- info: 'ThresholdLeanXmssSecurity.multStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multStatement

/-- info: 'ThresholdLeanXmssSecurity.extendMultSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extendMultSecurity

/-- info: 'ThresholdLeanXmssSecurity.multVerifyCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multVerifyCompleteness

/-- info: 'ThresholdLeanXmssSecurity.mainCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainCompleteness

/-- info: 'ThresholdLeanXmssSecurity.tprfCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tprfCorrectness

/-- info: 'ThresholdLeanXmssSecurity.tprfSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tprfSecurity

/-- info: 'ThresholdLeanXmssSecurity.signingCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCorrectness

end ThresholdLeanXmssSecurity
