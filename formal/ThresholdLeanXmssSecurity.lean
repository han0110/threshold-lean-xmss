import ThresholdLeanXmss.Statement
import ThresholdLeanXmssSecurity.Proof.Gadgets
import ThresholdLeanXmssSecurity.Proof.Tprf
import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.MainStages
import ThresholdLeanXmssSecurity.Proof.CheckFinish
import ThresholdLeanXmssSecurity.Proof.SeedGenFinish
import ThresholdLeanXmssSecurity.Proof.HiddenCore
import ThresholdLeanXmssSecurity.Proof.SeedGenKnown
import ThresholdLeanXmssSecurity.Proof.CheckLast
import ThresholdLeanXmssSecurity.Proof.SeedGenAlias
import ThresholdLeanXmssSecurity.Proof.CheckSound
import ThresholdLeanXmssSecurity.Proof.CheckSplit
import ThresholdLeanXmssSecurity.Proof.SigningCache
import ThresholdLeanXmssSecurity.Proof.SigningHitLane
import ThresholdLeanXmssSecurity.Proof.SigningGuessLane
import ThresholdLeanXmssSecurity.Proof.SigningHitProof
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Coupling
import ThresholdLeanXmssSecurity.Proof.SigningOwnBudget
import ThresholdLeanXmssSecurity.Proof.SigningStronglyUnforgeable

/-! # The end theorem of threshold leanXMSS

`thresholdLeanXmss_security` gives `ThresholdLeanXmssSecurityStatement`
(`ThresholdLeanXmss/Statement/Theorems.lean`). It is the bundle `Theorems`, with one field for each of
seventeen claims about the protocol of `ThresholdLeanXmss/Scheme.lean`. The theorem holds for every
committee `n = 2t - 1`, every check field `E` with `2^128` elements, every `Th`, every circuit family
and every setting. Each claim covers one protocol or one gadget alone. No claim composes the
seed generation, the ceremonies and the signing. `statement.tex` holds the deployment contract and the argument
of that composition. The module doc of `Statement/Theorems.lean` holds the full model. The module docs
of `Statement/Dkg.lean` and `Statement/Signing.lean` hold the deviations from the papers. The proofs
follow GS20 for the DKG and PRAWNS for the signing, and
they reuse leanVM `formal/lean_xmss` for the hash layer.

`signingSecurityClosed` gives `SigningSecurityStatement` (`Statement/SigningBudgets.lean`), the signing
claim with the budget of every party. That claim is no field of the bundle.

## Units and budgets

* The signing claim counts in units of `2^-128`. `signingHashError q = q / 2^127` is two units for
  each counted call.
* The other hash terms are birthday bounds over `2^256` outputs, for example
  `seedGenHashError C q = (q + seedGenSecrets C)^2 / 2^256`. `streamKeyError C` is the birthday bound
  `k^2 / 2^129` of the 128-bit AES keys of the `k` PRSS keys.
* The budget `q` of `SigningSecurityStatement` (`HasSigningQueryBound`) counts every call of `H` and
  `PRG` by every party, cache hits included.
* The budget of the signing claim of the bundle (`adversaryCost`) counts only the own calls of the
  forger to `H` and `PRG` and its round-2 requests, on every path of its program.
  `HasSigningOwnBound` is the same budget as a predicate.
* The simulation claims and `TprfSecurityStatement` count only the calls of the adversary and of the
  distinguisher (`IsQueryBounded`). No budget is a time bound.

## Model

* `H` is one lazy random oracle on `Query`. Its constructors are disjoint domains, so
  domain-separated hashing is the assumption.
* In the seed generation and ceremony claims, `Th` is one fixed function on the inputs that the MPC
  evaluates, the chain steps and the commitment `c_e`. `CircuitsCompute` states that the circuits
  compute this `Th`. In the signing claim, all of `H` is a random oracle. The difference between the
  two models is the random-oracle heuristic for Keccak.
* The seed generation and each ceremony have their own static coalition of at most `t - 1` operators and a
  rushing malicious adversary. The notion is security with selective abort (GL05), in which each
  operator aborts alone. The bundle has this claim for the seed generation. For a ceremony the claim is
  `TreeSecurityStatement`, which no theorem proves.
* The signing adversary corrupts adaptively, at most `t - 1` operators over the lifetime. A
  corruption gives only the keys, because an operator erases its ceremony state.
* Honest operators sign at most one message for each key (`breaksOneMessagePerKey`). The map `bound`
  of `tsigOracles` enforces it in the game.

## Seed generation

1. `seedGenCompleteness` (`Proof/SeedGen`) gives `SeedGenCompletenessStatement`. The honest run differs
   from `F_seedGen` only when two derived keys collide, at `derivedKeyCollision`.
2. `seedGenSecurityClosed` (`Proof/SeedGenAlias`) gives `SeedGenSecurityStatement` with
   `seedGenSimulator`. The simulator extracts the corrupt reveals from the observed calls and programs
   `H` (CDG+18). Honest commitments become fresh values until a call hits a commitment input.
   `seedGenProgramAliasBound` pays the programming collisions. The bad events fit `seedGenHashError`.

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
3. `TreeSecurityStatement`, the claim that a ceremony securely computes `F_tree`, is no field of the
   bundle. No theorem proves it.

## Signing plan

`TprfCorrectnessStatement` and `TprfSecurityStatement` (`tprfCorrectness`, `tprfSecurity` in
`Proof/Tprf`) follow PRAWNS, Theorem 5.1, with `prawns_quorum_holds_term`, `prawns_L_partition`,
`prawns_lemma52_guess` and `tprfError`. `signingCorrectness` (`Proof/Signing`) pays two searches.

`signingSecurityFull` (`Proof/HiddenCore`) gives `SigningSecurityStatement`, the claim with the budget
of every party, through
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

`SigningOwnBudget.signingOwnBudget` (`Proof/SigningOwnBudget`) gives `SigningOwnBudgetStatement`. It
runs the same two stages with the count of the forger alone. `SeedHitOwn.distinctFlagOwn` pays the
hidden keys. The charged lane is the sum of four bounds, `hitOwn_of_gate`, `altOwn`, `topOwn` and
`r1OwnSource`, and it stops at the first second opening of a commitment `c_e`. The capped lane is
`ownCapClean` with `compilerCouplingClean`. The fixed slack `signingSlack` pays the first read of
each top key and the verification.

`SigningStronglyUnforgeable.stronglyUnforgeable` (`Proof/SigningStronglyUnforgeable`) gives the field
`stronglyUnforgeable` of the bundle, `ThresholdLeanXmssStronglyUnforgeable`, from
`SigningOwnBudgetStatement`. `stronglyUnforgeable_iff` states that the two claims are equivalent. The
budget is a cost function in the one and a predicate in the other.

## Modules

The statement layer is `ThresholdLeanXmss/`. The proofs are in `ThresholdLeanXmssSecurity/Proof/`.

* `Scheme`, `Ideal`, `Reductions` and the files of `Statement/` hold the protocol and the world, the
  functionalities and the games, the simulators and the reductions, and the claims.
* `Lemmas`, `Execution` and `Coupling` hold the paper lemmas named after their source, the
  execution model and the round-by-round coupling.
* `SeedGen*` holds seed generation completeness and the seed generation simulation.
* `Gadgets`, `Check*` and `Main*` hold the gadgets, the check and the batch.
* `Tree` and `Dealer` hold the ceremony completeness, the dealer and the tree success. `TreeSim` and
  `TreeCheckKernelCoupling` hold lemmas on the runs of a ceremony that the signing proof uses.
* `Tprf`, `Signing`, `SigningSecurity`, `SigningCore`, `SeedHit` and `HiddenCore` hold the
  threshold PRF, signing correctness, the signing spine and the hidden keys.
* `SigningDescent`, `SigningCache`, `SigningSelection` and `SigningOpening` hold the leanVM descent
  and the classification of a win.
* `SigningCost`, `SigningHit*`, `SigningGuess*`, `SigningPartner*` and `SigningLinkPaid` hold the
  charged lanes.
* `SigningLaneUnion`, `SigningLaneFinal`, `SigningReleased*`, `SigningSignedSeparation`,
  `SigningLane2*`, `SigningLaneInputLogged`, `SigningLaneHybrid*` and `SigningCompiler*` hold the
  uncharged lane and its shared cap.
* `SigningOwn*`, `SeedHitOwn`, `SigningLedgerExpect` and `SigningStronglyUnforgeable` hold the signing
  claim with the budget of the forger alone.
* `VendoredExcerpt` holds eight declarations of leanVM `1acdff19` that leanVM removed later.

The library does not hold the modules of the key hop and of the simulation hop of a ceremony. -/

namespace ThresholdLeanXmssSecurity

/-- Threshold leanXMSS meets its security claim. -/
theorem thresholdLeanXmss_security : ThresholdLeanXmss.ThresholdLeanXmssSecurityStatement := by
  intro C E _ _ _ _ K prims circuits settings
  letI : SampleableType E := SampleableType.ofFintype E
  exact {
    seedGenCompleteness := seedGenCompleteness prims
    seedGenSecurity := seedGenSecurityClosed prims
    treeCompleteness := treeCompleteness prims K circuits settings
    dealerTree := dealerTreeProof prims circuits settings C
    treeSuccess := treeSuccessProof prims circuits settings C
    coin := coinSecurity prims K
    coinCompleteness := coinCompleteness prims K
    mult := multStatement prims K
    extendMult := extendMultSecurity prims K
    multVerify := multVerifyClosed prims K
    multVerifyCompleteness := multVerifyCompleteness prims K
    main := mainStatementFull prims K
    mainCompleteness := mainCompleteness prims K
    tprfCorrectness := tprfCorrectness prims C
    tprfSecurity := tprfSecurity prims C
    signingCorrectness := signingCorrectness prims C
    stronglyUnforgeable := SigningStronglyUnforgeable.stronglyUnforgeable prims C }

/-! The build fails if the axiom footprint of the end theorem changes. -/

/-- info: 'ThresholdLeanXmssSecurity.thresholdLeanXmss_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdLeanXmss_security

/-! The build fails unless each component claim below depends only on `propext`, `Classical.choice`
and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.multVerifyClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multVerifyClosed

/-- info: 'ThresholdLeanXmssSecurity.seedGenSecurityClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedGenSecurityClosed

/-- info: 'ThresholdLeanXmssSecurity.signingSecurityClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingSecurityClosed

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.signingOwnBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningOwnBudget.signingOwnBudget

/-- info: 'ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.stronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningStronglyUnforgeable.stronglyUnforgeable

/-- info: 'ThresholdLeanXmssSecurity.dealerTreeProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerTreeProof

/-- info: 'ThresholdLeanXmssSecurity.treeSuccessProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSuccessProof

/-- info: 'ThresholdLeanXmssSecurity.mainStatementFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainStatementFull

/-- info: 'ThresholdLeanXmssSecurity.seedGenCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedGenCompleteness

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
