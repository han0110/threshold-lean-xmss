import ThresholdLeanXmss.Reductions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Threshold leanXMSS security statement

The claims about the protocol of `Scheme.lean`, at the level at which GS20 and PRAWNS state them.
This file holds the world with its counted calls, the notions of secure computation, the games and
the claims.

| claim | statement | source |
| --- | --- | --- |
| `KeygenCompletenessStatement` | An honest keygen gives the keys of `F_keygen`, except when two derived keys collide. | the note, Section 2.1, honest run |
| `KeygenSecurityStatement` | The keygen securely computes `F_keygen` with selective abort, with the simulator `keygenSimulator`. | GL05 and CDG+18 |
| `TreeCompletenessStatement` | An honest ceremony gives the tree of `F_tree`. | GS20, Theorem 2, honest run |
| `TreeSecurityStatement` | Each ceremony securely computes `F_tree` with selective abort, with the simulator `treeSimulator`. | GS20, Theorem 2, and GL05 |
| `DealerTreeStatement` | When the circuits compute `Th`, the dealer of `F_tree` gives the trees of `KeyGen` of the signing claims. | PRAWNS, Section 3.1, and `doc/dkg.md` 3.1 |
| `TreeSuccessStatement` | When the circuits compute `Th`, `F_tree` gives a bottom tree `b` on the top tree of the same seeds, except with probability `(1 - p)^L`. | PRAWNS, Section 3.1, honest run |
| `CoinStatement` | `Coin` securely computes `F_coin` with selective abort in the `F_rand`-hybrid model. | GS20, Lemma 3 |
| `CoinCompletenessStatement` | An honest `Coin` gives the output of `F_coin`. | GS20, Protocol 6, honest run |
| `MultStatement` | `MulRep` and `Reshare` in each mode securely compute `F_mult` up to an additive attack, with selective abort. | GS20, Lemma 4 |
| `ExtendMultStatement` | `MulRep` or `MulSh` and `Reshare` securely compute `F_extendMult` up to an additive attack, with selective abort. | GS20, Lemma 5 |
| `MultVerifyStatement` | The check with its digests securely computes `F_multVerify` with selective abort. | GS20, Lemmas 8 to 11, and CGH+18 |
| `MultVerifyCompletenessStatement` | An honest check accepts correct tuples. | GS20, Protocol 17, honest run |
| `MainStatement` | A batch securely computes `F_main` in the `{F_mult, F_multVerify}`-hybrid model. | GS20, Theorem 2, for public outputs and pre-shared inputs |
| `MainCompletenessStatement` | An honest batch gives the outputs of `F_main`. | GS20, Protocol 19, honest run |
| `TprfCorrectnessStatement` | `Combine'` of the parts of a quorum gives `F(msk, x)`. | PRAWNS, Definition 2.1 |
| `TprfSecurityStatement` | The threshold PRF is adaptively secure. | PRAWNS, Definition 2.2 and Theorem 5.1 |
| `SigningCorrectnessStatement` | An honest quorum fails with probability at most `2 (1 - p)^L`, and its signature verifies. | PRAWNS, Section 3.1, honest run |
| `SigningSecurityStatement` | The signing is strongly unforgeable with adaptive corruption in the random-oracle model, up to `q / 2^127` and the hidden keys. | PRAWNS, Definition 3.2, in the random-oracle model |
| `LifetimeSecurityStatement` | Against a static coalition, the real keygen, the real ceremonies with retries and the signing service give a forgery only with the probability of the bound, which holds the advantage of the fixed forger `lifetimeForger`. | the composition of the claims above, with PRAWNS, Definition 3.2 |

The first 18 claims are component claims. Each claim covers one protocol or one gadget alone.
`LifetimeSecurityStatement` states the security of the real keygen, the real ceremonies and the
signing service together.

GS20 states no completeness lemma. Security with abort alone allows a protocol that always aborts,
so each completeness claim is the honest run of the protocol of its row.

## Review boundary

The simulators and the reductions run the network and the oracles of the games, and the claims name
them. So these definitions stay before `Reductions.lean` in the import chain, and a review also reads
them.

* `Scheme.lean` holds the oracles of the world (`WorldSpec`, `counted`, `free`, `localAnswer`,
  `programAnswer`), the network (`Functionality`, `Adversary`, `Simulator`, `executePhase`) and the
  honest runs.
* `Ideal.lean` holds the functionalities and the oracles of the games (`tprfOracles`, `tsigOracles`,
  `tsigGameWith`).
* `Reductions.lean` holds the simulators and the reductions. A bound with the advantage of a
  reduction is only as strong as that reduction.

## Model

* There are `n = 2t - 1` operators, synchronous rounds and private authenticated links (GS20,
  Section 3.1). In the keygen and ceremony claims, a rushing malicious adversary statically corrupts
  at most `t - 1` operators.
* The keygen and each ceremony are separate claims, each with its own static coalition. A ceremony
  takes the keys as its input, because the operators build bottom trees on demand while they sign.
  The coalition of a ceremony is the set of operators corrupted before it, and no operator is
  corrupted during a ceremony.
* The adversary gets the inputs of the corrupt operators and an auxiliary input `z`. A simulation
  claim fixes the simulator before the inputs and `z` (Canetti 2000).
* In the keygen and ceremony claims, `Th` is one fixed function on the inputs that the MPC
  evaluates, namely the chain steps and the commitment `c_e`. The leaves, the nodes, the message
  digests and every other domain of `H` are a lazy random oracle.
* In the signing claim, all of `H` is a lazy random oracle, `Th` included. The gap between the two
  models is the random-oracle heuristic for Keccak.
* The signing budget `q` counts every call of `H` and `PRG` by every party, the key generation, the
  signers, the forger and the verification included, and cache hits included
  (`HasSigningQueryBound`). The lifetime budget `Q` counts in the same way. The simulation claims
  and `TprfSecurityStatement` count only the calls of the adversary and of the distinguisher.
* `F_tree` runs the circuits of the ceremony, so the ceremony claims hold for every circuit family.
  `DealerTreeStatement` and `TreeSuccessStatement` assume that the circuits compute `Th`
  (`CircuitsCompute`), and they link `F_tree` to the trees of the signing claims.
* The claims take every value of `Constants`. Its field `encode` gives `E` exactly `2 ^ 192`
  elements (`Constants.card`), so `E` is isomorphic to `GF(2^192)`. No claim fixes the basis or
  the bit encoding of the implementation. `constants_nonempty` gives a value only for the committee
  of one operator, so it does not instantiate the implementation.
* The constructors of `Query` are disjoint domains of `H`, and a repeated query gets the same
  answer. `H` is one lazy random oracle on `Query`, except on the inputs of `Th` that the keygen
  and ceremony claims fix. This models domain-separated hashing (Bellare, Davis and Günther,
  EUROCRYPT 2020). To match it, the implementation needs injective encodings with a distinct tag
  for each domain, `hash`, the PRF and the masks included, and fields of fixed width or with a
  length prefix. The current byte encoding does not meet this requirement. Its change is a later
  implementation item.
* `PRG` is AES-128 under a hash of the key. The ceremony claim pays the multi-key PRF advantage of
  `prgReduction` against `hiddenStreams` and a birthday term for the 128-bit keys.
* The budget `q` bounds the counted calls of the adversary and of the distinguisher for every answer
  of the oracles and for every state, namely their random-oracle calls (BR93, `IsQueryBounded` with
  `IsQueryBoundP` of VCVio). The simulation claims use this budget, and in them the honest operators
  and the functionalities call `H` for free.
* Each simulation claim bounds the counted calls of the ideal run by `q` plus a fixed overhead
  (Canetti 2000, efficient simulators). An explicit simulator emulates the honest operators on the
  free copy as the real operators do, and its overhead counts only its programming queries. A
  simulator that a claim only asserts to exist has all its calls counted, and its overhead counts
  its emulation of the honest operators.
* A protocol securely computes a functionality when a distinguisher with oracle access tells its real
  execution from the ideal execution with a simulator at most with the error of the claim. The
  distinguisher reads the joint output of the adversary and the honest operators.
* With selective abort, the adversary names the honest operators that receive each output (GL05).
* The gadget claims are in the `F_rand`-hybrid model. The PRSS outputs of one round realize `F_rand`
  (CDI05). The keygen and ceremony claims run the real network with the real PRSS.
* The explicit simulators program `H` as the local programmable random oracle of CDG+18, which has
  no `IsProgrammed` query.
* The signing adversary corrupts adaptively, and a corruption gives only the keys of an operator.
  After a ceremony, an operator erases its ceremony state.
* At most `t - 1` operators are corrupt over the lifetime of the key.
* Honest operators sign at most one message at each key over all quorums
  (`breaksOneMessagePerKey`). The signing game enforces it, the PoC does not, and production must.
* The keygen and ceremony claims cover their static coalitions, and the signing claim covers
  adaptive corruptions. `LifetimeSecurityStatement` states their composition for one static
  coalition of at most `t - 1` operators that is corrupt from the start. It is weaker than an
  adaptive lifetime claim, which these claims do not give.
* In the lifetime claim, the keygen runs once. If an honest operator has no keys, the lifetime
  ends. The adversary gets the public parameter after the keygen. It gets the public key and the
  top tree of the first honest operator `h` once `h` holds its top tree. If an honest operator has
  no top tree at the end, the adversary loses.
* The adversary runs one ceremony at a time and chooses each tree and the start of each run. Each
  tree has at most `attempts` runs. A retry runs on the same keys with a fresh PRSS setup. A bottom
  ceremony runs only when every honest operator has the top tree. It does not run after the first
  signing request on its tree.
* Signing requests can come between the rounds of a ceremony. A request on the tree of the running
  ceremony is refused. An honest operator answers a signing request on a bottom tree, round 1
  included, only when it holds its own ceremony output of that tree. It signs at most one message
  for each key (`breaksOneMessagePerKey`).
* The lifetime claim takes the fixed `Th` of `prims` on the inputs that the MPC evaluates, and the
  fixed `circuits` compute it (`CircuitsCompute`), as in the ceremony claims.
* The budget `Q` counts every call of `H` and `PRG` by every party, as in the signing claim. It
  holds on every path of the lifetime game, for every answer of the oracles, and not only on the
  runs of the real lifetime. Unlike `IsQueryBounded`, it does not bound an adversary state that no
  answer reaches.
* In the lifetime bound, the keygen term takes `(setupRounds + 2) Q`. Each ceremony run takes
  `(fuel + 2) Q` for its own rounds and `Q + lifetimeOverhead` for the cache of the phases before
  it. The last term is the advantage of `lifetimeForger` in the signing game, in the world of the
  lifetime claim. It has no budget, and `SigningSecurityStatement` does not bound it.
* The use of the lifetime claim for Keccak is the random-oracle heuristic for `Th`. The heuristic is
  not a term of the bound.

## Deviations from the papers

* Replicated sharing replaces Shamir sharing (CDI05). A corrupt operator that fills a term can give
  each honest holder its own copy. So `F_mult` sums the shares of the honest operators from their
  own views and takes a copy offset, and `F_multVerify` checks the copies (KPPS23, `Π_agree`, and
  CGH+18, Protocol 3.3).
* `F_mult` and `F_multVerify` leak the view of each honest operator of the terms that the corrupt
  operators know. GS20 leaks one copy of these terms in Functionalities 7 and 16. In a run of
  circuits, a corrupt filler chooses each split copy, so the adversary already knows the leaked
  copies. On other inputs of the gadget claims, the leak is larger than in GS20.
* `F_main` also leaks these views. Its inputs agree at every holder, the corrupt holders included,
  as the keygen echo makes them, so it leaks only what GS20, Functionality 18, leaks.
* Each operator aborts alone, so every functionality except `F_rand` has selective abort, `F_mult`
  and `F_extendMult` included. GS20 aborts all honest operators together.
* `F_rand` has no abort, because the PRSS of CDI05 that realizes it sends no message.
* The de-linearization weighs tuple `k` by a product of `d` coins in place of the powers of one coin
  of GS20, Protocol 13. The multilinear weights follow the prototype (`crates/rss/src/verify.rs`).
* Bit `q` of a word of tuples has the public weight `x^q` in place of a coin (`src/check.rs`), so the
  six bit coins of the tensor are fixed to `x, x^2, ..., x^32`. This is the partially deterministic
  challenge of Dao and Thaler 2024 (Claim 1), with the geometric weights of Flock (Bünz, Rothblum and
  Wang 2026, Section 4.3). The errors are bits and `1, x, ..., x^63` are linearly independent over
  `F_2`, so a wrong word stays a nonzero weight, and the Schwartz-Zippel count of Lemma 8 holds. The
  model takes every family of weights that is linearly independent over `F_2` (`Constants.weight`).
* The first seven halving steps fold the slices with the coin kept out of `x` (Gruen 2024) and the
  small-value table of BDDT25. Each step is still a degree-2 claim in its challenge.
* GS20 assumes exactly `(n - 1) / 2` corrupt parties, which is `t - 1` here (GS20, Theorem 1, writes
  `n = 2t + 1`). `treeSimulator` handles every coalition size, because it shifts one lacked term at
  the opening.
* The `Eval'` of PRAWNS, Section 5.1, adds two masks under `k_ij` and `k_ji`. The note adds one mask
  under the common key `K_ij`, and the masks still cancel in pairs.
* The signing game takes the quorum, and `c_e` fixes the randomizer value (`doc/sign.md`, Section
  4). `OSign` has two rounds.
* PRAWNS lets the adversary choose `n` and `t`. Here the committee is a parameter of each claim.
* The model splits each run into batches of `batchSize` jobs. The implementation sizes chain batches
  and commitment batches apart, and it puts the top randomizer value in the last commitment batch.

Each bound is a fixed expression, namely the exact error of the checks, `q / 2 ^ bits` terms, and the
advantage of a reduction that `Reductions.lean` defines.
-/

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

/-! ## The world -/

section World

variable {C : Committee} (prims : Primitives)

/-- The world. Both copies share one cache. Each call of a random-oracle domain of `H`, each call of
`PRG` and each programming query on the counted copy costs one query. The fixed part of `Th` costs
nothing. -/
def world : QueryImpl (WorldSpec C) (AddWriterT ℕ (StateT (HashCache C) ProbComp)) :=
  QueryImpl.withAddCost (localAnswer (C := C) prims + programAnswer (C := C) + localAnswer (C := C) prims :
      QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp))
    fun | .inl (.inl (.inl _)) => 0 | .inl (.inl (.inr (.inl (.hash input)))) => if MpcInput input then 0 else 1
        | .inl _ => 1 | .inr _ => 0

/-- Run a computation in the world from an empty cache, with its number of counted queries. -/
def runWorld {α : Type} (oa : OracleComp (WorldSpec C) α) : ProbComp (α × ℕ) :=
  (simulateQ (world prims) oa).run.run' ∅

/-- Every execution makes at most `q` counted queries. In an ideal run these are the calls of the
simulator, which runs the adversary, its programming queries, and the calls of the distinguisher. -/
def HasHashQueryBound {α : Type} (run : ProbComp (α × ℕ)) (q : ℕ) : Prop :=
  ∀ r ∈ support run, r.2 ≤ q

/-- The probability that a computation outputs `true`. -/
def accepts (oa : OracleComp (WorldSpec C) Bool) : ℝ := (Pr[fun r => r.1 = true | runWorld prims oa]).toReal

/-- The world of the signing claim. All of `H` is a lazy random oracle. Each call of `H` and of `PRG`
costs one query, on both copies, so the calls of every party count. Private sampling costs nothing. -/
def signingWorld : QueryImpl (WorldSpec C) (AddWriterT ℕ (StateT (HashCache C) ProbComp)) :=
  QueryImpl.withAddCost (signingLocalAnswer (C := C) prims + programAnswer (C := C) + signingLocalAnswer (C := C) prims :
      QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp))
    fun | .inl (.inl (.inl _)) => 0 | .inr (.inl _) => 0 | _ => 1

/-- Run a computation in the signing world from an empty cache, with its number of calls of `H` and
`PRG`. -/
def runSigningWorld {α : Type} (oa : OracleComp (WorldSpec C) α) : ProbComp (α × ℕ) :=
  (simulateQ (signingWorld prims) oa).run.run' ∅

/-- Every execution makes at most `q` calls of `H` and `PRG`, by every party, cache hits included.
The key generation, the signers, the forger and the verification all
count. The signing oracles build each bottom tree once, at the first request that needs it, and
that build counts. When at least `t` operators can sign the forged message, the win test builds its
tree again, and that build counts too. -/
def HasSigningQueryBound {α : Type} (oa : OracleComp (WorldSpec C) α) (q : ℕ) : Prop :=
  ∀ r ∈ support (runSigningWorld prims oa), r.2 ≤ q

/-- The probability that a computation outputs `true` in the signing world. -/
def signingAccepts (oa : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr[fun r => r.1 = true | runSigningWorld prims oa]).toReal

/-- The calls that the lifetime counts, namely each call of `H` and of `PRG` and each programming
query, on both copies. Private sampling is free. -/
def LifetimeCounted : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inl _)) => False
  | .inr (.inl _) => False
  | _ => True

/-- The world of the lifetime claim. `H` answers the inputs that the MPC evaluates with `Th`, and
every other input as a lazy random oracle. Each call in `LifetimeCounted` costs one query, so the
calls of every party count, as in `signingWorld`. -/
def lifetimeWorld : QueryImpl (WorldSpec C) (AddWriterT ℕ (StateT (HashCache C) ProbComp)) :=
  QueryImpl.withAddCost (localAnswer (C := C) prims + programAnswer (C := C) + localAnswer (C := C) prims :
      QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp))
    fun t => if LifetimeCounted t then 1 else 0

/-- Run a game in the lifetime world from an empty cache, with its number of calls of `H` and
`PRG`. `Th` is the fixed function of `prims`. -/
def lifetimeRun (game : OracleComp (WorldSpec C) Bool) : ProbComp (Bool × ℕ) :=
  (simulateQ (lifetimeWorld prims) game).run.run' ∅

end World

/-! ## Secure computation -/

section SecureComputation

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The calls of a local computation that the budget counts, namely the random-oracle inputs of `H`
and `PRG`. -/
def Counted : (LocalSpec C).Domain → Prop
  | .inr (.inl (.hash input)) => ¬ MpcInput input
  | .inr _ => True
  | .inl _ => False

/-- A distinguisher reads the joint output of the adversary and the honest operators, with oracle
access (GL05 and Canetti 2000). -/
abbrev Distinguisher (C : Committee) (σ O : Type) := σ × (C.Party → Option O) → OracleComp (LocalSpec C) Bool

/-- A `q`-query adversary with its distinguisher, in the sense of BR93. For every answer of the
oracles, the start makes at most `start` counted calls, each round and each reply at most `step`, and
the distinguisher at most `final`, and a run of `fuel` steps stays within `q`. A step runs one round
or one functionality, and each functionality of the model leaks once. -/
def IsQueryBounded {I L R O : Type} (A : Adversary C E I L R) (Z : Distinguisher C A.State O) (fuel q : ℕ) : Prop :=
  ∃ start step final : ℕ, start + fuel * step + final ≤ q ∧
    (∀ x z, IsQueryBoundP (A.start x z) Counted start) ∧
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) ∧
    (∀ state l, IsQueryBoundP (A.answer state l) Counted step) ∧
    (∀ r, IsQueryBoundP (Z r) Counted final)

/-- The real execution of a protocol in the hybrid model of `Fh`, on the inputs `x` and the auxiliary
input `z`. -/
def realExecution {I O Ih Oh Lh Rh : Type} (D : C.Coalition) (A : Adversary C E I Lh Rh)
    (Fh : Functionality C Ih Oh Lh Rh) (fuel : ℕ) (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (x : C.Party → I) (z : Aux) : OracleComp (WorldSpec C) (A.State × (C.Party → Option O)) := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  executePhase worldRoles D A Fh fuel state fun i => program i (x i)

/-- The ideal execution of `F` with the simulator `Sim`. The functionality runs on the free copy. -/
def idealExecution {κ : Type} {S : OracleSpec κ} {I O L R σ : Type}
    (lift : ∀ {β : Type}, OracleComp S β → OracleComp (WorldSpec C) β) (D : C.Coalition)
    (F : Functionality C I O L R) (Sim : Simulator (C := C) S I L R σ) (x : C.Party → I) (z : Aux) :
    OracleComp (WorldSpec C) (σ × (C.Party → Option O)) := do
  let state ← lift (Sim.start (corruptInputs D x) z)
  let impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT Sim.State (OracleComp (WorldSpec C))) :=
    (fun (t : (LocalSpec C).Domain) =>
      (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) : StateT Sim.State _ _)) +
    (fun (l : L) => (StateT.mk fun st => do
      let (st, r) ← lift (Sim.answer st l)
      pure (r, st) : StateT Sim.State (OracleComp (WorldSpec C)) R))
  let (outputs, state) ← (simulateQ impl (F.run D fun i => if i ∈ D.1 then none else some (x i))).run state
  pure (← lift (Sim.output state), outputs)

/-- An execution followed by the distinguisher on the counted copy. -/
def distinguish {σ O : Type} (oa : OracleComp (WorldSpec C) (σ × (C.Party → Option O)))
    (Z : Distinguisher C σ O) : OracleComp (WorldSpec C) Bool :=
  oa >>= fun r => worldRoles.adversary (Z r)

/-- The protocol `program` in the `Fh`-hybrid model securely computes `F` on the valid inputs
(Canetti 2000, GS20). For each coalition and adversary there is a simulator without programming, and
all its calls are counted. It is fixed before the inputs, the auxiliary input, the distinguisher and
the budget, and it sees only the corrupt inputs, the auxiliary input and the leaks of `F`. For a
`q`-query adversary and distinguisher, the ideal run makes at most `q + overhead` counted queries,
and the error is `ε q`. -/
def SecurelyComputes {I O L R Ih Oh Lh Rh : Type} (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (fuel : ℕ) (Fh : Functionality C Ih Oh Lh Rh) (F : Functionality C I O L R)
    (valid : C.Coalition → (C.Party → I) → Prop) (overhead : ℕ) (ε : ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E I Lh Rh), ∃ S : Simulator (C := C) (LocalSpec C) I L R A.State,
    ∀ (x : C.Party → I) (z : Aux) (Z : Distinguisher C A.State O) (q : ℕ), valid D x →
      IsQueryBounded A Z fuel q →
      HasHashQueryBound (runWorld prims (distinguish (idealExecution worldRoles.adversary D F S x z) Z))
          (q + overhead) ∧
        |accepts prims (distinguish (realExecution D A Fh fuel program x z) Z) -
          accepts prims (distinguish (idealExecution worldRoles.adversary D F S x z) Z)| ≤ ε q

/-- The protocol `program` on the real network securely computes `F` on the valid inputs with the
explicit simulator `Sim D A`. It is fixed code that runs the adversary on the counted copy, emulates
the honest operators on the free copy as the real operators do, and may program `H`. For a `q`-query adversary and distinguisher, the
ideal run makes at most `q + overhead` counted queries, and the error is `ε D A x z Z q`. -/
def SimulatedBy {I O L R : Type} (program : C.Party → I → PartyM C E RealSpec O) (fuel : ℕ)
    (F : Functionality C I O L R) (valid : C.Coalition → (C.Party → I) → Prop)
    (Sim : (D : C.Coalition) → (A : Adversary C E I PEmpty PEmpty) → Simulator (C := C) (WorldSpec C) I L R A.State)
    (overhead : ℕ)
    (ε : (D : C.Coalition) → (A : Adversary C E I PEmpty PEmpty) → (C.Party → I) → Aux →
      Distinguisher C A.State O → ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (x : C.Party → I) (z : Aux)
    (Z : Distinguisher C A.State O) (q : ℕ), valid D x →
    IsQueryBounded A Z fuel q →
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D F (Sim D A) x z) Z))
        (q + overhead) ∧
      |accepts prims (distinguish (realExecution D A noFunctionality fuel program x z) Z) -
        accepts prims (distinguish (idealExecution (fun oa => oa) D F (Sim D A) x z) Z)| ≤ ε D A x z Z q

def noCoalition : C.Coalition := ⟨∅, by simp⟩

/-- The adversary of an honest run. It controls no operator and replies `reply` to each leak. -/
def honestAdversary {I L R : Type} (reply : L → R) : Adversary C E I L R :=
  ⟨Unit, fun _ _ => pure (), fun _ _ => pure ((), fun _ _ => none), fun _ l => pure ((), reply l)⟩

/-- The simulator of an honest run, which replies `reply` to each leak. -/
def honestSimulator {κ : Type} {S : OracleSpec κ} {I L R : Type} (reply : L → R) :
    Simulator (C := C) S I L R Unit :=
  ⟨Unit, fun _ _ => pure (), fun _ l => pure ((), reply l), fun _ => pure ()⟩

/-- An honest run of `program` in the `Fh`-hybrid model gives the outputs of `F` on the valid inputs,
up to `ε` in statistical distance. Each functionality gets the reply of an honest adversary. -/
def Completes {I O L R Ih Oh Lh Rh : Type} (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (fuel : ℕ) (Fh : Functionality C Ih Oh Lh Rh) (replyH : Lh → Rh) (F : Functionality C I O L R)
    (reply : L → R) (valid : C.Coalition → (C.Party → I) → Prop) (ε : ℝ) : Prop :=
  ∀ x : C.Party → I, valid noCoalition x →
    tvDist ((fun r => r.1.2) <$> runWorld prims
        (realExecution noCoalition (honestAdversary replyH) Fh fuel program x []))
      ((fun r => r.1.2) <$> runWorld prims
        (idealExecution (fun oa => oa) noCoalition F (honestSimulator reply) x [])) ≤ ε

end SecureComputation

/-! ## The games -/

section Games

variable {C : Committee} (prims : Primitives)

/-- The game `G^tprf` of PRAWNS, Figure 1, with `KeyGen'` of PRAWNS, Section 5.1. -/
def tprfGame (A : TprfAdversary C) (b : Bool) : OracleComp (WorldSpec C) Bool := do
  let (_, seeds, keys) ← free (liftComp (prawnsKeyGen (C := C)) _)
  let forward : QueryImpl (LocalSpec C) (StateT (TprfState C) (OracleComp (WorldSpec C))) :=
    fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  (simulateQ (forward + tprfOracles keys seeds b) A : StateT (TprfState C) (OracleComp (WorldSpec C)) Bool).run'
    ⟨∅, fun _ _ => ∅, ∅, fun _ => none⟩

/-- `Adv^tprf`, PRAWNS, Definition 2.2. -/
def tprfAdvantage (A : TprfAdversary C) : ℝ :=
  |accepts prims (tprfGame A false) - accepts prims (tprfGame A true)|

/-- The game `G^tsig` of PRAWNS, Figure 3. -/
def tsigGame (A : TsigAdversary C) : OracleComp (WorldSpec C) Bool := do
  let some dealt ← dealerKeyGen | pure false
  (·.1) <$> tsigGameWith worldRoles dealt A

/-- `Adv^tsig`, PRAWNS, Definition 3.2, in the signing world. -/
def tsigAdvantage (A : TsigAdversary C) : ℝ := signingAccepts prims (tsigGame A)

end Games

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-! ## Error terms -/

/-- The terms `C(n, t - 1)` of a committee. -/
def termCount (C : Committee) : ℕ := C.n.choose (C.t - 1)

/-- The hashes of two values of each term at each operator, namely the history and the digest of the
check, or the two copy hashes of `OpenRep`. -/
def termHashes (C : Committee) : ℕ := 2 * C.n * termCount C

/-- The checked batches of a ceremony, of the top tree or of the two runs of a bottom tree. -/
def treeBatches : Tree → ℕ
  | .top => (chunks settings.batchSize topJobs).length
  | .bottom b => (chunks settings.batchSize (bottomJobs b)).length +
      (chunks settings.batchSize (signJobs b fun _ => digit 0)).length

/-- The soundness error of one check with `d` coins and `R` halving steps, `(d + 2 (R + 1)) / (|E| - 2)`
(GS20, Lemmas 8 to 10). It adds `q / |E|` for each of the `R + 2` coins, for a counted call that hits
the key input of a coin before the coin opens. -/
def checkErrorOf (d R q : ℕ) : ℝ :=
  (d + 2 * (R + 1) : ℕ) / (Fintype.card E - 2 : ℝ) + ((R + 2) * q : ℕ) / (Fintype.card E : ℝ)

/-- The soundness error of the checks of all batches of a ceremony. -/
def treeCheckError (tree : Tree) (q : ℕ) : ℝ :=
  treeBatches settings tree * checkErrorOf (E := E) (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
    (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q

/-- The probability that the coins of an honest check with `R` halving steps fail. A slice coin is
`0`, or one of the `R + 1` challenges finds no value outside `{0, 1}` within `challengeTries` values. -/
def coinFailure (R : ℕ) : ℝ :=
  (sliceBits : ℝ) / Fintype.card E + (R + 1 : ℕ) * (2 / Fintype.card E : ℝ) ^ challengeTries

/-- The probability that two of `k` coin keys collide, which `k² / 2` pairs bound. -/
def coinKeyCollision (k : ℕ) : ℝ := (k ^ 2 : ℕ) / 2 ^ 257

/-- The probability that an honest check with `R` halving steps aborts, on its coins or on a collision
of its `R + 2` coin keys. -/
def abortErrorOf (R : ℕ) : ℝ := coinFailure (E := E) R + coinKeyCollision (R + 2)

/-- The probability that an honest check of some batch of a ceremony aborts. Two of the `B (R + 2)`
coin keys of all `B` batches can collide, because a later check reads the cached coins of an earlier
batch. -/
def treeAbortError (tree : Tree) : ℝ :=
  let batches := treeBatches settings tree
  let halvingCount := maxBatch circuits settings fun jobs => halvings (tupleCount jobs)
  batches * coinFailure (E := E) halvingCount + coinKeyCollision (batches * (halvingCount + 2))

/-- The honest points of `H` in the keygen that a counted call must not hit, namely the parts of each
operator, the derived keys, and the inputs of the hashes of the shared seeds. -/
def keygenSecrets (C : Committee) : ℕ :=
  C.n * (1 + termCount C + C.n) + 1 + termCount C + C.n.choose 2 + C.n ^ 2

/-- The birthday bound of the counted calls and the honest points of the keygen. It covers a guessed
secret, a collision of two secrets, a failed programming and a failed extraction. -/
def keygenHashError (C : Committee) (q : ℕ) : ℝ := ((q + keygenSecrets C) ^ 2 : ℕ) / 2 ^ 256

/-- The programming queries of `keygenSimulator`, one for `P`, at most one for each term and one for
each pair of a corrupt and an honest operator. -/
def keygenOverhead (C : Committee) : ℕ := 1 + termCount C + C.n ^ 2

/-- The honest points of `H` in a ceremony that a counted call must not hit. The PRSS setup has the
parts of each operator, the derived keys and the inputs of the hashes of the shared keys. Each PRSS
key has a stream-key input. Each batch has the history, the digest and the copy hash of each term,
the copies that a corrupt owner sends to each honest operator, which it hashes for free, and the
`R + 2` coin keys of its check. -/
def treeSecrets (C : Committee) (tree : Tree) : ℕ :=
  let terms := termCount C
  let pairs := C.n.choose 2
  C.n * (terms + C.n) + terms + pairs + C.n ^ 2 + (terms + pairs) +
    treeBatches settings tree * (3 * terms + C.n * terms +
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2)

/-- The birthday bound of the counted calls and the honest points of a ceremony. -/
def treeHashError (C : Committee) (tree : Tree) (q : ℕ) : ℝ :=
  ((q + treeSecrets circuits settings C tree) ^ 2 : ℕ) / 2 ^ 256

/-- The birthday bound `k² / 2^129` of the 128-bit AES keys of the `k` PRSS keys of a ceremony
(`doc/dkg.md` 3.3). -/
def streamKeyError (C : Committee) : ℝ := ((termCount C + C.n.choose 2) ^ 2 : ℕ) / 2 ^ 129

/-- The error of Theorem 5.1 with `F(k, x) = H16(k ‖ x)` in the random-oracle model, for `q`
counted calls. PRAWNS bounds it by `2 C(n, t - 1) ε_F`, which gives `2 C(n, t - 1) q / 2^256`. The
masks add `n² q / 2^256` for the guess of a hidden pair key. Honest calls are free, so two of the
`C(n, t - 1) + n²` keys may also collide. -/
def tprfError (C : Committee) (q : ℕ) : ℝ :=
  ((2 * C.n.choose (C.t - 1) + C.n ^ 2) * q + (C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 : ℕ) / 2 ^ 256

/-- The bound `q / 2^127` for `q` calls. Each call costs two units of `2^-128`. One unit
pays a call whose output hits an honest output at its tweak. The other pays a call that meets a
hidden honest input, namely a chain value below an opened position or `ρ_e` before round 1, or the
output of a digest that a later search selects. -/
def signingHashError (q : ℕ) : ℝ := q / 2 ^ 127

/-- The probability that one of `q` calls hits the input of a hidden key, namely a term seed or a
pair key, of the `C(n, t - 1) + n²` keys. Each call names one key, which is uniform on 256 bits. -/
def seedHitError (C : Committee) (q : ℕ) : ℝ :=
  ((C.n.choose (C.t - 1) + C.n ^ 2) * q : ℕ) / 2 ^ 256

/-- The probability that two of the `C(n, t - 1) + n²` keys are equal. Equal term seeds cancel in
`F`, and a hidden key equal to a corrupt key is known. -/
def seedCollisionError (C : Committee) : ℝ :=
  ((C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 : ℕ) / 2 ^ 256

/-- The probability that two derived keys of one kind have the same parts. A derivation hashes only
the tag of its kind and the parts (`src/mpc.rs`), so two terms or two pairs share a key only when an
honest part repeats. -/
def derivedKeyCollision (C : Committee) : ℝ :=
  (termCount C ^ 2 + C.n.choose 2 ^ 2 : ℕ) / 2 ^ 256

/-- The calls of an emulation of the honest operators in a check of `count` tuples. Each operator
hashes `R + 2` coin keys, `d` expanded coins, at most `challengeTries` expanded values for each of
the `R + 1` challenges, and the history and the digest of each term. -/
def checkOverhead (C : Committee) (count : ℕ) : ℕ :=
  C.n * (halvings count + 2 + coins count + (halvings count + 1) * challengeTries + 2 * termCount C)

/-- The birthday bound of the counted calls and the honest points of a check of `count` tuples,
namely the history and the digest of each term at each operator and the `R + 2` coin keys. -/
def checkHashError (C : Committee) (count q : ℕ) : ℝ :=
  ((q + termHashes C + halvings count + 2) ^ 2 : ℕ) / 2 ^ 256

/-- The birthday bound of the counted calls and the copy hashes of `OpenRep` of the honest
operators. -/
def copyHashError (C : Committee) (q : ℕ) : ℝ := ((q + termHashes C) ^ 2 : ℕ) / 2 ^ 256

/-- The probability `p` that one trial of a randomizer search finds a codeword, since a message
digest is a uniform 128-bit value. -/
def codewordProbability : ℝ :=
  ((Finset.univ.filter fun x : Encoding => Codeword.sum x = targetSum).card : ℝ) / 2 ^ digestBits

/-- The probability `(1 - p)^L` that a randomizer search of `L` trials fails. -/
def searchFailure : ℝ := (1 - codewordProbability) ^ randomizerAttemptLimit

/-- An upper bound on the calls of `H` that `referenceTree` makes for one tree, with `termCount C`
calls for each PRF value. The terms pay the chain rows, the commitments, the Merkle tree, at most `L`
randomizer trials, the top signature and its check. -/
def bottomTreeCalls (C : Committee) : ℕ :=
  let terms := termCount C
  2 ^ layerHeight * numChains * (3 * terms + 6) + 2 ^ layerHeight * (terms + 1) + numChains * (terms + 6) +
    terms + 2 ^ (layerHeight + 2) + randomizerAttemptLimit

/-- The ceremony runs of a lifetime, at most `attempts` for the top tree and for each bottom tree. -/
def lifetimeRuns (attempts : ℕ) : ℕ := attempts * (2 ^ layerHeight + 1)

/-- The calls that a reduction adds to the `Q` calls of a lifetime. A reduction pays at most
`bottomTreeCalls` for each tree that it computes in the clear.

* The signing oracles build a bottom tree once. The oracle requests of the lifetime reduction build
  only trees with a ceremony run. Each such tree costs at least one call of `Q`, so at most
  `min Q (2^h)` trees are built.
* `lifetimeRuns` pays one tree for each run. The signing reduction takes the trees of `F_tree` from
  the signing game and pays the top tree of `KeyGen` from this term. A ceremony hop pays its runs of
  `F_tree` from it. With no run, no top tree exists and the adversary cannot win.
* At each of the `n` operators, the emulated `treeSimulator` of each run evaluates the openings.
* `keygenSimulator` programs `H`. -/
def lifetimeOverhead (C : Committee) (attempts Q : ℕ) : ℕ :=
  (min Q (2 ^ layerHeight) + lifetimeRuns attempts) * bottomTreeCalls C +
    lifetimeRuns attempts * C.n * bottomTreeCalls C + keygenOverhead C

/-- The circuits compute the jobs of leanXMSS, namely chain steps and the commitment, with the fixed
function `Th`, on every job with the number of points that its kind takes. -/
def CircuitsCompute (Th : HashInput → HashOutput) : Prop :=
  ∀ (parameter : PublicParameter) (job : Job) (F : Point → Digest), job.points.length = job.kind.arity →
    (circuits parameter job.kind).eval ((job.points.map F).flatMap bitsOfDigest) =
      referenceJob (m := Id) (fun oa => evalTh Th oa) F parameter job

/-! ## Valid inputs -/

/-- The keys of all operators come from one dealing of a parameter, seeds and pair keys. -/
def DealtInputs (_D : C.Coalition) (x : C.Party → Keys C) : Prop :=
  ∃ parameter seeds pairKeys, ∀ i, x i = dealtKeys parameter seeds pairKeys i

/-- The honest Shamir shares of each `shamir` entry lie on one polynomial of degree at most `t - 1`,
and the honest operators agree on the kind and the length of each entry. -/
def ShamirInputs (D : C.Coalition) (x : C.Party → List (Product C E)) : Prop :=
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (x i).map Product.shape = (x j).map Product.shape) ∧
  ∀ g k : ℕ, ∃ V W : Polynomial E, V.natDegree ≤ C.t - 1 ∧ W.natDegree ≤ C.t - 1 ∧ ∀ i, i ∉ D.1 →
    ∀ a b count, (x i)[g]? = some (.shamir a b count) → a k = V.eval (K.point i) ∧ b k = W.eval (K.point i)

/-- The honest views of the tuples have the lengths `counts` and one mode for each tuple. For each
term, if its honest holders agree on the values of it that a corrupt operator fills, then they agree
on all its copies. So a term with no corrupt holder always agrees, and a term with a split copy has
a split value that a corrupt operator filled. -/
def TupleInputs (counts : List ℕ) (D : C.Coalition) (x : C.Party → List (Tuple C)) : Prop :=
  (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) ∧
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (x i).map (·.mode) = (x j).map (·.mode)) ∧
  ∀ T, ConsistentAt D (fun i T => (x i).map fun τ => vector τ.count fun g =>
      if ∃ j ∈ D.1, filler K τ.mode T g = some j then τ.z T g else 0) T →
    ConsistentAt D (fun i T => (x i).map fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T),
      vector τ.count (τ.z T))) T

/-- Every tuple is a product, with each term from its first holder. -/
def CorrectTuples (x : C.Party → List (Tuple C)) : Prop :=
  ∀ k < (firstInput fun i => some (x i)).length,
    let τ := tupleAt (fun i => some (x i)) k
    ∀ g < τ.count, shareValue τ.z g = shareValue τ.x g * shareValue τ.y g

/-- The inputs of a batch have one sharing for each job. The terms of a job have one width at each
honest holder and are empty elsewhere. Every holder of each term agrees on it, the corrupt holders
included, as the inputs of a ceremony come from the seeds that the keygen echo compares. -/
def MainInputs (jobs : List Circuit) (D : C.Coalition) (x : C.Party → List (C.Term → List Bit)) : Prop :=
  ∃ widths : List ℕ, widths.length = jobs.length ∧
    (∀ i, i ∉ D.1 → (x i).length = jobs.length ∧ ∀ k < jobs.length, ∀ T,
      ((((x i)[k]?).getD fun _ => []) T).length = if i ∈ C.holders T then widths.getD k 0 else 0) ∧
    ∀ k : ℕ, Consistent noCoalition fun i T => (((x i)[k]?).getD fun _ => []) T

/-! ## The claims -/

/-- An honest keygen gives the keys of `F_keygen`, except when two derived keys collide. -/
def KeygenCompletenessStatement (C : Committee) (E : Type) : Prop :=
  Completes prims (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) setupRounds noFunctionality
    (fun l => l.elim) Fkeygen (fun _ => Finset.univ) (fun _ _ => True) (derivedKeyCollision C)

/-- The keygen securely computes `F_keygen` with selective abort against a static coalition, with the
simulator `keygenSimulator` (GL05 and CDG+18). -/
def KeygenSecurityStatement (C : Committee) (E : Type) : Prop :=
  SimulatedBy prims (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) setupRounds Fkeygen
    (fun _ _ => True) keygenSimulator (keygenOverhead C) fun _ _ _ _ _ q => keygenHashError C q

/-- An honest ceremony gives the tree of `F_tree`, except when an honest check aborts. -/
def TreeCompletenessStatement : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree),
    Completes prims (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
      (ceremonyFuel circuits settings) noFunctionality (fun l => l.elim) (Ftree circuits settings top tree)
      (fun _ => Finset.univ) DealtInputs (treeAbortError (E := E) circuits settings tree)

/-- Each ceremony securely computes `F_tree` with selective abort against its own static coalition,
with the simulator `treeSimulator` (GS20, Theorem 2, and GL05). The bound adds the multi-key PRF
advantage of `prgReduction` against `hiddenStreams` on the real run, because `treeSimulator` already
uses ideal streams. -/
def TreeSecurityStatement : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree),
    SimulatedBy prims (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
      (ceremonyFuel circuits settings) (Ftree circuits settings top tree) DealtInputs
      (treeSimulator K circuits settings top tree) 0 fun D A x z Z q =>
        treeCheckError (E := E) circuits settings tree q + treeHashError circuits settings C tree q + streamKeyError C +
          PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D
            (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
              (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput)) x z) Z))

/-- When the circuits compute `Th`, the dealer of `F_tree` gives the trees of `KeyGen` of the signing
claims, namely `referenceTree` with the PRF values of the seeds. The two runs have the same
distribution of the tree and of the next cache of `H`, from every cache. -/
def DealerTreeStatement (C : Committee) : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
      (cache : HashCache C),
      evalDist ((simulateQ (localAnswer prims)
          (liftComp (Prod.fst <$> dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run cache) =
        evalDist ((simulateQ (localAnswer prims)
          (liftComp (referenceTree (fun oa => tweakable oa) (prfValue seeds) parameter top tree) (LocalSpec C))).run cache)

/-- When the circuits compute `Th`, the dealer of `F_tree` gives the top tree, and then a bottom
tree `b` on that top tree, except with probability `(1 - p)^L` for the randomizer search of its top
signature. `TreeCompletenessStatement` bounds the distance of an honest ceremony to `F_tree`, so this
claim bounds the abort of `F_tree` itself. -/
def TreeSuccessStatement (C : Committee) : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)),
      (Pr[fun r => r.1 = none | runWorld prims (free (C := C) (liftComp (do
        let (output, _) ← dealerCeremony circuits settings parameter seeds emptyTop .top
        let some top := TreeOutput.topTree output | pure none
        Prod.fst <$> dealerCeremony circuits settings parameter seeds top (.bottom b)) _))]).toReal ≤ searchFailure

/-- `Coin` securely computes `F_coin` with selective abort in the `F_rand`-hybrid model, perfectly
(GS20, Lemma 3). The simulator makes no oracle call of its own. -/
def CoinStatement [SampleableType E] : Prop :=
  SecurelyComputes prims (coinProtocol K) coinRounds (Frand E) Fcoin SameCount 0 fun _ => 0

/-- An honest `Coin` gives the output of `F_coin`. -/
def CoinCompletenessStatement [SampleableType E] : Prop :=
  Completes prims (coinProtocol K) coinRounds (Frand E) (randReply E) Fcoin (fun _ => Finset.univ) SameCount 0

/-- `MulRep` and `Reshare` in each mode securely compute `F_mult` up to an additive attack in the
`F_rand`-hybrid model, perfectly (GS20, Lemma 4). The simulator makes no oracle call of its own. -/
def MultStatement : Prop :=
  ∀ mode : ReshareMode,
    SecurelyComputes prims (multProtocol K mode) (multRounds mode) (Frand Bit) (FmultBit K mode)
      (fun D x => SameCount D fun i => (x i).2.2) 0 fun _ => 0

/-- `MulRep` or `MulSh` and `Reshare` securely compute `F_extendMult` up to an additive attack in the
`F_rand`-hybrid model, perfectly (GS20, Lemma 5). The simulator makes no oracle call of its own. -/
def ExtendMultStatement [SampleableType E] : Prop :=
  SecurelyComputes prims (extendMultProtocol K) extendMultRounds (Frand E) (FextendMult K) (ShamirInputs K) 0 fun _ => 0

/-- The check with its salted digests securely computes `F_multVerify` with selective abort in the
`{F_coin, F_extendMult, F_rand}`-hybrid model (GS20, Lemmas 8 to 11, and CGH+18, Protocol 3.3). The
error is the soundness of the check and the birthday bound of the counted calls and the honest
points, namely the history and the digest of each term at each operator and the `R + 2` coin keys. -/
def MultVerifyStatement [SampleableType E] : Prop :=
  ∀ counts : List ℕ,
    SecurelyComputes prims (checkProtocol K) (checkRounds counts.sum) (checkFunctionalities K) FmultVerify
      (TupleInputs K counts) (checkOverhead C counts.sum)
      fun q => checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q + checkHashError C counts.sum q

/-- An honest check accepts correct tuples, except when it aborts on a coin. -/
def MultVerifyCompletenessStatement [SampleableType E] : Prop :=
  ∀ counts : List ℕ,
    Completes prims (checkProtocol K) (checkRounds counts.sum) (checkFunctionalities K) checkReply
      FmultVerify (fun _ => Finset.univ) (fun D x => TupleInputs K counts D x ∧ CorrectTuples x)
      (abortErrorOf (E := E) (halvings counts.sum))

/-- A batch securely computes `F_main` with selective abort in the `{F_mult, F_multVerify}`-hybrid
model. This is GS20, Theorem 2, for public outputs and inputs that the operators already share.

* The overhead is the emulation of the copy hashes of `OpenRep`, two for each term and operator.
* The error `copyHashError` is the birthday bound `(q + 2 n C(n, t - 1))² / 2^256` of the copy
  hashes. The adversary chooses the honest copy of each term that it holds at the `Rerand` leak, so
  a collision of two copies passes the hash check of `OpenRep`. The `q` counted calls and the
  `2 n C(n, t - 1)` copy hashes of the honest operators can collide. -/
def MainStatement : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit),
    SecurelyComputes prims (mainProtocol K mode jobs) (mainRounds jobs) (mainFunctionalities K mode) (Fmain jobs)
      (MainInputs jobs) (termHashes C) (copyHashError C)

/-- An honest batch gives the outputs of `F_main`. -/
def MainCompletenessStatement : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit),
    Completes prims (mainProtocol K mode jobs) (mainRounds jobs) (mainFunctionalities K mode) mainReply
      (Fmain jobs) (fun _ => Finset.univ) (MainInputs jobs) 0

/-- `Combine'` of the parts of every quorum gives `F(msk, x)` (PRAWNS, Definition 2.1). -/
def TprfCorrectnessStatement (C : Committee) : Prop :=
  ∀ (J : C.Quorum) (x : Point) (ec : Message), ∀ r ∈ support (runWorld prims (tprfCorrectnessRun J x ec)), r.1 = true

/-- The threshold PRF is adaptively secure (PRAWNS, Definition 2.2 and Theorem 5.1). -/
def TprfSecurityStatement (C : Committee) : Prop :=
  ∀ (A : TprfAdversary C) (q : ℕ),
    IsQueryBoundP A (fun t => Sum.elim Counted (fun _ => False) t) q →
    tprfAdvantage prims A ≤ tprfError C q

/-- An honest quorum fails with probability at most `2 (1 - p)^L`, for the search of the top
signature in `KeyGen` and the search of the signature. Every signature that it outputs verifies
(PRAWNS, Section 3.1, honest run). -/
def SigningCorrectnessStatement (C : Committee) : Prop :=
  ∀ (J : C.Quorum) (e : KeyIndex) (m : Message),
    (∀ r ∈ support (runWorld prims (honestSigning J e m)), r.1 ≠ some false) ∧
      (Pr[fun r => r.1 = none | runWorld prims (honestSigning J e m)]).toReal ≤ 2 * searchFailure

/-- The signing is strongly unforgeable with adaptive corruption (PRAWNS, Definition 3.2), in the
random-oracle model.

* `q` bounds the calls of `H` and `PRG` by every party in the signing world. `signingHashError q` is
  `q / 2^127`.
* At most `t - 1` corrupt operators leave the seed of at least one term and the pair keys of the
  honest pairs hidden. `seedHitError` pays a call on such a key, and `seedCollisionError` two equal
  keys. Otherwise each unopened `F(x)` is a fresh uniform value, which covers `ρ_e` before round 1,
  the chain starts and the masks.
* The claim has one named coordination assumption, `breaksOneMessagePerKey`. Honest operators sign
  at most one message for each key over all quorums. The game enforces it, the PoC does not, and
  production must. -/
def SigningSecurityStatement (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q →
    tsigAdvantage prims A ≤ signingHashError q + seedHitError C q + seedCollisionError C

section Lifetime

variable (attempts : ℕ)

/-- Every lifetime makes at most `Q` calls of `H` and `PRG`, by every party, cache hits included. The
bound holds for every answer of the oracles (BR93, `IsQueryBoundP` of VCVio), so also on runs that
the real lifetime never reaches. It bounds the paths of the lifetime game. Unlike `IsQueryBounded`,
it does not bound an adversary state that no answer reaches. -/
def HasLifetimeQueryBound (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ) : Prop :=
  IsQueryBoundP (lifetimeGame K circuits settings attempts D A) LifetimeCounted Q

/-- The probability that the lifetime adversary forges. -/
def lifetimeAdvantage (D : C.Coalition) (A : LifetimeAdversary C E) : ℝ :=
  (Pr[fun r => r.1 = true | lifetimeRun prims (lifetimeGame K circuits settings attempts D A)]).toReal

/-- The probability that `lifetimeForger` wins the existing signing game `G^tsig` (`tsigGame`) in the
lifetime world `lifetimeWorld`, not in `signingWorld`. In this world `H` answers the inputs that the
MPC evaluates (`MpcInput`) with the fixed `Th`, and every other input as a lazy random oracle.

`lifetimeForger` makes at most `q₀ = Q + lifetimeOverhead C attempts Q` calls of `H` and `PRG` when
the lifetime adversary makes at most `Q`. `SigningSecurityStatement` does not bound this term,
because that claim is for `signingWorld`, where all of `H` is a random oracle, and `lifetimeForger`
uses the circuits of the fixed `Th`. -/
def lifetimeForgerAdvantage (D : C.Coalition) (A : LifetimeAdversary C E) : ℝ :=
  (Pr[fun r => r.1 = true | lifetimeRun prims (tsigGame (lifetimeForger K circuits settings attempts D A))]).toReal

/-- The signing is strongly unforgeable over the lifetime of the key, against a static coalition of
at most `t - 1` operators, up to the advantage of one fixed forger.

* The keygen runs once on the real network. The adversary gets the public parameter. It gets the
  public key and the top tree of the first honest operator once that operator holds them. It runs
  each ceremony at most `attempts` times, one at a time, and sends signing requests between the
  rounds. No ceremony of a bottom tree runs after the first signing request on it. An honest
  operator answers a signing request only with its own ceremony output of the tree, and it signs at
  most one message for each key.
* `Th` is the fixed function of `prims` on the inputs that the MPC evaluates, and the fixed
  `circuits` compute it, as in the ceremony claims. Every other input of `H` is a random oracle.
* `Q` bounds the calls of `H` and `PRG` by every party, on every path of the lifetime game.
* The keygen term and each ceremony term take the budget `(fuel + 2) Q` with the fuel of the phase.
  One step of the phase adversary holds all that the lifetime adversary does between two rounds.
* `keygenHashError` pays the keygen. Each run of each ceremony pays its check, its birthday bound
  and its stream keys, after the `q₀ = Q + lifetimeOverhead` calls of the earlier phases.
* Each run also pays `seedHitError` for a call on a hidden key of an honest term or pair. The
  emulated signing keeps the masks of the honest pairs in its own table.
* Each run pays the PRF advantage of its own reduction. Each bottom tree pays one failed search,
  because each retry gives the same search.
* The last term is `lifetimeForgerAdvantage`, the advantage of the fixed forger `lifetimeForger`
  in the signing game. The claim does not bound it, and `SigningSecurityStatement` does not bound it. -/
def LifetimeSecurityStatement : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    ∀ (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ),
      HasLifetimeQueryBound K circuits settings attempts D A Q →
      let q₀ := Q + lifetimeOverhead C attempts Q
      let q := (ceremonyFuel circuits settings + 2) * Q
      let runError := fun tree => (attempts : ℝ) * (treeCheckError (E := E) circuits settings tree (q₀ + q) +
        treeHashError circuits settings C tree (q₀ + q) + streamKeyError C + seedHitError C (q₀ + q))
      lifetimeAdvantage prims K circuits settings attempts D A ≤
        keygenHashError C ((setupRounds + 2) * Q) +
          (runError .top + ∑ b : Fin (2 ^ layerHeight), runError (.bottom b)) +
          ∑ n : Fin (lifetimeRuns attempts),
            PRFScheme.prfAdvantage (hiddenStreams prims.aes) (lifetimeRunReduction K circuits settings attempts prims D A n) +
          2 ^ layerHeight * searchFailure + lifetimeForgerAdvantage prims K circuits settings attempts D A

end Lifetime

/-- The security claim, for every committee, every check field of characteristic `2` with its
constants, every `Th` and AES-128, every circuit family, and every setting. -/
abbrev ThresholdLeanXmssSecurityStatement : Prop :=
  ∀ (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (K : Constants C E) (prims : Primitives) (circuits : Circuits) (settings : Settings),
    letI : SampleableType E := SampleableType.ofFintype E
    KeygenCompletenessStatement prims C E ∧ KeygenSecurityStatement prims C E ∧
      TreeCompletenessStatement prims K circuits settings ∧ TreeSecurityStatement prims K circuits settings ∧
      DealerTreeStatement prims circuits settings C ∧ TreeSuccessStatement prims circuits settings C ∧
      CoinStatement prims K ∧ CoinCompletenessStatement prims K ∧ MultStatement prims K ∧
      ExtendMultStatement prims K ∧ MultVerifyStatement prims K ∧ MultVerifyCompletenessStatement prims K ∧
      MainStatement prims K ∧ MainCompletenessStatement prims K ∧
      TprfCorrectnessStatement prims C ∧ TprfSecurityStatement prims C ∧
      SigningCorrectnessStatement prims C ∧ SigningSecurityStatement prims C

end ThresholdLeanXmss
