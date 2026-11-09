import ThresholdLeanXmss.Reductions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Threshold leanXMSS security statement

The claims about the protocol of `Scheme.lean`, at the level at which GS20 and PRAWNS state them.
`Ideal.lean` holds the functionalities and the games. `Reductions.lean` holds the simulators and the
reductions that the claims name.

| claim | statement | source |
| --- | --- | --- |
| `KeygenCompletenessStatement` | An honest keygen gives the keys of `F_keygen`, except when two derived keys collide. | the note, Section 2.1, honest run |
| `KeygenSecurityStatement` | The keygen securely computes `F_keygen` with selective abort, with the simulator `keygenSimulator`. | GL05 and CDG+18 |
| `TreeCompletenessStatement` | An honest ceremony gives the tree of `F_tree`. | GS20, Theorem 2, honest run |
| `TreeSecurityStatement` | Each ceremony securely computes `F_tree` with selective abort, with the simulator `treeSimulator`. | GS20, Theorem 2, and GL05 |
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
| `SigningSecurityStatement` | The signing is strongly unforgeable with adaptive corruption, up to the reductions and `N² / 2^129` for tree collisions. | PRAWNS, Definition 3.2 and Theorem 3.1 |

GS20 states no completeness lemma. Security with abort alone allows a protocol that always aborts,
so each completeness claim is the honest run of the protocol of its row.

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
* `Th` is one fixed function on the inputs that the MPC evaluates, namely the chain steps and the
  commitment `c_e`, in every claim. The ceremony claims assume that the circuits compute it
  (`CircuitsCompute`). The leaves, the nodes, the message digests and every other domain of `H` are a
  lazy random oracle.
* `PRG` is AES-128 under a hash of the key. The ceremony claim pays an AES term and a birthday term
  for the 128-bit keys.
* The budget `q` bounds the counted calls of the adversary and of the distinguisher for every answer
  of the oracles, namely their random-oracle calls (BR93, `IsQueryBounded` with `IsQueryBoundP` of
  VCVio). The honest operators and the functionalities call `H` for free.
* Each simulation claim bounds the counted calls of the ideal run by `q` plus a fixed overhead
  (Canetti 2000, efficient simulators). An explicit simulator emulates the honest operators on the
  free copy as the real operators do, and its overhead counts only its programming queries. A
  simulator that a claim only asserts to exist has all its calls counted, and its overhead counts
  its emulation of the honest operators.
* A protocol securely computes a functionality when its real execution and the ideal execution with
  a simulator give the same joint output of the adversary and the honest operators. A distinguisher
  with oracle access reads it.
* With selective abort, the adversary names the honest operators that receive each output (GL05).
* The PRSS outputs of one round play `F_rand`, as the PRSS of CDI05 realizes it.
* The signing adversary corrupts adaptively, and a corruption gives only the keys of an operator.
  After a ceremony, an operator erases its ceremony state.
* At most `t - 1` operators are corrupt over the lifetime of the key.
* The keygen and ceremony claims cover their static coalitions, and the signing claim covers
  adaptive corruptions. End-to-end security would need a composed claim, which these claims do not
  give.

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
* Bit `q` of a word of tuples has the public weight `x^q` in place of a coin (`src/check.rs`). This
  owner-approved deviation has no published source. The weights are linearly independent over
  `F_2`, so a wrong word stays a nonzero weight, and the Schwartz-Zippel count of Lemma 8 holds.
* The first seven halving steps fold the slices with the coin kept out of `x` (Gruen 2024) and the
  small-value table of BDDT25. Each step is still a degree-2 claim in its challenge.
* A challenge is the first value outside `{0, 1}` of the expansion of a coin key `H(coin)`. The
  implementation expands with AES-128 under that public key. The model takes the expansion as a
  domain of `H`, which deviates from the implementation.
* The explicit simulators program `H` as the programmable random oracle of CDG+18. The world has no
  `IsProgrammed` query of CDG+18, because no party can test whether a point is programmed.
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

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-! ## Error terms -/

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

/-- The probability that an honest check with `R` halving steps aborts. A slice coin is `0`, or one
of the `R + 1` challenges finds no value outside `{0, 1}` within `challengeTries` values, or two of
the `R + 2` coin keys collide, which `(R + 2)² / 2` pairs bound. -/
def abortErrorOf (R : ℕ) : ℝ :=
  (sliceBits : ℝ) / Fintype.card E + (R + 1 : ℕ) * (2 / Fintype.card E : ℝ) ^ challengeTries +
    ((R + 2) ^ 2 : ℕ) / 2 ^ 257

/-- The probability that an honest check of some batch of a ceremony aborts. Two of the `B (R + 2)`
coin keys of all `B` batches can collide, because a later check reads the cached coins of an earlier
batch. -/
def treeAbortError (tree : Tree) : ℝ :=
  let batches := treeBatches settings tree
  let halvingCount := maxBatch circuits settings fun jobs => halvings (tupleCount jobs)
  batches * ((sliceBits : ℝ) / Fintype.card E + (halvingCount + 1 : ℕ) * (2 / Fintype.card E : ℝ) ^ challengeTries) +
    ((batches * (halvingCount + 2)) ^ 2 : ℕ) / 2 ^ 257

/-- The honest points of `H` in the keygen that a counted call must not hit, namely the parts of each
operator, the derived keys, and the inputs of the hashes of the shared seeds. -/
def keygenSecrets (C : Committee) : ℕ :=
  C.n * (1 + C.n.choose (C.t - 1) + C.n) + 1 + C.n.choose (C.t - 1) + C.n.choose 2 + C.n ^ 2

/-- The birthday bound of the counted calls and the honest points of the keygen. It covers a guessed
secret, a collision of two secrets, a failed programming and a failed extraction. -/
def keygenHashError (C : Committee) (q : ℕ) : ℝ := ((q + keygenSecrets C) ^ 2 : ℕ) / 2 ^ 256

/-- The programming queries of `keygenSimulator`, one for `P`, at most one for each term and one for
each pair of a corrupt and an honest operator. -/
def keygenOverhead (C : Committee) : ℕ := 1 + C.n.choose (C.t - 1) + C.n ^ 2

/-- The honest points of `H` in a ceremony that a counted call must not hit. The PRSS setup has the
parts of each operator, the derived keys and the inputs of the hashes of the shared keys. Each PRSS
key has a stream-key input. Each batch has the history, the digest and the copy hash of each term,
the copies that a corrupt owner sends to each honest operator, which it hashes for free, and the
`R + 2` coin keys of its check. -/
def treeSecrets (C : Committee) (tree : Tree) : ℕ :=
  let terms := C.n.choose (C.t - 1)
  let pairs := C.n.choose 2
  C.n * (terms + C.n) + terms + pairs + C.n ^ 2 + (terms + pairs) +
    treeBatches settings tree * (3 * terms + C.n * terms +
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2)

/-- The birthday bound of the counted calls and the honest points of a ceremony. -/
def treeHashError (C : Committee) (tree : Tree) (q : ℕ) : ℝ :=
  ((q + treeSecrets circuits settings C tree) ^ 2 : ℕ) / 2 ^ 256

/-- The birthday bound `k² / 2^129` of the 128-bit AES keys of the `k` PRSS keys of a ceremony
(`doc/dkg.md` 3.3). -/
def streamKeyError (C : Committee) : ℝ := ((C.n.choose (C.t - 1) + C.n.choose 2) ^ 2 : ℕ) / 2 ^ 129

/-- The error of Theorem 5.1 with `F(k, x) = H16(k ‖ x)` in the random-oracle model, for `q`
counted calls. PRAWNS bounds it by `2 C(n, t - 1) ε_F`, which gives `2 C(n, t - 1) q / 2^256`. The
masks add `n² q / 2^256` for the guess of a hidden pair key. Honest calls are free, so two of the
`C(n, t - 1) + n²` keys may also collide. -/
def tprfError (C : Committee) (q : ℕ) : ℝ :=
  ((2 * C.n.choose (C.t - 1) + C.n ^ 2) * q + (C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 : ℕ) / 2 ^ 256

/-- The birthday bound `N² / 2^129` of a collision of the random oracle on leaves, nodes and message
digests. `N` calls give at most `N² / 2` pairs of different inputs, and each pair has one 128-bit
truncated output with probability `2^-128`. -/
def treeCollisionError (N : ℕ) : ℝ := (N ^ 2 : ℕ) / 2 ^ 129

/-- The probability that two derived keys of one kind have the same parts. A derivation hashes only
the tag of its kind and the parts (`src/mpc.rs`), so two terms or two pairs share a key only when an
honest part repeats. -/
def derivedKeyCollision (C : Committee) : ℝ :=
  (C.n.choose (C.t - 1) ^ 2 + C.n.choose 2 ^ 2 : ℕ) / 2 ^ 256

/-- The calls of an emulation of the honest operators in a check of `count` tuples. Each operator
hashes `R + 2` coin keys, `d` expanded coins, at most `challengeTries` expanded values for each of
the `R + 1` challenges, and the history and the digest of each term. -/
def checkOverhead (C : Committee) (count : ℕ) : ℕ :=
  C.n * (halvings count + 2 + coins count + (halvings count + 1) * challengeTries + 2 * C.n.choose (C.t - 1))

/-- The probability `p` that one trial of a randomizer search finds a codeword, since a message
digest is a uniform 128-bit value. -/
def codewordProbability : ℝ :=
  ((Finset.univ.filter fun x : Encoding => Codeword.sum x = targetSum).card : ℝ) / 2 ^ digestBits

/-- The probability `(1 - p)^L` that a randomizer search of `L` trials fails. -/
def searchFailure : ℝ := (1 - codewordProbability) ^ randomizerAttemptLimit

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
def KeygenCompletenessStatement : Prop :=
  Completes prims (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) setupRounds noFunctionality
    (fun l => l.elim) Fkeygen (fun _ => Finset.univ) (fun _ _ => True) (derivedKeyCollision C)

/-- The keygen securely computes `F_keygen` with selective abort against a static coalition, with the
simulator `keygenSimulator` (GL05 and CDG+18). -/
def KeygenSecurityStatement : Prop :=
  SimulatedBy prims (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) setupRounds Fkeygen
    (fun _ _ => True) keygenSimulator (keygenOverhead C) fun _ _ _ _ _ q => keygenHashError C q

/-- An honest ceremony gives the tree of `F_tree`, except when an honest check aborts. -/
def TreeCompletenessStatement : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree),
    Completes prims (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
      (ceremonyFuel circuits settings) noFunctionality (fun l => l.elim) (Ftree circuits settings top tree)
      (fun _ => Finset.univ) DealtInputs (treeAbortError (E := E) circuits settings tree)

/-- Each ceremony securely computes `F_tree` with selective abort against its own static coalition,
with the simulator `treeSimulator` (GS20, Theorem 2, and GL05). The bound adds the AES term of the
reduction `prgReduction` on the real run, because `treeSimulator` already uses ideal streams. -/
def TreeSecurityStatement : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree),
    SimulatedBy prims (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
      (ceremonyFuel circuits settings) (Ftree circuits settings top tree) DealtInputs
      (treeSimulator K circuits settings top tree) 0 fun D A x z Z q =>
        treeCheckError (E := E) circuits settings tree q + treeHashError circuits settings C tree q + streamKeyError C +
          PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D
            (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
              (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput)) x z) Z))

/-- `Coin` securely computes `F_coin` with selective abort in the `F_rand`-hybrid model, perfectly
(GS20, Lemma 3). The simulator makes no oracle call of its own. -/
def CoinStatement [SampleableType E] : Prop :=
  SecurelyComputes prims (coinProtocol K) 2 (Frand E) Fcoin SameCount 0 fun _ => 0

/-- An honest `Coin` gives the output of `F_coin`. -/
def CoinCompletenessStatement [SampleableType E] : Prop :=
  Completes prims (coinProtocol K) 2 (Frand E) (randReply E) Fcoin (fun _ => Finset.univ) SameCount 0

/-- `MulRep` and `Reshare` in each mode securely compute `F_mult` up to an additive attack in the
`F_rand`-hybrid model, perfectly (GS20, Lemma 4). The simulator makes no oracle call of its own. -/
def MultStatement : Prop :=
  ∀ mode : ReshareMode,
    SecurelyComputes prims (multProtocol K mode) (1 + mode.rounds) (Frand Bit) (FmultBit K mode)
      (fun D x => SameCount D fun i => (x i).2.2) 0 fun _ => 0

/-- `MulRep` or `MulSh` and `Reshare` securely compute `F_extendMult` up to an additive attack in the
`F_rand`-hybrid model, perfectly (GS20, Lemma 5). The simulator makes no oracle call of its own. -/
def ExtendMultStatement [SampleableType E] : Prop :=
  SecurelyComputes prims (extendMultProtocol K) 2 (Frand E) (FextendMult K) (ShamirInputs K) 0 fun _ => 0

/-- The check with its salted digests securely computes `F_multVerify` with selective abort in the
`{F_coin, F_extendMult, F_rand}`-hybrid model (GS20, Lemmas 8 to 11, and CGH+18, Protocol 3.3). The
error is the soundness of the check and the birthday bound of the counted calls and the honest
points, namely the history and the digest of each term at each operator and the `R + 2` coin keys. -/
def MultVerifyStatement [SampleableType E] : Prop :=
  ∀ counts : List ℕ,
    SecurelyComputes prims (checkProtocol K) (2 * halvings counts.sum + 8) (checkFunctionalities K) FmultVerify
      (TupleInputs K counts) (checkOverhead C counts.sum)
      fun q => checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q +
        ((q + 2 * C.n * C.n.choose (C.t - 1) + halvings counts.sum + 2) ^ 2 : ℕ) / 2 ^ 256

/-- An honest check accepts correct tuples, except when it aborts on a coin. -/
def MultVerifyCompletenessStatement [SampleableType E] : Prop :=
  ∀ counts : List ℕ,
    Completes prims (checkProtocol K) (2 * halvings counts.sum + 8) (checkFunctionalities K) checkReply
      FmultVerify (fun _ => Finset.univ) (fun D x => TupleInputs K counts D x ∧ CorrectTuples x)
      (abortErrorOf (E := E) (halvings counts.sum))

/-- A batch securely computes `F_main` with selective abort in the `{F_mult, F_multVerify}`-hybrid
model. This is GS20, Theorem 2, for public outputs and inputs that the operators already share.

* The overhead is the emulation of the copy hashes of `OpenRep`, two for each term and operator.
* The error `(q + 2 n C(n, t - 1))² / 2^256` is the birthday bound of the copy hashes. The
  adversary chooses the honest copy of each term that it holds at the `Rerand` leak, so a collision
  of two copies passes the hash check of `OpenRep`. The `q` counted calls and the `2 n C(n, t - 1)`
  copy hashes of the honest operators can collide. -/
def MainStatement : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit),
    SecurelyComputes prims (mainProtocol K mode jobs) (depth jobs + 3) (mainFunctionalities K mode) (Fmain jobs)
      (MainInputs jobs) (2 * C.n * C.n.choose (C.t - 1))
      fun q => ((q + 2 * C.n * C.n.choose (C.t - 1)) ^ 2 : ℕ) / 2 ^ 256

/-- An honest batch gives the outputs of `F_main`. -/
def MainCompletenessStatement : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit),
    Completes prims (mainProtocol K mode jobs) (depth jobs + 3) (mainFunctionalities K mode) mainReply
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

/-- The signing is strongly unforgeable with adaptive corruption (PRAWNS, Definition 3.2 and
Theorem 3.1), in the reduction form of Theorem 3.1.

* A guess of Game 2 counts only on the highest layer where the forgery differs from `KeyGen`.
* The guess of Game 2 costs `guessCount`. PRAWNS, equation (6), prints `ℓd ε_F + ε_f`. Its
  equations (2) to (4) give `ℓd (ε_F + ε_f)`, which this bound uses.
* The random-oracle events of the threshold PRF enter through `TprfSecurityStatement`, whose bound
  is `tprfError`.
* A collision of `E_1` is a collision of the fixed `Th` on chain steps or commitments, which
  `collisionReduction` finds, or a collision of the random oracle on leaves, nodes or message
  digests. The second costs `N² / 2^129` for `N` such calls by every party, the honest key
  generation, the signers and the verification included.
* The claim has one named coordination assumption. Honest operators sign at most one message for
  each key over all quorums. The game enforces it, the PoC does not, and production must. -/
def SigningSecurityStatement (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (N : ℕ), HasTreeCallBound prims (tsigGame A) N →
    tsigAdvantage prims A ≤ collisionAdvantage prims (collisionReduction A) + treeCollisionError N +
      guessCount * (tprfAdvantage prims (tprfReduction A) + sprAdvantage prims (sprReduction A))

/-- The security claim, for every committee, every check field of characteristic `2` with its
constants, every `Th` and AES-128, every circuit family that computes `Th`, and every setting. -/
abbrev ThresholdLeanXmssSecurityStatement : Prop :=
  ∀ (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (K : Constants C E) (prims : Primitives) (circuits : Circuits) (settings : Settings),
    letI : SampleableType E := SampleableType.ofFintype E
    CircuitsCompute circuits prims.Th →
    KeygenCompletenessStatement (C := C) (E := E) prims ∧ KeygenSecurityStatement (C := C) (E := E) prims ∧
      TreeCompletenessStatement prims K circuits settings ∧ TreeSecurityStatement prims K circuits settings ∧
      CoinStatement prims K ∧ CoinCompletenessStatement prims K ∧ MultStatement prims K ∧
      ExtendMultStatement prims K ∧ MultVerifyStatement prims K ∧ MultVerifyCompletenessStatement prims K ∧
      MainStatement prims K ∧ MainCompletenessStatement prims K ∧
      TprfCorrectnessStatement prims C ∧ TprfSecurityStatement prims C ∧
      SigningCorrectnessStatement prims C ∧ SigningSecurityStatement prims C

end ThresholdLeanXmss
