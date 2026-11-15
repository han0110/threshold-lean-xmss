import ThresholdLeanXmss.Statement.SecureComputation
import Mathlib.Algebra.Polynomial.Eval.Defs
import VCVio.EvalDist.EvalDistEq

/-!
# The seed generation, the ceremonies and the gadgets

The claims about the key generation of `doc/dkg.md`, at the level at which GS20 states them. This
file holds the error terms, the valid inputs and the claims. `Theorems.lean` holds the model.

## Deviations from GS20

* Replicated sharing replaces Shamir sharing (CDI05). A corrupt operator that fills a term can give
  each honest holder its own copy. So `F_mult` sums the shares of the honest operators from their
  own views and takes a copy offset, and `F_multVerify` checks the copies (KPPS23, `Π_agree`, and
  CGH+18, Protocol 3.3).
* `F_mult` and `F_multVerify` leak the view of each honest operator of the terms that the corrupt
  operators know. GS20 leaks one copy of these terms in Functionalities 7 and 16. In a run of
  circuits, a corrupt filler chooses each split copy, so the adversary already knows the leaked
  copies. On other inputs of the gadget claims, the leak is larger than in GS20.
* `F_main` also leaks these views. Its inputs agree at every holder, the corrupt holders included,
  as the seed generation echo makes them, so it leaks only what GS20, Functionality 18, leaks.
* Each operator aborts alone, so every functionality except `F_rand` has selective abort, `F_mult`
  and `F_extendMult` included. GS20 aborts all honest operators together.
* `F_rand` has no abort, because the PRSS of CDI05 that realizes it sends no message.
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
  `n = 2t + 1`). `ceremonySimulator` is defined for every coalition size, because it shifts one
  lacked term at the opening.
* The model splits each ceremony into batches of `batchSize` jobs. The implementation sizes chain
  batches and commitment batches apart, and it puts the top randomizer value in the last commitment
  batch. The implementation runs the signature ceremony as one batch of all its jobs
  (`top_signature` of `src/dkg.rs`).
* The signature of the root of a bottom tree by its top key is one more ceremony, with its own PRSS
  setup (`new_bottom_tree` of `src/dkg.rs`). `TreeSecurityStatement` is the claim for one ceremony.
  It does not join the two ceremonies of a bottom tree.
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

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

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

/-- The soundness error of the checks of all batches of a ceremony of `jobs`. -/
def treeCheckError (jobs : List Job) (q : ℕ) : ℝ :=
  (chunks settings.batchSize jobs).length *
    checkErrorOf (E := E) (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
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

/-- The probability that an honest check of some batch of a tree aborts. Two of the `B (R + 2)`
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

/-- The birthday bound of the counted calls and the honest points of the seed generation. It covers a guessed
secret, a collision of two secrets, a failed programming and a failed extraction. -/
def seedGenHashError (C : Committee) (q : ℕ) : ℝ := ((q + seedGenSecrets C) ^ 2 : ℕ) / 2 ^ 256

/-- The programming queries of `seedGenSimulator`, one for `P`, at most one for each term and one for
each pair of a corrupt and an honest operator. -/
def seedGenOverhead (C : Committee) : ℕ := 1 + termCount C + C.n ^ 2

/-- The honest points of `H` in a ceremony of `jobs` that a counted call must not hit. The PRSS
setup has the parts of each operator, the derived keys and the inputs of the hashes of the shared
keys. Each PRSS key has a stream-key input. Each batch has the history, the digest and the copy hash
of each term, the copies that a corrupt owner sends to each honest operator, which it hashes for
free, and the `R + 2` coin keys of its check. -/
def treeSecrets (C : Committee) (jobs : List Job) : ℕ :=
  let terms := termCount C
  let pairs := C.n.choose 2
  C.n * (terms + C.n) + terms + pairs + C.n ^ 2 + (terms + pairs) +
    (chunks settings.batchSize jobs).length * (3 * terms + C.n * terms +
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2)

/-- The birthday bound of the counted calls and the honest points of a ceremony of `jobs`. -/
def treeHashError (C : Committee) (jobs : List Job) (q : ℕ) : ℝ :=
  ((q + treeSecrets circuits settings C jobs) ^ 2 : ℕ) / 2 ^ 256

/-- The birthday bound `k² / 2^129` of the 128-bit AES keys of the `k` PRSS keys of a ceremony
(`doc/dkg.md` 3.3). -/
def streamKeyError (C : Committee) : ℝ := ((termCount C + C.n.choose 2) ^ 2 : ℕ) / 2 ^ 129

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
included, as the inputs of a ceremony come from the seeds that the seed generation echo compares. -/
def MainInputs (jobs : List Circuit) (D : C.Coalition) (x : C.Party → List (C.Term → List Bit)) : Prop :=
  ∃ widths : List ℕ, widths.length = jobs.length ∧
    (∀ i, i ∉ D.1 → (x i).length = jobs.length ∧ ∀ k < jobs.length, ∀ T,
      ((((x i)[k]?).getD fun _ => []) T).length = if i ∈ C.holders T then widths.getD k 0 else 0) ∧
    ∀ k : ℕ, Consistent noCoalition fun i T => (((x i)[k]?).getD fun _ => []) T

/-! ## The claims -/

/-- An honest seed generation gives the keys of `F_seedGen`, except when two derived keys collide. -/
def SeedGenCompletenessStatement (C : Committee) (E : Type) : Prop :=
  Completes prims (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) setupRounds noFunctionality
    (fun l => l.elim) FseedGen (fun _ => Finset.univ) (fun _ _ => True) (derivedKeyCollision C)

/-- The seed generation securely computes `F_seedGen` with selective abort against a static coalition, with the
simulator `seedGenSimulator` (GL05 and CDG+18). -/
def SeedGenSecurityStatement (C : Committee) (E : Type) : Prop :=
  SimulatedBy prims (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) setupRounds FseedGen
    (fun _ _ => True) seedGenSimulator (seedGenOverhead C) fun _ _ _ _ _ q => seedGenHashError C q

/-- The honest ceremonies of a tree give the tree of `F_tree`, except when an honest check aborts.
The program is `newTree`. For a bottom tree it is the ceremony of the tree, the randomizer search,
the signature ceremony with its own PRSS setup, and the check of the top signature. -/
def TreeCompletenessStatement : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree),
    Completes prims (fun i keys => (newTree K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
      (setupRounds + ceremonyFuel circuits settings) noFunctionality (fun l => l.elim) (Ftree circuits settings top tree)
      (fun _ => Finset.univ) DealtInputs (treeAbortError (E := E) circuits settings tree)

/-- One ceremony securely computes `F_ceremony` with selective abort against its own static
coalition, with the simulator `ceremonySimulator` (GS20, Theorem 2, and GL05). The claim is for
each start of the counters and for the three forms of a job list, namely `topJobs`, `bottomJobs b`
and `signJobs b encoding`, for every `b` and every `encoding`. The job list and the counters are
public inputs. The bound adds the multi-key PRF advantage of `prgReduction` against `hiddenStreams`
on the real run, because `ceremonySimulator` already uses ideal streams. This claim is no field of
the bundle `Theorems`. It is stated and not proved.

The claim does not join the two ceremonies of a bottom tree. It does not state that the honest
operators of a signature ceremony hold the same `encoding`, or that each of them starts. -/
def TreeSecurityStatement : Prop :=
  0 < settings.batchSize → ∀ (counters : ℕ × ℕ) (b : Fin (2 ^ layerHeight)) (encoding : Encoding),
    ∀ jobs ∈ [topJobs, bottomJobs b, signJobs b encoding],
    SimulatedBy prims (fun i keys => (ceremony K circuits settings i keys counters jobs : PartyM C E RealSpec (List (List Bit))))
      (ceremonyFuel circuits settings) (Fceremony circuits jobs) DealtInputs
      (ceremonySimulator K circuits settings counters jobs) 0 fun D A x z Z q =>
        treeCheckError (E := E) circuits settings jobs q + treeHashError circuits settings C jobs q + streamKeyError C +
          (PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D
            (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
              (fun i keys => (ceremony K circuits settings i keys counters jobs : PartyM C E RealSpec (List (List Bit)))) x z) Z))).toReal

/-- When the circuits compute `Th`, the dealer of `F_tree` gives the trees of `KeyGen` of the signing
claims, namely `referenceTree` with the PRF values of the seeds. The two runs have the same
distribution of the tree and of the next cache of `H`, from every cache. -/
def DealerTreeStatement (C : Committee) : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
      (cache : HashCache C),
      (simulateQ (localAnswer prims)
          (liftComp (Prod.fst <$> dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run cache =ᵈ
        (simulateQ (localAnswer prims)
          (liftComp (referenceTree (fun oa => tweakable oa) (prfValue seeds) parameter top tree) (LocalSpec C))).run cache

/-- When the circuits compute `Th`, the dealer of `F_tree` gives the top tree, and then a bottom
tree `b` on that top tree, except with probability `(1 - p)^L` for the randomizer search of its top
signature. `TreeCompletenessStatement` bounds the distance of the honest ceremonies of a tree to
`F_tree`, so this claim bounds the abort of `F_tree` itself. -/
def TreeSuccessStatement (C : Committee) : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)),
      (Pr{let r ← runWorld prims (free (C := C) (liftComp (do
        let (output, _) ← dealerCeremony circuits settings parameter seeds emptyTop .top
        let some top := TreeOutput.topTree output | pure none
        Prod.fst <$> dealerCeremony circuits settings parameter seeds top (.bottom b)) _))}[r.1 = none]).toReal ≤ searchFailure

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

end ThresholdLeanXmss
