import ThresholdLeanXmssSecurity.Base.Dkg
import ThresholdLeanXmss.Statement.Dkg
import Mathlib.Algebra.Polynomial.Eval.Defs
import VCVio.EvalDist.EvalDistEq

/-!
# The claims of the building blocks and of one tree

The notions of secure computation with a distinguisher, the valid inputs, and the claims of the
building blocks, of the honest run of one tree and of the dealer of a tree.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

section SecureComputation

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A distinguisher reads the joint output of the adversary and the honest operators (GL05 and
Canetti 2000). Its oracle access is the random-oracle form of this model. -/
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

end SecureComputation

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The probability that an honest check with `R` halving steps aborts, on its coins or on a collision
of its `R + 2` coin keys. -/
def abortErrorOf (R : ℕ) : ℝ := coinFailure (E := E) R + coinKeyCollision (R + 2)

/-- The calls of an emulation of the honest operators in a check of `count` tuples. Each operator
hashes `R + 2` coin keys, `d` expanded coins, at most `challengeTries` expanded values for each of
the `R + 1` challenges, and the history and the digest of each term. -/
def checkOverhead (C : Committee) (count : ℕ) : ℕ :=
  C.n * (halvings count + 2 + coins count + (halvings count + 1) * challengeTries + 2 * termCount C)

/-- The birthday bound of the counted calls and the copy hashes of `OpenRep` of the honest
operators. -/
def copyHashError (C : Committee) (q : ℕ) : ℝ := ((q + termHashes C) ^ 2 : ℕ) / 2 ^ 256

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

/-- The honest ceremonies of a tree give the tree of `F_tree`, except when an honest check aborts.
The program is `newTree`. For a bottom tree it is the ceremony of the tree, the randomizer search,
the signature ceremony with its own PRSS setup, and the check of the top signature. -/
def TreeCompletenessStatement : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree),
    Completes prims (fun i keys => (newTree K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
      (setupRounds + ceremonyFuel circuits settings) noFunctionality (fun l => l.elim) (Ftree circuits settings top tree)
      (fun _ => Finset.univ) DealtInputs (treeAbortError (E := E) circuits settings tree)

/-- When the circuits compute `Th`, the dealer of `F_tree` gives the trees of `KeyGen` of the signing
claims, namely `referenceTree` with the PRF values of the seeds. The two runs have the same
distribution of the tree and of the next cache of `H`, from every cache. -/
def DealerTreeCorrectnessStatement (C : Committee) : Prop :=
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
def DealerTreeSuccessStatement (C : Committee) : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)),
      (Pr{let r ← runWorld prims (free (C := C) (liftComp (do
        let (output, _) ← dealerCeremony circuits settings parameter seeds emptyTop .top
        let some top := TreeOutput.topTree output | pure none
        Prod.fst <$> dealerCeremony circuits settings parameter seeds top (.bottom b)) _))}[r.1 = none]).toReal ≤ searchFailure

/-- `Coin` securely computes `F_coin` with selective abort in the `F_rand`-hybrid model, perfectly
(GS20, Lemma 3). The simulator makes no oracle call of its own. -/
def CoinSecurityStatement [SampleableType E] : Prop :=
  SecurelyComputes prims (coinProtocol K) coinRounds (Frand E) Fcoin SameCount 0 fun _ => 0

/-- An honest `Coin` gives the output of `F_coin`. -/
def CoinCompletenessStatement [SampleableType E] : Prop :=
  Completes prims (coinProtocol K) coinRounds (Frand E) (randReply E) Fcoin (fun _ => Finset.univ) SameCount 0

/-- `MulRep` and `Reshare` in each mode securely compute `F_mult` up to an additive attack in the
`F_rand`-hybrid model, perfectly (GS20, Lemma 4). The simulator makes no oracle call of its own. -/
def MultSecurityStatement : Prop :=
  ∀ mode : ReshareMode,
    SecurelyComputes prims (multProtocol K mode) (multRounds mode) (Frand Bit) (FmultBit K mode)
      (fun D x => SameCount D fun i => (x i).2.2) 0 fun _ => 0

/-- `MulRep` or `MulSh` and `Reshare` securely compute `F_extendMult` up to an additive attack in the
`F_rand`-hybrid model, perfectly (GS20, Lemma 5). The simulator makes no oracle call of its own. -/
def ExtendMultSecurityStatement [SampleableType E] : Prop :=
  SecurelyComputes prims (extendMultProtocol K) extendMultRounds (Frand E) (FextendMult K) (ShamirInputs K) 0 fun _ => 0

/-- The check with its salted digests securely computes `F_multVerify` with selective abort in the
`{F_coin, F_extendMult, F_rand}`-hybrid model (GS20, Lemmas 8 to 11, and CGH+18, Protocol 3.3). The
error is the soundness of the check and the birthday bound of the counted calls and the honest
points, namely the history and the digest of each term at each operator and the `R + 2` coin keys. -/
def MultVerifySecurityStatement [SampleableType E] : Prop :=
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
def MainSecurityStatement : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit),
    SecurelyComputes prims (mainProtocol K mode jobs) (mainRounds jobs) (mainFunctionalities K mode) (Fmain jobs)
      (MainInputs jobs) (termHashes C) (copyHashError C)

/-- An honest batch gives the outputs of `F_main`. -/
def MainCompletenessStatement : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit),
    Completes prims (mainProtocol K mode jobs) (mainRounds jobs) (mainFunctionalities K mode) mainReply
      (Fmain jobs) (fun _ => Finset.univ) (MainInputs jobs) 0

end ThresholdLeanXmss
