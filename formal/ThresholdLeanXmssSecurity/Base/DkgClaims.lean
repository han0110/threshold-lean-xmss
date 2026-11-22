import ThresholdLeanXmssSecurity.Base.Dkg
import ThresholdLeanXmss.Statement.Dkg
import VCVio.EvalDist.EvalDistEq

/-!
# The distinguisher, the valid inputs and the claims of the dealer

The distinguisher with its query bound, the valid inputs of a check and of a batch, and the claims
of the dealer of a tree.
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

end SecureComputation

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

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

/-- The inputs of a batch have one sharing for each job. The terms of a job have one width at each
honest holder and are empty elsewhere. Every holder of each term agrees on it, the corrupt holders
included, as the inputs of a ceremony come from the seeds that the seed generation echo compares. -/
def MainInputs (jobs : List Circuit) (D : C.Coalition) (x : C.Party → List (C.Term → List Bit)) : Prop :=
  ∃ widths : List ℕ, widths.length = jobs.length ∧
    (∀ i, i ∉ D.1 → (x i).length = jobs.length ∧ ∀ k < jobs.length, ∀ T,
      ((((x i)[k]?).getD fun _ => []) T).length = if i ∈ C.holders T then widths.getD k 0 else 0) ∧
    ∀ k : ℕ, Consistent noCoalition fun i T => (((x i)[k]?).getD fun _ => []) T

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
signature. -/
def DealerTreeSuccessStatement (C : Committee) : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)),
      (Pr{let r ← runWorld prims (free (C := C) (liftComp (do
        let (output, _) ← dealerCeremony circuits settings parameter seeds emptyTop .top
        let some top := TreeOutput.topTree output | pure none
        Prod.fst <$> dealerCeremony circuits settings parameter seeds top (.bottom b)) _))}[r.1 = none]).toReal ≤ searchFailure

end ThresholdLeanXmss
