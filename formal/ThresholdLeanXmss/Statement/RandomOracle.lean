import ThresholdLeanXmss.Reductions

/-!
# The random-oracle model

Read this file first. It holds the oracles of the claims, the count of their calls and the run of a
game.

* The world has a counted copy and a free copy of the oracles, on one cache. The adversary and the
  distinguisher run on the counted copy. The honest operators and the functionalities run on the
  free copy, so they call `H` for free.
* The constructors of `Query` are disjoint domains of `H`, and a repeated query gets the same
  answer. This models domain-separated hashing (Bellare, Davis and Günther, EUROCRYPT 2020). The
  byte encoding of the implementation does not give this separation yet (`statement.tex`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-! ## The world of the seed generation and ceremony claims -/

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
def accepts (oa : OracleComp (WorldSpec C) Bool) : ℝ := (Pr{let r ← runWorld prims oa}[r.1 = true]).toReal

/-! ## The world of the signing claim -/

/-- The world of the signing claim. All of `H` is a lazy random oracle. Each call of `H` and of `PRG`
costs one query, on both copies, so the calls of every party count. Private sampling costs nothing. -/
def signingWorld : QueryImpl (WorldSpec C) (AddWriterT ℕ (StateT (HashCache C) ProbComp)) :=
  QueryImpl.withAddCost (signingLocalAnswer (C := C) prims + programAnswer (C := C) + signingLocalAnswer (C := C) prims :
      QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp))
    fun | .inl (.inl (.inl _)) => 0 | .inr (.inl _) => 0 | _ => 1

/-- Run a computation in the signing world from an empty cache, with its number of calls of `H` and
`PRG`. The signing claim reads only the output. The number is the budget of every party, which
`SigningBudgets.lean` uses. -/
def runSigningWorld {α : Type} (oa : OracleComp (WorldSpec C) α) : ProbComp (α × ℕ) :=
  (simulateQ (signingWorld prims) oa).run.run' ∅

/-- The probability that a computation outputs `true` in the signing world. -/
def signingAccepts (oa : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr{let r ← runSigningWorld prims oa}[r.1 = true]).toReal

/-! ## A query cost on every path -/

-- Ported from https://github.com/leanEthereum/leanVM/blob/f5f3672f2b72d3f89dbbaeff18a53a73c975d620/formal/Statement/RandomPermutation.lean
/-- `oa` makes queries of total cost at most `Q` on every path. Whatever the oracles answer, the
costs of the queries of `oa` add up to at most `Q`, where a query `t` costs `cost t`. The count is a
worst case and not an expected value. -/
def QueryCostAtMost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (oa : OracleComp spec α)
    (cost : ι → ℕ) (Q : ℕ) : Prop :=
  IsQueryBound oa Q (fun t b ↦ cost t ≤ b) (fun t b ↦ b - cost t)

end ThresholdLeanXmss
