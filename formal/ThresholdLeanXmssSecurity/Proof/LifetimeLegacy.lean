import ThresholdLeanXmss.Statement

/-!
# The lifetime definitions with a sampled `Th`

`Statement.lean` states the lifetime claim for one fixed `Th` (option O3). The lifetime proofs that
were written before that change use the earlier forms, in which `Th` is uniform on the inputs that
the MPC evaluates. This file keeps those forms under new names, with their earlier text. A lemma
that holds for each `values` here holds for the fixed `Th` by `values := fun x => prims.Th x.1`,
because `lifetimeWorld` reads `Th` only on those inputs.
-/

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ThresholdLeanXmss

section World

variable {C : Committee} (prims : Primitives)

/-- A lifetime with a uniform `Th` on the inputs that the MPC evaluates, with its number of calls of
`H` and `PRG`. -/
def lifetimeRunSampled (aes : Aes) (game : (HashInput → HashOutput) → OracleComp (WorldSpec C) Bool) :
    ProbComp (Bool × ℕ) := do
  let values ← $ᵗ (MpcDomain → HashOutput)
  (simulateQ (lifetimeWorld ⟨thOf values, aes⟩) (game (thOf values))).run.run' ∅

end World

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The circuits of every `Th` have AND layers of the same lengths and the same number of outputs. So
the rounds and the errors of a ceremony do not depend on `Th`. -/
def FixedShape (circuitsOf : (HashInput → HashOutput) → Circuits) : Prop :=
  ∀ Th Th' parameter kind,
    (circuitsOf Th parameter kind).layers.map List.length = (circuitsOf Th' parameter kind).layers.map List.length ∧
      (circuitsOf Th parameter kind).outputs.length = (circuitsOf Th' parameter kind).outputs.length

section Lifetime

variable (attempts : ℕ)

/-- The reduction of run `n` of the lifetime to `hiddenStreams`. It samples `Th` and runs
`prgReduction` on the lifetime with `lifetimeHybridRoles D n`. Only the honest streams of run `n`
reach the PRF oracle, because the keygen and the signing call no `PRG`. -/
def lifetimeRunReductionSampled (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits) (D : C.Coalition)
    (A : LifetimeAdversary C E) (n : ℕ) : PRFScheme.PRFAdversary ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) Bit :=
  (do
    let values ← liftComp ($ᵗ (MpcDomain → HashOutput)) (StreamSpec C)
    prgReduction ⟨thOf values, aes⟩ D ((fun r => r.1.1) <$>
      ((lifetimeGameWith K (circuitsOf (thOf values)) settings attempts (lifetimeHybridRoles D n)
        (lifetimeHybridRoles D n n) D A).run ∅).run) :
    OracleComp (StreamSpec C) Bool)

/-- Every lifetime makes at most `Q` calls of `H` and `PRG`, by every party, cache hits included. The
bound holds for every `Th` of `lifetimeRunSampled` and for every answer of the oracles (BR93,
`IsQueryBoundP` of VCVio), so also on runs that the real lifetime never reaches. It bounds the paths
of the lifetime game. Unlike `IsQueryBounded`, it does not bound an adversary state that no answer
reaches. -/
def HasLifetimeQueryBoundAll (circuitsOf : (HashInput → HashOutput) → Circuits) (D : C.Coalition)
    (A : LifetimeAdversary C E) (Q : ℕ) : Prop :=
  ∀ values : MpcDomain → HashOutput,
    IsQueryBoundP (lifetimeGame K (circuitsOf (thOf values)) settings attempts D A) LifetimeCounted Q

/-- The probability that the lifetime adversary forges. -/
def lifetimeAdvantageSampled (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits) (D : C.Coalition)
    (A : LifetimeAdversary C E) : ℝ :=
  (Pr[fun r => r.1 = true | lifetimeRunSampled aes fun Th => lifetimeGame K (circuitsOf Th) settings attempts D A]).toReal

/-- The lifetime claim with a uniform `Th`, as stated before option O3. Its proofs carry over to the
fixed `Th` of `LifetimeSecurityStatement` pointwise.

* The keygen runs once on the real network. The adversary gets the public parameter. It gets the
  public key and the top tree of the first honest operator once that operator holds them. It runs
  each ceremony at most `attempts` times, one at a time, and sends signing requests between the
  rounds. No ceremony of a bottom tree runs after the first signing request on it. An honest
  operator answers a signing request only with its own ceremony output of the tree, and it signs at
  most one message for each key.
* `Th` is uniform on the inputs that the MPC evaluates. `circuitsOf Th` computes it, with AND layers
  of the same lengths and the same number of outputs for every `Th`.
* `Q` bounds the calls of `H` and `PRG` by every party, on every path of the lifetime game.
* The keygen term and each ceremony term take the budget `(fuel + 2) Q` with the fuel of the phase.
  One step of the phase adversary holds all that the lifetime adversary does between two rounds.
* `keygenHashError` pays the keygen. Each run of each ceremony pays its check, its birthday bound
  and its stream keys, after the `q₀ = Q + lifetimeOverhead` calls of the earlier phases.
* Each run also pays `seedHitError` for a call on a hidden key of an honest term or pair. The
  emulated signing keeps the masks of the honest pairs in its own table.
* Each run pays the PRF advantage of its own reduction. Each bottom tree pays one failed search,
  because each retry gives the same search.
* The last three terms are the bound of `SigningSecurityStatement` at `q₀`, for a forger that
  emulates the lifetime in the signing game. -/
def LifetimeSecurityStatementSampled (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits) : Prop :=
  (∀ Th, CircuitsCompute (circuitsOf Th) Th) → FixedShape circuitsOf → 0 < settings.batchSize →
    ∀ (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ),
      HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
      let circuits := circuitsOf fun _ => 0
      let q₀ := Q + lifetimeOverhead C attempts Q
      let q := (ceremonyFuel circuits settings + 2) * Q
      let runError := fun tree => (attempts : ℝ) * (treeCheckError (E := E) circuits settings tree (q₀ + q) +
        treeHashError circuits settings C tree (q₀ + q) + streamKeyError C + seedHitError C (q₀ + q))
      lifetimeAdvantageSampled K settings attempts aes circuitsOf D A ≤
        keygenHashError C ((setupRounds + 2) * Q) +
          (runError .top + ∑ b : Fin (2 ^ layerHeight), runError (.bottom b)) +
          ∑ n : Fin (lifetimeRuns attempts),
            PRFScheme.prfAdvantage (hiddenStreams aes) (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) +
          2 ^ layerHeight * searchFailure + signingHashError q₀ + seedHitError C q₀ + seedCollisionError C

end Lifetime

end ThresholdLeanXmss
