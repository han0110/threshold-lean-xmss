import ThresholdLeanXmss.Statement.DkgReduction

/-!
# The observed adversary

The log of the `H` calls of the adversary and the programming query of a simulator. The
execution lemmas of the proofs use them.
-/

set_option autoImplicit false

open OracleComp OracleSpec  HashSig LeanXmss

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A step of the adversary on the counted copy, with the log of its `H` calls. The simulator reads
each call of `A`, as with the local random oracle of CDG+18, Section 3 and Fig. 2(a). It is not the
`Observe` query of CDG+18, Fig. 10, which gives only the illegitimate calls to a global oracle. -/
def observe {α : Type} (oa : OracleComp (LocalSpec C) α) : OracleComp (WorldSpec C) (α × CallLog C) :=
  let impl : QueryImpl (LocalSpec C) (WriterT (CallLog C) (OracleComp (WorldSpec C))) := fun t =>
    match t with
    | .inr (.inl q) => do
        let y ← liftM (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C)))
        tell [(q, y)]
        pure y
    | t => liftM (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  (simulateQ impl oa).run

/-- The adversary under observation and the emulated honest operators on the free copy. -/
def observedRoles : Roles C (WriterT (CallLog C) (OracleComp (WorldSpec C))) :=
  ⟨fun oa => WriterT.mk (observe oa), fun oa => liftM (free oa)⟩

/-- A programming query on the counted copy. -/
def program (q : Query C) (value : HashOutput) : OracleComp (WorldSpec C) Bool :=
  counted (OracleComp.lift (OracleSpec.query (spec := SimulatorSpec C) (.inr (q, value))))

end ThresholdLeanXmss
