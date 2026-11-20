import ThresholdLeanXmssSecurity.Base.RandomOracle

/-!
# The honest run of a functionality

The counted calls of a local computation, the ideal execution with a simulator, and the
completeness of an honest run in the statistical distance.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The calls of a local computation that the budget counts, namely the random-oracle inputs of `H`
and `PRG`. -/
def Counted : (LocalSpec C).Domain → Prop
  | .inr (.inl (.hash input)) => ¬ MpcInput input
  | .inr _ => True
  | .inl _ => False

/-- The ideal execution of `F` with the simulator `Sim`. The functionality runs on the free copy. -/
def idealExecution {κ : Type} {S : OracleSpec κ} {I O L R σ : Type}
    (lift : ∀ {β : Type}, OracleComp S β → OracleComp (WorldSpec C) β) (D : C.Coalition)
    (F : Functionality C I O L R) (Sim : Simulator (C := C) S I L R σ) (x : C.Party → I) (z : Aux) :
    OracleComp (WorldSpec C) (σ × (C.Party → Option O)) := do
  let state ← lift (Sim.start (corruptInputs D x) z)
  let impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT Sim.State (OracleComp (WorldSpec C))) :=
    QueryImpl.add ((fun (t : (LocalSpec C).Domain) =>
      (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) : StateT Sim.State _ _)) :
        QueryImpl (LocalSpec C) (StateT Sim.State (OracleComp (WorldSpec C))))
    ((fun (l : L) => (StateT.mk fun st => do
      let (st, r) ← lift (Sim.answer st l)
      pure (r, st) : StateT Sim.State (OracleComp (WorldSpec C)) R)) :
        QueryImpl (L →ₒ R) (StateT Sim.State (OracleComp (WorldSpec C))))
  let (outputs, state) ← (simulateQ impl (F.run D fun i => if i ∈ D.1 then none else some (x i))).run state
  pure (← lift (Sim.output state), outputs)

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
    letI : MeasurableSpace (C.Party → Option O) := ⊤
    measureTVDist ((fun r => r.1.2) <$> runWorld prims
        (realExecution noCoalition (honestAdversary replyH) Fh fuel program x []))
      ((fun r => r.1.2) <$> runWorld prims
        (idealExecution (fun oa => oa) noCoalition F (honestSimulator reply) x [])) ≤ ε

end ThresholdLeanXmss
