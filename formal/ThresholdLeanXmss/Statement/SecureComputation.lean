import ThresholdLeanXmss.Statement.RandomOracle
import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# Secure computation

Read this file second. It holds the notions of the keygen, ceremony and gadget claims, namely
secure computation in the simulation framework of Canetti 2000, with the selective abort of GL05
and the hybrid model of GS20.

* A distinguisher with oracle access reads the joint output of the adversary and the honest
  operators. It tells the real execution from the ideal execution with a simulator at most with the
  error of the claim.
* With selective abort, the adversary names the honest operators that receive each output (GL05).
* The explicit simulators program `H` as the local programmable random oracle of CDG+18, which has
  no `IsProgrammed` query.
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
    QueryImpl.add ((fun (t : (LocalSpec C).Domain) =>
      (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) : StateT Sim.State _ _)) :
        QueryImpl (LocalSpec C) (StateT Sim.State (OracleComp (WorldSpec C))))
    ((fun (l : L) => (StateT.mk fun st => do
      let (st, r) ← lift (Sim.answer st l)
      pure (r, st) : StateT Sim.State (OracleComp (WorldSpec C)) R)) :
        QueryImpl (L →ₒ R) (StateT Sim.State (OracleComp (WorldSpec C))))
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
    letI : MeasurableSpace (C.Party → Option O) := ⊤
    measureTVDist ((fun r => r.1.2) <$> runWorld prims
        (realExecution noCoalition (honestAdversary replyH) Fh fuel program x []))
      ((fun r => r.1.2) <$> runWorld prims
        (idealExecution (fun oa => oa) noCoalition F (honestSimulator reply) x [])) ≤ ε

end ThresholdLeanXmss
