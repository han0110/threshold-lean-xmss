import ThresholdLeanXmssSecurity.Base.DkgClaims
import ThresholdLeanXmssSecurity.Base.Reductions

/-!
# The simulators of the setups

The explicit simulators of the seed generation and of the PRSS setup, the streams of one call under
the keys that the coalition knows, and the security claims of the two setups with their simulators.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

section Simulators

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The state of an explicit simulator. It keeps the log of every observed call of the adversary
from its start, and the inputs of the corrupt operators. -/
structure SimulatorState (C : Committee) (I σ : Type) where
  adversary : σ
  log : CallLog C
  corrupt : C.Party → Option I

/-- The simulator of a setup of `phase`. It runs `A` with emulated honest operators on the free copy
and observes every `H` call of `A`. After the commit round, it extracts the corrupt reveals from all
observed calls, as in the proof of CDG+18, Theorem 6 (Section 5.3). Then it programs `H` so that the
term keys and the pair keys of the corrupt operators are those of the dealer. This programming is an
adaptation of this project. The seed generation also programs `P`. The receivers are the emulated
honest operators that do not abort (GL05). `setup` is the setup of one emulated operator, and `dealt`
reads the parameter and the corrupt keys from the leak of the dealer. In the seed generation the
parameter is `P`. In the PRSS setup the leak has no `P`, and `dealt` gives the parameter `0`. -/
def setupSimulator (phase : Phase) {O L : Type} (setup : C.Party → Parts C → PartyM C E RealSpec O)
    (dealt : L → PublicParameter × (C.Party → Option (PrssKeys C)))
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit L (Finset C.Party) A.State where
  State := SimulatorState C Unit A.State
  start corrupt z := do
    let (state, log) ← observe (A.start corrupt z)
    pure ⟨state, log, corrupt⟩
  answer st := fun l => do
    let (parameter, corrupt) := dealt l
    let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
    let steps ← startSteps worldRoles D fun i => setup i (parts i)
    let ((state, steps, sent), calls) ← (stepRound observedRoles D A noFunctionality st.adversary steps).run
    let log := st.log ++ calls
    let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
    let view := fun (i j : C.Party) =>
      if j ∈ D.1 then readReveal phase (extractReveal phase log sent j i) i j else parts j
    let _ ← (if phase = .seedGen then do
        let high ← free (liftComp ($ᵗ HashOutput) _)
        program (.derive phase .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
          (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
      else pure true)
    let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j =>
        let i := firstHonest (C.holders T)
        program (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun k => (view i k).term T))
          (((corrupt j).map (·.term T)).getD 0)
      | none => pure true
    let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        program (.derive phase .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((corrupt j).map (·.pair i)).getD 0)
      else pure true
    let ((state, keys), rest) ← (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state steps).run
    pure (⟨state, log ++ rest, st.corrupt⟩, Finset.univ.filter fun i => (keys i).isSome)
  output st := pure st.adversary

/-- The simulator of the seed generation. It programs `P`, the corrupt seeds and the corrupt pair
keys of `F_seedGen`. -/
def seedGenSimulator (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) A.State :=
  setupSimulator .seedGen seedGenWith (fun l => (l.1, fun j => (l.2 j).map fun k => ⟨k.seed, k.pairKey⟩)) D A

/-- The simulator of the PRSS setup. It programs the corrupt term keys and pair keys of
`F_prssKeys`, and no `P`. -/
def prssSetupSimulator (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    Simulator (C := C) (WorldSpec C) Unit (C.Party → Option (PrssKeys C)) (Finset C.Party) A.State :=
  setupSimulator .prss prssSetupWith (fun corrupt => (0, corrupt)) D A

/-- The streams of one call under the keys that the coalition knows and an honest receiver holds, at
the `count` positions. The terms have a corrupt holder and a holder that is an honest receiver.
Pair stream `(j, i)` is the stream of a corrupt operator `j` and an honest receiver `i`. -/
def knownStreams {R : Type} [Zero R] (D : C.Coalition) (receivers : Finset C.Party) (codec : Codec C E R)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (Shares C R × (C.Party → C.Party → ℕ → R)) := do
  let r ← C.terms.mapM fun T =>
    if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
      codec.draw (.term T) (term T) ρ idx count
    else pure fun _ => 0
  let Z ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
      let p := C.pairOf i j (fun e => h.2.1 (e ▸ h.1))
      codec.draw (.pair p) (pair p) ρ idx count
    else pure fun _ => 0
  pure (fun T g => if g < count then (r.getD (C.terms.idxOf T) fun _ => 0) g else 0,
    fun j i g => if g < count then ((Z.getD j.val []).getD i.val fun _ => 0) g else 0)

end Simulators

section Claims

variable {C : Committee} {E : Type} (prims : Primitives)

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

end Claims

section SetupClaims

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives)

/-- The programming queries of `seedGenSimulator`, one for `P`, at most one for each term and one for
each pair of a corrupt and an honest operator. -/
def seedGenOverhead (C : Committee) : ℕ := 1 + termCount C + C.n ^ 2

/-- The programming queries of `prssSetupSimulator`, at most one for each term and one for each pair
of a corrupt and an honest operator. -/
def prssSetupOverhead (C : Committee) : ℕ := termCount C + C.n ^ 2

/-- The seed generation securely computes `F_seedGen` with selective abort against a static coalition, with the
simulator `seedGenSimulator`. GL05 gives the notion and CDG+18 gives the observation, the extraction
and the programming, but the setup argument and its bound are an adaptation of this project. -/
def SeedGenSecurityStatement (C : Committee) (E : Type) : Prop :=
  SimulatedBy prims (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) setupRounds FseedGen
    (fun _ _ => True) seedGenSimulator (seedGenOverhead C) fun _ _ _ _ _ q => seedGenHashError C q

/-- The PRSS setup of a ceremony securely computes `F_prssKeys` with selective abort against a static
coalition, on the real network, with the simulator `prssSetupSimulator`. The error is
`(q + prssSetupSecrets C)² / 2^256`. GL05 gives the notion and CDG+18 gives the observation, the
extraction and the programming, but the setup argument and its bound are an adaptation of this project.

* It has the form of `SeedGenSecurityStatement`. The PRSS setup is the seed generation protocol with
  the phase `.prss`. `sampleParts` samples the field `parameter` in both phases. The PRSS setup does
  not reveal this field, derives no `P` from it and does not hash it in the echo.
* The claim is for one setup from the empty hash cache. A bottom tree runs two setups
  (`new_bottom_tree` of `src/dkg.rs`), and the second starts from a cache with `.prss` cells of the
  first. This claim does not cover the second setup. -/
def PrssSetupSecurityStatement (C : Committee) (E : Type) : Prop :=
  SimulatedBy prims (fun i (_ : Unit) => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) setupRounds FprssKeys
    (fun _ _ => True) prssSetupSimulator (prssSetupOverhead C) fun _ _ _ _ _ q => prssSetupHashError C q

end SetupClaims

end ThresholdLeanXmss
