import ThresholdLeanXmssSecurity.Proof.SigningLedgerExpect
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Clean

/-!
# The compiler run with a ledger of charged calls

`ownRun` is `compilerRunO1` over `SigningLedgerExpect.ledgerHybrid` with the ghost `OwnGhost`.

* `ownCharged` charges two kinds of backend calls. A call of the first kind carries a candidate at a
  key with no revealed secret, so it is each call that can raise the cap flag. A call of the second
  kind is a fresh message digest call that the lane 2 key decodes, on a backend that is not stale
  and has no second opening.
* `ownAux` adds the charge to the ledger, and it raises `dirty` after a call from a backend with a
  second opening.
* `ownRun_proj` states that the run without the ghost is `compilerRunO1`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningOwnLedger

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerO1Coupling
open SigningCompilerCouplingProof SigningCompilerO1Release
open SigningLedgerExpect SigningCompilerO1Clean

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The ghost state of the compiler run. `ledger` counts the charged calls. `dirty` is up after a
call from a backend with a second opening. -/
structure OwnGhost where
  ledger : ℕ
  dirty : Bool

/-- The own count. A backend call is charged in two cases. It is a hash call that carries a
candidate at a key with no revealed secret. Or it is a fresh message digest call that the lane 2
key decodes, in a backend that is not stale and has no second opening. -/
def ownCharged (P : PublicParameter) (seeds : C.Term → HashOutput) (t : DeferredQuery C)
    (st : (CompilerBackend C × ℕ) × (HiddenKey → Option Digest)) (g : OwnGhost) : Prop :=
  ∃ input, t = .hash (.hash input) ∧
    ((∃ c, hiddenCandidate P input = some c ∧ st.2 c.1 = none) ∨
      (IsMsg input ∧ (XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey P).parameter input).isSome ∧
        st.1.1.data.cache (.hash input) = none ∧ st.1.1.trace.2 = false ∧ g.dirty = false ∧
        ¬SecondOpening P seeds st.1.1.data))

/-- The ghost after a backend call. -/
def ownAux (P : PublicParameter) (seeds : C.Term → HashOutput) (t : DeferredQuery C)
    (st : (CompilerBackend C × ℕ) × (HiddenKey → Option Digest)) (g : OwnGhost) : OwnGhost :=
  ⟨g.ledger + if ownCharged P seeds t st g then 1 else 0,
    g.dirty || decide (SecondOpening P seeds st.1.1.data)⟩

/-- The capped hybrid of `compilerRunO1` with the ledger. -/
abbrev ownHybrid (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ)
    (s : HiddenKey → Digest) :=
  ledgerHybrid (countImpl (compilerImpl P seeds) deferredCounted) (cappedCall deferredCounted Q)
    (deferredInputSide P) (deferredKey P) (deferredPoint P) (ownAux P seeds) s

/-- The start of the compiler run with the ledger. -/
def ownInit : CappedCompilerState C × OwnGhost :=
  (((compilerInit, 0), fun _ => none, false), ⟨0, false⟩)

/-- The compiler run with the ledger. -/
def ownRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (Q : ℕ) :
    ProbComp (CompilerOutcomeO1 C × OwnGhost) := do
  let s ← $ᵗ (HiddenKey → Digest)
  (fun r => ((r.1, r.2.1), r.2.2)) <$>
    (simulateQ (ownHybrid x.1 x.2.1 Q s) (sourceProgramO1 prims A x)).run ownInit

attribute [local irreducible] sourceProgramO1 in
set_option maxRecDepth 100000 in
/-- Without the ledger, the run is `compilerRunO1`. -/
theorem ownRun_proj (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (Q : ℕ) :
    Prod.fst <$> ownRun prims A x Q = compilerRunO1 prims A x Q := by
  have h : ∀ s : HiddenKey → Digest,
      Prod.map id Prod.fst <$>
          (simulateQ (ownHybrid x.1 x.2.1 Q s) (sourceProgramO1 prims A x)).run ownInit =
        (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
          (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) Q s)
          (sourceProgramO1 prims A x)).run ((compilerInit, 0), fun _ => none, false) :=
    fun s => OracleComp.extendState_run_proj_eq _ _ _ _ _
  unfold ownRun compilerRunO1
  rw [map_bind]
  refine bind_congr fun s => ?_
  rw [Functor.map_map, ← h s]
  rfl

end SigningOwnLedger

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnLedger.ownRun_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnLedger.ownRun_proj
