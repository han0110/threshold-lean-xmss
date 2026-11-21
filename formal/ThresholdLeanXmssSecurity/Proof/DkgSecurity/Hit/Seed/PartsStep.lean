import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Touch
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.RestEmu

/-!
# The split of `PartsStep` into a commit side and a derive side

`PartsStep` compares the run on the parts of a hidden term `T` shifted by `δ` with the reference run
`partsRef`. Let `X` be the hidden cell of `T` on the shifted parts. The two runs differ in two ways.

* The commitments between honest operators. The shifted run asks them in the shared cache at the
  commit addresses of the shifted parts. The reference run asks them in a private cache at the commit
  addresses of the unshifted parts.
* The derivations of `T`. The shifted run asks `X` in the shared cache. The reference run asks
  `markCell` in the private cache.

`pairRun` is the middle run. It has the private commitments of the reference run and the derive calls
of the shifted run. `CommitSide` bounds the shifted run by `pairRun`. `DeriveSide` bounds `pairRun` by
the reference run. `partsStep_of_sides` gives `PartsStep` from the two statements.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal (seedGenAt commitAddress termAddress
  seedGenRest_eq_normal partsShift)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The middle world -/

section World

variable (prims : Primitives) (D : C.Coalition)

/-- A commitment cell of the seed generation between two honest operators. -/
def PairCell (q : Query C) : Prop :=
  ∃ (i j : C.Party) (r : List HashOutput), i ∉ D.1 ∧ j ∉ D.1 ∧ q = .commit .seedGen i j r

/-- The state of `pairWorld`, namely the state of `loggedWorld`, the private cache and the flag. -/
abbrev PairState (C : Committee) := LogState C × HashCache C × Bool

/-- `flagAt X` where a free call of `H` at a commitment cell between two honest operators takes its
answer from the private cache and leaves the world as it is. -/
def pairWorld (X : Query C) : QueryImpl (WorldSpec C) (StateT (PairState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      if PairCell D q then StateT.mk fun s =>
        (fun r => (r.1, (s.1, r.2, s.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s.2.1
      else StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$>
        (loggedWorld prims D (.inr (.inr (.inl q)))).run s.1
  | t => StateT.mk fun s =>
      (fun r => (r.1, (r.2, s.2.1, s.2.2 || decide (TouchAt X t)))) <$> (loggedWorld prims D t).run s.1

end World

/-! ## The three runs -/

section Runs

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The parts with the term part of `T` shifted by `δ` at the holders of `T`. -/
abbrev shiftBy (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput) : (C.Party → Parts C) → C.Party → Parts C :=
  shiftAll T (extendShift T δ)

/-- The run on the shifted parts in the form of `suffixAt`. The suffix asks the commit addresses and
the derive addresses of the shifted parts, in `flagAt` of the shifted hidden cell. -/
def shiftRun (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput) :
    ProbComp Bool := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let z ← (simulateQ (flagAt prims D (hiddenInput (shiftBy T δ x.1.2.2) T))
    (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1 (commitAddress (shiftBy T δ x.1.2.2))
      (termAddress D (shiftBy T δ x.1.2.2)))).run
      (x.2, (x.2.1.1 (hiddenInput (shiftBy T δ x.1.2.2) T)).isSome)
  pure z.2.2

/-- The middle run. The suffix asks the commit addresses of the unshifted parts and the derive
addresses of the shifted parts, in `pairWorld` of the shifted hidden cell. -/
def pairRun (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput) :
    ProbComp Bool := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let z ← (simulateQ (pairWorld prims D (hiddenInput (shiftBy T δ x.1.2.2) T))
    (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1 (commitAddress x.1.2.2)
      (termAddress D (shiftBy T δ x.1.2.2)))).run
      (x.2, ∅, (x.2.1.1 (hiddenInput (shiftBy T δ x.1.2.2) T)).isSome)
  pure z.2.2.2

/-- The commit side. For a term `T` with no corrupt holder and each shift `δ` of its holders, the touch
at the shifted hidden cell in the run on the shifted parts has at most the probability of the touch in
the middle run. The two runs differ only in the commitments between honest operators. The shifted run
asks them in the shared cache at the addresses of the shifted parts, and the middle run asks them in
the private cache at the addresses of the unshifted parts. Such an answer goes only into the test of the
receiver, which asks the same cell. The bound is a mean over the run from the empty start. -/
def CommitSide : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput),
    ¬ KnownTo D.1 T →
    Pr{let b ← shiftRun prims K circuits settings runLimit D A T δ}[b = true] ≤
      Pr{let b ← pairRun prims K circuits settings runLimit D A T δ}[b = true]

/-- The derive side. For a term `T` with no corrupt holder and each shift `δ` of its holders, the touch
at the shifted hidden cell in the middle run has at most the probability that the reference run names
`δ`. The two runs differ only in the derivations of `T`, which ask the shifted hidden cell in the shared
cache in the middle run and `markCell` in the private cache in the reference run. The bound is a mean
over the run from the empty start. -/
def DeriveSide : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput),
    ¬ KnownTo D.1 T →
    Pr{let b ← pairRun prims K circuits settings runLimit D A T δ}[b = true] ≤
      Pr{let r ← partsRef prims K circuits settings runLimit D A T}[δ ∈ partsNamed T r.1 r.2.2]

omit [Fintype E] [DecidableEq E] in
/-- The suffix on the shifted parts is `suffixAt` on the unshifted parts with the commit addresses and
the derive addresses of the shifted parts. -/
theorem dealtSuffix_shift (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) (T : C.Term)
    (c : C.Party → HashOutput) (hT : ¬ KnownTo D.1 T) :
    dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (mapParts (shiftAll T c) x) =
      suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress (shiftAll T c x.2.2))
        (termAddress D (shiftAll T c x.2.2)) := by
  unfold dealtSuffix suffixAt mapParts
  rw [seedGenRest_eq_normal, partsShift D A.net x.1.1 x.1.2 x.2.1.1 x.2.1.2.2 x.2.2 T c hT]

omit [Fintype E] [DecidableEq E] in
theorem touchRunWith_eq_shiftRun (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term)
    (δ : {k // k ∈ C.holders T} → HashOutput) (hT : ¬ KnownTo D.1 T) :
    touchRunWith prims K circuits settings runLimit D A T (shiftBy T δ) =
      shiftRun prims K circuits settings runLimit D A T δ := by
  unfold touchRunWith shiftRun
  refine bind_congr fun x => ?_
  rw [dealtSuffix_shift K circuits settings runLimit D A x.1 T _ hT]

omit [Fintype E] [DecidableEq E] in
/-- `CommitSide` and `DeriveSide` give `PartsStep`. -/
theorem partsStep_of_sides (commit : CommitSide prims K circuits settings runLimit)
    (derive : DeriveSide prims K circuits settings runLimit) : PartsStep prims K circuits settings runLimit := by
  intro D A T δ hT
  rw [touchRunWith_eq_shiftRun prims K circuits settings runLimit D A T δ hT]
  exact (commit D A T δ hT).trans (derive D A T δ hT)

end Runs

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsStep_of_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsStep_of_sides
