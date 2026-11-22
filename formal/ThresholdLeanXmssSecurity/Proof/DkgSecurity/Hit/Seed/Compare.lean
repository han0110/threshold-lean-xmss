import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CellHit
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CompareErrors

/-!
# The comparison game with one independent seed for each hidden term

`dealtPartsRun` is the prefix `dealtPrefix` (the start, the keys of the dealer and the parts) and then
the suffix `dealtSuffix` (the rest of the seed generation and the rest of the game), by
`dealtPartsRun_split`.

`compWorld parts seed` is `loggedWorld` with one change. A free call of `H` at the derive input
`hiddenInput parts T` of a hidden term `T` gives the independent seed `seed T` and changes no state.
A counted call and a programming call at that cell go to `loggedWorld`. `compRun` runs the prefix in
`loggedWorld`, draws `seed` uniformly, and runs the suffix in `compWorld`. `CompHitOf` states that a
counted call asks a PRF cell under the seed of a hidden term.

The two statements of the comparison are `SeedClose` and `CompHit`.

* `SeedClose` states that the game with the keys of the dealer gives `CellHitOf` at most with the
  probability of `CompHitOf` in the comparison game and `compCloseError`. The two games differ only
  when the cell of a hidden derive input has a value that no honest free call gave. That is a counted
  call that names the vector of the `t` honest parts, or a programming call or a pre-set value at that
  cell (an alias).
* `CompHit` bounds `CompHitOf` by `compHitError`. A counted call names an independent seed, or the
  comparison of the echo hashes of a pair of honest holders shows a collision.

`hitSeed_of_compare` states that the two statements give `HitSeed`, with the empty log at `q = 0`,
the trivial case of a bound of at least one, and `errors_le`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The prefix and the suffix -/

/-- The result of the prefix, namely the state and the log of the start, the parameter, the seeds and
the keys of the dealer, and the parts of the emulated operators. -/
abbrev PrefixOut (C : Committee) (σ : Type) :=
  (σ × CallLog C) × (PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) × (C.Party → Parts C)

/-- The result of `dealtRun`. -/
abbrev RunOut (C : Committee) :=
  Bool × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C))

/-- The start, the keys of the dealer and the parts. -/
def dealtPrefix (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) (PrefixOut C A.net.State) := do
  let a ← observe (A.net.start (corruptInputs D fun _ => ()) [])
  let b ← free (liftComp (prawnsKeyGen (C := C)) _)
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
  pure (a, b, parts)

/-- The rest of the seed generation and the rest of the game after the prefix `x`. -/
def dealtSuffix (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) :
    OracleComp (WorldSpec C) (RunOut C) := do
  let (state, emu) ← seedGenRest D A.net x.1.1 x.1.2 x.2.1.1 x.2.1.2.2 x.2.2
  let keys := fun i => (emu i).map fun _ => x.2.1.2.2 i
  let win ← (secRest K circuits settings runLimit m D A x.2.1.1 x.2.1.2.1 x.2.1.2.2 emu).run' (startState D state keys)
  pure (win, x.2.1.1, x.2.1.2.1, x.2.1.2.2, emu)

omit [Fintype E] [DecidableEq E] in
theorem dealtPartsRun_split (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    dealtPartsRun K circuits settings runLimit m D A = (do
      let x ← dealtPrefix D A
      let y ← dealtSuffix K circuits settings runLimit m D A x
      pure (x.2.2, y)) := by
  unfold dealtPartsRun dealtPrefix dealtSuffix
  simp only [bind_assoc, pure_bind]

/-! ## The comparison game -/

/-- The hidden term whose derive input on the parts `parts` is `q`, if one exists. -/
def hiddenTermOf (D : C.Coalition) (parts : C.Party → Parts C) (q : Query C) : Option C.Term :=
  if h : ∃ T, ¬ KnownTo D.1 T ∧ q = hiddenInput parts T then some (Classical.choose h) else none

/-- `loggedWorld` where a free call of `H` at the derive input of a hidden term `T` gives `seed T`
and changes no state. -/
def compWorld (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) :
    QueryImpl (WorldSpec C) (StateT (LogState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      match hiddenTermOf D parts q with
      | some T => (pure (seed T) : StateT (LogState C) ProbComp HashOutput)
      | none => loggedWorld prims D (.inr (.inr (.inl q)))
  | t => loggedWorld prims D t

/-- The comparison game. The prefix runs in `loggedWorld`, the seeds of the hidden terms are drawn
uniformly, and the suffix runs in `compWorld`. -/
def compRun (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ProbComp ((C.Party → Parts C) × (C.Term → HashOutput) × (RunOut C × LogState C)) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let seed ← $ᵗ (C.Term → HashOutput)
  let z ← (simulateQ (compWorld prims D x.1.2.2 seed)
    (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1)).run x.2
  pure (x.1.2.2, seed, z)

/-- A counted call asks a PRF cell under the independent seed of a hidden term. -/
def CompHitOf (D : C.Coalition) (r : (C.Party → Parts C) × (C.Term → HashOutput) × (RunOut C × LogState C)) :
    Prop :=
  ∃ q ∈ r.2.2.2.2, ∃ (T : C.Term) (x : Point), ¬ KnownTo D.1 T ∧ q = .prf (r.2.1 T) x

/-- The step from the game with the keys of the dealer to the comparison game. -/
def SeedClose : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    (Pr{let z ← (simulateQ (loggedWorld prims D)
      (dealtPartsRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[CellHitOf D z]).toReal ≤
      (Pr{let r ← compRun prims K circuits settings runLimit D A}[CompHitOf D r]).toReal + compCloseError C q

/-- The hit in the comparison game. -/
def CompHit : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    (Pr{let r ← compRun prims K circuits settings runLimit D A}[CompHitOf D r]).toReal ≤ compHitError C q

/-! ## The glue -/

omit [Fintype E] [DecidableEq E] in
/-- The two statements of the comparison give `CellHit`. -/
theorem cellHit_of_compare (close : SeedClose prims K circuits settings runLimit)
    (hit : CompHit prims K circuits settings runLimit) : CellHit prims K circuits settings runLimit := by
  intro D A q bounded
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hlog : IsQueryBoundP (dealtPartsRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A) Logged 0 := by
      have h := LoggedCount.logged_dealtRun K circuits settings runLimit D ⟨true, fun _ => 0⟩ (fun _ => rfl) A 0 bounded
      rw [← snd_dealtPartsRun] at h
      exact (isQueryBoundP_map_iff _ _ _).1 h
    have h0 : Pr{let z ← (simulateQ (loggedWorld prims D)
        (dealtPartsRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[CellHitOf D z] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨q, hq, _⟩ => by
        have hl := log_length_le prims D _ 0 hlog _ z hz
        simp only [List.length_nil, Nat.add_zero, Nat.le_zero, List.length_eq_zero_iff] at hl
        rw [hl] at hq
        exact List.not_mem_nil hq
    rw [h0]
    simp [hitSeedError]
  · by_cases big : 1 ≤ hitSeedError C q
    · refine le_trans ?_ big
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
    · replace big := not_le.1 big
      have h1 := close D A q bounded
      have h2 := hit D A q bounded
      have h3 := errors_le C q hq big
      unfold hitSeedError
      linarith

omit [Fintype E] [DecidableEq E] in
/-- The two statements of the comparison give `HitSeed`. -/
theorem hitSeed_of_compare (close : SeedClose prims K circuits settings runLimit)
    (hit : CompHit prims K circuits settings runLimit) : HitSeed prims K circuits settings runLimit :=
  hitSeed_of_cellHit prims K circuits settings runLimit (cellHit_of_compare prims K circuits settings runLimit close hit)

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.hitSeed_of_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.hitSeed_of_compare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.dealtPartsRun_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.dealtPartsRun_split
