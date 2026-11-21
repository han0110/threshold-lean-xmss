import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Hops

/-!
# The four parts of the first hit

`SharedHit hit` bounds `HitOf` in the game with no emulated run. `HitOf` is the union of four events
(`hitOf_iff`), and `HitPart` bounds one event in that game.

* `HitSeedOf` says that a counted call asks a PRF cell under an emulated seed of a hidden term.
* `HitSaltOf` says that a counted call asks a digest cell under a salt of a hidden term.
* `ClashOf` is `SeedClash`.
* `MismatchOf` is `KeyMismatch`.

`HitSeed`, `HitSalt`, `HitClash` and `HitMismatch` are the four statements, each with its own bound.
`sharedHit_of_parts` gives `SharedHit hitError` from them, and `hitError_eq` states that `hitError` is
`privacyHitError`.

The bound of `HitSalt` counts the free calls too. An honest holder of a term with a corrupt holder
asks a digest cell under a salt that is an AES stream, on the free copy. Such a call under the salt of
a hidden term gives the digest that the coalition read before, so the coalition tests one value of
that salt with no counted call.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The four events -/

/-- A counted call asks a PRF cell under the seed that an emulated operator holds for a term with no
corrupt holder. -/
def HitSeedOf (D : C.Coalition) (r : DealtOut C × LogState C) : Prop :=
  ∃ q ∈ r.2.2, ∃ (i : C.Party) (keys : Keys C) (T : C.Term) (x : Point), i ∉ D.1 ∧ r.1.2.2.2.2 i = some keys ∧
    i ∈ C.holders T ∧ ¬ KnownTo D.1 T ∧ q = .prf (keys.seed T) x

/-- A counted call asks a digest cell under a salt of a term with no corrupt holder. The salts are
those of the hidden table at the end of the game, so the event has each call that came before the
draw of its salt. -/
def HitSaltOf (D : C.Coalition) (r : DealtOut C × LogState C) : Prop :=
  ∃ q ∈ r.2.2, ∃ (salt : List Bit) (history : HashOutput), salt ∈ hiddenSalts D r.2.1.2 ∧ q = .digest salt history

/-- An emulated seed of a term with no corrupt holder is a seed of the dealer. -/
def ClashOf (D : C.Coalition) (r : DealtOut C × LogState C) : Prop := SeedClash D r.1.2.2.1 r.1.2.2.2.2

/-- An emulated operator holds a known key that is not the key of the dealer. -/
def MismatchOf (D : C.Coalition) (r : DealtOut C × LogState C) : Prop :=
  KeyMismatch D r.1.2.1 r.1.2.2.2.1 r.1.2.2.2.2

/-- A first hit is one of the four events. -/
theorem hitOf_iff (D : C.Coalition) (r : DealtOut C × LogState C) :
    HitOf D r ↔ HitSeedOf D r ∨ HitSaltOf D r ∨ ClashOf D r ∨ MismatchOf D r := by
  unfold HitOf FirstHit HitSeedOf HitSaltOf ClashOf MismatchOf SensitiveCell
  constructor
  · rintro (⟨q, hq, h | h⟩ | h | h)
    · exact Or.inl ⟨q, hq, h⟩
    · exact Or.inr (Or.inl ⟨q, hq, h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩ | h | h)
    · exact Or.inl ⟨q, hq, Or.inl h⟩
    · exact Or.inl ⟨q, hq, Or.inr h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-! ## The four statements -/

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The bound `bound q` of the event `event` in the game with the keys of the dealer and no emulated
run, the game of `SharedHit`. -/
def HitPart (event : C.Coalition → DealtOut C × LogState C → Prop) (bound : ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    dealtProb prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (event D) ≤ bound q

/-- The bound of `HitSeedOf`. The game has at most `n * termCount C` emulated seeds of hidden terms. A
counted call names the derive input of one of them or names the seed, so a call counts two times. -/
def hitSeedError (C : Committee) (q : ℕ) : ℝ := ((2 * q * (C.n * termCount C) : ℕ) : ℝ) / 2 ^ 256

/-- The bound of `HitSaltOf`. In each check each honest operator asks one digest cell for each term
that it holds, on the free copy, so the game has at most `gameBatches * n * termCount C` such calls.
Each of them is under a new salt of a hidden term or under a salt of a term with a corrupt holder. A
salt of a hidden term shows only in the answer of its digest cell. So each other call of a digest
cell tests one value of that salt, namely each of the `q` counted calls and each free call of another
place. A pair of a salt and a test has the probability `2^-256`, for a test before the draw and for
a test after it. The bound is a mean. After a free call with the salt of a hidden term, one counted
call names that salt with the probability 1. -/
def hitSaltError (C : Committee) (q : ℕ) : ℝ :=
  (((q + gameBatches settings runLimit * C.n * termCount C) * (gameBatches settings runLimit * C.n * termCount C) : ℕ) :
    ℝ) / 2 ^ 256

/-- The bound of `ClashOf`. An emulated seed of a hidden term at an operator meets one of the
`termCount C` seeds of the dealer as two independent values, or its derive cell has the input of a
programming query of one of the at most `termCount C` known terms. -/
def hitClashError (C : Committee) : ℝ := ((2 * (C.n * termCount C ^ 2) : ℕ) : ℝ) / 2 ^ 256

/-- The bound of `MismatchOf`, the bound of `SetupKnownMismatch` for the seed generation. -/
def hitMismatchError (C : Committee) (q : ℕ) : ℝ := seedGenHashError C q / 2

/-- The bound of a first hit from its four parts. -/
def hitError (C : Committee) (q : ℕ) : ℝ :=
  hitSeedError C q + hitSaltError settings runLimit C q + hitClashError C + hitMismatchError C q

/-- The statement that bounds `HitSeedOf`. The emulated seed of a hidden term is the value of a
derive cell on parts of honest operators. The parts go to honest holders only, the commitments to
them go to honest receivers only, and the echo hash with the seed goes to an honest holder only. The
game has no emulated run, so no later step reads the seed. -/
def HitSeed : Prop := HitPart prims K circuits settings runLimit HitSeedOf (hitSeedError C)

/-- The statement that bounds `HitSaltOf`. A salt of a hidden term is 256 bits of the hidden table,
which only a free call of an honest holder reads. The holder uses the salt in one digest cell and
sends the digest. The tests of a salt are the counted calls of a digest cell and the free calls of a
digest cell from each other place, and with no test at the salt the view has no bit of the salt. -/
def HitSalt : Prop := HitPart prims K circuits settings runLimit HitSaltOf (hitSaltError settings runLimit C)

/-- The statement that bounds `ClashOf`. -/
def HitClash : Prop := HitPart prims K circuits settings runLimit ClashOf fun _ => hitClashError C

/-- The statement that bounds `MismatchOf`. -/
def HitMismatch : Prop := HitPart prims K circuits settings runLimit MismatchOf (hitMismatchError C)

omit [Fintype E] [DecidableEq E] in
/-- The four parts give the bound of a first hit. -/
theorem sharedHit_of_parts (seed : HitSeed prims K circuits settings runLimit)
    (salt : HitSalt prims K circuits settings runLimit) (clash : HitClash prims K circuits settings runLimit)
    (mismatch : HitMismatch prims K circuits settings runLimit) :
    SharedHit prims K circuits settings runLimit (hitError settings runLimit C) := by
  intro D A q bounded
  have h₁ := seed D A q bounded
  have h₂ := salt D A q bounded
  have h₃ := clash D A q bounded
  have h₄ := mismatch D A q bounded
  have c₁ := dealtProb_cover prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (HitOf D) (HitSeedOf D)
    (fun r => HitSaltOf D r ∨ ClashOf D r ∨ MismatchOf D r) fun r hr => (hitOf_iff D r).mp hr
  have c₂ := dealtProb_cover prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A
    (fun r => HitSaltOf D r ∨ ClashOf D r ∨ MismatchOf D r) (HitSaltOf D)
    (fun r => ClashOf D r ∨ MismatchOf D r) fun _ hr => hr
  have c₃ := dealtProb_cover prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A
    (fun r => ClashOf D r ∨ MismatchOf D r) (ClashOf D) (MismatchOf D) fun _ hr => hr
  unfold hitError
  linarith

/-- The bound of the four parts is `privacyHitError`. -/
theorem hitError_eq (C : Committee) (q : ℕ) :
    hitError settings runLimit C q = privacyHitError settings runLimit C q := by
  unfold hitError hitSeedError hitSaltError hitClashError hitMismatchError privacyHitError
  push_cast
  ring

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedHit_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedHit_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.hitError_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.hitError_eq
