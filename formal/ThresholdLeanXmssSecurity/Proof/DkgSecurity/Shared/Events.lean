import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Rest

/-!
# The first hit and the games with the shared bad event

* `SensitiveCell` is a cell that only the emulation or a hidden term makes, namely a PRF cell under
  an emulated seed of a hidden term and a digest cell under a salt of a hidden term. `FirstHit` says
  that a counted call asks such a cell, that an emulated seed of a hidden term is a seed of the
  dealer (`SeedClash`), or that an emulated operator holds a known key that is not the key of the
  dealer (`KeyMismatch`). `loggedWorld` is `streamWorld` with the log of the counted calls of `H`.
* `sharedReal` and `sharedDealt` are the games with the shared event in `loggedWorld`. They give the
  win, the flag and, after the seed generation of the simulator, the data of the dealer. `realProb`
  and `dealtProb` are the probabilities of an event on their results.
* `tableRestShared` is the distinguisher of the seed generation claim with the shared event.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-- The salts of the digests of the terms with no corrupt holder. `randBits` draws the 256 bits of a
salt at the stream index 2, and no other draw has that index. -/
def hiddenSalts (D : C.Coalition) (hidden : HiddenCache C) : Set (List Bit) :=
  {salt | ∃ (T : C.Term) (key : HashOutput) (ρ : ℕ), ¬ KnownTo D.1 T ∧
    hidden ((.term T, key), ρ, 2, 0) ≠ none ∧
    salt = (List.range 256).map fun position => (hidden ((.term T, key), ρ, 2, position)).getD 0}

/-- A cell that the adversary must not ask. It is a PRF cell under the seed that an emulated operator
holds for a term with no corrupt holder, or a digest cell under a salt of such a term. -/
def SensitiveCell (D : C.Coalition) (emu : C.Party → Option (Keys C)) (hidden : HiddenCache C)
    (q : Query C) : Prop :=
  (∃ (i : C.Party) (keys : Keys C) (T : C.Term) (x : Point), i ∉ D.1 ∧ emu i = some keys ∧ i ∈ C.holders T ∧
      ¬ KnownTo D.1 T ∧ q = .prf (keys.seed T) x) ∨
    ∃ (salt : List Bit) (history : HashOutput), salt ∈ hiddenSalts D hidden ∧ q = .digest salt history

/-- An emulated seed of a term with no corrupt holder is a seed of the dealer. Then a free call of
the dealer, of the signing or of the win test asks a cell of the emulation. -/
def SeedClash (D : C.Coalition) (seeds : C.Term → HashOutput) (emu : C.Party → Option (Keys C)) : Prop :=
  ∃ (i : C.Party) (keys : Keys C) (T T' : C.Term), i ∉ D.1 ∧ emu i = some keys ∧ i ∈ C.holders T ∧
    ¬ KnownTo D.1 T ∧ keys.seed T = seeds T'

/-! ## The first hit -/

/-- The cell of a counted call of `H`. -/
def countedCells : (WorldSpec C).Domain → List (Query C)
  | .inl (.inl (.inr (.inl q))) => [q]
  | _ => []

/-- `streamWorld` with the log of the counted calls of `H`. -/
def loggedWorld (prims : Primitives) (D : C.Coalition) :
    QueryImpl (WorldSpec C) (StateT (StreamState C × List (Query C)) ProbComp) := fun t =>
  StateT.mk fun st => (fun r => (r.1, (r.2, st.2 ++ countedCells t))) <$> (streamWorld prims D t).run st.1

/-- An emulated operator with keys holds another parameter than the dealer, or another seed of a term
with a corrupt holder. A write of `worldSeedGen` met a cell with a value, or the operator derived the
key from another view than the first honest holder and its echo passed. Then an emulated run and a
real run compute on different known inputs. -/
def KeyMismatch (D : C.Coalition) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) : Prop :=
  ∃ (i : C.Party) (keys : Keys C), i ∉ D.1 ∧ emu i = some keys ∧
    (keys.parameter ≠ parameter ∨ ∃ T : C.Term, i ∈ C.holders T ∧ KnownTo D.1 T ∧ keys.seed T ≠ (dealt i).seed T)

/-- The result of `dealtRun` with the world and the log of the counted calls. -/
abbrev LoggedRun (C : Committee) :=
  (Bool × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C))) ×
    (StreamState C × List (Query C))

/-- A first hit at the end of a run of `dealtRun`. A counted call asked a sensitive cell, to the end
of the game, so also a cell of a run that aborted. Or an emulated seed is a seed of the dealer. Or an
emulated operator holds a known key that is not the key of the dealer. -/
def FirstHit (D : C.Coalition) (r : LoggedRun C) : Prop :=
  (∃ q ∈ r.2.2, SensitiveCell D r.1.2.2.2.2 r.2.1.2 q) ∨ SeedClash D r.1.2.2.1 r.1.2.2.2.2 ∨
    KeyMismatch D r.1.2.1 r.1.2.2.2.1 r.1.2.2.2.2

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The games -/

/-- The world of the games with the shared event, `streamWorld` with the log of the counted calls. -/
abbrev LogState (C : Committee) := StreamState C × List (Query C)

/-- The game with the real seed generation and real runs, with the shared event. With `own` it is
`dkgTsigGame`, and with no `own` it is `refGame`. -/
def sharedReal (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) : StateT (LogState C) ProbComp (Bool × Bool) := do
  let (state, keys) ← simulateQ (loggedWorld prims D) (realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])
  sharedRestOf K circuits settings runLimit (loggedWorld prims D) Prod.fst own D A state keys

/-- The result of a game with the keys of the dealer, namely the win, the flag, and the parameter,
the seeds and the keys of the dealer with the keys of the emulated operators. -/
abbrev DealtOut (C : Committee) :=
  (Bool × Bool) × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C))

/-- The game with the keys of the dealer in the mode `m`, as `dealtRun`, with the shared event. -/
def sharedDealt (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) : StateT (LogState C) ProbComp (DealtOut C) := do
  let (state, parameter, seeds, dealt, emu) ← simulateQ (loggedWorld prims D) (worldSeedGen D A.net)
  let keys := fun i => (emu i).map fun _ => dealt i
  let r ← sharedRest K circuits settings runLimit (loggedWorld prims D) Prod.fst false m D A parameter seeds dealt emu
    (startState D state keys)
  pure (r, parameter, seeds, dealt, emu)

/-- The probability of `event` on the result of `sharedReal`. -/
def realProb (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) (event : Bool × Bool → Prop) : ℝ :=
  (Pr{let r ← (sharedReal prims K circuits settings runLimit own D A).run ((∅, ∅), [])}[event r.1]).toReal

/-- The probability of `event` on the result of `sharedDealt` with the world and the log. -/
def dealtProb (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) (event : DealtOut C × LogState C → Prop) : ℝ :=
  (Pr{let r ← (sharedDealt prims K circuits settings runLimit m D A).run ((∅, ∅), [])}[event r]).toReal

/-- The win with no flag. -/
def Clean (r : Bool × Bool) : Prop := r.1 = true ∧ r.2 = false

/-- A first hit in a game with the keys of the dealer. -/
def HitOf (D : C.Coalition) (r : DealtOut C × LogState C) : Prop := FirstHit D ((r.1.1.1, r.1.2), r.2)

/-- The win with no flag and no first hit. -/
def CleanNoHit (D : C.Coalition) (r : DealtOut C × LogState C) : Prop := Clean r.1.1 ∧ ¬ HitOf D r

/-- The distinguisher of the seed generation claim with the shared event. It runs the rest with real
runs and the answers of the dealer on the private table, and gives "win and no flag". -/
def tableRestShared (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Distinguisher C (tableNet prims A.net).State (Keys C) := fun r =>
  (fun x => x.1 && !x.2) <$>
    (sharedRestOf K circuits settings runLimit (tableWorld prims D) id false D A r.1.1 r.2).run' (r.1.2, ∅)

end ThresholdLeanXmssSecurity.DkgSecurityProof
