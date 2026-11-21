import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.UpToTouch
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.NormalShift

/-!
# The steps from the parts of a hidden term to `SeedTouch`

`SeedTouch` bounds a touch of a hidden cell in `touchRun`. This file splits the touch by the hidden
term, moves the parts of one term by a shift, and states the two statements on the world that
remain.

* `flagAt X` is `loggedWorld` with a flag that records a counted call of `H` or a programming call at
  the cell `X`. `flagsWorld` keeps one such flag for each term. `touch_le_sum` bounds the touch in
  `touchRun` by the sum over the hidden terms `T` of the touch at `hiddenInput parts T` in
  `touchRunWith T id`.
* `touchRunWith T g` is the run with the parts `g parts` in the suffix and in the flag. The draw of
  the parts is invariant under `shiftAll T c`, so `touchRunWith T id` and
  `touchRunWith T (shiftAll T c)` have one law (`touchRunWith_shift`).
* `partsRef T` is the reference run. The suffix is `seedGenAt` on the unshifted parts, and the
  derivations of `T` ask the cell `markCell` by their place in the code. `partsWorld` gives a private
  answer to each free call at a commitment cell between two honest operators and at `markCell`, and
  records the cell of each programming call. No answer and no state depends on a shift.
* `partsNamed T parts s` is the set of the shifts `δ` of the holders of `T` for which the shifted
  hidden cell is in the cache or in the recorded programming cells of `s`.
* `PartsStep` states the step from the shifted run to the reference run. `PartsCount` bounds the
  named shifts. `seedTouch_of_steps` gives `SeedTouch` from the two statements.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal (seedGenAt commitAddress termAddress)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## A state map of a run -/

/-- A map of the state that commutes with each step of two handlers commutes with each run. -/
theorem run_map_state {ι : Type} {spec : OracleSpec ι} {σ τ α : Type} (impl₁ : QueryImpl spec (StateT σ ProbComp))
    (impl₂ : QueryImpl spec (StateT τ ProbComp)) (φ : σ → τ)
    (h : ∀ t s, (fun r => (r.1, φ r.2)) <$> (impl₁ t).run s = (impl₂ t).run (φ s)) (oa : OracleComp spec α) (s : σ) :
    (fun r => (r.1, φ r.2)) <$> (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run (φ s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, map_bind, OracleQuery.input_query, OracleQuery.cont_query,
      liftM, monadLift_self]
    rw [← h t s, bind_map_left]
    exact bind_congr fun r => ih r.1 r.2

/-! ## The flag of one cell and the flags of all terms -/

section Flags

variable (prims : Primitives) (D : C.Coalition)

/-- A counted call of `H` or a programming call at the cell `X`. -/
def TouchAt (X : Query C) : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inr (.inl q))) => q = X
  | .inl (.inr x) => x.1 = X
  | _ => False

/-- `loggedWorld` with a flag that records each counted call of `H` and each programming call at the
cell `X`. -/
def flagAt (X : Query C) : QueryImpl (WorldSpec C) (StateT (LogState C × Bool) ProbComp) := fun t =>
  StateT.mk fun s => (fun r => (r.1, (r.2, s.2 || decide (TouchAt X t)))) <$> (loggedWorld prims D t).run s.1

/-- `loggedWorld` with one flag for each term `T`, which records each counted call of `H` and each
programming call at `hiddenInput parts T`. -/
def flagsWorld (parts : C.Party → Parts C) :
    QueryImpl (WorldSpec C) (StateT (LogState C × (C.Term → Bool)) ProbComp) := fun t =>
  StateT.mk fun s => (fun r => (r.1, (r.2, fun T => s.2 T || decide (TouchAt (hiddenInput parts T) t)))) <$>
    (loggedWorld prims D t).run s.1

theorem touch_iff (parts : C.Party → Parts C) (t : (WorldSpec C).Domain) :
    Touch D parts t ↔ ∃ T, ¬ KnownTo D.1 T ∧ TouchAt (hiddenInput parts T) t := by
  rcases t with ((n | q | x) | p) | (n | q | x) <;> simp [Touch, TouchAt, HiddenCell, eq_comm]

/-- The flag of `flagWorld` is the flag of some hidden term in `flagsWorld`. -/
def anyHidden (s : LogState C × (C.Term → Bool)) : LogState C × Bool :=
  (s.1, decide (∃ T, ¬ KnownTo D.1 T ∧ s.2 T = true))

theorem flagsWorld_any (parts : C.Party → Parts C) (t : (WorldSpec C).Domain) (s : LogState C × (C.Term → Bool)) :
    (fun r => (r.1, anyHidden D r.2)) <$> (flagsWorld prims D parts t).run s =
      (flagWorld prims D parts t).run (anyHidden D s) := by
  simp only [flagsWorld, flagWorld, anyHidden, StateT.run_mk, Functor.map_map]
  congr 1
  funext r
  congr 3
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, touch_iff]
  constructor
  · rintro ⟨T, hT, h | h⟩
    · exact Or.inl ⟨T, hT, h⟩
    · exact Or.inr ⟨T, hT, h⟩
  · rintro (⟨T, hT, h⟩ | ⟨T, hT, h⟩)
    · exact ⟨T, hT, Or.inl h⟩
    · exact ⟨T, hT, Or.inr h⟩

theorem flagsWorld_one (parts : C.Party → Parts C) (T : C.Term) (t : (WorldSpec C).Domain)
    (s : LogState C × (C.Term → Bool)) :
    (fun r => (r.1, (r.2.1, r.2.2 T))) <$> (flagsWorld prims D parts t).run s =
      (flagAt prims D (hiddenInput parts T) t).run (s.1, s.2 T) := by
  simp only [flagsWorld, flagAt, StateT.run_mk, Functor.map_map]

end Flags

/-! ## The runs of one term -/

section Runs

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The prefix with the parts `g parts`. -/
def mapParts {σ : Type} (g : (C.Party → Parts C) → C.Party → Parts C) (x : PrefixOut C σ) : PrefixOut C σ :=
  (x.1, x.2.1, g x.2.2)

/-- The game with the keys of the dealer and no emulated run, with the parts `g parts` in the suffix
and the flag of the cell `hiddenInput (g parts) T` on the suffix. The flag starts up when the cell has
a value at the end of the prefix. The result is the flag. -/
def touchRunWith (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term)
    (g : (C.Party → Parts C) → C.Party → Parts C) : ProbComp Bool := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let z ← (simulateQ (flagAt prims D (hiddenInput (g x.1.2.2) T))
    (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (mapParts g x.1))).run
      (x.2, (x.2.1.1 (hiddenInput (g x.1.2.2) T)).isSome)
  pure z.2.2

/-- The game with one flag for each term. -/
def touchMulti (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ProbComp (PrefixOut C A.net.State × (RunOut C × (LogState C × (C.Term → Bool)))) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let z ← (simulateQ (flagsWorld prims D x.1.2.2)
    (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1)).run
      (x.2, fun T => (x.2.1.1 (hiddenInput x.1.2.2 T)).isSome)
  pure (x.1, z)

omit [Fintype E] [DecidableEq E] in
theorem touchRun_eq_multi (D : C.Coalition) (A : DkgTsigAdversary C E) :
    touchRun prims K circuits settings runLimit D A =
      (fun r => (r.1, (r.2.1, anyHidden D r.2.2))) <$> touchMulti prims K circuits settings runLimit D A := by
  unfold touchRun touchMulti
  simp only [map_bind, map_pure]
  refine bind_congr fun x => ?_
  have hs : anyHidden D (x.2, fun T => (x.2.1.1 (hiddenInput x.1.2.2 T)).isSome) =
      (x.2, startFlag D x.1.2.2 x.2) := by
    unfold anyHidden startFlag
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    simp only [HiddenCell]
    constructor
    · rintro ⟨T, hT, h⟩
      exact ⟨_, ⟨T, hT, rfl⟩, h⟩
    · rintro ⟨_, ⟨T, hT, rfl⟩, h⟩
      exact ⟨T, hT, h⟩
  rw [← hs, ← run_map_state _ _ (anyHidden D) (flagsWorld_any prims D x.1.2.2), bind_map_left]

omit [Fintype E] [DecidableEq E] in
theorem touchRunWith_eq_multi (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) :
    touchRunWith prims K circuits settings runLimit D A T id =
      (fun r => r.2.2.2 T) <$> touchMulti prims K circuits settings runLimit D A := by
  unfold touchRunWith touchMulti
  rw [map_bind]
  refine bind_congr fun x => ?_
  have h := run_map_state _ _ (fun s : LogState C × (C.Term → Bool) => (s.1, s.2 T))
    (flagsWorld_one prims D x.1.2.2 T) (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1)
    (x.2, fun T => (x.2.1.1 (hiddenInput x.1.2.2 T)).isSome)
  dsimp only at h
  change (simulateQ (flagAt prims D (hiddenInput x.1.2.2 T))
    (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1)).run
      (x.2, (x.2.1.1 (hiddenInput x.1.2.2 T)).isSome) >>= (fun z => pure z.2.2) = _
  rw [← h]
  simp only [map_bind, map_pure, bind_map_left]

/-- The hidden terms. -/
def hiddenTerms (D : C.Coalition) : Finset C.Term := Finset.univ.filter fun T => ¬ KnownTo D.1 T

omit [Fintype E] [DecidableEq E] in
/-- A touch in `touchRun` has at most the sum over the hidden terms of the probability of a touch at
the cell of one term. -/
theorem touch_le_sum (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Pr{let r ← touchRun prims K circuits settings runLimit D A}[r.2.2.2 = true] ≤
      ∑ T ∈ hiddenTerms D, Pr{let b ← touchRunWith prims K circuits settings runLimit D A T id}[b = true] := by
  rw [touchRun_eq_multi, prEvent_map]
  simp only [touchRunWith_eq_multi, prEvent_map]
  calc _ ≤ Pr{let r ← touchMulti prims K circuits settings runLimit D A}[∃ T ∈ hiddenTerms D, r.2.2.2 T = true] := by
        refine prEvent_mono _ _ _ fun r h => ?_
        simp only [anyHidden, decide_eq_true_iff] at h
        obtain ⟨T, hT, h⟩ := h
        exact ⟨T, by simp [hiddenTerms, hT], h⟩
    _ ≤ _ := prEvent_exists_finset_le (hiddenTerms D) (touchMulti prims K circuits settings runLimit D A)
          fun T r => r.2.2.2 T = true

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The prefix in `loggedWorld` draws the keys and the parts with no change of the world. -/
theorem prefix_run (D : C.Coalition) (A : DkgTsigAdversary C E) :
    (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), []) = (do
      let a ← (simulateQ (loggedWorld prims D) (observe (A.net.start (corruptInputs D fun _ => ()) []))).run
        ((∅, ∅), [])
      let b ← (prawnsKeyGen (C := C))
      let parts ← partsDraw C
      pure ((a.1, b, parts), a.2)) := by
  unfold dealtPrefix
  simp only [simulateQ_bind, StateT.run_bind, loggedWorld_free_liftComp, simulateQ_pure, StateT.run_pure,
    bind_map_left]

omit [Fintype E] [DecidableEq E] in
/-- The run of one term with the parts shifted has the law of the run with no shift. -/
theorem touchRunWith_shift (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (c : C.Party → HashOutput) :
    touchRunWith prims K circuits settings runLimit D A T id =ᵈ
      touchRunWith prims K circuits settings runLimit D A T (shiftAll T c) := by
  unfold touchRunWith
  rw [prefix_run]
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b => ?_
  have e := (evalDist_shiftAll T c).symm.bind_left (fun parts =>
    (simulateQ (flagAt prims D (hiddenInput parts T))
      (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A (a.1, b, parts))).run
        (a.2, (a.2.1.1 (hiddenInput parts T)).isSome) >>= fun z => pure z.2.2)
  rw [bind_map_left] at e
  exact e

end Runs

/-! ## The reference run of one term -/

section Reference

/-- The cell that the derivations of the shifted term ask in the reference run. A derivation of a
term on the parts has one part for each of its `t` holders, so no such derivation asks this cell. -/
def markCell : Query C := .derive .seedGen .term []

/-- A free call at this cell has a private answer in the reference world. It is `markCell` or a
commitment cell of the seed generation between two honest operators. -/
def PrivateCell (D : C.Coalition) (q : Query C) : Prop :=
  q = markCell ∨ ∃ (i j : C.Party) (r : List HashOutput), i ∉ D.1 ∧ j ∉ D.1 ∧ q = .commit .seedGen i j r

/-- The state of `partsWorld`, namely the state of `loggedWorld`, the private cache and the list of
the cells of the programming calls. -/
abbrev PartsState (C : Committee) := LogState C × HashCache C × List (Query C)

variable (prims : Primitives)

/-- `loggedWorld` where a free call of `H` at a private cell takes its answer from the private cache
and leaves the world as it is, and where each programming call adds its cell to the list. No answer
and no state depends on a shift. -/
def partsWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (PartsState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      if PrivateCell D q then StateT.mk fun s =>
        (fun r => (r.1, (s.1, r.2, s.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s.2.1
      else StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$>
        (loggedWorld prims D (.inr (.inr (.inl q)))).run s.1
  | .inl (.inr x) => StateT.mk fun s =>
      (fun r => (r.1, (r.2, s.2.1, s.2.2 ++ [x.1]))) <$> (loggedWorld prims D (.inl (.inr x))).run s.1
  | t => StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> (loggedWorld prims D t).run s.1

/-- The shift `δ` of the holders of `T`, with zero at each other operator. -/
def extendShift (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput) : C.Party → HashOutput :=
  fun k => if h : k ∈ C.holders T then δ ⟨k, h⟩ else 0

/-- The shifts `δ` for which the hidden cell of `T` on the parts shifted by `δ` is in the cache or in
the list of the programming cells. Each cell `.derive .seedGen .term L` names at most one shift. -/
def partsNamed (T : C.Term) (parts : C.Party → Parts C) (s : PartsState C) :
    Finset ({k // k ∈ C.holders T} → HashOutput) :=
  Finset.univ.filter fun δ => (s.1.1.1 (hiddenInput (shiftAll T (extendShift T δ) parts) T)).isSome ∨
    hiddenInput (shiftAll T (extendShift T δ) parts) T ∈ s.2.2

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The derive addresses of the reference run. The derivations of `T` ask `markCell`, and each other
derivation asks its address on the parts. -/
def termMark (D : C.Coalition) (parts : C.Party → Parts C) (T : C.Term) : C.Party → Mail C E → C.Term → Query C :=
  fun i inbox T' => if T' = T then markCell else termAddress D parts i inbox T'

/-- The suffix of the game with the seed generation `seedGenAt` with the commit addresses `commitAt`
and the derive addresses `termAt`. -/
def suffixAt (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (commitAt : C.Party → C.Party → Query C) (termAt : C.Party → Mail C E → C.Term → Query C) :
    OracleComp (WorldSpec C) (RunOut C) := do
  let (state, emu) ← seedGenAt D A.net x.1.1 x.1.2 x.2.1.1 x.2.1.2.2 x.2.2 commitAt termAt
  let keys := fun i => (emu i).map fun _ => x.2.1.2.2 i
  let win ← (secRest K circuits settings runLimit m D A x.2.1.1 x.2.1.2.1 x.2.1.2.2 emu).run' (startState D state keys)
  pure (win, x.2.1.1, x.2.1.2.1, x.2.1.2.2, emu)

/-- The reference run of the term `T`. The prefix runs in `loggedWorld`. The suffix runs on the
unshifted parts with the commit addresses of the parts and the derive addresses `termMark`, in
`partsWorld`. The result is the parts, the result of the game and the state. -/
def partsRef (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) :
    ProbComp ((C.Party → Parts C) × (RunOut C × PartsState C)) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let z ← (simulateQ (partsWorld prims D) (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1
    (commitAddress x.1.2.2) (termMark D x.1.2.2 T))).run (x.2, ∅, [])
  pure (x.1.2.2, z)

/-- The step on the world. For a term `T` with no corrupt holder and each shift `δ` of its holders, the
touch at the hidden cell of `T` in the run on the parts shifted by `δ` has at most the probability that
the reference run names `δ`. The two runs agree until the shifted hidden cell is asked by a counted
call, a programming call or a free call of another derivation, or has a value at the end of the
prefix. The commitments between honest operators differ in the two runs, and only an equality test
reads them. The bound is a mean over the run from the empty start. -/
def PartsStep : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput),
    ¬ KnownTo D.1 T →
    Pr{let b ← touchRunWith prims K circuits settings runLimit D A T (shiftAll T (extendShift T δ))}[b = true] ≤
      Pr{let r ← partsRef prims K circuits settings runLimit D A T}[δ ∈ partsNamed T r.1 r.2.2]

/-- The known terms. -/
def knownTerms (D : C.Coalition) : Finset C.Term := Finset.univ.filter fun T => KnownTo D.1 T

/-- The count of the named shifts at the end of the reference run with the budget `q`. A named shift
comes from a counted call (at most `q`), the derivation of another hidden term (at most `h - 1`),
or a known term, with one programming call and at most `n` derivations of its honest holders. -/
def PartsCount : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ T : C.Term, ¬ KnownTo D.1 T →
    ∀ r ∈ support (partsRef prims K circuits settings runLimit D A T),
      (partsNamed T r.1 r.2.2).card ≤ q + ((hiddenTerms D).card - 1) + (C.n + 1) * (knownTerms D).card

end Reference

/-! ## The glue -/

section Glue

theorem card_shifts (T : C.Term) :
    (Fintype.card ({k // k ∈ C.holders T} → HashOutput) : ℝ≥0∞) = 2 ^ (256 * C.t) := by
  rw [Fintype.card_fun, card_holders, Nat.cast_pow, pow_mul]
  congr 1
  simp
  norm_num

theorem hidden_add_known (D : C.Coalition) : (hiddenTerms D).card + (knownTerms D).card = termCount C := by
  unfold hiddenTerms knownTerms
  rw [add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ, card_term, termCount]

/-- The sum of the counts over the hidden terms fits in the numerator of `compCloseError`. -/
theorem count_sum_le (n q h k : ℕ) :
    h * (q + (h - 1) + (n + 1) * k) ≤ q * (h + k) + (n + 2) * (h + k) * (h + k - 1) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · have h1 : h - 1 ≤ h + k - 1 := by omega
    have h2 : k ≤ h + k - 1 := by omega
    have e : (n + 2) * (h + k) * (h + k - 1) = (h + k) * (h + k - 1) + (n + 1) * (h + k) * (h + k - 1) := by ring
    rw [e]
    calc h * (q + (h - 1) + (n + 1) * k) = h * q + h * (h - 1) + (n + 1) * (h * k) := by ring
      _ ≤ (h + k) * q + (h + k) * (h + k - 1) + (n + 1) * ((h + k) * (h + k - 1)) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right q (by omega)) (Nat.mul_le_mul (by omega) h1))
            (Nat.mul_le_mul_left (n + 1) (Nat.mul_le_mul (by omega) h2))
      _ = q * (h + k) + ((h + k) * (h + k - 1) + (n + 1) * (h + k) * (h + k - 1)) := by ring

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- `PartsStep` and `PartsCount` give `SeedTouch`. -/
theorem seedTouch_of_steps (step : PartsStep prims K circuits settings runLimit)
    (count : PartsCount prims K circuits settings runLimit) : SeedTouch prims K circuits settings runLimit := by
  intro D A q bounded
  set N := q + ((hiddenTerms D).card - 1) + (C.n + 1) * (knownTerms D).card with hN
  have hT : ∀ T ∈ hiddenTerms D,
      Pr{let b ← touchRunWith prims K circuits settings runLimit D A T id}[b = true] ≤
        (N : ℝ≥0∞) / 2 ^ (256 * C.t) := by
    intro T hT
    have hT' : ¬ KnownTo D.1 T := (Finset.mem_filter.1 hT).2
    have h := prEvent_le_of_shiftMean _ (partsRef prims K circuits settings runLimit D A T)
      (fun r => partsNamed T r.1 r.2.2) N
      (fun δ => ((touchRunWith_shift prims K circuits settings runLimit D A T (extendShift T δ)).prEvent_eq _).trans_le
        (step D A T δ hT')) (count D A q bounded T hT')
    rwa [card_shifts] at h
  have hsum := (touch_le_sum prims K circuits settings runLimit D A).trans (Finset.sum_le_sum hT)
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc] at hsum
  have hcast : ((hiddenTerms D).card : ℝ≥0∞) * (N : ℝ≥0∞) = (((hiddenTerms D).card * N : ℕ) : ℝ≥0∞) := by
    push_cast
    rfl
  rw [hcast] at hsum
  have hfin : (((hiddenTerms D).card * N : ℕ) : ℝ≥0∞) / 2 ^ (256 * C.t) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
  have hreal := ENNReal.toReal_mono hfin hsum
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow] at hreal
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [htwo] at hreal
  refine hreal.trans ?_
  unfold compCloseError
  have hnum := count_sum_le C.n q (hiddenTerms D).card (knownTerms D).card
  rw [hidden_add_known] at hnum
  gcongr

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.touchRunWith_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.touchRunWith_shift

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.seedTouch_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.seedTouch_of_steps
