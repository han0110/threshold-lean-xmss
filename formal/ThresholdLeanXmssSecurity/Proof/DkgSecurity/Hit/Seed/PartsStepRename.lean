import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepDerive

/-!
# The private commitments at the shifted addresses

`pairRun` asks the commitments between honest operators in the private cache at the commit addresses
of the unshifted parts. `pairShiftRun` asks them at the commit addresses of the shifted parts. The two
runs have one law of the flag (`pairShiftRun_eq`).

* `swapCommit R R'` swaps the commit cell with the reveal `R i j` and the commit cell with the reveal
  `R' i j`, for each pair `(i, j)`, and keeps each other cell. It is an involution.
* By `suffixAt_cellRw` the rewrite by the swap sends the suffix of `pairRun` to the suffix of
  `pairShiftRun`. The rewrite changes only the keys of the private cache, so the state map that reads
  the private cache through the swap commutes with each call (`run_map_state`).

`CommitShift` is the commit side with the middle run `pairShiftRun`, so both runs ask one program.
`commitSide_of_shift` gives `CommitSide` from it.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal (commitAddress termAddress openAddress
  openAddress_corrupt openAddress_self)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The swap of two commit cells of each pair -/

section Swap

variable (R R' : C.Party → C.Party → List HashOutput)

/-- The commit cell of `(i, j)` with the reveal `R i j` goes to the reveal `R' i j` and back. Each other
cell stays. -/
def swapCommit : Query C → Query C
  | .commit .seedGen i j r => .commit .seedGen i j (if r = R i j then R' i j else if r = R' i j then R i j else r)
  | q => q

theorem swapCommit_commit (i j : C.Party) (r : List HashOutput) :
    swapCommit R R' (.commit .seedGen i j r) =
      .commit .seedGen i j (if r = R i j then R' i j else if r = R' i j then R i j else r) := rfl

theorem swapCommit_of_not {q : Query C} (hq : ∀ i j r, q ≠ .commit .seedGen i j r) : swapCommit R R' q = q := by
  unfold swapCommit
  split
  · next i j r => exact absurd rfl (hq i j r)
  · rfl

theorem swapCommit_swapCommit (q : Query C) : swapCommit R R' (swapCommit R R' q) = q := by
  by_cases hq : ∃ i j r, q = .commit .seedGen i j r
  · obtain ⟨i, j, r, rfl⟩ := hq
    rw [swapCommit_commit, swapCommit_commit]
    congr 1
    by_cases h₁ : r = R i j
    · subst h₁
      by_cases h₂ : R' i j = R i j <;> simp [h₂]
    · by_cases h₂ : r = R' i j
      · subst h₂
        simp [h₁]
      · simp [h₁, h₂]
  · push Not at hq
    rw [swapCommit_of_not R R' hq, swapCommit_of_not R R' hq]

theorem swapCommit_of_eq {i j : C.Party} (h : R i j = R' i j) (r : List HashOutput) :
    swapCommit R R' (.commit .seedGen i j r) = .commit .seedGen i j r := by
  rw [swapCommit_commit]
  congr 1
  by_cases h₁ : r = R i j
  · rw [ite_eq_left h₁, h₁, h]
  · rw [ite_eq_right h₁]
    by_cases h₂ : r = R' i j
    · rw [ite_eq_left h₂, h₂, h]
    · rw [ite_eq_right h₂]

theorem pairCell_swapCommit (D : C.Coalition) (q : Query C) : PairCell D (swapCommit R R' q) ↔ PairCell D q := by
  by_cases hq : ∃ i j r, q = .commit .seedGen i j r
  · obtain ⟨i, j, r, rfl⟩ := hq
    rw [swapCommit_commit]
    constructor
    · rintro ⟨i', j', r', hi, hj, h⟩
      simp only [Query.commit.injEq, true_and] at h
      exact ⟨i, j, r, h.1 ▸ hi, h.2.1 ▸ hj, rfl⟩
    · rintro ⟨i', j', r', hi, hj, h⟩
      simp only [Query.commit.injEq, true_and] at h
      exact ⟨i, j, _, h.1 ▸ hi, h.2.1 ▸ hj, rfl⟩
  · push Not at hq
    rw [swapCommit_of_not R R' hq]

/-- The cache `p` read through the map `σ`. -/
def renameCache (σ : Query C → Query C) (p : HashCache C) : HashCache C := QueryCache.ofFn fun q => p (σ q)

theorem renameCache_apply (σ : Query C → Query C) (p : HashCache C) (q : Query C) : renameCache σ p q = p (σ q) := by
  simp [renameCache]

theorem renameCache_empty (σ : Query C → Query C) : renameCache σ (∅ : HashCache C) = ∅ := by
  refine QueryCache.ext fun q => ?_
  simp [renameCache]

theorem renameCache_cacheQuery (σ : Query C → Query C) (hσ : ∀ q, σ (σ q) = q) (p : HashCache C) (q : Query C)
    (u : HashOutput) : renameCache σ (p.cacheQuery (σ q) u) = (renameCache σ p).cacheQuery q u := by
  refine QueryCache.ext fun q' => ?_
  rw [renameCache_apply]
  by_cases h : q' = q
  · subst h
    simp
  · have h' : σ q' ≠ σ q := fun e => h (by rw [← hσ q', e, hσ q])
    rw [QueryCache.cacheQuery_of_ne _ _ h', QueryCache.cacheQuery_of_ne _ _ h, renameCache_apply]

end Swap

/-! ## The private world through the swap -/

section World

variable (prims : Primitives) (D : C.Coalition) (X : Query C) (σ : Query C → Query C)

/-- The state map that reads the private cache through `σ`. -/
def renameState (s : PairState C) : PairState C := (s.1, renameCache σ s.2.1, s.2.2)

theorem pairWorld_rename (hσ : ∀ q, σ (σ q) = q) (hpair : ∀ q, PairCell D (σ q) ↔ PairCell D q)
    (hfix : ∀ q, ¬ PairCell D q → σ q = q) (t : (WorldSpec C).Domain) (s : PairState C) :
    (fun r => (r.1, renameState σ r.2)) <$> ((pairWorld prims D X ∘ₛ cellRw σ) t).run s =
      (pairWorld prims D X t).run (renameState σ s) := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [QueryImpl.apply_compose, cellRw, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map]
  all_goals try (simp only [pairWorld, renameState, StateT.run_mk, Functor.map_map]; done)
  by_cases hq : PairCell D q
  · rw [pairWorld_private prims D X ((hpair q).2 hq), pairWorld_private prims D X hq, Functor.map_map]
    simp only [renameState]
    rw [randomOracle.run_eq, randomOracle.run_eq, renameCache_apply]
    cases σ q |> s.2.1 with
    | some v => simp
    | none =>
      simp only [map_bind, map_pure]
      refine bind_congr fun a => ?_
      rw [renameCache_cacheQuery σ hσ]
  · rw [hfix q hq, pairWorld_shared prims D X hq, pairWorld_shared prims D X hq, Functor.map_map]
    rfl

end World

/-! ## The middle run at the shifted commit addresses -/

section Runs

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The middle run with the commit addresses of the shifted parts. -/
def pairShiftRun (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput) :
    ProbComp Bool := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let z ← (simulateQ (pairWorld prims D (hiddenInput (shiftBy T δ x.1.2.2) T))
    (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1 (commitAddress (shiftBy T δ x.1.2.2))
      (termAddress D (shiftBy T δ x.1.2.2)))).run
      (x.2, ∅, (x.2.1.1 (hiddenInput (shiftBy T δ x.1.2.2) T)).isSome)
  pure z.2.2.2

/-- The commit side with the middle run at the shifted commit addresses. For a term `T` with no corrupt
holder and each shift `δ` of its holders, the touch at the shifted hidden cell in the run on the shifted
parts has at most the probability of the touch in `pairShiftRun`. The two runs ask one program. They
differ only in the commitments between honest operators, which the run on the shifted parts asks in
the shared cache and `pairShiftRun` asks in the private cache. The bound is a mean over the run from the
empty start. -/
def CommitShift : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput),
    ¬ KnownTo D.1 T →
    Pr{let b ← shiftRun prims K circuits settings runLimit D A T δ}[b = true] ≤
      Pr{let b ← pairShiftRun prims K circuits settings runLimit D A T δ}[b = true]

theorem revealTo_ne_nil (phase : Phase) (c : Parts C) (i j : C.Party) : revealTo phase c i j ≠ [] := by
  simp [revealTo]

/-- The reveal of a sender to a receiver does not change under the shift of a term that one of them does
not hold. -/
theorem revealTo_shiftAll_of_not (T : C.Term) (c : C.Party → HashOutput) (parts : C.Party → Parts C) (k j : C.Party)
    (h : k ∉ C.holders T ∨ j ∉ C.holders T) :
    revealTo .seedGen (shiftAll T c parts k) k j = revealTo .seedGen (parts k) k j := by
  unfold revealTo
  rw [SeedNormal.shiftAll_parameter, SeedNormal.shiftAll_pair]
  congr 2
  refine List.map_congr_left fun T' hT' => SeedNormal.shiftAll_term_ne T T' c parts k fun e => ?_
  subst e
  simp [sharedTerms] at hT'
  rcases h with h | h
  · exact h hT'.2.1
  · exact h hT'.2.2

omit [Fintype E] [DecidableEq E] in
/-- The rewrite by the swap sends the suffix of `pairRun` to the suffix of `pairShiftRun`. -/
theorem suffixAt_swap (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) (T : C.Term)
    (δ : {k // k ∈ C.holders T} → HashOutput) (hT : ¬ KnownTo D.1 T) :
    simulateQ (cellRw (swapCommit (fun i j => revealTo .seedGen (x.2.2 i) i j)
        (fun i j => revealTo .seedGen (shiftBy T δ x.2.2 i) i j)))
      (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress x.2.2)
        (termAddress D (shiftBy T δ x.2.2))) =
      suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress (shiftBy T δ x.2.2))
        (termAddress D (shiftBy T δ x.2.2)) := by
  rw [suffixAt_cellRw K circuits settings runLimit _ D A x _ _ (fun i inbox k hk => ?_) (fun l => rfl) (fun l => rfl)
    (fun l => rfl) (fun q hq => ?_)]
  · congr 1
    funext a b
    simp only [commitAddress, swapCommit_commit, ite_true]
  · by_cases hkD : k ∈ D.1
    · rw [openAddress_corrupt _ _ _ _ _ hkD]
      refine swapCommit_of_eq _ _ ?_ _
      exact (revealTo_shiftAll_of_not T _ x.2.2 k i (Or.inl fun h => hT ⟨k, hkD, h⟩)).symm
    · have hki : k = i := hk.resolve_left hkD
      subst hki
      rw [openAddress_self _ _ _ _ hkD, swapCommit_commit, ite_eq_right (revealTo_ne_nil _ _ _ _).symm,
        ite_eq_right (revealTo_ne_nil _ _ _ _).symm]
  · refine swapCommit_of_not _ _ fun i j r e => ?_
    subst e
    simp [isSeedGenQuery] at hq

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The swap keeps each cell that is no commitment cell between two honest operators. -/
theorem swapCommit_fix (D : C.Coalition) (parts : C.Party → Parts C) (T : C.Term)
    (δ : {k // k ∈ C.holders T} → HashOutput) (hT : ¬ KnownTo D.1 T) (q : Query C) (hq : ¬ PairCell D q) :
    swapCommit (fun i j => revealTo .seedGen (parts i) i j) (fun i j => revealTo .seedGen (shiftBy T δ parts i) i j) q =
      q := by
  by_cases hc : ∃ i j r, q = .commit .seedGen i j r
  · obtain ⟨i, j, r, rfl⟩ := hc
    refine swapCommit_of_eq _ _ ?_ _
    refine (revealTo_shiftAll_of_not T _ parts i j ?_).symm
    by_cases hi : i ∈ D.1
    · exact Or.inl fun h => hT ⟨i, hi, h⟩
    · by_cases hj : j ∈ D.1
      · exact Or.inr fun h => hT ⟨j, hj, h⟩
      · exact absurd ⟨i, j, r, hi, hj, rfl⟩ hq
  · push Not at hc
    exact swapCommit_of_not _ _ hc

omit [Fintype E] [DecidableEq E] in
/-- `pairShiftRun` and `pairRun` have one law of the flag. -/
theorem pairShiftRun_eq (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term)
    (δ : {k // k ∈ C.holders T} → HashOutput) (hT : ¬ KnownTo D.1 T) :
    Pr{let b ← pairShiftRun prims K circuits settings runLimit D A T δ}[b = true] =
      Pr{let b ← pairRun prims K circuits settings runLimit D A T δ}[b = true] := by
  unfold pairShiftRun pairRun
  rw [DkgSecurityProof.prEvent_bind_wp, DkgSecurityProof.prEvent_bind_wp]
  refine congrArg _ (funext fun x => ?_)
  simp only [bind_pure_comp, prEvent_map]
  rw [← suffixAt_swap K circuits settings runLimit D A x.1 T δ hT, ← QueryImpl.simulateQ_compose]
  set σ := swapCommit (fun i j => revealTo .seedGen (x.1.2.2 i) i j)
    (fun i j => revealTo .seedGen (shiftBy T δ x.1.2.2 i) i j)
  have h := run_map_state _ _ (renameState σ)
    (pairWorld_rename prims D (hiddenInput (shiftBy T δ x.1.2.2) T) σ (swapCommit_swapCommit _ _)
      (pairCell_swapCommit _ _ D) (swapCommit_fix D x.1.2.2 T δ hT))
    (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1 (commitAddress x.1.2.2)
      (termAddress D (shiftBy T δ x.1.2.2)))
    (x.2, ∅, (x.2.1.1 (hiddenInput (shiftBy T δ x.1.2.2) T)).isSome)
  have e : renameState σ ((x.2, ∅, (x.2.1.1 (hiddenInput (shiftBy T δ x.1.2.2) T)).isSome) : PairState C) =
      (x.2, ∅, (x.2.1.1 (hiddenInput (shiftBy T δ x.1.2.2) T)).isSome) := by
    simp only [renameState, renameCache_empty]
  rw [e] at h
  rw [← h, prEvent_map]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- `CommitShift` gives `CommitSide`. -/
theorem commitSide_of_shift (shift : CommitShift prims K circuits settings runLimit) :
    CommitSide prims K circuits settings runLimit := fun D A T δ hT =>
  (shift D A T δ hT).trans_eq (pairShiftRun_eq prims K circuits settings runLimit D A T δ hT)

end Runs

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.commitSide_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.commitSide_of_shift
