import ThresholdLeanXmssSecurity.Proof.KeygenKnown
import ThresholdLeanXmssSecurity.Proof.Coupling
import XmssSecurity.Proof.Seeded.FreshTable

/-!
# Keygen security: aliases of programming inputs

Honest commitments are replaced by fresh uncached values. A coupling preserves the parts and the
complete observed transcript until a logged query hits an honest commitment input. Distinct sender
and receiver tags make the commitment inputs distinct; the cache remains equal elsewhere.

In the fresh-commitment prefix the transcript is independent of the parts. A commitment query costs
one honest parameter coordinate, and a derivation query costs at most `K` honest coordinates. These
query classes are disjoint, so each counted call costs at most `K / 2^256`. Distinct programming
inputs collide with probability at most `2^-256` per pair. The union bound is `(q * K + K^2) / 2^256`.

`keygenProgramAliasBound` closes the last hypothesis of `keygenSecurityDone_of_programAlias`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- A proposed derivation exposes a proposed value at each position of its input. -/
def keygenAliasValue (q : Query C) (k : ℕ) : HashOutput :=
  match q with
  | .derive _ _ values => values.getD k 0
  | _ => 0

theorem keygenAlias_term_coordinate (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (parts : C.Party → Parts C) (T : C.Term)
    (a : C.Party) (ha : a ∈ C.holders T) (hD : a ∉ D.1) :
    keygenAliasValue (keygenTermProgrammingInput D (keygenProgramView D parts log sent) T)
      ((C.parties.filter (· ∈ C.holders T)).idxOf a) = (parts a).term T := by
  simp [keygenTermProgrammingInput, keygenAliasValue, Committee.parties, ha,
    keygenProgramView, hD]

/-- For a fixed commit transcript, guessing a programmed term input costs one honest part. -/
theorem probEvent_keygenAlias_term_guess (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (T : C.Term) (q : Query C) :
    Pr[fun parts => keygenTermProgrammingInput D (keygenProgramView D parts log sent) T = q |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  obtain ⟨a, ha, hD⟩ := keygen_honest_holder D T
  calc
    _ ≤ Pr[fun parts => (parts a).term T =
        keygenAliasValue q ((C.parties.filter (· ∈ C.holders T)).idxOf a) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
      apply probEvent_mono
      intro parts _ he
      rw [← he, keygenAlias_term_coordinate D log sent parts T a ha hD]
    _ = _ := probEvent_parts_collision (fun parts => (parts a).term T) (fun _ =>
        keygenAliasValue q ((C.parties.filter (· ∈ C.holders T)).idxOf a)) a (some T) none
      (fun c parts => by simp [shiftAt, shiftParts]) (fun _ _ => rfl)

theorem probEvent_keygenAlias_pair_guess (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (p : C.Pair)
    (hp : p.1.1 ∉ D.1 ∨ p.1.2 ∉ D.1) (q : Query C) :
    Pr[fun parts => keygenPairProgrammingInput D (keygenProgramView D parts log sent) p = q |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rcases hp with ha | hb
  · calc
      _ ≤ Pr[fun parts => (parts p.1.1).pair p.1.2 = keygenAliasValue q 0 |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        apply probEvent_mono
        intro parts _ he
        rw [← he]
        simp [keygenAliasValue, keygenPairProgrammingInput, keygenProgramView, ha]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.1).pair p.1.2)
        (fun _ => keygenAliasValue q 0) p.1.1 none (some p.1.2)
        (fun c parts => by simp [shiftAt, shiftParts]) (fun _ _ => rfl)
  · calc
      _ ≤ Pr[fun parts => (parts p.1.2).pair p.1.1 = keygenAliasValue q 1 |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        apply probEvent_mono
        intro parts _ he
        rw [← he]
        simp [keygenAliasValue, keygenPairProgrammingInput, keygenProgramView, hb]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.2).pair p.1.1)
        (fun _ => keygenAliasValue q 1) p.1.2 none (some p.1.1)
        (fun c parts => by simp [shiftAt, shiftParts]) (fun _ _ => rfl)

theorem evalDist_keygenAlias_parameters :
    𝒟[(fun parts : C.Party → Parts C => fun i => (parts i).parameter) <$>
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] =
      𝒟[$ᵗ (C.Party → HashOutput)] := by
  rw [map_eq_bind_pure_comp]
  change 𝒟[(Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))) >>=
    (fun parts => pure (fun i => (parts i).parameter))] = _
  rw [← sequenceFin_bind_pure]
  trans 𝒟[Concrete.sequenceFin (fun _ : C.Party => ($ᵗ HashOutput : ProbComp HashOutput))]
  · apply evalDist_sequenceFin_congr
    intro i
    unfold sampleParts
    simp only [bind_assoc, pure_bind]
    apply evalDist_bind_congr'
    intro parameter
    rw [evalDist_uniform_bind_const, evalDist_uniform_bind_const]
    rfl
  · have he : ∀ n : ℕ, Concrete.sequenceFin (fun _ : Fin n => ($ᵗ HashOutput)) =
        XmssSecurity.Concrete.sequenceFin (fun _ : Fin n => ($ᵗ HashOutput)) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp only [Concrete.sequenceFin, XmssSecurity.Concrete.sequenceFin, ih]
    rw [he]
    exact XmssSecurity.Seeded.evalDist_sequenceFin_uniform _

theorem probEvent_keygenAlias_parameter_coordinate (a : C.Party) (v : HashOutput) :
    Pr[fun parts => (parts a).parameter = v |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] =
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun s : C.Party → HashOutput => s a = v |
        (fun parts : C.Party → Parts C => fun i => (parts i).parameter) <$>
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun s : C.Party → HashOutput => s a = v | $ᵗ (C.Party → HashOutput)] := by
      rw [probEvent_def, evalDist_keygenAlias_parameters, ← probEvent_def]
    _ = _ := probEvent_uniform_coord_eq a v

theorem probEvent_keygenAlias_parameter_guess (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : Query C) :
    Pr[fun parts => keygenParameterProgrammingInput D (keygenProgramView D parts log sent) = q |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  obtain ⟨a, ha⟩ := keygen_exists_honest D
  calc
    _ ≤ Pr[fun parts => (parts a).parameter = keygenAliasValue q (C.parties.idxOf a) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
      apply probEvent_mono
      intro parts _ he
      rw [← he]
      simp [keygenParameterProgrammingInput, keygenAliasValue, Committee.parties,
        keygenProgramView, ha]
    _ = _ := probEvent_keygenAlias_parameter_coordinate a _

/-- The honest commitments are the protected cells in the cache-erasure hybrid. -/
def KeygenAliasCommitHit (D : C.Coalition) (parts : C.Party → Parts C) : Query C → Prop
  | .commit .keygen i j values => i ∉ D.1 ∧ values = revealTo .keygen (parts i) i j
  | _ => False

theorem probEvent_keygenAlias_commit_guess (D : C.Coalition) (q : Query C) :
    Pr[fun parts => KeygenAliasCommitHit D parts q |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  cases q <;> try (solve | simp [KeygenAliasCommitHit])
  case commit phase i j values =>
    cases phase <;> try (solve | simp [KeygenAliasCommitHit])
    calc
      _ ≤ Pr[fun parts => (parts i).parameter = values.getD 0 0 |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        apply probEvent_mono
        intro parts _ he
        rw [he.2]
        simp [revealTo]
      _ = _ := probEvent_keygenAlias_parameter_coordinate i _

theorem keygenAlias_cross_honest (D : C.Coalition) (p : C.Pair)
    (hp : p ∈ keygenCrossCoordinates D) : p.1.1 ∉ D.1 ∨ p.1.2 ∉ D.1 := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
  have hr := (keygenCrossList_mem D r.1).mp r.2
  unfold keygenCrossPair Committee.pairOf
  split_ifs <;> simp_all

private theorem alias_prob_exists_list {α β : Type} (xs : List α) (oa : ProbComp β)
    (P : α → β → Prop) (ε : ℝ≥0∞) (h : ∀ a ∈ xs, Pr[P a | oa] ≤ ε) :
    Pr[fun x => ∃ a ∈ xs, P a x | oa] ≤ xs.length * ε := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have he : (fun x => ∃ b ∈ a :: xs, P b x) =
        (fun x => P a x ∨ ∃ b ∈ xs, P b x) := by funext x; simp
    rw [he]
    refine (probEvent_or_le _ _ _).trans ?_
    calc
      _ ≤ ε + xs.length * ε := add_le_add (h a (by simp))
        (ih (fun b hb => h b (by simp [hb])))
      _ = _ := by simp [Nat.cast_add, add_mul, add_comm]

/-- Fixed transcripts give the exact per-query coefficient `K`. -/
theorem probEvent_keygenAlias_program_guess (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : Query C) :
    Pr[fun parts => q ∈ keygenProgrammingInputs D (keygenProgramView D parts log sent) |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      keygenProgrammingCount D * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let sd := Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))
  have he : (fun parts => q ∈ keygenProgrammingInputs D (keygenProgramView D parts log sent)) =
      (fun parts => keygenParameterProgrammingInput D (keygenProgramView D parts log sent) = q ∨
        (∃ T ∈ keygenKnownCoordinates D,
          keygenTermProgrammingInput D (keygenProgramView D parts log sent) T = q) ∨
        ∃ p ∈ keygenCrossCoordinates D,
          keygenPairProgrammingInput D (keygenProgramView D parts log sent) p = q) := by
    funext parts
    simp [keygenProgrammingInputs, eq_comm]
  rw [he]
  refine (probEvent_or_le _ _ _).trans ?_
  refine le_trans (add_le_add (probEvent_keygenAlias_parameter_guess D log sent q)
    ((probEvent_or_le _ _ _).trans (add_le_add
      (alias_prob_exists_list (keygenKnownCoordinates D) sd _ _
        (fun T _ => probEvent_keygenAlias_term_guess D log sent T q))
      (alias_prob_exists_list (keygenCrossCoordinates D) sd _ _
        (fun p hp => probEvent_keygenAlias_pair_guess D log sent p (keygenAlias_cross_honest D p hp) q))))) ?_
  simp [keygenProgrammingCount, Nat.cast_add, add_mul, add_assoc]

theorem keygenAlias_term_shift_other (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (T U : C.Term) (hTU : T ≠ U)
    (a : C.Party) (c : HashOutput) (parts : C.Party → Parts C) :
    keygenTermProgrammingInput D (keygenProgramView D (shiftAt a (some T) none c parts) log sent) U =
      keygenTermProgrammingInput D (keygenProgramView D parts log sent) U := by
  unfold keygenTermProgrammingInput
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j ∈ D.1 <;> by_cases hja : j = a <;>
    simp_all [keygenProgramView, shiftAt, shiftParts]

theorem probEvent_keygenAlias_term_collision (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (T U : C.Term) :
    Pr[fun parts => T ≠ U ∧
        keygenTermProgrammingInput D (keygenProgramView D parts log sent) T =
          keygenTermProgrammingInput D (keygenProgramView D parts log sent) U |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hTU : T = U
  · simp [hTU]
  obtain ⟨a, ha, hD⟩ := keygen_honest_holder D T
  calc
    _ ≤ Pr[fun parts => (parts a).term T =
        keygenAliasValue (keygenTermProgrammingInput D (keygenProgramView D parts log sent) U)
          ((C.parties.filter (· ∈ C.holders T)).idxOf a) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
      apply probEvent_mono
      intro parts _ he
      rw [← he.2, keygenAlias_term_coordinate D log sent parts T a ha hD]
    _ = _ := probEvent_parts_collision (fun parts => (parts a).term T)
      (fun parts => keygenAliasValue (keygenTermProgrammingInput D (keygenProgramView D parts log sent) U)
        ((C.parties.filter (· ∈ C.holders T)).idxOf a)) a (some T) none
      (fun c parts => by simp [shiftAt, shiftParts])
      (fun c parts => by rw [keygenAlias_term_shift_other D log sent T U hTU a c parts])

theorem keygenAlias_pair_shift_other (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (p r : C.Pair) (hpr : p ≠ r)
    (a b : C.Party) (hab : (a = p.1.1 ∧ b = p.1.2) ∨ (a = p.1.2 ∧ b = p.1.1))
    (c : HashOutput) (parts : C.Party → Parts C) :
    keygenPairProgrammingInput D (keygenProgramView D (shiftAt a none (some b) c parts) log sent) r =
      keygenPairProgrammingInput D (keygenProgramView D parts log sent) r := by
  have h₁ : ¬ (r.1.1 = a ∧ r.1.2 = b) := by
    rintro ⟨e₁, e₂⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpr (Subtype.ext (Prod.ext e₁.symm e₂.symm))
    · exact lt_asymm p.2 (by simpa only [e₁, e₂] using r.2)
  have h₂ : ¬ (r.1.2 = a ∧ r.1.1 = b) := by
    rintro ⟨e₁, e₂⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact lt_asymm p.2 (by simpa only [e₁, e₂] using r.2)
    · exact hpr (Subtype.ext (Prod.ext e₂.symm e₁.symm))
  have hv (i j k : C.Party) (hjk : ¬ (j = a ∧ k = b)) :
      (keygenProgramView D (shiftAt a none (some b) c parts) log sent i j).pair k =
        (keygenProgramView D parts log sent i j).pair k := by
    by_cases hj : j ∈ D.1 <;> by_cases hja : j = a <;> by_cases hkb : k = b <;>
      simp_all [keygenProgramView, shiftAt, shiftParts, eq_comm]
  simp only [keygenPairProgrammingInput, hv _ _ _ h₁, hv _ _ _ h₂]

theorem probEvent_keygenAlias_pair_collision (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (p r : C.Pair) (hp : p.1.1 ∉ D.1 ∨ p.1.2 ∉ D.1) :
    Pr[fun parts => p ≠ r ∧
        keygenPairProgrammingInput D (keygenProgramView D parts log sent) p =
          keygenPairProgrammingInput D (keygenProgramView D parts log sent) r |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hpr : p = r
  · simp [hpr]
  rcases hp with ha | hb
  · calc
      _ ≤ Pr[fun parts => (parts p.1.1).pair p.1.2 = keygenAliasValue
          (keygenPairProgrammingInput D (keygenProgramView D parts log sent) r) 0 |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        apply probEvent_mono
        intro parts _ he
        rw [← he.2]
        simp [keygenAliasValue, keygenPairProgrammingInput, keygenProgramView, ha]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.1).pair p.1.2)
        (fun parts => keygenAliasValue
          (keygenPairProgrammingInput D (keygenProgramView D parts log sent) r) 0)
        p.1.1 none (some p.1.2) (fun c parts => by simp [shiftAt, shiftParts])
        (fun c parts => by rw [keygenAlias_pair_shift_other D log sent p r hpr _ _ (Or.inl ⟨rfl, rfl⟩)])
  · calc
      _ ≤ Pr[fun parts => (parts p.1.2).pair p.1.1 = keygenAliasValue
          (keygenPairProgrammingInput D (keygenProgramView D parts log sent) r) 1 |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        apply probEvent_mono
        intro parts _ he
        rw [← he.2]
        simp [keygenAliasValue, keygenPairProgrammingInput, keygenProgramView, hb]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.2).pair p.1.1)
        (fun parts => keygenAliasValue
          (keygenPairProgrammingInput D (keygenProgramView D parts log sent) r) 1)
        p.1.2 none (some p.1.1) (fun c parts => by simp [shiftAt, shiftParts])
        (fun c parts => by rw [keygenAlias_pair_shift_other D log sent p r hpr _ _ (Or.inr ⟨rfl, rfl⟩)])

theorem keygenAlias_inputs_nodup (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (hT : ∀ T ∈ keygenKnownCoordinates D, ∀ U ∈ keygenKnownCoordinates D,
      keygenTermProgrammingInput D view T = keygenTermProgrammingInput D view U → T = U)
    (hP : ∀ p ∈ keygenCrossCoordinates D, ∀ r ∈ keygenCrossCoordinates D,
      keygenPairProgrammingInput D view p = keygenPairProgrammingInput D view r → p = r) :
    (keygenProgrammingInputs D view).Nodup := by
  unfold keygenProgrammingInputs
  rw [List.cons_append, List.nodup_cons, List.nodup_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [keygenParameterProgrammingInput, keygenTermProgrammingInput, keygenPairProgrammingInput]
  · exact (List.nodup_map_iff_inj_on (keygenKnownCoordinates_nodup D)).2 hT
  · exact (List.nodup_map_iff_inj_on (keygenCrossCoordinates_nodup D)).2 hP
  · intro x hx y hy he
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hy
    simp [keygenTermProgrammingInput, keygenPairProgrammingInput] at he

/-- For a fixed transcript, the birthday term only counts the actual programming coordinates. -/
theorem probEvent_keygenAlias_inputs_collision (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) :
    Pr[fun parts => ¬ (keygenProgrammingInputs D (keygenProgramView D parts log sent)).Nodup |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (keygenProgrammingCount D : ℝ≥0∞) ^ 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let sd := Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))
  let ε : ℝ≥0∞ := (Fintype.card HashOutput : ℝ≥0∞)⁻¹
  let ts := keygenKnownCoordinates D
  let ps := keygenCrossCoordinates D
  calc
    _ ≤ Pr[fun parts =>
        (∃ T ∈ ts, ∃ U ∈ ts, T ≠ U ∧
          keygenTermProgrammingInput D (keygenProgramView D parts log sent) T =
            keygenTermProgrammingInput D (keygenProgramView D parts log sent) U) ∨
        (∃ p ∈ ps, ∃ r ∈ ps, p ≠ r ∧
          keygenPairProgrammingInput D (keygenProgramView D parts log sent) p =
            keygenPairProgrammingInput D (keygenProgramView D parts log sent) r) | sd] := by
      apply probEvent_mono
      intro parts _ hbad
      by_contra hn
      push Not at hn
      exact hbad (keygenAlias_inputs_nodup D _
        (fun T hT U hU he => by_contra fun hne => hn.1 T hT U hU hne he)
        (fun p hp r hr he => by_contra fun hne => hn.2 p hp r hr hne he))
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ ts.length * (ts.length * ε) + ps.length * (ps.length * ε) := by
      apply add_le_add
      · exact alias_prob_exists_list ts sd _ _ fun T _ =>
          alias_prob_exists_list ts sd _ _ fun U _ => probEvent_keygenAlias_term_collision D log sent T U
      · exact alias_prob_exists_list ps sd _ _ fun p hp =>
          alias_prob_exists_list ps sd _ _ fun r _ =>
            probEvent_keygenAlias_pair_collision D log sent p r (keygenAlias_cross_honest D p hp)
    _ = ((ts.length ^ 2 + ps.length ^ 2 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring
    _ ≤ _ := by
      apply mul_le_mul_left
      rw [← Nat.cast_pow]
      exact_mod_cast (show ts.length ^ 2 + ps.length ^ 2 ≤ keygenProgrammingCount D ^ 2 by
        dsimp [ts, ps, keygenProgrammingCount]
        nlinarith [Nat.zero_le ((keygenKnownCoordinates D).length * (keygenCrossCoordinates D).length)])

/-- The hybrid's bad event combines commitment hits and programming aliases. These query classes
are disjoint, so combining them does not increase the coefficient of the query budget. -/
def KeygenAliasHybridBad (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) : Prop :=
  (∃ v ∈ log, KeygenAliasCommitHit D parts v.1 ∨
    v.1 ∈ keygenProgrammingInputs D (keygenProgramView D parts log sent)) ∨
  ¬ (keygenProgrammingInputs D (keygenProgramView D parts log sent)).Nodup

theorem probEvent_keygenAlias_hit_guess (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : Query C) :
    Pr[fun parts => KeygenAliasCommitHit D parts q ∨
        q ∈ keygenProgrammingInputs D (keygenProgramView D parts log sent) |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      keygenProgrammingCount D * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hd : ∃ kind values, q = .derive .keygen kind values
  · obtain ⟨kind, values, rfl⟩ := hd
    simpa only [KeygenAliasCommitHit, false_or] using
      probEvent_keygenAlias_program_guess D log sent (.derive .keygen kind values)
  · have he : ∀ parts, q ∉ keygenProgrammingInputs D (keygenProgramView D parts log sent) := by
      intro parts hq
      exact hd (keygenProgrammingInputs_derive D _ q hq)
    simp only [he, or_false]
    refine (probEvent_keygenAlias_commit_guess D q).trans ?_
    calc
      _ = (1 : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := (one_mul _).symm
      _ ≤ _ := mul_le_mul_left (by exact_mod_cast (show 1 ≤ keygenProgrammingCount D by
        unfold keygenProgrammingCount; omega)) _

theorem keygenAlias_hit_not_fixed (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (q : Query C)
    (hq : KeygenAliasCommitHit D parts q ∨
      q ∈ keygenProgrammingInputs D (keygenProgramView D parts log sent)) : ¬ IsFixed q := by
  rcases hq with hq | hq
  · rintro ⟨input, rfl, _⟩
    exact hq
  · exact keygenProgrammingInputs_not_fixed D _ q hq

theorem probEvent_keygenAlias_hybrid_fixed (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : ℕ)
    (hq : (log.filter fun v => ¬ IsFixed v.1).length ≤ q) :
    Pr[fun parts => KeygenAliasHybridBad D parts log sent |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      ((q * keygenProgrammingCount D + keygenProgrammingCount D ^ 2 : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let L := log.filter fun v => ¬ IsFixed v.1
  have he (parts : C.Party → Parts C) :
      (∃ v ∈ log, KeygenAliasCommitHit D parts v.1 ∨
        v.1 ∈ keygenProgrammingInputs D (keygenProgramView D parts log sent)) ↔
      (∃ v ∈ L, KeygenAliasCommitHit D parts v.1 ∨
        v.1 ∈ keygenProgrammingInputs D (keygenProgramView D parts log sent)) := by
    constructor
    · rintro ⟨v, hv, hh⟩
      exact ⟨v, List.mem_filter.mpr ⟨hv, by simpa using keygenAlias_hit_not_fixed D parts log sent v.1 hh⟩, hh⟩
    · rintro ⟨v, hv, hh⟩
      exact ⟨v, (List.mem_filter.mp hv).1, hh⟩
  unfold KeygenAliasHybridBad
  simp only [he]
  refine (probEvent_or_le _ _ _).trans ?_
  refine le_trans (add_le_add
    (alias_prob_exists_list L _ _ _ (fun v _ => probEvent_keygenAlias_hit_guess D log sent v.1))
    (probEvent_keygenAlias_inputs_collision D log sent)) ?_
  calc
    _ ≤ (q : ℝ≥0∞) * (keygenProgrammingCount D * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        keygenProgrammingCount D ^ 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
      gcongr
    _ = _ := by push_cast; ring

theorem probEvent_keygenAlias_independent (D : C.Coalition)
    (transcript : ProbComp (CallLog C × (C.Party → Mail C E))) (q : ℕ)
    (hq : ∀ r ∈ support transcript, (r.1.filter fun v => ¬ IsFixed v.1).length ≤ q) :
    Pr[fun p => KeygenAliasHybridBad D p.1 p.2.1 p.2.2 |
      keygenPartsKernel (fun _ => transcript)] ≤
      ((q * keygenProgrammingCount D + keygenProgrammingCount D ^ 2 : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  unfold keygenPartsKernel
  rw [probEvent_congr_evalDist (DeferredSampling.evalDist_bind_comm _ _ _)]
  apply probEvent_bind_le_const
  intro r hr
  rw [bind_pure_comp, probEvent_map]
  exact probEvent_keygenAlias_hybrid_fixed D r.1 r.2 q (hq r hr)

def keygenAliasQueryLog (t : (LocalSpec C).Domain) (u : (LocalSpec C).Range t) : CallLog C :=
  match t with
  | .inr (.inl q) => [(q, u)]
  | _ => []

theorem keygenAlias_observe_query_bind {α : Type} (t : (LocalSpec C).Domain)
    (k : (LocalSpec C).Range t → OracleComp (LocalSpec C) α) :
    observe (OracleComp.lift (OracleSpec.query t) >>= k) = (do
      let u ← worldRoles.adversary (OracleComp.lift (OracleSpec.query t))
      let r ← observe (k u)
      pure (r.1, keygenAliasQueryLog t u ++ r.2)) := by
  simp only [observe, simulateQ_bind, WriterT.run_bind, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, id_map]
  rcases t with t | (q | x) <;>
    simp [keygenAliasQueryLog, WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell]
  rfl

theorem keygenAlias_queryLog_length (t : (LocalSpec C).Domain) (u : (LocalSpec C).Range t) :
    ((keygenAliasQueryLog t u).filter fun v => ¬ IsFixed v.1).length ≤
      if Counted t then 1 else 0 := by
  rcases t with t | (q | x)
  · simp [keygenAliasQueryLog, Counted]
  · cases q with
    | hash input =>
      have hf : IsFixed (Query.hash (C := C) input) ↔ MpcInput input := by simp [IsFixed]
      by_cases hi : MpcInput input <;> simp [keygenAliasQueryLog, Counted, hf, hi]
    | _ => simp [keygenAliasQueryLog, Counted, IsFixed]
  · simp [keygenAliasQueryLog]

theorem keygenAlias_observe_length {α : Type} (oa : OracleComp (LocalSpec C) α)
    (n : ℕ) (hn : IsQueryBoundP oa Counted n) (r : α × CallLog C)
    (hr : r ∈ support (observe oa)) : (r.2.filter fun v => ¬ IsFixed v.1).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure a =>
    simp only [observe, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [keygenAlias_observe_query_bind] at hr
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, _, s, hs, rfl⟩ := hr
    have hrest := ih u _ (hn.2 u) s hs
    have hcall := keygenAlias_queryLog_length t u
    simp only [List.filter_append, List.length_append]
    by_cases ht : Counted t
    · have hn0 : 0 < n := hn.1.resolve_left (not_not.mpr ht)
      simp only [if_pos ht] at hrest hcall
      omega
    · simp only [if_neg ht] at hrest hcall
      omega

/-- The independent transcript uses fresh uncached honest commitments. -/
def keygenAliasFreshTranscript (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) : OracleComp (WorldSpec C) (CallLog C × (C.Party → Mail C E)) := do
  let (state, log) ← observe (A.start (corruptInputs D x) z)
  let commitments ← free (liftComp (Concrete.sequenceFin fun i : C.Party =>
    if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput)) (LocalSpec C))
  let ((_, sent), calls) ← observe (A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    commitOutbox i (commitments i) c else none)
  pure (log ++ calls, sent)

theorem keygenAliasFreshTranscript_length (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) (r : CallLog C × (C.Party → Mail C E))
    (hr : r ∈ support (keygenAliasFreshTranscript D A x z)) :
    (r.1.filter fun v => ¬ IsFixed v.1).length ≤ q := by
  obtain ⟨start, step, final, htotal, hstart, hround, _⟩ := hq
  unfold keygenAliasFreshTranscript at hr
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨⟨state, log⟩, hlog, commitments, _, ⟨⟨st, sent⟩, calls⟩, hcalls, rfl⟩ := hr
  have h₁ := keygenAlias_observe_length _ start (hstart (corruptInputs D x) z) _ hlog
  have h₂ := keygenAlias_observe_length _ step (hround state _) _ hcalls
  simp only [List.filter_append, List.length_append]
  dsimp only at h₁ h₂
  simp only [setupRounds] at htotal
  omega

theorem probEvent_keygenAlias_fresh (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    Pr[fun p => KeygenAliasHybridBad D p.1 p.2.1 p.2.2 |
      keygenPartsKernel (fun _ =>
        (simulateQ (worldAnswer prims) (keygenAliasFreshTranscript D A x z)).run' ∅)] ≤
      ((q * keygenProgrammingCount D + keygenProgrammingCount D ^ 2 : ℕ) : ℝ≥0∞) /
        2 ^ 256 := by
  have hb := probEvent_keygenAlias_independent D
    ((simulateQ (worldAnswer prims) (keygenAliasFreshTranscript D A x z)).run' ∅) q
    (fun r hr => keygenAliasFreshTranscript_length D A x z Z q hq r
      (support_simulateQ_run'_subset _ _ _ hr))
  have hc : Fintype.card HashOutput = 2 ^ 256 := by
    unfold HashOutput hashOutputBits
    exact card_bitVec 256
  simpa only [hc, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hb

/-- Sender and receiver tags make the honest commitment cells distinct for every choice of parts. -/
def keygenAliasCommitCell (parts : C.Party → Parts C) (ij : C.Party × C.Party) : Query C :=
  .commit .keygen ij.1 ij.2 (revealTo .keygen (parts ij.1) ij.1 ij.2)

theorem keygenAliasCommitCell_injective (parts : C.Party → Parts C) :
    Function.Injective (keygenAliasCommitCell parts) := by
  intro a b he
  simp only [keygenAliasCommitCell, Query.commit.injEq] at he
  exact Prod.ext he.2.1 he.2.2.1

theorem keygenAlias_cache_update_agrees (P : Query C → Prop) (s t : HashCache C)
    (hst : ∀ v, ¬ P v → s v = t v) (q : Query C) (u : HashOutput) :
    ∀ v, ¬ P v → (s.cacheQuery q u) v = (t.cacheQuery q u) v := by
  intro v hv
  by_cases he : v = q
  · subst v
    simp
  · rw [QueryCache.cacheQuery_of_ne _ _ he, QueryCache.cacheQuery_of_ne _ _ he]
    exact hst v hv

theorem relTriple_keygenAlias_hash_off (prims : Primitives) (P : Query C → Prop)
    (s t : HashCache C) (hst : ∀ v, ¬ P v → s v = t v) (q : Query C) (hq : ¬ P q) :
    RelTriple ((hashAnswer prims q).run s) ((hashAnswer prims q).run t)
      (fun a b => a.1 = b.1 ∧ ∀ v, ¬ P v → a.2 v = b.2 v) := by
  by_cases hfix : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hfix
    rw [hashAnswer_of_isFixed prims hm]
    exact relTriple_pure_pure ⟨rfl, hst⟩
  rw [hashAnswer_of_not_isFixed prims hfix, OracleSpec.randomOracle]
  have hqt := (hst q hq).symm
  cases hs : s q with
  | none =>
    rw [QueryImpl.withCaching_run_none _ hs, QueryImpl.withCaching_run_none _ (hqt.trans hs)]
    apply relTriple_map
    apply relTriple_post_mono (relTriple_refl ($ᵗ HashOutput))
    intro a b he
    subst b
    exact ⟨rfl, keygenAlias_cache_update_agrees P s t hst q a⟩
  | some y =>
    rw [QueryImpl.withCaching_run_some _ hs, QueryImpl.withCaching_run_some _ (hqt.trans hs)]
    exact relTriple_pure_pure ⟨rfl, hst⟩

theorem relTriple_keygenAlias_local_off (prims : Primitives) (P : Query C → Prop)
    (s t : HashCache C) (hst : ∀ v, ¬ P v → s v = t v)
    (u : (LocalSpec C).Domain) (hu : ¬ KeygenTouches P u) :
    RelTriple ((localAnswer prims u).run s) ((localAnswer prims u).run t)
      (fun a b => a.1 = b.1 ∧ ∀ v, ¬ P v → a.2 v = b.2 v) := by
  rcases u with n | (q | x)
  · change RelTriple ((fun y => (y, s)) <$> (query (spec := unifSpec) n))
      ((fun y => (y, t)) <$> (query (spec := unifSpec) n)) _
    apply relTriple_map
    exact relTriple_post_mono (relTriple_refl _) (fun _ _ he => ⟨he, hst⟩)
  · exact relTriple_keygenAlias_hash_off prims P s t hst q
      (fun hq => hu ⟨q, by simp [keygenLocalHashInputs], hq⟩)
  · have hx : ¬ P (.streamKey x.2.1) := fun hx => hu ⟨_, by simp [keygenLocalHashInputs], hx⟩
    change RelTriple ((prgAnswer prims x).run s) ((prgAnswer prims x).run t) _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (relTriple_keygenAlias_hash_off prims P s t hst _ hx)
    intro a b hab
    apply relTriple_pure_pure
    exact ⟨by rw [hab.1], hab.2⟩

theorem keygenAlias_observe_run_query_bind (prims : Primitives) {α : Type}
    (u : (LocalSpec C).Domain) (k : (LocalSpec C).Range u → OracleComp (LocalSpec C) α)
    (s : HashCache C) :
    (simulateQ (worldAnswer prims) (observe (OracleComp.lift (OracleSpec.query u) >>= k))).run s =
      ((localAnswer prims u).run s >>= fun a =>
        (simulateQ (worldAnswer prims) (observe (k a.1))).run a.2 >>= fun r =>
          pure ((r.1.1, keygenAliasQueryLog u a.1 ++ r.1.2), r.2)) := by
  rw [keygenAlias_observe_query_bind]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    simulateQ_world_adversary, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]

theorem keygenAlias_touches_logged (D : C.Coalition) (parts : C.Party → Parts C)
    (u : (LocalSpec C).Domain) (hu : KeygenTouches (KeygenAliasCommitHit D parts) u)
    (a : (LocalSpec C).Range u) : ∃ v ∈ keygenAliasQueryLog u a, KeygenAliasCommitHit D parts v.1 := by
  rcases u with n | (q | x)
  · simp [KeygenTouches, keygenLocalHashInputs] at hu
  · have hq : KeygenAliasCommitHit D parts q := by
      simpa [KeygenTouches, keygenLocalHashInputs] using hu
    exact ⟨(q, a), by simp [keygenAliasQueryLog], hq⟩
  · simp [KeygenTouches, keygenLocalHashInputs, KeygenAliasCommitHit] at hu

/-- Adaptive observed computations agree off the honest commitment cells until the left log
contains one of those cells. The relation preserves the complete observed answer log. -/
theorem relTriple_keygenAlias_observe (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ s t : HashCache C, (∀ v, ¬ KeygenAliasCommitHit D parts v → s v = t v) →
      RelTriple ((simulateQ (worldAnswer prims) (observe oa)).run s)
        ((simulateQ (worldAnswer prims) (observe oa)).run t)
        (fun a b => (∃ v ∈ a.1.2, KeygenAliasCommitHit D parts v.1) ∨
          (a.1 = b.1 ∧ ∀ v, ¬ KeygenAliasCommitHit D parts v → a.2 v = b.2 v)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s t hst
    simp only [observe, simulateQ_pure, WriterT.run_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨rfl, hst⟩)
  | query_bind u k ih =>
    intro s t hst
    rw [keygenAlias_observe_run_query_bind, keygenAlias_observe_run_query_bind]
    by_cases hu : KeygenTouches (KeygenAliasCommitHit D parts) u
    · apply relTriple_of_support_left
      intro r hr b
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨a, _, z, _, rfl⟩ := hr
      obtain ⟨v, hv, hp⟩ := keygenAlias_touches_logged D parts u hu a.1
      exact Or.inl ⟨v, List.mem_append_left _ hv, hp⟩
    · apply relTriple_bind (relTriple_keygenAlias_local_off prims (KeygenAliasCommitHit D parts) s t hst u hu)
      rintro ⟨a, s'⟩ ⟨b, t'⟩ ⟨he, hst'⟩
      dsimp only at he hst' ⊢
      subst b
      apply relTriple_bind (ih a s' t' hst')
      intro r z hrz
      apply relTriple_pure_pure
      rcases hrz with ⟨v, hv, hp⟩ | ⟨he, hc⟩
      · exact Or.inl ⟨v, List.mem_append_right _ hv, hp⟩
      · exact Or.inr ⟨by rw [he], hc⟩

theorem keygenAlias_start_fresh (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) {α : Type} (oa : OracleComp (LocalSpec C) α)
    (w : (α × CallLog C) × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (observe oa)).run ∅))
    (hlog : ¬ ∃ v ∈ w.1.2, KeygenAliasCommitHit D parts v.1) :
    ∀ v, KeygenAliasCommitHit D parts v → w.2 v = none := by
  intro v hv
  by_contra hn
  rcases keygenObserve_new_logged prims oa ∅ w hw v rfl hn with ⟨y, hy⟩ | ⟨k, rfl⟩
  · exact hlog ⟨(v, y), hy, hv⟩
  · exact hv

/-- A block of distinct fresh commitment cells can be sampled independently. The final cache
agrees with its initial value at every cell outside the block. -/
theorem relTriple_keygenAlias_fresh_hashes (prims : Primitives) (qs : List (Query C)) :
    ∀ (s : HashCache C), qs.Nodup → (∀ q ∈ qs, s q = none) → (∀ q ∈ qs, ¬ IsFixed q) →
      RelTriple (qs.mapM fun _ => ($ᵗ HashOutput)) ((qs.mapM (hashAnswer prims)).run s)
        (fun a b => a = b.1 ∧ ∀ v, v ∉ qs → s v = b.2 v) := by
  induction qs with
  | nil =>
    intro s _ _ _
    simp only [List.mapM_nil, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, fun _ _ => rfl⟩
  | cons q qs ih =>
    intro s hnd hfresh hfix
    have hn := List.nodup_cons.mp hnd
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
    rw [hashAnswer_of_not_isFixed prims (hfix q (by simp)), OracleSpec.randomOracle,
      QueryImpl.withCaching_run_none _ (hfresh q (by simp)), bind_map_left]
    apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
    intro a b hab
    subst b
    have hs : ∀ v ∈ qs, (s.cacheQuery q a) v = none := by
      intro v hv
      have hvq : v ≠ q := fun he => hn.1 (he ▸ hv)
      rw [QueryCache.cacheQuery_of_ne _ _ hvq]
      exact hfresh v (by simp [hv])
    apply relTriple_bind (ih (s.cacheQuery q a) hn.2 hs (fun v hv => hfix v (by simp [hv])))
    intro r z hrz
    apply relTriple_pure_pure
    refine ⟨by rw [hrz.1], ?_⟩
    intro v hv
    have hvq : v ≠ q := fun he => hv (he ▸ List.mem_cons_self ..)
    have hvs : v ∉ qs := fun hm => hv (List.mem_cons_of_mem q hm)
    rw [← hrz.2 v hvs, QueryCache.cacheQuery_of_ne _ _ hvq]

theorem relTriple_keygenAlias_fresh_blocks (prims : Primitives) :
    ∀ (n : ℕ) (qs : Fin n → List (Query C)) (s : HashCache C),
      (∀ i, (qs i).Nodup) → (∀ i j, i ≠ j → (qs i).Disjoint (qs j)) →
      (∀ i q, q ∈ qs i → s q = none) → (∀ i q, q ∈ qs i → ¬ IsFixed q) →
      RelTriple (Concrete.sequenceFin fun i => (qs i).mapM fun _ => ($ᵗ HashOutput))
        ((Concrete.sequenceFin fun i => (qs i).mapM (hashAnswer prims)).run s)
        (fun a b => a = b.1 ∧ ∀ v, (∀ i, v ∉ qs i) → s v = b.2 v) := by
  intro n
  induction n with
  | zero =>
    intro qs s _ _ _ _
    exact relTriple_pure_pure ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro qs s hnd hdis hfresh hfix
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (relTriple_keygenAlias_fresh_hashes prims (qs 0) s (hnd 0) (hfresh 0) (hfix 0))
    rintro a ⟨b, t⟩ ⟨he, ht⟩
    dsimp only at he ht ⊢
    subst b
    have htail (i : Fin n) (q : Query C) (hq : q ∈ qs i.succ) : t q = none := by
      have hq0 : q ∉ qs 0 := fun hq0 => hdis 0 i.succ (Ne.symm (Fin.succ_ne_zero i)) hq0 hq
      rw [← ht q hq0]
      exact hfresh i.succ q hq
    apply relTriple_bind (ih (fun i => qs i.succ) t (fun i => hnd i.succ)
      (fun i j hij => hdis i.succ j.succ (fun he => hij (Fin.succ_injective _ he))) htail
      (fun i => hfix i.succ))
    intro r z hrz
    apply relTriple_pure_pure
    refine ⟨by rw [hrz.1], ?_⟩
    intro v hv
    exact (ht v (hv 0)).trans (hrz.2 v (fun i => hv i.succ))

def keygenAliasCommitQueries (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) :
    List (Query C) :=
  if i ∈ D.1 then [] else C.parties.map fun j => keygenAliasCommitCell parts (i, j)

theorem keygenAliasCommitQueries_mem (D : C.Coalition) (parts : C.Party → Parts C)
    (i : C.Party) (q : Query C) :
    q ∈ keygenAliasCommitQueries D parts i ↔
      i ∉ D.1 ∧ ∃ j, q = keygenAliasCommitCell parts (i, j) := by
  by_cases hi : i ∈ D.1 <;> simp [keygenAliasCommitQueries, hi, Committee.parties, eq_comm]

theorem relTriple_keygenAlias_initial (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (s : HashCache C)
    (hfresh : ∀ v, KeygenAliasCommitHit D parts v → s v = none) :
    RelTriple (Concrete.sequenceFin fun i : C.Party =>
        if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput))
      ((simulateQ (localAnswer prims) (keygenInitialCommitments D parts)).run s)
      (fun a b => a = b.1 ∧ ∀ v, ¬ KeygenAliasCommitHit D parts v → s v = b.2 v) := by
  have hl : (Concrete.sequenceFin fun i : C.Party =>
      (keygenAliasCommitQueries D parts i).mapM fun _ => ($ᵗ HashOutput)) =
      (Concrete.sequenceFin fun i : C.Party =>
        if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput)) := by
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp [keygenAliasCommitQueries, hi, List.mapM_map, Function.comp_def]
  have hr : simulateQ (localAnswer prims) (keygenInitialCommitments D parts) =
      Concrete.sequenceFin fun i : C.Party => (keygenAliasCommitQueries D parts i).mapM (hashAnswer prims) := by
    rw [keygenInitialCommitments, simulateQ_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi, keygenAliasCommitQueries]
    · simp only [hi, if_false, keygenAliasCommitQueries]
      have he : commitQueries .keygen i (parts i) =
          (C.parties.map fun j => keygenAliasCommitCell parts (i, j)).mapM hashQuery := by
        simp [commitQueries, List.mapM_map, keygenAliasCommitCell, Function.comp_def]
      rw [he, simulateQ_localAnswer_hashes]
  rw [hr, ← hl]
  refine relTriple_post_mono (relTriple_keygenAlias_fresh_blocks prims C.n
    (keygenAliasCommitQueries D parts) s ?_ ?_ ?_ ?_) ?_
  · intro i
    by_cases hi : i ∈ D.1
    · simp [keygenAliasCommitQueries, hi]
    · simp only [keygenAliasCommitQueries, hi, if_false]
      exact (List.nodup_finRange C.n).map (fun j k he =>
        (Prod.mk.inj (keygenAliasCommitCell_injective parts he)).2)
  · intro i j hij q hqi hqj
    obtain ⟨_, k, rfl⟩ := (keygenAliasCommitQueries_mem D parts i q).mp hqi
    obtain ⟨_, l, he⟩ := (keygenAliasCommitQueries_mem D parts j _).mp hqj
    exact hij (Prod.mk.inj (keygenAliasCommitCell_injective parts he)).1
  · intro i q hq
    obtain ⟨hi, j, rfl⟩ := (keygenAliasCommitQueries_mem D parts i q).mp hq
    exact hfresh _ ⟨hi, rfl⟩
  · intro i q hq
    obtain ⟨_, j, rfl⟩ := (keygenAliasCommitQueries_mem D parts i q).mp hq
    simp [keygenAliasCommitCell, IsFixed]
  · intro a b hab
    refine ⟨hab.1, fun v hv => hab.2 v (fun i hm => ?_)⟩
    obtain ⟨hi, j, rfl⟩ := (keygenAliasCommitQueries_mem D parts i v).mp hm
    exact hv ⟨hi, rfl⟩

def keygenAliasFreshTail (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (parts : C.Party → Parts C)
    (st : (A.State × CallLog C) × HashCache C) :
    ProbComp ((C.Party → Parts C) × CallLog C × (C.Party → Mail C E)) := do
  let commitments ← Concrete.sequenceFin fun i : C.Party =>
    if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput)
  let r ← (simulateQ (worldAnswer prims) (observe (A.round st.1.1 fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 then commitOutbox i (commitments i) c else none))).run st.2
  pure (parts, st.1.2 ++ r.1.2, r.1.1.2)

def keygenAliasKnownTail (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (parts : C.Party → Parts C)
    (st : (A.State × CallLog C) × HashCache C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    ProbComp (KeygenKnownPre C E A.State × HashCache C) := do
  let com ← (simulateQ (localAnswer prims) (keygenInitialCommitments D parts)).run st.2
  let r ← (simulateQ (worldAnswer prims) (observe (A.round st.1.1 fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 then commitOutbox i (com.1 i) c else none))).run com.2
  let high ← $ᵗ HashOutput
  let ok ← (simulateQ (worldAnswer prims)
    (keygenProgramOk D parts (st.1.2 ++ r.1.2) r.1.1.2 parameter seeds pairs high)).run r.2
  pure (⟨parameter, seeds, pairs, parts, st.1.2 ++ r.1.2, r.1.1.2, com.1, ok.1, r.1.1.1⟩, ok.2)

theorem evalDist_keygenAlias_fresh_start (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    𝒟[keygenPartsKernel (fun _ =>
      (simulateQ (worldAnswer prims) (keygenAliasFreshTranscript D A x z)).run' ∅)] =
    𝒟[do
      let st ← (simulateQ (worldAnswer prims) (observe (A.start (corruptInputs D x) z))).run ∅
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      keygenAliasFreshTail prims D A parts st] := by
  unfold keygenPartsKernel keygenAliasFreshTranscript keygenAliasFreshTail
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_world_sample, StateT.run'_eq,
    StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure]
  rw [DeferredSampling.evalDist_bind_comm]

theorem keygenAlias_known_start (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    (simulateQ (worldAnswer prims) (keygenKnownPrefix D A x z)).run ∅ = (do
      let st ← (simulateQ (worldAnswer prims) (observe (A.start (corruptInputs D x) z))).run ∅
      let dealer ← keygenDealerSamples (C := C)
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      keygenAliasKnownTail prims D A parts st dealer.1 dealer.2.1 dealer.2.2) := by
  unfold keygenKnownPrefix keygenAliasKnownTail
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_world_sample, StateT.run_bind,
    StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  simp only [simulateQ_free]

theorem relTriple_keygenAlias_support {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : α → β → Prop} (h : RelTriple oa ob R) :
    RelTriple oa ob (fun a b => a ∈ support oa ∧ b ∈ support ob ∧ R a b) := by
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => ?_⟩
  have hl : z.1 ∈ support (Prod.fst <$> c.1) := by rw [support_map]; exact ⟨z, hz, rfl⟩
  have hr : z.2 ∈ support (Prod.snd <$> c.1) := by rw [support_map]; exact ⟨z, hz, rfl⟩
  rw [c.2.map_fst] at hl
  rw [c.2.map_snd] at hr
  exact ⟨(mem_support_evalDist_iff _ _).1 hl, (mem_support_evalDist_iff _ _).1 hr, hc z hz⟩

theorem relTriple_keygenAlias_tail (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (parts : C.Party → Parts C)
    (st : (A.State × CallLog C) × HashCache C)
    (hstart : (¬ ∃ v ∈ st.1.2, KeygenAliasCommitHit D parts v.1) →
      ∀ v, KeygenAliasCommitHit D parts v → st.2 v = none)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    RelTriple (keygenAliasFreshTail prims D A parts st)
      (keygenAliasKnownTail prims D A parts st parameter seeds pairs)
      (fun p w => (∃ v ∈ p.2.1, KeygenAliasCommitHit D p.1 v.1) ∨
        (w.1.parts = p.1 ∧ w.1.log = p.2.1 ∧ w.1.sent = p.2.2)) := by
  by_cases hhit : ∃ v ∈ st.1.2, KeygenAliasCommitHit D parts v.1
  · apply relTriple_of_support_left
    intro p hp w
    unfold keygenAliasFreshTail at hp
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨com, _, r, _, rfl⟩ := hp
    obtain ⟨v, hv, hh⟩ := hhit
    exact Or.inl ⟨v, List.mem_append_left _ hv, hh⟩
  unfold keygenAliasFreshTail keygenAliasKnownTail
  apply relTriple_bind (relTriple_keygenAlias_initial prims D parts st.2 (hstart hhit))
  rintro commitments ⟨com, cache⟩ ⟨he, hcache⟩
  dsimp only at he hcache ⊢
  subst com
  apply relTriple_bind (relTriple_keygenAlias_observe prims D parts _ st.2 cache hcache)
  intro r z hrz
  apply relTriple_post_mono (relTriple_keygenAlias_support (relTriple_true _ _))
  intro p w hpw
  rcases hpw with ⟨hp, hw, _⟩
  simp only [support_pure, Set.mem_singleton_iff] at hp
  subst p
  rcases hrz with ⟨v, hv, hh⟩ | ⟨he, _⟩
  · exact Or.inl ⟨v, List.mem_append_right _ hv, hh⟩
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨high, _, ok, _, rfl⟩ := hw
    exact Or.inr ⟨rfl, by rw [he], by rw [he]⟩

/-- Couple the real prefix to the independent fresh-commitment transcript.
The parts and the extraction transcript agree until a logged honest commitment input is hit. -/
def KeygenAliasPrefixCoupling (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux),
    RelTriple
      (keygenPartsKernel (fun _ =>
        (simulateQ (worldAnswer prims) (keygenAliasFreshTranscript D A x z)).run' ∅))
      ((simulateQ (worldAnswer prims) (keygenKnownPrefix D A x z)).run ∅)
      (fun p w => (∃ v ∈ p.2.1, KeygenAliasCommitHit D p.1 v.1) ∨
        (w.1.parts = p.1 ∧ w.1.log = p.2.1 ∧ w.1.sent = p.2.2))

theorem keygenAliasPrefixCoupling (prims : Primitives) :
    KeygenAliasPrefixCoupling (C := C) (E := E) prims := by
  intro D A x z
  apply relTriple_of_evalDist_eq_left (evalDist_keygenAlias_fresh_start prims D A x z)
  rw [keygenAlias_known_start]
  apply relTriple_bind (relTriple_keygenAlias_support (relTriple_refl _))
  intro st st' hst
  rcases hst with ⟨hsupport, _, he⟩
  subst st'
  rw [← pure_bind () (fun _ =>
    (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) >>=
      fun parts => keygenAliasFreshTail prims D A parts st)]
  apply relTriple_bind (relTriple_true _ _)
  intro _ dealer _
  apply relTriple_bind (relTriple_refl _)
  intro parts parts' he
  subst parts'
  exact relTriple_keygenAlias_tail prims D A parts st
    (fun hhit => keygenAlias_start_fresh prims D parts _ st hsupport hhit)
    dealer.1 dealer.2.1 dealer.2.2

theorem keygenProgramAliasBound (prims : Primitives) :
    KeygenProgramAliasBound (C := C) (E := E) prims := by
  intro D A x z Z q hq
  have hc : Pr[fun w => KeygenProgramAlias D w.1 |
      (simulateQ (worldAnswer prims) (keygenKnownPrefix D A x z)).run ∅] ≤
      Pr[fun p => KeygenAliasHybridBad D p.1 p.2.1 p.2.2 |
        keygenPartsKernel (fun _ =>
          (simulateQ (worldAnswer prims) (keygenAliasFreshTranscript D A x z)).run' ∅)] := by
    apply probEvent_le_of_relTriple (relTriple_symm (keygenAliasPrefixCoupling prims D A x z))
    intro w p hp hw
    rcases hp with ⟨v, hv, hh⟩ | ⟨hparts, hlog, hsent⟩
    · exact Or.inl ⟨v, hv, Or.inl hh⟩
    · unfold KeygenProgramAlias at hw
      rw [hparts, hlog, hsent] at hw
      rcases hw with ⟨v, hv, y, hy⟩ | hn
      · exact Or.inl ⟨(v, y), hy, Or.inr hv⟩
      · exact Or.inr hn
  have hb := hc.trans (probEvent_keygenAlias_fresh prims D A x z Z q hq)
  have hr := ENNReal.toReal_mono (by finiteness) hb
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using hr

theorem keygenSecurityClosed (prims : Primitives) :
    KeygenSecurityStatement (C := C) (E := E) prims :=
  keygenSecurityDone_of_programAlias prims (keygenProgramAliasBound prims)

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.keygenProgramAliasBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.keygenProgramAliasBound

/-- info: 'ThresholdLeanXmssSecurity.keygenSecurityClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.keygenSecurityClosed
