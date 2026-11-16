import ThresholdLeanXmssSecurity.Proof.SeedGenKnown
import ThresholdLeanXmssSecurity.Proof.Coupling
import XmssSecurity.Proof.Seeded.FreshTable

/-!
# The aliases of the programming inputs of a setup

Honest commitments are replaced by fresh uncached values. A coupling preserves the parts and the
complete observed transcript until a logged query hits an honest commitment input. Distinct sender
and receiver tags make the commitment inputs distinct. The cache remains equal elsewhere.

In the fresh-commitment prefix the transcript is independent of the parts. A commitment query costs
one honest pair part, and a derivation query costs at most `K` honest coordinates. These
query classes are disjoint, so each counted call costs at most `K / 2^256`. Distinct programming
inputs collide with probability at most `2^-256` per pair. The union bound is `(q * K + K^2) / 2^256`.

`setupProgramAliasBound` supplies the programming-input hypothesis of `setupSecurityDistance_of_programAlias`.
So `setupSecurityDistance` is the distance claim of a setup, and `seedGenSecurity` is its instance for the
seed generation.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- A proposed derivation exposes a proposed value at each position of its input. -/
def seedGenAliasValue (q : Query C) (k : ℕ) : HashOutput :=
  match q with
  | .derive _ _ values => values.getD k 0
  | _ => 0

theorem setupAlias_term_coordinate (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (parts : C.Party → Parts C) (T : C.Term)
    (a : C.Party) (ha : a ∈ C.holders T) (hD : a ∉ D.1) :
    seedGenAliasValue (setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) T)
      ((C.parties.filter (· ∈ C.holders T)).idxOf a) = (parts a).term T := by
  simp [setupTermProgrammingInput, seedGenAliasValue, Committee.parties, ha,
    setupProgramView, hD]

/-- For a fixed commit transcript, guessing a programmed term input costs one honest part. -/
theorem probEvent_setupAlias_term_guess (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (T : C.Term) (q : Query C) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) T = q] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  obtain ⟨a, ha, hD⟩ := seedGen_honest_holder D T
  calc
    _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
        (parts a).term T =
        seedGenAliasValue q ((C.parties.filter (· ∈ C.holders T)).idxOf a)] := by
      apply prEvent_mono
      intro parts he
      rw [← he, setupAlias_term_coordinate phase D log sent parts T a ha hD]
    _ = _ := probEvent_parts_collision (fun parts => (parts a).term T) (fun _ =>
        seedGenAliasValue q ((C.parties.filter (· ∈ C.holders T)).idxOf a)) a (some T) none
      (fun c parts => by simp [shiftAt, shiftParts]) (fun _ _ => rfl)

theorem probEvent_setupAlias_pair_guess (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (p : C.Pair)
    (hp : p.1.1 ∉ D.1 ∨ p.1.2 ∉ D.1) (q : Query C) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) p = q] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rcases hp with ha | hb
  · calc
      _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts p.1.1).pair p.1.2 = seedGenAliasValue q 0] := by
        apply prEvent_mono
        intro parts he
        rw [← he]
        simp [seedGenAliasValue, setupPairProgrammingInput, setupProgramView, ha]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.1).pair p.1.2)
        (fun _ => seedGenAliasValue q 0) p.1.1 none (some p.1.2)
        (fun c parts => by simp [shiftAt, shiftParts]) (fun _ _ => rfl)
  · calc
      _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts p.1.2).pair p.1.1 = seedGenAliasValue q 1] := by
        apply prEvent_mono
        intro parts he
        rw [← he]
        simp [seedGenAliasValue, setupPairProgrammingInput, setupProgramView, hb]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.2).pair p.1.1)
        (fun _ => seedGenAliasValue q 1) p.1.2 none (some p.1.1)
        (fun c parts => by simp [shiftAt, shiftParts]) (fun _ _ => rfl)

theorem evalDist_seedGenAlias_parameters :
    ((fun parts : C.Party → Parts C => fun i => (parts i).parameter) <$>
      OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))) =ᵈ
      $ᵗ (C.Party → HashOutput) := by
  rw [map_eq_bind_pure_comp]
  change ((OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))) >>=
    (fun parts => pure (fun i => (parts i).parameter))) =ᵈ _
  rw [← sequenceFin_bind_pure]
  refine EvalDistEq.trans
    (my := OverPermutation.sequenceFin (fun _ : C.Party => ($ᵗ HashOutput : ProbComp HashOutput))) ?_ ?_
  · apply evalDist_sequenceFin_congr
    intro i
    unfold sampleParts
    simp only [bind_assoc, pure_bind]
    refine (EvalDistEq.bind_right _ fun parameter =>
      (evalDist_uniform_bind_const _).trans (evalDist_uniform_bind_const _)).trans ?_
    rw [bind_pure]
  · have he : ∀ n : ℕ, OverPermutation.sequenceFin (fun _ : Fin n => ($ᵗ HashOutput)) =
        XmssSecurity.Concrete.sequenceFin (fun _ : Fin n => ($ᵗ HashOutput)) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp only [OverPermutation.sequenceFin, XmssSecurity.Concrete.sequenceFin, ih]
    rw [he]
    exact XmssSecurity.Seeded.evalDist_sequenceFin_uniform _

theorem probEvent_seedGenAlias_parameter_coordinate (a : C.Party) (v : HashOutput) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      (parts a).parameter = v] =
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr{let s : C.Party → HashOutput ← (fun parts : C.Party → Parts C => fun i => (parts i).parameter) <$>
          OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
        s a = v] := by
      rw [prEvent_map]
    _ = Pr{let s : C.Party → HashOutput ← $ᵗ (C.Party → HashOutput)}[s a = v] :=
      evalDist_seedGenAlias_parameters.prEvent_eq _
    _ = _ := probEvent_uniform_coord_eq a v

/-- The programming input of `P` costs one honest part of `P` in the seed generation. The PRSS setup
has no such input. -/
theorem probEvent_setupAlias_parameter_guess (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : Query C) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      q ∈ setupParameterInputs phase D (setupProgramView phase D parts log sent)] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  cases phase
  · obtain ⟨a, ha⟩ := seedGen_exists_honest D
    calc
      _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts a).parameter = seedGenAliasValue q (C.parties.idxOf a)] := by
        apply prEvent_mono
        intro parts he
        simp only [setupParameterInputs, ite_true, List.mem_singleton] at he
        rw [he]
        simp [seedGenAliasValue, Committee.parties, setupProgramView, ha]
      _ = _ := probEvent_seedGenAlias_parameter_coordinate a _
  · simp [setupParameterInputs]

/-- The position of the pair part in the reveal from `i` to `j`. -/
def pairPosition (phase : Phase) (i j : C.Party) : ℕ :=
  (sharedTerms i j).length + (if phase = .seedGen then 1 else 0)

/-- A reveal holds the pair part of the sender for the receiver at `pairPosition`. -/
theorem revealTo_getD_pairPosition (phase : Phase) (c : Parts C) (i j : C.Party) :
    (revealTo phase c i j).getD (pairPosition phase i j) 0 = c.pair j := by
  cases phase <;> simp [revealTo, pairPosition, List.getD_eq_getElem?_getD]

/-- One pair part of one operator is uniform. -/
theorem probEvent_pairPart_eq (i j : C.Party) (v : HashOutput) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      (parts i).pair j = v] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
  probEvent_parts_collision (fun parts => (parts i).pair j) (fun _ => v) i none (some j)
    (fun c parts => by simp [shiftAt, shiftParts]) (fun _ _ => rfl)

/-- The honest commitments are the protected cells in the cache-erasure hybrid. -/
def CommitHit (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) : Query C → Prop
  | .commit phase' i j values => phase' = phase ∧ i ∉ D.1 ∧ values = revealTo phase (parts i) i j
  | _ => False

/-- A fixed query is the commitment input of an honest sender with probability at most `1 / 2^256`.
The pair part of the sender for the receiver is the hidden coordinate, in each phase. -/
theorem probEvent_commit_guess (phase : Phase) (D : C.Coalition) (q : Query C) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      CommitHit phase D parts q] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  cases q <;> try (solve | simp [CommitHit])
  case commit phase' i j values =>
    calc
      _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts i).pair j = values.getD (pairPosition phase i j) 0] := by
        apply prEvent_mono
        intro parts he
        rw [he.2.2, revealTo_getD_pairPosition]
      _ = _ := probEvent_pairPart_eq i j _

/-- One logged query in the alias bound of a setup. It is a commitment input of an honest sender or a
programming input with probability at most `K / 2^256`. The programming inputs are derivations, so
the two cases are disjoint. The bound needs `1 ≤ K`, because a commitment hit has no programming
input. With an empty coalition the PRSS setup has no programming input. -/
theorem probEvent_hit_guess (phase : Phase) (D : C.Coalition) (K : ℕ) (hK : 1 ≤ K)
    (inputs : (C.Party → Parts C) → List (Query C))
    (hderive : ∀ parts q, q ∈ inputs parts → ∃ ph kind values, q = Query.derive ph kind values)
    (hguess : ∀ q, Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      q ∈ inputs parts] ≤ K * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) (q : Query C) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      CommitHit phase D parts q ∨ q ∈ inputs parts] ≤ K * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hq : ∃ ph kind values, q = Query.derive ph kind values
  · obtain ⟨ph, kind, values, rfl⟩ := hq
    simpa only [CommitHit, false_or] using hguess (.derive ph kind values)
  · have he : (fun parts : C.Party → Parts C => CommitHit phase D parts q ∨ q ∈ inputs parts) =
        fun parts => CommitHit phase D parts q := by
      funext parts
      exact propext ⟨fun h => h.resolve_right fun hm => hq (hderive parts q hm), Or.inl⟩
    rw [he]
    refine (probEvent_commit_guess phase D q).trans ?_
    calc (Fintype.card HashOutput : ℝ≥0∞)⁻¹ = 1 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := (one_mul _).symm
      _ ≤ _ := by gcongr; exact_mod_cast hK

theorem seedGenAlias_cross_honest (D : C.Coalition) (p : C.Pair)
    (hp : p ∈ seedGenCrossCoordinates D) : p.1.1 ∉ D.1 ∨ p.1.2 ∉ D.1 := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
  have hr := (seedGenCrossList_mem D r.1).mp r.2
  unfold seedGenCrossPair Committee.pairOf
  split_ifs <;> simp_all

private theorem alias_prob_exists_list {α β : Type} (xs : List α) (oa : ProbComp β)
    (P : α → β → Prop) (ε : ℝ≥0∞) (h : ∀ a ∈ xs, Pr{let z ← oa}[P a z] ≤ ε) :
    Pr{let x ← oa}[∃ a ∈ xs, P a x] ≤ xs.length * ε := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have he : (fun x => ∃ b ∈ a :: xs, P b x) =
        (fun x => P a x ∨ ∃ b ∈ xs, P b x) := by funext x; simp
    rw [he]
    refine (prEvent_or_le _ _ _).trans ?_
    calc
      _ ≤ ε + xs.length * ε := add_le_add (h a (by simp))
        (ih (fun b hb => h b (by simp [hb])))
      _ = _ := by simp [Nat.cast_add, add_mul, add_comm]

/-- Fixed transcripts give the exact per-query coefficient `K`. -/
theorem probEvent_setupAlias_program_guess (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : Query C) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      q ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent)] ≤
      seedGenProgrammingCount D * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let sd := OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))
  have he : (fun parts => q ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent)) =
      (fun parts => q ∈ setupParameterInputs phase D (setupProgramView phase D parts log sent) ∨
        (∃ T ∈ seedGenKnownCoordinates D,
          setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) T = q) ∨
        ∃ p ∈ seedGenCrossCoordinates D,
          setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) p = q) := by
    funext parts
    simp [setupProgrammingInputs]
  rw [he]
  refine (prEvent_or_le _ _ _).trans ?_
  refine le_trans (add_le_add (probEvent_setupAlias_parameter_guess phase D log sent q)
    ((prEvent_or_le _ _ _).trans (add_le_add
      (alias_prob_exists_list (seedGenKnownCoordinates D) sd _ _
        (fun T _ => probEvent_setupAlias_term_guess phase D log sent T q))
      (alias_prob_exists_list (seedGenCrossCoordinates D) sd _ _
        (fun p hp => probEvent_setupAlias_pair_guess phase D log sent p (seedGenAlias_cross_honest D p hp) q))))) ?_
  simp [seedGenProgrammingCount, Nat.cast_add, add_mul, add_assoc]

theorem setupAlias_term_shift_other (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (T U : C.Term) (hTU : T ≠ U)
    (a : C.Party) (c : HashOutput) (parts : C.Party → Parts C) :
    setupTermProgrammingInput phase D (setupProgramView phase D (shiftAt a (some T) none c parts) log sent) U =
      setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) U := by
  unfold setupTermProgrammingInput
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j ∈ D.1 <;> by_cases hja : j = a <;>
    simp_all [setupProgramView, shiftAt, shiftParts]

theorem probEvent_setupAlias_term_collision (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (T U : C.Term) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      T ≠ U ∧
        setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) T =
          setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) U] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hTU : T = U
  · simp [hTU]
  obtain ⟨a, ha, hD⟩ := seedGen_honest_holder D T
  calc
    _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
        (parts a).term T =
        seedGenAliasValue (setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) U)
          ((C.parties.filter (· ∈ C.holders T)).idxOf a)] := by
      apply prEvent_mono
      intro parts he
      rw [← he.2, setupAlias_term_coordinate phase D log sent parts T a ha hD]
    _ = _ := probEvent_parts_collision (fun parts => (parts a).term T)
      (fun parts => seedGenAliasValue (setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) U)
        ((C.parties.filter (· ∈ C.holders T)).idxOf a)) a (some T) none
      (fun c parts => by simp [shiftAt, shiftParts])
      (fun c parts => by rw [setupAlias_term_shift_other phase D log sent T U hTU a c parts])

theorem setupAlias_pair_shift_other (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (p r : C.Pair) (hpr : p ≠ r)
    (a b : C.Party) (hab : (a = p.1.1 ∧ b = p.1.2) ∨ (a = p.1.2 ∧ b = p.1.1))
    (c : HashOutput) (parts : C.Party → Parts C) :
    setupPairProgrammingInput phase D (setupProgramView phase D (shiftAt a none (some b) c parts) log sent) r =
      setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) r := by
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
      (setupProgramView phase D (shiftAt a none (some b) c parts) log sent i j).pair k =
        (setupProgramView phase D parts log sent i j).pair k := by
    by_cases hj : j ∈ D.1 <;> by_cases hja : j = a <;> by_cases hkb : k = b <;>
      simp_all [setupProgramView, shiftAt, shiftParts, eq_comm]
  simp only [setupPairProgrammingInput, hv _ _ _ h₁, hv _ _ _ h₂]

theorem probEvent_setupAlias_pair_collision (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (p r : C.Pair) (hp : p.1.1 ∉ D.1 ∨ p.1.2 ∉ D.1) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      p ≠ r ∧
        setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) p =
          setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) r] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hpr : p = r
  · simp [hpr]
  rcases hp with ha | hb
  · calc
      _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts p.1.1).pair p.1.2 = seedGenAliasValue
          (setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) r) 0] := by
        apply prEvent_mono
        intro parts he
        rw [← he.2]
        simp [seedGenAliasValue, setupPairProgrammingInput, setupProgramView, ha]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.1).pair p.1.2)
        (fun parts => seedGenAliasValue
          (setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) r) 0)
        p.1.1 none (some p.1.2) (fun c parts => by simp [shiftAt, shiftParts])
        (fun c parts => by rw [setupAlias_pair_shift_other phase D log sent p r hpr _ _ (Or.inl ⟨rfl, rfl⟩)])
  · calc
      _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts p.1.2).pair p.1.1 = seedGenAliasValue
          (setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) r) 1] := by
        apply prEvent_mono
        intro parts he
        rw [← he.2]
        simp [seedGenAliasValue, setupPairProgrammingInput, setupProgramView, hb]
      _ = _ := probEvent_parts_collision (fun parts => (parts p.1.2).pair p.1.1)
        (fun parts => seedGenAliasValue
          (setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) r) 1)
        p.1.2 none (some p.1.1) (fun c parts => by simp [shiftAt, shiftParts])
        (fun c parts => by rw [setupAlias_pair_shift_other phase D log sent p r hpr _ _ (Or.inr ⟨rfl, rfl⟩)])

theorem setupAlias_inputs_nodup (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (hT : ∀ T ∈ seedGenKnownCoordinates D, ∀ U ∈ seedGenKnownCoordinates D,
      setupTermProgrammingInput phase D view T = setupTermProgrammingInput phase D view U → T = U)
    (hP : ∀ p ∈ seedGenCrossCoordinates D, ∀ r ∈ seedGenCrossCoordinates D,
      setupPairProgrammingInput phase D view p = setupPairProgrammingInput phase D view r → p = r) :
    (setupProgrammingInputs phase D view).Nodup := by
  have hparam : (setupParameterInputs phase D view).Nodup := by
    unfold setupParameterInputs
    split_ifs <;> simp
  have hkind : ∀ x ∈ setupParameterInputs phase D view, ∃ values, x = Query.derive phase .parameter values := by
    intro x hx
    unfold setupParameterInputs at hx
    split_ifs at hx
    · exact ⟨_, List.mem_singleton.mp hx⟩
    · simp at hx
  unfold setupProgrammingInputs
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨hparam, (List.nodup_map_iff_inj_on (seedGenKnownCoordinates_nodup D)).2 hT, ?_⟩,
    (List.nodup_map_iff_inj_on (seedGenCrossCoordinates_nodup D)).2 hP, ?_⟩
  · intro x hx y hy he
    obtain ⟨values, rfl⟩ := hkind x hx
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hy
    simp [setupTermProgrammingInput] at he
  · intro x hx y hy he
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨values, rfl⟩ := hkind x hx
      simp [setupPairProgrammingInput] at he
    · obtain ⟨T, _, rfl⟩ := List.mem_map.mp hx
      simp [setupTermProgrammingInput, setupPairProgrammingInput] at he

/-- For a fixed transcript, the birthday term only counts the actual programming coordinates. -/
theorem probEvent_setupAlias_inputs_collision (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      ¬ (setupProgrammingInputs phase D (setupProgramView phase D parts log sent)).Nodup] ≤
      (seedGenProgrammingCount D : ℝ≥0∞) ^ 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let sd := OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))
  let ε : ℝ≥0∞ := (Fintype.card HashOutput : ℝ≥0∞)⁻¹
  let ts := seedGenKnownCoordinates D
  let ps := seedGenCrossCoordinates D
  calc
    _ ≤ Pr{let parts ← sd}[(∃ T ∈ ts, ∃ U ∈ ts, T ≠ U ∧
          setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) T =
            setupTermProgrammingInput phase D (setupProgramView phase D parts log sent) U) ∨
        (∃ p ∈ ps, ∃ r ∈ ps, p ≠ r ∧
          setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) p =
            setupPairProgrammingInput phase D (setupProgramView phase D parts log sent) r)] := by
      apply prEvent_mono
      intro parts hbad
      by_contra hn
      push Not at hn
      exact hbad (setupAlias_inputs_nodup phase D _
        (fun T hT U hU he => by_contra fun hne => hn.1 T hT U hU hne he)
        (fun p hp r hr he => by_contra fun hne => hn.2 p hp r hr hne he))
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ ts.length * (ts.length * ε) + ps.length * (ps.length * ε) := by
      apply add_le_add
      · exact alias_prob_exists_list ts sd _ _ fun T _ =>
          alias_prob_exists_list ts sd _ _ fun U _ => probEvent_setupAlias_term_collision phase D log sent T U
      · exact alias_prob_exists_list ps sd _ _ fun p hp =>
          alias_prob_exists_list ps sd _ _ fun r _ =>
            probEvent_setupAlias_pair_collision phase D log sent p r (seedGenAlias_cross_honest D p hp)
    _ = ((ts.length ^ 2 + ps.length ^ 2 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring
    _ ≤ _ := by
      apply mul_le_mul_left
      rw [← Nat.cast_pow]
      exact_mod_cast (show ts.length ^ 2 + ps.length ^ 2 ≤ seedGenProgrammingCount D ^ 2 by
        dsimp [ts, ps, seedGenProgrammingCount]
        nlinarith [Nat.zero_le ((seedGenKnownCoordinates D).length * (seedGenCrossCoordinates D).length)])

/-- The hybrid's bad event combines commitment hits and programming aliases. These query classes
are disjoint, so combining them does not increase the coefficient of the query budget. -/
def SetupAliasHybridBad (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) : Prop :=
  (∃ v ∈ log, CommitHit phase D parts v.1 ∨
    v.1 ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent)) ∨
  ¬ (setupProgrammingInputs phase D (setupProgramView phase D parts log sent)).Nodup

theorem probEvent_setupAlias_hit_guess (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : Query C) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      CommitHit phase D parts q ∨
        q ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent)] ≤
      seedGenProgrammingCount D * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
  probEvent_hit_guess phase D (seedGenProgrammingCount D) (by unfold seedGenProgrammingCount; omega)
    (fun parts => setupProgrammingInputs phase D (setupProgramView phase D parts log sent))
    (fun parts q hq => ⟨_, setupProgrammingInputs_derive phase D _ q hq⟩)
    (probEvent_setupAlias_program_guess phase D log sent) q

theorem setupAlias_hit_not_fixed (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (q : Query C)
    (hq : CommitHit phase D parts q ∨
      q ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent)) : ¬ IsFixed q := by
  rcases hq with hq | hq
  · rintro ⟨input, rfl, _⟩
    exact hq
  · rintro ⟨input, rfl, _⟩
    obtain ⟨kind, values, he⟩ := setupProgrammingInputs_derive phase D _ _ hq
    cases he

theorem probEvent_setupAlias_hybrid_fixed (phase : Phase) (D : C.Coalition) (log : CallLog C)
    (sent : C.Party → Mail C E) (q : ℕ)
    (hq : (log.filter fun v => ¬ IsFixed v.1).length ≤ q) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      SetupAliasHybridBad phase D parts log sent] ≤
      ((q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2 : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let L := log.filter fun v => ¬ IsFixed v.1
  have he (parts : C.Party → Parts C) :
      (∃ v ∈ log, CommitHit phase D parts v.1 ∨
        v.1 ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent)) ↔
      (∃ v ∈ L, CommitHit phase D parts v.1 ∨
        v.1 ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent)) := by
    constructor
    · rintro ⟨v, hv, hh⟩
      exact ⟨v, List.mem_filter.mpr ⟨hv, by simpa using setupAlias_hit_not_fixed phase D parts log sent v.1 hh⟩, hh⟩
    · rintro ⟨v, hv, hh⟩
      exact ⟨v, (List.mem_filter.mp hv).1, hh⟩
  unfold SetupAliasHybridBad
  simp only [he]
  refine (prEvent_or_le _ _ _).trans ?_
  refine le_trans (add_le_add
    (alias_prob_exists_list L _ _ _ (fun v _ => probEvent_setupAlias_hit_guess phase D log sent v.1))
    (probEvent_setupAlias_inputs_collision phase D log sent)) ?_
  calc
    _ ≤ (q : ℝ≥0∞) * (seedGenProgrammingCount D * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        seedGenProgrammingCount D ^ 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
      gcongr
    _ = _ := by push_cast; ring

/-- The transcript does not depend on the parts and logs at most `q` random-oracle queries. Then the bad
event of a setup of `phase` has a probability of at most `(q K + K²) / 2^256`. -/
theorem probEvent_setupAlias_independent (phase : Phase) (D : C.Coalition)
    (transcript : ProbComp (CallLog C × (C.Party → Mail C E))) (q : ℕ)
    (hq : ∀ r ∈ support transcript, (r.1.filter fun v => ¬ IsFixed v.1).length ≤ q) :
    Pr{let p ← seedGenPartsKernel (fun _ => transcript)}[
      SetupAliasHybridBad phase D p.1 p.2.1 p.2.2] ≤
      ((q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2 : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  unfold seedGenPartsKernel
  rw [probEvent_congr_evalDist (OracleComp.EvalDistEq.bind_bind_swap _ _ _)]
  apply probEvent_bind_le_const
  intro r hr
  rw [bind_pure_comp, prEvent_map]
  exact probEvent_setupAlias_hybrid_fixed phase D r.1 r.2 q (hq r hr)

def seedGenAliasQueryLog (t : (LocalSpec C).Domain) (u : (LocalSpec C).Range t) : CallLog C :=
  match t with
  | .inr (.inl q) => [(q, u)]
  | _ => []

theorem seedGenAlias_observe_query_bind {α : Type} (t : (LocalSpec C).Domain)
    (k : (LocalSpec C).Range t → OracleComp (LocalSpec C) α) :
    observe (OracleComp.lift (OracleSpec.query t) >>= k) = (do
      let u ← worldRoles.adversary (OracleComp.lift (OracleSpec.query t))
      let r ← observe (k u)
      pure (r.1, seedGenAliasQueryLog t u ++ r.2)) := by
  simp only [observe, simulateQ_bind, WriterT.run_bind, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, id_map]
  rcases t with t | (q | x) <;>
    simp [seedGenAliasQueryLog, WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell]
  rfl

theorem seedGenAlias_queryLog_length (t : (LocalSpec C).Domain) (u : (LocalSpec C).Range t) :
    ((seedGenAliasQueryLog t u).filter fun v => ¬ IsFixed v.1).length ≤
      if Counted t then 1 else 0 := by
  rcases t with t | (q | x)
  · simp [seedGenAliasQueryLog, Counted]
  · cases q with
    | hash input =>
      have hf : IsFixed (Query.hash (C := C) input) ↔ MpcInput input := by simp [IsFixed]
      by_cases hi : MpcInput input <;> simp [seedGenAliasQueryLog, Counted, hf, hi]
    | _ => simp [seedGenAliasQueryLog, Counted, IsFixed]
  · simp [seedGenAliasQueryLog]

theorem seedGenAlias_observe_length {α : Type} (oa : OracleComp (LocalSpec C) α)
    (n : ℕ) (hn : IsQueryBoundP oa Counted n) (r : α × CallLog C)
    (hr : r ∈ support (observe oa)) : (r.2.filter fun v => ¬ IsFixed v.1).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure a =>
    simp only [observe, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [seedGenAlias_observe_query_bind] at hr
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, _, s, hs, rfl⟩ := hr
    have hrest := ih u _ (hn.2 u) s hs
    have hcall := seedGenAlias_queryLog_length t u
    simp only [List.filter_append, List.length_append]
    by_cases ht : Counted t
    · have hn0 : 0 < n := hn.1.resolve_left (not_not.mpr ht)
      simp only [if_pos ht] at hrest hcall
      omega
    · simp only [if_neg ht] at hrest hcall
      omega

/-- The independent transcript uses fresh uncached honest commitments. -/
def seedGenAliasFreshTranscript (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) : OracleComp (WorldSpec C) (CallLog C × (C.Party → Mail C E)) := do
  let (state, log) ← observe (A.start (corruptInputs D x) z)
  let commitments ← free (liftComp (OverPermutation.sequenceFin fun i : C.Party =>
    if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput)) (LocalSpec C))
  let ((_, sent), calls) ← observe (A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    commitOutbox i (commitments i) c else none)
  pure (log ++ calls, sent)

theorem seedGenAliasFreshTranscript_length (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) (r : CallLog C × (C.Party → Mail C E))
    (hr : r ∈ support (seedGenAliasFreshTranscript D A x z)) :
    (r.1.filter fun v => ¬ IsFixed v.1).length ≤ q := by
  obtain ⟨start, step, final, htotal, hstart, hround, _⟩ := hq
  unfold seedGenAliasFreshTranscript at hr
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨⟨state, log⟩, hlog, commitments, _, ⟨⟨st, sent⟩, calls⟩, hcalls, rfl⟩ := hr
  have h₁ := seedGenAlias_observe_length _ start (hstart (corruptInputs D x) z) _ hlog
  have h₂ := seedGenAlias_observe_length _ step (hround state _) _ hcalls
  simp only [List.filter_append, List.length_append]
  dsimp only at h₁ h₂
  simp only [setupRounds] at htotal
  omega

theorem probEvent_setupAlias_fresh (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    Pr{let p ← seedGenPartsKernel (fun _ =>
        (simulateQ (worldAnswer prims) (seedGenAliasFreshTranscript D A x z)).run' ∅)}[
      SetupAliasHybridBad (phase := phase) D p.1 p.2.1 p.2.2] ≤
      ((q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2 : ℕ) : ℝ≥0∞) /
        2 ^ 256 := by
  have hb := probEvent_setupAlias_independent (phase := phase) D
    ((simulateQ (worldAnswer prims) (seedGenAliasFreshTranscript D A x z)).run' ∅) q
    (fun r hr => seedGenAliasFreshTranscript_length D A x z Z q hq r
      (support_simulateQ_run'_subset _ _ _ hr))
  have hc : Fintype.card HashOutput = 2 ^ 256 := by
    unfold HashOutput
    exact Fintype.card_bitVec 256
  simpa only [hc, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hb

/-- Sender and receiver tags make the honest commitment cells distinct for every choice of parts. -/
def setupAliasCommitCell (phase : Phase) (parts : C.Party → Parts C) (ij : C.Party × C.Party) : Query C :=
  .commit phase ij.1 ij.2 (revealTo phase (parts ij.1) ij.1 ij.2)

theorem setupAliasCommitCell_injective (phase : Phase) (parts : C.Party → Parts C) :
    Function.Injective (setupAliasCommitCell (phase := phase) parts) := by
  intro a b he
  simp only [setupAliasCommitCell, Query.commit.injEq] at he
  exact Prod.ext he.2.1 he.2.2.1

theorem seedGenAlias_cache_update_agrees (P : Query C → Prop) (s t : HashCache C)
    (hst : ∀ v, ¬ P v → s v = t v) (q : Query C) (u : HashOutput) :
    ∀ v, ¬ P v → (s.cacheQuery q u) v = (t.cacheQuery q u) v := by
  intro v hv
  by_cases he : v = q
  · subst v
    simp
  · rw [QueryCache.cacheQuery_of_ne _ _ he, QueryCache.cacheQuery_of_ne _ _ he]
    exact hst v hv

theorem relTriple_seedGenAlias_hash_off (prims : Primitives) (P : Query C → Prop)
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
    exact ⟨rfl, seedGenAlias_cache_update_agrees P s t hst q a⟩
  | some y =>
    rw [QueryImpl.withCaching_run_some _ hs, QueryImpl.withCaching_run_some _ (hqt.trans hs)]
    exact relTriple_pure_pure ⟨rfl, hst⟩

theorem relTriple_seedGenAlias_local_off (prims : Primitives) (P : Query C → Prop)
    (s t : HashCache C) (hst : ∀ v, ¬ P v → s v = t v)
    (u : (LocalSpec C).Domain) (hu : ¬ SeedGenTouches P u) :
    RelTriple ((localAnswer prims u).run s) ((localAnswer prims u).run t)
      (fun a b => a.1 = b.1 ∧ ∀ v, ¬ P v → a.2 v = b.2 v) := by
  rcases u with n | (q | x)
  · change RelTriple ((fun y => (y, s)) <$> (query (spec := unifSpec) n))
      ((fun y => (y, t)) <$> (query (spec := unifSpec) n)) _
    apply relTriple_map
    exact relTriple_post_mono (relTriple_refl _) (fun _ _ he => ⟨he, hst⟩)
  · exact relTriple_seedGenAlias_hash_off prims P s t hst q
      (fun hq => hu ⟨q, by simp [seedGenLocalHashInputs], hq⟩)
  · have hx : ¬ P (.streamKey x.2.1) := fun hx => hu ⟨_, by simp [seedGenLocalHashInputs], hx⟩
    change RelTriple ((prgAnswer prims x).run s) ((prgAnswer prims x).run t) _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (relTriple_seedGenAlias_hash_off prims P s t hst _ hx)
    intro a b hab
    apply relTriple_pure_pure
    exact ⟨by rw [hab.1], hab.2⟩

theorem seedGenAlias_observe_run_query_bind (prims : Primitives) {α : Type}
    (u : (LocalSpec C).Domain) (k : (LocalSpec C).Range u → OracleComp (LocalSpec C) α)
    (s : HashCache C) :
    (simulateQ (worldAnswer prims) (observe (OracleComp.lift (OracleSpec.query u) >>= k))).run s =
      ((localAnswer prims u).run s >>= fun a =>
        (simulateQ (worldAnswer prims) (observe (k a.1))).run a.2 >>= fun r =>
          pure ((r.1.1, seedGenAliasQueryLog u a.1 ++ r.1.2), r.2)) := by
  rw [seedGenAlias_observe_query_bind]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    simulateQ_world_adversary, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]

theorem setupAlias_touches_logged (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (u : (LocalSpec C).Domain) (hu : SeedGenTouches (CommitHit (phase := phase) D parts) u)
    (a : (LocalSpec C).Range u) : ∃ v ∈ seedGenAliasQueryLog u a, CommitHit (phase := phase) D parts v.1 := by
  rcases u with n | (q | x)
  · simp [SeedGenTouches, seedGenLocalHashInputs] at hu
  · have hq : CommitHit (phase := phase) D parts q := by
      simpa [SeedGenTouches, seedGenLocalHashInputs] using hu
    exact ⟨(q, a), by simp [seedGenAliasQueryLog], hq⟩
  · simp [SeedGenTouches, seedGenLocalHashInputs, CommitHit] at hu

/-- Adaptive observed computations agree off the honest commitment cells until the left log
contains one of those cells. The relation preserves the complete observed answer log. -/
theorem relTriple_setupAlias_observe (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ s t : HashCache C, (∀ v, ¬ CommitHit (phase := phase) D parts v → s v = t v) →
      RelTriple ((simulateQ (worldAnswer prims) (observe oa)).run s)
        ((simulateQ (worldAnswer prims) (observe oa)).run t)
        (fun a b => (∃ v ∈ a.1.2, CommitHit (phase := phase) D parts v.1) ∨
          (a.1 = b.1 ∧ ∀ v, ¬ CommitHit (phase := phase) D parts v → a.2 v = b.2 v)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s t hst
    simp only [observe, simulateQ_pure, WriterT.run_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨rfl, hst⟩)
  | query_bind u k ih =>
    intro s t hst
    rw [seedGenAlias_observe_run_query_bind, seedGenAlias_observe_run_query_bind]
    by_cases hu : SeedGenTouches (CommitHit (phase := phase) D parts) u
    · apply relTriple_of_support_left
      intro r hr b
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨a, _, z, _, rfl⟩ := hr
      obtain ⟨v, hv, hp⟩ := setupAlias_touches_logged (phase := phase) D parts u hu a.1
      exact Or.inl ⟨v, List.mem_append_left _ hv, hp⟩
    · apply relTriple_bind (relTriple_seedGenAlias_local_off prims (CommitHit (phase := phase) D parts) s t hst u hu)
      rintro ⟨a, s'⟩ ⟨b, t'⟩ ⟨he, hst'⟩
      dsimp only at he hst' ⊢
      subst b
      apply relTriple_bind (ih a s' t' hst')
      intro r z hrz
      apply relTriple_pure_pure
      rcases hrz with ⟨v, hv, hp⟩ | ⟨he, hc⟩
      · exact Or.inl ⟨v, List.mem_append_right _ hv, hp⟩
      · exact Or.inr ⟨by rw [he], hc⟩

theorem setupAlias_start_fresh (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) {α : Type} (oa : OracleComp (LocalSpec C) α)
    (w : (α × CallLog C) × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (observe oa)).run ∅))
    (hlog : ¬ ∃ v ∈ w.1.2, CommitHit (phase := phase) D parts v.1) :
    ∀ v, CommitHit (phase := phase) D parts v → w.2 v = none := by
  intro v hv
  by_contra hn
  rcases seedGenObserve_new_logged prims oa ∅ w hw v rfl hn with ⟨y, hy⟩ | ⟨k, rfl⟩
  · exact hlog ⟨(v, y), hy, hv⟩
  · exact hv

/-- A block of distinct fresh commitment cells can be sampled independently. The final cache
agrees with its initial value at every cell outside the block. -/
theorem relTriple_seedGenAlias_fresh_hashes (prims : Primitives) (qs : List (Query C)) :
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

theorem relTriple_seedGenAlias_fresh_blocks (prims : Primitives) :
    ∀ (n : ℕ) (qs : Fin n → List (Query C)) (s : HashCache C),
      (∀ i, (qs i).Nodup) → (∀ i j, i ≠ j → (qs i).Disjoint (qs j)) →
      (∀ i q, q ∈ qs i → s q = none) → (∀ i q, q ∈ qs i → ¬ IsFixed q) →
      RelTriple (OverPermutation.sequenceFin fun i => (qs i).mapM fun _ => ($ᵗ HashOutput))
        ((OverPermutation.sequenceFin fun i => (qs i).mapM (hashAnswer prims)).run s)
        (fun a b => a = b.1 ∧ ∀ v, (∀ i, v ∉ qs i) → s v = b.2 v) := by
  intro n
  induction n with
  | zero =>
    intro qs s _ _ _ _
    exact relTriple_pure_pure ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro qs s hnd hdis hfresh hfix
    simp only [OverPermutation.sequenceFin, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (relTriple_seedGenAlias_fresh_hashes prims (qs 0) s (hnd 0) (hfresh 0) (hfix 0))
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

def setupAliasCommitQueries (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) :
    List (Query C) :=
  if i ∈ D.1 then [] else C.parties.map fun j => setupAliasCommitCell (phase := phase) parts (i, j)

theorem setupAliasCommitQueries_mem (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (i : C.Party) (q : Query C) :
    q ∈ setupAliasCommitQueries (phase := phase) D parts i ↔
      i ∉ D.1 ∧ ∃ j, q = setupAliasCommitCell (phase := phase) parts (i, j) := by
  by_cases hi : i ∈ D.1 <;> simp [setupAliasCommitQueries, hi, Committee.parties, eq_comm]

theorem relTriple_setupAlias_initial (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (s : HashCache C)
    (hfresh : ∀ v, CommitHit (phase := phase) D parts v → s v = none) :
    RelTriple (OverPermutation.sequenceFin fun i : C.Party =>
        if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput))
      ((simulateQ (localAnswer prims) (setupInitialCommitments phase D parts)).run s)
      (fun a b => a = b.1 ∧ ∀ v, ¬ CommitHit (phase := phase) D parts v → s v = b.2 v) := by
  have hl : (OverPermutation.sequenceFin fun i : C.Party =>
      (setupAliasCommitQueries (phase := phase) D parts i).mapM fun _ => ($ᵗ HashOutput)) =
      (OverPermutation.sequenceFin fun i : C.Party =>
        if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput)) := by
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp [setupAliasCommitQueries, hi, List.mapM_map, Function.comp_def]
  have hr : simulateQ (localAnswer prims) (setupInitialCommitments phase D parts) =
      OverPermutation.sequenceFin fun i : C.Party => (setupAliasCommitQueries (phase := phase) D parts i).mapM (hashAnswer prims) := by
    rw [setupInitialCommitments, simulateQ_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi, setupAliasCommitQueries]
    · simp only [hi, if_false, setupAliasCommitQueries]
      have he : commitQueries phase i (parts i) =
          (C.parties.map fun j => setupAliasCommitCell (phase := phase) parts (i, j)).mapM hashQuery := by
        simp [commitQueries, List.mapM_map, setupAliasCommitCell, Function.comp_def]
      rw [he, simulateQ_localAnswer_hashes]
  rw [hr, ← hl]
  refine relTriple_post_mono (relTriple_seedGenAlias_fresh_blocks prims C.n
    (setupAliasCommitQueries (phase := phase) D parts) s ?_ ?_ ?_ ?_) ?_
  · intro i
    by_cases hi : i ∈ D.1
    · simp [setupAliasCommitQueries, hi]
    · simp only [setupAliasCommitQueries, hi, if_false]
      exact (List.nodup_finRange C.n).map (fun j k he =>
        (Prod.mk.inj (setupAliasCommitCell_injective (phase := phase) parts he)).2)
  · intro i j hij q hqi hqj
    obtain ⟨_, k, rfl⟩ := (setupAliasCommitQueries_mem (phase := phase) D parts i q).mp hqi
    obtain ⟨_, l, he⟩ := (setupAliasCommitQueries_mem (phase := phase) D parts j _).mp hqj
    exact hij (Prod.mk.inj (setupAliasCommitCell_injective (phase := phase) parts he)).1
  · intro i q hq
    obtain ⟨hi, j, rfl⟩ := (setupAliasCommitQueries_mem (phase := phase) D parts i q).mp hq
    exact hfresh _ ⟨rfl, hi, rfl⟩
  · intro i q hq
    obtain ⟨_, j, rfl⟩ := (setupAliasCommitQueries_mem (phase := phase) D parts i q).mp hq
    simp [setupAliasCommitCell, IsFixed]
  · intro a b hab
    refine ⟨hab.1, fun v hv => hab.2 v (fun i hm => ?_)⟩
    obtain ⟨hi, j, rfl⟩ := (setupAliasCommitQueries_mem (phase := phase) D parts i v).mp hm
    exact hv ⟨rfl, hi, rfl⟩

def seedGenAliasFreshTail (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (parts : C.Party → Parts C)
    (st : (A.State × CallLog C) × HashCache C) :
    ProbComp ((C.Party → Parts C) × CallLog C × (C.Party → Mail C E)) := do
  let commitments ← OverPermutation.sequenceFin fun i : C.Party =>
    if i ∈ D.1 then pure [] else C.parties.mapM fun _ => ($ᵗ HashOutput)
  let r ← (simulateQ (worldAnswer prims) (observe (A.round st.1.1 fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 then commitOutbox i (commitments i) c else none))).run st.2
  pure (parts, st.1.2 ++ r.1.2, r.1.1.2)

def setupAliasKnownTail (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (parts : C.Party → Parts C)
    (st : (A.State × CallLog C) × HashCache C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    ProbComp (SeedGenKnownPre C E A.State × HashCache C) := do
  let com ← (simulateQ (localAnswer prims) (setupInitialCommitments phase D parts)).run st.2
  let r ← (simulateQ (worldAnswer prims) (observe (A.round st.1.1 fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 then commitOutbox i (com.1 i) c else none))).run com.2
  let high ← setupHighSample phase
  let ok ← (simulateQ (worldAnswer prims)
    (setupProgramOk (phase := phase) D parts (st.1.2 ++ r.1.2) r.1.1.2 parameter seeds pairs high)).run r.2
  pure (⟨parameter, seeds, pairs, parts, st.1.2 ++ r.1.2, r.1.1.2, com.1, ok.1, r.1.1.1⟩, ok.2)

theorem evalDist_seedGenAlias_fresh_start (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    seedGenPartsKernel (fun _ =>
      (simulateQ (worldAnswer prims) (seedGenAliasFreshTranscript D A x z)).run' ∅) =ᵈ
    (do
      let st ← (simulateQ (worldAnswer prims) (observe (A.start (corruptInputs D x) z))).run ∅
      let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
      seedGenAliasFreshTail prims D A parts st) := by
  unfold seedGenPartsKernel seedGenAliasFreshTranscript seedGenAliasFreshTail
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_world_sample, StateT.run'_eq,
    StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem setupAlias_known_start (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    (simulateQ (worldAnswer prims) (setupKnownPrefix (phase := phase) D A x z)).run ∅ = (do
      let st ← (simulateQ (worldAnswer prims) (observe (A.start (corruptInputs D x) z))).run ∅
      let dealer ← setupDealerSamples phase (C := C)
      let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
      setupAliasKnownTail (phase := phase) prims D A parts st dealer.1 dealer.2.1 dealer.2.2) := by
  unfold setupKnownPrefix setupAliasKnownTail
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_world_sample, StateT.run_bind,
    StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  simp only [simulateQ_free]

theorem relTriple_seedGenAlias_support {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : α → β → Prop} (h : RelTriple oa ob R) :
    RelTriple oa ob (fun a b => a ∈ support oa ∧ b ∈ support ob ∧ R a b) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, ?_⟩
  filter_upwards [ae_mem_support_prod c, hc] with z hz hR
  exact ⟨hz.1, hz.2, hR⟩

theorem relTriple_setupAlias_tail (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (parts : C.Party → Parts C)
    (st : (A.State × CallLog C) × HashCache C)
    (hstart : (¬ ∃ v ∈ st.1.2, CommitHit (phase := phase) D parts v.1) →
      ∀ v, CommitHit (phase := phase) D parts v → st.2 v = none)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    RelTriple (seedGenAliasFreshTail prims D A parts st)
      (setupAliasKnownTail (phase := phase) prims D A parts st parameter seeds pairs)
      (fun p w => (∃ v ∈ p.2.1, CommitHit (phase := phase) D p.1 v.1) ∨
        (w.1.parts = p.1 ∧ w.1.log = p.2.1 ∧ w.1.sent = p.2.2)) := by
  by_cases hhit : ∃ v ∈ st.1.2, CommitHit (phase := phase) D parts v.1
  · apply relTriple_of_support_left
    intro p hp w
    unfold seedGenAliasFreshTail at hp
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨com, _, r, _, rfl⟩ := hp
    obtain ⟨v, hv, hh⟩ := hhit
    exact Or.inl ⟨v, List.mem_append_left _ hv, hh⟩
  unfold seedGenAliasFreshTail setupAliasKnownTail
  apply relTriple_bind (relTriple_setupAlias_initial (phase := phase) prims D parts st.2 (hstart hhit))
  rintro commitments ⟨com, cache⟩ ⟨he, hcache⟩
  dsimp only at he hcache ⊢
  subst com
  apply relTriple_bind (relTriple_setupAlias_observe (phase := phase) prims D parts _ st.2 cache hcache)
  intro r z hrz
  apply relTriple_post_mono (relTriple_seedGenAlias_support (relTriple_true _ _))
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
def SetupAliasPrefixCoupling (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux),
    RelTriple
      (seedGenPartsKernel (fun _ =>
        (simulateQ (worldAnswer prims) (seedGenAliasFreshTranscript D A x z)).run' ∅))
      ((simulateQ (worldAnswer prims) (setupKnownPrefix (phase := phase) D A x z)).run ∅)
      (fun p w => (∃ v ∈ p.2.1, CommitHit (phase := phase) D p.1 v.1) ∨
        (w.1.parts = p.1 ∧ w.1.log = p.2.1 ∧ w.1.sent = p.2.2))

theorem setupAliasPrefixCoupling (phase : Phase) (prims : Primitives) :
    SetupAliasPrefixCoupling (phase := phase) (C := C) (E := E) prims := by
  intro D A x z
  apply relTriple_of_evalDistEq_left (evalDist_seedGenAlias_fresh_start prims D A x z)
  rw [setupAlias_known_start]
  apply relTriple_bind (relTriple_seedGenAlias_support (relTriple_refl _))
  intro st st' hst
  rcases hst with ⟨hsupport, _, he⟩
  subst st'
  rw [← pure_bind () (fun _ =>
    (OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)) >>=
      fun parts => seedGenAliasFreshTail prims D A parts st)]
  apply relTriple_bind (relTriple_true _ _)
  intro _ dealer _
  apply relTriple_bind (relTriple_refl _)
  intro parts parts' he
  subst parts'
  exact relTriple_setupAlias_tail (phase := phase) prims D A parts st
    (fun hhit => setupAlias_start_fresh (phase := phase) prims D parts _ st hsupport hhit)
    dealer.1 dealer.2.1 dealer.2.2

theorem setupProgramAliasBound (phase : Phase) (prims : Primitives) :
    SetupProgramAliasBound (phase := phase) (C := C) (E := E) prims := by
  intro D A x z Z q hq
  have hc : Pr{let w ← (simulateQ (worldAnswer prims) (setupKnownPrefix (phase := phase) D A x z)).run ∅}[
      SetupProgramAlias (phase := phase) D w.1] ≤
      Pr{let p ← seedGenPartsKernel (fun _ =>
          (simulateQ (worldAnswer prims) (seedGenAliasFreshTranscript D A x z)).run' ∅)}[
        SetupAliasHybridBad (phase := phase) D p.1 p.2.1 p.2.2] := by
    apply prEvent_le_of_relTriple (relTriple_symm (setupAliasPrefixCoupling (phase := phase) prims D A x z))
    intro w p hp hw
    rcases hp with ⟨v, hv, hh⟩ | ⟨hparts, hlog, hsent⟩
    · exact Or.inl ⟨v, hv, Or.inl hh⟩
    · unfold SetupProgramAlias at hw
      rw [hparts, hlog, hsent] at hw
      rcases hw with ⟨v, hv, y, hy⟩ | hn
      · exact Or.inl ⟨(v, y), hy, Or.inr hv⟩
      · exact Or.inr hn
  have hb := hc.trans (probEvent_setupAlias_fresh (phase := phase) prims D A x z Z q hq)
  have hr := ENNReal.toReal_mono (by finiteness) hb
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using hr

/-- The distance claim of a setup of each phase. -/
theorem setupSecurityDistance (prims : Primitives) (phase : Phase) :
    SetupSecurityDistance (C := C) (E := E) phase prims :=
  setupSecurityDistance_of_programAlias prims phase (setupProgramAliasBound phase prims)

/-- `SeedGenSecurityStatement`, as the instance of `setupSecurityDistance` for the seed generation. -/
theorem seedGenSecurity (prims : Primitives) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  seedGenSecurity_of_setup prims (setupSecurityDistance prims .seedGen)

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.setupProgramAliasBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.setupProgramAliasBound

/-- info: 'ThresholdLeanXmssSecurity.setupSecurityDistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.setupSecurityDistance

/-- info: 'ThresholdLeanXmssSecurity.seedGenSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.seedGenSecurity
