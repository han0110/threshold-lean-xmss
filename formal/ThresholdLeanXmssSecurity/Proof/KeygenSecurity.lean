import ThresholdLeanXmssSecurity.Proof.Keygen

/-!
# Keygen security: the coupling

This module closes `KeygenCoupling` of `Proof/Keygen.lean`, and with it `KeygenSecurityStatement`.

1. A coupling with a private coin as the bad flag turns any distance bound into an identical-until-bad
   pair. Every probability of a finite computation is rational, so the coin exists.
2. The hybrid: the emulated outputs with the dealer's hidden keys (`keygenMixedGame`). The known half
   `KeygenKnownMismatch` bounds the mismatch with the ideal outputs.
3. The hidden half. The dealer's hidden keys are independent of the corrupt leak, so the mixed game is
   the real run whose distinguisher replaces the hidden keys by fresh ones (`keygenHiddenZ`). The real
   run is a mixture of fixed-table reference runs on a common covering domain. On distinct canonical
   inputs, the hidden oracle cells and an independent dealer table exchange (the relabeling), so the
   open claim is `KeygenHiddenFreshSwapped`, on the relabeled reference runs.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

set_option pp.deepTerms false
set_option pp.maxSteps 2000

/-- The probability of every event of a finite computation is a nonnegative rational. -/
theorem probEvent_rational {α : Type} (oa : ProbComp α) (p : α → Prop) :
    ∃ r : ℚ, 0 ≤ r ∧ Pr[p | oa] = ENNReal.ofReal r := by
  classical
  induction oa using ProbComp.inductionOn with
  | pure a =>
    by_cases hp : p a
    · exact ⟨1, zero_le_one, by simp [hp]⟩
    · exact ⟨0, le_rfl, by simp [hp]⟩
  | query_bind n mx ih =>
    choose r hr hpr using ih
    refine ⟨∑ m, r m / (n + 1), Finset.sum_nonneg fun m _ => div_nonneg (hr m) (by positivity), ?_⟩
    rw [probEvent_bind_eq_tsum, tsum_fintype]
    push_cast
    rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => div_nonneg (by exact_mod_cast hr m) (by positivity))]
    apply Finset.sum_congr rfl
    intro m _
    rw [ProbComp.probOutput_uniformFin, hpr m, div_eq_mul_inv, ENNReal.ofReal_mul (by exact_mod_cast hr m)]
    rw [mul_comm]
    congr 1
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp

/-- A coin with any rational probability. -/
def ratCoin (a m : ℕ) : ProbComp Bool := (fun u : Fin (m + 1) => decide (u.val < a)) <$> $[0..m]

theorem probOutput_ratCoin_true (a m : ℕ) (ha : a ≤ m + 1) :
    Pr[= true | ratCoin a m] = (a : ℝ≥0∞) / (m + 1) := by
  unfold ratCoin
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  have hf : ((fun b => b = true) ∘ fun u : Fin (m + 1) => decide (u.val < a)) = fun u => u.val < a := by
    funext u; simp
  rw [hf, ProbComp.probEvent_uniformFin]
  have hc : Fin.countP (fun i : Fin (m + 1) => decide (i.val < a)) = a := by
    have h1 := Fin.card_eq_countP_mem ({i : Fin (m + 1) | i.val < a} : Finset (Fin (m + 1)))
    rw [Fin.card_filter_val_lt] at h1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
    rw [← h1]
    omega
  rw [hc]
  push_cast
  rfl

/-- A coin with each rational probability in `[0, 1]`. -/
theorem exists_coin (α : ℚ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∃ coin : ProbComp Bool, Pr[= true | coin] = ENNReal.ofReal α ∧
      Pr[= false | coin] = ENNReal.ofReal (1 - α) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = α.num := ⟨α.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr h0)⟩
  have hden := α.den_pos
  have hα : (α : ℝ) = (a : ℝ) / α.den := by
    rw [Rat.cast_def, ← ha]
    push_cast
    ring
  have hle : a ≤ α.den := by
    have : (a : ℝ) / α.den ≤ 1 := by rw [← hα]; exact_mod_cast h1
    rw [div_le_one (by exact_mod_cast hden)] at this
    exact_mod_cast this
  have hm : α.den - 1 + 1 = α.den := by omega
  have ht : Pr[= true | ratCoin a (α.den - 1)] = ENNReal.ofReal α := by
    rw [probOutput_ratCoin_true a _ (by omega), hα, ENNReal.ofReal_div_of_pos (by exact_mod_cast hden)]
    have hcast : ((α.den - 1 : ℕ) : ℝ≥0∞) + 1 = (α.den : ℝ≥0∞) := by exact_mod_cast hm
    rw [hcast]
    simp
  refine ⟨ratCoin a (α.den - 1), ht, ?_⟩
  have hs := probOutput_false_eq_sub (ratCoin a (α.den - 1))
  rw [hs, ht, probFailure_eq_zero, tsub_zero, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by exact_mod_cast h0)]

variable {C : Committee}

/-- A game whose bad flag is a private coin on its acceptance. -/
def coinFlagged (g : OracleComp (WorldSpec C) Bool) (coin : ProbComp Bool) :
    OracleComp (WorldSpec C) (Bool × Bool) :=
  g >>= fun b => (fun c => (b, b && c)) <$> free (liftComp coin (LocalSpec C))

theorem run_coinFlagged (prims : Primitives) (g : OracleComp (WorldSpec C) Bool) (coin : ProbComp Bool) :
    (simulateQ (worldAnswer prims) (coinFlagged g coin)).run' ∅ =
      (simulateQ (worldAnswer prims) g).run' ∅ >>= fun b => (fun c => (b, b && c)) <$> coin := by
  unfold coinFlagged
  simp only [simulateQ_bind, simulateQ_map, simulateQ_world_sample, StateT.run'_eq, StateT.run_bind,
    StateT.run_map, StateT.run_lift, map_bind, bind_map_left, Functor.map_map]
  simp [map_eq_bind_pure_comp]

theorem probEvent_runWorld_fst (prims : Primitives) {β : Type} (oa : OracleComp (WorldSpec C) β)
    (Q : β → Prop) :
    Pr[fun r => Q r.1 | runWorld prims oa] = Pr[Q | (simulateQ (worldAnswer prims) oa).run' ∅] := by
  rw [← fst_map_runWorld, probEvent_map]
  rfl


theorem probEvent_flag (P coin : ProbComp Bool) (Q : Bool × Bool → Prop) :
    Pr[Q | P >>= fun b => (fun c => (b, b && c)) <$> coin] =
      Pr[= true | P] * Pr[fun c => Q (true, c) | coin] +
        Pr[= false | P] * (if Q (false, false) then 1 else 0) := by
  classical
  rw [probEvent_bind_eq_tsum, tsum_fintype, Fintype.sum_bool, probEvent_map, probEvent_map]
  congr 1
  by_cases hq : Q (false, false)
  · simp [Function.comp_def, hq]
  · simp [Function.comp_def, hq]

theorem accepts_eq_probOutput (prims : Primitives) (g : OracleComp (WorldSpec C) Bool) :
    accepts prims g = (Pr[= true | (simulateQ (worldAnswer prims) g).run' ∅]).toReal := by
  unfold accepts
  rw [probEvent_runWorld_fst prims g (fun b => b = true), probEvent_eq_eq_probOutput]

/-- The coin-flagged game keeps the acceptance of its game, and its flag is the coin on acceptance. -/
theorem coinFlagged_spec (prims : Primitives) (g : OracleComp (WorldSpec C) Bool) (coin : ProbComp Bool) :
    accepts prims (Prod.fst <$> coinFlagged g coin) = accepts prims g ∧
      Pr[fun r => r.1 = (true, false) | runWorld prims (coinFlagged g coin)] =
        Pr[= true | (simulateQ (worldAnswer prims) g).run' ∅] * Pr[= false | coin] ∧
      Pr[fun r => r.1.2 = true | runWorld prims (coinFlagged g coin)] =
        Pr[= true | (simulateQ (worldAnswer prims) g).run' ∅] * Pr[= true | coin] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [accepts_eq_probOutput prims g]
    unfold accepts
    rw [runWorld_map, probEvent_map]
    congr 1
    have h := probEvent_runWorld_fst prims (coinFlagged g coin) (fun p => p.1 = true)
    simp only [Function.comp_def]
    rw [h, run_coinFlagged, probEvent_flag]
    simp
  · rw [probEvent_runWorld_fst prims (coinFlagged g coin) (fun p => p = (true, false)), run_coinFlagged,
      probEvent_flag]
    simp
  · rw [probEvent_runWorld_fst prims (coinFlagged g coin) (fun p => p.2 = true), run_coinFlagged,
      probEvent_flag]
    simp

/-- The coin of one side: it flags the excess acceptance of this side over the other. -/
theorem exists_excess_coin (ra rb : ℚ) (ha : 0 ≤ ra) (hb : 0 ≤ rb) :
    ∃ coin : ProbComp Bool,
      ENNReal.ofReal ra * Pr[= false | coin] = ENNReal.ofReal ((min ra rb : ℚ) : ℝ) ∧
      ENNReal.ofReal ra * Pr[= true | coin] = ENNReal.ofReal ((ra - min ra rb : ℚ) : ℝ) := by
  by_cases h0 : ra = 0
  · obtain ⟨coin, ht, hf⟩ := exists_coin 0 le_rfl zero_le_one
    refine ⟨coin, ?_, ?_⟩ <;> simp [h0, min_eq_left hb]
  · have hpos : 0 < ra := lt_of_le_of_ne ha (Ne.symm h0)
    set α : ℚ := (ra - min ra rb) / ra with hα
    have hα0 : 0 ≤ α := div_nonneg (by linarith [min_le_left ra rb]) ha
    have hα1 : α ≤ 1 := by
      rw [hα, div_le_one hpos]; linarith [le_min ha hb]
    obtain ⟨coin, ht, hf⟩ := exists_coin α hα0 hα1
    refine ⟨coin, ?_, ?_⟩
    · rw [hf, ← ENNReal.ofReal_mul (by exact_mod_cast ha)]
      congr 1
      have : (ra : ℝ) * (1 - (α : ℝ)) = ((ra * (1 - α) : ℚ) : ℝ) := by push_cast; ring
      rw [this]
      congr 1
      rw [hα]
      field_simp
      ring
    · rw [ht, ← ENNReal.ofReal_mul (by exact_mod_cast ha)]
      congr 1
      have : (ra : ℝ) * (α : ℝ) = ((ra * α : ℚ) : ℝ) := by push_cast; ring
      rw [this]
      congr 1
      rw [hα]
      field_simp

/-- Every distance bound between two games gives an identical-until-bad pair with the same bound. -/
theorem coupling_of_abs_accepts_le (prims : Primitives) (ga gb : OracleComp (WorldSpec C) Bool) (ε : ℝ)
    (h : |accepts prims ga - accepts prims gb| ≤ ε) :
    ∃ oa ob : OracleComp (WorldSpec C) (Bool × Bool),
      accepts prims (Prod.fst <$> oa) = accepts prims ga ∧
      accepts prims (Prod.fst <$> ob) = accepts prims gb ∧
      Pr[fun r => r.1 = (true, false) | runWorld prims oa] =
        Pr[fun r => r.1 = (true, false) | runWorld prims ob] ∧
      Pr[fun r => r.1.2 = true | runWorld prims oa].toReal ≤ ε ∧
      Pr[fun r => r.1.2 = true | runWorld prims ob].toReal ≤ ε := by
  obtain ⟨ra, ha, hra⟩ := probEvent_rational ((simulateQ (worldAnswer prims) ga).run' ∅) (· = true)
  obtain ⟨rb, hb, hrb⟩ := probEvent_rational ((simulateQ (worldAnswer prims) gb).run' ∅) (· = true)
  rw [probEvent_eq_eq_probOutput] at hra hrb
  have hacc_a : accepts prims ga = ra := by
    rw [accepts_eq_probOutput, hra, ENNReal.toReal_ofReal (by exact_mod_cast ha)]
  have hacc_b : accepts prims gb = rb := by
    rw [accepts_eq_probOutput, hrb, ENNReal.toReal_ofReal (by exact_mod_cast hb)]
  rw [hacc_a, hacc_b] at h
  obtain ⟨ca, hfa, hta⟩ := exists_excess_coin ra rb ha hb
  obtain ⟨cb, hfb, htb⟩ := exists_excess_coin rb ra hb ha
  obtain ⟨sa₁, sa₂, sa₃⟩ := coinFlagged_spec prims ga ca
  obtain ⟨sb₁, sb₂, sb₃⟩ := coinFlagged_spec prims gb cb
  refine ⟨coinFlagged ga ca, coinFlagged gb cb, sa₁, sb₁, ?_, ?_, ?_⟩
  · rw [sa₂, sb₂, hra, hrb, hfa, hfb, min_comm]
  · have hq : ra - min ra rb ≤ |ra - rb| := by
      rcases le_total ra rb with hle | hle
      · rw [min_eq_left hle]; simp
      · rw [min_eq_right hle]; exact le_abs_self _
    have hq' : ((ra - min ra rb : ℚ) : ℝ) ≤ ε := le_trans (by exact_mod_cast hq) h
    rw [sa₃, hra, hta, ENNReal.toReal_ofReal (by exact_mod_cast sub_nonneg.mpr (min_le_left ra rb))]
    exact hq'
  · have hq : rb - min rb ra ≤ |ra - rb| := by
      rcases le_total ra rb with hle | hle
      · rw [min_eq_right hle, abs_sub_comm]; exact le_abs_self _
      · rw [min_eq_left hle]; simp
    have hq' : ((rb - min rb ra : ℚ) : ℝ) ≤ ε := le_trans (by exact_mod_cast hq) h
    rw [sb₃, hrb, htb, ENNReal.toReal_ofReal (by exact_mod_cast sub_nonneg.mpr (min_le_left rb ra))]
    exact hq'

/-- The coupling form of the keygen claim follows from its distance form. -/
theorem keygenCoupling_of_distance (prims : Primitives) {E : Type}
    (h : KeygenSecurityDistance (C := C) (E := E) prims) :
    KeygenCoupling (C := C) (E := E) prims := by
  intro D A x z Z q hq
  exact coupling_of_abs_accepts_le prims _ _ _ (h D A x z Z q hq)

/-! ## Two continuations of one game -/

theorem run'_bind_world (prims : Primitives) {R β : Type} (g : OracleComp (WorldSpec C) R)
    (k : R → OracleComp (WorldSpec C) β) :
    (simulateQ (worldAnswer prims) (g >>= k)).run' ∅ =
      (simulateQ (worldAnswer prims) g).run ∅ >>= fun p => (simulateQ (worldAnswer prims) (k p.1)).run' p.2 := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Two continuations of one game differ by at most the probability that they differ. -/
theorem abs_accepts_bind_sub_le_keygen (prims : Primitives) {R : Type} (g : OracleComp (WorldSpec C) R)
    (k₁ k₂ : R → OracleComp (WorldSpec C) Bool) :
    |accepts prims (g >>= k₁) - accepts prims (g >>= k₂)| ≤
      (Pr[fun r => k₁ r.1 ≠ k₂ r.1 | runWorld prims g]).toReal := by
  let flag (k : R → OracleComp (WorldSpec C) Bool) : OracleComp (WorldSpec C) (Bool × Bool) :=
    g >>= fun r => (fun b => (b, decide (k₁ r ≠ k₂ r))) <$> k r
  have hfst (k : R → OracleComp (WorldSpec C) Bool) : Prod.fst <$> flag k = g >>= k := by
    simp only [flag, map_bind, Functor.map_map, id_map']
  have hbad (k : R → OracleComp (WorldSpec C) Bool) :
      Pr[fun r => r.1.2 = true | runWorld prims (flag k)] =
        Pr[fun r => k₁ r.1 ≠ k₂ r.1 | runWorld prims g] := by
    rw [probEvent_runWorld_fst prims (flag k) (fun p => p.2 = true),
      probEvent_runWorld_fst prims g (fun r => k₁ r ≠ k₂ r), run'_bind_world]
    rw [StateT.run'_eq, probEvent_map, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    apply tsum_congr
    intro p
    rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, probEvent_map]
    by_cases hp : k₁ p.1 ≠ k₂ p.1
    · simp [Function.comp_def, hp]
    · simp [Function.comp_def, hp]
  have heq : Pr[fun r => r.1 = (true, false) | runWorld prims (flag k₁)] =
      Pr[fun r => r.1 = (true, false) | runWorld prims (flag k₂)] := by
    rw [probEvent_runWorld_fst prims (flag k₁) (fun p => p = (true, false)),
      probEvent_runWorld_fst prims (flag k₂) (fun p => p = (true, false)), run'_bind_world, run'_bind_world,
      probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    apply tsum_congr
    intro p
    congr 1
    by_cases hp : k₁ p.1 = k₂ p.1
    · rw [hp]
    · rw [simulateQ_map, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, StateT.run_map,
        probEvent_map, probEvent_map, probEvent_map, probEvent_map]
      simp [Function.comp_def, hp]
  have h := abs_accepts_sub_le_of_eq_until_bad prims (flag k₁) (flag k₂) heq
  rw [hfst, hfst, hbad, hbad, max_self] at h
  exact h

/-! ## The hybrid between the emulated and the dealt outputs -/

section Hybrid

variable {E : Type}

/-- The keys `k` with the hidden coordinates of `d`, for operator `i`. -/
def keygenHiddenOverlay (D : C.Coalition) (i : C.Party) (k d : Keys C) : Keys C :=
  ⟨k.parameter, fun T => if KnownTo D.1 T then k.seed T else d.seed T,
    fun j => if i ∈ D.1 ∨ j ∈ D.1 then k.pairKey j else d.pairKey j⟩

/-- The emulated outputs with the hidden coordinates of the dealer. -/
def keygenMixedProjection {σ : Type} (D : C.Coalition) (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) :
    σ × (C.Party → Option (Keys C)) :=
  (r.1, fun i => (r.2.1 i).map fun k => keygenHiddenOverlay D i k (r.2.2 i))

/-- The hybrid game: the common game, and the distinguisher on the mixed outputs. -/
def keygenMixedGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) Bool :=
  distinguish (keygenMixedProjection D <$> keygenCommonGame D A x z) Z

/-- Hidden half: the hidden keys of the real run are indistinguishable from the dealer's. -/
def KeygenHiddenDistance (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (keygenCommonEmulatedGame D A x z Z) - accepts prims (keygenMixedGame D A x z Z)| ≤
      keygenHashError C q / 2

/-- Known half: the simulator's programming fixes every exposed coordinate of an accepted output. -/
def KeygenKnownMismatch (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr[fun r => keygenMixedProjection D r.1 ≠ keygenIdealProjection D r.1 |
      runWorld prims (keygenCommonGame D A x z)]).toReal ≤ keygenHashError C q / 2

theorem abs_accepts_mixed_ideal_le (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    |accepts prims (keygenMixedGame D A x z Z) -
        accepts prims (distinguish (idealExecution (fun oa => oa) D Fkeygen (keygenSimulator D A) x z) Z)| ≤
      (Pr[fun r => keygenMixedProjection D r.1 ≠ keygenIdealProjection D r.1 |
        runWorld prims (keygenCommonGame D A x z)]).toReal := by
  rw [← keygenCommonGame_ideal]
  unfold keygenMixedGame distinguish
  simp only [bind_map_left]
  refine (abs_accepts_bind_sub_le_keygen prims _ _ _).trans ?_
  apply ENNReal.toReal_mono probEvent_ne_top
  apply probEvent_mono
  intro r _ hr he
  exact hr (by rw [he])

/-- The distance half of the keygen claim from its two hybrid halves. -/
theorem keygenSecurityDistance_of_hybrids (prims : Primitives)
    (hH : KeygenHiddenDistance (C := C) (E := E) prims) (hK : KeygenKnownMismatch (C := C) (E := E) prims) :
    KeygenSecurityDistance (C := C) (E := E) prims := by
  intro D A x z Z q hq
  rw [← keygenCommonGame_real_accepts prims D A x z Z]
  have h₁ := hH D A x z Z q hq
  have h₂ := (abs_accepts_mixed_ideal_le prims D A x z Z).trans (hK D A x z Z q hq)
  calc _ ≤ |accepts prims (keygenCommonEmulatedGame D A x z Z) - accepts prims (keygenMixedGame D A x z Z)| +
        |accepts prims (keygenMixedGame D A x z Z) -
          accepts prims (distinguish (idealExecution (fun oa => oa) D Fkeygen (keygenSimulator D A) x z) Z)| :=
        abs_sub_le _ _ _
    _ ≤ keygenHashError C q / 2 + keygenHashError C q / 2 := add_le_add h₁ h₂
    _ = keygenHashError C q := by ring

end Hybrid

/-! ## The hidden half on the real run -/

section RealHidden

variable {E : Type}

/-- The distinguisher that replaces the hidden coordinates of each output by fresh uniform keys. -/
def keygenHiddenZ (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C)) : Distinguisher C σ (Keys C) :=
  fun r => do
    let seeds ← liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C)
    let pairs ← liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C)
    Z (r.1, fun i => (r.2 i).map fun k => keygenHiddenOverlay D i k (dealtKeys 0 seeds pairs i))

theorem simulateQ_local_sample_keygensecurity (prims : Primitives) {α : Type} (p : ProbComp α) :
    simulateQ (localAnswer (C := C) prims) (liftComp p (LocalSpec C)) = StateT.lift p := by
  rw [show simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p from
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p]
  funext s
  change (simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p).run s = p >>= fun a => pure (a, s)
  rw [unifFwdImpl.simulateQ_run]
  rfl

/-- The dealer's corrupt keys, as the simulator receives them. -/
def keygenCorruptLeak (D : C.Coalition) (d : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) :
    C.Party → Option (Keys C) :=
  fun i => if i ∈ D.1 then some (dealtKeys d.1 d.2.1 d.2.2 i) else none

theorem keygenMixedGame_expand (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    keygenMixedGame D A x z Z = (do
      let st ← (keygenSimulator D A).start (corruptInputs D x) z
      let d ← free (liftComp (keygenDealerSamples (C := C)) (LocalSpec C))
      let r ← keygenEmulation D A st d.1 (keygenCorruptLeak D d)
      worldRoles.adversary (Z (keygenMixedProjection D (r.1.adversary, r.2, dealtKeys d.1 d.2.1 d.2.2)))) := by
  unfold keygenMixedGame distinguish keygenCommonGame keygenDealerSamples prawnsKeyGen keygenCorruptLeak
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure]

theorem keygenCommonEmulatedGame_expand' (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    keygenCommonEmulatedGame D A x z Z = (do
      let st ← (keygenSimulator D A).start (corruptInputs D x) z
      let d ← free (liftComp (keygenDealerSamples (C := C)) (LocalSpec C))
      let r ← keygenEmulation D A st d.1 (keygenCorruptLeak D d)
      worldRoles.adversary (Z (r.1.adversary, r.2))) := by
  unfold keygenCommonEmulatedGame distinguish keygenCommonGame keygenDealerSamples prawnsKeyGen keygenCorruptLeak
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure, keygenEmulatedProjection]

/-- Replace the coordinates in `P` of a uniform table by those of a second uniform table. -/
theorem evalDist_piecewise_uniform {ι H β : Type} [Fintype ι] [DecidableEq ι] [Fintype H] [Nonempty H]
    [SampleableType H] [SampleableType (ι → H)] (P : ι → Prop) [DecidablePred P]
    (k : (ι → H) → ProbComp β) :
    𝒟[do let f ← $ᵗ (ι → H); let g ← $ᵗ (ι → H); k (fun i => if P i then g i else f i)] =
      𝒟[do let f ← $ᵗ (ι → H); k f] := by
  let Ψ : (ι → H) × (ι → H) → (ι → H) × (ι → H) := fun p =>
    (fun i => if P i then p.2 i else p.1 i, fun i => if P i then p.1 i else p.2 i)
  have hΨ : Function.Involutive Ψ := by
    intro p
    apply Prod.ext <;> funext i <;> by_cases h : P i <;> simp [Ψ, h]
  have e1 : (do let f ← $ᵗ (ι → H); let g ← $ᵗ (ι → H); k (fun i => if P i then g i else f i)) =
      ($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1 := by
    change _ = ((·, ·) <$> ($ᵗ (ι → H)) <*> ($ᵗ (ι → H))) >>= _
    simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Ψ]
  have e2 : 𝒟[($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1] =
      𝒟[($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1] := by
    have h : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1) =
        (Ψ <$> ($ᵗ ((ι → H) × (ι → H)))) >>= fun p => k p.1 := by rw [bind_map_left]
    rw [h, evalDist_bind, evalDist_map_bijective_uniform_cross _ _ hΨ.bijective, ← evalDist_bind]
  have e3 : 𝒟[($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1] = 𝒟[($ᵗ (ι → H)) >>= k] := by
    have h : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1) =
        (Prod.fst <$> ($ᵗ ((ι → H) × (ι → H)))) >>= k := by rw [bind_map_left]
    rw [h, evalDist_bind, evalDist_map_fst_uniformSample_prod, ← evalDist_bind]
  rw [e1, e2, e3]

/-- A hidden name of the dealer's tables. -/
def KeygenHiddenTerm (D : C.Coalition) (T : C.Term) : Prop := ¬ KnownTo D.1 T

def KeygenHiddenPair (D : C.Coalition) (p : C.Pair) : Prop := p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1

theorem keygenHiddenPair_pairOf (D : C.Coalition) (i j : C.Party) (h : i ≠ j) :
    KeygenHiddenPair D (C.pairOf i j h) ↔ i ∉ D.1 ∧ j ∉ D.1 := by
  unfold KeygenHiddenPair Committee.pairOf
  split_ifs <;> simp [and_comm]

theorem keygenCorruptLeak_piecewise (D : C.Coalition) (parameter : PublicParameter)
    (seeds seeds' : C.Term → HashOutput) (pairs pairs' : C.Pair → HashOutput) :
    keygenCorruptLeak D (parameter, (fun T => if KeygenHiddenTerm D T then seeds' T else seeds T),
      (fun p => if KeygenHiddenPair D p then pairs' p else pairs p)) =
      keygenCorruptLeak D (parameter, seeds, pairs) := by
  funext j
  unfold keygenCorruptLeak
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj, dealtKeys, Option.some.injEq, Keys.mk.injEq, true_and]
    constructor
    · funext T
      by_cases hT : j ∈ C.holders T
      · have hk : ¬ KeygenHiddenTerm D T := fun h => h ⟨j, hj, hT⟩
        simp [hT, hk]
      · simp [hT]
    · funext i
      by_cases hij : i = j
      · simp [hij]
      · have hk : ¬ KeygenHiddenPair D (C.pairOf j i (Ne.symm hij)) := by
          rw [keygenHiddenPair_pairOf]; exact fun h => h.1 hj
        simp [hij, hk]
  · simp [hj]

theorem keygenHiddenOverlay_piecewise (D : C.Coalition) (i : C.Party) (k : Keys C) (parameter : PublicParameter)
    (seeds seeds' : C.Term → HashOutput) (pairs pairs' : C.Pair → HashOutput) :
    keygenHiddenOverlay D i k (dealtKeys parameter (fun T => if KeygenHiddenTerm D T then seeds' T else seeds T)
      (fun p => if KeygenHiddenPair D p then pairs' p else pairs p) i) =
      keygenHiddenOverlay D i k (dealtKeys 0 seeds' pairs' i) := by
  unfold keygenHiddenOverlay dealtKeys
  simp only [Keys.mk.injEq, true_and]
  constructor
  · funext T
    by_cases hT : KnownTo D.1 T
    · simp [hT]
    · have hk : KeygenHiddenTerm D T := hT
      simp [hT, hk]
  · funext j
    by_cases hc : i ∈ D.1 ∨ j ∈ D.1
    · simp [hc]
    · simp only [if_neg hc]
      by_cases hij : j = i
      · simp [hij]
      · have hk : KeygenHiddenPair D (C.pairOf i j (Ne.symm hij)) := by
          rw [keygenHiddenPair_pairOf]; exact not_or.mp hc
        simp [hij, hk]

/-- The dealer's hidden coordinates can be replaced by those of an independent second dealer. -/
theorem evalDist_dealer_piecewise (D : C.Coalition) {β : Type}
    (k : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput) → ProbComp β) :
    𝒟[do
      let d ← keygenDealerSamples (C := C)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (d.1, (fun T => if KeygenHiddenTerm D T then seeds' T else d.2.1 T),
        (fun p => if KeygenHiddenPair D p then pairs' p else d.2.2 p))] =
      𝒟[keygenDealerSamples (C := C) >>= k] := by
  unfold keygenDealerSamples
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr'
  intro parameter
  have hswap : 𝒟[do
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, (fun T => if KeygenHiddenTerm D T then seeds' T else seeds T),
        (fun p => if KeygenHiddenPair D p then pairs' p else pairs p))] =
      𝒟[do
      let seeds ← $ᵗ (C.Term → HashOutput)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, (fun T => if KeygenHiddenTerm D T then seeds' T else seeds T),
        (fun p => if KeygenHiddenPair D p then pairs' p else pairs p))] := by
    apply evalDist_bind_congr'
    intro seeds
    exact DeferredSampling.evalDist_bind_comm _ _ _
  rw [hswap]
  refine (evalDist_piecewise_uniform (KeygenHiddenTerm D) (fun s => do
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, s, (fun p => if KeygenHiddenPair D p then pairs' p else pairs p)))).trans ?_
  apply evalDist_bind_congr'
  intro seeds
  exact evalDist_piecewise_uniform (KeygenHiddenPair D) (fun p => k (parameter, seeds, p))

theorem evalDist_run'_of_run {σ α : Type} {X Y : StateT σ ProbComp α} (s : σ)
    (h : 𝒟[X.run s] = 𝒟[Y.run s]) : 𝒟[X.run' s] = 𝒟[Y.run' s] := by
  simp only [StateT.run'_eq, evalDist_map, h]

/-- Two independent samples move before a computation. -/
theorem evalDist_bind_two_comm {α β γ δ : Type} (m : ProbComp α) (p₁ : ProbComp β)
    (p₂ : ProbComp γ) (k : α → β → γ → ProbComp δ) :
    𝒟[m >>= fun r => p₁ >>= fun a => p₂ >>= fun b => k r a b] =
      𝒟[p₁ >>= fun a => p₂ >>= fun b => m >>= fun r => k r a b] := by
  rw [DeferredSampling.evalDist_bind_comm]
  apply evalDist_bind_congr'
  intro a
  exact DeferredSampling.evalDist_bind_comm _ _ _

/-- The mixed game is the emulated game whose distinguisher replaces the hidden keys by fresh ones. -/
theorem evalDist_keygenMixedGame_hiddenZ (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    𝒟[(simulateQ (worldAnswer prims) (keygenMixedGame D A x z Z)).run' ∅] =
      𝒟[(simulateQ (worldAnswer prims) (keygenCommonEmulatedGame D A x z (keygenHiddenZ D Z))).run' ∅] := by
  rw [keygenMixedGame_expand, keygenCommonEmulatedGame_expand']
  unfold keygenHiddenZ
  simp only [simulateQ_bind, simulateQ_world_sample, simulateQ_world_adversary, simulateQ_local_sample_keygensecurity]
  apply evalDist_stateT_run'_bind_congr
  intro st s
  apply evalDist_run'_of_run
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  symm
  refine (evalDist_bind_congr' _ fun d => evalDist_bind_two_comm _ _ _ _).trans ?_
  conv_rhs => rw [← evalDist_dealer_piecewise D]
  apply evalDist_bind_congr'
  intro d
  apply evalDist_bind_congr'
  intro a
  apply evalDist_bind_congr'
  intro b
  rw [keygenCorruptLeak_piecewise]
  simp only [keygenMixedProjection, keygenHiddenOverlay_piecewise]

theorem keygenMixedGame_accepts (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (keygenMixedGame D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) (keygenHiddenZ D Z)) := by
  rw [← keygenCommonGame_real_accepts, accepts_eq_probOutput, accepts_eq_probOutput, probOutput_def,
    probOutput_def, evalDist_keygenMixedGame_hiddenZ]

/-- Hidden half on the real run: the hidden keys of the honest outputs are indistinguishable from
fresh uniform keys. -/
def KeygenHiddenFresh (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) -
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) (keygenHiddenZ D Z))| ≤
      keygenHashError C q / 2

theorem keygenHiddenDistance_of_fresh (prims : Primitives) (h : KeygenHiddenFresh (C := C) (E := E) prims) :
    KeygenHiddenDistance (C := C) (E := E) prims := by
  intro D A x z Z q hq
  rw [keygenCommonGame_real_accepts, keygenMixedGame_accepts]
  exact h D A x z Z q hq

/-- The real run as a mixture of fixed-table reference runs, on every oracle domain that covers it. -/
def keygenReferenceMixture (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) :
    ProbComp Bool := do
  let ht ← $ᵗ (S → HashOutput)
  let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let h := keygenFiniteTotal prims S ht
  simulateQ (fixedLocal prims h)
    (keygenReferenceLocalGame prims D h (fun name => h (keygenNamedInput parts name)) A x z Z parts)

theorem evalDist_keygenReal_referenceMixture (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hS : KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z))) :
    𝒟[(simulateQ (worldAnswer prims)
        (distinguish (realExecution D A noFunctionality setupRounds
          (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z)).run' ∅] =
      𝒟[keygenReferenceMixture prims D A x z Z S] := by
  have he := evalDist_keygenWorld_eager prims S (free (keygenNormalizedLocalGame D A x z Z)) hS ∅
  simp only [worldAnswer, keygenFiniteWorld, simulateQ_free] at he
  have hc : keygenRestrictCache S (∅ : HashCache C) = ∅ := rfl
  simp only [hc, keygenFiniteLocal_eager_fixed, tableExtending_empty] at he
  rw [simulateQ_keygenReal_eq_local, (sameRun_keygenLocal_normalized prims D A x z Z).run'_eq, he]
  unfold keygenReferenceMixture
  apply evalDist_bind_congr'
  intro ht
  exact evalDist_keygenNormalized_fixed_reference prims D (keygenFiniteTotal prims S ht) A x z Z

/-- Hidden half on fixed-table reference runs: for every oracle domain that covers both runs and
every canonical input, replacing the hidden output keys by fresh ones moves the acceptance by at
most half the error. -/
def KeygenHiddenFreshReference (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∀ S : Finset (Query C), (∀ parts name, keygenNamedInput parts name ∈ S) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z)) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z))) →
      |(Pr[= true | keygenReferenceMixture prims D A x z Z S]).toReal -
        (Pr[= true | keygenReferenceMixture prims D A x z (keygenHiddenZ D Z) S]).toReal| ≤
        keygenHashError C q / 2

theorem keygenHiddenFresh_of_reference (prims : Primitives)
    (h : KeygenHiddenFreshReference (C := C) (E := E) prims) :
    KeygenHiddenFresh (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨S₁, h₁⟩ := keygenWorldCovered_exists (free (keygenNormalizedLocalGame D A x z Z))
  obtain ⟨S₂, h₂⟩ := keygenWorldCovered_exists (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z)))
  let S := S₁ ∪ S₂ ∪ keygenAllNamedInputs C
  have hS₁ : KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z)) :=
    h₁.mono (fun _ hq => Finset.mem_union_left _ (Finset.mem_union_left _ hq))
  have hS₂ : KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z))) :=
    h₂.mono (fun _ hq => Finset.mem_union_left _ (Finset.mem_union_right _ hq))
  have hmem : ∀ parts name, keygenNamedInput parts name ∈ S :=
    fun parts name => Finset.mem_union_right _ (keygenAllNamedInputs_mem parts name)
  rw [accepts_eq_probOutput, accepts_eq_probOutput, probOutput_def, probOutput_def,
    evalDist_keygenReal_referenceMixture prims D A x z Z S hS₁,
    evalDist_keygenReal_referenceMixture prims D A x z (keygenHiddenZ D Z) S hS₂,
    ← probOutput_def, ← probOutput_def]
  exact h D A x z Z q hq S hmem hS₁ hS₂

/-! ### The relabeling of the hidden keys -/

theorem keygenMaskKeys_table_congr (D : C.Coalition) (t t' : KeyName C → HashOutput)
    (ht : ∀ name, Hidden D name → t name = t' name) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    keygenMaskKeys D t i keys = keygenMaskKeys D t' i keys := by
  unfold keygenMaskKeys
  congr 2
  · funext T
    by_cases hT : KnownTo D.1 T
    · simp [hT]
    · simp only [if_neg hT]
      rw [ht (.term T) hT]
  · funext j
    by_cases hj : j = i
    · simp [hj]
    · simp only [dif_neg hj]
      by_cases hc : i ∈ D.1 ∨ j ∈ D.1
      · simp [hc]
      · simp only [if_neg hc]
        apply ht
        change (C.pairOf i j (Ne.symm hj)).1.1 ∉ D.1 ∧ (C.pairOf i j (Ne.symm hj)).1.2 ∉ D.1
        exact (keygenHiddenPair_pairOf D i j (Ne.symm hj)).mpr (not_or.mp hc)

/-- The reference run reads its table only at the hidden names. -/
theorem keygenReferenceLocalGame_table_congr (prims : Primitives) (D : C.Coalition)
    (h : Query C → HashOutput) (t t' : KeyName C → HashOutput)
    (ht : ∀ name, Hidden D name → t name = t' name)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    keygenReferenceLocalGame prims D h t A x z Z parts = keygenReferenceLocalGame prims D h t' A x z Z parts := by
  have hk : keygenReferenceKeys (E := E) prims D h t parts = keygenReferenceKeys prims D h t' parts := by
    funext revealed i
    exact keygenMaskKeys_table_congr D t t' ht i _
  have hd : keygenReferenceData (E := E) prims D h t parts = keygenReferenceData prims D h t' parts := by
    funext commitSent revealSent i
    simp only [keygenReferenceData, hk]
  simp only [keygenReferenceLocalGame, keygenReferencePostCommit, hd]

/-- The reference mixture after the relabeling: on distinct canonical inputs, the hidden keys are an
independent dealer table, and the oracle answers the hidden canonical inputs with the dealer's keys. -/
def keygenSwappedMixture (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, keygenNamedInput parts name ∈ S) : ProbComp Bool := do
  let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
  let ht := if Function.Injective (keygenNamedInput parts) then
    (keygenFiniteHiddenSwap D S parts (hmem parts) p).1 else p.1
  let h := keygenFiniteTotal prims S ht
  let table := if Function.Injective (keygenNamedInput parts) then p.2 else
    fun name => h (keygenNamedInput parts name)
  simulateQ (fixedLocal prims h) (keygenReferenceLocalGame prims D h table A x z Z parts)

theorem evalDist_keygenReferenceMixture_swap (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, keygenNamedInput parts name ∈ S) :
    𝒟[keygenReferenceMixture prims D A x z Z S] = 𝒟[keygenSwappedMixture prims D A x z Z S hmem] := by
  unfold keygenReferenceMixture keygenSwappedMixture
  rw [DeferredSampling.evalDist_bind_comm]
  apply evalDist_bind_congr'
  intro parts
  let F : (S → HashOutput) → ProbComp Bool := fun ht =>
    simulateQ (fixedLocal prims (keygenFiniteTotal prims S ht))
      (keygenReferenceLocalGame prims D (keygenFiniteTotal prims S ht)
        (fun name => keygenFiniteTotal prims S ht (keygenNamedInput parts name)) A x z Z parts)
  have hfst : 𝒟[($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p => F p.1] =
      𝒟[($ᵗ (S → HashOutput)) >>= F] := by
    rw [← bind_map_left Prod.fst, evalDist_bind, evalDist_map_fst_uniformSample_prod, ← evalDist_bind]
  change 𝒟[($ᵗ (S → HashOutput)) >>= F] = _
  rw [← hfst]
  by_cases hinj : Function.Injective (keygenNamedInput parts)
  · simp only [if_pos hinj]
    have hswap : 𝒟[($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p => F p.1] =
        𝒟[($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
          F (keygenFiniteHiddenSwap D S parts (hmem parts) p).1] := by
      have he := congrArg (fun d => d >>= fun p => 𝒟[F p.1])
        (evalDist_keygenFiniteHiddenSwap D S parts (hmem parts) hinj)
      rw [← evalDist_bind, ← evalDist_bind, bind_map_left] at he
      exact he.symm
    rw [hswap]
    apply evalDist_bind_congr'
    intro p
    dsimp only [F]
    apply congrArg
    apply congrArg
    apply keygenReferenceLocalGame_table_congr
    intro name hh
    rw [keygenFiniteTotal_named prims S _ parts name (hmem parts name),
      keygenFiniteHiddenSwap_cell D S parts (hmem parts) hinj p name hh]
  · simp only [if_neg hinj]
    rfl

/-- Hidden half on the relabeled reference runs. -/
def KeygenHiddenFreshSwapped (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∀ (S : Finset (Query C)) (hmem : ∀ parts name, keygenNamedInput parts name ∈ S),
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z)) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z))) →
      |(Pr[= true | keygenSwappedMixture prims D A x z Z S hmem]).toReal -
        (Pr[= true | keygenSwappedMixture prims D A x z (keygenHiddenZ D Z) S hmem]).toReal| ≤
        keygenHashError C q / 2

theorem keygenHiddenFreshReference_of_swapped (prims : Primitives)
    (h : KeygenHiddenFreshSwapped (C := C) (E := E) prims) :
    KeygenHiddenFreshReference (C := C) (E := E) prims := by
  intro D A x z Z q hq S hmem h₁ h₂
  rw [probOutput_def, probOutput_def, evalDist_keygenReferenceMixture_swap prims D A x z Z S hmem,
    evalDist_keygenReferenceMixture_swap prims D A x z (keygenHiddenZ D Z) S hmem,
    ← probOutput_def, ← probOutput_def]
  exact h D A x z Z q hq S hmem h₁ h₂

end RealHidden

/-! ## The claim from the two hybrid halves -/

section Main

variable {E : Type} (prims : Primitives)

/-- `KeygenCoupling` from the two hybrid halves. -/
theorem keygenCoupling_of_halves (hH : KeygenHiddenDistance (C := C) (E := E) prims)
    (hK : KeygenKnownMismatch (C := C) (E := E) prims) :
    KeygenCoupling (C := C) (E := E) prims :=
  keygenCoupling_of_distance prims (keygenSecurityDistance_of_hybrids prims hH hK)

/-- `KeygenSecurityStatement` from the two hybrid halves. -/
theorem keygenSecurity_of_halves (hH : KeygenHiddenDistance (C := C) (E := E) prims)
    (hK : KeygenKnownMismatch (C := C) (E := E) prims) :
    KeygenSecurityStatement (C := C) (E := E) prims :=
  keygenSecurity_of_coupling prims (keygenCoupling_of_halves prims hH hK)

/-- `KeygenCoupling`, open at the hidden half on the relabeled reference runs and at the known
half. -/
theorem keygenCoupling (hH : KeygenHiddenFreshSwapped (C := C) (E := E) prims)
    (hK : KeygenKnownMismatch (C := C) (E := E) prims) :
    KeygenCoupling (C := C) (E := E) prims :=
  keygenCoupling_of_halves prims
    (keygenHiddenDistance_of_fresh prims
      (keygenHiddenFresh_of_reference prims (keygenHiddenFreshReference_of_swapped prims hH))) hK

/-- `KeygenSecurityStatement`, open at the same two halves as `keygenCoupling`. -/
theorem keygenSecurityProof (hH : KeygenHiddenFreshSwapped (C := C) (E := E) prims)
    (hK : KeygenKnownMismatch (C := C) (E := E) prims) :
    KeygenSecurityStatement (C := C) (E := E) prims :=
  keygenSecurity_of_coupling prims (keygenCoupling prims hH hK)

end Main

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.keygenSecurityProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.keygenSecurityProof
