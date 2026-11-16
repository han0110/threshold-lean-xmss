import ThresholdLeanXmssSecurity.Proof.SeedGenGames

/-!
# The coupling of the seed generation security

The coupling route relates `SeedGenCoupling` of `Proof/SeedGenGames.lean` to `SeedGenSecurityStatement`.

1. A coupling with a private coin as the bad flag turns any distance bound into an identical-until-bad
   pair. Every probability of a finite computation is rational, so the coin exists.
2. The hybrid `seedGenMixedGame` gives the emulated outputs with the dealer's hidden keys. The known
   half `SeedGenKnownMismatch` bounds the mismatch with the ideal outputs.
3. In the hidden half, the dealer's hidden keys are independent of the corrupt leak. So the mixed
   game is the real run whose distinguisher replaces the hidden keys by fresh ones
   (`seedGenHiddenZ`). The real run is a mixture of fixed-table reference runs on a common covering
   domain. On distinct canonical inputs, the hidden oracle cells and an independent dealer table
   exchange (the relabeling). So the hidden-half hypothesis `SeedGenHiddenFresh` reduces to the
   relabeled reference runs (`seedGenSwappedMixture`).
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

set_option pp.deepTerms false
set_option pp.maxSteps 2000

/-- The probability of every event of a finite computation is a nonnegative rational. -/
theorem probEvent_rational {α : Type} (oa : ProbComp α) (p : α → Prop) :
    ∃ r : ℚ, 0 ≤ r ∧ Pr{let z ← oa}[p z] = ENNReal.ofReal r := by
  classical
  induction oa using ProbComp.inductionOn with
  | pure a =>
    by_cases hp : p a
    · exact ⟨1, zero_le_one, by simp [hp]⟩
    · exact ⟨0, le_rfl, by simp [hp]⟩
  | query_bind n mx ih =>
    choose r hr hpr using ih
    refine ⟨∑ m, r m / (n + 1), Finset.sum_nonneg fun m _ => div_nonneg (hr m) (by positivity), ?_⟩
    rw [prEvent_bind_eq_sum_fintype]
    push_cast
    rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => div_nonneg (by exact_mod_cast hr m) (by positivity))]
    apply Finset.sum_congr rfl
    intro m _
    rw [ProbComp.prEvent_uniformFin, hpr m, Finset.filter_eq', if_pos (Finset.mem_univ m),
      Finset.card_singleton, Nat.cast_one, one_div, div_eq_mul_inv (r m : ℝ),
      ENNReal.ofReal_mul (by exact_mod_cast hr m)]
    rw [mul_comm]
    congr 1
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp

/-- A coin with any rational probability. -/
def ratCoin (a m : ℕ) : ProbComp Bool := (fun u : Fin (m + 1) => decide (u.val < a)) <$> $[0..m]

theorem probOutput_ratCoin_true (a m : ℕ) (ha : a ≤ m + 1) :
    Pr{let z ← ratCoin a m}[z = true] = (a : ℝ≥0∞) / (m + 1) := by
  unfold ratCoin
  rw [prEvent_map]
  simp only [decide_eq_true_eq]
  rw [ProbComp.prEvent_uniformFin, Fin.card_filter_val_lt]
  congr 2
  omega

/-- A coin with each rational probability in `[0, 1]`. -/
theorem exists_coin (α : ℚ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∃ coin : ProbComp Bool, Pr{let z ← coin}[z = true] = ENNReal.ofReal α ∧
      Pr{let z ← coin}[z = false] = ENNReal.ofReal (1 - α) := by
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
  have ht : Pr{let z ← ratCoin a (α.den - 1)}[z = true] = ENNReal.ofReal α := by
    rw [probOutput_ratCoin_true a _ (by omega), hα, ENNReal.ofReal_div_of_pos (by exact_mod_cast hden)]
    have hcast : ((α.den - 1 : ℕ) : ℝ≥0∞) + 1 = (α.den : ℝ≥0∞) := by exact_mod_cast hm
    rw [hcast]
    simp
  refine ⟨ratCoin a (α.den - 1), ht, ?_⟩
  have hs : Pr{let z ← ratCoin a (α.den - 1)}[z = false] =
      1 - Pr{let z ← ratCoin a (α.den - 1)}[z = true] := by
    rw [← OracleComp.prEvent_not_eq_one_sub]
    exact prEvent_congr _ _ _ (by simp)
  rw [hs, ht, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by exact_mod_cast h0)]

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
    Pr{let r ← runWorld prims oa}[Q r.1] = Pr{let z ← (simulateQ (worldAnswer prims) oa).run' ∅}[Q z] := by
  rw [← fst_map_runWorld, prEvent_map]


theorem probEvent_flag (P coin : ProbComp Bool) (Q : Bool × Bool → Prop) :
    Pr{let z ← P >>= fun b => (fun c => (b, b && c)) <$> coin}[Q z] =
      Pr{let z ← P}[z = true] * Pr{let c ← coin}[Q (true, c)] +
        Pr{let z ← P}[z = false] * (if Q (false, false) then 1 else 0) := by
  classical
  rw [prEvent_bind_eq_sum_fintype, Fintype.sum_bool, prEvent_map, prEvent_map]
  congr 1
  by_cases hq : Q (false, false)
  · simp [hq]
  · simp [hq]

theorem accepts_eq_probOutput (prims : Primitives) (g : OracleComp (WorldSpec C) Bool) :
    accepts prims g = (Pr{let z ← (simulateQ (worldAnswer prims) g).run' ∅}[z = true]).toReal := by
  unfold accepts
  rw [probEvent_runWorld_fst prims g (fun b => b = true)]

/-- The coin-flagged game keeps the acceptance of its game, and its flag is the coin on acceptance. -/
theorem coinFlagged_spec (prims : Primitives) (g : OracleComp (WorldSpec C) Bool) (coin : ProbComp Bool) :
    accepts prims (Prod.fst <$> coinFlagged g coin) = accepts prims g ∧
      Pr{let r ← runWorld prims (coinFlagged g coin)}[r.1 = (true, false)] =
        Pr{let z ← (simulateQ (worldAnswer prims) g).run' ∅}[z = true] * Pr{let z ← coin}[z = false] ∧
      Pr{let r ← runWorld prims (coinFlagged g coin)}[r.1.2 = true] =
        Pr{let z ← (simulateQ (worldAnswer prims) g).run' ∅}[z = true] * Pr{let z ← coin}[z = true] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [accepts_eq_probOutput prims g]
    unfold accepts
    rw [runWorld_map, prEvent_map]
    congr 1
    have h := probEvent_runWorld_fst prims (coinFlagged g coin) (fun p => p.1 = true)
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
      ENNReal.ofReal ra * Pr{let z ← coin}[z = false] = ENNReal.ofReal ((min ra rb : ℚ) : ℝ) ∧
      ENNReal.ofReal ra * Pr{let z ← coin}[z = true] = ENNReal.ofReal ((ra - min ra rb : ℚ) : ℝ) := by
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
      Pr{let r ← runWorld prims oa}[r.1 = (true, false)] =
        Pr{let r ← runWorld prims ob}[r.1 = (true, false)] ∧
      Pr{let r ← runWorld prims oa}[r.1.2 = true].toReal ≤ ε ∧
      Pr{let r ← runWorld prims ob}[r.1.2 = true].toReal ≤ ε := by
  obtain ⟨ra, ha, hra⟩ := probEvent_rational ((simulateQ (worldAnswer prims) ga).run' ∅) (· = true)
  obtain ⟨rb, hb, hrb⟩ := probEvent_rational ((simulateQ (worldAnswer prims) gb).run' ∅) (· = true)
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

/-- The coupling form of the seed generation claim follows from its distance form. -/
theorem seedGenCoupling_of_distance (prims : Primitives) {E : Type}
    (h : SeedGenSecurityDistance (C := C) (E := E) prims) :
    SeedGenCoupling (C := C) (E := E) prims := by
  intro D A x z Z q hq
  exact coupling_of_abs_accepts_le prims _ _ _ (h D A x z Z q hq)

/-! ## Two continuations of one game -/

theorem run'_bind_world (prims : Primitives) {R β : Type} (g : OracleComp (WorldSpec C) R)
    (k : R → OracleComp (WorldSpec C) β) :
    (simulateQ (worldAnswer prims) (g >>= k)).run' ∅ =
      (simulateQ (worldAnswer prims) g).run ∅ >>= fun p => (simulateQ (worldAnswer prims) (k p.1)).run' p.2 := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Two continuations of one game differ by at most the probability that they differ. -/
theorem abs_accepts_bind_sub_le_seedGen (prims : Primitives) {R : Type} (g : OracleComp (WorldSpec C) R)
    (k₁ k₂ : R → OracleComp (WorldSpec C) Bool) :
    |accepts prims (g >>= k₁) - accepts prims (g >>= k₂)| ≤
      (Pr{let r ← runWorld prims g}[k₁ r.1 ≠ k₂ r.1]).toReal := by
  let flag (k : R → OracleComp (WorldSpec C) Bool) : OracleComp (WorldSpec C) (Bool × Bool) :=
    g >>= fun r => (fun b => (b, decide (k₁ r ≠ k₂ r))) <$> k r
  have hfst (k : R → OracleComp (WorldSpec C) Bool) : Prod.fst <$> flag k = g >>= k := by
    simp only [flag, map_bind, Functor.map_map, id_map']
  have hbad (k : R → OracleComp (WorldSpec C) Bool) :
      Pr{let r ← runWorld prims (flag k)}[r.1.2 = true] =
        Pr{let r ← runWorld prims g}[k₁ r.1 ≠ k₂ r.1] := by
    rw [probEvent_runWorld_fst prims (flag k) (fun p => p.2 = true),
      probEvent_runWorld_fst prims g (fun r => k₁ r ≠ k₂ r), run'_bind_world]
    rw [StateT.run'_eq, prEvent_map, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
    apply tsum_congr
    intro p
    rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map]
    by_cases hp : k₁ p.1 ≠ k₂ p.1
    · simp [hp]
    · simp [hp]
  have heq : Pr{let r ← runWorld prims (flag k₁)}[r.1 = (true, false)] =
      Pr{let r ← runWorld prims (flag k₂)}[r.1 = (true, false)] := by
    rw [probEvent_runWorld_fst prims (flag k₁) (fun p => p = (true, false)),
      probEvent_runWorld_fst prims (flag k₂) (fun p => p = (true, false)), run'_bind_world, run'_bind_world,
      OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
    apply tsum_congr
    intro p
    congr 1
    by_cases hp : k₁ p.1 = k₂ p.1
    · rw [hp]
    · rw [simulateQ_map, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, StateT.run_map,
        prEvent_map, prEvent_map, prEvent_map, prEvent_map]
      simp [hp]
  have h := abs_accepts_sub_le_of_eq_until_bad prims (flag k₁) (flag k₂) heq
  rw [hfst, hfst, hbad, hbad, max_self] at h
  exact h

/-! ## The hybrid between the emulated and the dealt outputs -/

section Hybrid

variable {E : Type}

/-- The keys `k` with the hidden coordinates of `d`, for operator `i`. -/
def seedGenHiddenOverlay (D : C.Coalition) (i : C.Party) (k d : Keys C) : Keys C :=
  ⟨k.parameter, fun T => if KnownTo D.1 T then k.seed T else d.seed T,
    fun j => if i ∈ D.1 ∨ j ∈ D.1 then k.pairKey j else d.pairKey j⟩

/-- The emulated outputs with the hidden coordinates of the dealer. -/
def seedGenMixedProjection {σ : Type} (D : C.Coalition) (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) :
    σ × (C.Party → Option (Keys C)) :=
  (r.1, fun i => (r.2.1 i).map fun k => seedGenHiddenOverlay D i k (r.2.2 i))

/-- The hybrid game: the common game, and the distinguisher on the mixed outputs. -/
def seedGenMixedGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) Bool :=
  distinguish (seedGenMixedProjection D <$> setupCommonGame .seedGen D A x z) Z

/-- Hidden half: the hidden keys of the real run are indistinguishable from the dealer's. -/
def SeedGenHiddenDistance (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (setupCommonEmulatedGame .seedGen D A x z Z) - accepts prims (seedGenMixedGame D A x z Z)| ≤
      seedGenHashError C q / 2

/-- Known half: the simulator's programming fixes every exposed coordinate of an accepted output. -/
def SeedGenKnownMismatch (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let r ← runWorld prims (setupCommonGame .seedGen D A x z)}[
      seedGenMixedProjection D r.1 ≠ seedGenIdealProjection D r.1]).toReal ≤ seedGenHashError C q / 2

theorem abs_accepts_mixed_ideal_le (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    |accepts prims (seedGenMixedGame D A x z Z) -
        accepts prims (distinguish (idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) x z) Z)| ≤
      (Pr{let r ← runWorld prims (setupCommonGame .seedGen D A x z)}[
        seedGenMixedProjection D r.1 ≠ seedGenIdealProjection D r.1]).toReal := by
  rw [← setupCommonGame_seedGen_ideal]
  unfold seedGenMixedGame distinguish
  simp only [bind_map_left]
  refine (abs_accepts_bind_sub_le_seedGen prims _ _ _).trans ?_
  apply ENNReal.toReal_mono (prEvent_ne_top _)
  apply prEvent_mono
  intro r hr he
  exact hr (by rw [he])

/-- The distance half of the seed generation claim from its two hybrid halves. -/
theorem seedGenSecurityDistance_of_hybrids (prims : Primitives)
    (hH : SeedGenHiddenDistance (C := C) (E := E) prims) (hK : SeedGenKnownMismatch (C := C) (E := E) prims) :
    SeedGenSecurityDistance (C := C) (E := E) prims := by
  intro D A x z Z q hq
  erw [← setupCommonGame_real_accepts .seedGen prims D A x z Z]
  have h₁ := hH D A x z Z q hq
  have h₂ := (abs_accepts_mixed_ideal_le prims D A x z Z).trans (hK D A x z Z q hq)
  calc _ ≤ |accepts prims (setupCommonEmulatedGame .seedGen D A x z Z) - accepts prims (seedGenMixedGame D A x z Z)| +
        |accepts prims (seedGenMixedGame D A x z Z) -
          accepts prims (distinguish (idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) x z) Z)| :=
        abs_sub_le _ _ _
    _ ≤ seedGenHashError C q / 2 + seedGenHashError C q / 2 := add_le_add h₁ h₂
    _ = seedGenHashError C q := by ring

end Hybrid

/-! ## The hidden half on the real run -/

section RealHidden

variable {E : Type}

/-- The distinguisher that replaces the hidden coordinates of each output by fresh uniform keys. -/
def seedGenHiddenZ (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C)) : Distinguisher C σ (Keys C) :=
  fun r => do
    let seeds ← liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C)
    let pairs ← liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C)
    Z (r.1, fun i => (r.2 i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 seeds pairs i))

theorem simulateQ_local_sample_seedGensecurity (prims : Primitives) {α : Type} (p : ProbComp α) :
    simulateQ (localAnswer (C := C) prims) (liftComp p (LocalSpec C)) = StateT.lift p := by
  rw [show simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p from
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p]
  funext s
  change (simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p).run s = p >>= fun a => pure (a, s)
  rw [unifFwdImpl.simulateQ_run, map_eq_bind_pure_comp]
  rfl

/-- The dealer's corrupt keys, as the simulator receives them. -/
def seedGenCorruptLeak (D : C.Coalition) (d : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) :
    C.Party → Option (Keys C) :=
  fun i => if i ∈ D.1 then some (dealtKeys d.1 d.2.1 d.2.2 i) else none

theorem seedGenMixedGame_expand (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    seedGenMixedGame D A x z Z = (do
      let st ← (seedGenSimulator D A).start (corruptInputs D x) z
      let d ← free (liftComp (setupDealerSamples .seedGen (C := C)) (LocalSpec C))
      let r ← setupEmulation .seedGen D A st d.1 (seedGenCorruptLeak D d)
      worldRoles.adversary (Z (seedGenMixedProjection D (r.1.adversary, r.2, dealtKeys d.1 d.2.1 d.2.2)))) := by
  unfold seedGenMixedGame distinguish setupCommonGame setupDealerSamples seedGenCorruptLeak
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure]
  rfl

theorem seedGenCommonEmulatedGame_expand' (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    setupCommonEmulatedGame .seedGen D A x z Z = (do
      let st ← (seedGenSimulator D A).start (corruptInputs D x) z
      let d ← free (liftComp (setupDealerSamples .seedGen (C := C)) (LocalSpec C))
      let r ← setupEmulation .seedGen D A st d.1 (seedGenCorruptLeak D d)
      worldRoles.adversary (Z (r.1.adversary, r.2))) := by
  unfold setupCommonEmulatedGame distinguish setupCommonGame setupDealerSamples seedGenCorruptLeak
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure, seedGenEmulatedProjection]
  rfl

/-- Replace the coordinates in `P` of a uniform table by those of a second uniform table. -/
theorem evalDist_piecewise_uniform {ι H β : Type} [Fintype ι] [DecidableEq ι] [Fintype H] [Nonempty H]
    [SampleableType H] [SampleableType (ι → H)] (P : ι → Prop) [DecidablePred P]
    (k : (ι → H) → ProbComp β) :
    (do let f ← $ᵗ (ι → H); let g ← $ᵗ (ι → H); k (fun i => if P i then g i else f i)) =ᵈ
      (do let f ← $ᵗ (ι → H); k f) := by
  let Ψ : (ι → H) × (ι → H) → (ι → H) × (ι → H) := fun p =>
    (fun i => if P i then p.2 i else p.1 i, fun i => if P i then p.1 i else p.2 i)
  have hΨ : Function.Involutive Ψ := by
    intro p
    apply Prod.ext <;> funext i <;> by_cases h : P i <;> simp [Ψ, h]
  have e1 : (do let f ← $ᵗ (ι → H); let g ← $ᵗ (ι → H); k (fun i => if P i then g i else f i)) =
      ($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1 := by
    change _ = ((·, ·) <$> ($ᵗ (ι → H)) <*> ($ᵗ (ι → H))) >>= _
    simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Ψ]
  have e2 : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1) =ᵈ
      (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1) := by
    have h : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1) =
        (Ψ <$> ($ᵗ ((ι → H) × (ι → H)))) >>= fun p => k p.1 := by rw [bind_map_left]
    rw [h]
    exact (SampleableType.map_uniformSample_evalDistEq_of_bijective hΨ.bijective).bind_left _
  have e3 : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1) =ᵈ (($ᵗ (ι → H)) >>= k) := by
    have h : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1) =
        (Prod.fst <$> ($ᵗ ((ι → H) × (ι → H)))) >>= k := by rw [bind_map_left]
    rw [h]
    refine EvalDistEq.bind_left ?_ _
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans
      (by rw [bind_pure])
  rw [e1]
  exact e2.trans e3

/-- A hidden name of the dealer's tables. -/
def SeedGenHiddenTerm (D : C.Coalition) (T : C.Term) : Prop := ¬ KnownTo D.1 T

def SeedGenHiddenPair (D : C.Coalition) (p : C.Pair) : Prop := p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1

theorem seedGenHiddenPair_pairOf (D : C.Coalition) (i j : C.Party) (h : i ≠ j) :
    SeedGenHiddenPair D (C.pairOf i j h) ↔ i ∉ D.1 ∧ j ∉ D.1 := by
  unfold SeedGenHiddenPair Committee.pairOf
  split_ifs <;> simp [and_comm]

theorem seedGenCorruptLeak_piecewise (D : C.Coalition) (parameter : PublicParameter)
    (seeds seeds' : C.Term → HashOutput) (pairs pairs' : C.Pair → HashOutput) :
    seedGenCorruptLeak D (parameter, (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T),
      (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p)) =
      seedGenCorruptLeak D (parameter, seeds, pairs) := by
  funext j
  unfold seedGenCorruptLeak
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj, dealtKeys, Option.some.injEq, Keys.mk.injEq, true_and]
    constructor
    · funext T
      by_cases hT : j ∈ C.holders T
      · have hk : ¬ SeedGenHiddenTerm D T := fun h => h ⟨j, hj, hT⟩
        simp [hT, hk]
      · simp [hT]
    · funext i
      by_cases hij : i = j
      · simp [hij]
      · have hk : ¬ SeedGenHiddenPair D (C.pairOf j i (Ne.symm hij)) := by
          rw [seedGenHiddenPair_pairOf]; exact fun h => h.1 hj
        simp [hij, hk]
  · simp [hj]

theorem seedGenHiddenOverlay_piecewise (D : C.Coalition) (i : C.Party) (k : Keys C) (parameter : PublicParameter)
    (seeds seeds' : C.Term → HashOutput) (pairs pairs' : C.Pair → HashOutput) :
    seedGenHiddenOverlay D i k (dealtKeys parameter (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T)
      (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p) i) =
      seedGenHiddenOverlay D i k (dealtKeys 0 seeds' pairs' i) := by
  unfold seedGenHiddenOverlay dealtKeys
  simp only [Keys.mk.injEq, true_and]
  constructor
  · funext T
    by_cases hT : KnownTo D.1 T
    · simp [hT]
    · have hk : SeedGenHiddenTerm D T := hT
      simp [hT, hk]
  · funext j
    by_cases hc : i ∈ D.1 ∨ j ∈ D.1
    · simp [hc]
    · simp only [if_neg hc]
      by_cases hij : j = i
      · simp [hij]
      · have hk : SeedGenHiddenPair D (C.pairOf i j (Ne.symm hij)) := by
          rw [seedGenHiddenPair_pairOf]; exact not_or.mp hc
        simp [hij, hk]

/-- The dealer's hidden coordinates can be replaced by those of an independent second dealer. -/
theorem evalDist_dealer_piecewise (D : C.Coalition) {β : Type}
    (k : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput) → ProbComp β) :
    (do
      let d ← setupDealerSamples .seedGen (C := C)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (d.1, (fun T => if SeedGenHiddenTerm D T then seeds' T else d.2.1 T),
        (fun p => if SeedGenHiddenPair D p then pairs' p else d.2.2 p))) =ᵈ
      (setupDealerSamples .seedGen (C := C) >>= k) := by
  unfold setupDealerSamples
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun parameter => ?_
  have hswap : (do
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T),
        (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p))) =ᵈ
      (do
      let seeds ← $ᵗ (C.Term → HashOutput)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T),
        (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p))) := by
    refine EvalDistEq.bind_right _ fun seeds => ?_
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  refine hswap.trans ?_
  refine (evalDist_piecewise_uniform (SeedGenHiddenTerm D) (fun s => do
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, s, (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p)))).trans ?_
  refine EvalDistEq.bind_right _ fun seeds => ?_
  exact evalDist_piecewise_uniform (SeedGenHiddenPair D) (fun p => k (parameter, seeds, p))

theorem evalDist_run'_of_run {σ α : Type} {X Y : StateT σ ProbComp α} (s : σ)
    (h : X.run s =ᵈ Y.run s) : X.run' s =ᵈ Y.run' s := by
  simp only [StateT.run'_eq]
  exact h.map _

/-- Two independent samples move before a computation. -/
theorem evalDist_bind_two_comm {α β γ δ : Type} (m : ProbComp α) (p₁ : ProbComp β)
    (p₂ : ProbComp γ) (k : α → β → γ → ProbComp δ) :
    (m >>= fun r => p₁ >>= fun a => p₂ >>= fun b => k r a b) =ᵈ
      (p₁ >>= fun a => p₂ >>= fun b => m >>= fun r => k r a b) := by
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun a => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- The mixed game is the emulated game whose distinguisher replaces the hidden keys by fresh ones. -/
theorem evalDist_seedGenMixedGame_hiddenZ (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    (simulateQ (worldAnswer prims) (seedGenMixedGame D A x z Z)).run' ∅ =ᵈ
      (simulateQ (worldAnswer prims) (setupCommonEmulatedGame .seedGen D A x z (seedGenHiddenZ D Z))).run' ∅ := by
  rw [seedGenMixedGame_expand, seedGenCommonEmulatedGame_expand']
  unfold seedGenHiddenZ
  simp only [simulateQ_bind, simulateQ_world_sample, simulateQ_world_adversary, simulateQ_local_sample_seedGensecurity]
  apply evalDist_stateT_run'_bind_congr
  intro st s
  apply evalDist_run'_of_run
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine EvalDistEq.symm ?_
  refine (EvalDistEq.bind_right _ fun d => evalDist_bind_two_comm _ _ _ _).trans ?_
  refine EvalDistEq.trans ?_ (evalDist_dealer_piecewise D _)
  refine EvalDistEq.bind_right _ fun d => ?_
  refine EvalDistEq.bind_right _ fun a => ?_
  refine EvalDistEq.bind_right _ fun b => ?_
  rw [seedGenCorruptLeak_piecewise]
  simp only [seedGenMixedProjection, seedGenHiddenOverlay_piecewise]
  rfl

theorem seedGenMixedGame_accepts (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (seedGenMixedGame D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) (seedGenHiddenZ D Z)) := by
  have hreal : accepts prims (distinguish (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) (seedGenHiddenZ D Z)) =
      accepts prims (setupCommonEmulatedGame .seedGen D A x z (seedGenHiddenZ D Z)) :=
    (setupCommonGame_real_accepts .seedGen prims D A x z _).symm
  rw [hreal, accepts_eq_probOutput, accepts_eq_probOutput,
    (evalDist_seedGenMixedGame_hiddenZ prims D A x z Z).prEvent_eq (· = true)]

/-- Hidden half on the real run: the hidden keys of the honest outputs are indistinguishable from
fresh uniform keys. -/
def SeedGenHiddenFresh (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) -
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) (seedGenHiddenZ D Z))| ≤
      seedGenHashError C q / 2

theorem seedGenHiddenDistance_of_fresh (prims : Primitives) (h : SeedGenHiddenFresh (C := C) (E := E) prims) :
    SeedGenHiddenDistance (C := C) (E := E) prims := by
  intro D A x z Z q hq
  rw [setupCommonGame_real_accepts, seedGenMixedGame_accepts]
  exact h D A x z Z q hq

/-- The real run as a mixture of fixed-table reference runs, on every oracle domain that covers it. -/
def seedGenReferenceMixture (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) :
    ProbComp Bool := do
  let ht ← $ᵗ (S → HashOutput)
  let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let h := seedGenFiniteTotal prims S ht
  simulateQ (fixedLocal prims h)
    (seedGenReferenceLocalGame prims D h (fun name => h (setupNamedInput .seedGen parts name)) A x z Z parts)

theorem evalDist_seedGenReal_referenceMixture (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hS : SeedGenWorldCovered S (free (setupNormalizedLocalGame .seedGen D A x z Z))) :
    (simulateQ (worldAnswer prims)
        (distinguish (realExecution D A noFunctionality setupRounds
          (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z)).run' ∅ =ᵈ
      seedGenReferenceMixture prims D A x z Z S := by
  have he := evalDist_seedGenWorld_eager prims S (free (setupNormalizedLocalGame .seedGen D A x z Z)) hS ∅
  simp only [worldAnswer, seedGenFiniteWorld, simulateQ_free] at he
  have hc : seedGenRestrictCache S (∅ : HashCache C) = ∅ := rfl
  simp only [hc, seedGenFiniteLocal_eager_fixed, tableExtending_empty] at he
  erw [simulateQ_setupReal_eq_local]
  refine ((sameRun_setupLocal_normalized .seedGen prims D A x z Z).run'_eq).trans (he.trans ?_)
  unfold seedGenReferenceMixture
  refine EvalDistEq.bind_right _ fun ht => ?_
  exact evalDist_seedGenNormalized_fixed_reference prims D (seedGenFiniteTotal prims S ht) A x z Z

/-! ### The relabeling of the hidden keys -/

theorem seedGenMaskKeys_table_congr (D : C.Coalition) (t t' : KeyName C → HashOutput)
    (ht : ∀ name, Hidden D name → t name = t' name) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    seedGenMaskKeys D t i keys = seedGenMaskKeys D t' i keys := by
  unfold seedGenMaskKeys
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
        exact (seedGenHiddenPair_pairOf D i j (Ne.symm hj)).mpr (not_or.mp hc)

/-- The reference run reads its table only at the hidden names. -/
theorem seedGenReferenceLocalGame_table_congr (prims : Primitives) (D : C.Coalition)
    (h : Query C → HashOutput) (t t' : KeyName C → HashOutput)
    (ht : ∀ name, Hidden D name → t name = t' name)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    seedGenReferenceLocalGame prims D h t A x z Z parts = seedGenReferenceLocalGame prims D h t' A x z Z parts := by
  have hk : seedGenReferenceKeys (E := E) prims D h t parts = seedGenReferenceKeys prims D h t' parts := by
    funext revealed i
    exact seedGenMaskKeys_table_congr D t t' ht i _
  have hd : seedGenReferenceData (E := E) prims D h t parts = seedGenReferenceData prims D h t' parts := by
    funext commitSent revealSent i
    simp only [seedGenReferenceData, hk]
  simp only [seedGenReferenceLocalGame, seedGenReferencePostCommit, hd]

/-- The reference mixture after the relabeling: on distinct canonical inputs, the hidden keys are an
independent dealer table, and the oracle answers the hidden canonical inputs with the dealer's keys. -/
def seedGenSwappedMixture (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, setupNamedInput .seedGen parts name ∈ S) : ProbComp Bool := do
  let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
  let ht := if Function.Injective (setupNamedInput .seedGen parts) then
    (seedGenFiniteHiddenSwap D S parts (hmem parts) p).1 else p.1
  let h := seedGenFiniteTotal prims S ht
  let table := if Function.Injective (setupNamedInput .seedGen parts) then p.2 else
    fun name => h (setupNamedInput .seedGen parts name)
  simulateQ (fixedLocal prims h) (seedGenReferenceLocalGame prims D h table A x z Z parts)

theorem evalDist_seedGenReferenceMixture_swap (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, setupNamedInput .seedGen parts name ∈ S) :
    seedGenReferenceMixture prims D A x z Z S =ᵈ seedGenSwappedMixture prims D A x z Z S hmem := by
  unfold seedGenReferenceMixture seedGenSwappedMixture
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun parts => ?_
  let F : (S → HashOutput) → ProbComp Bool := fun ht =>
    simulateQ (fixedLocal prims (seedGenFiniteTotal prims S ht))
      (seedGenReferenceLocalGame prims D (seedGenFiniteTotal prims S ht)
        (fun name => seedGenFiniteTotal prims S ht (setupNamedInput .seedGen parts name)) A x z Z parts)
  have hfst : (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p => F p.1) =ᵈ
      (($ᵗ (S → HashOutput)) >>= F) := by
    rw [← bind_map_left Prod.fst]
    refine EvalDistEq.bind_left ?_ _
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans
      (by rw [bind_pure])
  change (($ᵗ (S → HashOutput)) >>= F) =ᵈ _
  refine hfst.symm.trans ?_
  by_cases hinj : Function.Injective (setupNamedInput .seedGen parts)
  · simp only [if_pos hinj]
    have hswap : (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p => F p.1) =ᵈ
        (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
          F (seedGenFiniteHiddenSwap D S parts (hmem parts) p).1) := by
      have he := (evalDist_seedGenFiniteHiddenSwap D S parts (hmem parts) hinj).bind_left
        (fun p => F p.1)
      rw [bind_map_left] at he
      exact he.symm
    refine hswap.trans ?_
    refine EvalDistEq.bind_right _ fun p => ?_
    dsimp only [F]
    have htable : ∀ name, Hidden D name →
        seedGenFiniteTotal prims S (seedGenFiniteHiddenSwap D S parts (hmem parts) p).1
          (setupNamedInput .seedGen parts name) = p.2 name := by
      intro name hh
      rw [seedGenFiniteTotal_named prims S _ parts name (hmem parts name),
        seedGenFiniteHiddenSwap_cell D S parts (hmem parts) hinj p name hh]
    rw [seedGenReferenceLocalGame_table_congr prims D _ _ _ htable]
  · simp only [if_neg hinj]
    rfl

end RealHidden

/-! ## The claim from the two hybrid halves -/

section Main

variable {E : Type} (prims : Primitives)

/-- `SeedGenCoupling` from the two hybrid halves. -/
theorem seedGenCoupling_of_halves (hH : SeedGenHiddenDistance (C := C) (E := E) prims)
    (hK : SeedGenKnownMismatch (C := C) (E := E) prims) :
    SeedGenCoupling (C := C) (E := E) prims :=
  seedGenCoupling_of_distance prims (seedGenSecurityDistance_of_hybrids prims hH hK)

/-- `SeedGenSecurityStatement` from the two hybrid halves. -/
theorem seedGenSecurity_of_halves (hH : SeedGenHiddenDistance (C := C) (E := E) prims)
    (hK : SeedGenKnownMismatch (C := C) (E := E) prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  seedGenSecurity_of_coupling prims (seedGenCoupling_of_halves prims hH hK)

end Main

end ThresholdLeanXmssSecurity
