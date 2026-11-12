import XmssSecurity.Proof.MarginalCoupling

/-!
# Couplings on disjoint cells

Couplings indexed by a left-hand key can be joined when their good part lands in
matching, disjoint right-hand cells. The unused right mass is coupled with the
bad left mass. No finiteness assumption on the keys or outcome types is needed.
-/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace ThresholdLeanXmssSecurity.TreeTwinGlue

private theorem map_fst_apply {α β : Type} (c : PMF (α × β)) (a : α) :
    c.map Prod.fst a = ∑' b, c (a, b) := by
  classical
  letI : DecidableEq α := Classical.decEq α
  rw [PMF.map_apply, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp

private theorem map_snd_apply {α β : Type} (c : PMF (α × β)) (b : β) :
    c.map Prod.snd b = ∑' a, c (a, b) := by
  classical
  letI : DecidableEq β := Classical.decEq β
  rw [PMF.map_apply, ENNReal.tsum_prod']
  simp

/-- Join probability couplings along disjoint key cells, allowing an arbitrary
relation on the bad left outcomes. -/
theorem pmf_glue {α β J : Type} (p : PMF α) (q : PMF β) (Bad : α → Prop)
    (key : α → J) (key' : β → J) (R : α → β → Prop)
    (cells : ∀ j, ∃ c : PMF.Coupling p q,
      ∀ a b, c.1 (a, b) ≠ 0 → Bad a ∨ (key a = j → key' b = j ∧ R a b)) :
    ∃ c : PMF.Coupling p q, ∀ a b, c.1 (a, b) ≠ 0 → Bad a ∨ R a b := by
  classical
  choose c hc using cells
  have row (j : J) (a : α) : (∑' b, (c j).1 (a, b)) = p a := by
    rw [← map_fst_apply, (c j).2.map_fst]
  have col (j : J) (b : β) : (∑' a, (c j).1 (a, b)) = q b := by
    rw [← map_snd_apply, (c j).2.map_snd]
  let g : α → β → ℝ≥0∞ := fun a b => if Bad a then 0 else (c (key a)).1 (a, b)
  let l : α → ℝ≥0∞ := fun a => if Bad a then p a else 0
  let v : β → ℝ≥0∞ := fun b => ∑' a, g a b
  let r : β → ℝ≥0∞ := fun b => q b - v b
  let δ : ℝ≥0∞ := ∑' a, l a
  have grows (a : α) : (∑' b, g a b) + l a = p a := by
    by_cases ha : Bad a <;> simp [g, l, ha, row]
  have gcol (b : β) : v b ≤ q b := by
    rw [← col (key' b) b]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases ha : Bad a
    · simp [g, ha]
    · rcases Classical.em ((c (key a)).1 (a, b) = 0) with hz | hz
      · simp [g, ha, hz]
      · have heq := ((hc (key a) a b hz).resolve_left ha) rfl
        simp only [g, if_neg ha]
        rw [heq.1]
  have mass : (∑' b, v b) + δ = 1 := by
    rw [show (∑' b, v b) = ∑' a, ∑' b, g a b from ENNReal.tsum_comm]
    rw [← ENNReal.tsum_add]
    simp only [grows, PMF.tsum_coe]
  have vfinite : (∑' b, v b) ≠ ∞ := by
    apply ne_top_of_le_ne_top one_ne_top
    calc
      (∑' b, v b) ≤ (∑' b, v b) + δ := le_self_add
      _ = 1 := mass
  have dfinite : δ ≠ ∞ := by
    apply ne_top_of_le_ne_top one_ne_top
    calc
      δ ≤ (∑' b, v b) + δ := le_add_self
      _ = 1 := mass
  have rsum : (∑' b, r b) = δ := by
    have h : (∑' b, r b) + (∑' b, v b) = 1 := by
      rw [← ENNReal.tsum_add]
      simp only [r, tsub_add_cancel_of_le (gcol _), PMF.tsum_coe]
    exact (ENNReal.add_right_inj vfinite).mp ((add_comm _ _).trans (h.trans mass.symm))
  have lzero (hd : δ = 0) (a : α) : l a = 0 := (ENNReal.tsum_eq_zero.mp hd) a
  have rzero (hd : δ = 0) (b : β) : r b = 0 :=
    (ENNReal.tsum_eq_zero.mp (rsum.trans hd)) b
  let w : α × β → ℝ≥0∞ := fun ab => g ab.1 ab.2 + l ab.1 * (r ab.2 * δ⁻¹)
  have wrow (a : α) : (∑' b, w (a, b)) = p a := by
    simp only [w, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, rsum]
    rcases Classical.em (δ = 0) with hd | hd
    · simpa only [lzero hd a, zero_mul, add_zero] using grows a
    · rw [ENNReal.mul_inv_cancel hd dfinite, mul_one]
      exact grows a
  have wcol (b : β) : (∑' a, w (a, b)) = q b := by
    simp only [w, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    change v b + δ * (r b * δ⁻¹) = q b
    rcases Classical.em (δ = 0) with hd | hd
    · have hv : v b = q b := by
        have h := tsub_add_cancel_of_le (gcol b)
        change r b + v b = q b at h
        simpa only [rzero hd b, zero_add] using h
      simp [hd, hv]
    · rw [show δ * (r b * δ⁻¹) = r b * (δ * δ⁻¹) by ac_rfl,
        ENNReal.mul_inv_cancel hd dfinite, mul_one]
      exact add_tsub_cancel_of_le (gcol b)
  have wsum : (∑' ab, w ab) = 1 := by
    exact (ENNReal.tsum_prod' (f := w)).trans (by simp only [wrow, PMF.tsum_coe])
  -- The normalization and marginal construction follow the pinned leanVM
  -- `generalFiberCoupling` and `generalFiberCoupling_isCoupling` pattern.
  let d : PMF (α × β) := PMF.normalize w
    (by rw [wsum]; exact one_ne_zero) (by rw [wsum]; exact one_ne_top)
  have deq (ab) : d ab = w ab := by simp [d, PMF.normalize_apply, wsum]
  refine ⟨⟨d, ?_, ?_⟩, ?_⟩
  · ext a
    rw [map_fst_apply]
    simp only [deq, wrow]
  · ext b
    rw [map_snd_apply]
    simp only [deq, wcol]
  · intro a b hab
    by_cases ha : Bad a
    · exact Or.inl ha
    · right
      have hne : (c (key a)).1 (a, b) ≠ 0 := by
        simpa [deq, w, g, l, ha] using hab
      exact (((hc (key a) a b hne).resolve_left ha) rfl).2

/-- Disjoint-cell gluing for oracle computations. Each guessed-key coupling
only has to establish the relation on its own good left cell. -/
theorem relTriple_glue
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {α β J : Type} (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (Bad : α → Prop) (key : α → J) (key' : β → J) (R : α → β → Prop)
    (cells : ∀ j, RelTriple oa ob
      (fun u v => Bad u ∨ (key u = j → key' v = j ∧ R u v))) :
    RelTriple oa ob (fun u v => Bad u ∨ R u v) := by
  classical
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq β := Classical.decEq β
  let hp : (evalDist oa).toPMF none = 0 := probFailure_eq_zero (mx := oa)
  let hq : (evalDist ob).toPMF none = 0 := probFailure_eq_zero (mx := ob)
  let p := XmssSecurity.generalSuccessPMF (evalDist oa) hp
  let q := XmssSecurity.generalSuccessPMF (evalDist ob) hq
  have pcells (j : J) : ∃ c : PMF.Coupling p q,
      ∀ a b, c.1 (a, b) ≠ 0 → Bad a ∨ (key a = j → key' b = j ∧ R a b) := by
    obtain ⟨d, hd⟩ := relTriple_iff_relWP.mp (cells j)
    -- Pinned leanVM `relTriple_trans_exists` uses this same conversion of a
    -- coupling of total oracle computations to a probability coupling.
    have hfail : d.1.toPMF none = 0 := by
      have hmap := d.2.map_fst
      rw [SPMF.fmap_eq_map] at hmap
      change PMF.map (Option.map Prod.fst) d.1.toPMF = (evalDist oa).toPMF at hmap
      have h := congrArg (fun μ : PMF (Option α) => μ none) hmap
      rw [PMF.map_apply] at h
      simpa using h.trans hp
    refine ⟨⟨XmssSecurity.generalSuccessPMF d.1 hfail, ?_, ?_⟩, ?_⟩
    · have h := XmssSecurity.generalSuccessPMF_map_eq_of_spmf_map_eq
        d.1 (evalDist oa) Prod.fst id hfail hp (by simpa using d.2.map_fst)
      simpa only [PMF.map_id] using h
    · have h := XmssSecurity.generalSuccessPMF_map_eq_of_spmf_map_eq
        d.1 (evalDist ob) Prod.snd id hfail hq (by simpa using d.2.map_snd)
      simpa only [PMF.map_id] using h
    · intro a b hab
      apply hd (a, b)
      apply (SPMF.mem_support_iff d.1 (a, b)).mpr
      simpa only [XmssSecurity.generalSuccessPMF_apply] using hab
  obtain ⟨⟨c, hfst, hsnd⟩, hc⟩ := pmf_glue p q Bad key key' R pcells
  apply relTriple_iff_relWP.mpr
  refine ⟨⟨(liftM c : SPMF (α × β)), ?_, ?_⟩, ?_⟩
  · rw [← liftM_map]
    change liftM (c.map Prod.fst) = evalDist oa
    rw [hfst]
    exact XmssSecurity.liftM_generalSuccessPMF_eq (evalDist oa) hp
  · rw [← liftM_map]
    change liftM (c.map Prod.snd) = evalDist ob
    rw [hsnd]
    exact XmssSecurity.liftM_generalSuccessPMF_eq (evalDist ob) hq
  · rintro ⟨a, b⟩ hab
    apply hc a b
    simpa using (SPMF.mem_support_iff (liftM c : SPMF (α × β)) (a, b)).mp hab

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGlue.pmf_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmf_glue

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGlue.relTriple_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_glue

end ThresholdLeanXmssSecurity.TreeTwinGlue
