import ThresholdLeanXmssSecurity.Proof.TreeTwinFinishPass
import ThresholdLeanXmssSecurity.Proof.TreeTwinSegmentDefs
import ThresholdLeanXmssSecurity.Proof.TreeTwinLocalSum

/-! # Entering the guessed final field exchange
The saved last halving step retains its caller and histories. The two mask
regions are coupled after the held term streams have been prefilled.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinGuessStart
open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinSavedKinds TreeTwinSegment
open TreeTwinPrefill TreeTwinPassPrefill TreeTwinFinishPass TreeTwinLocalSum
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- A field exchange with an honest abort and its actual retained continuation. -/
def StoppedFieldStage {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (d : TreeSimExtendMultData K D) (live : C.Party → Bool),
    (∃ j, j ∉ D.1 ∧ live j ≠ true) ∧ δ = d.δ ∧
    a.1.2 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂

/-- The GS20 final-mask translation on the lacked term. -/
def finalMaskDelta (T₀ : C.Term) (r? : Option E) (eA eB : E) : KeyName C → Fin 2 → E
  | .term T => match r? with
      | some r => if T = T₀ then ![r / (1 + r) * eA, r / (1 + r) * eB] else 0
      | none => 0
  | _ => 0


/-- Prefilling complete first-region blocks initializes both region certificates. -/
theorem prefilled_twoField (D : C.Coalition) (label idx count next idx' count' : ℕ)
    (δ₀ : KeyName C → Fin count → E) (δ₁ : KeyName C → Fin count' → E)
    (blocks : List (KeyName C × HashOutput)) (qs : List (Query C))
    (h₀ h : HashCache C) (base₁ base₂ c₁ c₂ : HiddenCache C)
    (filled : Prefilled K D label idx count δ₀ blocks qs h₀ base₁ base₂ h c₁ c₂)
    (hidden : ∀ x ∈ blocks, Hidden D x.1) (sep : label ≠ next)
    (fresh₁ : TreeSimFutureEmpty label base₁) (fresh₂ : TreeSimFutureEmpty label base₂)
    (later : label ≤ next) :
    TwoFieldCaches K D label idx count next idx' count' δ₀ δ₁ base₁ base₂ c₁ c₂ := by
  have outside (name : KeyName C) (key : HashOutput) (g : Fin (count * elementBits))
      (absent : (name, key) ∉ blocks) :
      ∀ x ∈ blocks, ∀ k : Fin (count * elementBits),
        ((name, key), label, idx, g.val) ≠ (x, label, idx, k.val) := by
    intro x hx k eq
    have he : (name, key) = x := congrArg Prod.fst eq
    exact absent (he ▸ hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro name key hh
    by_cases listed : (name, key) ∈ blocks
    · exact Or.inr (filled.blocks _ listed)
    · exact Or.inl ⟨fun g => (filled.frame₁ _ (outside name key g listed)).trans (fresh₁ _ le_rfl),
        fun g => (filled.frame₂ _ (outside name key g listed)).trans (fresh₂ _ le_rfl)⟩
  · intro name key hh
    have miss (g : Fin (count' * elementBits)) :
        ∀ x ∈ blocks, ∀ k : Fin (count * elementBits),
          ((name, key), next, idx', g.val) ≠ (x, label, idx, k.val) := by
      intro x hx k eq
      exact sep (congrArg (fun z => z.2.1) eq).symm
    exact Or.inl ⟨fun g => (filled.frame₁ _ (miss g)).trans (fresh₁ _ later),
      fun g => (filled.frame₂ _ (miss g)).trans (fresh₂ _ later)⟩
  · intro y hy _
    apply filled.frame₁
    intro x hx g eq
    apply hy
    rw [eq]
    exact ⟨hidden x hx, rfl, rfl, g.isLt⟩
  · intro y hy _
    apply filled.frame₂
    intro x hx g eq
    apply hy
    rw [eq]
    exact ⟨hidden x hx, rfl, rfl, g.isLt⟩

/-- Prefilling empty hash cells keeps every existing public cache value. -/
theorem prefilled_hash_le (D : C.Coalition) (label idx count : ℕ)
    (δ₀ : KeyName C → Fin count → E) (blocks : List (KeyName C × HashOutput))
    (qs : List (Query C)) (h₀ h : HashCache C) (base₁ base₂ c₁ c₂ : HiddenCache C)
    (filled : Prefilled K D label idx count δ₀ blocks qs h₀ base₁ base₂ h c₁ c₂)
    (fresh : ∀ q ∈ qs, h₀ q = none) : h₀ ≤ h := by
  intro q v hv
  by_cases mem : q ∈ qs
  · rw [fresh q mem] at hv
    cases hv
  · rw [filled.hashFrame q mem]
    exact hv

/-- Predictions are unchanged when the initially cached held terms persist. -/
theorem predictedTerms_mono (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (h h' : HashCache C) (c c' : HiddenCache C) (hh : h ≤ h') (hc : c ≤ c')
    (hidden : ∀ T, ctx.self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (count * elementBits), c ((.term T, ctx.prss.term T), label, idx, g.val) ≠ none)
    (visible : ∀ T, ctx.self ∈ C.holders T → ¬ Hidden D (.term T) →
      h (.streamKey (ctx.prss.term T)) ≠ none) :
    predictedTerms prims K D h' c' ctx label idx count =
      predictedTerms prims K D h c ctx label idx count := by
  funext T
  by_cases held : ctx.self ∈ C.holders T
  · simp only [predictedTerms, if_pos held]
    apply congrArg (treeStagesFieldResult K count)
    apply congrArg (treeStagesDecode K count)
    funext g
    by_cases ht : Hidden D (.term T)
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hidden T held ht g)
      simp [ht, hv, hc hv]
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (visible T held ht)
      simp [ht, hv, hh hv]
  · simp only [predictedTerms, if_neg held]


/-- The final two local products have the usual Lagrange-weighted form. -/
theorem finalProducts_values (ctx : Context C) (claim : (ℕ → E) × (ℕ → E) × E)
    (w : Shares C E) :
    contextProductValues K ctx (finalProducts K ctx claim w) 0 =
      lagrangeAll K ctx.self * (conv K ctx w 0 * conv K ctx w 1) ∧
    contextProductValues K ctx (finalProducts K ctx claim w) 1 =
      lagrangeAll K ctx.self * ((conv K ctx w 0 + claim.1 0) * (conv K ctx w 1 + claim.2.1 0)) := by
  simp [contextProductValues, finalProducts, productShare, mulSh]

/-- GS20's final-mask identity after summing the actual honest product shares. -/
theorem guess_conjunct (D : C.Coalition) (T₀ : C.Term) (lacked : lackedTerm D.1 = some T₀)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (claim₁ claim₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (w₁ w₂ : C.Party → Shares C E) (r e : E) (hr : 1 + r ≠ 0)
    (rel : HalvRel K D 1 (fun i => (claim₁ i).1) (fun i => (claim₁ i).2.1)
      (fun i => (claim₂ i).1) (fun i => (claim₂ i).2.1)
      (fun i => (claim₁ i).2.2) (fun i => (claim₂ i).2.2))
    (shape : ∀ i, i ∉ D.1 → (claim₁ i).2.2 - (claim₂ i).2.2 = lackedShare K D i e)
    (mask₀ : ∀ i, i ∉ D.1 → conv K (ctx₂ i) (w₂ i) 0 = conv K (ctx₁ i) (w₁ i) 0 +
      r / (1 + r) * ((claim₁ i).1 0 - (claim₂ i).1 0))
    (mask₁ : ∀ i, i ∉ D.1 → conv K (ctx₂ i) (w₂ i) 1 = conv K (ctx₁ i) (w₁ i) 1 +
      r / (1 + r) * ((claim₁ i).2.1 0 - (claim₂ i).2.1 0))
    (out₁ out₂ : C.Party → Shares C E)
    (outputs : OutputShift K D ctx₁ ctx₂
      (fun i => finalProducts K (ctx₁ i) (claim₁ i) (w₁ i))
      (fun i => finalProducts K (ctx₂ i) (claim₂ i) (w₂ i)) out₁ out₂) :
    ∀ i, i ∉ D.1 → ∀ k < 3,
      finalVector K (ctx₁ i) (claim₁ i) (w₁ i) (out₁ i) r k =
        finalVector K (ctx₂ i) (claim₂ i) (w₂ i) (out₂ i) r k := by
  letI : CharP E 2 := charTwo
  letI : SampleableType E := SampleableType.ofFintype E
  let v₁ := fun i => contextProductValues K (ctx₁ i) (finalProducts K (ctx₁ i) (claim₁ i) (w₁ i))
  let v₂ := fun i => contextProductValues K (ctx₂ i) (finalProducts K (ctx₂ i) (claim₂ i) (w₂ i))
  let S := fun g => ∑ i ∈ univ.filter (· ∉ D.1), (v₁ i g - v₂ i g)
  have esum := halvRel_localSum K D _ _ _ _ _ _ rel e T₀ lacked shape
  have localIdentity (i : C.Party) (hi : i ∉ D.1) :
      (1 + r) * (v₁ i 0 - v₂ i 0) + r * (1 + r) * (v₁ i 1 - v₂ i 1) =
        r * (lagrangeAll K i * ((claim₁ i).1 0 * (claim₁ i).2.1 0 -
          (claim₂ i).1 0 * (claim₂ i).2.1 0)) := by
    have h := finalMask_local r (lagrangeAll K i) (conv K (ctx₁ i) (w₁ i) 0)
      (conv K (ctx₁ i) (w₁ i) 1) ((claim₁ i).1 0) ((claim₁ i).2.1 0)
      ((claim₁ i).1 0 - (claim₂ i).1 0) ((claim₁ i).2.1 0 - (claim₂ i).2.1 0) hr
    have aa : (claim₁ i).1 0 + ((claim₁ i).1 0 - (claim₂ i).1 0) = (claim₂ i).1 0 := by
      simp [sub_eq_add_neg, CharTwo.neg_eq, ← add_assoc, CharTwo.add_self_eq_zero]
    have bb : (claim₁ i).2.1 0 + ((claim₁ i).2.1 0 - (claim₂ i).2.1 0) = (claim₂ i).2.1 0 := by
      simp [sub_eq_add_neg, CharTwo.neg_eq, ← add_assoc, CharTwo.add_self_eq_zero]
    dsimp only [v₁, v₂]
    rw [(finalProducts_values K _ _ _).1, (finalProducts_values K _ _ _).1,
      (finalProducts_values K _ _ _).2, (finalProducts_values K _ _ _).2,
      self₁ i hi, self₂ i hi, mask₀ i hi, mask₁ i hi]
    rw [aa, bb] at h
    linear_combination h
  have combined : (1 + r) * S 0 + r * (1 + r) * S 1 = r * e := by
    rw [esum]
    simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact localIdentity i (Finset.mem_filter.mp hi).2
  intro i hi k hk
  have h₀ := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ outputs i hi 0 (by omega)
  have h₁ := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ outputs i hi 1 (by omega)
  change _ = lackedShare K D i (S 0) at h₀
  change _ = lackedShare K D i (S 1) at h₁
  have hc := congrArg (lackedShare K D i) combined
  simp only [lackedShare_add, lackedShare_mul] at hc
  have hd := shape i hi
  interval_cases k
  · simp only [finalVector, mask₀ i hi]
    exact (final_mask_shift _ _ _ _ hr).symm
  · simp only [finalVector, mask₁ i hi]
    exact (final_mask_shift _ _ _ _ hr).symm
  · simp only [finalVector]
    have h2 : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
    linear_combination (1 + r) * h₀ + r * (1 + r) * h₁ + r * hd + hc +
      (r * lackedShare K D i e) * h2


/-- Both mask regions, retaining every value fixed by prefill. -/
def PassRel (D : C.Coalition) (label : ℕ)
    (δ₀ δ₁ : KeyName C → Fin 2 → E) (base₁ base₂ : HiddenCache C)
    (h : HashCache C) (c₁ c₂ : HiddenCache C)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) : Prop :=
  TwoFieldRel K D label 1 2 (label + 1) 0 2 δ₀ δ₁ base₁ base₂ a b ∧
    h ≤ a.1.1 ∧ c₁ ≤ a.1.2 ∧ c₂ ≤ b.2

/-- The second-region draw preserves the cached predictions. -/
theorem passDraws_second (D : C.Coalition) (label : ℕ)
    (δ₀ δ₁ : KeyName C → Fin 2 → E) (base₁ base₂ : HiddenCache C)
    (h : HashCache C) (c₁ c₂ : HiddenCache C)
    (visible : ∀ name, ¬ Hidden D name → δ₁ name = 0) :
    TreeStagesFieldDraws prims K D (label + 1) 0 2 δ₁
      (PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂) := by
  intro name key a b hab
  apply relTriple_post_mono (treeSim_relTriple_support
    (twoFieldDraws_second prims (by omega : label ≠ label + 1) visible name key a b hab.1))
  intro u v huv
  exact ⟨huv.1.1, huv.1.2,
    hab.2.1.trans (treeSim_logged_grows prims D _ a u huv.2.1),
    hab.2.2.1.trans (treeSim_hidden_grows_logged prims D _ a u huv.2.1),
    hab.2.2.2.trans (treeSim_hidden_grows prims D _ b v huv.2.2)⟩

/-- The first complete PRSS draw preserves the cached predictions and both marginal supports. -/
theorem passPrss_first (D : C.Coalition) (label : ℕ)
    (δ₀ δ₁ : KeyName C → Fin 2 → E) (base₁ base₂ : HiddenCache C)
    (h : HashCache C) (c₁ c₂ : HiddenCache C)
    (visible : ∀ name, ¬ Hidden D name → δ₀ name = 0) (ctx : Context C)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hab : PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) label 1 2) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) label 1 2) (LocalSpec C)))).run b)
      (fun u v => v.1 = u.1 + treeStagesPrssFieldShift ctx 2 δ₀ ∧
        PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ u.2 v.2 ∧
        u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (liftComp (prssDraw ctx (elementCodec K) label 1 2) (LocalSpec C)))).run a) ∧
        v ∈ support ((simulateQ (streamWorld prims D)
          (free (liftComp (prssDraw ctx (elementCodec K) label 1 2) (LocalSpec C)))).run b)) := by
  apply relTriple_post_mono (treeSim_relTriple_support
    (twoFieldPrss_first prims (by omega : label ≠ label + 1) visible ctx a b hab.1))
  intro u v huv
  exact ⟨huv.1.1, ⟨huv.1.2,
    hab.2.1.trans (treeSim_logged_grows prims D _ a u huv.2.1),
    hab.2.2.1.trans (treeSim_hidden_grows_logged prims D _ a u huv.2.1),
    hab.2.2.2.trans (treeSim_hidden_grows prims D _ b v huv.2.2)⟩, huv.2⟩


/-- A live finishing body uses the prefilled masks before its dependent reshare. -/
theorem finishing_entry (D : C.Coalition) (label : ℕ)
    (δ₀ δ₁ : KeyName C → Fin 2 → E) (base₁ base₂ : HiddenCache C)
    (h : HashCache C) (c₁ c₂ : HiddenCache C)
    (visible₀ : ∀ name, ¬ Hidden D name → δ₀ name = 0)
    (visible₁ : ∀ name, ¬ Hidden D name → δ₁ name = 0)
    (ctx₁ ctx₂ : Context C) (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (hidden₁ : ∀ T, ctx₁.self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (2 * elementBits), c₁ ((.term T, ctx₁.prss.term T), label, 1, g.val) ≠ none)
    (hidden₂ : ∀ T, ctx₁.self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (2 * elementBits), c₂ ((.term T, ctx₁.prss.term T), label, 1, g.val) ≠ none)
    (visible : ∀ T, ctx₁.self ∈ C.holders T → ¬ Hidden D (.term T) →
      h (.streamKey (ctx₁.prss.term T)) ≠ none)
    (width j : ℕ) (p₁ p₂ : (ℕ → E) × (ℕ → E) × E)
    (finish₁ finish₂ : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : Shares C E × RunState C) (r : E) (st₁ st₂ : RunState C)
    (lab₁ : st₁.label = label) (lab₂ : st₂.label = label)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hab : PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ a b) :
    let claim₁ := treeStagesHalvingUpdate K ctx₁ width j p₁ out₁.1 r
    let claim₂ := treeStagesHalvingUpdate K ctx₂ width j p₂ out₂.1 r
    let w₁ := predictedTerms prims K D h c₁ ctx₁ label 1 2
    let w₂ := predictedTerms prims K D h c₂ ctx₁ label 1 2
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (advance
        (treeStagesHalvingBody K ctx₁ width j [] p₁ finish₁ out₁ (r, st₁)).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance
        (treeStagesHalvingBody K ctx₂ width j [] p₂ finish₂ out₂ (r, st₂)).run))).run b)
      (fun u v => (∃ rnd,
        u.1 = treeSimPeerStep K ctx₁ (elementCodec K) rnd
          (contextProductValues K ctx₁ (finalProducts K ctx₁ claim₁ w₁)) 2
          (nextLabel st₁) (finalAfterField K ctx₁ claim₁ w₁ finish₁) ∧
        v.1 = treeSimPeerStep K ctx₂ (elementCodec K) (rnd + treeStagesPrssFieldShift ctx₁ 2 δ₁)
          (contextProductValues K ctx₂ (finalProducts K ctx₂ claim₂ w₂)) 2
          (nextLabel st₂) (finalAfterField K ctx₂ claim₂ w₂ finish₂)) ∧
        w₂ = w₁ + (treeStagesPrssFieldShift ctx₁ 2 δ₀).1 ∧
        PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ u.2 v.2) := by
  dsimp only
  rw [finishing_body_program, finishing_body_program, lab₁, lab₂,
    ← treeSim_prssDraw_context ctx₁ ctx₂ self keys]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (passPrss_first prims K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ visible₀ ctx₁ a b hab)
  intro u v huv
  have hb : h ≤ b.1 := by rw [← hab.1.1]; exact hab.2.1
  have lift_nonempty {ι : Type} {spec : OracleSpec ι} {x y : QueryCache spec}
      (le : x ≤ y) (i : spec.Domain) (filled : x i ≠ none) : y i ≠ none := by
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp filled
    rw [le hz]
    exact Option.some_ne_none _
  have predicted₁ : u.1.1 = predictedTerms prims K D h c₁ ctx₁ label 1 2 := by
    rw [prssDraw_predicted prims K D ctx₁ label 1 2 a u
      (fun T ht hh g => lift_nonempty hab.2.2.1 _ (hidden₁ T ht hh g))
      (fun T ht hh => lift_nonempty hab.2.1 _ (visible T ht hh)) huv.2.2.1]
    exact predictedTerms_mono prims K D ctx₁ label 1 2 h a.1.1 c₁ a.1.2
      hab.2.1 hab.2.2.1 hidden₁ visible
  have predicted₂ : v.1.1 = predictedTerms prims K D h c₂ ctx₁ label 1 2 := by
    rw [prssDraw_predicted_stream prims K D ctx₁ label 1 2 b v
      (fun T ht hh g => lift_nonempty hab.2.2.2 _ (hidden₂ T ht hh g))
      (fun T ht hh => lift_nonempty hb _ (visible T ht hh)) huv.2.2.2]
    exact predictedTerms_mono prims K D ctx₁ label 1 2 h b.1 c₂ b.2 hb hab.2.2.2 hidden₂ visible
  have masks : predictedTerms prims K D h c₂ ctx₁ label 1 2 =
      predictedTerms prims K D h c₁ ctx₁ label 1 2 + (treeStagesPrssFieldShift ctx₁ 2 δ₀).1 := by
    rw [← predicted₁, ← predicted₂, huv.1]
    rfl
  rw [predicted₁, predicted₂]
  apply relTriple_post_mono (treeStages_field_peer_entry prims K D ctx₁ ctx₂ self keys
    (label + 1) 0 2 _ _ (nextLabel st₁) (nextLabel st₂)
    (by simp only [nextLabel, lab₁])
    (by simp only [nextLabel, lab₂]) _ _ δ₁
    (PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂)
    (passDraws_second prims K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ visible₁) u.2 v.2 huv.2.1)
  intro u' v' result
  exact ⟨result.1, masks, result.2⟩


/-- All covered finishing tails are coupled in the driver's original order. -/
theorem finishing_prefilled_pass (D : C.Coalition) (label : ℕ)
    (δ₀ δ₁ : KeyName C → Fin 2 → E) (base₁ base₂ : HiddenCache C)
    (h : HashCache C) (c₁ c₂ : HiddenCache C)
    (visible₀ : ∀ name, ¬ Hidden D name → δ₀ name = 0)
    (visible₁ : ∀ name, ¬ Hidden D name → δ₁ name = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (width j : ℕ) (p₁ p₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (prior₁ prior₂ : C.Party → Shares C E × RunState C)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label) (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (tag hashLabel : C.Party → ℕ) (out : C.Party → Option (List E))
    (corrupt : ∀ i, i ∈ D.1 → out i = none) (base : HashCache C) (base_le : base ≤ h)
    (covered : ∀ i values, out i = some values → TreeStagesChallengeCovered K base (tag i) (hashLabel i) values)
    (hidden₁ : ∀ i values s, out i = some values →
      treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some s →
      ∀ T, (ctx₁ i).self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (2 * elementBits), c₁ ((.term T, (ctx₁ i).prss.term T), label, 1, g.val) ≠ none)
    (hidden₂ : ∀ i values s, out i = some values →
      treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some s →
      ∀ T, (ctx₁ i).self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (2 * elementBits), c₂ ((.term T, (ctx₁ i).prss.term T), label, 1, g.val) ≠ none)
    (visible : ∀ i values s, out i = some values →
      treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some s →
      ∀ T, (ctx₁ i).self ∈ C.holders T → ¬ Hidden D (.term T) →
        h (.streamKey ((ctx₁ i).prss.term T)) ≠ none)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hab : PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ a b) :
    let r := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) ((out i).getD [])).getD 0
    let live := treeStagesChallengeLive K base tag hashLabel (fun i => (out i).getD []) (fun i => (out i).map fun _ => ())
    let claim₁ := fun i => treeStagesHalvingUpdate K (ctx₁ i) width j (p₁ i) (prior₁ i).1 (r i)
    let claim₂ := fun i => treeStagesHalvingUpdate K (ctx₂ i) width j (p₂ i) (prior₂ i).1 (r i)
    let w₁ := fun i => predictedTerms prims K D h c₁ (ctx₁ i) label 1 2
    let w₂ := fun i => predictedTerms prims K D h c₂ (ctx₁ i) label 1 2
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll (fun i values =>
        treeStagesChallengeTail K (tag i) (hashLabel i)
          (treeStagesHalvingBody K (ctx₁ i) width j [] (p₁ i) (finish₁ i) (prior₁ i)) (values, st₁ i)) out)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll (fun i values =>
        treeStagesChallengeTail K (tag i) (hashLabel i)
          (treeStagesHalvingBody K (ctx₂ i) width j [] (p₂ i) (finish₂ i) (prior₂ i)) (values, st₂ i)) out)).run b)
      (fun u v => (∃ rnd,
        u.1 = treeSimExtendMultPartial K D ctx₁ live 2 rnd
          (fun i => contextProductValues K (ctx₁ i) (finalProducts K (ctx₁ i) (claim₁ i) (w₁ i)))
          (fun i => nextLabel (st₁ i)) (fun i => finalAfterField K (ctx₁ i) (claim₁ i) (w₁ i) (finish₁ i)) ∧
        v.1 = treeSimExtendMultPartial K D ctx₂ live 2
          (fun i => rnd i + treeStagesPrssFieldShift (ctx₁ i) 2 δ₁)
          (fun i => contextProductValues K (ctx₂ i) (finalProducts K (ctx₂ i) (claim₂ i) (w₂ i)))
          (fun i => nextLabel (st₂ i)) (fun i => finalAfterField K (ctx₂ i) (claim₂ i) (w₂ i) (finish₂ i))) ∧
        (∀ i, live i = true → w₂ i = w₁ i + (treeStagesPrssFieldShift (ctx₁ i) 2 δ₀).1) ∧
        PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ u.2 v.2) := by
  dsimp only
  let r := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) ((out i).getD [])).getD 0
  let live := treeStagesChallengeLive K base tag hashLabel (fun i => (out i).getD []) (fun i => (out i).map fun _ => ())
  let claim₁ := fun i => treeStagesHalvingUpdate K (ctx₁ i) width j (p₁ i) (prior₁ i).1 (r i)
  let claim₂ := fun i => treeStagesHalvingUpdate K (ctx₂ i) width j (p₂ i) (prior₂ i).1 (r i)
  let w₁ := fun i => predictedTerms prims K D h c₁ (ctx₁ i) label 1 2
  let w₂ := fun i => predictedTerms prims K D h c₂ (ctx₁ i) label 1 2
  let v₁ := fun i => contextProductValues K (ctx₁ i) (finalProducts K (ctx₁ i) (claim₁ i) (w₁ i))
  let v₂ := fun i => contextProductValues K (ctx₂ i) (finalProducts K (ctx₂ i) (claim₂ i) (w₂ i))
  let k₁ := fun i => finalAfterField K (ctx₁ i) (claim₁ i) (w₁ i) (finish₁ i)
  let k₂ := fun i => finalAfterField K (ctx₂ i) (claim₂ i) (w₂ i) (finish₂ i)
  let Q := fun i x y => (∃ rnd : PrssOutput C E,
    x = treeSimExtendMultPartial K D ctx₁ live 2 (fun _ => rnd) v₁ (fun i => nextLabel (st₁ i)) k₁ i ∧
    y = treeSimExtendMultPartial K D ctx₂ live 2 (fun i => rnd + treeStagesPrssFieldShift (ctx₁ i) 2 δ₁)
      v₂ (fun i => nextLabel (st₂ i)) k₂ i) ∧
    (live i = true → w₂ i = w₁ i + (treeStagesPrssFieldShift (ctx₁ i) 2 δ₀).1)
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ out out
    (PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂) Q ?_ a b hab)
  · intro u v hu
    choose rnd left right using fun i => (hu.1 i).1
    exact ⟨⟨rnd, funext left, funext right⟩, fun i => (hu.1 i).2, hu.2⟩
  · intro i t z htz
    cases ho : out i with
    | none =>
      simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨⟨⟨0, ?_, ?_⟩, ?_⟩, htz⟩ <;>
        simp [treeSimExtendMultPartial, live, treeStagesChallengeLive, ho]
    | some values =>
      have hi : i ∉ D.1 := fun hi => by simpa [ho] using corrupt i hi
      simp only [treeSimResume]
      rw [treeStages_challenge_tail_factor, treeStages_challenge_tail_factor]
      simp only [simulateQ_bind, StateT.run_bind]
      have le₁ : base ≤ t.1.1 := base_le.trans htz.2.1
      have le₂ : base ≤ z.1 := by rw [← htz.1.1]; exact le₁
      have replay₁ := treeStages_challengeQuery_replay prims K D (tag i) (hashLabel i) values t.1
        (treeStages_challengeCovered_mono K le₁ _ _ _ (covered i values ho))
      have replay₂ := treeStages_challengeQuery_replay prims K D (tag i) (hashLabel i) values z
        (treeStages_challengeCovered_mono K le₂ _ _ _ (covered i values ho))
      rw [← treeStages_cachedChallenge_mono K le₁ _ _ _ (covered i values ho)] at replay₁
      rw [← treeStages_cachedChallenge_mono K le₂ _ _ _ (covered i values ho)] at replay₂
      apply relTriple_bind (treeStages_readOnly_pair prims D _ _ t z _ _ replay₁ replay₂)
      intro u v huv
      rw [huv.1, huv.2.1]
      have rel : PassRel K D label δ₀ δ₁ base₁ base₂ h c₁ c₂ u.2 v.2 := by
        simpa only [PassRel, TwoFieldRel, huv.2.2.1, huv.2.2.2] using htz
      cases hr : treeStagesCachedChallenge K base (tag i) (hashLabel i) values with
      | none =>
        simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        apply relTriple_pure_pure
        refine ⟨⟨⟨0, ?_, ?_⟩, ?_⟩, rel⟩ <;>
          simp [treeSimExtendMultPartial, live, treeStagesChallengeLive, ho, hr]
      | some s =>
        simp only [treeSimResume]
        apply relTriple_post_mono (finishing_entry prims K D label δ₀ δ₁ base₁ base₂ h c₁ c₂
          visible₀ visible₁ (ctx₁ i) (ctx₂ i) ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi)
          (hidden₁ i values s ho hr) (hidden₂ i values s ho hr) (visible i values s ho hr)
          width j (p₁ i) (p₂ i) (finish₁ i) (finish₂ i) (prior₁ i) (prior₂ i) s (st₁ i) (st₂ i)
          (lab₁ i hi) (lab₂ i hi) u.2 v.2 rel)
        intro u' v' result
        obtain ⟨⟨rnd, left, right⟩, masks, related⟩ := result
        refine ⟨⟨⟨rnd, ?_, ?_⟩, ?_⟩, related⟩
        · simpa [treeSimExtendMultPartial, treeSimExtendMultWaiting, live, treeStagesChallengeLive,
            ho, hr, hi, v₁, claim₁, r, w₁, k₁] using left
        · simpa [treeSimExtendMultPartial, treeSimExtendMultWaiting, live, treeStagesChallengeLive,
            ho, hr, hi, v₂, claim₂, r, w₂, k₂] using right
        · exact fun _ => masks


/-- The final mask shift is zero for every visible key name. -/
theorem finalMaskDelta_visible (D : C.Coalition) (T₀ : C.Term)
    (lacked : lackedTerm D.1 = some T₀) (r? : Option E) (a b : E) :
    ∀ name, ¬ Hidden D name → finalMaskDelta T₀ r? a b name = 0 := by
  intro name visible
  cases name with
  | parameter => rfl
  | pair p => rfl
  | term T =>
    cases r? with
    | none => rfl
    | some r =>
      have ne : T ≠ T₀ := by
        intro eq
        subst T
        exact visible (lackedTerm_unknown D T₀ lacked)
      simp [finalMaskDelta, ne]

/-- Conversion of the first mask shift gives the corresponding lacked-term share. -/
theorem finalMaskDelta_conv (D : C.Coalition) (T₀ : C.Term)
    (lacked : lackedTerm D.1 = some T₀) (ctx : Context C) (i : C.Party) (self : ctx.self = i)
    (r a b : E) (w : Shares C E) :
    conv K ctx (w + (treeStagesPrssFieldShift ctx 2 (finalMaskDelta T₀ (some r) a b)).1) 0 =
      conv K ctx w 0 + r / (1 + r) * lackedShare K D i a ∧
    conv K ctx (w + (treeStagesPrssFieldShift ctx 2 (finalMaskDelta T₀ (some r) a b)).1) 1 =
      conv K ctx w 1 + r / (1 + r) * lackedShare K D i b := by
  have each (g : Fin 2) :
      conv K ctx (w + (treeStagesPrssFieldShift ctx 2 (finalMaskDelta T₀ (some r) a b)).1) g =
        conv K ctx w g + r / (1 + r) * lackedShare K D i (![a,b] g) := by
    simp only [conv, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [lackedShare, conv, localContext, self, Finset.mul_sum, lacked]
    apply Finset.sum_congr rfl
    intro T ht
    have held := (Finset.mem_filter.mp ht).2
    simp only [treeStagesPrssFieldShift, self, if_pos held, treeStagesFieldDelta, g.isLt, ↓reduceDIte,
      finalMaskDelta, Option.some.injEq]
    by_cases eq : T = T₀
    · subst T
      fin_cases g <;> simp <;> ring
    · simp [eq, Ne.symm eq]
  exact ⟨each 0, each 1⟩


/-- Hidden term blocks read by a fixed set of live recipients. -/
def finishingBlocks (D : C.Coalition) (ctx : C.Party → Context C) (live : C.Party → Bool) :
    List (KeyName C × HashOutput) :=
  ((univ.filter fun it : C.Party × C.Term => live it.1 = true ∧
    (ctx it.1).self ∈ C.holders it.2 ∧ Hidden D (.term it.2)).image
      fun it => (KeyName.term it.2, (ctx it.1).prss.term it.2)).toList

/-- Empty visible stream keys read by the same recipients. -/
def finishingKeys (D : C.Coalition) (ctx : C.Party → Context C) (live : C.Party → Bool)
    (h : HashCache C) : List (Query C) :=
  ((univ.filter fun it : C.Party × C.Term => live it.1 = true ∧
    (ctx it.1).self ∈ C.holders it.2 ∧ ¬ Hidden D (.term it.2) ∧
    h (.streamKey ((ctx it.1).prss.term it.2)) = none).image
      fun it => Query.streamKey ((ctx it.1).prss.term it.2)).toList

/-- Membership exposes an actual live reader of a hidden block. -/
theorem finishingBlocks_mem (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (x : KeyName C × HashOutput) :
    x ∈ finishingBlocks D ctx live ↔ ∃ i T, live i = true ∧
      (ctx i).self ∈ C.holders T ∧ Hidden D (.term T) ∧ (.term T, (ctx i).prss.term T) = x := by
  simp only [finishingBlocks, Finset.mem_toList, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists]
  aesop

/-- Membership exposes an actual live reader of an empty visible stream key. -/
theorem finishingKeys_mem (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (h : HashCache C) (q : Query C) :
    q ∈ finishingKeys D ctx live h ↔ ∃ i T, live i = true ∧
      (ctx i).self ∈ C.holders T ∧ ¬ Hidden D (.term T) ∧
      h (.streamKey ((ctx i).prss.term T)) = none ∧ .streamKey ((ctx i).prss.term T) = q := by
  simp only [finishingKeys, Finset.mem_toList, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists]
  aesop

/-- The fixed live set is exactly successful Coin delivery followed by cached acceptance. -/
theorem finishing_live_iff (base : HashCache C) (tag hashLabel : C.Party → ℕ)
    (out : C.Party → Option (List E)) (i : C.Party) :
    treeStagesChallengeLive K base tag hashLabel (fun i => (out i).getD [])
      (fun i => (out i).map fun _ => ()) i = true ↔
      ∃ values r, out i = some values ∧
        treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some r := by
  cases ho : out i with
  | none => simp [treeStagesChallengeLive, ho]
  | some values =>
    simp only [treeStagesChallengeLive, ho, Option.map_some, Option.isSome_some,
      Bool.true_and, Option.getD_some]
    cases hr : treeStagesCachedChallenge K base (tag i) (hashLabel i) values <;> simp [hr]

/-- A supported actual finishing pass reads every listed cell, including visible stream keys. -/
theorem finishing_prefill_reads (D : C.Coalition) (label : ℕ)
    (ctx ref : C.Party → Context C) (width j : ℕ)
    (p : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (prior : C.Party → Shares C E × RunState C) (st : C.Party → RunState C)
    (tag hashLabel : C.Party → ℕ) (out : C.Party → Option (List E))
    (base : HashCache C) (s : TreeSimState C)
    (r : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (base_le : base ≤ s.1.1)
    (covered : ∀ i values, out i = some values → TreeStagesChallengeCovered K base (tag i) (hashLabel i) values)
    (same : ∀ i values, out i = some values → (ctx i).self = (ref i).self ∧
      (ctx i).prss = (ref i).prss ∧ (st i).label = label)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (treeSimResumeAll (fun i values => treeStagesChallengeTail K (tag i) (hashLabel i)
        (treeStagesHalvingBody K (ctx i) width j [] (p i) (finish i) (prior i)) (values, st i)) out)).run s)) :
    let live := treeStagesChallengeLive K base tag hashLabel (fun i => (out i).getD [])
      (fun i => (out i).map fun _ => ())
    (∀ x ∈ finishingBlocks D ref live, ∀ g : Fin (2 * elementBits),
      r.2.1.2 (x, label, 1, g.val) ≠ none) ∧
    ∀ q ∈ finishingKeys D ref live s.1.1, r.2.1.1 q ≠ none := by
  dsimp only
  have read (i : C.Party) (live : treeStagesChallengeLive K base tag hashLabel
      (fun i => (out i).getD []) (fun i => (out i).map fun _ => ()) i = true) :
      FinishingReads D (ref i) label r.2.1 := by
    obtain ⟨values, ch, coin, accept⟩ := (finishing_live_iff K base tag hashLabel out i).mp live
    have reads := finishing_pass_reads prims K D ctx width j p finish prior tag hashLabel
      (fun i => (out i).map fun values => (values, st i)) base s r base_le
      (by simpa only [treeStages_resumeAll_map] using run) i values (st i) ch
      (by simp only [coin, Option.map_some]) (covered i values coin) accept
    obtain ⟨self, keys, labels⟩ := same i values coin
    rw [labels] at reads
    unfold FinishingReads at reads ⊢
    intro T held
    have result := reads T (self.symm ▸ held)
    convert result using 1 <;> rw [keys]
  constructor
  · intro x hx g
    obtain ⟨i, T, live, held, hidden, rfl⟩ := (finishingBlocks_mem D ref _ x).mp hx
    exact ((read i live) T held).1 hidden g.val g.isLt
  · intro q hq
    obtain ⟨i, T, live, held, visible, _, rfl⟩ := (finishingKeys_mem D ref _ _ q).mp hq
    exact ((read i live) T held).2 visible

/-- The same list of mandatory reads in the ideal stream world. -/
theorem finishing_prefill_reads_stream (D : C.Coalition) (label : ℕ)
    (ctx ref : C.Party → Context C) (width j : ℕ)
    (p : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (prior : C.Party → Shares C E × RunState C) (st : C.Party → RunState C)
    (tag hashLabel : C.Party → ℕ) (out : C.Party → Option (List E))
    (base : HashCache C) (s : HashCache C × HiddenCache C)
    (r : (C.Party → Step C E RealSpec TreeOutput) × (HashCache C × HiddenCache C))
    (base_le : base ≤ s.1)
    (covered : ∀ i values, out i = some values → TreeStagesChallengeCovered K base (tag i) (hashLabel i) values)
    (same : ∀ i values, out i = some values → (ctx i).self = (ref i).self ∧
      (ctx i).prss = (ref i).prss ∧ (st i).label = label)
    (run : r ∈ support ((simulateQ (streamWorld prims D)
      (treeSimResumeAll (fun i values => treeStagesChallengeTail K (tag i) (hashLabel i)
        (treeStagesHalvingBody K (ctx i) width j [] (p i) (finish i) (prior i)) (values, st i)) out)).run s)) :
    let live := treeStagesChallengeLive K base tag hashLabel (fun i => (out i).getD [])
      (fun i => (out i).map fun _ => ())
    (∀ x ∈ finishingBlocks D ref live, ∀ g : Fin (2 * elementBits),
      r.2.2 (x, label, 1, g.val) ≠ none) ∧
    ∀ q ∈ finishingKeys D ref live s.1, r.2.1 q ≠ none := by
  rw [← treeSimLoggedWorld_erase prims D _ s [], support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  exact finishing_prefill_reads prims K D label ctx ref width j p finish prior st tag hashLabel out base
    (s, []) u base_le covered same hu


/-- A prefilled finishing pass determines both sides of every live term mask. -/
theorem finishing_prefilled_terms (D : C.Coalition) (label : ℕ)
    (δ₀ : KeyName C → Fin 2 → E) (ctx : C.Party → Context C) (live : C.Party → Bool)
    (h₀ h : HashCache C) (base₁ base₂ c₁ c₂ : HiddenCache C)
    (filled : Prefilled K D label 1 2 δ₀ (finishingBlocks D ctx live)
      (finishingKeys D ctx live h₀) h₀ base₁ base₂ h c₁ c₂)
    (i : C.Party) (hi : live i = true) :
    (∀ T, (ctx i).self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (2 * elementBits),
        c₁ ((.term T, (ctx i).prss.term T), label, 1, g.val) ≠ none ∧
        c₂ ((.term T, (ctx i).prss.term T), label, 1, g.val) ≠ none) ∧
    (∀ T, (ctx i).self ∈ C.holders T → ¬ Hidden D (.term T) →
      h (.streamKey ((ctx i).prss.term T)) ≠ none) := by
  constructor
  · intro T held hidden g
    obtain ⟨bits, left, right⟩ := filled.blocks _
      ((finishingBlocks_mem D ctx live _).mpr ⟨i, T, hi, held, hidden, rfl⟩)
    rw [left g, right g]
    exact ⟨Option.some_ne_none _, Option.some_ne_none _⟩
  · intro T held visible
    by_cases fresh : h₀ (.streamKey ((ctx i).prss.term T)) = none
    · exact filled.hashes _ ((finishingKeys_mem D ctx live h₀ _).mpr
        ⟨i, T, hi, held, visible, fresh, rfl⟩)
    · have absent : .streamKey ((ctx i).prss.term T) ∉ finishingKeys D ctx live h₀ := by
        intro mem
        obtain ⟨j, U, _, _, _, empty, eq⟩ := (finishingKeys_mem D ctx live h₀ _).mp mem
        rw [eq] at empty
        exact fresh empty
      rw [filled.hashFrame _ absent]
      exact fresh

section Stages
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (openings : List (List (List Bit)))

/-- The full field-stage body with its witnesses fixed. -/
def GuessFieldAt (r? : Option E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (f : FinalData K circuits settings top tree D parameter openings)
    (d : TreeSimExtendMultData K D) (offset L : ℕ) : Prop :=
    d.ctx₁ = f.caller.peer.ctx₁ ∧ d.ctx₂ = f.caller.peer.ctx₂ ∧ d.count = 2 ∧
    d.v₁ = (fun i => contextProductValues K (d.ctx₁ i) (f.products₁ K circuits settings top tree D parameter openings i)) ∧
    d.v₂ = (fun i => contextProductValues K (d.ctx₂ i) (f.products₂ K circuits settings top tree D parameter openings i)) ∧
    d.k₁ = (fun i => finalAfterField K (d.ctx₁ i) (f.claim₁ i) (f.w₁ i)
      (f.finish₁ K circuits settings top tree D parameter openings i)) ∧
    d.k₂ = (fun i => finalAfterField K (d.ctx₂ i) (f.claim₂ i) (f.w₂ i)
      (f.finish₂ K circuits settings top tree D parameter openings i)) ∧
    Position circuits settings tree D parameter f.caller.rest.circs offset d.st₁ ∧
    (∀ i, i ∉ D.1 → (d.st₁ i).tag = (d.st₂ i).tag ∧ (d.st₁ i).label = L ∧ (d.st₂ i).label = L) ∧
    CommonHistory D (fun _ => true) d.st₁ ∧ CommonHistory D (fun _ => true) d.st₂ ∧
    Frames D A (L + 1) δ a b ∧ δ = d.δ ∧
    (AllHistory D d.st₁ → ∀ r, r? = some r → ∀ i, i ∉ D.1 → ∀ o₁ o₂,
      o₂ = treeSimFieldHeldShift D i 2
        (fun g => ∑ j ∈ univ.filter (· ∉ D.1), (d.v₁ j g - d.v₂ j g)) o₁ → ∀ k < 3,
      finalVector K (d.ctx₁ i) (f.claim₁ i) (f.w₁ i) o₁ r k =
        finalVector K (d.ctx₂ i) (f.claim₂ i) (f.w₂ i) o₂ r k) ∧
    a.1.2 = treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂

/-- The guessed field stage retains the original saved stage and its exact successor. -/
def GuessFieldPlus (ĉ : E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (q : TreeStagesExtendMultChallenge K D)
    (w : SavedWitness K circuits settings top tree D parameter openings)
    (rnd : C.Party → PrssOutput C E) (δp : HiddenAddress C → Bit)
    (sent : C.Party → Mail C E) (s : E) (j : ℕ)
    (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (f : FinalData K circuits settings top tree D parameter openings)
    (d : TreeSimExtendMultData K D) (offset : ℕ),
    let n := q.coinNext K D rnd δp sent
    let tag := (q.st₁ q.pivotParty).tag
    SavedRelAt K circuits settings top tree D parameter openings q w ∧
    w.phase = .halving j v₁ v₂ ∧ w.phase.Finishing (tupleCount w.caller.rest.circs) ∧
    (∀ i, i ∉ D.1 → n.live i = true) ∧ f.caller = w.caller ∧
    (∀ i, i ∉ D.1 →
      f.claim₁ i = treeStagesHalvingUpdate K (q.ctx₁ i)
        (sliceWidth (tupleCount w.caller.rest.circs)) j (v₁ i) (n.x₁ i).1 s ∧
      f.claim₂ i = treeStagesHalvingUpdate K (q.ctx₂ i)
        (sliceWidth (tupleCount w.caller.rest.circs)) j (v₂ i) (n.x₂ i).1 s) ∧
    (∀ i, i ∉ D.1 → d.st₁ i = nextLabel (nextLabel (n.st₁ i)) ∧
      d.st₂ i = nextLabel (nextLabel (n.st₂ i))) ∧
    TreeStagesChallengeCovered K a.2.1.1 tag (q.label + 5) [ĉ] ∧
    GuessFieldAt K circuits settings top tree D A parameter openings
      (challengeAt K a.2.1.1 tag (q.label + 5) ĉ) δ a b f d offset (q.label + 3)

/-- Forgetting the saved data recovers the original guessed field stage. -/
theorem guessFieldPlus_stage (ĉ : E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : GuessFieldPlus K circuits settings top tree D A parameter openings ĉ δ a b) :
    ∃ r?, (∀ r, r? = some r → r ≠ 0 ∧ r ≠ 1) ∧
      GuessFieldStage K circuits settings top tree D A parameter openings r? δ a b := by
  obtain ⟨q, w, rnd, δp, sent, s, j, v₁, v₂, f, d, offset,
    _, _, _, _, _, _, _, _, stage⟩ := h
  exact ⟨_, fun r hr => challengeAt_some K _ _ _ _ r hr, f, d, offset, q.label + 3, stage⟩

/-- Every outcome of the finishing Coin pass, at the selected final guess. -/
def Round1End (ĉ : E) := treeTwinReq D (fun _ δ a b =>
  TreeTwinDoneStage a b ∨ StoppedFieldStage K D δ a b ∨
    GuessFieldPlus K circuits settings top tree D A parameter openings ĉ δ a b)


variable {K circuits settings top tree D parameter openings}

/-- The finishing field record can be cancelled from later holder agreement. -/
theorem finishing_history_before {q : TreeStagesExtendMultChallenge K D}
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true)
    (hist : AllHistory D (q.coinNext K D rnd δ sent).st₁) : AllHistory D q.st₁ := by
  apply allHistory_of_append D q.st₁ _
    (fun T => ((List.range q.count).filter fun g => (filler K .peer T g).isSome).length * elementBits) _ hist
  intro T i hi held
  have he := (SavedRelAt.coinNext_exit rnd δ sent live i hi).2.1
  change (q.coinNext K D rnd δ sent).st₁ i = _ at he
  rw [he]
  change ∃ l : List Bit, l.length = _ ∧
    recordPeer K (elementCodec K) (q.ctx₁ i).self (q.st₁ i).history _ q.count T = _
  rw [q.self₁ i hi]
  exact recordPeer_block K i _ _ _ T held

/-- The last saved halving leaves all five final labels within the batch. -/
theorem finishing_offset_bound {q : TreeStagesExtendMultChallenge K D}
    {w : SavedWitness K circuits settings top tree D parameter openings}
    (saved : SavedRelAt K circuits settings top tree D parameter openings q w)
    (finish : w.phase.Finishing (tupleCount w.caller.rest.circs))
    (jobs : List Job) (circs : w.caller.rest.circs = runCircuits circuits parameter jobs) :
    savedOffset w.caller.rest.circs w.phase + 5 ≤ batchLabels circuits parameter jobs := by
  obtain ⟨j, v₁, v₂, phase, last⟩ := saved.finishing_halving finish
  have nonzero := saved.count_ne_zero
  rw [phase, savedOffset]
  simp only [SavedPhase.index]
  rw [circs] at nonzero last ⊢
  change depth (runCircuits circuits parameter jobs) + 2 + 2 * (sliceBits + j) + 5 ≤
    depth (runCircuits circuits parameter jobs) + 1 + checkLabels (tupleCount (runCircuits circuits parameter jobs))
  rw [checkLabels, if_neg nonzero]
  unfold halvings halvSteps at *
  omega

/-- The actual twice-incremented field state has saved offset plus three. -/
theorem finishing_offset {q : TreeStagesExtendMultChallenge K D}
    {w : SavedWitness K circuits settings top tree D parameter openings}
    (saved : SavedRelAt K circuits settings top tree D parameter openings q w)
    (finish : w.phase.Finishing (tupleCount w.caller.rest.circs))
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) :
    Position circuits settings tree D parameter w.caller.rest.circs
      (savedOffset w.caller.rest.circs w.phase + 3)
      (fun i => nextLabel (nextLabel ((q.coinNext K D rnd δ sent).st₁ i))) := by
  apply position_shift circuits settings tree D parameter _ _ 3 q.st₁ _ saved.position
  · intro i hi
    have he := (SavedRelAt.coinNext_exit rnd δ sent live i hi).2.1
    change (q.coinNext K D rnd δ sent).st₁ i = _ at he
    simp only [nextLabel, he]
    rfl
  · intro i hi
    have he := (SavedRelAt.coinNext_exit rnd δ sent live i hi).2.1
    change (q.coinNext K D rnd δ sent).st₁ i = _ at he
    simp only [nextLabel, he]
    change (q.st₁ i).label + 1 + 1 + 1 = (q.st₁ i).label + 3
    omega
  · intro jobs hc
    exact Nat.le_trans (by omega) (finishing_offset_bound saved finish jobs hc)

/-- The final Coin address lies in the padding domain for this saved batch. -/
theorem finalAddress_mem {q : TreeStagesExtendMultChallenge K D}
    {w : SavedWitness K circuits settings top tree D parameter openings}
    (saved : SavedRelAt K circuits settings top tree D parameter openings q w)
    (finish : w.phase.Finishing (tupleCount w.caller.rest.circs)) :
    ((q.st₁ q.pivotParty).tag, q.label + 5) ∈ tagLabels circuits settings tree parameter := by
  let st := fun i => (⟨(q.st₁ i).history, (q.st₁ i).label + 5, (q.st₁ i).tag⟩ : RunState C)
  have pos : Position circuits settings tree D parameter w.caller.rest.circs
      (savedOffset w.caller.rest.circs w.phase + 5) st :=
    position_shift circuits settings tree D parameter _ _ 5 q.st₁ st saved.position
      (fun _ _ => rfl) (fun _ _ => rfl) (finishing_offset_bound saved finish)
  simpa only [st, Nat.add_zero, q.lab₁ q.pivotParty q.pivot.honest] using
    position_mem circuits settings tree D parameter _ _ _ pos 0 (by omega) q.pivotParty q.pivot.honest

end Stages

/-- Padding covers any final-Coin guess at the reached saved finishing address. -/
theorem finalAddress_covered (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (TreeTwinLinked2.padding K circuits settings tree parameter seeds)).run p.2.2.1.1))
    (q : TreeStagesExtendMultChallenge K D)
    (w : SavedWitness K circuits settings top tree D parameter p.1.2)
    (saved : SavedRelAt K circuits settings top tree D parameter p.1.2 q w)
    (finish : w.phase.Finishing (tupleCount w.caller.rest.circs))
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a)
    (swaps : List (List Bit × HashOutput × HashOutput)) (ĉ : E) :
    TreeStagesChallengeCovered K (treeStagesTwin swaps a.2).1.1
      (q.st₁ q.pivotParty).tag (q.label + 5) [ĉ] :=
  treeTwin_reached_challengeCovered prims K circuits settings top tree D A
    (dealtKeys parameter seeds pairs) p.2.1 p.2.2 seeds
    (tagLabels circuits settings tree parameter) (historyLimit circuits settings) r padding n a reach swaps
    _ _ (finalAddress_mem saved finish) [ĉ] rfl


/-- One actual saved finishing Coin round, for every fixed final-Coin guess. -/
theorem finishingRound (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (TreeTwinLinked2.padding K circuits settings tree parameter seeds)).run p.2.2.1.1))
    (ĉ : E) : ∀ n δ swaps a b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a → n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    segReq K circuits settings top tree D A parameter p.1.2 n δ (a.1, treeStagesTwin swaps a.2) b →
    FinishingCoinLive K circuits settings top tree D A parameter p.1.2 δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
      (fun v w => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
        ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
          Round1End K circuits settings top tree D A parameter p.1.2 ĉ (n + 1) δ'
            ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2)) := by
  intro round δ swaps a b reach bound good active salts req stage
  obtain ⟨related, state, _, _, _⟩ := req
  obtain ⟨q, rnd, sent, coinRnd, ⟨w, saved, finish⟩, allLive, visibleOld, future,
    fresh₁, fresh₂, left, right⟩ := stage
  let n := q.coinNext K D rnd δ sent
  obtain ⟨j, v₁, v₂, phase, last⟩ := saved.finishing_halving finish
  have source := saved.state
  simp only [SavedState, phase] at source
  obtain ⟨body₁, body₂, products₁, products₂, shape, rel⟩ := source
  have suffix : halvSuffix (tupleCount w.caller.rest.circs) j = [] := by
    simpa only [phase, SavedPhase.Finishing] using finish
  let width := sliceWidth (tupleCount w.caller.rest.circs)
  let finish₁ := (w.caller.checkData K circuits settings top tree D parameter p.1.2).finish₁
  let finish₂ := (w.caller.checkData K circuits settings top tree D parameter p.1.2).finish₂
  let tag := fun i => (n.st₁ i).tag
  let hashLabel := fun i => (n.st₁ i).label
  let k₁ := fun i => treeStagesChallengeTail K (tag i) (hashLabel i)
    (treeStagesHalvingBody K (q.ctx₁ i) width j [] (v₁ i) (finish₁ i) (n.x₁ i))
  let k₂ := fun i => treeStagesChallengeTail K (tag i) (hashLabel i)
    (treeStagesHalvingBody K (q.ctx₂ i) width j [] (v₂ i) (finish₂ i) (n.x₂ i))
  have tags (i : C.Party) (hi : i ∉ D.1) : (n.st₂ i).tag = (n.st₁ i).tag :=
    (q.coinNext_tag K D rnd δ sent i).2.trans
      ((saved.tags i hi).symm.trans (q.coinNext_tag K D rnd δ sent i).1.symm)
  have labels (i : C.Party) (hi : i ∉ D.1) : (n.st₂ i).label = (n.st₁ i).label :=
    (n.lab₂ i hi).trans (n.lab₁ i hi).symm
  have next₁ (i : C.Party) (hi : i ∉ D.1) : n.next₁ i = k₁ i := by
    change treeStagesChallengeTail K (n.st₁ i).tag (n.st₁ i).label (q.body₁ i (n.x₁ i)) = _
    rw [body₁ i hi, saved.counts i hi, suffix]
  have next₂ (i : C.Party) (hi : i ∉ D.1) : n.next₂ i = k₂ i := by
    change treeStagesChallengeTail K (n.st₂ i).tag (n.st₂ i).label (q.body₂ i (n.x₂ i)) = _
    rw [body₂ i hi, saved.counts i hi, suffix, tags i hi, labels i hi]
  have coins₁ : treeSimCoinWaiting K D n.count coinRnd n.st₁ n.next₁ =
      treeSimCoinWaiting K D 1 coinRnd n.st₁ k₁ := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCoinWaiting, hi]
    · simp only [treeSimCoinWaiting, if_neg hi, next₁ i hi]
      rfl
  have coins₂ : treeSimCoinWaiting K D n.count coinRnd n.st₂ n.next₂ =
      treeSimCoinWaiting K D 1 coinRnd n.st₂ k₂ := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCoinWaiting, hi]
    · simp only [treeSimCoinWaiting, if_neg hi, next₂ i hi]
      rfl
  rw [left, right, treeStages_coin_partial_live K D n.live allLive,
    treeStages_coin_partial_live K D n.live allLive, coins₁, coins₂, ← state]
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_coin_round_factor, treeSim_coin_round_factor]
  simp only [treeStages_resumeAll_map, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeSim_local_streamRel_fixed prims D δ _ (treeStagesTwin swaps a.2) b.2 related))
  intro r₁ r₂ hr
  rw [hr.1.1]
  let base := (treeStagesTwin swaps a.2).1.1
  let out := treeSimCoinOutput K D 1 coinRnd r₂.1.2
  let live := treeStagesChallengeLive K base tag hashLabel (fun i => (out i).getD [])
    (fun i => (out i).map fun _ => ())
  let sampled := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) ((out i).getD [])).getD 0
  have base_le : base ≤ r₁.2.1.1 := treeSim_logged_grows prims D _ _ r₁ hr.2.1
  have fresh₁' : TreeSimFutureEmpty (q.label + 2) r₁.2.1.2 := by
    rw [hr.1.2.2.1]
    exact fresh₁
  have fresh₂' : TreeSimFutureEmpty (q.label + 2) r₂.2.2 := by
    rw [hr.1.2.2.2]
    exact fresh₂
  have corrupt (i : C.Party) (hi : i ∈ D.1) : out i = none := by simp [out, treeSimCoinOutput, hi]
  have honest (i : C.Party) (values : List E) (ho : out i = some values) : i ∉ D.1 :=
    fun hi => by rw [corrupt i hi] at ho; cases ho
  have covered (i : C.Party) (values : List E) (ho : out i = some values) :
      TreeStagesChallengeCovered K base (tag i) (hashLabel i) values := by
    exact treeTwin_reached_challengeCovered prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) p.2.1 p.2.2 seeds
      (tagLabels circuits settings tree parameter) (historyLimit circuits settings) r padding round a reach swaps
      _ _ (saved.address rnd δ sent i (honest i values ho)).2 values
      (treeStages_coinOutput_length K D 1 coinRnd r₂.1.2 i values ho)
  have finalCovered : TreeStagesChallengeCovered K base (q.st₁ q.pivotParty).tag (q.label + 5) [ĉ] :=
    finalAddress_covered prims K circuits settings top tree D A parameter seeds pairs p r padding
      q w saved finish round a reach swaps ĉ
  let guess := challengeAt K base (q.st₁ q.pivotParty).tag (q.label + 5) ĉ
  let s := sampled q.pivotParty
  have shifted := saved.outputShift rnd δ sent allLive
  have shifted' := shifted.congr_products K D q.ctx₁ q.ctx₂ _ _ _ _ _ _ products₁ products₂
  have shape' := halvFold_shape K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ width j v₁ v₂ _ _ shifted' s shape
  obtain ⟨eA, eB, e, shapeA, shapeB, shapeD⟩ := shape'
  let δ₀ := if ∀ i, i ∉ D.1 → live i = true then finalMaskDelta q.T₀ guess (eA 0) (eB 0) else 0
  have visible₀ : ∀ name, ¬ Hidden D name → δ₀ name = 0 := by
    dsimp only [δ₀]
    split
    · exact finalMaskDelta_visible D q.T₀ q.pivot.lacked guess (eA 0) (eB 0)
    · simp
  let blocks := finishingBlocks D q.ctx₁ live
  let qs := finishingKeys D q.ctx₁ live r₁.2.1.1
  have hiddenB : ∀ x ∈ blocks, Hidden D x.1 := by
    intro x hx
    obtain ⟨i, T, _, _, hidden, rfl⟩ := (finishingBlocks_mem D q.ctx₁ live x).mp hx
    exact hidden
  have freshQ : ∀ x ∈ qs, r₁.2.1.1 x = none := by
    intro x hx
    obtain ⟨i, T, _, _, _, empty, rfl⟩ := (finishingKeys_mem D q.ctx₁ live _ x).mp hx
    exact empty
  have lab₁ (i : C.Party) (hi : i ∉ D.1) : (nextLabel (n.st₁ i)).label = q.label + 2 := by
    change (n.st₁ i).label + 1 = _
    rw [n.lab₁ i hi]
    rfl
  have lab₂ (i : C.Party) (hi : i ∉ D.1) : (nextLabel (n.st₂ i)).label = q.label + 2 := by
    change (n.st₂ i).label + 1 = _
    rw [n.lab₂ i hi]
    rfl
  refine relTriple_bind (R := fun u v => ∃ δ',
    Round1End K circuits settings top tree D A parameter p.1.2 ĉ (round + 1) δ'
      ((r₂.1.1, u.1), u.2) ((r₂.1.1, v.1), v.2)) ?_ (by
    intro u v huv
    obtain ⟨δ', result⟩ := huv
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨[], δ', fun x hx => by simp at hx, result⟩))
  apply prefill_pass_coupling prims K D (q.label + 2) 1 2 δ₀ blocks
    (Finset.nodup_toList _) hiddenB qs (Finset.nodup_toList _)
    (by
      intro x hx
      obtain ⟨i, T, _, _, _, _, rfl⟩ := (finishingKeys_mem D q.ctx₁ live _ x).mp hx
      rintro ⟨_, eq, _⟩
      cases eq)
    _ _ r₁.2 r₂.2 hr.1.2.1.1
    (fun x hx g => fresh₁' _ le_rfl) (fun x hx g => fresh₂' _ le_rfl) freshQ
    (by
      intro u hu
      exact finishing_prefill_reads prims K D (q.label + 2) q.ctx₁ q.ctx₁ width j v₁ finish₁ n.x₁
        (fun i => nextLabel (n.st₁ i)) tag hashLabel out base r₁.2 u base_le covered
        (fun i values ho => ⟨rfl, rfl, lab₁ i (honest i values ho)⟩) hu)
    (by
      intro u hu
      have reads := finishing_prefill_reads_stream prims K D (q.label + 2) q.ctx₂ q.ctx₁ width j v₂ finish₂ n.x₂
        (fun i => nextLabel (n.st₂ i)) tag hashLabel out base r₂.2 u
        (by rw [← hr.1.2.1.1]; exact base_le) covered
        (fun i values ho => ⟨(q.self₂ i (honest i values ho)).trans (q.self₁ i (honest i values ho)).symm,
          (q.keys i (honest i values ho)).symm, lab₂ i (honest i values ho)⟩) hu
      simpa only [qs, hr.1.2.1.1] using reads)
  intro h c₁ c₂ filled
  let f : FinalData K circuits settings top tree D parameter p.1.2 := {
    caller := w.caller
    claim₁ := fun i => treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 (sampled i)
    claim₂ := fun i => treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 (sampled i)
    w₁ := fun i => predictedTerms prims K D h c₁ (q.ctx₁ i) (q.label + 2) 1 2
    w₂ := fun i => predictedTerms prims K D h c₂ (q.ctx₁ i) (q.label + 2) 1 2 }
  let fv₁ := fun i => contextProductValues K (q.ctx₁ i) (finalProducts K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i))
  let fv₂ := fun i => contextProductValues K (q.ctx₂ i) (finalProducts K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i))
  let dt := termShift K D q.T₀ q.pivotParty (fv₁ - fv₂) (0 : C.Term → Fin 2 → E)
  let dp := pairShift q.pivotParty (pairDelta K D q.T₀ q.pivotParty (fv₁ - fv₂) (0 : C.Term → Fin 2 → E))
  let δ₁ := treeStagesMaskDelta D 2 dt dp
  have prefilledLe : r₁.2.1.1 ≤ h := prefilled_hash_le K D (q.label + 2) 1 2 δ₀ blocks qs
    _ _ _ _ _ _ filled freshQ
  have prefilledRel : PassRel K D (q.label + 2) δ₀ δ₁ r₁.2.1.2 r₂.2.2 h c₁ c₂
      ((h, c₁), r₁.2.2) (h, c₂) := by
    refine ⟨⟨rfl, ?_⟩, le_rfl, le_rfl, le_rfl⟩
    exact prefilled_twoField K D (q.label + 2) 1 2 (q.label + 2 + 1) 0 2 δ₀ δ₁ blocks qs
      r₁.2.1.1 h r₁.2.1.2 r₂.2.2 c₁ c₂ filled hiddenB (by omega) fresh₁' fresh₂' (by omega)
  have reads (i : C.Party) (values : List E) (ch : E) (ho : out i = some values)
      (hs : treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some ch) :=
    finishing_prefilled_terms K D (q.label + 2) δ₀ q.ctx₁ live r₁.2.1.1 h r₁.2.1.2 r₂.2.2 c₁ c₂
      filled i ((finishing_live_iff K base tag hashLabel out i).mpr ⟨values, ch, ho, hs⟩)
  apply relTriple_post_mono (finishing_prefilled_pass prims K D (q.label + 2) δ₀ δ₁ r₁.2.1.2 r₂.2.2
    h c₁ c₂ visible₀ (treeStagesMaskDelta_visible D 2 dt dp) q.ctx₁ q.ctx₂ q.self₁ q.self₂ q.keys
    width j v₁ v₂ finish₁ finish₂ n.x₁ n.x₂ (fun i => nextLabel (n.st₁ i))
    (fun i => nextLabel (n.st₂ i)) lab₁ lab₂ tag hashLabel out corrupt base
    (base_le.trans prefilledLe) covered
    (fun i values ch ho hs T ht hh g => ((reads i values ch ho hs).1 T ht hh g).1)
    (fun i values ch ho hs T ht hh g => ((reads i values ch ho hs).1 T ht hh g).2)
    (fun i values ch ho hs => (reads i values ch ho hs).2)
    ((h, c₁), r₁.2.2) (h, c₂) prefilledRel)
  intro u v result
  obtain ⟨⟨fieldRnd, step₁, step₂⟩, masks, caches⟩ := result
  let δ' := twoFieldCacheDelta D (q.label + 2) 1 2 (q.label + 2 + 1) 0 2 δ u.2.1.2 v.2.2
  let d := treeStagesExtendMultData K D q.T₀ q.pivotParty q.pivot δ' 2 q.ctx₁ q.ctx₂ q.self₁ q.self₂
    fieldRnd fv₁ fv₂ (fun i => nextLabel (nextLabel (n.st₁ i))) (fun i => nextLabel (nextLabel (n.st₂ i)))
    (fun i => finalAfterField K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i) (finish₁ i))
    (fun i => finalAfterField K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i) (finish₂ i))
  have steps₁ : u.1 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ := step₁
  have steps₂ : v.1 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ := by
    rw [step₂]
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
    · have shift := treeStages_prssFieldShift_mask D (q.ctx₁ i)
        (by simpa only [q.self₁ i hi] using hi) 2 dt dp
      rw [q.self₁ i hi] at shift
      simp only [d, treeStagesExtendMultData, treeSimExtendMultPartial, treeSimExtendMultWaiting, if_neg hi]
      split
      · rw [shift]
      · rfl
  have stream : TreeSimStreamRel δ' u.2 v.2 :=
    ⟨caches.1.1, twoFieldCaches_related K D _ _ _ _ _ _ δ₀ δ₁ δ _ _ _ _ caches.1.2 hr.1.2.1.2⟩
  have frames : Frames D A (q.label + 4) δ' ((r₂.1.1, u.1), u.2) ((r₂.1.1, v.1), v.2) := by
    refine ⟨twoFieldCacheDelta_visible D _ _ _ _ _ _ δ _ _ visibleOld,
      twoFieldCacheDelta_future D _ _ _ _ _ _ _ δ _ _ (by omega) (by omega)
        (fun x hx => future x (by omega)), ?_⟩
    exact twoFieldCaches_future K D _ _ _ _ _ _ _ δ₀ δ₁ _ _ _ _ caches.1.2 (by omega) (by omega)
      (fun x hx => fresh₁' x (by omega)) (fun x hx => fresh₂' x (by omega))
  have flags := treeTwin_flags_of_sameKind D u.1 v.1 (fun i hi => by
    rw [steps₁, steps₂]
    exact treeTwin_sameKind_extendPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
  refine ⟨δ', stream, rfl, flags.1, flags.2, ?_⟩
  by_cases full : ∀ i, i ∉ D.1 → live i = true
  · have sampled_eq (i : C.Party) (hi : i ∉ D.1) : sampled i = s := by
      obtain ⟨values, ch, oi, ci⟩ := (finishing_live_iff K base tag hashLabel out i).mp (full i hi)
      obtain ⟨values', ch', op, cp⟩ := (finishing_live_iff K base tag hashLabel out q.pivotParty).mp
        (full q.pivotParty q.pivot.honest)
      have vals := coinOutput_agree K D 1 coinRnd r₂.1.2 hi q.pivot.honest oi op
      have addr : (tag i, hashLabel i) = (tag q.pivotParty, hashLabel q.pivotParty) :=
        (saved.address rnd δ sent i hi).1.trans
          (saved.address rnd δ sent q.pivotParty q.pivot.honest).1.symm
      obtain ⟨tags', labels'⟩ := Prod.mk.inj addr
      simp only [sampled, s, oi, op, Option.getD_some, vals, tags', labels']
    have claim₁ (i : C.Party) (hi : i ∉ D.1) : f.claim₁ i =
        treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 s := by
      change treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 (sampled i) = _
      rw [sampled_eq i hi]
    have claim₂ (i : C.Party) (hi : i ∉ D.1) : f.claim₂ i =
        treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 s := by
      change treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 (sampled i) = _
      rw [sampled_eq i hi]
    have hist₁ : CommonHistory D (fun _ => true) n.st₁ := by
      exact commonHistory_extendMult K D q.ctx₁ q.self₁ q.count rnd (fun i => contextProductValues K (q.ctx₁ i) (q.products₁ i)) q.st₁ (q.k₁ K D) sent n.x₁
        (fun i hi => by
          have hl : n.live i = true := allLive i hi
          simpa only [if_neg hi, hl, ↓reduceIte] using n.shape₁ i) saved.history₁
    have hist₂ : CommonHistory D (fun _ => true) n.st₂ := by
      exact commonHistory_extendMult K D q.ctx₂ q.self₂ q.count (q.data K D rnd δ).rnd₂ (fun i => contextProductValues K (q.ctx₂ i) (q.products₂ i)) q.st₂
        (q.k₂ K D) sent n.x₂
        (fun i hi => by
          have hl : n.live i = true := allLive i hi
          simpa only [if_neg hi, hl, ↓reduceIte] using n.shape₂ i) saved.history₂
    have leFinal : base ≤ u.2.1.1 := base_le.trans (prefilledLe.trans caches.2.1)
    refine Or.inr (Or.inr ⟨q, w, rnd, δ, sent, s, j, v₁, v₂, f, d,
      savedOffset w.caller.rest.circs w.phase + 3, saved, phase, finish, allLive, rfl,
      (fun i hi => ⟨claim₁ i hi, claim₂ i hi⟩), (fun _ _ => ⟨rfl, rfl⟩),
      treeStages_challengeCovered_mono K leFinal _ _ _ finalCovered, ?_⟩)
    refine ⟨saved.ctx₁, saved.ctx₂, rfl, ?_, ?_, rfl, rfl,
      finishing_offset saved finish rnd δ sent allLive, ?_, hist₁, hist₂,
      frames, rfl, ?_, steps₁.trans (extendMultPartial_allLive K D _ _ _ _ _ _ _ full),
      steps₂.trans (extendMultPartial_allLive K D _ _ _ _ _ _ _ full)⟩
    · change fv₁ = fun i => contextProductValues K (q.ctx₁ i)
        (f.products₁ K circuits settings top tree D parameter p.1.2 i)
      unfold FinalData.products₁
      change fv₁ = fun i => contextProductValues K (q.ctx₁ i)
        (finalProducts K (w.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i))
      rw [← saved.ctx₁]
    · change fv₂ = fun i => contextProductValues K (q.ctx₂ i)
        (f.products₂ K circuits settings top tree D parameter p.1.2 i)
      unfold FinalData.products₂
      change fv₂ = fun i => contextProductValues K (q.ctx₂ i)
        (finalProducts K (w.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i))
      rw [← saved.ctx₂]
    · intro i hi
      exact ⟨(tags i hi).symm, by change (n.st₁ i).label + 1 + 1 = q.label + 3; rw [n.lab₁ i hi]; rfl,
        by change (n.st₂ i).label + 1 + 1 = q.label + 3; rw [n.lab₂ i hi]; rfl⟩
    · intro allHist rr hrr i hi o₁ o₂ ho k hk
      have guessEq : guess = some rr := by
        change challengeAt K base (q.st₁ q.pivotParty).tag (q.label + 5) ĉ = some rr
        rw [challengeAt_mono K leFinal _ _ _ finalCovered]
        exact hrr
      have rrne := challengeAt_some K base (q.st₁ q.pivotParty).tag (q.label + 5) ĉ rr guessEq
      have nonzero : 1 + rr ≠ 0 := by
        letI : CharP E 2 := charTwo
        intro eq
        apply rrne.2
        have h2 : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
        linear_combination eq - h2
      let c₁' := fun i => treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 s
      let c₂' := fun i => treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 s
      have relation : HalvRel K D 1 (fun i => (c₁' i).1) (fun i => (c₁' i).2.1)
          (fun i => (c₂' i).1) (fun i => (c₂' i).2.1) (fun i => (c₁' i).2.2) (fun i => (c₂' i).2.2) := by
        letI : CharP E 2 := charTwo
        have h := halvFold_rel K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ width j v₁ v₂ _ _ shifted' s
          (rel (finishing_history_before rnd δ sent allLive allHist))
        rw [Function.iterate_succ_apply', saved.finishing_length finish j v₁ v₂ phase] at h
        exact h
      have maskEq (j : C.Party) (hj : j ∉ D.1) :
          f.w₂ j = f.w₁ j + (treeStagesPrssFieldShift (q.ctx₁ j) 2
            (finalMaskDelta q.T₀ (some rr) (eA 0) (eB 0))).1 := by
        have m := masks j (full j hj)
        simpa only [δ₀, if_pos full, guessEq] using m
      have ma (j : C.Party) (hj : j ∉ D.1) : conv K (q.ctx₂ j) (f.w₂ j) 0 =
          conv K (q.ctx₁ j) (f.w₁ j) 0 + rr / (1 + rr) * ((c₁' j).1 0 - (c₂' j).1 0) := by
        rw [conv_self K _ j (q.self₂ j hj), ← conv_self K (q.ctx₁ j) j (q.self₁ j hj), maskEq j hj]
        rw [(finalMaskDelta_conv K D q.T₀ q.pivot.lacked (q.ctx₁ j) j (q.self₁ j hj)
          rr (eA 0) (eB 0) (f.w₁ j)).1, shapeA j hj 0]
      have mb (j : C.Party) (hj : j ∉ D.1) : conv K (q.ctx₂ j) (f.w₂ j) 1 =
          conv K (q.ctx₁ j) (f.w₁ j) 1 + rr / (1 + rr) * ((c₁' j).2.1 0 - (c₂' j).2.1 0) := by
        rw [conv_self K _ j (q.self₂ j hj), ← conv_self K (q.ctx₁ j) j (q.self₁ j hj), maskEq j hj]
        rw [(finalMaskDelta_conv K D q.T₀ q.pivot.lacked (q.ctx₁ j) j (q.self₁ j hj)
          rr (eA 0) (eB 0) (f.w₁ j)).2, shapeB j hj 0]
      let out₁ := fun _ : C.Party => o₁
      let out₂ := fun j => treeSimFieldHeldShift D j 2
        (fun g => ∑ l ∈ univ.filter (· ∉ D.1), (fv₁ l g - fv₂ l g)) o₁
      have output : OutputShift K D q.ctx₁ q.ctx₂
          (fun i => finalProducts K (q.ctx₁ i) (c₁' i) (f.w₁ i))
          (fun i => finalProducts K (q.ctx₂ i) (c₂' i) (f.w₂ i)) out₁ out₂ := by
        apply OutputShift.congr_products K D q.ctx₁ q.ctx₂
          (fun i => finalProducts K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i))
          (fun i => finalProducts K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i)) _ _ out₁ out₂
          (fun _ _ => rfl)
        · intro j hj
          rw [claim₁ j hj]
        · intro j hj
          rw [claim₂ j hj]
      have eq := guess_conjunct K D q.T₀ q.pivot.lacked q.ctx₁ q.ctx₂ q.self₁ q.self₂
        c₁' c₂' f.w₁ f.w₂ rr e nonzero relation shapeD ma mb out₁ out₂ output i hi k hk
      change finalVector K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i) o₁ rr k =
        finalVector K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i) o₂ rr k
      rw [claim₁ i hi, claim₂ i hi, ho]
      exact eq
  · push Not at full
    exact Or.inr (Or.inl ⟨d, live, full, rfl, steps₁, steps₂⟩)


/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.prefilled_twoField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefilled_twoField

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.predictedTerms_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms predictedTerms_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.guess_conjunct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guess_conjunct

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishing_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishing_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishing_prefilled_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishing_prefilled_pass

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finalMaskDelta_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalMaskDelta_conv

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishing_prefill_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishing_prefill_reads

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishing_prefill_reads_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishing_prefill_reads_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishing_prefilled_terms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishing_prefilled_terms

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.guessFieldPlus_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guessFieldPlus_stage

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishing_history_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishing_history_before

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishing_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishing_offset

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finalAddress_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalAddress_covered

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessStart.finishingRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finishingRound

end ThresholdLeanXmssSecurity.TreeTwinGuessStart
