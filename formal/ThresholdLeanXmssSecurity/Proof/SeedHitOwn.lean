import ThresholdLeanXmssSecurity.Proof.SigningOwnClaim

/-!
# The cost of a call on a hidden key with the own budget

`DistinctFlagOwn` of `Proof/SigningOwnClaim.lean` (`distinctFlagOwn`). It is the second stage of
`seedHitBound` of `Proof/SeedHit.lean`, with the own budget of the forger in place of the count of the
world.

* A call can hit a hidden key only if it is an own call of `H` by the forger. Such a call is counted,
  so the static budget pays it (`roCost_counted`).
* So the first hits of a key, summed over all its values, cost at most the own budget
  (`sum_ff_le_own`). The calls of the dealer and of the honest operators are not in the sum.
* With the resampling of one key, each key costs `q / 2^256` (`keyHitOwn`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SeedHitOwn

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof SeedHitProof
open SigningOwnForger SigningOwnClaim

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)
attribute [local irreducible] MonadAttach.support

/-- A call that can hit a key costs at most one, and it is counted in the own budget. -/
theorem roCost_counted (t : (LocalSpec C + TsigSpec C).Domain) :
    roCost t ≤ 1 ∧ (roCost t ≠ 0 → SigningOwnCounted t) := by
  rcases t with (_ | (_ | _)) | _ <;> simp [roCost, SigningOwnCounted]

/-- The weight of the first hits of `σ` over its values outside `V` is at most the own budget. -/
theorem sum_ff_le_own (x : Keys3 C) (σ : KeySlot C) (top : TopTree) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) : ∀ (n : ℕ) (V : Finset HashOutput)
    (p : SeedHitProof.GState C),
    (∀ k ∉ V, Function.Injective (slotInput (SeedHitProof.xk x σ k).2.1 (SeedHitProof.xk x σ k).2.2)) →
    ¬Revealed p.1.1.1.corrupt σ → σ ∉ p.1.2 → IsQueryBoundP oa SigningOwnCounted n →
    ∑ k ∈ Finset.univ \ V, Pr{let z ←
      (simulateQ (SeedHitProof.fusedImpl prims (SeedHitProof.xk x σ k) top) oa).run p}[σ ∈ z.2.1.2] ≤ (n : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n V p _ _ hσ _
    refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ?_) bot_le
    simp [hσ]
  | query_bind t cont ih =>
    intro n V p hinj hD hσ hq
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
    by_cases hf : p.1.1.2 = true
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => tsum_eq_zero_iff.mpr fun z => ?_) bot_le
      by_cases hz : z ∈ support ((fusedImpl prims (xk x σ k) top t).run p)
      · obtain ⟨h1, h2⟩ := fused_frozen prims _ top t p hf z hz
        rw [fused_ff_zero prims _ top σ _ z.2 (Or.inr h1) (h2 ▸ hσ), mul_zero]
      · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul]
    by_cases hrev : RevealsT σ p.1.1.1 t
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => tsum_eq_zero_iff.mpr fun z => ?_) bot_le
      by_cases hz : z ∈ support ((fusedImpl prims (xk x σ k) top t).run p)
      · obtain ⟨h1, h2⟩ := fused_reveals prims _ top σ t p hrev hσ z hz
        rw [fused_ff_zero prims _ top σ _ z.2 (Or.inl h1) h2, mul_zero]
      · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul]
    -- the values of `σ` that the call hits
    obtain ⟨H, hHdef⟩ : ∃ H : Finset HashOutput, H = Finset.univ.filter fun k => HitT σ t k := ⟨_, rfl⟩
    have hmemH : ∀ k, k ∈ H ↔ HitT σ t k := fun k => by simp [hHdef]
    have hH : H.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
      obtain ⟨u, rfl, hu⟩ := (hmemH a).mp ha
      obtain ⟨u', hu', hu''⟩ := (hmemH b).mp hb
      cases hu'
      exact hitQuery_unique hu hu''
    obtain ⟨V', hV'⟩ : ∃ V' : Finset HashOutput, V' = V ∪ H := ⟨_, rfl⟩
    have hsplit : Finset.univ \ V = (H \ V) ∪ (Finset.univ \ V') := by
      ext k
      subst hV'
      by_cases hk : k ∈ H <;> by_cases hkV : k ∈ V <;> simp [hk, hkV]
    have hdisj : Disjoint (H \ V) (Finset.univ \ V') := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      subst hV'
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hk hk'
      exact hk'.2 hk.1
    rw [hsplit, Finset.sum_union hdisj]
    -- the cost of the call and the budget of the rest
    obtain ⟨ct, hct⟩ : ∃ ct : ℕ, ct = roCost t := ⟨_, rfl⟩
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, n' = if SigningOwnCounted t then n - 1 else n := ⟨_, rfl⟩
    have hbud : ct + n' ≤ n := by
      obtain ⟨h1, h2⟩ := roCost_counted t
      by_cases hc : SigningOwnCounted t
      · rw [ite_eq_left hc] at hn'
        have := hq.1.resolve_left (not_not.mpr hc)
        omega
      · rw [ite_eq_right hc] at hn'
        have : roCost t = 0 := by by_contra h; exact hc (h2 h)
        omega
    -- the hit part
    have hhit : ∑ k ∈ H \ V, (∑' z, Pr{let y ← (fusedImpl prims (xk x σ k) top t).run p}[y = z] *
        Pr{let z' ← (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2}[σ ∈ z'.2.1.2]) ≤ ct := by
      rcases (H \ V).eq_empty_or_nonempty with he | ⟨k₀, hk₀⟩
      · rw [he, Finset.sum_empty]; exact zero_le
      have hct1 : ct = 1 := by
        obtain ⟨u, hu, -⟩ := (hmemH k₀).mp (Finset.mem_sdiff.mp hk₀).1
        rw [hct, hu]; rfl
      rw [hct1, Nat.cast_one]
      calc ∑ k ∈ H \ V, (∑' z, Pr{let y ← (fusedImpl prims (xk x σ k) top t).run p}[y = z] *
            Pr{let z' ← (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2}[σ ∈ z'.2.1.2])
          ≤ ∑ k ∈ H \ V, (1 : ℝ≥0∞) := Finset.sum_le_sum fun k _ => by
            rw [← OracleComp.prEvent_bind_eq_tsum]; exact (prEvent_le_one _)
        _ = ((H \ V).card : ℝ≥0∞) := by simp
        _ ≤ 1 := by exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hH
    -- the other values
    have hrest : ∑ k ∈ Finset.univ \ V', (∑' z, Pr{let y ← (fusedImpl prims (xk x σ k) top t).run p}[y = z] *
        Pr{let z' ← (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2}[σ ∈ z'.2.1.2]) ≤
          (n' : ℝ≥0∞) := by
      rcases (Finset.univ \ V').eq_empty_or_nonempty with he | ⟨k₁, hk₁⟩
      · rw [he, Finset.sum_empty]; exact zero_le
      have hnot : ∀ k ∈ Finset.univ \ V', k ∉ V ∧ ¬HitT σ t k := fun k hk => by
        have := (Finset.mem_sdiff.mp hk).2
        rw [hV', Finset.mem_union, not_or] at this
        exact ⟨this.1, fun h => this.2 ((hmemH k).mpr h)⟩
      obtain ⟨hk₁V, hk₁H⟩ := hnot k₁ hk₁
      set M := (fusedImpl prims (xk x σ k₁) top t).run p with hM
      have hstep : ∀ k ∈ Finset.univ \ V', (fusedImpl prims (xk x σ k) top t).run p = M := fun k hk =>
        fusedImpl_upd_eq prims x σ top (hinj k (hnot k hk).1) (hinj k₁ hk₁V) t p hrev (hnot k hk).2 hk₁H
      have hz : ∀ z ∈ support M, ∑ k ∈ Finset.univ \ V',
          Pr{let z' ← (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2}[σ ∈ z'.2.1.2] ≤
            (n' : ℝ≥0∞) := by
        intro z hzM
        obtain ⟨hzD, hzσ⟩ := fused_miss prims (xk x σ k₁) top σ t p hD hσ hrev
          (fun u hu hs => hk₁H ⟨u, hu, (hitT_iff x σ k₁ u).mp hs⟩) z hzM
        exact ih z.1 n' V' z.2 (fun k hk => hinj k fun h => hk (hV' ▸ Finset.mem_union_left _ h)) hzD hzσ
          (hn' ▸ hq.2 z.1)
      calc ∑ k ∈ Finset.univ \ V', (∑' z, Pr{let y ← (fusedImpl prims (xk x σ k) top t).run p}[y = z] *
            Pr{let z' ← (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2}[σ ∈ z'.2.1.2])
          = ∑ k ∈ Finset.univ \ V', (∑' z, Pr{let y ← M}[y = z] *
            Pr{let z' ← (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2}[σ ∈ z'.2.1.2]) :=
            Finset.sum_congr rfl fun k hk => by rw [hstep k hk]
        _ = ∑' z, Pr{let y ← M}[y = z] * ∑ k ∈ Finset.univ \ V',
            Pr{let z' ← (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2}[σ ∈ z'.2.1.2] := by
            rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
            exact tsum_congr fun z => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑' z, Pr{let y ← M}[y = z] * (n' : ℝ≥0∞) := tsum_le_tsum fun z => by
            by_cases hzM : z ∈ support M
            · exact mul_le_mul_right (hz z hzM) _
            · simp [prEvent_eq_zero_of_not_mem_support _ hzM]
        _ ≤ (n' : ℝ≥0∞) := by
            rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
    refine (add_le_add hhit hrest).trans ?_
    exact_mod_cast hbud

set_option linter.constructorNameAsVariable false in
/-- After each top tree of the dealer, the first hits of `σ` over its good values cost at most the own
budget `q`. -/
theorem rest_sum_le_own (A : TsigAdversary C) (q : ℕ) (hown : HasSigningOwnBound A q) (x : Keys3 C)
    (σ : KeySlot C) (V : Finset HashOutput) (hV : ∀ u ∉ V, Function.Injective (slotInput (xk x σ u).2.1 (xk x σ u).2.2))
    (os : Option TreeOutput × WState C) :
    ∑ u ∈ Finset.univ \ V, Pr{let w ← restOf prims A (xk x σ u) os}[σ ∈ w.1.2] ≤ (q : ℝ≥0∞) := by
  rcases os with ⟨_ | (top | tree), s⟩
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun u _ => ?_) zero_le
    simp [restOf]
  · calc ∑ u ∈ Finset.univ \ V, Pr{let w ← restOf prims A (xk x σ u) (some (.top top), s)}[σ ∈ w.1.2]
        ≤ ∑ u ∈ Finset.univ \ V, Pr{let z ←
            (simulateQ (fusedImpl prims (xk x σ u) top) (A ⟨top.root, x.1⟩ top)).run (((tsigInit, false), ∅), s)}[σ ∈ z.2.1.2] :=
          Finset.sum_le_sum fun u _ => probEvent_bind_le_of_imp _ _ _ _ fun z _ w hw hσ => by
            rw [support_map] at hw
            obtain ⟨v, -, rfl⟩ := hw
            exact hσ
      _ ≤ (q : ℝ≥0∞) := sum_ff_le_own prims x σ top (A ⟨top.root, x.1⟩ top) q V (((tsigInit, false), ∅), s) hV
          (not_revealed_empty σ) (Finset.notMem_empty σ) (hown _ _)
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun u _ => ?_) zero_le
    simp [restOf]

/-- Over all values of the key `σ`, its first hits with distinct keys cost at most the own budget `q`. -/
theorem core_sum_own (A : TsigAdversary C) (q : ℕ) (hown : HasSigningOwnBound A q) (x : Keys3 C)
    (σ : KeySlot C) :
    ∑ u : HashOutput, Pr{let z ←
      (fun r => (xk x σ u, r)) <$> runSigningWorld prims (ffAfter A (xk x σ u))}[¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2] ≤ (q : ℝ≥0∞) := by
  classical
  obtain ⟨V, hVdef⟩ : ∃ V : Finset HashOutput, V = Finset.univ.filter fun u =>
      KeyCollision (xk x σ u).2.1 (xk x σ u).2.2 := ⟨_, rfl⟩
  have hV : ∀ u ∉ V, Function.Injective (slotInput (xk x σ u).2.1 (xk x σ u).2.2) := fun u hu => by
    have h : ¬KeyCollision (xk x σ u).2.1 (xk x σ u).2.2 := fun h => hu (by rw [hVdef]; simpa using h)
    simp only [KeyCollision, not_or, not_not] at h
    exact slotInput_injective h.1 h.2
  have hterm : ∀ u, Pr{let z ←
      (fun r => (xk x σ u, r)) <$> runSigningWorld prims (ffAfter A (xk x σ u))}[¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2] =
        if u ∈ V then 0 else Pr{let w ← dealerSlot (C := C) x.1 >>= restOf prims A (xk x σ u)}[σ ∈ w.1.2] := by
    intro u
    rw [prEvent_map]
    split_ifs with hu
    · refine prEvent_eq_zero_of_forall_mem_support _ _ fun r _ h => h.1 ?_
      rw [hVdef] at hu
      simpa using hu
    · have hc : ¬KeyCollision (xk x σ u).2.1 (xk x σ u).2.2 := fun h => hu (by rw [hVdef]; simpa using h)
      simp only [hc, not_false_eq_true, true_and]
      rw [runSigningWorld_eq_split prims _ _ (hV u hu), prEvent_map, split_ffAfter prims A _ (hV u hu)]
      rfl
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, ← Finset.sdiff_eq_filter]
  simp only [OracleComp.prEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
  calc ∑' os, ∑ u ∈ Finset.univ \ V, Pr{let z ← dealerSlot (C := C) x.1}[z = os] *
        Pr{let w ← restOf prims A (xk x σ u) os}[σ ∈ w.1.2]
      = ∑' os, Pr{let z ← dealerSlot (C := C) x.1}[z = os] *
          ∑ u ∈ Finset.univ \ V, Pr{let w ← restOf prims A (xk x σ u) os}[σ ∈ w.1.2] :=
        tsum_congr fun os => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑' os, Pr{let z ← dealerSlot (C := C) x.1}[z = os] * (q : ℝ≥0∞) :=
        tsum_le_tsum fun os => mul_le_mul_right (rest_sum_le_own prims A q hown x σ V hV os) _
    _ ≤ (q : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

/-- Each key is the first hit with probability at most `q / 2^256` when the keys are distinct. -/
theorem keyHitOwn (A : TsigAdversary C) (q : ℕ) (hown : HasSigningOwnBound A q) (σ : KeySlot C) :
    Pr{let z ← ffRun prims A}[¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
  have e : ffRun prims A = (do
      let P ← $ᵗ PublicParameter
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pk ← $ᵗ (C.Pair → HashOutput)
      (fun r => ((P, seeds, pk), r)) <$> runSigningWorld prims (ffAfter A (P, seeds, pk))) := by
    rw [bind_keyGen3]
    rfl
  rw [e, ← card_hashOutput]
  rcases σ with T | p
  · refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun P _ => ?_
    refine probEvent_resample T _ _ _ fun g => sum_tsum_bind_le _ _ _ fun pk => ?_
    exact core_sum_own prims A q hown (P, g, pk) (.inl T)
  · refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun P _ => prEvent_bind_le_of_forall_le_of_support _ _ _ fun seeds _ => ?_
    refine probEvent_resample p _ _ _ fun g => ?_
    exact core_sum_own prims A q hown (P, seeds, g) (.inr p)

set_option maxRecDepth 100000 in
/-- For distinct keys, the flag has probability at most `card (KeySlot C) · q / 2^256`. -/
theorem distinctFlagOwn : SigningOwnClaim.DistinctFlagOwn prims C := by
  intro A q hown
  rw [flaggedRun_eq_ffRun, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ fun z hz hf => ?_).trans ((prEvent_exists_finset_le Finset.univ _
    (fun σ z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2)).trans ?_)
  · simp only at hf
    unfold ffRun at hz
    simp only [mem_support_bind_iff, support_map, Set.mem_image] at hz
    obtain ⟨x, -, r, hr, rfl⟩ := hz
    have h1 : r.1 ∈ support (ffAfter A x) := support_runSigningWorld prims _ r hr
    have h2 : r.1.1.2 = true := hf.2
    obtain ⟨σ, hσ⟩ := ffAfter_support A x r.1 h1 h2
    exact ⟨σ, Finset.mem_univ _, hf.1, hσ⟩
  · refine (Finset.sum_le_sum fun σ _ => keyHitOwn prims A q hown σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, mul_div_assoc]

end ThresholdLeanXmssSecurity.SeedHitOwn

/-- info: 'ThresholdLeanXmssSecurity.SeedHitOwn.sum_ff_le_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SeedHitOwn.sum_ff_le_own

/-- info: 'ThresholdLeanXmssSecurity.SeedHitOwn.distinctFlagOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SeedHitOwn.distinctFlagOwn
