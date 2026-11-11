import ThresholdLeanXmssSecurity.Proof.TreeSaltStages
import XmssSecurity.Scan.Frame

/-!
# The salt reuse as a union over address pairs

This module replaces the joint eager game of `TreeSaltStages.lean` with a union bound over the
pairs of the two-stage salt table.

* `saltPairWeight` is a potential for one pair of salts of 256 positions. Each side of a position
  is a lazy bit or a fixed bit. A position weighs `1` on a match, `0` on a mismatch and `1/2`
  while a side is open.
* `saltPairWeight_randomOracle` shows that one lazy random-oracle query on the bits keeps the
  expected weight. `saltPairWeight_keep` shows the same for a step that keeps the bits.
* `saltPair_probEvent_le` bounds the probability that the two salts end equal by the weight at
  the start. The weight is `2^-256` when each position has an open side (`saltPairWeight_of_open`).
  The proof uses `XmssSecurity.expectedFinal_le` of leanVM.
* `treeSimLogged_saltPair_le` applies it to `treeSimLoggedWorld` from any state.
* `treeSaltStages_reuse_le` is the union over the pairs `i < j` of the table. It needs no eager
  game. `treeSimSaltReuseGuarded_of_pairs` and `treeSimulationHop_of_pairs` give the guarded
  estimate and the hop from `TreeSaltStagesPairs`.

`TreeSaltStagesPairs` stays open. It contains `TreeSaltStagesAddresses`, because its table is a
witness. On paper the potential pays for a pair when each position has an open side at the start
of the pair, and the known salt of the pair is fixed there. The bridge to the split needs the
state at the stage point and the agreement of the log with the hidden cache. A known salt is not a lazy bit. `streamWorld` answers it with `prims.aes` under the key
from `.streamKey`. So the potential does not pay for a pair of a hidden stage-1 salt and a known
stage-2 salt. The stage point fixes the label of the known salt after the hidden salt exists.
This pair needs the fact that the stage-2 labels do not depend on the hidden stage-1 salts, as
`TreeSaltStages.lean` also states.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section LazyBits

variable {Dom : Type} [DecidableEq Dom]

/-- The value of one side of a salt position. A side is a lazy bit `.inl d` or a fixed bit
`.inr b`. -/
def saltSideValue (cache : (Dom →ₒ Bit).QueryCache) : Dom ⊕ Bit → Option Bit
  | .inl d => cache d
  | .inr b => some b

/-- The weight of one position. It is `1` on a match, `0` on a mismatch, and `1/2` while a side
is open. -/
def saltPositionWeight : Option Bit → Option Bit → ℝ≥0∞
  | some a, some b => if a = b then 1 else 0
  | _, _ => 2⁻¹

/-- The potential of a pair of salts `u` and `v` of 256 positions. -/
def saltPairWeight (u v : Fin 256 → Dom ⊕ Bit) (cache : (Dom →ₒ Bit).QueryCache) : ℝ≥0∞ :=
  ∏ g, saltPositionWeight (saltSideValue cache (u g)) (saltSideValue cache (v g))

/-- The two salts are set and equal at each position. -/
def SaltPairEqual (u v : Fin 256 → Dom ⊕ Bit) (cache : (Dom →ₒ Bit).QueryCache) : Prop :=
  ∀ g, ∃ b, saltSideValue cache (u g) = some b ∧ saltSideValue cache (v g) = some b

/-- Each lazy point occurs at most once among the 512 sides. -/
def SaltPairDistinct (u v : Fin 256 → Dom ⊕ Bit) : Prop :=
  ∀ (x y : Fin 256 ⊕ Fin 256) (d : Dom), Sum.elim u v x = .inl d → Sum.elim u v y = .inl d → x = y

theorem saltSideValue_cacheQuery (cache : (Dom →ₒ Bit).QueryCache) (d : Dom) (b : Bit)
    (s : Dom ⊕ Bit) :
    saltSideValue (cache.cacheQuery d b) s =
      if s = .inl d then some b else saltSideValue cache s := by
  rcases s with e | a
  · by_cases h : e = d
    · subst h; simp [saltSideValue]
    · simp [saltSideValue, QueryCache.cacheQuery, h]
  · simp [saltSideValue]

theorem saltPositionWeight_open (x : Option Bit) :
    saltPositionWeight none x = 2⁻¹ ∧ saltPositionWeight x none = 2⁻¹ := by
  rcases x with _ | a <;> simp [saltPositionWeight]

theorem saltPositionWeight_draw (x : Option Bit) :
    saltPositionWeight (some 0) x + saltPositionWeight (some 1) x = 1 ∧
      saltPositionWeight x (some 0) + saltPositionWeight x (some 1) = 1 := by
  rcases x with _ | a
  · simp [saltPositionWeight, ENNReal.inv_two_add_inv_two]
  · have h10 : (1 : Bit) ≠ 0 := by decide
    obtain rfl | rfl : a = 0 ∨ a = 1 := by revert a; decide
    all_goals simp [saltPositionWeight, h10, h10.symm]

/-- A fresh uniform bit at an open lazy point keeps the expected pair weight. -/
theorem saltPairWeight_draw {u v : Fin 256 → Dom ⊕ Bit} (hd : SaltPairDistinct u v)
    {cache : (Dom →ₒ Bit).QueryCache} {d : Dom} (hc : cache d = none) :
    2⁻¹ * saltPairWeight u v (cache.cacheQuery d 0) +
      2⁻¹ * saltPairWeight u v (cache.cacheQuery d 1) = saltPairWeight u v cache := by
  by_cases hg : ∃ g, u g = .inl d ∨ v g = .inl d
  · obtain ⟨g, hg⟩ := hg
    have hrest : ∀ g' ≠ g, u g' ≠ .inl d ∧ v g' ≠ .inl d := by
      intro g' hne
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> rcases hg with hg | hg
      · exact hne (Sum.inl_injective (hd (.inl g') (.inl g) d h hg))
      · exact absurd (hd (.inl g') (.inr g) d h hg) (by simp)
      · exact absurd (hd (.inr g') (.inl g) d h hg) (by simp)
      · exact hne (Sum.inr_injective (hd (.inr g') (.inr g) d h hg))
    have hprod : ∀ b : Bit, ∏ g' ∈ {g}ᶜ, saltPositionWeight
        (saltSideValue (cache.cacheQuery d b) (u g')) (saltSideValue (cache.cacheQuery d b) (v g')) =
        ∏ g' ∈ {g}ᶜ, saltPositionWeight (saltSideValue cache (u g')) (saltSideValue cache (v g')) := by
      intro b
      refine Finset.prod_congr rfl fun g' hg' => ?_
      have hne := hrest g' (by simpa using hg')
      simp only [saltSideValue_cacheQuery, if_neg hne.1, if_neg hne.2]
    simp only [saltPairWeight]
    rw [Fintype.prod_eq_mul_prod_compl g, Fintype.prod_eq_mul_prod_compl g,
      Fintype.prod_eq_mul_prod_compl g, hprod 0, hprod 1]
    rcases hg with hu | hv
    · have hv : v g ≠ .inl d := fun h => absurd (hd (.inl g) (.inr g) d hu h) (by simp)
      have hs : ∀ b : Bit, saltSideValue (cache.cacheQuery d b) (u g) = some b := fun b => by
        rw [saltSideValue_cacheQuery, if_pos hu]
      have ht : ∀ b : Bit, saltSideValue (cache.cacheQuery d b) (v g) = saltSideValue cache (v g) :=
        fun b => by rw [saltSideValue_cacheQuery, if_neg hv]
      have ho : saltSideValue cache (u g) = none := by rw [hu]; exact hc
      rw [hs, hs, ht, ht, ho, (saltPositionWeight_open _).1, ← mul_assoc, ← mul_assoc, ← add_mul,
        ← mul_add, (saltPositionWeight_draw _).1, mul_one]
    · have hu : u g ≠ .inl d := fun h => absurd (hd (.inl g) (.inr g) d h hv) (by simp)
      have hs : ∀ b : Bit, saltSideValue (cache.cacheQuery d b) (v g) = some b := fun b => by
        rw [saltSideValue_cacheQuery, if_pos hv]
      have ht : ∀ b : Bit, saltSideValue (cache.cacheQuery d b) (u g) = saltSideValue cache (u g) :=
        fun b => by rw [saltSideValue_cacheQuery, if_neg hu]
      have ho : saltSideValue cache (v g) = none := by rw [hv]; exact hc
      rw [hs, hs, ht, ht, ho, (saltPositionWeight_open _).2, ← mul_assoc, ← mul_assoc, ← add_mul,
        ← mul_add, (saltPositionWeight_draw _).2, mul_one]
  · push Not at hg
    have heq : ∀ b : Bit, saltPairWeight u v (cache.cacheQuery d b) = saltPairWeight u v cache := by
      intro b
      refine Finset.prod_congr rfl fun g _ => ?_
      simp only [saltSideValue_cacheQuery, if_neg (hg g).1, if_neg (hg g).2]
    rw [heq, heq, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- One lazy random-oracle query on the bits keeps the expected pair weight. -/
theorem saltPairWeight_randomOracle {u v : Fin 256 → Dom ⊕ Bit} (hd : SaltPairDistinct u v)
    (d : Dom) (cache : (Dom →ₒ Bit).QueryCache) :
    ∑' r, Pr[= r | ((Dom →ₒ Bit).randomOracle d).run cache] * saltPairWeight u v r.2 ≤
      saltPairWeight u v cache := by
  cases hc : cache d with
  | some b =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, tsum_probOutput_pure_mul]
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, tsum_probOutput_map_mul]
    rw [tsum_fintype]
    have hp : ∀ x : Bit, Pr[= x | uniformSampleImpl (spec := (Dom →ₒ Bit)) d] = 2⁻¹ := by
      intro x
      simp [uniformSampleImpl, probOutput_uniformSample]
    simp only [hp]
    rw [← saltPairWeight_draw hd hc]
    exact le_of_eq (Fin.sum_univ_two _)

theorem saltPairWeight_of_equal {u v : Fin 256 → Dom ⊕ Bit} {cache : (Dom →ₒ Bit).QueryCache}
    (h : SaltPairEqual u v cache) : 1 ≤ saltPairWeight u v cache := by
  refine le_of_eq (Finset.prod_eq_one fun g _ => ?_).symm
  obtain ⟨b, hu, hv⟩ := h g
  simp [hu, hv, saltPositionWeight]

/-- A pair with an open side at each position has weight `2^-256`. -/
theorem saltPairWeight_of_open {u v : Fin 256 → Dom ⊕ Bit} {cache : (Dom →ₒ Bit).QueryCache}
    (h : ∀ g, saltSideValue cache (u g) = none ∨ saltSideValue cache (v g) = none) :
    saltPairWeight u v cache = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hg : ∀ g, saltPositionWeight (saltSideValue cache (u g)) (saltSideValue cache (v g)) = 2⁻¹ :=
    fun g => by
      rcases h g with h | h
      · rw [h, (saltPositionWeight_open _).1]
      · rw [h, (saltPositionWeight_open _).2]
  simp only [saltPairWeight, hg, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.inv_pow]

/-- A step that keeps the lazy bits keeps the expected pair weight. -/
theorem saltPairWeight_keep {σ β : Type} (step : ProbComp (β × σ))
    (hidden : σ → (Dom →ₒ Bit).QueryCache) (u v : Fin 256 → Dom ⊕ Bit) (s : σ)
    (hkeep : ∀ r ∈ support step, hidden r.2 = hidden s) :
    ∑' r, Pr[= r | step] * saltPairWeight u v (hidden r.2) ≤ saltPairWeight u v (hidden s) := by
  calc ∑' r, Pr[= r | step] * saltPairWeight u v (hidden r.2)
      = ∑' r, Pr[= r | step] * saltPairWeight u v (hidden s) := by
        refine tsum_congr fun r => ?_
        by_cases hr : r ∈ support step
        · rw [hkeep r hr]
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ = (∑' r, Pr[= r | step]) * saltPairWeight u v (hidden s) := ENNReal.tsum_mul_right
    _ ≤ saltPairWeight u v (hidden s) := mul_le_of_le_one_left (zero_le) tsum_probOutput_le_one

/-- The pair bound on any handler whose steps keep the expected pair weight. Each step either
keeps the lazy bits or is one lazy random-oracle query on them (`saltPairWeight_keep` and
`saltPairWeight_randomOracle`). -/
theorem saltPair_probEvent_le {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (hidden : σ → (Dom →ₒ Bit).QueryCache)
    (u v : Fin 256 → Dom ⊕ Bit)
    (hstep : ∀ t s, ∑' r, Pr[= r | (impl t).run s] * saltPairWeight u v (hidden r.2) ≤
      saltPairWeight u v (hidden s))
    (oa : OracleComp spec α) (s : σ) :
    Pr[fun r => SaltPairEqual u v (hidden r.2) | (simulateQ impl oa).run s] ≤
      saltPairWeight u v (hidden s) := by
  refine (XmssSecurity.probEvent_le_expectedFinal impl (fun s => saltPairWeight u v (hidden s))
    (fun s => SaltPairEqual u v (hidden s)) (fun _ h => saltPairWeight_of_equal h) oa s).trans ?_
  have h := XmssSecurity.expectedFinal_le impl (Inv := fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun s => saltPairWeight u v (hidden s)) (fun _ _ => 0)
    (fun t s _ => by simpa only [add_zero] using hstep t s) oa s trivial
  have hz : XmssSecurity.expectedSimulatedCost impl (fun _ _ => 0) oa s = 0 := by
    simpa using XmssSecurity.expectedSimulatedCost_const_mul impl 0 (fun _ _ => 0) oa s
  rwa [hz, add_zero] at h

end LazyBits

section Pairs

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable {prims : Primitives} {K : Constants C E} {circuits : Circuits} {settings : Settings}

/-- The 256 honest index-2 bits of the address `a` in `log` are `salt`. -/
def TreeSaltAt (log : TreeSimLog C) (a : C.Term × HashOutput × ℕ) (salt : List Bit) : Prop :=
  ∀ g : Fin 256,
    (⟨.inr (.inr (.inr (.term a.1, a.2.1, a.2.2, 2, g.val))), salt.getD g.val 0⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log

/-- The table entries `i` and `j` exist, one of them is hidden, and the two read the same salt. -/
def TreeSaltPairReuse (D : C.Coalition) {n : ℕ} (addr : Fin n → C.Term × HashOutput × ℕ)
    (i j : ℕ) (log : TreeSimLog C) : Prop :=
  ∃ (hi : i < n) (hj : j < n) (salt : List Bit), salt.length = 256 ∧
    (¬ KnownTo D.1 (addr ⟨i, hi⟩).1 ∨ ¬ KnownTo D.1 (addr ⟨j, hj⟩).1) ∧
    TreeSaltAt log (addr ⟨i, hi⟩) salt ∧ TreeSaltAt log (addr ⟨j, hj⟩) salt

/-- The run of a split that also returns its stage point. -/
def TreeSaltStageSplit.paired {run : ProbComp (Bool × TreeSimLog C)} (split : TreeSaltStageSplit run) :
    ProbComp (split.View × (Bool × TreeSimLog C)) :=
  split.first >>= fun m => (fun r => (m, r)) <$> split.rest m

theorem TreeSaltStageSplit.snd_paired {run : ProbComp (Bool × TreeSimLog C)}
    (split : TreeSaltStageSplit run) : Prod.snd <$> split.paired = run := by
  simp [TreeSaltStageSplit.paired, split.split, map_bind, Functor.map_map]

/-- `onHash` keeps the hidden cache. -/
theorem onHash_hidden {α : Type} (m : StateT (HashCache C) ProbComp α)
    (s : HashCache C × HiddenCache C) : ∀ r ∈ support ((onHash m).run s), r.2.2 = s.2 := by
  intro r hr
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', -, rfl⟩ := hr
  rfl

/-- Each query of `streamWorld` keeps the expected pair weight on the hidden cache. -/
theorem streamWorld_saltPairStep (D : C.Coalition)
    {u v : Fin 256 → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) ⊕ Bit} (hd : SaltPairDistinct u v)
    (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C) :
    ∑' r, Pr[= r | (streamWorld prims D t).run s] * saltPairWeight u v r.2.2 ≤
      saltPairWeight u v s.2 := by
  rcases t with t | (t | t | x)
  · exact saltPairWeight_keep _ Prod.snd u v s (onHash_hidden _ s)
  · exact saltPairWeight_keep _ Prod.snd u v s (onHash_hidden _ s)
  · exact saltPairWeight_keep _ Prod.snd u v s (onHash_hidden _ s)
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk]
      rw [tsum_probOutput_map_mul]
      exact saltPairWeight_randomOracle hd _ s.2
    · simp only [streamWorld, if_neg hx]
      exact saltPairWeight_keep _ Prod.snd u v s (onHash_hidden _ s)

/-- Each query of the logged world keeps the expected pair weight on the hidden cache. -/
theorem treeSimLoggedWorld_saltPairStep (D : C.Coalition)
    {u v : Fin 256 → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) ⊕ Bit} (hd : SaltPairDistinct u v)
    (t : (WorldSpec C).Domain) (s : TreeSimState C) :
    ∑' r, Pr[= r | (treeSimLoggedWorld prims D t).run s] * saltPairWeight u v r.2.1.2 ≤
      saltPairWeight u v s.1.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk]
  rw [tsum_probOutput_map_mul]
  exact streamWorld_saltPairStep D hd t s.1

/-- The pair bound on the logged world from any state. -/
theorem treeSimLogged_saltPair_le (D : C.Coalition)
    {u v : Fin 256 → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) ⊕ Bit} (hd : SaltPairDistinct u v)
    {α : Type} (oa : OracleComp (WorldSpec C) α) (s : TreeSimState C) :
    Pr[fun r => SaltPairEqual u v r.2.1.2 | (simulateQ (treeSimLoggedWorld prims D) oa).run s] ≤
      saltPairWeight u v s.1.2 :=
  saltPair_probEvent_le (treeSimLoggedWorld prims D) (fun s => s.1.2) u v
    (fun t s => treeSimLoggedWorld_saltPairStep D hd t s) oa s

/-- After the PRSS setup, a two-stage table covers the salts, and each pair `i < j` of its
entries reuses a salt with probability at most `2^-256`. The table is a witness, because a table
that orders its stage-2 entries by the salts can put a reuse into one fixed pair. -/
def TreeSaltStagesPairs (splits : TreeSaltStageSplits prims K circuits settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSaltSetup prims D A x z),
    ∃ (n₁ : ℕ) (addr₁ : Fin n₁ → C.Term × HashOutput × ℕ)
      (n₂ : (splits top tree D A x Z p).View → ℕ)
      (addr₂ : (m : (splits top tree D A x Z p).View) → Fin (n₂ m) → C.Term × HashOutput × ℕ),
      TreeSaltStagesCover (splits top tree D A x Z p) (treeBatches settings tree * termCount C)
        n₁ addr₁ n₂ addr₂ ∧
      ∀ i j : ℕ, i < j →
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧
            TreeSaltPairReuse D (Fin.append addr₁ (addr₂ r.1)) i j r.2.2 |
          (splits top tree D A x Z p).paired] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

/-- The union over table pairs. A salt reuse with no budget collision is a reuse of one pair
`i < j` of the two-stage table. -/
theorem treeSaltStages_reuse_le {run : ProbComp (Bool × TreeSimLog C)}
    (split : TreeSaltStageSplit run) (D : C.Coalition) {N : ℕ} {n₁ : ℕ}
    {addr₁ : Fin n₁ → C.Term × HashOutput × ℕ} {n₂ : split.View → ℕ}
    {addr₂ : (m : split.View) → Fin (n₂ m) → C.Term × HashOutput × ℕ}
    (hcover : TreeSaltStagesCover split N n₁ addr₁ n₂ addr₂)
    (hpair : ∀ i j : ℕ, i < j →
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧
          TreeSaltPairReuse D (Fin.append addr₁ (addr₂ r.1)) i j r.2.2 | split.paired] ≤
        (2 ^ 256 : ℝ≥0∞)⁻¹) :
    Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 | run] ≤
      ((N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
  let pairs : Finset (Fin N × Fin N) := {x | x.1 < x.2}
  rw [← split.snd_paired, probEvent_map]
  calc Pr[(fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2) ∘ Prod.snd |
        split.paired]
      ≤ Pr[fun r => ∃ x ∈ pairs, ¬ TreeSimHashBudgetCollision r.2.2 ∧
          TreeSaltPairReuse D (Fin.append addr₁ (addr₂ r.1)) x.1.val x.2.val r.2.2 |
          split.paired] := by
        apply probEvent_mono
        rintro ⟨m, r⟩ hr ⟨hnc, salt, T, key, label, T', key', label', hlen, hT, hne, hbits⟩
        simp only [TreeSaltStageSplit.paired, support_bind, support_map, Set.mem_iUnion,
          Set.mem_image, Prod.mk.injEq, exists_prop] at hr
        obtain ⟨m', hm, r', hr', rfl, rfl⟩ := hr
        obtain ⟨-, -, hn, hc⟩ := hcover m' hm
        have hc := hc r' hr' hnc
        obtain ⟨a, ha⟩ := hc T key label 0 _ (hbits ⟨0, by norm_num⟩).1
        obtain ⟨b, hb⟩ := hc T' key' label' 0 _ (hbits ⟨0, by norm_num⟩).2
        have hab : a ≠ b := fun h => hne (by rw [← ha, ← hb, h])
        have hsa : TreeSaltAt r'.2 (Fin.append addr₁ (addr₂ m') a) salt := by
          rw [ha]; exact fun g => (hbits g).1
        have hsb : TreeSaltAt r'.2 (Fin.append addr₁ (addr₂ m') b) salt := by
          rw [hb]; exact fun g => (hbits g).2
        have hha : ¬ KnownTo D.1 (Fin.append addr₁ (addr₂ m') a).1 := by rw [ha]; exact hT
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
        · refine ⟨(⟨a, by omega⟩, ⟨b, by omega⟩), by simp [pairs, h], hnc, a.isLt, b.isLt, salt,
            hlen, Or.inl hha, hsa, hsb⟩
        · refine ⟨(⟨b, by omega⟩, ⟨a, by omega⟩), by simp [pairs, h], hnc, b.isLt, a.isLt, salt,
            hlen, Or.inr hha, hsb, hsa⟩
    _ ≤ ∑ x ∈ pairs, Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧
          TreeSaltPairReuse D (Fin.append addr₁ (addr₂ r.1)) x.1.val x.2.val r.2.2 |
          split.paired] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _x ∈ pairs, (2 ^ 256 : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun x hx => hpair _ _ (by simpa [pairs] using hx)
    _ ≤ ((N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hN : 2 * pairs.card ≤ N ^ 2 := treeSaltPairs_card N
        rw [ENNReal.le_div_iff_mul_le (by simp) (by simp),
          show (2 : ℝ≥0∞) ^ 257 = 2 * 2 ^ 256 from pow_succ' 2 256, ← mul_assoc,
          mul_comm _ (2 : ℝ≥0∞), mul_assoc, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
          mul_one]
        exact_mod_cast hN

/-- The guarded estimate from the pair bounds of a two-stage table. -/
theorem treeSimSaltReuseGuarded_of_pairs
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits) :
    TreeSimSaltReuseGuarded prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  have hle : Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
    rw [treeSaltSetup_split]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    obtain ⟨n₁, addr₁, n₂, addr₂, hcover, hpair⟩ := pairBounds hb top tree D A x z Z q hx hq hsmall p hp
    exact treeSaltStages_reuse_le (splits top tree D A x Z p) D hcover hpair
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hle).trans_eq ?_
  simp [ENNReal.toReal_div]

/-- The full hop from the old check goal, the two hash estimates and the pair bounds of a two-stage
table. -/
theorem treeSimulationHop_of_pairs
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits) (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_guarded prims K circuits settings stages honest salt
    (treeSimSaltReuseGuarded_of_pairs splits pairBounds) checkBound

end Pairs

/-- info: 'ThresholdLeanXmssSecurity.saltPair_probEvent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saltPair_probEvent_le

/-- info: 'ThresholdLeanXmssSecurity.saltPairWeight_randomOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saltPairWeight_randomOracle

/-- info: 'ThresholdLeanXmssSecurity.treeSaltStages_reuse_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltStages_reuse_le

/-- info: 'ThresholdLeanXmssSecurity.treeSimSaltReuseGuarded_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimSaltReuseGuarded_of_pairs

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairs

/-- info: 'ThresholdLeanXmssSecurity.treeSimLogged_saltPair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimLogged_saltPair_le

end ThresholdLeanXmssSecurity
