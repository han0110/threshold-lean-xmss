import ThresholdLeanXmssSecurity.Proof.TreeSaltPairs
import ThresholdLeanXmssSecurity.Proof.TreeEvents3

/-!
# The pair bounds of the two-stage salt table with the guess guard

`TreeSaltStagesPairs` (`TreeSaltPairs.lean`) asks for each pair of the table a bound outside the
budget collision only. Review P3 shows that this does not pay for the pair of a hidden stage-1
salt and a known stage-2 salt. This module adds two guards to the pair event, at no cost.

* The union `treeSimHash_union_guess` gives the reuse term also outside `TreeSimSaltGuess`. The
  guess is the second term of the union, so the three terms do not change.
* The union over the table pairs `treeSaltStages_reuse_le_least` charges a reuse to the least
  reuse pair, ordered by the larger index. So the pair event also states that no pair with a
  smaller larger index reuses a salt.
* `TreeSaltStagesPairsGuarded` is `TreeSaltStagesPairs` with the two guards.
  `treeSaltStagesPairsGuarded_of_pairs` shows that it is weaker.
* `treeSimulationHop_of_pairsGuarded` gives the hop with the sum and the arithmetic of
  `treeSimHashBoundGoal3_of_guarded`.

## The hidden stage-1 salt and the known stage-2 salt

Let `S` be the hidden salt of entry `i < n₁`, and let entry `j ≥ n₁` be known. On paper, the
guards give that the stage-2 table and the known salt at `j` are independent of `S`.

* The salt goes only into `.digest S h` (`compareDigests`, `Scheme.lean`). It is not recorded in a
  history. The pair streams of `randBits 256` are not used.
* The real game runs on `LocalSpec + LocalSpec` (`treeSim_localReal_eq`), so no one programs `H`.
  The stream queries of the adversary use AES, not the hidden cache.
* Outside `TreeSimSaltGuess`, no counted query has the input `.digest S h`. Outside the budget
  collision, two honest digests are equal only for equal histories.
* A known salt is AES under `H(.streamKey k)` at the label `ρ`. The setup fixes the key `k`. The
  label is an honest counter.
* A stage-1 known salt equal to `S` at a holder with an equal history hash gives two equal
  published digests, and so tells `S` to the adversary with no counted query. The least pair guard
  excludes it, because its larger index is below `n₁ ≤ j`.

The bound is a coupling. In a run where the honest digests of the term are fresh values of `H`,
the view and the address of entry `j` do not depend on `S`, so they match with probability
`2^-256`. That run has the real view on the guard event. A counted `.digest v h` with `v ≠ S`
removes one candidate, so `S` is not uniform given the real view. Only the coupled bound holds.

The proof in Lean needs a program-level fact of the whole ceremony, namely that the salt reaches
only `.digest` queries. This is a representation of the kind of
`TreeRawSaltCeremonyRepresentation` (`TreeRawSalt.lean`). An oracle-level potential cannot
give it. A program can read `S`, then read a known stream at the label `ρ` whose bits are `S`,
under an `aes` with `aes.eval k (ρ, 2, g) = ρ.testBit g`. It makes no counted query and no
collision, and its pair reuses with probability 1. Thus `TreeSaltStagesPairsGuarded` requires an additional coupling certificate.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable {prims : Primitives} {K : Constants C E} {circuits : Circuits} {settings : Settings}

/-- The pair `i < j` reuses a salt, and no pair with a larger index below `j` reuses a salt. -/
def TreeSaltLeastPairReuse (D : C.Coalition) {n : ℕ} (addr : Fin n → C.Term × HashOutput × ℕ)
    (i j : ℕ) (log : TreeSimLog C) : Prop :=
  (∀ i' j' : ℕ, i' < j' → j' < j → ¬ TreeSaltPairReuse D addr i' j' log) ∧
    TreeSaltPairReuse D addr i j log

/-- `TreeSaltStagesPairs` outside the salt guess, and for the least reuse pair. -/
def TreeSaltStagesPairsGuarded (splits : TreeSaltStageSplits prims K circuits settings) : Prop :=
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
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧ ¬ TreeSimSaltGuess D r.2.2 ∧
            TreeSaltLeastPairReuse D (Fin.append addr₁ (addr₂ r.1)) i j r.2.2 |
          (splits top tree D A x Z p).paired] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

/-- The guarded pair bounds follow from the unguarded ones. -/
theorem treeSaltStagesPairsGuarded_of_pairs
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits) : TreeSaltStagesPairsGuarded splits := by
  intro hb top tree D A x z Z q hx hq hsmall p hp
  obtain ⟨n₁, addr₁, n₂, addr₂, hcover, hpair⟩ :=
    pairBounds hb top tree D A x z Z q hx hq hsmall p hp
  refine ⟨n₁, addr₁, n₂, addr₂, hcover, fun i j hij => le_trans (probEvent_mono ?_) (hpair i j hij)⟩
  rintro r - ⟨hnc, -, -, hr⟩
  exact ⟨hnc, hr⟩

/-- The union over the table pairs, charged to the least reuse pair. -/
theorem treeSaltStages_reuse_le_least {run : ProbComp (Bool × TreeSimLog C)}
    (split : TreeSaltStageSplit run) (D : C.Coalition) {N : ℕ} {n₁ : ℕ}
    {addr₁ : Fin n₁ → C.Term × HashOutput × ℕ} {n₂ : split.View → ℕ}
    {addr₂ : (m : split.View) → Fin (n₂ m) → C.Term × HashOutput × ℕ}
    (hcover : TreeSaltStagesCover split N n₁ addr₁ n₂ addr₂)
    (hpair : ∀ i j : ℕ, i < j →
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧ ¬ TreeSimSaltGuess D r.2.2 ∧
          TreeSaltLeastPairReuse D (Fin.append addr₁ (addr₂ r.1)) i j r.2.2 | split.paired] ≤
        (2 ^ 256 : ℝ≥0∞)⁻¹) :
    Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧
        TreeSimSaltReuse D r.2 | run] ≤ ((N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
  let pairs : Finset (Fin N × Fin N) := {x | x.1 < x.2}
  let event := fun (r : split.View × (Bool × TreeSimLog C)) (i j : ℕ) =>
    ¬ TreeSimHashBudgetCollision r.2.2 ∧ ¬ TreeSimSaltGuess D r.2.2 ∧
      TreeSaltLeastPairReuse D (Fin.append addr₁ (addr₂ r.1)) i j r.2.2
  rw [← split.snd_paired, probEvent_map]
  calc Pr[(fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧
        TreeSimSaltReuse D r.2) ∘ Prod.snd | split.paired]
      ≤ Pr[fun r => ∃ x ∈ pairs, event r x.1.val x.2.val | split.paired] := by
        apply probEvent_mono
        rintro ⟨m, r⟩ hr ⟨hnc, hng, salt, T, key, label, T', key', label', hlen, hT, hne, hbits⟩
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
        have hex : ∃ j, ∃ i < j, TreeSaltPairReuse D (Fin.append addr₁ (addr₂ m')) i j r'.2 := by
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
          · exact ⟨b, a, h, a.isLt, b.isLt, salt, hlen, Or.inl hha, hsa, hsb⟩
          · exact ⟨a, b, h, b.isLt, a.isLt, salt, hlen, Or.inr hha, hsb, hsa⟩
        obtain ⟨i, hij, hi, hj, hreuse⟩ := Nat.find_spec hex
        have hmin : ∀ i' j' : ℕ, i' < j' → j' < Nat.find hex →
            ¬ TreeSaltPairReuse D (Fin.append addr₁ (addr₂ m')) i' j' r'.2 :=
          fun i' j' h h' hr => Nat.find_min hex h' ⟨i', h, hr⟩
        refine ⟨(⟨i, by omega⟩, ⟨Nat.find hex, by omega⟩), by simp [pairs, hij], hnc, hng, hmin,
          hi, hj, hreuse⟩
    _ ≤ ∑ x ∈ pairs, Pr[fun r => event r x.1.val x.2.val | split.paired] :=
        probEvent_exists_finset_le_sum _ _ _
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

variable (prims K circuits settings) in
/-- `TreeSimSaltReuseGuarded` outside the salt guess. -/
def TreeSimSaltReuseGuessGuarded : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    (Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧
        TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ) / 2 ^ 257

/-- The guarded estimate from the guarded pair bounds of a two-stage table. -/
theorem treeSimSaltReuseGuessGuarded_of_pairs
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairsGuarded splits) :
    TreeSimSaltReuseGuessGuarded prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  have hle : Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧
      TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
    rw [treeSaltSetup_split]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    obtain ⟨n₁, addr₁, n₂, addr₂, hcover, hpair⟩ :=
      pairBounds hb top tree D A x z Z q hx hq hsmall p hp
    exact treeSaltStages_reuse_le_least (splits top tree D A x Z p) D hcover hpair
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hle).trans_eq ?_
  simp [ENNReal.toReal_div]

/-- The union of `treeSimHash_union3` with the reuse term outside the salt guess. The guess is the
second term, so the three terms do not change. -/
theorem treeSimHash_union_guess {α : Type} (D : C.Coalition) (p : ProbComp (α × TreeSimLog C)) :
    (Pr[fun r => TreeSimHashBad3 D r.2 | p]).toReal ≤
      (Pr[fun r => TreeSimHashBudgetCollision r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧
        TreeSimSaltReuse D r.2 | p]).toReal := by
  have h1 := probEvent_or_le p (fun r => TreeSimHashBudgetCollision r.2)
    (fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
  have h2 := probEvent_or_le p
    (fun r => TreeSimHashBudgetCollision r.2 ∨ (¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2))
    (fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧ TreeSimSaltReuse D r.2)
  have hle : Pr[fun r => TreeSimHashBad3 D r.2 | p] ≤
      Pr[fun r => TreeSimHashBudgetCollision r.2 | p] +
      Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p] +
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧
        TreeSimSaltReuse D r.2 | p] := by
    refine le_trans (probEvent_mono ?_) (h2.trans (add_le_add h1 le_rfl))
    intro r _ h
    by_cases hb : TreeSimHashBudgetCollision r.2
    · exact Or.inl (Or.inl hb)
    have hnc : ¬ TreeSimHashCollision r.2 := fun hc =>
      hb (treeSimHashBudgetCollision_of_collision _ hc)
    by_cases hg : TreeSimSaltGuess D r.2
    · exact Or.inl (Or.inr ⟨hnc, hg⟩)
    rcases (treeSimHashBad3_iff D r.2).mp h with hc | hc | hu
    · exact (hb hc).elim
    · exact (hg hc).elim
    · exact Or.inr ⟨hb, hg, hu⟩
  have hab := ENNReal.add_ne_top.mpr ⟨probEvent_ne_top (mx := p)
    (p := fun r => TreeSimHashBudgetCollision r.2), probEvent_ne_top (mx := p)
    (p := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)⟩
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hab, probEvent_ne_top⟩) hle
  rwa [ENNReal.toReal_add hab probEvent_ne_top,
    ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at h

variable (prims K circuits settings) in
/-- `treeSimHashBoundGoal3_of_guarded` with the reuse estimate outside the salt guess. The proof
and the arithmetic are the same, with `treeSimHash_union_guess` for `treeSimHash_union3`. -/
theorem treeSimHashBoundGoal3_of_guessGuarded
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuessGuarded prims K circuits settings) :
    TreeSimHashBoundGoal3 prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  let N := q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)
  by_cases hlarge : 2 ^ 128 ≤ N
  · apply le_trans _ (treeSimHash_unit_budget _ hlarge)
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (probEvent_le_one (mx := treeSimTrace prims K circuits settings
        (treeSimEvents3 prims K circuits settings) top tree D A x z Z) (p := fun r => r.2.1 = true))
  have hn : N < 2 ^ 128 := Nat.lt_of_not_ge hlarge
  have cert := treeSimHash_terminal_fresh prims K circuits settings top tree D A x z Z q hq hn
    (treeSimHash_terminal_of_honest prims K circuits settings honest hb top tree D A x z Z q hx hq hn)
  have h := treeSimHash_logged_budget_birthday prims D
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) N cert
  rw [treeSim_localReal_eq K circuits settings top tree D A x z Z] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow] at hreal
  have hc : (Pr[fun r => TreeSimHashBudgetCollision r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
        ((N ^ 2 : ℕ) : ℝ) / (2 * 2 ^ 256) := by
    refine hreal.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have hN : N * (N - 1) ≤ N ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_left N (Nat.sub_le N 1)
    exact_mod_cast hN
  rw [treeSimHash_flag3]
  refine (treeSimHash_union_guess D _).trans ((add_le_add (add_le_add hc
    (salt hb top tree D A x z Z q hx hq hsmall)) (reuse hb top tree D A x z Z q hx hq hsmall)).trans ?_)
  simp only [N, Nat.cast_pow, Nat.cast_add]
  apply treeSimHash_union2_arith _ _ _ _ (by positivity) (by positivity) (by positivity)
  have hs : 2 * ((treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) +
      2 * ((treeBatches settings tree * termCount C : ℕ) : ℝ) ≤
      ((treeSecrets circuits settings C tree - 2 * prssKeyCount C : ℕ) : ℝ) := by
    exact_mod_cast treeSimHash_reuse_capacity (C := C) circuits settings tree
  linarith

variable (prims K circuits settings) in
/-- The hop from the guarded pair bounds of a two-stage table, as `treeSimulationHop_of_pairs3`. -/
theorem treeSimulationHop_of_pairsGuarded
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairsGuarded splits)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHopClosed3 prims K circuits settings stages
    (treeSimHashBoundGoal3_of_guessGuarded prims K circuits settings honest salt
      (treeSimSaltReuseGuessGuarded_of_pairs splits pairBounds))
    (treeSimCheckBoundGoal3_of_setupBranches3 prims K circuits settings branches)

/-- info: 'ThresholdLeanXmssSecurity.treeSaltStagesPairsGuarded_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltStagesPairsGuarded_of_pairs

/-- info: 'ThresholdLeanXmssSecurity.treeSaltStages_reuse_le_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltStages_reuse_le_least

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_union_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_union_guess

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_pairsGuarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairsGuarded

end ThresholdLeanXmssSecurity
