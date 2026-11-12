import ThresholdLeanXmssSecurity.Proof.TreeEvents

/-!
# The salt reuse estimate of the tree simulation hop

This module bounds `TreeSimSaltReuseEstimate` of `TreeEvents.lean` with an eager model.

* The eager model has `n` addresses. A hidden address reads a uniform 256-bit table entry, and a
  known address has a fixed salt.
* `treeSaltEager_bound` is the birthday bound of the model. Each unordered pair with a hidden
  member costs `2^-256`.
* `treeSimSaltReuseEstimate_of_eager` gives the estimate from `TreeSimSaltReuseEager`, which
  moves the real run into the model with `n ≤ treeBatches * termCount`.

Conditioning the run on the end of the PRSS setup does not establish
`TreeSimSaltReuseEager`: it leaves the following address-selection and
collision obstacles.

* The setup fixes the PRSS key of each term. The only honest index-2 draw is `randBits 256` of
  the check, so the setup and the labels fix the address of each later salt.
* The addresses depend on the setup, so no fixed set of addresses bounds every run. A count of
  the addresses in each run is not sufficient either, because a run can choose a known address
  after it reads a hidden salt.
* A corrupt holder of a known term can send different parts to the honest holders. Only the echo
  makes them agree on the key. On a `.sharedKeys` collision the run reads more than
  `treeBatches * termCount` addresses. `TreeSimHashCollision` does not exclude this case, because
  `TreeSimHashDomain` has no `.sharedKeys` input.
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
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The salt of the address `i` in the eager model. A hidden address reads the uniform table. -/
def treeSaltEagerValue {n : ℕ} (hidden : Fin n → Prop) (known : Fin n → Fin 256 → Bit)
    (table : Fin n → Fin 256 → Bit) (i : Fin n) : Fin 256 → Bit :=
  if hidden i then table i else known i

/-- Two distinct addresses with the same salt, and one of them is hidden. -/
def TreeSaltEagerBad {n : ℕ} (hidden : Fin n → Prop) (known : Fin n → Fin 256 → Bit)
    (table : Fin n → Fin 256 → Bit) : Prop :=
  ∃ i j, i ≠ j ∧ hidden i ∧
    treeSaltEagerValue hidden known table i = treeSaltEagerValue hidden known table j

/-- A hidden salt equals the salt of another address with probability `2^-256`. -/
theorem treeSaltEager_pair {n : ℕ} (hidden : Fin n → Prop) (known : Fin n → Fin 256 → Bit)
    {i j : Fin n} (hij : i ≠ j) (hi : hidden i) :
    Pr[fun table => treeSaltEagerValue hidden known table i = treeSaltEagerValue hidden known table j |
      $ᵗ (Fin n → Fin 256 → Bit)] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have h := treeSimHash_uniform_coordinate_event (κ := Fin n) (R := Fin 256 → Bit) i
    (fun t => (pure t : ProbComp _))
    (fun table => treeSaltEagerValue hidden known table i = treeSaltEagerValue hidden known table j)
  rw [bind_pure] at h
  rw [← h]
  apply probEvent_bind_le_of_forall_le
  intro table _
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, treeSaltEagerValue, if_pos hi,
    Function.update_self, Function.update_of_ne hij.symm]
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  norm_num

/-- The ordered pairs `i < j` fill at most half of the square. -/
theorem treeSaltPairs_card (n : ℕ) :
    2 * ({x | x.1 < x.2} : Finset (Fin n × Fin n)).card ≤ n ^ 2 := by
  have hd : Disjoint ({x | x.1 < x.2} : Finset (Fin n × Fin n))
      ({x | x.2 < x.1} : Finset (Fin n × Fin n)) :=
    Finset.disjoint_filter.mpr (fun _ _ h h' => lt_asymm h h')
  have hc : ({x | x.2 < x.1} : Finset (Fin n × Fin n)).card =
      ({x | x.1 < x.2} : Finset (Fin n × Fin n)).card :=
    Finset.card_bij (fun x _ => x.swap) (by simp) (by simp)
      (by intro b hb; exact ⟨b.swap, by simpa using hb, by simp⟩)
  have hu := Finset.card_le_univ
    (({x | x.1 < x.2} : Finset (Fin n × Fin n)) ∪ ({x | x.2 < x.1} : Finset (Fin n × Fin n)))
  rw [Finset.card_union_of_disjoint hd, hc] at hu
  simpa [Fintype.card_prod, Fintype.card_fin, two_mul, pow_two] using hu

/-- The birthday bound of the eager model, one term for each unordered pair of addresses. -/
theorem treeSaltEager_bound {n : ℕ} (hidden : Fin n → Prop) (known : Fin n → Fin 256 → Bit) :
    Pr[TreeSaltEagerBad hidden known | $ᵗ (Fin n → Fin 256 → Bit)] ≤
      (({x | x.1 < x.2} : Finset (Fin n × Fin n)).card : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let value := treeSaltEagerValue hidden known
  let pairs : Finset (Fin n × Fin n) := {x | x.1 < x.2}
  calc Pr[TreeSaltEagerBad hidden known | $ᵗ (Fin n → Fin 256 → Bit)]
      ≤ Pr[fun table => ∃ p ∈ pairs, (hidden p.1 ∨ hidden p.2) ∧
          value table p.1 = value table p.2 | $ᵗ (Fin n → Fin 256 → Bit)] := by
        apply probEvent_mono
        rintro table _ ⟨i, j, hij, hi, he⟩
        rcases lt_or_gt_of_ne hij with h | h
        · exact ⟨(i, j), by simp [pairs, h], Or.inl hi, he⟩
        · exact ⟨(j, i), by simp [pairs, h], Or.inr hi, he.symm⟩
    _ ≤ ∑ p ∈ pairs, Pr[fun table => (hidden p.1 ∨ hidden p.2) ∧
          value table p.1 = value table p.2 | $ᵗ (Fin n → Fin 256 → Bit)] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _p ∈ pairs, (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hne : p.1 ≠ p.2 := ne_of_lt (by simpa [pairs] using hp)
        by_cases h1 : hidden p.1
        · exact (probEvent_mono fun table _ h => h.2).trans (treeSaltEager_pair hidden known hne h1)
        · by_cases h2 : hidden p.2
          · exact (probEvent_mono fun table _ h => h.2.symm).trans
              (treeSaltEager_pair hidden known hne.symm h2)
          · simp [h1, h2]
    _ = _ := by simp [pairs]

/-- The eager model bounds the reuse of a real run, with at most `treeBatches * termCount`
addresses. The model fixes the addresses and the known salts of the run, and draws each
hidden salt uniformly. -/
def TreeSimSaltReuseEager : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∃ (n : ℕ) (hidden : Fin n → Prop) (known : Fin n → Fin 256 → Bit),
      n ≤ treeBatches settings tree * termCount C ∧
      Pr[fun r => TreeSimSaltReuse D r.2 |
        treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
        Pr[TreeSaltEagerBad hidden known | $ᵗ (Fin n → Fin 256 → Bit)]

/-- The salt reuse estimate follows from the eager model. -/
theorem treeSimSaltReuseEstimate_of_eager
    (eager : TreeSimSaltReuseEager prims K circuits settings) :
    TreeSimSaltReuseEstimate prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  obtain ⟨n, hidden, known, hn, hle⟩ := eager hb top tree D A x z Z q hx hq hsmall
  have h := ENNReal.toReal_mono (by finiteness) (hle.trans (treeSaltEager_bound hidden known))
  refine h.trans ?_
  have hc := treeSaltPairs_card n
  have hN : 2 * ({x | x.1 < x.2} : Finset (Fin n × Fin n)).card ≤
      (treeBatches settings tree * termCount C) ^ 2 :=
    hc.trans (Nat.pow_le_pow_left hn 2)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  have hr : (2 : ℝ) * (({x | x.1 < x.2} : Finset (Fin n × Fin n)).card : ℝ) ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hN
  rw [show (2 : ℝ) ^ 257 = 2 ^ 256 * 2 from pow_succ 2 256, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [show (0 : ℝ) < 2 ^ 256 by positivity]

/-- info: 'ThresholdLeanXmssSecurity.treeSaltEager_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltEager_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimSaltReuseEstimate_of_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimSaltReuseEstimate_of_eager

end ThresholdLeanXmssSecurity
