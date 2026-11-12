import ThresholdLeanXmssSecurity.Proof.Tree

/-!
# The security of a ceremony

`TreeSecurityStatement` (GS20, Theorem 2, and GL05) through `TreeSecurityDistance`.

The distance splits into two hops at the PRF reduction `prgReduction` (`treeSecurityDistance_of_hops`).

1. The key hop. The real run against the run with independent AES keys for the hidden streams.
   `keyWorld_coupling` bounds it by the stream-key bad event `probBad_streamKey`. The bad event
   pays `streamKeyError` and `keySplit`, the birthday terms of the `2 m` honest points of the
   `m` PRSS keys, namely the derived keys and their stream-key inputs.
2. The simulation hop. The real run with random hidden streams against the run of `treeSimulator`.
   It pays `treeCheckError` and the rest of `treeHashError`, which is at least the birthday bound
   of the other honest points (`keySplit_add_rest_le`).

The stage hypothesis is `TreeHopsRemaining`, the stream-key bound and the simulation hop.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section TreeSecurityProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-! ## The split of the hash budget -/

/-- The PRSS keys of a ceremony, one for each term and one for each pair. -/
def prssKeyCount (C : Committee) : ℕ := termCount C + C.n.choose 2

/-- The share of `treeHashError` that the key hop pays, `((q + 2 m)² - q²) / 2^256` for the `2 m`
honest points of the `m` PRSS keys, namely the derived keys and their stream-key inputs. -/
def keySplit (C : Committee) (q : ℕ) : ℝ :=
  ((4 * q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 256

/-- The honest points of a ceremony include the `2 m` points of the PRSS keys. -/
theorem two_prssKeyCount_le_treeSecrets (tree : Tree) :
    2 * prssKeyCount C ≤ treeSecrets circuits settings C tree := by
  unfold treeSecrets prssKeyCount
  simp only
  omega

/-- The key hop leaves the simulation hop at least the birthday bound of the counted calls and the
other honest points. -/
theorem keySplit_add_rest_le (tree : Tree) (q : ℕ) :
    keySplit C q + (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) / 2 ^ 256 ≤
      treeHashError circuits settings C tree q := by
  have hS := two_prssKeyCount_le_treeSecrets circuits settings (C := C) tree
  obtain ⟨S', hS'⟩ : ∃ S', treeSecrets circuits settings C tree = S' + 2 * prssKeyCount C :=
    ⟨_, (Nat.sub_add_cancel hS).symm⟩
  unfold treeHashError keySplit
  rw [hS', Nat.add_sub_cancel, ← add_div]
  gcongr
  rw [← Nat.cast_add]
  gcongr
  set m := prssKeyCount C
  have : (q + (S' + 2 * m)) ^ 2 = (q + S') ^ 2 + 4 * m * (q + S') + 4 * m ^ 2 := by ring
  rw [this]
  nlinarith

/-- The share of the simulation hop is nonnegative. -/
theorem keySplit_le_treeHashError (tree : Tree) (q : ℕ) :
    keySplit C q ≤ treeHashError circuits settings C tree q := by
  refine le_trans ?_ (keySplit_add_rest_le circuits settings tree q)
  have : (0 : ℝ) ≤ (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
    positivity
  linarith

/-! ## The key hop -/

/-- The stream-key bad event of a ceremony costs at most `streamKeyError` and `keySplit`. -/
def TreeStreamKeyBound : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    probBad_streamKey prims D (treeRealGame K circuits settings top tree D A x z Z) ≤
      streamKeyError C + keySplit C q

omit [Fintype E] [DecidableEq E] in
/-- `TreeKeyHop` from the stream-key bound, by `keyWorld_coupling`. -/
theorem treeKeyHop_of_streamKeyBound (h : TreeStreamKeyBound prims K circuits settings) :
    TreeKeyHop prims K circuits settings (keySplit C) :=
  fun hb top tree D A x z Z q hx hq =>
    (keyWorld_coupling prims D _).trans (h hb top tree D A x z Z q hx hq)

/-! ## The assembly -/

/-- The remaining stage, namely the stream-key bound of the key hop and the simulation hop with the
rest of the hash budget. -/
def TreeHopsRemaining : Prop :=
  TreeStreamKeyBound prims K circuits settings ∧ TreeSimulationHop prims K circuits settings (keySplit C)

theorem treeSecurityDistance (h : TreeHopsRemaining prims K circuits settings) :
    TreeSecurityDistance prims K circuits settings :=
  treeSecurityDistance_of_hops prims K circuits settings (keySplit C)
    (treeKeyHop_of_streamKeyBound prims K circuits settings h.1) h.2

theorem treeSecurityProof (h : TreeHopsRemaining prims K circuits settings) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurity_of_distance prims K circuits settings (treeSecurityDistance prims K circuits settings h)

end TreeSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityProof

end ThresholdLeanXmssSecurity
