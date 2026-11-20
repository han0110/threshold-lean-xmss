import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.Birthday
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.SetupBudgets

/-!
# The four collision hops of the game

`echoHop`, `reuseHop`, `copyHop` and `splitHop` prove `CollisionHopW` at the echo hashes, the derived
keys, the copy hashes and the history and digest cells, with `echoError`, `reuseError`, `copyError`
and `splitError`. Each is `Collision.firstCollision_le` with the honest budget of its domain.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- A bound over `2^257` is at most the same bound over `2^256`. -/
theorem Collision.div_two_pow_257_le (x : ℝ) (hx : 0 ≤ x) : x / 2 ^ 257 ≤ x / 2 ^ 256 :=
  div_le_div_of_nonneg_left hx (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-- The honest copy and digest cells of `runLimit` runs of each tree are the cells of `gameBatches`. -/
theorem Collision.runs_termHashes :
    0 + runLimit * (treeBatches settings .top * termHashes C +
      ∑ b : Fin (2 ^ layerHeight), treeBatches settings (.bottom b) * termHashes C) =
      gameBatches settings runLimit * termHashes C := by
  unfold gameBatches
  rw [← Finset.sum_mul]
  ring

/-- Two copy hashes collide at the world of the first bad record with probability at most
`copyError`. -/
theorem copyHop :
    ∀ prims : Primitives, CollisionHopW prims K circuits settings runLimit CopyDomain (copyError settings runLimit C) := by
  intro prims D A q ready hA
  have hPc : ∀ x : Query C, CopyDomain x → queryClass x = .copy := fun x hx => by
    cases x <;> simp_all [CopyDomain, queryClass]
  have h := Collision.firstCollision_le K circuits settings runLimit (c := .copy) (by decide) CopyDomain hPc 0
    (fun tree => treeBatches settings tree * termHashes C)
    (Collision.honestBudget_of_class K circuits settings hPc 0 _ (DigestBudgets.seedHonest (by decide))
      (DigestBudgets.treeHonest K circuits settings (Or.inr rfl)))
    (DigestBudgets.signQuiet (by decide)) prims D A q ready hA
  rw [Collision.runs_termHashes] at h
  exact h.trans (Collision.div_two_pow_257_le _ (by positivity))

/-- Two history or digest cells collide at the world of the first bad record with probability at most
`splitError`. -/
theorem splitHop :
    ∀ prims : Primitives, CollisionHopW prims K circuits settings runLimit SplitHashDomain (splitError settings runLimit C) := by
  intro prims D A q ready hA
  have hPc : ∀ x : Query C, SplitHashDomain x → queryClass x = .digest := fun x hx => by
    cases x <;> simp_all [SplitHashDomain, queryClass]
  have h := Collision.firstCollision_le K circuits settings runLimit (c := .digest) (by decide) SplitHashDomain
    hPc 0 (fun tree => treeBatches settings tree * termHashes C)
    (Collision.honestBudget_of_class K circuits settings hPc 0 _ (DigestBudgets.seedHonest (by decide))
      (DigestBudgets.treeHonest K circuits settings (Or.inl rfl)))
    (DigestBudgets.signQuiet (by decide)) prims D A q ready hA
  rw [Collision.runs_termHashes] at h
  refine h.trans (le_of_eq ?_)
  unfold splitError splitRisk splitBudget
  rw [show (2 : ℝ) ^ 257 = 2 * 2 ^ 256 from pow_succ' 2 256]
  push_cast
  ring

/-- The budget of a domain of the PRSS setups from the bound `R` of the setup of one operator. The seed
generation makes no call of the domain, and a run of `tree` makes the calls of `treeSetups tree`
setups at each of the `n` operators. -/
theorem Collision.setupBudget {P : Query C → Prop} (hPc : ∀ x, P x → queryClass x = .prssSetup) (R : ℕ)
    (hsetup : ∀ i, SetupBudgets.PBound (E := E) (SplitRegionCounted P) (prssSetup i) R) :
    Collision.HonestBudget K circuits settings P 0 fun tree => C.n * (treeSetups tree * R) := by
  have hp : ∀ t, SplitRegionCounted P t → InClass .prssSetup t := fun t ht => Collision.inClass_of_counted hPc ht
  refine ⟨fun D net => ?_, fun D net tree s => ?_⟩
  · have h := DigestBudgets.seedHonest (C := C) (E := E) (c := .prssSetup) (by decide) D net
    rw [GameCount.bound_iff] at h ⊢
    exact h.of_imp fun t ht => by
      rcases t with _ | u
      · exact ht.elim
      · exact hp u ht
  · rw [GameCount.bound_iff]
    exact (SetupBudgets.treeHonestP K circuits settings hp R hsetup D net tree s).of_imp fun t ht => by
      rcases t with _ | u
      · exact ht.elim
      · exact ht

/-- The honest cells of `runLimit` runs of each tree with `R` cells for each setup of each operator. -/
theorem Collision.runs_setups (R : ℕ) :
    0 + runLimit * (C.n * (treeSetups .top * R) +
      ∑ b : Fin (2 ^ layerHeight), C.n * (treeSetups (.bottom b) * R)) = gameSetups runLimit * C.n * R := by
  simp only [treeSetups, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold gameSetups
  ring

/-- Two echo hashes of the PRSS setups collide at the world of the first bad record with probability at
most `echoError`. -/
theorem echoHop :
    ∀ prims : Primitives, CollisionHopW prims K circuits settings runLimit EchoDomain (echoError runLimit C) := by
  intro prims D A q ready hA
  have hPc : ∀ x : Query C, EchoDomain x → queryClass x = .prssSetup := fun x hx => by
    rcases x with _ | _ | _ | _ | _ | ⟨_ | _, _⟩ | _ | _ | _ | _ | _ | _ <;> simp_all [EchoDomain, queryClass, phaseClass]
  have hsetup : ∀ i, SetupBudgets.PBound (E := E) (SplitRegionCounted EchoDomain) (prssSetup i)
      (0 + C.parties.length * 1) := fun i =>
    SetupBudgets.prssSetup_pbound (fun t ht => Collision.inClass_of_counted hPc ht) i 0 1
      (fun j k l => by simp [SplitRegionCounted, splitLocalHashInput, IsFixed, EchoDomain])
      (fun view => SetupBudgets.deriveKeys_zero i view fun kind l => by
        simp [SplitRegionCounted, splitLocalHashInput, IsFixed, EchoDomain])
      (fun l => (hashQuery_queryBound _).of_imp fun _ _ => trivial)
  have h := Collision.firstCollision_le K circuits settings runLimit (c := .prssSetup) (by decide) EchoDomain hPc 0
    _ (Collision.setupBudget K circuits settings hPc _ hsetup) (DigestBudgets.signQuiet (by decide)) prims D A q ready hA
  rw [Collision.runs_setups, SetupAgree.parties_length] at h
  refine h.trans (le_of_eq ?_)
  unfold echoError
  congr 3
  ring

/-- Two derived keys of the PRSS setups collide at the world of the first bad record with probability at
most `reuseError`. -/
theorem reuseHop :
    ∀ prims : Primitives, CollisionHopW prims K circuits settings runLimit DeriveDomain (reuseError runLimit C) := by
  intro prims D A q ready hA
  have hPc : ∀ x : Query C, DeriveDomain x → queryClass x = .prssSetup := fun x hx => by
    rcases x with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | _ | _ | _ | _ | _ | _ | _ <;>
      simp_all [DeriveDomain, queryClass, phaseClass]
  have hsetup : ∀ i, SetupBudgets.PBound (E := E) (SplitRegionCounted DeriveDomain) (prssSetup i)
      (C.terms.length + C.parties.length + C.parties.length * 0) := fun i =>
    SetupBudgets.prssSetup_pbound (fun t ht => Collision.inClass_of_counted hPc ht) i _ 0
      (fun j k l => by simp [SplitRegionCounted, splitLocalHashInput, IsFixed, DeriveDomain])
      (fun view => SetupBudgets.deriveKeys_count _ i view)
      (fun l => (SigningSelectionProof.noCall_iff _ _).1 (SigningSelectionProof.noCall_query _ _ (by
        simp [SplitRegionCounted, splitLocalHashInput, IsFixed, DeriveDomain])))
  have h := Collision.firstCollision_le K circuits settings runLimit (c := .prssSetup) (by decide) DeriveDomain hPc
    0 _ (Collision.setupBudget K circuits settings hPc _ hsetup) (DigestBudgets.signQuiet (by decide)) prims D A q ready hA
  rw [Collision.runs_setups, SetupAgree.parties_length, check_terms_length] at h
  refine h.trans (le_of_eq ?_)
  unfold reuseError termCount
  rw [Nat.mul_zero, Nat.add_zero, Nat.mul_assoc]

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.echoHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.echoHop

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.reuseHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.reuseHop

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.copyHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.copyHop

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.splitHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.splitHop
