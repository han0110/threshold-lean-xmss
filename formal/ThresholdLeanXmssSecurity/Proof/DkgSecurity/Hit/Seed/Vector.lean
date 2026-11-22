import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Clash

/-!
# The full vector of the honest parts of a hidden term

The draw of the parts of all operators is invariant under a shift of the term part of each operator
by its own value (`evalDist_shiftAll`). So the vector of the term parts of the `t` holders of a term
is uniform (`evalDist_holderParts`). So the derive input `hiddenInput parts T` meets a fixed cell
with probability at most `2^-(256 t)` (`probEvent_hiddenInput_eq_le`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The draw of the parts of all operators. -/
abbrev partsDraw (C : Committee) : ProbComp (C.Party → Parts C) :=
  OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)

/-- The parts of all operators with the term part of `T` of each operator `i` shifted by `c i`. -/
def shiftAll (T : C.Term) (c : C.Party → HashOutput) (parts : C.Party → Parts C) : C.Party → Parts C :=
  fun i => shiftParts (parts i) (some T) none (c i)

theorem evalDist_shiftAll (T : C.Term) (c : C.Party → HashOutput) :
    (shiftAll T c <$> partsDraw C) =ᵈ partsDraw C := by
  have h := sequenceFin_bind_pure (m := ProbComp) (fun _ : C.Party => sampleParts (C := C))
    (fun i own => shiftParts own (some T) none (c i))
  rw [map_eq_bind_pure_comp]
  have e : (pure ∘ shiftAll T c : (C.Party → Parts C) → ProbComp (C.Party → Parts C)) =
      fun rs => pure fun i => shiftParts (rs i) (some T) none (c i) := rfl
  rw [e, ← h]
  refine evalDist_sequenceFin_congr _ _ fun i => ?_
  rw [bind_pure_comp]
  exact evalDist_shift_sampleParts _ _ _

/-- The term parts of `T` of the holders of `T`. -/
def holderParts (T : C.Term) (parts : C.Party → Parts C) : {k // k ∈ C.holders T} → HashOutput :=
  fun k => (parts k.1).term T

theorem evalDist_holderParts (T : C.Term) :
    (holderParts T <$> partsDraw C) =ᵈ $ᵗ ({k // k ∈ C.holders T} → HashOutput) := by
  refine evalDist_eq_uniform_of_probOutput_eq _ fun u v => ?_
  let d : {k // k ∈ C.holders T} → HashOutput := fun k => u k ^^^ v k
  let φ : ({k // k ∈ C.holders T} → HashOutput) → ({k // k ∈ C.holders T} → HashOutput) := fun y k => y k ^^^ d k
  let c : C.Party → HashOutput := fun i => if h : i ∈ C.holders T then d ⟨i, h⟩ else 0
  have hshift : holderParts T ∘ shiftAll T c = φ ∘ holderParts T := by
    funext parts k
    simp [holderParts, shiftAll, shiftParts, c, φ, k.2]
  have h₁ : (holderParts T <$> partsDraw C) =ᵈ (φ <$> (holderParts T <$> partsDraw C)) :=
    calc (holderParts T <$> partsDraw C)
        =ᵈ (holderParts T <$> (shiftAll T c <$> partsDraw C)) := ((evalDist_shiftAll T c).map _).symm
      _ = _ := by
          rw [Functor.map_map, Functor.map_map]
          exact congrArg (· <$> partsDraw C) hshift
  have hφ : Function.Injective φ := fun a b e => by
    funext k
    have := congrArg (fun y => y k ^^^ d k) e
    simpa [φ, BitVec.xor_assoc] using this
  have hu : u = φ v := by
    funext k
    simp only [φ, d]
    rw [BitVec.xor_comm (u k) (v k), ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have key := prEvent_map_injective (holderParts T <$> partsDraw C) hφ v
  rw [← hu] at key
  exact (h₁.prEvent_eq _).trans key

theorem card_holders (T : C.Term) : Fintype.card {k // k ∈ C.holders T} = C.t := by
  simp [Committee.holders, T.2, Committee.n]
  have := C.one_le_t
  omega

theorem holdersList_ne_nil (T : C.Term) : seedGenHolderList T ≠ [] := by
  intro h
  have hc := card_holders T
  have hpos : 0 < (C.holders T).card := by
    rw [Fintype.card_coe] at hc
    have := C.one_le_t
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.1 hpos
  have : k ∈ seedGenHolderList T := by simp [seedGenHolderList, hk, Committee.parties]
  rw [h] at this
  exact List.not_mem_nil this

theorem holderParts_of_hiddenInput {T : C.Term} {parts parts' : C.Party → Parts C}
    (h : hiddenInput parts T = hiddenInput parts' T) : holderParts T parts = holderParts T parts' := by
  funext k
  simp only [hiddenInput, Query.derive.injEq, true_and] at h
  have hk : k.1 ∈ seedGenHolderList T := by simp [seedGenHolderList, Committee.parties, k.2]
  exact List.map_inj_left.1 h k.1 hk

/-- The derive input of a term on fresh parts meets a fixed cell with probability at most
`2^-(256 t)`. -/
theorem probEvent_hiddenInput_eq_le (T : C.Term) (L : Query C) :
    Pr{let parts ← partsDraw C}[hiddenInput parts T = L] ≤ ((Fintype.card HashOutput : ℝ≥0∞) ^ C.t)⁻¹ := by
  by_cases hL : ∃ parts₀ : C.Party → Parts C, hiddenInput parts₀ T = L
  · obtain ⟨parts₀, rfl⟩ := hL
    calc _ ≤ Pr{let parts ← partsDraw C}[holderParts T parts = holderParts T parts₀] :=
          prEvent_mono _ _ _ fun parts h => holderParts_of_hiddenInput h
      _ = Pr{let y ← holderParts T <$> partsDraw C}[y = holderParts T parts₀] := by rw [prEvent_map]
      _ = _ := by
          rw [(evalDist_holderParts T).prEvent_eq, SampleableType.prEvent_uniformSample_eq_singleton,
            Fintype.card_fun, card_holders, Nat.cast_pow]
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun parts _ h => hL ⟨parts, h⟩) bot_le

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.probEvent_hiddenInput_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.probEvent_hiddenInput_eq_le

