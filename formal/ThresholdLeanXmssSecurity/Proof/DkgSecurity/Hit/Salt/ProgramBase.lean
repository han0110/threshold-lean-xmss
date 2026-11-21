import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Provenance

/-!
# The two rewrites of a program with a fixed queue

`Prov D δ q oa` states that the rewrite `provShift D δ` of `oa` from the queue `q` is the program
`shiftQ D (saltShift D δ) oa`, and that it ends with the queue `q`. It is closed under `pure` and
`bind` (`Prov.bind`).

`Touch` is a free read of a stream at the index 2 under the name of a term or a free digest call. A
program with no call of `Touch` keeps each queue and has no shift (`prov_of_noTouch`,
`shiftQ_of_noTouch`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (D : C.Coalition) (δ : Fin 256 → Bit)

/-- A free read of a stream at the index 2 under the name of a term, or a free digest call. -/
def Touch : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr x)) => (∃ T : C.Term, x.1 = .term T) ∧ x.2.2.2.1 = 2
  | .inr (.inr (.inl q)) => ∃ (salt : List Bit) (history : HashOutput), q = .digest salt history
  | _ => False

/-- The rewrite of `oa` from the queue `q` is the shifted program and ends with the queue `q`. -/
def Prov (q : ProvQueue C) {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  (simulateQ (provShift D δ) oa).run q = (fun a => (a, q)) <$> shiftQ D (saltShift D δ) oa

variable {D δ}

theorem prov_pure (q : ProvQueue C) {α : Type} (a : α) : Prov D δ q (pure a) := by
  simp [Prov, shiftQ]

theorem Prov.bind {q : ProvQueue C} {α β : Type} {oa : OracleComp (WorldSpec C) α}
    {f : α → OracleComp (WorldSpec C) β} (h : Prov D δ q oa) (hf : ∀ a, Prov D δ q (f a)) :
    Prov D δ q (oa >>= f) := by
  unfold Prov shiftQ at h hf ⊢
  rw [simulateQ_bind, StateT.run_bind, h, simulateQ_bind, bind_map_left, map_bind]
  exact bind_congr fun a => hf a

theorem Prov.map {q : ProvQueue C} {α β : Type} {oa : OracleComp (WorldSpec C) α} (f : α → β)
    (h : Prov D δ q oa) : Prov D δ q (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun a => prov_pure q _

variable (D δ)

/-- The shift of a cell that is no cell at the index 2 of a term is zero. -/
theorem saltShift_eq_zero (c : HiddenCell C) (hc : ¬ ((∃ T : C.Term, c.1.1 = .term T) ∧ c.2.2.1 = 2)) :
    saltShift D δ c = 0 := by
  unfold saltShift
  split
  · rename_i T h
    split_ifs with h'
    · exact absurd ⟨⟨T, h⟩, h'.2.1⟩ hc
    · rfl
  · rfl

theorem pushRead_eq_self (x : PrgInput C) (hx : ¬ ((∃ T : C.Term, x.1 = .term T) ∧ x.2.2.2.1 = 2)) (b : Bit)
    (queue : ProvQueue C) : pushRead x b queue = queue := by
  unfold pushRead
  split
  · rename_i T h
    rw [ite_eq_right_iff.2 fun h2 => absurd ⟨⟨T, h⟩, h2⟩ hx]
  · rfl

/-- A call that is no call of `Touch` keeps each queue and has no shift. -/
theorem provShift_run_of_not_touch (t : (WorldSpec C).Domain) (ht : ¬ Touch t) (q : ProvQueue C) :
    (provShift D δ t).run q = (fun r => (r, q)) <$> (query (spec := WorldSpec C) t : OracleComp (WorldSpec C) _) ∧
      shiftImpl D (saltShift D δ) t = query (spec := WorldSpec C) t := by
  rcases t with ((u | q' | x) | p) | (u | q' | x)
  all_goals try exact ⟨rfl, rfl⟩
  · cases q'
    all_goals first | exact ⟨rfl, rfl⟩ | exact absurd ⟨_, _, rfl⟩ ht
  · refine ⟨?_, ?_⟩
    · change (fun b => (b, pushRead x b q)) <$> _ = _
      simp only [pushRead_eq_self x ht]
      rfl
    · simp only [shiftImpl]
      split_ifs
      · rw [saltShift_eq_zero D δ (streamCell x) ht]
        simp
      · rfl

/-- A program with no call of `Touch` has no shift. -/
theorem shiftQ_of_noTouch {α : Type} (oa : OracleComp (WorldSpec C) α) (h : NoCall Touch oa) :
    shiftQ D (saltShift D δ) oa = oa := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a => simp [shiftQ]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ Touch t := h.1.resolve_right (by omega)
    rw [shiftQ, simulateQ_bind, simulateQ_spec_query, (provShift_run_of_not_touch D δ t ht []).2]
    exact bind_congr fun u => ih u (by simpa [ht] using h.2 u)

/-- A program with no call of `Touch` keeps each queue. -/
theorem prov_of_noTouch (q : ProvQueue C) {α : Type} (oa : OracleComp (WorldSpec C) α) (h : NoCall Touch oa) :
    Prov D δ q oa := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a => exact prov_pure q a
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ Touch t := h.1.resolve_right (by omega)
    refine Prov.bind ?_ fun u => ih u (by simpa [ht] using h.2 u)
    obtain ⟨h₁, h₂⟩ := provShift_run_of_not_touch D δ t ht q
    unfold Prov
    rw [simulateQ_spec_query, h₁, shiftQ, simulateQ_spec_query, h₂]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.prov_of_noTouch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.prov_of_noTouch
