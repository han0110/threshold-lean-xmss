import ThresholdLeanXmssSecurity.Proof.LifetimeStreamKeyQuiet

/-!
# The lifetime boundary split into setup events and a tail flag

The actual lifetime tail is evaluated with the lazy aimed oracle after
`worldSetup`. A fresh key hit with apart keys implies its flag. The joint
world's bad event is therefore covered by failed separation at setup, a
setup key hit, and this flagged tail event.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeTailFlag

open LifetimeRunBoundary LifetimeJointHop
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E) (prims : Primitives)

/-- The actual lifetime setup paired with its lazy aimed tail. -/
def lazyRunBoundary :=
  worldRun prims (worldSetup K circuits settings attempts D n A) >>= fun r =>
    (fun y => (r, y)) <$>
      (simulateQ (lazyAimedImpl prims D (rowsAt r.1))
        (worldTail K circuits settings attempts D n r.1)).run ((r.2, ∅), false)

/-- With apart keys and no setup hit, a final key hit raises the tail flag. -/
theorem boundary_afterHit_le_flag :
    Pr[fun y => KeysApart D (rowsAt y.1.1) ∧ ¬ KeyHit D (rowsAt y.1.1) y.1.2 ∧
        KeyHit D (rowsAt y.1.1) y.2.2.hash |
      runBoundary K circuits settings attempts D n A prims] ≤
    Pr[fun y => KeysApart D (rowsAt y.1.1) ∧ y.2.2.2 = true |
      lazyRunBoundary K circuits settings attempts D n A prims] := by
  unfold runBoundary boundaryOf lazyRunBoundary
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun r => ?_
  by_cases hs : r ∈ support (worldRun prims (worldSetup K circuits settings attempts D n A))
  · have hs' : r.1 ∈ support (worldSetup K circuits settings attempts D n A) := by
      apply support_simulateQ_run'_subset (worldAnswer prims) _ ∅
      simp only [StateT.run'_eq, support_map, Set.mem_image]
      exact ⟨r, hs, rfl⟩
    refine mul_le_mul_right ?_ _
    rw [probEvent_map, probEvent_map]
    by_cases hr : KeysApart D (rowsAt r.1) ∧ ¬ KeyHit D (rowsAt r.1) r.2
    · let game := worldTail K circuits settings attempts D n r.1
      have hb : keyJointIdealProjection (boundaryState r.2) = (r.2, (∅ : KeyCache C)) := by
        simp only [keyJointIdealProjection, boundaryState, Prod.mk.injEq, true_and]
        funext y
        rfl
      rw [← hb, ← probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_aimedImpl_projection prims D (rowsAt r.1) game (boundaryState r.2) false),
        probEvent_map]
      rw [← probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_flagImpl_fst (jointKeyWorld prims D false)
          (fun t (_ : Unit) => AimedCall D (rowsAt r.1) t) () game (boundaryState r.2) false),
        probEvent_map]
      apply probEvent_mono
      intro y hy hhit
      refine ⟨hr.1, ?_⟩
      by_contra hf
      have ha := worldTail_allowed K circuits settings attempts D n A
        (tailAllowed K circuits settings attempts D n A
          (LifetimeStreamKeyQuiet.freeStreamKeyQuiet K circuits settings attempts n D A)) r.1 hs'
      have h := aimedImpl_run_noKeyHit prims D (rowsAt r.1) hr.1 game ha
        (boundaryState r.2) false y hy (Bool.eq_false_iff.mpr hf)
      exact h.2 hr.2 hhit.2.2
    · exact (probEvent_eq_zero (fun y _ hy => hr ⟨hy.1, hy.2.1⟩)).le.trans zero_le
  · simp [probOutput_eq_zero_of_not_mem_support hs]

/-- The joint-world bad event is covered by two setup events and the lazy tail flag. -/
theorem bad_le_setup_add_flag :
    Pr[fun y => y.2.2.bad = true | runBoundary K circuits settings attempts D n A prims] ≤
      Pr[fun r => ¬ KeysApart D (rowsAt r.1) |
        worldRun prims (worldSetup K circuits settings attempts D n A)] +
      Pr[fun r => KeyHit D (rowsAt r.1) r.2 |
        worldRun prims (worldSetup K circuits settings attempts D n A)] +
      Pr[fun y => KeysApart D (rowsAt y.1.1) ∧ y.2.2.2 = true |
        lazyRunBoundary K circuits settings attempts D n A prims] := by
  have hcover := runBoundary_bad K circuits settings attempts D n A prims
    (LifetimeStreamKeyQuiet.freeStreamKeyQuiet K circuits settings attempts n D A)
  have hsplit : Pr[fun y => y.2.2.bad = true |
      runBoundary K circuits settings attempts D n A prims] ≤
      Pr[fun y => ¬ KeysApart D (rowsAt y.1.1) |
        runBoundary K circuits settings attempts D n A prims] +
      (Pr[fun y => KeyHit D (rowsAt y.1.1) y.1.2 |
        runBoundary K circuits settings attempts D n A prims] +
      Pr[fun y => KeysApart D (rowsAt y.1.1) ∧ ¬ KeyHit D (rowsAt y.1.1) y.1.2 ∧
          KeyHit D (rowsAt y.1.1) y.2.2.hash |
        runBoundary K circuits settings attempts D n A prims]) := by
    refine (probEvent_mono fun y hy hb => ?_).trans
      ((probEvent_or_le _ _ _).trans (add_le_add le_rfl (probEvent_or_le _ _ _)))
    rcases hcover y hy hb with h | h
    · exact Or.inl h
    · by_cases hh : KeyHit D (rowsAt y.1.1) y.1.2
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ⟨h.1, hh, h.2⟩)
  rw [← add_assoc] at hsplit
  refine hsplit.trans (add_le_add (add_le_add ?_ ?_)
    (boundary_afterHit_le_flag K circuits settings attempts D n A prims))
  · unfold runBoundary boundaryOf
    exact probEvent_pair_fst_le _ _
      (fun r : ((Option (Boundary C E) × StreamCache C) × CallLog C) × HashCache C => ¬ KeysApart D (rowsAt r.1))
  · unfold runBoundary boundaryOf
    exact probEvent_pair_fst_le _ _
      (fun r : ((Option (Boundary C E) × StreamCache C) × CallLog C) × HashCache C => KeyHit D (rowsAt r.1) r.2)

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlag.boundary_afterHit_le_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_afterHit_le_flag

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlag.bad_le_setup_add_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bad_le_setup_add_flag

end ThresholdLeanXmssSecurity.LifetimeTailFlag
