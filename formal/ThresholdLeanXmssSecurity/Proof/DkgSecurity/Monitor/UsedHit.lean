import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Monitor.Commute
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Monitor.Erase

/-!
# The monitor does not change the stream-key event

`dkgTsigGame` and `dkgTreeGame` are two projections of `dkgTsigRun`, with no monitor and with the
monitor `wrongOutput D`. Both monitors are free, and `jointKeyWorld prims D false` has the two
properties of the erasure (`monitorCommutes_joint`, `monitorKeeps_joint`). So the two games give one
law of `privateView` of the final state, and `UsedHit` has one probability in both
(`usedHitProb_monitor_eq`). `monitorErase` is the inequality between the two games that the hops of
`dkgSecurity` use.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (noCall_pure)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem monitorCommutes_joint (D : C.Coalition) : MonitorCommutes (jointKeyWorld prims D false) :=
  fun t t' ht ht' => jointKeyWorld_monitorCommute prims D t t' ht ht'

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem monitorKeeps_joint (D : C.Coalition) : MonitorKeeps (jointKeyWorld prims D false) privateView :=
  fun t ht s => jointKeyWorld_monitorView prims D t ht s

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A map of the result keeps the final state. -/
theorem usedHitProb_map {α : Type} (D : C.Coalition) (f g : α → Bool) (P : OracleComp (WorldSpec C) α) :
    usedHitProb prims D (f <$> P) = usedHitProb prims D (g <$> P) := by
  unfold usedHitProb
  simp only [simulateQ_map, StateT.run_map, prEvent_map]

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- `UsedHit` reads `privateView` only. -/
theorem usedHitProb_view (D : C.Coalition) (P : OracleComp (WorldSpec C) Bool) :
    usedHitProb prims D P = (Pr{let z ← (fun r => (r.1, privateView r.2)) <$>
        (simulateQ (jointKeyWorld prims D false) (P >>= pure)).run keyJointInitial}[
          ∃ s, privateView s = z.2 ∧ UsedHit D s]).toReal := by
  unfold usedHitProb
  rw [bind_pure, prEvent_map]
  congr 3
  funext r
  exact propext ⟨fun h => ⟨r.2, rfl, h⟩, fun ⟨s, hs, h⟩ => (usedHit_iff_view D hs).1 h⟩

omit [Fintype E] [DecidableEq E] in
/-- The two games give `UsedHit` one probability. -/
theorem usedHitProb_monitor_eq (D : C.Coalition) (A : DkgTsigAdversary C E) :
    usedHitProb prims D (dkgTsigGame K circuits settings runLimit D A) =
      usedHitProb prims D (dkgTreeGame K circuits settings runLimit D A) := by
  have h := dkgTsigRun_obsEq K circuits settings runLimit D (monitorCommutes_joint prims D)
    (monitorKeeps_joint prims D) freeMonitor_noMonitor (freeMonitor_wrongOutput D) A Bool pure
    (fun _ => noCall_pure _ _) keyJointInitial
  unfold dkgTreeGame
  rw [usedHitProb_map prims D Prod.snd Prod.fst]
  unfold dkgTsigGame
  rw [usedHitProb_view, usedHitProb_view]
  exact congrArg ENNReal.toReal (h.prEvent_eq _)

omit [Fintype E] [DecidableEq E] in
/-- The stream-key event of `dkgTsigGame` is at most as likely as the one of `dkgTreeGame`. -/
theorem monitorErase : ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    usedHitProb prims D (dkgTsigGame K circuits settings runLimit D A) ≤
      usedHitProb prims D (dkgTreeGame K circuits settings runLimit D A) :=
  fun D A => (usedHitProb_monitor_eq prims K circuits settings runLimit D A).le

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.monitorErase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.monitorErase
