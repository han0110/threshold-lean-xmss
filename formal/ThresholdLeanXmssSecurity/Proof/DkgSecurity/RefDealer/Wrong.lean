import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.Couple
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.PassTree

/-!
# The wrong output of one run

`passWrongCheck_of_bottom` proves `PassWrongCheck` from `PassWrongBottom`, its case of a bottom
tree. The case of the top tree is `passWrongTop` on `streamWorld`. `sharedRefDealer_of_bottom` proves
`SharedRefDealer` from `PassWrongBottom`. `passWrongBottom_of_batch` proves
`PassWrongBottom` from `PassBottomBatch`, the joint part of a bottom tree, with the path of one
operator `passBottom_fix`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- `PassWrongCheck` for a bottom tree. -/
def PassWrongBottom : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
      (s : RealState C net.State) (w : LogState C), NoMpc w.1.1 → RefOutputs prims D s w.1.1 →
      ∀ r ∈ support ((simulateQ (loggedWorld prims D) (executePhaseR worldRoles D net noFunctionality
          ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
            (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run)).run w),
        ¬ GlobalEvent r.2.1 →
        ∀ i, i ∉ D.1 → ∀ o, (r.1.2 i).output = some o → ∀ h, Good prims h → Agrees h r.2.1.1 →
          ¬ (∃ top, treeTop (s.operators i) (.bottom b) = some top ∧
            ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
              (prfValue (gameSeeds D fun i => (s.operators i).keys)) (gameParameter D fun i => (s.operators i).keys)
              top (.bottom b)) = some o) →
          PassBad K D fun j => (r.1.2 j).record []

/-- `PassWrongCheck` from its case of a bottom tree, with `passWrongTop` for the top tree. -/
theorem passWrongCheck_of_bottom (bottom : PassWrongBottom prims K circuits settings) :
    PassWrongCheck prims K circuits settings := by
  intro batch compute D net tree s w hmpc hout r hr hglobal i hi o ho h hg ha hnot
  cases tree with
  | top =>
    exact passWrongTop prims K circuits settings batch compute D net s w.1 hout.1 (r.1, r.2.1)
      (loggedWorld_support_stream prims D _ w r hr) hglobal i hi o ho h hg ha
      fun heq => hnot ⟨emptyTop, rfl, heq.symm⟩
  | bottom b => exact bottom batch compute D net b s w hmpc hout r hr hglobal i hi o ho h hg ha hnot

/-- `SharedRefDealer` from the case of a bottom tree of `PassWrongCheck`. -/
theorem sharedRefDealer_of_bottom (bottom : PassWrongBottom prims K circuits settings) :
    SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_wrong prims K circuits settings runLimit (passWrongCheck_of_bottom prims K circuits settings bottom)

/-- `PassWrongBottom` from the joint part of a bottom tree, with the path of one operator
`passBottom_fix`. -/
theorem passWrongBottom_of_batch (batch : PassBottomBatch prims K circuits settings) :
    PassWrongBottom prims K circuits settings := by
  intro hsize hc D net b s w hmpc hout r hr hglobal i hi o ho h hg ha hnot
  have hr' := loggedWorld_support_stream prims D _ w r hr
  have hstep : r.1.2 i = .done (some o) ((r.1.2 i).record []) := by
    rcases hs : r.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at ho
    · cases ho
      rfl
    · cases ho
    · cases ho
  have hpath := CeremonyRecords.onPath_done (hstep ▸ CeremonyRecords.ghostOnPath prims D D net ([] : Record C E)
    (treeFuel circuits settings) s.adversary _ w.1 (r.1, r.2.1) hr' h hg ha i hi)
  rcases hk : (s.operators i).keys with _ | keys
  · simp [passTree, hk, OptionT.run_failure] at hpath
  rcases ht : (s.operators i).top with _ | top
  · simp [passTree, hk, ht, OptionT.run_failure] at hpath
  have hpar : keys.parameter = gameParameter D fun i => (s.operators i).keys :=
    parameter_eq_gameParameter D _ hout.1 i hi keys hk
  obtain ⟨k, b', out, hb', hout', hnr⟩ := passBottom_fix prims K circuits settings hsize hc h hg
    (gameSeeds D fun i => (s.operators i).keys) i s b keys top hk ht o _ hpath
    (by rw [hpar]; exact fun heq => hnot ⟨top, by simp [treeTop, ht], heq.symm⟩)
  exact batch D net b s w.1 hout.1 (r.1, r.2.1) hr' hglobal i hi (by rw [ho]; rfl) h hg ha k b' out hb' hout' hnr

/-- `SharedRefDealer` from the joint part of a bottom tree. -/
theorem sharedRefDealer_of_bottomBatch (batch : PassBottomBatch prims K circuits settings) :
    SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_bottom prims K circuits settings runLimit (passWrongBottom_of_batch prims K circuits settings batch)

/-- `SharedRefDealer` from the rest of the joint part of a bottom tree. -/
theorem sharedRefDealer_of_bottomRest (rest : PassBottomRest prims K circuits settings) :
    SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_bottomBatch prims K circuits settings runLimit (passBottomBatch_of_rest prims K circuits settings rest)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_bottom

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_bottomBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_bottomBatch

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_bottomRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_bottomRest
