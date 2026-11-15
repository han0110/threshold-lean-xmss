import ThresholdLeanXmssSecurity.Proof.SigningPartnerBound

/-!
# The joint run with both logs

`jointRun` runs `verifyFinal` under `loggedImpl`. So one execution holds both logs.

* `jointRun_logged` drops the candidates and gives `loggedRun` exactly.
* `jointRun_verify` drops the call log and gives `verifyRun` exactly.

So `guess_hiddenInputHit` holds on the joint run with no coupling. The opening candidates need the
state at call time (`Released`), which the call log does not hold.

`fresh_state_at` shows that a fresh call at another key keeps the state of the monitor at `e`.

`SigningAssembly`, `SigningLinkPaid` and `SigningOneRun` use the joint run.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningUnchargedLoggedProof

open HashSig LeanXmss ThresholdLeanXmss SigningHitLaneProof SigningCostProof SigningPartnerBoundProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- An outcome of `jointRun`. -/
abbrev JointOutcome (C : Committee) :=
  (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (SigningOpeningProof.HiddenKey × Digest)) ×
    LoggedState C

/-- One run with both logs. `verifyFinal` keeps the unreleased candidates, and `loggedImpl` logs
each world call with its answer. -/
def jointRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) : ProbComp (JointOutcome C) :=
  (simulateQ (loggedImpl prims) (SigningGuessLinkProof.verifyFinal A x)).run loggedInit

/-- The joint run without the candidates is `loggedRun`. -/
theorem jointRun_logged (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1.1, z.2)) <$> jointRun prims A x = loggedRun prims A x := by
  unfold jointRun loggedRun
  rw [← SigningGuessLinkProof.verifyFinal_forget, simulateQ_map, StateT.run_map]
  rfl

/-- The joint run without the call log is `verifyRun`. -/
theorem jointRun_verify (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, z.2.1)) <$> jointRun prims A x = SigningGuessLinkProof.verifyRun prims A x :=
  SigningCoreProof.simulateQ_run_forget _ _ (fun t s b => by simp [loggedImpl, Functor.map_map]) _ _ _


set_option maxRecDepth 100000 in
/-- The joint run without the call log and the candidates is `exposedRun`. -/
theorem mem_exposedRun_of_joint (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) :
    (w.1.1, w.2.1) ∈ support (SigningDescentProof.exposedRun prims A x) := by
  rw [← SigningGuessLinkProof.verifyRun_forget, ← jointRun_verify, Functor.map_map, support_map, Set.mem_image]
  with_reducible exact ⟨w, hw, rfl⟩

set_option maxRecDepth 100000 in
theorem mem_verifyRun_of_joint (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) :
    (w.1, w.2.1) ∈ support (SigningGuessLinkProof.verifyRun prims A x) := by
  rw [← jointRun_verify, support_map, Set.mem_image]
  with_reducible exact ⟨w, hw, rfl⟩

section MonitorList

variable (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)

/-- A hash entry holds the input, the digest of the answer, and `true` on the free copy. -/
abbrev Entry := XmssSecurity.HashInput × XmssSecurity.Digest × Bool

variable (e : XmssSecurity.LeafIndex) (forged : XmssSecurity.HashInput) (digest : XmssSecurity.Digest)

/-- A fresh call at another key or at no key keeps the state at `e`. -/
theorem fresh_state_at (m : Monitor) (input : XmssSecurity.HashInput) (d : XmssSecurity.Digest) (honest : Bool)
    (hk : keyOf input ≠ some e) :
    (m.fresh keyOf input d honest).state.signed e = m.state.signed e ∧
      (m.fresh keyOf input d honest).state.pending e = m.state.pending e ∧
      (m.fresh keyOf input d honest).seen = insert input m.seen ∧
      ((m.fresh keyOf input d honest).hit = true ∨ (m.fresh keyOf input d honest).hit = m.hit) := by
  cases hk' : keyOf input with
  | none => rw [m.fresh_none keyOf input d honest hk']; simp
  | some e' =>
    have he : e ≠ e' := fun h => hk (h ▸ hk')
    cases hs : m.state.signed e' with
    | none =>
      rw [m.fresh_unsigned keyOf input d honest e' hk' hs]
      split_ifs <;>
        simp [XmssSecurity.EncodingMonitor.State.install, XmssSecurity.EncodingMonitor.State.addPending,
          Function.update_of_ne he]; tauto
    | some target => rw [m.fresh_signed keyOf input d honest e' hk' target hs]; simp; tauto

end MonitorList

end SigningUnchargedLoggedProof

end ThresholdLeanXmssSecurity
