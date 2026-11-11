import ThresholdLeanXmssSecurity.Proof.SigningFlatEager

/-!
# The eager law with both signing logs

The opening handler and the verification suffix make no programming queries. Their forgetful
projections reduce this fact to the existing program-free signing lemmas, using VCV-io's
`isQueryBoundP_iff_of_map_eq`. The map-invariance argument also appears in leanVM's
`CappedGlobalCausalSetup` through `isQueryBoundP_map_iff`; no leanVM lemma needs porting here.

The joint game carries the signing state, released trees and candidate log through each world
call. The hash law of `SigningFlatEager` therefore applies to its setup, adversary and verification
stages. Extra lazy calls preserve the joint law of the result, count, call log and carried state
after forgetting the final cache. The eager and lazy final caches need not agree.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningJointEagerProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof

variable {C : Committee}

/-- The state carried by the opening handler. -/
abbrev OpeningState (C : Committee) :=
  (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) ×
    List (SigningOpeningProof.HiddenKey × Digest)

/-- The concrete dealer used in the joint run. -/
abbrev dealtOf (x : SigningSecurityProof.Keys3 C) (top : TopTree) :
    Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
    (dealtKeys x.1 x.2.1 x.2.2) top
    (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))

/-- Adding released trees and candidates to the flagged handler adds no queries. -/
theorem programFree_openingOracles (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : OpeningState C) :
    SigningHitProof.ProgramFree
      ((SigningOpeningProof.openingOracles x (dealtOf x top) t).run s) := by
  classical
  exact (isQueryBoundP_iff_of_map_eq
    (SigningOpeningProof.openingOracles_forget x (dealtOf x top) t s.1 s.2)).mpr
      (SigningHitProof.programFree_flaggedOracles x top t s.1)

/-- Logging the verification candidates adds no programming queries. -/
theorem programFree_tsigFinishLogged (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (trees : Finset (Fin (2 ^ layerHeight))) (p : Forgery × TsigState C) :
    SigningHitProof.ProgramFree
      (SigningGuessLinkProof.tsigFinishLogged (dealtOf x top) trees p) := by
  classical
  exact (isQueryBoundP_iff_of_map_eq
    (SigningGuessLinkProof.tsigFinishLogged_forget (dealtOf x top) trees p)).mpr
      (SigningHitProof.programFree_finish x top p)

set_option maxRecDepth 100000 in
/-- The complete joint program has no programming query on any response branch. -/
theorem programFree_verifyFinal (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    SigningHitProof.ProgramFree (SigningGuessLinkProof.verifyFinal A x) := by
  classical
  exact (isQueryBoundP_iff_of_map_eq (SigningGuessLinkProof.verifyFinal_forget A x)).mpr
    (SigningHitProof.programFree_finalRun A x)

/-- The result and the unreleased candidates of the joint run. -/
abbrev JointResult (C : Committee) :=
  Result C × List (SigningOpeningProof.HiddenKey × Digest)

/-- The three stages of the joint run over arbitrary handlers. -/
def jointGameWith {m : Type → Type} [Monad m] (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (world : QueryImpl (WorldSpec C) m)
    (forger : Dealt C (OracleComp (WorldSpec C)) → QueryImpl (LocalSpec C + TsigSpec C) m)
    (carried : m (OpeningState C)) : m (JointResult C) := do
  let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
  let r ← simulateQ world
    (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa)) value x.1 emptyTop .top)
  match r with
  | some (.top top) =>
    let dealt := dealtOf x top
    let a ← simulateQ (forger dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)
    let s ← carried
    let w ← simulateQ world (SigningGuessLinkProof.tsigFinishLogged dealt s.2.1 (a, s.1.1))
    pure (((w.1.1, s.1.2), some (top, w.1.2)), s.2.2 ++ w.2)
  | _ => pure (((false, false), none), [])

/-- The joint game with a world handler that can read the full carried state. -/
def jointGame (W : QueryImpl (WorldSpec C) (StateT (FlatJointState C) ProbComp))
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT (FlatJointState C) ProbComp (JointResult C) :=
  jointGameWith A x W (fun dealt => flatWith (SigningOpeningProof.openingOracles x dealt) W)
    getCarried

/-- The joint game in hash form. -/
def jointHash (prims : Primitives) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT (Rest C (OpeningState C)) (OracleComp (SigningFlatProof.HashSpec C)) (JointResult C) :=
  jointGameWith A x (worldTracker prims)
    (fun dealt => outerTracker prims (SigningOpeningProof.openingOracles x dealt))
    (StateT.mk fun r => pure (r.2, r))

/-- The initial joint state. -/
def jointInit : FlatJointState C :=
  (SigningHitLaneProof.loggedInit, ((SigningCoreProof.tsigInit, false), ∅, []))

set_option maxRecDepth 100000 in
/-- Each stage of the joint game has its hash law, including the verification candidates. -/
theorem hashLaw_jointGame (prims : Primitives)
    (W : QueryImpl (WorldSpec C) (StateT (FlatJointState C) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W t) (worldHash prims t))
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    HashLaw (jointGame W A x) (jointHash prims A x).run := by
  unfold jointGame jointHash jointGameWith
  dsimp only
  have hsetup : SigningHitProof.ProgramFree
      (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    exact SigningHitProof.programFree_liftFree _
  refine hashLaw_bindT (hashLaw_simulateQ_world prims W hW _ hsetup) fun r => ?_
  rcases r with _ | (top | tree)
  · exact hashLaw_pure _
  · refine hashLaw_bindT (hashLaw_simulateQ _ _
      (fun t => hashLaw_flatWith prims _ (programFree_openingOracles x top) W hW t) _) fun a => ?_
    refine hashLaw_bindT hashLaw_getCarried fun s => ?_
    refine hashLaw_bindT (hashLaw_simulateQ_world prims W hW _
      (programFree_tsigFinishLogged x top s.2.1 _)) fun w => ?_
    exact hashLaw_pure _
  · exact hashLaw_pure _

/-- Forgetting the carried state of the ordinary joint game gives the existing joint run. -/
theorem jointGame_eq_jointRun (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, z.2.1)) <$>
        (jointGame (carry (SigningCostProof.loggedImpl prims)) A x).run jointInit =
      SigningUnchargedLoggedProof.jointRun prims A x := by
  rw [← flatJointRun_eq]
  unfold jointGame jointGameWith flatJointRun
  rw [StateT.run_bind, map_bind, carry_run]
  simp only [bind_map_left]
  refine bind_congr fun z => ?_
  rcases z with ⟨_ | (top | tree), l⟩
  · rfl
  · simp [StateT.run_bind, getCarried, flatOpening, flat_eq_flatWith, carry_run_pair,
      jointInit, dealtOf, Functor.map_map]
  · rfl

/-- World handlers with the same hash law give the same joint result, count, logs and carried
state, after forgetting their final caches. -/
theorem evalDist_jointGame_eq (prims : Primitives)
    (W W' : QueryImpl (WorldSpec C) (StateT (FlatJointState C) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W t) (worldHash prims t))
    (hW' : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W' t) (worldHash prims t))
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, restOf z.2)) <$> (jointGame W A x).run jointInit] =
      𝒟[(fun z => (z.1, restOf z.2)) <$> (jointGame W' A x).run jointInit] :=
  (evalDist_map_restOf (hashLaw_jointGame prims W hW A x) ∅
    ((0, []), ((SigningCoreProof.tsigInit, false), ∅, []))).trans
  (evalDist_map_restOf (hashLaw_jointGame prims W' hW' A x) ∅
    ((0, []), ((SigningCoreProof.tsigInit, false), ∅, []))).symm

/-- The canonical-base grind of the flat run, with the extra opening state carried along. -/
def jointGrindExtra (P : PublicParameter) (ρ : KeyIndex → Digest) (p : FlatJointState C)
    (t : (WorldSpec C).Domain) (p' : FlatJointState C) :
    OracleComp (Query C →ₒ HashOutput) Unit :=
  grindExtra P ρ (p.1, p.2.1) t (p'.1, p'.2.1)

/-- The joint run with an eager grind at each canonical base call. -/
def jointEagerRun (prims : Primitives) (P : PublicParameter) (ρ : KeyIndex → Digest)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (JointResult C × FlatJointState C) :=
  (jointGame (eagerWorld prims (jointGrindExtra P ρ)) A x).run jointInit

/-- The eager joint run preserves the result, count, both logs and the carried state. -/
theorem evalDist_jointEagerRun_rest (prims : Primitives) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, restOf z.2)) <$> jointEagerRun prims P ρ A x] =
      𝒟[(fun z => (z.1, restOf z.2)) <$>
        (jointGame (carry (SigningCostProof.loggedImpl prims)) A x).run jointInit] :=
  evalDist_jointGame_eq prims _ _ (hashLaw_eagerWorld prims _)
    (hashLaw_carry_logged prims) A x

/-- The eager law for `jointRun`: the result, verification candidates, count and call log have
exactly the original joint distribution. -/
theorem evalDist_jointEagerRun (prims : Primitives) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> jointEagerRun prims P ρ A x] =
      𝒟[(fun z => (z.1, z.2.1.2, z.2.2)) <$> SigningUnchargedLoggedProof.jointRun prims A x] := by
  have h := congrArg
    (fun d => (fun z : JointResult C × Rest C (OpeningState C) => (z.1, z.2.1)) <$> d)
    (evalDist_jointEagerRun_rest prims P ρ A x)
  simp only [← evalDist_map, Functor.map_map] at h
  rw [← jointGame_eq_jointRun, Functor.map_map]
  exact h

/-- Any event on the observable joint outcome transports through the eager law. -/
theorem probEvent_jointEagerRun (prims : Primitives) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (event : JointResult C × (ℕ × QueryLog (WorldSpec C)) → Prop) :
    Pr[fun z => event (z.1, z.2.1.1.2, z.2.1.2) | jointEagerRun prims P ρ A x] =
      Pr[fun z => event (z.1, z.2.1.2, z.2.2) | SigningUnchargedLoggedProof.jointRun prims A x] := by
  have h := evalDist_jointEagerRun prims P ρ A x
  have hp : Pr[event | (fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> jointEagerRun prims P ρ A x] =
      Pr[event | (fun z => (z.1, z.2.1.2, z.2.2)) <$>
        SigningUnchargedLoggedProof.jointRun prims A x] := by
    simp only [probEvent_eq_tsum_indicator, probOutput_def, h]
  simpa only [probEvent_map, Function.comp_def] using hp

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.programFree_openingOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programFree_openingOracles

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.programFree_tsigFinishLogged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programFree_tsigFinishLogged

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.programFree_verifyFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programFree_verifyFinal

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.hashLaw_jointGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hashLaw_jointGame

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.jointGame_eq_jointRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointGame_eq_jointRun

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.evalDist_jointEagerRun_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_jointEagerRun_rest

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.evalDist_jointEagerRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_jointEagerRun

/-- info: 'ThresholdLeanXmssSecurity.SigningJointEagerProof.probEvent_jointEagerRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_jointEagerRun

end SigningJointEagerProof
end ThresholdLeanXmssSecurity
