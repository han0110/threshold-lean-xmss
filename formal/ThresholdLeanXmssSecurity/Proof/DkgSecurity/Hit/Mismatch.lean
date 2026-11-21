import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Parts
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Glue
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.DealtAgree
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops
import ThresholdLeanXmssSecurity.Proof.SeedGenSecurity
import ThresholdLeanXmssSecurity.Proof.SeedGenAlias

/-!
# The bound of `KeyMismatch` from the common game of the seed generation

`hitMismatch` proves `HitMismatch`, the bound `seedGenHashError C q / 2` of `KeyMismatch` in the game
with the keys of the dealer and no emulated run.

* `WorldSeedGenCommon` states that `worldSeedGen` is the common game of the seed generation on the
  state, the emulated keys and the keys of the dealer. `worldSeedGen_common` proves it as an equality
  of programs.
* `hitMismatch_of_common` gives `HitMismatch` from it. The event `KeyMismatch` is fixed at the end of
  `worldSeedGen`. The seed generation in the stream world is the one of `tableNet` in the world
  (`worldSeedGen_coupling`), and `KeyMismatch` is inside the event of `SetupKnownMismatch`
  (`mixed_ne_ideal_of_keyMismatch`). The budget of `tableNet` comes from `isQueryBounded_table`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

open SeedPartition SeedEmulation

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- `KeyMismatch` on the emulated keys and the keys of the dealer gives two different projections of
the common game of the seed generation. -/
theorem mixed_ne_ideal_of_keyMismatch {σ : Type} (D : C.Coalition) (state : σ) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (hpar : ∀ i, (dealt i).parameter = parameter)
    (h : KeyMismatch D parameter dealt emu) :
    seedGenMixedProjection D (state, emu, dealt) ≠ seedGenIdealProjection D (state, emu, dealt) := by
  obtain ⟨i, keys, hi, he, hk⟩ := h
  intro heq
  have hfun := congrFun (congrArg Prod.snd heq) i
  simp only [seedGenMixedProjection, seedGenIdealProjection, he, Option.map_some, Option.isSome_some, hi,
    not_false_eq_true, and_self, ite_true, Option.some.injEq] at hfun
  rcases hk with hk | ⟨T, -, hT, hk⟩
  · have hp : keys.parameter = (dealt i).parameter :=
      congrArg Keys.parameter (a₁ := seedGenHiddenOverlay D i keys (dealt i)) hfun
    exact hk (hp.trans (hpar i))
  · have := congrFun (congrArg Keys.seed hfun) T
    simp only [seedGenHiddenOverlay, hT, ite_true] at this
    exact hk this

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The known half of the setup security for the seed generation. -/
theorem setupKnownMismatch_seedGen : SetupKnownMismatch (C := C) (E := E) .seedGen prims :=
  setupKnownMismatch_of_programFail .seedGen prims
    (setupProgramFailBound_of_alias .seedGen prims (setupProgramAliasBound .seedGen prims))

/-- `worldSeedGen` is the common game of the seed generation on the state, the emulated keys and the
keys of the dealer. -/
def WorldSeedGenCommon : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty),
    (fun r => (r.1, r.2.2.2.2, r.2.2.2.1)) <$> worldSeedGen D net = setupCommonGame .seedGen D net (fun _ => ()) []

/-- `KeyMismatch` on the outputs of a seed generation. -/
def SeedGenMismatch (D : C.Coalition) {σ : Type}
    (z : σ × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C))) : Prop :=
  KeyMismatch D z.2.1 z.2.2.2.1 z.2.2.2.2

omit [Fintype E] [DecidableEq E] in
/-- The event `MismatchOf` is fixed at the end of `worldSeedGen`. -/
theorem dealtProb_mismatch_le (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Pr{let r ← (sharedDealt prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A).run ((∅, ∅), [])}[
        MismatchOf D r] ≤
      Pr{let z ← (simulateQ (loggedWorld prims D) (worldSeedGen D A.net)).run ((∅, ∅), [])}[SeedGenMismatch D z.1] := by
  unfold sharedDealt
  rw [StateT.run_bind]
  refine prEvent_bind_le_of_imp _ _ _ _ fun z hz r hr => ?_
  obtain ⟨⟨state, parameter, seeds, dealt, emu⟩, w⟩ := z
  simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨p, -, rfl⟩ := hr
  exact hz

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The seed generation in `loggedWorld` is the one of `tableNet` in the world, on the outputs other
than the state. -/
theorem logged_mismatch_eq (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    Pr{let z ← (simulateQ (loggedWorld prims D) (worldSeedGen D net)).run ((∅, ∅), [])}[SeedGenMismatch D z.1] =
      Pr{let w ← (simulateQ (worldAnswer prims) (worldSeedGen D (tableNet prims net))).run ∅}[
        SeedGenMismatch D w.1] := by
  have hdrop := loggedWorld_drop prims D (worldSeedGen D net) (∅, ∅) []
  have hR := worldSeedGen_coupling (C := C) (E := E) prims D net ∅ ∅
  rw [merge_empty] at hR
  rw [hR] at hdrop
  have e := congrArg (fun m => Pr{let z ← m}[SeedGenMismatch D z.1]) hdrop
  simp only [prEvent_map] at e
  exact e

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `KeyMismatch` at the end of `worldSeedGen` in the world is inside the event of
`SetupKnownMismatch`. -/
theorem world_mismatch_le (common : WorldSeedGenCommon (C := C) (E := E)) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) :
    Pr{let w ← (simulateQ (worldAnswer prims) (worldSeedGen D net)).run ∅}[SeedGenMismatch D w.1] ≤
      Pr{let r ← runWorld prims (setupCommonGame .seedGen D net (fun _ => ()) [])}[
        seedGenMixedProjection D r.1 ≠ seedGenIdealProjection D r.1] := by
  rw [probEvent_runWorld_fst prims _ (fun r => seedGenMixedProjection D r ≠ seedGenIdealProjection D r),
    ← common D net, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun w hw hm => ?_
  have hsupp : w.1 ∈ support (worldSeedGen D net) :=
    support_simulateQ_run'_subset (worldAnswer prims) _ ∅ (by rw [StateT.run'_eq, support_map]; exact ⟨w, hw, rfl⟩)
  obtain ⟨pairKeys, hd⟩ := worldSeedGen_dealt D net w.1 hsupp
  refine mixed_ne_ideal_of_keyMismatch D w.1.1 w.1.2.1 w.1.2.2.2.1 w.1.2.2.2.2 (fun i => ?_) hm
  rw [hd]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- `HitMismatch` from the common game of the seed generation. -/
theorem hitMismatch_of_common (common : WorldSeedGenCommon (C := C) (E := E)) :
    HitMismatch prims K circuits settings runLimit := by
  intro D A q bounded
  obtain ⟨start, step, forge, hq, hstart, hround, -⟩ := bounded
  have hsum : start + setupRounds * step + 0 ≤ q :=
    le_trans (Nat.add_le_add_left (Nat.zero_le _) _) (budget_arith circuits settings runLimit start step forge q hq)
  have hbound : IsQueryBounded (tableNet prims A.net) (fun _ => pure true : Distinguisher C _ (Keys C)) setupRounds q :=
    isQueryBounded_table prims A.net _ start step 0 q hsum hstart hround fun _ => isQueryBoundP_pure _ _ _
  have hk := setupKnownMismatch_seedGen (E := E) prims D (tableNet prims A.net) (fun _ => ()) [] _ q hbound
  have hle := (dealtProb_mismatch_le prims K circuits settings runLimit D A).trans
    ((logged_mismatch_eq prims D A.net).trans_le (world_mismatch_le prims common D (tableNet prims A.net)))
  unfold dealtProb hitMismatchError
  rw [← setupHashError_seedGen]
  exact (ENNReal.toReal_mono (prEvent_ne_top _) hle).trans hk

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `worldSeedGen` is the common game of the seed generation on the state, the emulated keys and the
keys of the dealer. -/
theorem worldSeedGen_common (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    (fun r => (r.1, r.2.2.2.2, r.2.2.2.1)) <$> worldSeedGen D net = setupCommonGame .seedGen D net (fun _ => ()) [] := by
  unfold worldSeedGen setupCommonGame setupSimulatorStart setupDealerSamples setupParameterSample setupEmulation
    setupProgramBlock setupProgramView programParameter setupHighSample seedGenFirstHonest prawnsKeyGen
  simp only [map_bind, map_pure, liftComp_bind, liftComp_pure, free_bind, free_pure, bind_assoc, pure_bind]
  refine bind_congr fun a => ?_
  refine bind_congr fun parameter => ?_
  refine bind_congr fun seeds => ?_
  refine bind_congr fun pairs => ?_
  refine bind_congr fun parts => ?_
  have hsteps : startSteps worldRoles D (fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))) =
      startSteps worldRoles D fun i => setupWith .seedGen i (parts i) := rfl
  rw [hsteps]
  refine bind_congr fun steps => ?_
  refine bind_congr fun r => ?_
  refine bind_congr fun high => ?_
  refine bind_congr fun _ => ?_
  congr 1
  · congr 1
    funext T
    rcases hj : List.find? (fun j => decide (j ∈ D.1 ∧ j ∈ C.holders T)) C.parties with _ | j
    · rfl
    · have hD : j ∈ D.1 := by
        have := List.find?_some hj
        simp only [decide_eq_true_eq] at this
        exact this.1
      dsimp only
      congr 1
      simp [hD]
  funext _
  congr 1
  · congr 1
    funext j
    congr 1
    funext i
    by_cases h : j ∈ D.1 ∧ i ∉ D.1
    · simp [h]
    · simp only [h, dite_false]

omit [Fintype E] [DecidableEq E] in
/-- An emulated operator holds a known key that is not the key of the dealer with probability
at most `seedGenHashError C q / 2`. -/
theorem hitMismatch : HitMismatch prims K circuits settings runLimit :=
  hitMismatch_of_common prims K circuits settings runLimit worldSeedGen_common

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.hitMismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.hitMismatch
