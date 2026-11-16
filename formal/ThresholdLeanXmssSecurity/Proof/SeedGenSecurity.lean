import ThresholdLeanXmssSecurity.Proof.SeedGenGames

/-!
# The hybrid halves of the setup security

This module reduces the distance claim `SetupSecurityDistance` of a setup to its two hybrid halves.

1. The hybrid `setupMixedGame` gives the emulated outputs with the dealer's hidden keys. The known
   half `SetupKnownMismatch` bounds the mismatch with the ideal outputs.
2. In the hidden half, the dealer's hidden keys are independent of the corrupt leak. So the mixed
   game is the real run whose distinguisher replaces the hidden keys by fresh ones
   (`seedGenHiddenZ`). The real run is a mixture of fixed-table reference runs on a common covering
   domain. On distinct canonical inputs, the hidden oracle cells and an independent dealer table
   exchange (the relabeling). So the hidden-half hypothesis `SetupHiddenFresh` reduces to the
   relabeled reference runs (`setupSwappedMixture`).
3. `seedGenSecurity_of_setup` and `prssSetupSecurity_of_setup` give the claims of the two setups from
   the distance claim.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

set_option pp.deepTerms false
set_option pp.maxSteps 2000

variable {C : Committee}

theorem probEvent_runWorld_fst (prims : Primitives) {β : Type} (oa : OracleComp (WorldSpec C) β)
    (Q : β → Prop) :
    Pr{let r ← runWorld prims oa}[Q r.1] = Pr{let z ← (simulateQ (worldAnswer prims) oa).run' ∅}[Q z] := by
  rw [← fst_map_runWorld, prEvent_map]


theorem accepts_eq_probOutput (prims : Primitives) (g : OracleComp (WorldSpec C) Bool) :
    accepts prims g = (Pr{let z ← (simulateQ (worldAnswer prims) g).run' ∅}[z = true]).toReal := by
  unfold accepts
  rw [probEvent_runWorld_fst prims g (fun b => b = true)]

/-! ## Two continuations of one game -/

theorem run'_bind_world (prims : Primitives) {R β : Type} (g : OracleComp (WorldSpec C) R)
    (k : R → OracleComp (WorldSpec C) β) :
    (simulateQ (worldAnswer prims) (g >>= k)).run' ∅ =
      (simulateQ (worldAnswer prims) g).run ∅ >>= fun p => (simulateQ (worldAnswer prims) (k p.1)).run' p.2 := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Two continuations of one game differ by at most the probability that they differ. -/
theorem abs_accepts_bind_sub_le_seedGen (prims : Primitives) {R : Type} (g : OracleComp (WorldSpec C) R)
    (k₁ k₂ : R → OracleComp (WorldSpec C) Bool) :
    |accepts prims (g >>= k₁) - accepts prims (g >>= k₂)| ≤
      (Pr{let r ← runWorld prims g}[k₁ r.1 ≠ k₂ r.1]).toReal := by
  let flag (k : R → OracleComp (WorldSpec C) Bool) : OracleComp (WorldSpec C) (Bool × Bool) :=
    g >>= fun r => (fun b => (b, decide (k₁ r ≠ k₂ r))) <$> k r
  have hfst (k : R → OracleComp (WorldSpec C) Bool) : Prod.fst <$> flag k = g >>= k := by
    simp only [flag, map_bind, Functor.map_map, id_map']
  have hbad (k : R → OracleComp (WorldSpec C) Bool) :
      Pr{let r ← runWorld prims (flag k)}[r.1.2 = true] =
        Pr{let r ← runWorld prims g}[k₁ r.1 ≠ k₂ r.1] := by
    rw [probEvent_runWorld_fst prims (flag k) (fun p => p.2 = true),
      probEvent_runWorld_fst prims g (fun r => k₁ r ≠ k₂ r), run'_bind_world]
    rw [StateT.run'_eq, prEvent_map, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
    apply tsum_congr
    intro p
    rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map]
    by_cases hp : k₁ p.1 ≠ k₂ p.1
    · simp [hp]
    · simp [hp]
  have heq : Pr{let r ← runWorld prims (flag k₁)}[r.1 = (true, false)] =
      Pr{let r ← runWorld prims (flag k₂)}[r.1 = (true, false)] := by
    rw [probEvent_runWorld_fst prims (flag k₁) (fun p => p = (true, false)),
      probEvent_runWorld_fst prims (flag k₂) (fun p => p = (true, false)), run'_bind_world, run'_bind_world,
      OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
    apply tsum_congr
    intro p
    congr 1
    by_cases hp : k₁ p.1 = k₂ p.1
    · rw [hp]
    · rw [simulateQ_map, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, StateT.run_map,
        prEvent_map, prEvent_map, prEvent_map, prEvent_map]
      simp [hp]
  have h := abs_accepts_sub_le_of_eq_until_bad prims (flag k₁) (flag k₂) heq
  rw [hfst, hfst, hbad, hbad, max_self] at h
  exact h

/-! ## The hybrid between the emulated and the dealt outputs -/

section Hybrid

variable {E : Type}

/-- The keys `k` with the hidden coordinates of `d`, for operator `i`. -/
def seedGenHiddenOverlay (D : C.Coalition) (i : C.Party) (k d : Keys C) : Keys C :=
  ⟨k.parameter, fun T => if KnownTo D.1 T then k.seed T else d.seed T,
    fun j => if i ∈ D.1 ∨ j ∈ D.1 then k.pairKey j else d.pairKey j⟩

/-- The emulated outputs with the hidden coordinates of the dealer. -/
def seedGenMixedProjection {σ : Type} (D : C.Coalition) (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) :
    σ × (C.Party → Option (Keys C)) :=
  (r.1, fun i => (r.2.1 i).map fun k => seedGenHiddenOverlay D i k (r.2.2 i))

/-- The hybrid game: the common game, and the distinguisher on the mixed outputs. -/
def setupMixedGame (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) Bool :=
  distinguish (seedGenMixedProjection D <$> setupCommonGame phase D A x z) Z

/-- The distance of the real run and the ideal projection of the common game in a setup of `phase`. -/
def SetupSecurityDistance (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) Z) -
      accepts prims (distinguish (seedGenIdealProjection D <$> setupCommonGame phase D A x z) Z)| ≤
        setupHashError phase C q

/-- Hidden half: the hidden keys of the real run are indistinguishable from the dealer's. -/
def SetupHiddenDistance (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (setupCommonEmulatedGame phase D A x z Z) - accepts prims (setupMixedGame phase D A x z Z)| ≤
      setupHashError phase C q / 2

/-- Known half: the simulator's programming fixes every exposed coordinate of an accepted output. -/
def SetupKnownMismatch (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let r ← runWorld prims (setupCommonGame phase D A x z)}[
      seedGenMixedProjection D r.1 ≠ seedGenIdealProjection D r.1]).toReal ≤ setupHashError phase C q / 2

theorem abs_accepts_setupMixed_ideal_le (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    |accepts prims (setupMixedGame phase D A x z Z) -
        accepts prims (distinguish (seedGenIdealProjection D <$> setupCommonGame phase D A x z) Z)| ≤
      (Pr{let r ← runWorld prims (setupCommonGame phase D A x z)}[
        seedGenMixedProjection D r.1 ≠ seedGenIdealProjection D r.1]).toReal := by
  unfold setupMixedGame distinguish
  simp only [bind_map_left]
  refine (abs_accepts_bind_sub_le_seedGen prims _ _ _).trans ?_
  apply ENNReal.toReal_mono (prEvent_ne_top _)
  apply prEvent_mono
  intro r hr he
  exact hr (by rw [he])

/-- The distance claim of a setup from its two hybrid halves. -/
theorem setupSecurityDistance_of_hybrids (phase : Phase) (prims : Primitives)
    (hH : SetupHiddenDistance (C := C) (E := E) phase prims) (hK : SetupKnownMismatch (C := C) (E := E) phase prims) :
    SetupSecurityDistance (C := C) (E := E) phase prims := by
  intro D A x z Z q hq
  rw [← setupCommonGame_real_accepts phase prims D A x z Z]
  have h₁ := hH D A x z Z q hq
  have h₂ := (abs_accepts_setupMixed_ideal_le phase prims D A x z Z).trans (hK D A x z Z q hq)
  calc _ ≤ |accepts prims (setupCommonEmulatedGame phase D A x z Z) - accepts prims (setupMixedGame phase D A x z Z)| +
        |accepts prims (setupMixedGame phase D A x z Z) -
          accepts prims (distinguish (seedGenIdealProjection D <$> setupCommonGame phase D A x z) Z)| :=
        abs_sub_le _ _ _
    _ ≤ setupHashError phase C q / 2 + setupHashError phase C q / 2 := add_le_add h₁ h₂
    _ = setupHashError phase C q := by ring

/-- The distance half of the seed generation claim from the distance claim of a setup. -/
theorem seedGenSecurityDistance_of_setup (prims : Primitives) (h : SetupSecurityDistance (C := C) (E := E) .seedGen prims) :
    SeedGenSecurityDistance (C := C) (E := E) prims := by
  intro D A x z Z q hq
  have hd := h D A x z Z q hq
  rw [setupCommonGame_seedGen_ideal, setupHashError_seedGen] at hd
  exact hd

/-- `SeedGenSecurityStatement` from the distance claim of a setup. -/
theorem seedGenSecurity_of_setup (prims : Primitives) (h : SetupSecurityDistance (C := C) (E := E) .seedGen prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  seedGenSecurity_of_distance prims (seedGenSecurityDistance_of_setup prims h)

/-- `PrssSetupSecurityStatement` from the distance claim of a setup. -/
theorem prssSetupSecurity_of_setup (prims : Primitives) (h : SetupSecurityDistance (C := C) (E := E) .prss prims) :
    PrssSetupSecurityStatement (C := C) (E := E) prims := by
  intro D A x z Z q _ hq
  refine ⟨prssSetupSimulator_queryBound prims D A x z Z q hq, ?_⟩
  let Z' : Distinguisher C A.State (Keys C) := fun r => Z (r.1, fun i => (r.2 i).map carrierPrssKeys)
  have hq' : IsQueryBounded A Z' setupRounds q := by
    obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
    exact ⟨start, step, final, hsum, hs, hr, ha, fun r => hz _⟩
  have hd := h D A x z Z' q hq'
  rw [setupHashError_prss] at hd
  have hreal : distinguish (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) x z) Z =
      distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z) Z' := by
    rw [realExecution_prssSetup]
    simp only [distinguish, bind_map_left]
    rfl
  have hideal : distinguish (idealExecution (fun oa => oa) D FprssKeys (prssSetupSimulator D A) x z) Z =
      distinguish (seedGenIdealProjection D <$> setupCommonGame .prss D A x z) Z' := by
    rw [← setupCommonGame_prss_ideal]
    simp only [distinguish, bind_map_left]
    rfl
  rw [hreal, hideal]
  exact hd

end Hybrid

/-! ## The hidden half on the real run -/

section RealHidden

variable {E : Type}

/-- The distinguisher that replaces the hidden coordinates of each output by fresh uniform keys. -/
def seedGenHiddenZ (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C)) : Distinguisher C σ (Keys C) :=
  fun r => do
    let seeds ← liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C)
    let pairs ← liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C)
    Z (r.1, fun i => (r.2 i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 seeds pairs i))

theorem simulateQ_local_sample_seedGensecurity (prims : Primitives) {α : Type} (p : ProbComp α) :
    simulateQ (localAnswer (C := C) prims) (liftComp p (LocalSpec C)) = StateT.lift p := by
  rw [show simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p from
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p]
  funext s
  change (simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p).run s = p >>= fun a => pure (a, s)
  rw [unifFwdImpl.simulateQ_run, map_eq_bind_pure_comp]
  rfl

/-- The dealer's corrupt keys, as the simulator receives them. -/
def seedGenCorruptLeak (D : C.Coalition) (d : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) :
    C.Party → Option (Keys C) :=
  fun i => if i ∈ D.1 then some (dealtKeys d.1 d.2.1 d.2.2 i) else none

theorem setupMixedGame_expand (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    setupMixedGame (phase := phase) D A x z Z = (do
      let st ← setupSimulatorStart A (corruptInputs D x) z
      let d ← free (liftComp (setupDealerSamples phase (C := C)) (LocalSpec C))
      let r ← setupEmulation phase D A st d.1 (seedGenCorruptLeak D d)
      worldRoles.adversary (Z (seedGenMixedProjection D (r.1.adversary, r.2, dealtKeys d.1 d.2.1 d.2.2)))) := by
  unfold setupMixedGame distinguish setupCommonGame setupDealerSamples seedGenCorruptLeak
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure]

theorem setupCommonEmulatedGame_expand' (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    setupCommonEmulatedGame phase D A x z Z = (do
      let st ← setupSimulatorStart A (corruptInputs D x) z
      let d ← free (liftComp (setupDealerSamples phase (C := C)) (LocalSpec C))
      let r ← setupEmulation phase D A st d.1 (seedGenCorruptLeak D d)
      worldRoles.adversary (Z (r.1.adversary, r.2))) := by
  unfold setupCommonEmulatedGame distinguish setupCommonGame setupDealerSamples seedGenCorruptLeak
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure, seedGenEmulatedProjection]

/-- Replace the coordinates in `P` of a uniform table by those of a second uniform table. -/
theorem evalDist_piecewise_uniform {ι H β : Type} [Fintype ι] [DecidableEq ι] [Fintype H] [Nonempty H]
    [SampleableType H] [SampleableType (ι → H)] (P : ι → Prop) [DecidablePred P]
    (k : (ι → H) → ProbComp β) :
    (do let f ← $ᵗ (ι → H); let g ← $ᵗ (ι → H); k (fun i => if P i then g i else f i)) =ᵈ
      (do let f ← $ᵗ (ι → H); k f) := by
  let Ψ : (ι → H) × (ι → H) → (ι → H) × (ι → H) := fun p =>
    (fun i => if P i then p.2 i else p.1 i, fun i => if P i then p.1 i else p.2 i)
  have hΨ : Function.Involutive Ψ := by
    intro p
    apply Prod.ext <;> funext i <;> by_cases h : P i <;> simp [Ψ, h]
  have e1 : (do let f ← $ᵗ (ι → H); let g ← $ᵗ (ι → H); k (fun i => if P i then g i else f i)) =
      ($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1 := by
    change _ = ((·, ·) <$> ($ᵗ (ι → H)) <*> ($ᵗ (ι → H))) >>= _
    simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Ψ]
  have e2 : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1) =ᵈ
      (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1) := by
    have h : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k (Ψ p).1) =
        (Ψ <$> ($ᵗ ((ι → H) × (ι → H)))) >>= fun p => k p.1 := by rw [bind_map_left]
    rw [h]
    exact (SampleableType.map_uniformSample_evalDistEq_of_bijective hΨ.bijective).bind_left _
  have e3 : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1) =ᵈ (($ᵗ (ι → H)) >>= k) := by
    have h : (($ᵗ ((ι → H) × (ι → H))) >>= fun p => k p.1) =
        (Prod.fst <$> ($ᵗ ((ι → H) × (ι → H)))) >>= k := by rw [bind_map_left]
    rw [h]
    refine EvalDistEq.bind_left ?_ _
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans
      (by rw [bind_pure])
  rw [e1]
  exact e2.trans e3

/-- A hidden name of the dealer's tables. -/
def SeedGenHiddenTerm (D : C.Coalition) (T : C.Term) : Prop := ¬ KnownTo D.1 T

def SeedGenHiddenPair (D : C.Coalition) (p : C.Pair) : Prop := p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1

theorem seedGenHiddenPair_pairOf (D : C.Coalition) (i j : C.Party) (h : i ≠ j) :
    SeedGenHiddenPair D (C.pairOf i j h) ↔ i ∉ D.1 ∧ j ∉ D.1 := by
  unfold SeedGenHiddenPair Committee.pairOf
  split_ifs <;> simp [and_comm]

theorem seedGenCorruptLeak_piecewise (D : C.Coalition) (parameter : PublicParameter)
    (seeds seeds' : C.Term → HashOutput) (pairs pairs' : C.Pair → HashOutput) :
    seedGenCorruptLeak D (parameter, (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T),
      (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p)) =
      seedGenCorruptLeak D (parameter, seeds, pairs) := by
  funext j
  unfold seedGenCorruptLeak
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj, dealtKeys, Option.some.injEq, Keys.mk.injEq, true_and]
    constructor
    · funext T
      by_cases hT : j ∈ C.holders T
      · have hk : ¬ SeedGenHiddenTerm D T := fun h => h ⟨j, hj, hT⟩
        simp [hT, hk]
      · simp [hT]
    · funext i
      by_cases hij : i = j
      · simp [hij]
      · have hk : ¬ SeedGenHiddenPair D (C.pairOf j i (Ne.symm hij)) := by
          rw [seedGenHiddenPair_pairOf]; exact fun h => h.1 hj
        simp [hij, hk]
  · simp [hj]

theorem seedGenHiddenOverlay_piecewise (D : C.Coalition) (i : C.Party) (k : Keys C) (parameter : PublicParameter)
    (seeds seeds' : C.Term → HashOutput) (pairs pairs' : C.Pair → HashOutput) :
    seedGenHiddenOverlay D i k (dealtKeys parameter (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T)
      (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p) i) =
      seedGenHiddenOverlay D i k (dealtKeys 0 seeds' pairs' i) := by
  unfold seedGenHiddenOverlay dealtKeys
  simp only [Keys.mk.injEq, true_and]
  constructor
  · funext T
    by_cases hT : KnownTo D.1 T
    · simp [hT]
    · have hk : SeedGenHiddenTerm D T := hT
      simp [hT, hk]
  · funext j
    by_cases hc : i ∈ D.1 ∨ j ∈ D.1
    · simp [hc]
    · simp only [if_neg hc]
      by_cases hij : j = i
      · simp [hij]
      · have hk : SeedGenHiddenPair D (C.pairOf i j (Ne.symm hij)) := by
          rw [seedGenHiddenPair_pairOf]; exact not_or.mp hc
        simp [hij, hk]

/-- The dealer's hidden coordinates can be replaced by those of an independent second dealer. -/
theorem evalDist_dealer_piecewise (phase : Phase) (D : C.Coalition) {β : Type}
    (k : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput) → ProbComp β) :
    (do
      let d ← setupDealerSamples phase (C := C)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (d.1, (fun T => if SeedGenHiddenTerm D T then seeds' T else d.2.1 T),
        (fun p => if SeedGenHiddenPair D p then pairs' p else d.2.2 p))) =ᵈ
      (setupDealerSamples phase (C := C) >>= k) := by
  unfold setupDealerSamples
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun parameter => ?_
  have hswap : (do
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T),
        (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p))) =ᵈ
      (do
      let seeds ← $ᵗ (C.Term → HashOutput)
      let seeds' ← $ᵗ (C.Term → HashOutput)
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, (fun T => if SeedGenHiddenTerm D T then seeds' T else seeds T),
        (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p))) := by
    refine EvalDistEq.bind_right _ fun seeds => ?_
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  refine hswap.trans ?_
  refine (evalDist_piecewise_uniform (SeedGenHiddenTerm D) (fun s => do
      let pairs ← $ᵗ (C.Pair → HashOutput)
      let pairs' ← $ᵗ (C.Pair → HashOutput)
      k (parameter, s, (fun p => if SeedGenHiddenPair D p then pairs' p else pairs p)))).trans ?_
  refine EvalDistEq.bind_right _ fun seeds => ?_
  exact evalDist_piecewise_uniform (SeedGenHiddenPair D) (fun p => k (parameter, seeds, p))

theorem evalDist_run'_of_run {σ α : Type} {X Y : StateT σ ProbComp α} (s : σ)
    (h : X.run s =ᵈ Y.run s) : X.run' s =ᵈ Y.run' s := by
  simp only [StateT.run'_eq]
  exact h.map _

/-- Two independent samples move before a computation. -/
theorem evalDist_bind_two_comm {α β γ δ : Type} (m : ProbComp α) (p₁ : ProbComp β)
    (p₂ : ProbComp γ) (k : α → β → γ → ProbComp δ) :
    (m >>= fun r => p₁ >>= fun a => p₂ >>= fun b => k r a b) =ᵈ
      (p₁ >>= fun a => p₂ >>= fun b => m >>= fun r => k r a b) := by
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun a => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- The mixed game is the emulated game whose distinguisher replaces the hidden keys by fresh ones. -/
theorem evalDist_setupMixedGame_hiddenZ (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    (simulateQ (worldAnswer prims) (setupMixedGame (phase := phase) D A x z Z)).run' ∅ =ᵈ
      (simulateQ (worldAnswer prims) (setupCommonEmulatedGame phase D A x z (seedGenHiddenZ D Z))).run' ∅ := by
  rw [setupMixedGame_expand, setupCommonEmulatedGame_expand']
  unfold seedGenHiddenZ
  simp only [simulateQ_bind, simulateQ_world_sample, simulateQ_world_adversary, simulateQ_local_sample_seedGensecurity]
  apply evalDist_stateT_run'_bind_congr
  intro st s
  apply evalDist_run'_of_run
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine EvalDistEq.symm ?_
  refine (EvalDistEq.bind_right _ fun d => evalDist_bind_two_comm _ _ _ _).trans ?_
  refine EvalDistEq.trans ?_ (evalDist_dealer_piecewise (phase := phase) D _)
  refine EvalDistEq.bind_right _ fun d => ?_
  refine EvalDistEq.bind_right _ fun a => ?_
  refine EvalDistEq.bind_right _ fun b => ?_
  rw [seedGenCorruptLeak_piecewise]
  simp only [seedGenMixedProjection, seedGenHiddenOverlay_piecewise]
  rfl

theorem setupMixedGame_accepts (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (setupMixedGame (phase := phase) D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) (seedGenHiddenZ D Z)) := by
  have hreal : accepts prims (distinguish (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) (seedGenHiddenZ D Z)) =
      accepts prims (setupCommonEmulatedGame phase D A x z (seedGenHiddenZ D Z)) :=
    (setupCommonGame_real_accepts phase prims D A x z _).symm
  rw [hreal, accepts_eq_probOutput, accepts_eq_probOutput,
    (evalDist_setupMixedGame_hiddenZ (phase := phase) prims D A x z Z).prEvent_eq (· = true)]

/-- Hidden half on the real run: the hidden keys of the honest outputs are indistinguishable from
fresh uniform keys. -/
def SetupHiddenFresh (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) Z) -
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) (seedGenHiddenZ D Z))| ≤
      setupHashError (phase := phase) C q / 2

theorem setupHiddenDistance_of_fresh (phase : Phase) (prims : Primitives) (h : SetupHiddenFresh (phase := phase) (C := C) (E := E) prims) :
    SetupHiddenDistance (phase := phase) (C := C) (E := E) prims := by
  intro D A x z Z q hq
  rw [setupCommonGame_real_accepts, setupMixedGame_accepts]
  exact h D A x z Z q hq

/-- The real run as a mixture of fixed-table reference runs, on every oracle domain that covers it. -/
def setupReferenceMixture (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) :
    ProbComp Bool := do
  let ht ← $ᵗ (S → HashOutput)
  let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let h := seedGenFiniteTotal prims S ht
  simulateQ (fixedLocal prims h)
    (setupReferenceLocalGame (phase := phase) prims D h (fun name => h (setupNamedInput phase parts name)) A x z Z parts)

theorem evalDist_setupReal_referenceMixture (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hS : SeedGenWorldCovered S (free (setupNormalizedLocalGame phase D A x z Z))) :
    (simulateQ (worldAnswer prims)
        (distinguish (realExecution D A noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) Z)).run' ∅ =ᵈ
      setupReferenceMixture (phase := phase) prims D A x z Z S := by
  have he := evalDist_seedGenWorld_eager prims S (free (setupNormalizedLocalGame phase D A x z Z)) hS ∅
  simp only [worldAnswer, seedGenFiniteWorld, simulateQ_free] at he
  have hc : seedGenRestrictCache S (∅ : HashCache C) = ∅ := rfl
  simp only [hc, seedGenFiniteLocal_eager_fixed, tableExtending_empty] at he
  erw [simulateQ_setupReal_eq_local]
  refine ((sameRun_setupLocal_normalized phase prims D A x z Z).run'_eq).trans (he.trans ?_)
  unfold setupReferenceMixture
  refine EvalDistEq.bind_right _ fun ht => ?_
  exact evalDist_setupNormalized_fixed_reference (phase := phase) prims D (seedGenFiniteTotal prims S ht) A x z Z

/-! ### The relabeling of the hidden keys -/

theorem seedGenMaskKeys_table_congr (D : C.Coalition) (t t' : KeyName C → HashOutput)
    (ht : ∀ name, Hidden D name → t name = t' name) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    seedGenMaskKeys D t i keys = seedGenMaskKeys D t' i keys := by
  unfold seedGenMaskKeys
  congr 2
  · funext T
    by_cases hT : KnownTo D.1 T
    · simp [hT]
    · simp only [if_neg hT]
      rw [ht (.term T) hT]
  · funext j
    by_cases hj : j = i
    · simp [hj]
    · simp only [dif_neg hj]
      by_cases hc : i ∈ D.1 ∨ j ∈ D.1
      · simp [hc]
      · simp only [if_neg hc]
        apply ht
        change (C.pairOf i j (Ne.symm hj)).1.1 ∉ D.1 ∧ (C.pairOf i j (Ne.symm hj)).1.2 ∉ D.1
        exact (seedGenHiddenPair_pairOf D i j (Ne.symm hj)).mpr (not_or.mp hc)

/-- The reference run reads its table only at the hidden names. -/
theorem setupReferenceLocalGame_table_congr (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (h : Query C → HashOutput) (t t' : KeyName C → HashOutput)
    (ht : ∀ name, Hidden D name → t name = t' name)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    setupReferenceLocalGame (phase := phase) prims D h t A x z Z parts = setupReferenceLocalGame (phase := phase) prims D h t' A x z Z parts := by
  have hk : setupReferenceKeys phase (E := E) prims D h t parts = setupReferenceKeys phase prims D h t' parts := by
    funext revealed i
    exact seedGenMaskKeys_table_congr D t t' ht i _
  have hd : setupReferenceData (phase := phase) (E := E) prims D h t parts = setupReferenceData (phase := phase) prims D h t' parts := by
    funext commitSent revealSent i
    simp only [setupReferenceData, hk]
  simp only [setupReferenceLocalGame, setupReferencePostCommit, hd]

/-- The reference mixture after the relabeling: on distinct canonical inputs, the hidden keys are an
independent dealer table, and the oracle answers the hidden canonical inputs with the dealer's keys. -/
def setupSwappedMixture (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, setupNamedInput phase parts name ∈ S) : ProbComp Bool := do
  let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
  let ht := if Function.Injective (setupNamedInput phase parts) then
    (setupFiniteHiddenSwap phase D S parts (hmem parts) p).1 else p.1
  let h := seedGenFiniteTotal prims S ht
  let table := if Function.Injective (setupNamedInput phase parts) then p.2 else
    fun name => h (setupNamedInput phase parts name)
  simulateQ (fixedLocal prims h) (setupReferenceLocalGame (phase := phase) prims D h table A x z Z parts)

theorem evalDist_setupReferenceMixture_swap (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, setupNamedInput phase parts name ∈ S) :
    setupReferenceMixture (phase := phase) prims D A x z Z S =ᵈ setupSwappedMixture (phase := phase) prims D A x z Z S hmem := by
  unfold setupReferenceMixture setupSwappedMixture
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun parts => ?_
  let F : (S → HashOutput) → ProbComp Bool := fun ht =>
    simulateQ (fixedLocal prims (seedGenFiniteTotal prims S ht))
      (setupReferenceLocalGame (phase := phase) prims D (seedGenFiniteTotal prims S ht)
        (fun name => seedGenFiniteTotal prims S ht (setupNamedInput phase parts name)) A x z Z parts)
  have hfst : (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p => F p.1) =ᵈ
      (($ᵗ (S → HashOutput)) >>= F) := by
    rw [← bind_map_left Prod.fst]
    refine EvalDistEq.bind_left ?_ _
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans
      (by rw [bind_pure])
  change (($ᵗ (S → HashOutput)) >>= F) =ᵈ _
  refine hfst.symm.trans ?_
  by_cases hinj : Function.Injective (setupNamedInput phase parts)
  · simp only [if_pos hinj]
    have hswap : (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p => F p.1) =ᵈ
        (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
          F (setupFiniteHiddenSwap phase D S parts (hmem parts) p).1) := by
      have he := (evalDist_setupFiniteHiddenSwap phase D S parts (hmem parts) hinj).bind_left
        (fun p => F p.1)
      rw [bind_map_left] at he
      exact he.symm
    refine hswap.trans ?_
    refine EvalDistEq.bind_right _ fun p => ?_
    dsimp only [F]
    have htable : ∀ name, Hidden D name →
        seedGenFiniteTotal prims S (setupFiniteHiddenSwap phase D S parts (hmem parts) p).1
          (setupNamedInput phase parts name) = p.2 name := by
      intro name hh
      rw [setupFiniteTotal_named phase prims S _ parts name (hmem parts name),
        setupFiniteHiddenSwap_cell phase D S parts (hmem parts) hinj p name hh]
    rw [setupReferenceLocalGame_table_congr (phase := phase) prims D _ _ _ htable]
  · simp only [if_neg hinj]
    rfl

end RealHidden

/-! ## The claim from the two hybrid halves -/

section Main

variable {E : Type} (prims : Primitives)

/-- `SeedGenSecurityStatement` from the two hybrid halves. -/
theorem seedGenSecurity_of_halves (hH : SetupHiddenDistance (C := C) (E := E) .seedGen prims)
    (hK : SetupKnownMismatch (C := C) (E := E) .seedGen prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  seedGenSecurity_of_setup prims (setupSecurityDistance_of_hybrids .seedGen prims hH hK)

end Main

end ThresholdLeanXmssSecurity
