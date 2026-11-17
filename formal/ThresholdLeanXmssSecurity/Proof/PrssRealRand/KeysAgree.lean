import ThresholdLeanXmssSecurity.Proof.SeedGenAlias

/-!
# The keys of one setup agree

* `KeysAgree` and `PairKeysAgree` state that two honest operators with keys hold the same key of
  each term that both hold, and the same key of their pair.
* `setupKeysAgree_of_distance` bounds the event that the keys do not agree by the error of the setup.
  The proof uses `SetupSecurityDistance` at the distinguisher that reads only the outputs. On the
  ideal side the keys are `dealtKeys`, so the event is false there.
* `prssSetupKeysAgree` is this bound for the PRSS setup.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Two honest operators with keys hold the same key of each term that both hold. -/
def KeysAgree (D : C.Coalition) (out : C.Party → Option (Keys C)) : Prop :=
  ∀ (i j : C.Party) (T : C.Term), i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
    ∀ ki ∈ out i, ∀ kj ∈ out j, ki.seed T = kj.seed T

/-- Two honest operators with keys hold the same key of their pair. -/
def PairKeysAgree (D : C.Coalition) (out : C.Party → Option (Keys C)) : Prop :=
  ∀ (i j : C.Party), i ∉ D.1 → j ∉ D.1 → i ≠ j → ∀ ki ∈ out i, ∀ kj ∈ out j, ki.pairKey j = kj.pairKey i

/-- The keys of the honest operators of a setup of `phase` agree, except with the error of the setup. -/
def SetupKeysAgree (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (q : ℕ),
    IsQueryBounded A (fun _ => pure true : Distinguisher C A.State (Keys C)) setupRounds q →
    (Pr{let r ← runWorld prims (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z)}[
      ¬ (KeysAgree D r.1.2 ∧ PairKeysAgree D r.1.2)]).toReal ≤ setupHashError phase C q

/-- Outputs that are dealt keys always agree. -/
theorem keysAgree_of_dealt (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (out : C.Party → Option (Keys C))
    (hout : ∀ i, ∀ k ∈ out i, k = dealtKeys parameter seeds pairs i) :
    KeysAgree D out ∧ PairKeysAgree D out := by
  constructor
  · intro i j T _ _ hi hj ki hki kj hkj
    rw [hout i ki hki, hout j kj hkj]
    simp only [dealtKeys, BitVec.ofNat_eq_ofNat, hi, ↓reduceIte, hj]
  · intro i j _ _ hij ki hki kj hkj
    rw [hout i ki hki, hout j kj hkj]
    have hji : j ≠ i := fun h => hij h.symm
    simp only [dealtKeys, hji, hij, dite_false]
    congr 1
    unfold Committee.pairOf
    rcases lt_trichotomy i j with h | h | h
    · simp only [h, ↓reduceDIte, not_lt_of_gt h]
    · exact absurd h hij
    · simp only [not_lt_of_gt h, ↓reduceDIte, h]

/-- The outputs of the ideal projection always agree. -/
theorem keysAgree_idealProjection {σ : Type} (D : C.Coalition)
    (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (hr : r.2.2 = dealtKeys parameter seeds pairs) :
    KeysAgree D (seedGenIdealProjection D r).2 ∧ PairKeysAgree D (seedGenIdealProjection D r).2 := by
  refine keysAgree_of_dealt D parameter seeds pairs _ fun i k hk => ?_
  simp only [seedGenIdealProjection] at hk
  split_ifs at hk
  · simp only [Option.mem_def, Option.some.injEq] at hk
    rw [← hk, hr]
  · simp only [Option.mem_def, reduceCtorEq] at hk

theorem distinguish_pure {σ O : Type} (oa : OracleComp (WorldSpec C) (σ × (C.Party → Option O)))
    (f : σ × (C.Party → Option O) → Bool) : distinguish oa (fun r => pure (f r)) = f <$> oa := by
  simp only [distinguish, worldRoles, liftComp_pure, counted, simulateQ_pure, map_eq_bind_pure_comp,
    Function.comp_def]

theorem accepts_map (prims : Primitives) {α : Type} (oa : OracleComp (WorldSpec C) α) (f : α → Bool) :
    accepts prims (f <$> oa) = (Pr{let r ← runWorld prims oa}[f r.1 = true]).toReal := by
  rw [accepts_eq_probOutput, probEvent_runWorld_fst prims oa fun r => f r = true, simulateQ_map,
    StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map, prEvent_map]

/-- The keys of a setup agree, except with the error of the setup. The proof uses the distance claim
of the setup as a black box. -/
theorem setupKeysAgree_of_distance (phase : Phase) (prims : Primitives)
    (h : SetupSecurityDistance (C := C) (E := E) phase prims) : SetupKeysAgree (C := C) (E := E) phase prims := by
  intro D A x z q hq
  let f : A.State × (C.Party → Option (Keys C)) → Bool :=
    fun r => decide (¬ (KeysAgree D r.2 ∧ PairKeysAgree D r.2))
  have hq' : IsQueryBounded A (fun r => pure (f r) : Distinguisher C A.State (Keys C)) setupRounds q := by
    obtain ⟨start, step, final, hsum, hs, hr, ha, -⟩ := hq
    exact ⟨start, step, final, hsum, hs, hr, ha, fun _ => isQueryBoundP_pure _ _ _⟩
  have hd := h D A x z (fun r => pure (f r)) q hq'
  have hideal : f <$> (seedGenIdealProjection D <$> setupCommonGame phase D A x z) =
      (fun _ => false) <$> setupCommonGame phase D A x z := by
    unfold setupCommonGame
    simp only [map_bind, map_pure]
    refine bind_congr fun st => bind_congr fun s => ?_
    rcases s with ⟨p, s, pr⟩
    refine bind_congr fun e => ?_
    rcases e with ⟨st', em⟩
    have := keysAgree_idealProjection D (st'.adversary, em, dealtKeys p s pr) p s pr rfl
    simp only [not_and, decide_implies, decide_not, dite_eq_ite, Bool.ite_true_right, this,
        decide_true, Bool.not_true, Bool.or_self, f]
  rw [distinguish_pure, distinguish_pure, hideal, accepts_map, accepts_map] at hd
  simp only [Bool.false_eq_true, prEvent_false, ENNReal.toReal_zero, sub_zero] at hd
  refine le_trans (le_of_eq ?_) ((le_abs_self _).trans hd)
  congr 1
  exact prEvent_congr _ _ _ fun r => by simp only [f, decide_eq_true_eq]

/-- The keys of the PRSS setup agree, except with the error of the setup. -/
theorem prssSetupKeysAgree (prims : Primitives) : SetupKeysAgree (C := C) (E := E) .prss prims :=
  setupKeysAgree_of_distance .prss prims (setupSecurityDistance prims .prss)

end ThresholdLeanXmssSecurity
