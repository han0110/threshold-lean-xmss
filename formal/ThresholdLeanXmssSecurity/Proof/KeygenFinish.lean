import ThresholdLeanXmssSecurity.Proof.KeygenHalves
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# Keygen security: the two coupling stages

`keygenSecurityFull` of `Proof/KeygenHalves.lean` takes two stage hypotheses:
`KeygenEchoFresh` (the echo-collision core of the hidden half) and `KeygenKnownMismatch`
(the known half on the simulator's emulation).

`keygenHiddenDistanceProof` gives the hidden-half estimate.

1. `KeygenEchoFresh` holds for every covering domain `S`, but off `S` the finite oracle answers `0`.
   We choose the domain, so we add every echo input (`keygenSharedInputs`) and prove the bound there
   (`KeygenEchoFreshExt`). The chain of `KeygenHalves` and `KeygenSecurity` is redone with that domain.
2. The echo cells of the fresh table `u` are the echo inputs whose coordinate at the canonical hidden
   term of an honest pair is the fresh seed. Each fixed query is a cell with probability at most
   `|pairs| / 2^256` (`probEvent_keygenEchoCell_le`).
3. Swap the oracle on the cells with an independent copy `a'` (`evalDist_bind_keygenMix`). The prefix
   runs identically until it logs a cell (at most `q` counted calls) or an honest echo toward a corrupt
   operator is a cell (at most `n²` inputs) (`relTriple_keygenRefPrefixV`).
4. Otherwise an echo collision is a collision of two distinct cells of `a'`, `|pairs| / 2^256`.
5. The total `(1 + q + n²) |pairs| / 2^256` fits in the budget (`keygenEcho_arith`).

`KeygenKnownMismatch` is a hypothesis of `keygenSecurityComplete`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## The echo-collision bound on a domain with every echo input

`KeygenEchoFresh` quantifies over every covering domain `S`. Off `S` the finite oracle answers `0`,
so two echo inputs off `S` always collide. The domain of the proof is ours to choose
(`keygenHiddenFresh_of_reference` picks it), so we add every echo input of the keygen to it. -/

section Domain

variable {C : Committee}

/-- Every echo input `sharedKeys` of the keygen, for any pair and any seeds. -/
def keygenSharedInputs (C : Committee) : Finset (Query C) :=
  Finset.univ.biUnion fun p : C.Party × C.Party =>
    Finset.univ.image fun f : C.Term → HashOutput => Query.sharedKeys .keygen ((sharedTerms p.1 p.2).map f)

theorem keygenSharedInputs_mem (i j : C.Party) (f : C.Term → HashOutput) :
    Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ keygenSharedInputs C := by
  unfold keygenSharedInputs
  exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩

end Domain

section Chain

variable {C : Committee} {E : Type} (prims : Primitives)

/-- `KeygenEchoFresh` on a domain that holds every echo input. -/
def KeygenEchoFreshExt (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∀ (S : Finset (Query C)), (∀ parts name, keygenNamedInput parts name ∈ S) →
      (∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S) →
      (Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.1 |
        keygenPartsKernel (keygenStageBSampler prims D A x z S)]).toReal ≤
        (keygenHashError C q / 2 - 2 * keygenStageAError C q) / 2

theorem keygenAcceptGap_le_of_ext (hF : KeygenEchoFreshExt (C := C) (E := E) prims)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (S : Finset (Query C)) (hmem : ∀ parts name, keygenNamedInput parts name ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S) :
    (Pr[KeygenReceiversGap prims D A S | keygenPartsKernel (keygenStageBSampler prims D A x z S)]).toReal ≤
      keygenHashError C q / 2 - 2 * keygenStageAError C q := by
  have hb := hF D A x z Z q hq S hmem hsk
  have hle : Pr[KeygenReceiversGap prims D A S | keygenPartsKernel (keygenStageBSampler prims D A x z S)] ≤
      Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.1 |
        keygenPartsKernel (keygenStageBSampler prims D A x z S)] +
      Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.1 |
        keygenPartsKernel (keygenStageBSampler prims D A x z S)] :=
    calc _ ≤ Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.1 ∨ KeygenEchoIrregular prims D A S r r.2.2.2.2 |
          keygenPartsKernel (keygenStageBSampler prims D A x z S)] :=
          probEvent_mono fun r _ hr => keygenReceiversGap_irregular prims D A S r hr
      _ ≤ _ := probEvent_or_le _ _ _
      _ = _ := by rw [probEvent_keygenEchoIrregular_swap]
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) hle
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at ht
  linarith

theorem keygenIndepEcho_le_of_ext (hF : KeygenEchoFreshExt (C := C) (E := E) prims)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (S : Finset (Query C)) (hmem : ∀ parts name, keygenNamedInput parts name ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S) :
    |(Pr[= true | keygenIndepMixture prims D A x z Z S]).toReal -
        (Pr[= true | keygenIndepMixture prims D A x z (keygenHiddenZ D Z) S]).toReal| ≤
      keygenHashError C q / 2 - 2 * keygenStageAError C q := by
  refine le_trans ?_ (keygenAcceptGap_le_of_ext prims hF D A x z Z q hq S hmem hsk)
  have hZ : Pr[= true | keygenIndepMixture prims D A x z Z S] =
      Pr[= true | (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) >>= fun parts =>
        keygenStageBSampler prims D A x z S parts >>= fun w =>
          keygenStageBRun prims D A Z S parts w w.2.2.2 w.2.2.2] := by
    rw [probOutput_def, probOutput_def]
    exact congrArg (· true) (evalDist_bind_congr' _ fun parts => evalDist_keygenIndep_Z prims D A x z Z S parts)
  have hH : Pr[= true | keygenIndepMixture prims D A x z (keygenHiddenZ D Z) S] =
      Pr[= true | (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) >>= fun parts =>
        keygenStageBSampler prims D A x z S parts >>= fun w =>
          keygenStageBRun prims D A Z S parts w w.2.2.1 w.2.2.2] := by
    rw [probOutput_def, probOutput_def]
    exact congrArg (· true) (evalDist_bind_congr' _ fun parts =>
      evalDist_keygenIndep_hiddenZ prims D A x z Z S parts)
  rw [hZ, hH, probEvent_keygenPartsKernel_eq_tsum (keygenStageBSampler prims D A x z S)
    (fun parts w => KeygenReceiversGap prims D A S (parts, w))]
  refine abs_probOutput_bind_sub_le _ _ _ _ (fun parts => ?_) (fun parts => ?_) ?_
  · exact keygenStageB_parts prims D A x z Z S parts (fun w => w.2.2.2) (fun w => w.2.2.1) fun w hw => Ne.symm hw
  · exact keygenStageB_parts prims D A x z Z S parts (fun w => w.2.2.1) (fun w => w.2.2.2) fun w hw => hw
  · rw [← probEvent_keygenPartsKernel_eq_tsum (keygenStageBSampler prims D A x z S)
      (fun parts w => KeygenReceiversGap prims D A S (parts, w))]
    exact probEvent_ne_top

theorem keygenSwapped_le_of_ext (hF : KeygenEchoFreshExt (C := C) (E := E) prims)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (S : Finset (Query C)) (hmem : ∀ parts name, keygenNamedInput parts name ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S) :
    |(Pr[= true | keygenSwappedMixture prims D A x z Z S hmem]).toReal -
        (Pr[= true | keygenSwappedMixture prims D A x z (keygenHiddenZ D Z) S hmem]).toReal| ≤
      keygenHashError C q / 2 := by
  have hA₁ := keygenStageA prims D A x z Z S hmem q hq
  have hA₂ := keygenStageA prims D A x z (keygenHiddenZ D Z) S hmem q (isQueryBounded_keygenHiddenZ D A Z q hq)
  have hb := keygenIndepEcho_le_of_ext prims hF D A x z Z q hq S hmem hsk
  unfold keygenStageAError at hb
  calc _ ≤ |(Pr[= true | keygenSwappedMixture prims D A x z Z S hmem]).toReal -
          (Pr[= true | keygenIndepMixture prims D A x z Z S]).toReal| +
        |(Pr[= true | keygenIndepMixture prims D A x z Z S]).toReal -
          (Pr[= true | keygenIndepMixture prims D A x z (keygenHiddenZ D Z) S]).toReal| +
        |(Pr[= true | keygenIndepMixture prims D A x z (keygenHiddenZ D Z) S]).toReal -
          (Pr[= true | keygenSwappedMixture prims D A x z (keygenHiddenZ D Z) S hmem]).toReal| := by
        refine (abs_sub_le _ (Pr[= true | keygenIndepMixture prims D A x z (keygenHiddenZ D Z) S]).toReal _).trans ?_
        gcongr
        exact abs_sub_le _ _ _
    _ ≤ _ := by
        rw [abs_sub_comm ((Pr[= true | keygenIndepMixture prims D A x z (keygenHiddenZ D Z) S]).toReal)]
        linarith

/-- The hidden half on the real run, from the echo-collision bound on the extended domain. -/
theorem keygenHiddenFresh_of_echoFreshExt (hF : KeygenEchoFreshExt (C := C) (E := E) prims) :
    KeygenHiddenFresh (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨S₁, h₁⟩ := keygenWorldCovered_exists (free (keygenNormalizedLocalGame D A x z Z))
  obtain ⟨S₂, h₂⟩ := keygenWorldCovered_exists (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z)))
  let S := S₁ ∪ S₂ ∪ keygenAllNamedInputs C ∪ keygenSharedInputs C
  have hS₁ : KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z)) :=
    h₁.mono fun _ hq => by simp only [S, Finset.mem_union]; tauto
  have hS₂ : KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z))) :=
    h₂.mono fun _ hq => by simp only [S, Finset.mem_union]; tauto
  have hmem : ∀ parts name, keygenNamedInput parts name ∈ S := fun parts name => by
    have := keygenAllNamedInputs_mem parts name
    simp only [S, Finset.mem_union]; tauto
  have hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S :=
    fun i j f => Finset.mem_union_right _ (keygenSharedInputs_mem i j f)
  rw [accepts_eq_probOutput, accepts_eq_probOutput, probOutput_def, probOutput_def,
    evalDist_keygenReal_referenceMixture prims D A x z Z S hS₁,
    evalDist_keygenReal_referenceMixture prims D A x z (keygenHiddenZ D Z) S hS₂,
    evalDist_keygenReferenceMixture_swap prims D A x z Z S hmem,
    evalDist_keygenReferenceMixture_swap prims D A x z (keygenHiddenZ D Z) S hmem,
    ← probOutput_def, ← probOutput_def]
  exact keygenSwapped_le_of_ext prims hF D A x z Z q hq S hmem hsk

end Chain

/-! ## Two fixed oracles on a computation with an extra bad event -/

section LogCoupling

open OracleComp.ProgramLogic.Relational

variable {C : Committee} (prims : Primitives)

/-- A bind of a step that agrees until a logged point of `P` with continuations that agree until a
logged point of `P` or a bad output `Q`. -/
theorem relTriple_log_bind (h₁ h₂ : Query C → HashOutput) (P : Query C → Prop) {α β : Type}
    (Q : β → Prop) (oa : OracleComp (LocalSpec C) α) (k₁ k₂ : α → OracleComp (LocalSpec C) β)
    (hoa : RelTriple (simulateQ (fixedLocal prims h₂) (keygenHashLog oa)) (simulateQ (fixedLocal prims h₁) oa)
      (fun x y => (∃ v ∈ x.2, P v) ∨ x.1 = y))
    (hk : ∀ a, RelTriple (simulateQ (fixedLocal prims h₂) (keygenHashLog (k₂ a)))
      (simulateQ (fixedLocal prims h₁) (k₁ a)) (fun x y => (∃ v ∈ x.2, P v) ∨ Q x.1 ∨ x.1 = y)) :
    RelTriple (simulateQ (fixedLocal prims h₂) (keygenHashLog (oa >>= k₂)))
      (simulateQ (fixedLocal prims h₁) (oa >>= k₁)) (fun x y => (∃ v ∈ x.2, P v) ∨ Q x.1 ∨ x.1 = y) := by
  rw [keygenHashLog_bind]
  simp only [simulateQ_bind]
  refine relTriple_bind hoa fun x y hxy => ?_
  rcases hxy with ⟨v, hv, hp⟩ | he
  · refine relTriple_of_support_left fun z hz _ => Or.inl ?_
    simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact ⟨v, List.mem_append_left _ hv, hp⟩
  · subst he
    simp only [simulateQ_bind, simulateQ_pure]
    rw [← bind_pure (simulateQ (fixedLocal prims h₁) (k₁ x.1))]
    refine relTriple_bind (hk x.1) fun w b hwb => relTriple_pure_pure ?_
    rcases hwb with ⟨v, hv, hp⟩ | hq | he
    · exact Or.inl ⟨v, List.mem_append_right _ hv, hp⟩
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr he)

variable {E : Type}

/-- `keygenRefPrefix` with the echo view of the third round as a parameter. -/
def keygenRefPrefixV (D : C.Coalition) (h : Query C → HashOutput)
    (V : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) := do
  let state ← A.start (corruptInputs D x) z
  let r ← A.round state (keygenFixedCommitView prims D h parts)
  if ∀ i, i ∉ D.1 → keygenCommitAborted D r.2 i = true then pure (r.1, none) else do
    let r' ← A.round r.1 (keygenReferenceRevealView D parts r.2)
    if ∀ i, i ∉ D.1 → ¬ keygenReferenceActive D h r.2 r'.2 i then pure (r'.1, none) else do
      let r'' ← A.round r'.1 (V r.2 r'.2)
      pure (r''.1, some (r.2, r'.2, r''.2))

theorem keygenRefPrefix_eq_V (D : C.Coalition) (h : Query C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    keygenRefPrefix prims D h A x z parts = keygenRefPrefixV prims D h (keygenRefVisible prims D h parts) A x z parts :=
  rfl

/-- The two echo views of a transcript differ. -/
def KeygenViewDiff {σ : Type}
    (V₁ V₂ : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : Prop :=
  match π.2 with
  | none => False
  | some (s, rs, _) => V₁ s rs ≠ V₂ s rs

/-- Two fixed oracles that agree off `P` and two echo views run the prefix identically until a
logged point of `P` or a transcript whose two echo views differ. -/
theorem relTriple_keygenRefPrefixV (D : C.Coalition) (h₀ h₁ h₂ : Query C → HashOutput) (P : Query C → Prop)
    (hP : ∀ v, ¬ P v → h₁ v = h₂ v)
    (V₁ V₂ : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    RelTriple (simulateQ (fixedLocal prims h₂) (keygenHashLog (keygenRefPrefixV prims D h₀ V₂ A x z parts)))
      (simulateQ (fixedLocal prims h₁) (keygenRefPrefixV prims D h₀ V₁ A x z parts))
      (fun x y => (∃ v ∈ x.2, P v) ∨ KeygenViewDiff V₁ V₂ x.1 ∨ x.1 = y) := by
  unfold keygenRefPrefixV
  refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun state => ?_
  refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun r => ?_
  split_ifs with h1
  · simp only [keygenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr rfl))
  refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun r' => ?_
  split_ifs with h2
  · simp only [keygenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr rfl))
  by_cases hv : V₁ r.2 r'.2 = V₂ r.2 r'.2
  · rw [hv]
    refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun r'' => ?_
    simp only [keygenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr rfl))
  · refine relTriple_of_support_left fun w hw _ => Or.inr (Or.inl ?_)
    rw [keygenHashLog_bind] at hw
    simp only [simulateQ_bind, simulateQ_pure, keygenHashLog_pure, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨w', -, _, rfl, rfl⟩ := hw
    exact hv

theorem keygenReferenceKeys_congr_derive (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (hd : ∀ ph k l, h₁ (.derive ph k l) = h₂ (.derive ph k l)) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :
    keygenReferenceKeys prims D h₁ table parts revealed i = keygenReferenceKeys prims D h₂ table parts revealed i := by
  simp only [keygenReferenceKeys, D_deriveKeys, hd]

/-- The echo inputs of an honest operator toward a corrupt one, under the zero table. -/
def keygenVisiblePoint (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (rs : C.Party → Mail C E) (i c : C.Party) : Query C :=
  .sharedKeys .keygen ((sharedTerms i c).map
    (keygenReferenceKeys prims D h (fun _ => 0) parts (fun i j => rs j i) i).2.1)

/-- The corrupt recipients' echo view reads the oracle off the commitments and the derivations only
at the echo inputs toward corrupt operators. -/
theorem keygenRefVisible_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (hc : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l))
    (hd : ∀ ph k l, h₁ (.derive ph k l) = h₂ (.derive ph k l))
    (parts : C.Party → Parts C) (s rs : C.Party → Mail C E)
    (hpt : ∀ i c, i ∉ D.1 → c ∈ D.1 →
      h₁ (keygenVisiblePoint prims D h₁ parts rs i c) = h₂ (keygenVisiblePoint prims D h₁ parts rs i c)) :
    keygenRefVisible prims D h₁ parts s rs = keygenRefVisible prims D h₂ parts s rs := by
  funext c i
  unfold keygenRefVisible
  split_ifs with hci
  · have hactive : keygenReferenceActive D h₁ s rs i ↔ keygenReferenceActive D h₂ s rs i := by
      simp only [keygenReferenceActive, keygenReferenceOpenCheck, hc]
    rw [keygenReferenceData_active, keygenReferenceData_active]
    by_cases ha : keygenReferenceActive D h₁ s rs i
    · rw [if_pos ha, if_pos (hactive.1 ha)]
      simp only [keygenEchoDataStep, Step.outbox, echoOutbox]
      congr 2
      simp only [echoOf, ite_true, D_sharedQueries_at]
      rw [← keygenReferenceKeys_congr_derive prims D h₁ h₂ hd]
      have := hpt i c hci.2 hci.1
      unfold keygenVisiblePoint at this
      rw [this]
    · rw [if_neg ha, if_neg (fun h => ha (hactive.2 h))]
  · rfl

theorem keygenRefPrefixV_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (hc : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l))
    (V : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    keygenRefPrefixV prims D h₁ V A x z parts = keygenRefPrefixV prims D h₂ V A x z parts := by
  have hcv : keygenFixedCommitView (E := E) prims D h₁ parts = keygenFixedCommitView prims D h₂ parts := by
    funext c i
    simp only [keygenFixedCommitView, D_commitQueries, hc]
  have hactive : ∀ s rs i, keygenReferenceActive (E := E) D h₁ s rs i ↔ keygenReferenceActive D h₂ s rs i := by
    intro s rs i
    simp only [keygenReferenceActive, keygenReferenceOpenCheck, hc]
  simp only [keygenRefPrefixV, hcv, hactive]

end LogCoupling

/-! ## The echo cells of a fresh table -/

section Cells

variable {C : Committee}

/-- The coordinate `k` of an echo input. -/
def keygenEchoAt : Query C → ℕ → HashOutput
  | .sharedKeys _ l, k => l.getD k 0
  | _, _ => 0

/-- The echo cells of the fresh table `u`: an echo input whose coordinate at the canonical hidden term
of an honest pair is the fresh seed of that term. -/
def KeygenEchoCell (D : C.Coalition) (u : KeygenFresh C) (v : Query C) : Prop :=
  ∃ p : C.Pair, ∃ hs : KeygenShareHidden D p.1.1 p.1.2, p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧
    ∃ l, v = Query.sharedKeys .keygen l ∧
      l.getD ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)) 0 = u.1 (Classical.choose hs)

theorem keygenEchoCell_sharedKeys {D : C.Coalition} {u : KeygenFresh C} {v : Query C}
    (h : KeygenEchoCell D u v) : ∃ l, v = Query.sharedKeys .keygen l := by
  obtain ⟨_, _, _, _, l, hl, _⟩ := h
  exact ⟨l, hl⟩

theorem probEvent_fun_apply_eq {ι : Type} [Fintype ι] [DecidableEq ι] (T : ι) (c : HashOutput) :
    Pr[fun f : ι → HashOutput => f T = c | $ᵗ (ι → HashOutput)] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample]
  have hfil : (Finset.univ.filter fun s : ι → HashOutput => s T = c).card =
      Fintype.card HashOutput ^ (Fintype.card ι - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset HashOutput) T (Finset.mem_univ c)
    simpa using this
  have hk : Fintype.card ι = (Fintype.card ι - 1) + 1 := by have := Fintype.card_pos_iff.2 ⟨T⟩; omega
  have hP : (Fintype.card HashOutput : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card HashOutput := Fintype.card_pos_iff.2 ⟨c⟩
    exact_mod_cast this.ne'
  rw [hfil, Fintype.card_fun, hk, pow_succ, Nat.cast_mul, Nat.add_sub_cancel]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP))))
    (Or.inl (by simp))]
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP)))
    (ENNReal.natCast_ne_top _), one_mul]

/-- Two distinct cells of a uniform function collide with probability `1 / 2^256`. -/
theorem probEvent_fun_collide {ι : Type} [Fintype ι] [DecidableEq ι] {s₁ s₂ : ι} (hne : s₁ ≠ s₂) :
    Pr[fun f : ι → HashOutput => f s₁ = f s₂ | $ᵗ (ι → HashOutput)] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let φ : (ι → HashOutput) → (ι → HashOutput) := fun f => Function.update f s₁ (f s₁ + f s₂)
  have hφ : Function.Bijective φ := by
    refine Function.bijective_iff_has_inverse.mpr ⟨fun f => Function.update f s₁ (f s₁ - f s₂), ?_, ?_⟩ <;>
      intro f <;> funext k <;> by_cases hk : k = s₁
    · subst hk; simp [φ, Function.update_of_ne hne.symm, BitVec.add_sub_cancel]
    · simp [φ, Function.update_of_ne hk]
    · subst hk; simp [φ, Function.update_of_ne hne.symm, BitVec.sub_add_cancel]
    · simp [φ, Function.update_of_ne hk]
  have he : ∀ P : (ι → HashOutput) → Prop, Pr[P | $ᵗ (ι → HashOutput)] =
      Pr[P | φ <$> ($ᵗ (ι → HashOutput))] := by
    intro P
    simp only [probEvent_eq_tsum_ite, probOutput_map_bijective_uniformSample _ hφ]
  rw [he, probEvent_map, ← probEvent_fun_apply_eq s₁ 0]
  congr 1
  funext f
  simp only [Function.comp_apply, φ, Function.update_self, Function.update_of_ne hne.symm]
  apply propext
  constructor
  · intro h
    have := congrArg (· - f s₂) h
    simpa [BitVec.add_sub_cancel] using this
  · intro h
    rw [h]
    exact BitVec.zero_add _

/-- The cells of `a'` on `P` and of `a` elsewhere. -/
def keygenMix {ι : Type} (P : ι → Prop) (a a' : ι → HashOutput) : ι → HashOutput :=
  fun s => if P s then a' s else a s

/-- Replacing the cells of a uniform function on a set by the cells of an independent copy keeps it
uniform. -/
theorem evalDist_bind_keygenMix {ι β : Type} [Fintype ι] [DecidableEq ι] (P : ι → Prop)
    (k : (ι → HashOutput) → ProbComp β) :
    𝒟[($ᵗ ((ι → HashOutput) × (ι → HashOutput))) >>= fun p => k (keygenMix P p.1 p.2)] =
      𝒟[($ᵗ (ι → HashOutput)) >>= k] := by
  let ψ : (ι → HashOutput) × (ι → HashOutput) → (ι → HashOutput) × (ι → HashOutput) :=
    fun p => (keygenMix P p.1 p.2, keygenMix P p.2 p.1)
  have hψ : Function.Bijective ψ := by
    refine Function.bijective_iff_has_inverse.mpr ⟨ψ, ?_, ?_⟩ <;> intro p <;>
      refine Prod.ext (funext fun s => ?_) (funext fun s => ?_) <;> by_cases hs : P s <;>
      simp [ψ, keygenMix, hs]
  have hu : 𝒟[ψ <$> ($ᵗ ((ι → HashOutput) × (ι → HashOutput)))] =
      𝒟[$ᵗ ((ι → HashOutput) × (ι → HashOutput))] :=
    evalDist_ext fun y => probOutput_map_bijective_uniformSample _ hψ y
  have hm : 𝒟[(fun p => keygenMix P p.1 p.2) <$> ($ᵗ ((ι → HashOutput) × (ι → HashOutput)))] =
      𝒟[$ᵗ (ι → HashOutput)] := by
    have he : (fun p : (ι → HashOutput) × (ι → HashOutput) => keygenMix P p.1 p.2) <$>
        ($ᵗ ((ι → HashOutput) × (ι → HashOutput))) =
        Prod.fst <$> (ψ <$> ($ᵗ ((ι → HashOutput) × (ι → HashOutput)))) := by
      rw [Functor.map_map]
    rw [he, evalDist_map, hu, ← evalDist_map, evalDist_map_fst_uniformSample_prod]
  rw [← bind_map_left (fun p : (ι → HashOutput) × (ι → HashOutput) => keygenMix P p.1 p.2), evalDist_bind, hm,
    ← evalDist_bind]

theorem probEvent_fresh_term_eq (T : C.Term) (c : HashOutput) :
    Pr[fun u : KeygenFresh C => u.1 T = c | $ᵗ (KeygenFresh C)] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have h : Pr[fun u : KeygenFresh C => u.1 T = c | $ᵗ (KeygenFresh C)] =
      Pr[fun f : C.Term → HashOutput => f T = c | Prod.fst <$> ($ᵗ (KeygenFresh C))] := by
    rw [probEvent_map]
    rfl
  rw [h, probEvent_eq_tsum_ite, ← probEvent_fun_apply_eq T c, probEvent_eq_tsum_ite]
  refine tsum_congr fun f => ?_
  rw [probOutput_def, probOutput_def, evalDist_map_fst_uniformSample_prod]
  split_ifs
  · rw [← probOutput_def, ← probOutput_def, probOutput_uniformSample, probOutput_uniformSample]
  · rfl

/-- A fixed query is an echo cell of a fresh table with probability at most `|pairs| / 2^256`. -/
theorem probEvent_keygenEchoCell_le (D : C.Coalition) (v : Query C) :
    Pr[fun u => KeygenEchoCell D u v | $ᵗ (KeygenFresh C)] ≤
      (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc _ = Pr[fun u => ∃ p ∈ (Finset.univ : Finset C.Pair), ∃ hs : KeygenShareHidden D p.1.1 p.1.2,
        p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ ∃ l, v = Query.sharedKeys .keygen l ∧
          l.getD ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)) 0 = u.1 (Classical.choose hs) |
        $ᵗ (KeygenFresh C)] := by simp [KeygenEchoCell]
    _ ≤ ∑ p : C.Pair, Pr[fun u => ∃ hs : KeygenShareHidden D p.1.1 p.1.2,
        p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ ∃ l, v = Query.sharedKeys .keygen l ∧
          l.getD ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)) 0 = u.1 (Classical.choose hs) |
        $ᵗ (KeygenFresh C)] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hs : KeygenShareHidden D p.1.1 p.1.2
        · rw [← probEvent_fresh_term_eq (Classical.choose hs)
            (keygenEchoAt v ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)))]
          refine probEvent_mono fun u _ hu => ?_
          obtain ⟨hs', -, -, l, rfl, hl⟩ := hu
          rw [← hl]
          rfl
        · refine le_trans (le_of_eq ?_) (zero_le')
          rw [probEvent_eq_zero_iff]
          intro u _ hu
          exact hs hu.1
    _ = _ := by simp

theorem list_map_getD_idxOf {α β : Type} [BEq α] [LawfulBEq α] (l : List α) (f : α → β) (d : β) (T : α)
    (hT : T ∈ l) : (l.map f).getD (l.idxOf T) d = f T := by
  have hlt : l.idxOf T < l.length := List.idxOf_lt_length_iff.mpr hT
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

theorem mem_sharedTerms {i j : C.Party} {T : C.Term} (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) :
    T ∈ sharedTerms i j := by
  simp [sharedTerms, Committee.terms, hi, hj]

theorem keygenShareHidden_comm {D : C.Coalition} {i j : C.Party} (hs : KeygenShareHidden D i j) :
    KeygenShareHidden D j i := by
  obtain ⟨T, h1, h2, h3⟩ := hs
  exact ⟨T, h1, h3, h2⟩

/-- An echo input of an honest pair that shares a hidden term, with the fresh seeds at the hidden
terms, is an echo cell. -/
theorem keygenEchoCell_of (D : C.Coalition) (u : KeygenFresh C) {i j : C.Party} (hij : i ≠ j)
    (hi : i ∉ D.1) (hj : j ∉ D.1) (hs : KeygenShareHidden D i j) (f : C.Term → HashOutput)
    (hf : ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → f T = u.1 T) :
    KeygenEchoCell D u (.sharedKeys .keygen ((sharedTerms i j).map f)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨⟨(i, j), h⟩, hs, hi, hj, _, rfl, ?_⟩
    have hT := Classical.choose_spec hs
    exact (list_map_getD_idxOf (sharedTerms i j) f 0 _ (mem_sharedTerms hT.2.1 hT.2.2)).trans
      (hf _ hT.1 hT.2.1 hT.2.2)
  · have hs' := keygenShareHidden_comm hs
    refine ⟨⟨(j, i), h⟩, hs', hj, hi, _, rfl, ?_⟩
    have hT := Classical.choose_spec hs'
    have he : (sharedTerms i j).map f = (sharedTerms j i).map f := by rw [sharedTerms_comm i j]
    rw [he]
    exact (list_map_getD_idxOf (sharedTerms j i) f 0 _ (mem_sharedTerms hT.2.1 hT.2.2)).trans
      (hf _ hT.1 hT.2.2 hT.2.1)

end Cells

/-! ## The echo collision on one choice of parts -/

section EchoFresh

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The fresh table `u` makes an echo collision on a pair of honest operators that share a hidden
term, under the oracle `h`. -/
def keygenIrr (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (u : KeygenFresh C) : Prop :=
  match π.2 with
  | none => False
  | some (_, rs, _) => ¬ KeygenEchoRegularHidden D h
      (keygenReferenceKeys prims D h (keygenTableOf u.1 u.2) parts (fun i j => rs j i))

/-- The echo input of `i` toward `j`, as a cell of the domain. -/
def keygenEchoPt (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (rs : C.Party → Mail C E) (u : KeygenFresh C)
    (i j : C.Party) : S :=
  ⟨.sharedKeys .keygen ((sharedTerms i j).map
    (keygenReferenceKeys prims D h (keygenTableOf u.1 u.2) parts (fun i j => rs j i) i).2.1), hsk i j _⟩

/-- Two distinct echo inputs of a pair collide in `a'`. -/
def KeygenCollide (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (u : KeygenFresh C) (a' : S → HashOutput) : Prop :=
  match π.2 with
  | none => False
  | some (_, rs, _) => ∃ p : C.Pair,
      keygenEchoPt prims D S hsk h parts rs u p.1.1 p.1.2 ≠ keygenEchoPt prims D S hsk h parts rs u p.1.2 p.1.1 ∧
      a' (keygenEchoPt prims D S hsk h parts rs u p.1.1 p.1.2) = a' (keygenEchoPt prims D S hsk h parts rs u p.1.2 p.1.1)

theorem keygenFiniteTotal_mix_off (D : C.Coalition) (S : Finset (Query C)) (u : KeygenFresh C)
    (a a' : S → HashOutput) (v : Query C) (hv : ¬ KeygenEchoCell D u v) :
    keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a') v =
      keygenFiniteTotal prims S a v := by
  cases v <;> simp [keygenFiniteTotal, keygenMix, hv]

theorem keygenFiniteTotal_mix_cell (D : C.Coalition) (S : Finset (Query C)) (u : KeygenFresh C)
    (a a' : S → HashOutput) (v : Query C) (hv : KeygenEchoCell D u v) (hS : v ∈ S) :
    keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a') v = a' ⟨v, hS⟩ := by
  obtain ⟨l, rfl⟩ := keygenEchoCell_sharedKeys hv
  simp [keygenFiniteTotal, keygenMix, hv, hS]

theorem keygenReferenceKeys_hidden (D : C.Coalition) (h : Query C → HashOutput) (u : KeygenFresh C)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (hi : i ∈ C.holders T) :
    (keygenReferenceKeys prims D h (keygenTableOf u.1 u.2) parts revealed i).2.1 T = u.1 T := by
  simp [keygenReferenceKeys, keygenMaskKeys, hT, hi, keygenTableOf]

/-- An echo collision under the mixed oracle is a collision of two distinct cells of `a'`. -/
theorem keygenIrr_mix_collide (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) (a a' : S → HashOutput) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (u : KeygenFresh C)
    (hI : keygenIrr prims D (keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a'))
      parts π u) :
    KeygenCollide prims D S hsk (keygenFiniteTotal prims S a) parts π u a' := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · exact hI.elim
  simp only [keygenIrr, KeygenEchoRegularHidden] at hI
  push Not at hI
  obtain ⟨i, j, hi, hj, hs, heq, hne⟩ := hI
  have hd : ∀ ph k l, keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a')
      (.derive ph k l) = keygenFiniteTotal prims S a (.derive ph k l) := fun ph k l =>
    keygenFiniteTotal_mix_off prims D S u a a' _ fun hc => by
      obtain ⟨l', hl'⟩ := keygenEchoCell_sharedKeys hc
      cases hl'
  simp only [keygenReferenceKeys_congr_derive prims D _ _ hd] at heq hne
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  have hcx := keygenEchoCell_of D u hij hi hj hs
    (keygenReferenceKeys prims D (keygenFiniteTotal prims S a) (keygenTableOf u.1 u.2) parts
      (fun i j => rs j i) i).2.1 fun T hT hiT _ =>
    keygenReferenceKeys_hidden prims D _ u parts (fun i j => rs j i) i T hT hiT
  have hcy := keygenEchoCell_of D u hij.symm hj hi (keygenShareHidden_comm hs)
    (keygenReferenceKeys prims D (keygenFiniteTotal prims S a) (keygenTableOf u.1 u.2) parts
      (fun i j => rs j i) j).2.1 fun T hT hjT _ =>
    keygenReferenceKeys_hidden prims D _ u parts (fun i j => rs j i) j T hT hjT
  rw [keygenFiniteTotal_mix_cell prims D S u a a' _ hcx (hsk _ _ _),
    keygenFiniteTotal_mix_cell prims D S u a a' _ hcy (hsk _ _ _)] at heq
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨⟨(i, j), h⟩, fun he => hne (congrArg Subtype.val he), heq⟩
  · refine ⟨⟨(j, i), h⟩, fun he => hne (congrArg Subtype.val he).symm, heq.symm⟩

theorem probEvent_keygenCollide_le (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (u : KeygenFresh C) :
    Pr[fun a' => KeygenCollide prims D S hsk h parts π u a' | $ᵗ (S → HashOutput)] ≤
      (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · simp [KeygenCollide]
  let pt := keygenEchoPt prims D S hsk h parts rs u
  calc _ = Pr[fun a' => ∃ p ∈ (Finset.univ : Finset C.Pair), pt p.1.1 p.1.2 ≠ pt p.1.2 p.1.1 ∧
        a' (pt p.1.1 p.1.2) = a' (pt p.1.2 p.1.1) | $ᵗ (S → HashOutput)] := by simp [KeygenCollide, pt]
    _ ≤ ∑ p : C.Pair, Pr[fun a' => pt p.1.1 p.1.2 ≠ pt p.1.2 p.1.1 ∧
        a' (pt p.1.1 p.1.2) = a' (pt p.1.2 p.1.1) | $ᵗ (S → HashOutput)] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hne : pt p.1.1 p.1.2 = pt p.1.2 p.1.1
        · refine le_trans (le_of_eq ?_) (zero_le')
          rw [probEvent_eq_zero_iff]
          intro a' _ ha'
          exact ha'.1 hne
        · rw [← probEvent_fun_collide hne]
          exact probEvent_mono fun a' _ ha' => ha'.2
    _ = _ := by simp

/-- An honest echo input toward a corrupt operator is an echo cell. -/
def KeygenHonestHit (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (u : KeygenFresh C) : Prop :=
  match π.2 with
  | none => False
  | some (_, rs, _) => ∃ i c : C.Party, KeygenEchoCell D u (keygenVisiblePoint prims D h parts rs i c)

theorem keygenHonestHit_of_viewDiff (D : C.Coalition) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (a a' : S → HashOutput) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (u : KeygenFresh C)
    (hv : KeygenViewDiff
      (keygenRefVisible prims D (keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a')) parts)
      (keygenRefVisible prims D (keygenFiniteTotal prims S a) parts) π) :
    KeygenHonestHit prims D (keygenFiniteTotal prims S a) parts π u := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · exact hv.elim
  simp only [KeygenViewDiff] at hv
  simp only [KeygenHonestHit]
  by_contra hn
  push Not at hn
  have hoff := keygenFiniteTotal_mix_off prims D S u a a'
  refine hv (keygenRefVisible_congr prims D _ _ (fun ph b c l => ?_) (fun ph k l => ?_) parts s rs ?_).symm
  · exact (hoff _ fun hc => by obtain ⟨l', hl'⟩ := keygenEchoCell_sharedKeys hc; cases hl').symm
  · exact (hoff _ fun hc => by obtain ⟨l', hl'⟩ := keygenEchoCell_sharedKeys hc; cases hl').symm
  · intro i c _ _
    exact (hoff _ (hn i c)).symm

theorem probEvent_keygenHonestHit_le (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    {σ : Type} (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :
    Pr[fun u => KeygenHonestHit prims D h parts π u | $ᵗ (KeygenFresh C)] ≤
      ((C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · simp [KeygenHonestHit]
  calc _ = Pr[fun u => ∃ p ∈ (Finset.univ : Finset (C.Party × C.Party)),
        KeygenEchoCell D u (keygenVisiblePoint prims D h parts rs p.1 p.2) | $ᵗ (KeygenFresh C)] := by
        simp [KeygenHonestHit]
    _ ≤ ∑ p : C.Party × C.Party, Pr[fun u => KeygenEchoCell D u (keygenVisiblePoint prims D h parts rs p.1 p.2) |
        $ᵗ (KeygenFresh C)] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _p : C.Party × C.Party, (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun p _ => probEvent_keygenEchoCell_le D _
    _ = _ := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Committee.Party]

theorem probEvent_keygenLogHit_le (D : C.Coalition) (log : List (Query C)) (m : ℕ)
    (hm : (log.filter fun v => ¬ IsFixed v).length ≤ m) :
    Pr[fun u => ∃ v ∈ log, KeygenEchoCell D u v | $ᵗ (KeygenFresh C)] ≤
      (m : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  let L := (log.filter fun v => ¬ IsFixed v).toFinset
  calc _ ≤ Pr[fun u => ∃ v ∈ L, KeygenEchoCell D u v | $ᵗ (KeygenFresh C)] := by
        refine probEvent_mono fun u _ hu => ?_
        obtain ⟨v, hv, hc⟩ := hu
        refine ⟨v, ?_, hc⟩
        simp only [L, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        refine ⟨hv, ?_⟩
        rintro ⟨input, rfl, -⟩
        obtain ⟨l, hl⟩ := keygenEchoCell_sharedKeys hc
        cases hl
    _ ≤ ∑ v ∈ L, Pr[fun u => KeygenEchoCell D u v | $ᵗ (KeygenFresh C)] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _v ∈ L, (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun v _ => probEvent_keygenEchoCell_le D v
    _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (List.toFinset_card_le _).trans hm

theorem probEvent_bind_le_const {α β : Type} (oa : ProbComp α) (ob : α → ProbComp β) (P : β → Prop)
    (c : ℝ≥0∞) (h : ∀ a ∈ support oa, Pr[P | ob a] ≤ c) : Pr[P | oa >>= ob] ≤ c := by
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' a, Pr[= a | oa] * c := ENNReal.tsum_le_tsum fun a => by
        by_cases ha : a ∈ support oa
        · exact mul_le_mul_left' (h a ha) _
        · simp [probOutput_eq_zero_of_not_mem_support ha]
    _ ≤ c := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem probEvent_bind_mono_of {α β γ : Type} (oa : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (P : β → Prop) (Q : γ → Prop) (h : ∀ a, Pr[P | f a] ≤ Pr[Q | g a]) :
    Pr[P | oa >>= f] ≤ Pr[Q | oa >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_left' (h a) _

theorem probEvent_congr_evalDist {α : Type} {oa ob : ProbComp α} (h : 𝒟[oa] = 𝒟[ob]) (P : α → Prop) :
    Pr[P | oa] = Pr[P | ob] := by
  simp only [probEvent_eq_tsum_ite, probOutput_def, h]

/-- The logged prefix of the reference run. -/
def keygenPrefixLog (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (S : Finset (Query C)) (parts : C.Party → Parts C) (a : S → HashOutput) :
    ProbComp ((A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) ×
      List (Query C)) :=
  simulateQ (fixedLocal prims (keygenFiniteTotal prims S a))
    (keygenHashLog (keygenRefPrefix prims D (keygenFiniteTotal prims S a) A x z parts))

/-- The fresh table, the oracle with its independent copy, and the logged prefix. -/
def keygenEchoJoint (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (S : Finset (Query C)) (parts : C.Party → Parts C) :
    ProbComp (KeygenFresh C × ((S → HashOutput) × (S → HashOutput)) ×
      ((A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) ×
        List (Query C))) := do
  let u ← $ᵗ (KeygenFresh C)
  let p ← $ᵗ ((S → HashOutput) × (S → HashOutput))
  let r ← keygenPrefixLog prims D A x z S parts p.1
  pure (u, p, r)

theorem evalDist_keygenEchoJoint_last (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    𝒟[keygenEchoJoint prims D A x z S parts] =
      𝒟[($ᵗ ((S → HashOutput) × (S → HashOutput))) >>= fun p => keygenPrefixLog prims D A x z S parts p.1 >>= fun r =>
        ($ᵗ (KeygenFresh C)) >>= fun u => pure (u, p, r)] := by
  unfold keygenEchoJoint
  rw [DeferredSampling.evalDist_bind_comm]
  refine evalDist_bind_congr' _ fun p => ?_
  rw [DeferredSampling.evalDist_bind_comm]

theorem evalDist_keygenEchoJoint_copy (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    𝒟[keygenEchoJoint prims D A x z S parts] =
      𝒟[($ᵗ (KeygenFresh C)) >>= fun u => ($ᵗ (S → HashOutput)) >>= fun a =>
        keygenPrefixLog prims D A x z S parts a >>= fun r =>
        ($ᵗ (S → HashOutput)) >>= fun a' => pure (u, (a, a'), r)] := by
  unfold keygenEchoJoint
  refine evalDist_bind_congr' _ fun u => ?_
  rw [uniformSample_prod_bind]
  refine evalDist_bind_congr' _ fun a => ?_
  rw [DeferredSampling.evalDist_bind_comm]

theorem probEvent_keygenEchoJoint_collide_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) :
    Pr[fun t => KeygenCollide prims D S hsk (keygenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1 t.2.1.2 |
      keygenEchoJoint prims D A x z S parts] ≤
      (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [probEvent_congr_evalDist (evalDist_keygenEchoJoint_copy prims D A x z S parts)]
  refine probEvent_bind_le_const _ _ _ _ fun u _ => probEvent_bind_le_const _ _ _ _ fun a _ =>
    probEvent_bind_le_const _ _ _ _ fun r _ => ?_
  rw [bind_pure_comp, probEvent_map]
  have h := probEvent_keygenCollide_le prims D S hsk (keygenFiniteTotal prims S a) parts r.1 u
  exact h

theorem probEvent_keygenEchoJoint_log_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) (q : ℕ)
    (hq : ∀ a, ∀ r ∈ support (keygenPrefixLog prims D A x z S parts a), (r.2.filter fun v => ¬ IsFixed v).length ≤ q) :
    Pr[fun t => ∃ v ∈ t.2.2.2, KeygenEchoCell D t.1 v | keygenEchoJoint prims D A x z S parts] ≤
      (q : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  rw [probEvent_congr_evalDist (evalDist_keygenEchoJoint_last prims D A x z S parts)]
  refine probEvent_bind_le_const _ _ _ _ fun p _ => probEvent_bind_le_const _ _ _ _ fun r hr => ?_
  rw [bind_pure_comp, probEvent_map]
  exact probEvent_keygenLogHit_le D r.2 q (hq p.1 r hr)

theorem probEvent_keygenEchoJoint_honest_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    Pr[fun t => KeygenHonestHit prims D (keygenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1 |
      keygenEchoJoint prims D A x z S parts] ≤
      ((C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  rw [probEvent_congr_evalDist (evalDist_keygenEchoJoint_last prims D A x z S parts)]
  refine probEvent_bind_le_const _ _ _ _ fun p _ => probEvent_bind_le_const _ _ _ _ fun r _ => ?_
  rw [bind_pure_comp, probEvent_map]
  have h := probEvent_keygenHonestHit_le prims D (keygenFiniteTotal prims S p.1) parts r.1
  exact h

open OracleComp.ProgramLogic.Relational in
/-- On the mixed oracle, an echo collision needs a collision of the copy, a logged echo cell, or an
honest echo cell. -/
theorem probEvent_keygenIrr_mix_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) (u : KeygenFresh C) (a a' : S → HashOutput) :
    Pr[fun π => keygenIrr prims D (keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a'))
        parts π u |
      simulateQ (fixedLocal prims (keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a')))
        (keygenRefPrefix prims D (keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a'))
          A x z parts)] ≤
    Pr[fun r => KeygenCollide prims D S hsk (keygenFiniteTotal prims S a) parts r.1 u a' ∨
        (∃ v ∈ r.2, KeygenEchoCell D u v) ∨ KeygenHonestHit prims D (keygenFiniteTotal prims S a) parts r.1 u |
      simulateQ (fixedLocal prims (keygenFiniteTotal prims S a))
        (keygenHashLog (keygenRefPrefix prims D (keygenFiniteTotal prims S a) A x z parts))] := by
  set hm := keygenFiniteTotal prims S (keygenMix (fun s : S => KeygenEchoCell D u s.1) a a') with hhm
  set ha := keygenFiniteTotal prims S a with hha
  have hoff : ∀ v, ¬ KeygenEchoCell D u v → hm v = ha v := keygenFiniteTotal_mix_off prims D S u a a'
  have hc : ∀ ph b c l, hm (.commit ph b c l) = ha (.commit ph b c l) := fun ph b c l =>
    hoff _ fun hc => by obtain ⟨l', hl'⟩ := keygenEchoCell_sharedKeys hc; cases hl'
  rw [keygenRefPrefix_eq_V, keygenRefPrefixV_congr prims D hm ha hc, keygenRefPrefix_eq_V]
  have R := relTriple_keygenRefPrefixV prims D ha hm ha (KeygenEchoCell D u) hoff
    (keygenRefVisible prims D hm parts) (keygenRefVisible prims D ha parts) A x z parts
  refine probEvent_le_of_relTriple (relTriple_symm R) fun y r hry hy => ?_
  rcases hry with hl | hv | he
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr (keygenHonestHit_of_viewDiff prims D S parts a a' r.1 u hv))
  · subst he
    exact Or.inl (keygenIrr_mix_collide prims D S hsk parts a a' r.1 u hy)

/-- The prefix of the reference run. -/
def keygenRefRun (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (S : Finset (Query C)) (parts : C.Party → Parts C) (a : S → HashOutput) :
    ProbComp (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :=
  simulateQ (fixedLocal prims (keygenFiniteTotal prims S a))
    (keygenRefPrefix prims D (keygenFiniteTotal prims S a) A x z parts)

theorem probOutput_true_map_decide {α : Type} (oa : ProbComp α) (P : α → Prop) :
    Pr[= true | (fun a => decide (P a)) <$> oa] = Pr[P | oa] := by
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  simp [Function.comp_def]

/-- One fresh table: the echo collision on the prefix, through the mixed oracle. -/
theorem probEvent_keygenIrr_le_u (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) (u : KeygenFresh C) :
    Pr[fun s => keygenIrr prims D (keygenFiniteTotal prims S s.1) parts s.2 u |
      ($ᵗ (S → HashOutput)) >>= fun a => (fun π => (a, π)) <$> keygenRefRun prims D A x z S parts a] ≤
    Pr[fun s => KeygenCollide prims D S hsk (keygenFiniteTotal prims S s.1.1) parts s.2.1 u s.1.2 ∨
        (∃ v ∈ s.2.2, KeygenEchoCell D u v) ∨
        KeygenHonestHit prims D (keygenFiniteTotal prims S s.1.1) parts s.2.1 u |
      ($ᵗ ((S → HashOutput) × (S → HashOutput))) >>= fun p =>
        (fun r => (p, r)) <$> keygenPrefixLog prims D A x z S parts p.1] := by
  let k : (S → HashOutput) → ProbComp Bool := fun b =>
    (fun π => decide (keygenIrr prims D (keygenFiniteTotal prims S b) parts π u)) <$> keygenRefRun prims D A x z S parts b
  have hl : Pr[fun s => keygenIrr prims D (keygenFiniteTotal prims S s.1) parts s.2 u |
      ($ᵗ (S → HashOutput)) >>= fun a => (fun π => (a, π)) <$> keygenRefRun prims D A x z S parts a] =
      Pr[= true | ($ᵗ (S → HashOutput)) >>= k] := by
    rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun a => ?_
    rw [probEvent_map, probOutput_true_map_decide]
    rfl
  rw [hl, probOutput_def, ← evalDist_bind_keygenMix (fun s : S => KeygenEchoCell D u s.1) k, ← probOutput_def,
    probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun p => mul_le_mul_left' ?_ _
  rw [probOutput_true_map_decide, probEvent_map]
  exact probEvent_keygenIrr_mix_le prims D A x z S hsk parts u p.1 p.2

theorem evalDist_keygenStageBSampler_reorder (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    𝒟[(fun w => (w.2.2.1, w.1, w.2.1)) <$> keygenStageBSampler prims D A x z S parts] =
      𝒟[($ᵗ (KeygenFresh C)) >>= fun u => (fun s => (u, s)) <$>
        (($ᵗ (S → HashOutput)) >>= fun a => (fun π => (a, π)) <$> keygenRefRun prims D A x z S parts a)] := by
  unfold keygenStageBSampler keygenRefRun
  simp only [map_bind, map_pure, bind_map_left]
  rw [DeferredSampling.evalDist_bind_comm]
  refine evalDist_bind_congr' _ fun a => ?_
  rw [DeferredSampling.evalDist_bind_comm]
  refine evalDist_bind_congr' _ fun u => ?_
  rw [Functor.map_map, map_eq_bind_pure_comp]
  refine evalDist_bind_congr' _ fun π => ?_
  exact evalDist_uniform_bind_const (α := KeygenFresh C) (pure _)

theorem keygenEchoJoint_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    keygenEchoJoint prims D A x z S parts =
      ($ᵗ (KeygenFresh C)) >>= fun u => (fun s => (u, s)) <$>
        (($ᵗ ((S → HashOutput) × (S → HashOutput))) >>= fun p =>
          (fun r => (p, r)) <$> keygenPrefixLog prims D A x z S parts p.1) := by
  unfold keygenEchoJoint
  simp only [map_bind, Functor.map_map, bind_pure_comp]

/-- On one choice of parts, an echo collision needs a collision of the independent copy, a logged
echo cell, or an honest echo cell. -/
theorem probEvent_keygenEchoIrregular_le_joint (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) :
    Pr[fun w => KeygenEchoIrregular prims D A S (parts, w) w.2.2.1 | keygenStageBSampler prims D A x z S parts] ≤
    Pr[fun t => KeygenCollide prims D S hsk (keygenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1 t.2.1.2 ∨
        (∃ v ∈ t.2.2.2, KeygenEchoCell D t.1 v) ∨
        KeygenHonestHit prims D (keygenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1 |
      keygenEchoJoint prims D A x z S parts] := by
  have h1 : Pr[fun w => KeygenEchoIrregular prims D A S (parts, w) w.2.2.1 |
      keygenStageBSampler prims D A x z S parts] =
      Pr[fun t => keygenIrr prims D (keygenFiniteTotal prims S t.2.1) parts t.2.2 t.1 |
        (fun w => (w.2.2.1, w.1, w.2.1)) <$> keygenStageBSampler prims D A x z S parts] := by
    rw [probEvent_map]
    rfl
  rw [h1, probEvent_congr_evalDist (evalDist_keygenStageBSampler_reorder prims D A x z S parts),
    keygenEchoJoint_eq]
  refine probEvent_bind_mono_of _ _ _ _ _ fun u => ?_
  rw [probEvent_map, probEvent_map]
  have h := probEvent_keygenIrr_le_u prims D A x z S hsk parts u
  exact h

theorem exists_mem_support_probComp {α : Type} (oa : ProbComp α) : ∃ x, x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨x, by simp⟩
  | query_bind t mx ih =>
      obtain ⟨x, hx⟩ := ih default
      exact ⟨x, (mem_support_bind_iff _ _ _).2 ⟨default, mem_support_query t default, hx⟩⟩

/-- The logged prefix has at most `q` counted calls. -/
theorem keygenPrefixLog_length_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (a : S → HashOutput) (r) (hr : r ∈ support (keygenPrefixLog prims D A x z S parts a)) :
    (r.2.filter fun v => ¬ IsFixed v).length ≤ q := by
  set h := keygenFiniteTotal prims S a
  obtain ⟨y, hy⟩ := exists_mem_support_probComp (simulateQ (fixedLocal prims h)
    (keygenHashLog (Z (r.1.1, keygenRefOutputs prims D h (fun _ => 0) parts r.1.2))))
  have hk : (y.1, r.2 ++ y.2) ∈ support (keygenReferenceKernel prims D h (fun _ => 0) A x z Z parts) := by
    unfold keygenReferenceKernel
    rw [keygenReferenceLocalGame_eq_prefix, keygenHashLog_bind]
    simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff]
    exact ⟨r, hr, y, hy, rfl⟩
  have := keygenReferenceKernel_random_length_le prims D h (fun _ => 0) A x z Z q hq parts _ hk
  simp only [List.filter_append, List.length_append] at this
  omega

/-- On one choice of parts, the echo collision costs `(1 + q + n²) |pairs| / 2^256`. -/
theorem probEvent_keygenEchoIrregular_parts_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .keygen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) :
    Pr[fun w => KeygenEchoIrregular prims D A S (parts, w) w.2.2.1 | keygenStageBSampler prims D A x z S parts] ≤
      ((1 + q + C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  refine (probEvent_keygenEchoIrregular_le_joint prims D A x z S hsk parts).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  refine (add_le_add le_rfl (probEvent_or_le (keygenEchoJoint prims D A x z S parts) _ _)).trans ?_
  have h1 := probEvent_keygenEchoJoint_collide_le prims D A x z S hsk parts
  have h2 := probEvent_keygenEchoJoint_log_le prims D A x z S parts q
    (fun a r hr => keygenPrefixLog_length_le prims D A x z Z q hq S parts a r hr)
  have h3 := probEvent_keygenEchoJoint_honest_le prims D A x z S parts
  calc _ ≤ (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ +
        ((q : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
          ((C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹)) :=
        add_le_add h1 (add_le_add h2 h3)
    _ = _ := by push_cast; ring

end EchoFresh

section Arith

variable {C : Committee}

theorem keygenFinish_card_term : Fintype.card C.Term = termCount C := by
  simp [Committee.Term, Fintype.card_finset_len, termCount]

theorem keygenFinish_card_pair : Fintype.card C.Pair = C.n.choose 2 := by
  classical
  have hcard : Fintype.card (Finset.powersetCard 2 (Finset.univ : Finset C.Party)) = C.n.choose 2 := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Fintype.card_congr ⟨fun p => ⟨{p.1.1, p.1.2}, by
      simp [Finset.mem_powersetCard, Finset.card_pair (ne_of_lt p.2)]⟩,
    fun s => ⟨((s.1.min' (Finset.card_pos.mp (by have := (Finset.mem_powersetCard.mp s.2).2; omega))),
      (s.1.max' (Finset.card_pos.mp (by have := (Finset.mem_powersetCard.mp s.2).2; omega)))),
      Finset.min'_lt_max'_of_card _ (by have := (Finset.mem_powersetCard.mp s.2).2; omega)⟩, ?_, ?_⟩
  · intro p
    obtain ⟨⟨a, b⟩, hab⟩ := p
    apply Subtype.ext
    simp only
    ext
    · simp [Finset.min'_insert, min_eq_left hab.le]
    · simpa [Finset.max'_insert] using hab.le
  · intro s
    obtain ⟨s, hs⟩ := s
    apply Subtype.ext
    simp only
    have h2 := (Finset.mem_powersetCard.mp hs).2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    rcases lt_or_gt_of_ne hab with h | h
    · simp [Finset.min'_insert, Finset.max'_insert, min_eq_left h.le, max_eq_right h.le]
    · simp [Finset.min'_insert, Finset.max'_insert, min_eq_left h.le, max_eq_right h.le,
        Finset.pair_comm]

/-- The echo-collision cost fits in what remains of half the error after stage A on both
distinguishers. -/
theorem keygenEcho_arith (q : ℕ) :
    4 * ((1 + q + C.n * C.n) * C.n.choose 2) + 4 * (termCount C ^ 2 + 2 * C.n.choose 2 ^ 2 +
      q * (termCount C + C.n.choose 2)) ≤ (q + keygenSecrets C) ^ 2 := by
  have hn : 1 ≤ C.n := by have := C.one_le_t; unfold Committee.n; omega
  have hP : 2 * C.n.choose 2 ≤ C.n * C.n := by
    rw [Nat.choose_two_right]
    have := Nat.div_mul_le_self (C.n * (C.n - 1)) 2
    have h2 : C.n * (C.n - 1) ≤ C.n * C.n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  set P := C.n.choose 2
  set T := termCount C
  set n := C.n
  have hs : 2 * T + 2 * (n * n) + P ≤ keygenSecrets C := by
    unfold keygenSecrets
    have : T ≤ n * T := Nat.le_mul_of_pos_left T hn
    nlinarith
  have hs' : 4 * T + 8 * P ≤ 2 * keygenSecrets C := by omega
  set s := keygenSecrets C
  have hsq : (2 * T + 2 * (n * n) + P) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs 2
  have hn2 : 1 ≤ n * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith [hsq, hP, hn2, Nat.zero_le (q * s), Nat.zero_le (T * P), Nat.zero_le (n * n * P)]

end Arith

section EchoFreshMain

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The echo-collision bound on a domain with every echo input. -/
theorem keygenEchoFreshExt : KeygenEchoFreshExt (C := C) (E := E) prims := by
  intro D A x z Z q hq S _ hsk
  have hb : Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.1 |
      keygenPartsKernel (keygenStageBSampler prims D A x z S)] ≤
      ((1 + q + C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
    rw [probEvent_keygenPartsKernel_eq_tsum (keygenStageBSampler prims D A x z S)
      (fun parts w => KeygenEchoIrregular prims D A S (parts, w) w.2.2.1)]
    calc _ ≤ ∑' parts, Pr[= parts | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] *
          (((1 + q + C.n * C.n : ℕ) : ℝ≥0∞) *
            ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹)) :=
          ENNReal.tsum_le_tsum fun parts => mul_le_mul_left'
            (probEvent_keygenEchoIrregular_parts_le prims D A x z Z q hq S hsk parts) _
      _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          refine mul_le_of_le_one_left' ?_
          exact tsum_probOutput_le_one
  rw [← mul_assoc, ← Nat.cast_mul] at hb
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)) hb
  rw [toReal_nat_mul_inv_card] at ht
  refine ht.trans ?_
  have ha := keygenEcho_arith (C := C) q
  unfold keygenHashError keygenStageAError keygenClashCount keygenGuessNames
  rw [keygenFinish_card_pair, keygenFinish_card_term]
  have ha' : (4 * ((1 + q + C.n * C.n) * C.n.choose 2) + 4 * (termCount C ^ 2 + 2 * C.n.choose 2 ^ 2 +
      q * (termCount C + C.n.choose 2)) : ℝ) ≤ ((q + keygenSecrets C) ^ 2 : ℕ) := by exact_mod_cast ha
  push_cast at ha' ⊢
  rw [div_le_iff₀ (by positivity)]
  have h256 : (0 : ℝ) < 2 ^ 256 := by positivity
  field_simp
  nlinarith [ha']

end EchoFreshMain

section Main

variable {C : Committee} {E : Type} (prims : Primitives)

/-- `KeygenSecurityStatement`, from the two open stages. -/
theorem keygenSecurityComplete (hK : KeygenKnownMismatch (C := C) (E := E) prims) :
    KeygenSecurityStatement (C := C) (E := E) prims :=
  keygenSecurity_of_halves prims
    (keygenHiddenDistance_of_fresh prims (keygenHiddenFresh_of_echoFreshExt prims (keygenEchoFreshExt prims))) hK

/-- The hidden half of the keygen claim, with no open hypothesis. -/
theorem keygenHiddenDistanceProof : KeygenHiddenDistance (C := C) (E := E) prims :=
  keygenHiddenDistance_of_fresh prims (keygenHiddenFresh_of_echoFreshExt prims (keygenEchoFreshExt prims))

end Main

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.keygenSecurityComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.keygenSecurityComplete

/-- info: 'ThresholdLeanXmssSecurity.keygenHiddenDistanceProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.keygenHiddenDistanceProof
