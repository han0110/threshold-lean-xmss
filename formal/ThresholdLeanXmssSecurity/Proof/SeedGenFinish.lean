import ThresholdLeanXmssSecurity.Proof.SeedGenHalves
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The hidden half of the seed generation security

This file proves the hidden half `SeedGenHiddenFresh` (`seedGenHiddenFresh_of_echoFreshExt`) from the
echo-collision bound `seedGenEchoFreshExt`. `seedGenSecurityComplete` uses it and takes the known half
`SeedGenKnownMismatch` as a hypothesis. `seedGenSecurityDone_of_programAlias` of
`Proof/SeedGenKnown.lean` uses `seedGenSecurityComplete`.

1. Off the domain `S` the finite oracle answers `0`. The proof adds every echo input
   (`seedGenSharedInputs`) to `S` and proves the bound there (`SeedGenEchoFreshExt`). The chain of
   `SeedGenHalves` and `SeedGenSecurity` repeats with that domain.
2. The fresh table `u` defines the echo cells. An echo input is a cell when its coordinate at the
   canonical hidden term of an honest pair is the fresh seed. Each fixed query is a cell with
   probability at most
   `|pairs| / 2^256` (`probEvent_seedGenEchoCell_le`).
3. Swap the oracle on the cells with an independent copy `a'` (`evalDist_bind_seedGenMix`). The prefix
   runs identically until one of two events (`relTriple_seedGenRefPrefixV`). It logs a cell (at most
   `q` counted calls), or an honest echo toward a corrupt operator is a cell (at most `n²` inputs).
4. Otherwise an echo collision is a collision of two distinct cells of `a'`, `|pairs| / 2^256`.
5. The total `(1 + q + n²) |pairs| / 2^256` fits in the budget (`seedGenEcho_arith`).

`SeedGenKnownMismatch` is a hypothesis of `seedGenSecurityComplete`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## The echo-collision bound on a domain with every echo input

Off a covering domain `S` the finite oracle answers `0`, so two echo inputs off `S` always collide.
The proof chooses the domain (`seedGenHiddenFresh_of_echoFreshExt` picks it), so it adds every echo
input of the seed generation to it. -/

section Domain

variable {C : Committee}

/-- Every echo input `sharedKeys` of the seed generation, for any pair and any seeds. -/
def seedGenSharedInputs (C : Committee) : Finset (Query C) :=
  Finset.univ.biUnion fun p : C.Party × C.Party =>
    Finset.univ.image fun f : C.Term → HashOutput => Query.sharedKeys .seedGen ((sharedTerms p.1 p.2).map f)

theorem seedGenSharedInputs_mem (i j : C.Party) (f : C.Term → HashOutput) :
    Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ seedGenSharedInputs C := by
  unfold seedGenSharedInputs
  exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩

end Domain

section Chain

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The echo-collision bound on a domain that holds every echo input. -/
def SeedGenEchoFreshExt (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∀ (S : Finset (Query C)), (∀ parts name, setupNamedInput .seedGen parts name ∈ S) →
      (∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S) →
      (Pr{let r ← seedGenPartsKernel (seedGenStageBSampler prims D A x z S)}[
        SeedGenEchoIrregular prims D A S r r.2.2.2.1]).toReal ≤
        (seedGenHashError C q / 2 - 2 * seedGenStageAError C q) / 2

theorem seedGenAcceptGap_le_of_ext (hF : SeedGenEchoFreshExt (C := C) (E := E) prims)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (S : Finset (Query C)) (hmem : ∀ parts name, setupNamedInput .seedGen parts name ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S) :
    (Pr{let y ← seedGenPartsKernel (seedGenStageBSampler prims D A x z S)}[SeedGenReceiversGap prims D A S y]).toReal ≤
      seedGenHashError C q / 2 - 2 * seedGenStageAError C q := by
  have hb := hF D A x z Z q hq S hmem hsk
  have hle : Pr{let y ← seedGenPartsKernel (seedGenStageBSampler prims D A x z S)}[SeedGenReceiversGap prims D A S y] ≤
      Pr{let r ← seedGenPartsKernel (seedGenStageBSampler prims D A x z S)}[
        SeedGenEchoIrregular prims D A S r r.2.2.2.1] +
      Pr{let r ← seedGenPartsKernel (seedGenStageBSampler prims D A x z S)}[
        SeedGenEchoIrregular prims D A S r r.2.2.2.1] :=
    calc _ ≤ Pr{let r ← seedGenPartsKernel (seedGenStageBSampler prims D A x z S)}[
          SeedGenEchoIrregular prims D A S r r.2.2.2.1 ∨ SeedGenEchoIrregular prims D A S r r.2.2.2.2] :=
          prEvent_mono _ _ _ fun r hr => seedGenReceiversGap_irregular prims D A S r hr
      _ ≤ _ := prEvent_or_le _ _ _
      _ = _ := by rw [probEvent_seedGenEchoIrregular_swap]
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) hle
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at ht
  linarith

theorem seedGenIndepEcho_le_of_ext (hF : SeedGenEchoFreshExt (C := C) (E := E) prims)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (S : Finset (Query C)) (hmem : ∀ parts name, setupNamedInput .seedGen parts name ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S) :
    |(Pr{let y ← seedGenIndepMixture prims D A x z Z S}[y = true]).toReal -
        (Pr{let y ← seedGenIndepMixture prims D A x z (seedGenHiddenZ D Z) S}[y = true]).toReal| ≤
      seedGenHashError C q / 2 - 2 * seedGenStageAError C q := by
  refine le_trans ?_ (seedGenAcceptGap_le_of_ext prims hF D A x z Z q hq S hmem hsk)
  have hZ : Pr{let y ← seedGenIndepMixture prims D A x z Z S}[y = true] =
      Pr{let y ← (OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)) >>= fun parts =>
        seedGenStageBSampler prims D A x z S parts >>= fun w =>
          seedGenStageBRun prims D A Z S parts w w.2.2.2 w.2.2.2}[y = true] := by
    exact (EvalDistEq.bind_right _ fun parts =>
      evalDist_seedGenIndep_Z prims D A x z Z S parts).prEvent_eq (· = true)
  have hH : Pr{let y ← seedGenIndepMixture prims D A x z (seedGenHiddenZ D Z) S}[y = true] =
      Pr{let y ← (OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)) >>= fun parts =>
        seedGenStageBSampler prims D A x z S parts >>= fun w =>
          seedGenStageBRun prims D A Z S parts w w.2.2.1 w.2.2.2}[y = true] := by
    exact (EvalDistEq.bind_right _ fun parts =>
      evalDist_seedGenIndep_hiddenZ prims D A x z Z S parts).prEvent_eq (· = true)
  rw [hZ, hH, probEvent_seedGenPartsKernel_eq_tsum (seedGenStageBSampler prims D A x z S)
    (fun parts w => SeedGenReceiversGap prims D A S (parts, w))]
  refine abs_probOutput_bind_sub_le _ _ _ _ (fun parts => ?_) (fun parts => ?_) ?_
  · exact seedGenStageB_parts prims D A x z Z S parts (fun w => w.2.2.2) (fun w => w.2.2.1) fun w hw => Ne.symm hw
  · exact seedGenStageB_parts prims D A x z Z S parts (fun w => w.2.2.1) (fun w => w.2.2.2) fun w hw => hw
  · rw [← probEvent_seedGenPartsKernel_eq_tsum (seedGenStageBSampler prims D A x z S)
      (fun parts w => SeedGenReceiversGap prims D A S (parts, w))]
    exact (prEvent_ne_top _)

theorem seedGenSwapped_le_of_ext (hF : SeedGenEchoFreshExt (C := C) (E := E) prims)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (S : Finset (Query C)) (hmem : ∀ parts name, setupNamedInput .seedGen parts name ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S) :
    |(Pr{let y ← seedGenSwappedMixture prims D A x z Z S hmem}[y = true]).toReal -
        (Pr{let y ← seedGenSwappedMixture prims D A x z (seedGenHiddenZ D Z) S hmem}[y = true]).toReal| ≤
      seedGenHashError C q / 2 := by
  have hA₁ := seedGenStageA prims D A x z Z S hmem q hq
  have hA₂ := seedGenStageA prims D A x z (seedGenHiddenZ D Z) S hmem q (isQueryBounded_seedGenHiddenZ D A Z q hq)
  have hb := seedGenIndepEcho_le_of_ext prims hF D A x z Z q hq S hmem hsk
  unfold seedGenStageAError at hb
  calc _ ≤ |(Pr{let y ← seedGenSwappedMixture prims D A x z Z S hmem}[y = true]).toReal -
          (Pr{let y ← seedGenIndepMixture prims D A x z Z S}[y = true]).toReal| +
        |(Pr{let y ← seedGenIndepMixture prims D A x z Z S}[y = true]).toReal -
          (Pr{let y ← seedGenIndepMixture prims D A x z (seedGenHiddenZ D Z) S}[y = true]).toReal| +
        |(Pr{let y ← seedGenIndepMixture prims D A x z (seedGenHiddenZ D Z) S}[y = true]).toReal -
          (Pr{let y ← seedGenSwappedMixture prims D A x z (seedGenHiddenZ D Z) S hmem}[y = true]).toReal| := by
        refine (abs_sub_le _ (Pr{let y ← seedGenIndepMixture prims D A x z (seedGenHiddenZ D Z) S}[y = true]).toReal _).trans ?_
        gcongr
        exact abs_sub_le _ _ _
    _ ≤ _ := by
        rw [abs_sub_comm ((Pr{let y ← seedGenIndepMixture prims D A x z (seedGenHiddenZ D Z) S}[y = true]).toReal)]
        linarith

/-- The hidden half on the real run, from the echo-collision bound on the extended domain. -/
theorem seedGenHiddenFresh_of_echoFreshExt (hF : SeedGenEchoFreshExt (C := C) (E := E) prims) :
    SeedGenHiddenFresh (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨S₁, h₁⟩ := seedGenWorldCovered_exists (free (setupNormalizedLocalGame .seedGen D A x z Z))
  obtain ⟨S₂, h₂⟩ := seedGenWorldCovered_exists (free (setupNormalizedLocalGame .seedGen D A x z (seedGenHiddenZ D Z)))
  let S := S₁ ∪ S₂ ∪ setupAllNamedInputs .seedGen C ∪ seedGenSharedInputs C
  have hS₁ : SeedGenWorldCovered S (free (setupNormalizedLocalGame .seedGen D A x z Z)) :=
    h₁.mono fun _ hq => by simp only [S, Finset.mem_union]; tauto
  have hS₂ : SeedGenWorldCovered S (free (setupNormalizedLocalGame .seedGen D A x z (seedGenHiddenZ D Z))) :=
    h₂.mono fun _ hq => by simp only [S, Finset.mem_union]; tauto
  have hmem : ∀ parts name, setupNamedInput .seedGen parts name ∈ S := fun parts name => by
    have := setupAllNamedInputs_mem .seedGen parts name
    simp only [S, Finset.mem_union]; tauto
  have hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S :=
    fun i j f => Finset.mem_union_right _ (seedGenSharedInputs_mem i j f)
  rw [accepts_eq_probOutput, accepts_eq_probOutput,
    ((evalDist_seedGenReal_referenceMixture prims D A x z Z S hS₁).trans
      (evalDist_seedGenReferenceMixture_swap prims D A x z Z S hmem)).prEvent_eq (· = true),
    ((evalDist_seedGenReal_referenceMixture prims D A x z (seedGenHiddenZ D Z) S hS₂).trans
      (evalDist_seedGenReferenceMixture_swap prims D A x z (seedGenHiddenZ D Z) S hmem)).prEvent_eq (· = true)]
  exact seedGenSwapped_le_of_ext prims hF D A x z Z q hq S hmem hsk

end Chain

/-! ## Two fixed oracles on a computation with an extra bad event -/

section LogCoupling

open OracleComp.ProgramLogic.Relational

variable {C : Committee} (prims : Primitives)

/-- A bind of a step that agrees until a logged point of `P` with continuations that agree until a
logged point of `P` or a bad output `Q`. -/
theorem relTriple_log_bind (h₁ h₂ : Query C → HashOutput) (P : Query C → Prop) {α β : Type}
    (Q : β → Prop) (oa : OracleComp (LocalSpec C) α) (k₁ k₂ : α → OracleComp (LocalSpec C) β)
    (hoa : RelTriple (simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)) (simulateQ (fixedLocal prims h₁) oa)
      (fun x y => (∃ v ∈ x.2, P v) ∨ x.1 = y))
    (hk : ∀ a, RelTriple (simulateQ (fixedLocal prims h₂) (seedGenHashLog (k₂ a)))
      (simulateQ (fixedLocal prims h₁) (k₁ a)) (fun x y => (∃ v ∈ x.2, P v) ∨ Q x.1 ∨ x.1 = y)) :
    RelTriple (simulateQ (fixedLocal prims h₂) (seedGenHashLog (oa >>= k₂)))
      (simulateQ (fixedLocal prims h₁) (oa >>= k₁)) (fun x y => (∃ v ∈ x.2, P v) ∨ Q x.1 ∨ x.1 = y) := by
  rw [seedGenHashLog_bind]
  simp only [simulateQ_bind]
  refine relTriple_bind hoa fun x y hxy => ?_
  rcases hxy with ⟨v, hv, hp⟩ | he
  · refine relTriple_of_support_left fun z hz _ => Or.inl ?_
    simp only [simulateQ_pure, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact ⟨v, List.mem_append_left _ hv, hp⟩
  · subst he
    simp only [simulateQ_pure]
    rw [← bind_pure (simulateQ (fixedLocal prims h₁) (k₁ x.1))]
    refine relTriple_bind (hk x.1) fun w b hwb => relTriple_pure_pure ?_
    rcases hwb with ⟨v, hv, hp⟩ | hq | he
    · exact Or.inl ⟨v, List.mem_append_right _ hv, hp⟩
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr he)

variable {E : Type}

/-- `seedGenRefPrefix` with the echo view of the third round as a parameter. -/
def seedGenRefPrefixV (D : C.Coalition) (h : Query C → HashOutput)
    (V : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) := do
  let state ← A.start (corruptInputs D x) z
  let r ← A.round state (setupFixedCommitView .seedGen prims D h parts)
  if ∀ i, i ∉ D.1 → seedGenCommitAborted D r.2 i = true then pure (r.1, none) else do
    let r' ← A.round r.1 (setupReferenceRevealView .seedGen D parts r.2)
    if ∀ i, i ∉ D.1 → ¬ setupReferenceActive .seedGen D h r.2 r'.2 i then pure (r'.1, none) else do
      let r'' ← A.round r'.1 (V r.2 r'.2)
      pure (r''.1, some (r.2, r'.2, r''.2))

theorem seedGenRefPrefix_eq_V (D : C.Coalition) (h : Query C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    seedGenRefPrefix prims D h A x z parts = seedGenRefPrefixV prims D h (seedGenRefVisible prims D h parts) A x z parts :=
  rfl

/-- The two echo views of a transcript differ. -/
def SeedGenViewDiff {σ : Type}
    (V₁ V₂ : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : Prop :=
  match π.2 with
  | none => False
  | some (s, rs, _) => V₁ s rs ≠ V₂ s rs

/-- Two fixed oracles that agree off `P` and two echo views run the prefix identically until a
logged point of `P` or a transcript whose two echo views differ. -/
theorem relTriple_seedGenRefPrefixV (D : C.Coalition) (h₀ h₁ h₂ : Query C → HashOutput) (P : Query C → Prop)
    (hP : ∀ v, ¬ P v → h₁ v = h₂ v)
    (V₁ V₂ : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    RelTriple (simulateQ (fixedLocal prims h₂) (seedGenHashLog (seedGenRefPrefixV prims D h₀ V₂ A x z parts)))
      (simulateQ (fixedLocal prims h₁) (seedGenRefPrefixV prims D h₀ V₁ A x z parts))
      (fun x y => (∃ v ∈ x.2, P v) ∨ SeedGenViewDiff V₁ V₂ x.1 ∨ x.1 = y) := by
  unfold seedGenRefPrefixV
  refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun state => ?_
  refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun r => ?_
  split_ifs with h1
  · simp only [seedGenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr rfl))
  refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun r' => ?_
  split_ifs with h2
  · simp only [seedGenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr rfl))
  by_cases hv : V₁ r.2 r'.2 = V₂ r.2 r'.2
  · rw [hv]
    refine relTriple_log_bind prims h₁ h₂ P _ _ _ _ (relTriple_fixedLocal_swap prims h₁ h₂ P hP _) fun r'' => ?_
    simp only [seedGenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr rfl))
  · refine relTriple_of_support_left fun w hw _ => Or.inr (Or.inl ?_)
    rw [seedGenHashLog_bind] at hw
    simp only [simulateQ_bind, simulateQ_pure, seedGenHashLog_pure, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨w', -, _, rfl, rfl⟩ := hw
    exact hv

theorem seedGenReferenceKeys_congr_derive (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (hd : ∀ ph k l, h₁ (.derive ph k l) = h₂ (.derive ph k l)) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :
    setupReferenceKeys .seedGen prims D h₁ table parts revealed i = setupReferenceKeys .seedGen prims D h₂ table parts revealed i := by
  simp only [setupReferenceKeys, D_deriveKeys, hd]

/-- The echo inputs of an honest operator toward a corrupt one, under the zero table. -/
def seedGenVisiblePoint (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (rs : C.Party → Mail C E) (i c : C.Party) : Query C :=
  .sharedKeys .seedGen ((sharedTerms i c).map
    (setupReferenceKeys .seedGen prims D h (fun _ => 0) parts (fun i j => rs j i) i).2.1)

/-- The corrupt recipients' echo view reads the oracle off the commitments and the derivations only
at the echo inputs toward corrupt operators. -/
theorem seedGenRefVisible_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (hc : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l))
    (hd : ∀ ph k l, h₁ (.derive ph k l) = h₂ (.derive ph k l))
    (parts : C.Party → Parts C) (s rs : C.Party → Mail C E)
    (hpt : ∀ i c, i ∉ D.1 → c ∈ D.1 →
      h₁ (seedGenVisiblePoint prims D h₁ parts rs i c) = h₂ (seedGenVisiblePoint prims D h₁ parts rs i c)) :
    seedGenRefVisible prims D h₁ parts s rs = seedGenRefVisible prims D h₂ parts s rs := by
  funext c i
  unfold seedGenRefVisible
  split_ifs with hci
  · have hactive : setupReferenceActive .seedGen D h₁ s rs i ↔ setupReferenceActive .seedGen D h₂ s rs i := by
      simp only [setupReferenceActive, setupReferenceOpenCheck, hc]
    rw [setupReferenceData_active, setupReferenceData_active]
    by_cases ha : setupReferenceActive .seedGen D h₁ s rs i
    · rw [if_pos ha, if_pos (hactive.1 ha)]
      simp only [setupEchoDataStep, Step.outbox, echoOutbox]
      congr 2
      simp only [echoOf, ite_true, D_sharedQueries_at]
      rw [← seedGenReferenceKeys_congr_derive prims D h₁ h₂ hd]
      have := hpt i c hci.2 hci.1
      unfold seedGenVisiblePoint at this
      rw [this]
    · rw [if_neg ha, if_neg (fun h => ha (hactive.2 h))]
  · rfl

theorem seedGenRefPrefixV_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (hc : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l))
    (V : (C.Party → Mail C E) → (C.Party → Mail C E) → C.Party → C.Party → Option (Msg E))
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    seedGenRefPrefixV prims D h₁ V A x z parts = seedGenRefPrefixV prims D h₂ V A x z parts := by
  have hcv : setupFixedCommitView .seedGen (E := E) prims D h₁ parts = setupFixedCommitView .seedGen prims D h₂ parts := by
    funext c i
    simp only [setupFixedCommitView, D_commitQueries, hc]
  have hactive : ∀ s rs i, setupReferenceActive .seedGen (E := E) D h₁ s rs i ↔ setupReferenceActive .seedGen D h₂ s rs i := by
    intro s rs i
    simp only [setupReferenceActive, setupReferenceOpenCheck, hc]
  simp only [seedGenRefPrefixV, hcv, hactive]

end LogCoupling

/-! ## The echo cells of a fresh table -/

section Cells

variable {C : Committee}

/-- The coordinate `k` of an echo input. -/
def seedGenEchoAt : Query C → ℕ → HashOutput
  | .sharedKeys _ l, k => l.getD k 0
  | _, _ => 0

/-- The echo cells of the fresh table `u`: an echo input whose coordinate at the canonical hidden term
of an honest pair is the fresh seed of that term. -/
def SeedGenEchoCell (D : C.Coalition) (u : SeedGenFresh C) (v : Query C) : Prop :=
  ∃ p : C.Pair, ∃ hs : SeedGenShareHidden D p.1.1 p.1.2, p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧
    ∃ l, v = Query.sharedKeys .seedGen l ∧
      l.getD ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)) 0 = u.1 (Classical.choose hs)

theorem seedGenEchoCell_sharedKeys {D : C.Coalition} {u : SeedGenFresh C} {v : Query C}
    (h : SeedGenEchoCell D u v) : ∃ l, v = Query.sharedKeys .seedGen l := by
  obtain ⟨_, _, _, _, l, hl, _⟩ := h
  exact ⟨l, hl⟩

theorem probEvent_fun_apply_eq {ι : Type} [Fintype ι] [DecidableEq ι] (T : ι) (c : HashOutput) :
    Pr{let f : ι → HashOutput ← $ᵗ (ι → HashOutput)}[f T = c] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample]
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
    Pr{let f : ι → HashOutput ← $ᵗ (ι → HashOutput)}[f s₁ = f s₂] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let φ : (ι → HashOutput) → (ι → HashOutput) := fun f => Function.update f s₁ (f s₁ + f s₂)
  have hφ : Function.Bijective φ := by
    refine Function.bijective_iff_has_inverse.mpr ⟨fun f => Function.update f s₁ (f s₁ - f s₂), ?_, ?_⟩ <;>
      intro f <;> funext k <;> by_cases hk : k = s₁
    · subst hk; simp [φ, Function.update_of_ne hne.symm, BitVec.add_sub_cancel]
    · simp [φ, Function.update_of_ne hk]
    · subst hk; simp [φ, Function.update_of_ne hne.symm, BitVec.sub_add_cancel]
    · simp [φ, Function.update_of_ne hk]
  have he : ∀ P : (ι → HashOutput) → Prop, Pr{let z ← $ᵗ (ι → HashOutput)}[P z] =
      Pr{let z ← φ <$> ($ᵗ (ι → HashOutput))}[P z] := by
    intro P
    exact ((SampleableType.map_uniformSample_evalDistEq_of_bijective hφ).prEvent_eq P).symm
  rw [he, prEvent_map, ← probEvent_fun_apply_eq s₁ 0]
  refine prEvent_congr _ _ _ fun f => ?_
  simp only [φ, Function.update_self, Function.update_of_ne hne.symm]
  constructor
  · intro h
    have := congrArg (· - f s₂) h
    simpa [BitVec.add_sub_cancel] using this
  · intro h
    rw [h]
    exact BitVec.zero_add _

/-- The cells of `a'` on `P` and of `a` elsewhere. -/
def seedGenMix {ι : Type} (P : ι → Prop) (a a' : ι → HashOutput) : ι → HashOutput :=
  fun s => if P s then a' s else a s

/-- Replacing the cells of a uniform function on a set by the cells of an independent copy keeps it
uniform. -/
theorem evalDist_bind_seedGenMix {ι β : Type} [Fintype ι] [DecidableEq ι] (P : ι → Prop)
    (k : (ι → HashOutput) → ProbComp β) :
    (($ᵗ ((ι → HashOutput) × (ι → HashOutput))) >>= fun p => k (seedGenMix P p.1 p.2)) =ᵈ
      (($ᵗ (ι → HashOutput)) >>= k) := by
  let ψ : (ι → HashOutput) × (ι → HashOutput) → (ι → HashOutput) × (ι → HashOutput) :=
    fun p => (seedGenMix P p.1 p.2, seedGenMix P p.2 p.1)
  have hψ : Function.Bijective ψ := by
    refine Function.bijective_iff_has_inverse.mpr ⟨ψ, ?_, ?_⟩ <;> intro p <;>
      refine Prod.ext (funext fun s => ?_) (funext fun s => ?_) <;> by_cases hs : P s <;>
      simp [ψ, seedGenMix, hs]
  have hu : (ψ <$> ($ᵗ ((ι → HashOutput) × (ι → HashOutput)))) =ᵈ
      $ᵗ ((ι → HashOutput) × (ι → HashOutput)) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective hψ
  have hm : ((fun p => seedGenMix P p.1 p.2) <$> ($ᵗ ((ι → HashOutput) × (ι → HashOutput)))) =ᵈ
      $ᵗ (ι → HashOutput) := by
    have he : (fun p : (ι → HashOutput) × (ι → HashOutput) => seedGenMix P p.1 p.2) <$>
        ($ᵗ ((ι → HashOutput) × (ι → HashOutput))) =
        Prod.fst <$> (ψ <$> ($ᵗ ((ι → HashOutput) × (ι → HashOutput)))) := by
      rw [Functor.map_map]
    rw [he]
    refine (hu.map Prod.fst).trans ?_
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans
      (by rw [bind_pure])
  rw [← bind_map_left (fun p : (ι → HashOutput) × (ι → HashOutput) => seedGenMix P p.1 p.2)]
  exact hm.bind_left k

theorem probEvent_fresh_term_eq (T : C.Term) (c : HashOutput) :
    Pr{let u : SeedGenFresh C ← $ᵗ (SeedGenFresh C)}[u.1 T = c] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_fst (fun f : C.Term → HashOutput => f T = c),
    ← probEvent_fun_apply_eq T c]
  exact SampleableType.prEvent_uniformSample_inst_irrel _ _ _

/-- A fixed query is an echo cell of a fresh table with probability at most `|pairs| / 2^256`. -/
theorem probEvent_seedGenEchoCell_le (D : C.Coalition) (v : Query C) :
    Pr{let u ← $ᵗ (SeedGenFresh C)}[SeedGenEchoCell D u v] ≤
      (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc _ = Pr{let u ← $ᵗ (SeedGenFresh C)}[
        ∃ p ∈ (Finset.univ : Finset C.Pair), ∃ hs : SeedGenShareHidden D p.1.1 p.1.2,
        p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ ∃ l, v = Query.sharedKeys .seedGen l ∧
          l.getD ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)) 0 = u.1 (Classical.choose hs)] := by simp [SeedGenEchoCell]
    _ ≤ ∑ p : C.Pair, Pr{let u ← $ᵗ (SeedGenFresh C)}[
        ∃ hs : SeedGenShareHidden D p.1.1 p.1.2,
        p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ ∃ l, v = Query.sharedKeys .seedGen l ∧
          l.getD ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)) 0 = u.1 (Classical.choose hs)] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hs : SeedGenShareHidden D p.1.1 p.1.2
        · rw [← probEvent_fresh_term_eq (Classical.choose hs)
            (seedGenEchoAt v ((sharedTerms p.1.1 p.1.2).idxOf (Classical.choose hs)))]
          refine prEvent_mono _ _ _ fun u hu => ?_
          obtain ⟨hs', -, -, l, rfl, hl⟩ := hu
          rw [← hl]
          rfl
        · refine le_trans (le_of_eq ?_) (zero_le')
          refine prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => ?_
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

theorem seedGenShareHidden_comm {D : C.Coalition} {i j : C.Party} (hs : SeedGenShareHidden D i j) :
    SeedGenShareHidden D j i := by
  obtain ⟨T, h1, h2, h3⟩ := hs
  exact ⟨T, h1, h3, h2⟩

/-- An echo input of an honest pair that shares a hidden term, with the fresh seeds at the hidden
terms, is an echo cell. -/
theorem seedGenEchoCell_of (D : C.Coalition) (u : SeedGenFresh C) {i j : C.Party} (hij : i ≠ j)
    (hi : i ∉ D.1) (hj : j ∉ D.1) (hs : SeedGenShareHidden D i j) (f : C.Term → HashOutput)
    (hf : ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → f T = u.1 T) :
    SeedGenEchoCell D u (.sharedKeys .seedGen ((sharedTerms i j).map f)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨⟨(i, j), h⟩, hs, hi, hj, _, rfl, ?_⟩
    have hT := Classical.choose_spec hs
    exact (list_map_getD_idxOf (sharedTerms i j) f 0 _ (mem_sharedTerms hT.2.1 hT.2.2)).trans
      (hf _ hT.1 hT.2.1 hT.2.2)
  · have hs' := seedGenShareHidden_comm hs
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
def seedGenIrr (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (u : SeedGenFresh C) : Prop :=
  match π.2 with
  | none => False
  | some (_, rs, _) => ¬ SeedGenEchoRegularHidden D h
      (setupReferenceKeys .seedGen prims D h (seedGenTableOf u.1 u.2) parts (fun i j => rs j i))

/-- The echo input of `i` toward `j`, as a cell of the domain. -/
def seedGenEchoPt (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (rs : C.Party → Mail C E) (u : SeedGenFresh C)
    (i j : C.Party) : S :=
  ⟨.sharedKeys .seedGen ((sharedTerms i j).map
    (setupReferenceKeys .seedGen prims D h (seedGenTableOf u.1 u.2) parts (fun i j => rs j i) i).2.1), hsk i j _⟩

/-- Two distinct echo inputs of a pair collide in `a'`. -/
def SeedGenCollide (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (u : SeedGenFresh C) (a' : S → HashOutput) : Prop :=
  match π.2 with
  | none => False
  | some (_, rs, _) => ∃ p : C.Pair,
      seedGenEchoPt prims D S hsk h parts rs u p.1.1 p.1.2 ≠ seedGenEchoPt prims D S hsk h parts rs u p.1.2 p.1.1 ∧
      a' (seedGenEchoPt prims D S hsk h parts rs u p.1.1 p.1.2) = a' (seedGenEchoPt prims D S hsk h parts rs u p.1.2 p.1.1)

theorem seedGenFiniteTotal_mix_off (D : C.Coalition) (S : Finset (Query C)) (u : SeedGenFresh C)
    (a a' : S → HashOutput) (v : Query C) (hv : ¬ SeedGenEchoCell D u v) :
    seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a') v =
      seedGenFiniteTotal prims S a v := by
  cases v <;> simp [seedGenFiniteTotal, seedGenMix, hv]

theorem seedGenFiniteTotal_mix_cell (D : C.Coalition) (S : Finset (Query C)) (u : SeedGenFresh C)
    (a a' : S → HashOutput) (v : Query C) (hv : SeedGenEchoCell D u v) (hS : v ∈ S) :
    seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a') v = a' ⟨v, hS⟩ := by
  obtain ⟨l, rfl⟩ := seedGenEchoCell_sharedKeys hv
  simp [seedGenFiniteTotal, seedGenMix, hv, hS]

theorem seedGenReferenceKeys_hidden (D : C.Coalition) (h : Query C → HashOutput) (u : SeedGenFresh C)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (hi : i ∈ C.holders T) :
    (setupReferenceKeys .seedGen prims D h (seedGenTableOf u.1 u.2) parts revealed i).2.1 T = u.1 T := by
  simp [setupReferenceKeys, seedGenMaskKeys, hT, hi, seedGenTableOf]

/-- An echo collision under the mixed oracle is a collision of two distinct cells of `a'`. -/
theorem seedGenIrr_mix_collide (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) (a a' : S → HashOutput) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (u : SeedGenFresh C)
    (hI : seedGenIrr prims D (seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a'))
      parts π u) :
    SeedGenCollide prims D S hsk (seedGenFiniteTotal prims S a) parts π u a' := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · exact hI.elim
  simp only [seedGenIrr, SeedGenEchoRegularHidden] at hI
  push Not at hI
  obtain ⟨i, j, hi, hj, hs, heq, hne⟩ := hI
  have hd : ∀ ph k l, seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a')
      (.derive ph k l) = seedGenFiniteTotal prims S a (.derive ph k l) := fun ph k l =>
    seedGenFiniteTotal_mix_off prims D S u a a' _ fun hc => by
      obtain ⟨l', hl'⟩ := seedGenEchoCell_sharedKeys hc
      cases hl'
  simp only [seedGenReferenceKeys_congr_derive prims D _ _ hd] at heq hne
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  have hcx := seedGenEchoCell_of D u hij hi hj hs
    (setupReferenceKeys .seedGen prims D (seedGenFiniteTotal prims S a) (seedGenTableOf u.1 u.2) parts
      (fun i j => rs j i) i).2.1 fun T hT hiT _ =>
    seedGenReferenceKeys_hidden prims D _ u parts (fun i j => rs j i) i T hT hiT
  have hcy := seedGenEchoCell_of D u hij.symm hj hi (seedGenShareHidden_comm hs)
    (setupReferenceKeys .seedGen prims D (seedGenFiniteTotal prims S a) (seedGenTableOf u.1 u.2) parts
      (fun i j => rs j i) j).2.1 fun T hT hjT _ =>
    seedGenReferenceKeys_hidden prims D _ u parts (fun i j => rs j i) j T hT hjT
  rw [seedGenFiniteTotal_mix_cell prims D S u a a' _ hcx (hsk _ _ _),
    seedGenFiniteTotal_mix_cell prims D S u a a' _ hcy (hsk _ _ _)] at heq
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨⟨(i, j), h⟩, fun he => hne (congrArg Subtype.val he), heq⟩
  · refine ⟨⟨(j, i), h⟩, fun he => hne (congrArg Subtype.val he).symm, heq.symm⟩

theorem probEvent_seedGenCollide_le (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (u : SeedGenFresh C) :
    Pr{let a' ← $ᵗ (S → HashOutput)}[SeedGenCollide prims D S hsk h parts π u a'] ≤
      (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun a' _ ha' => ?_)) zero_le
    exact ha'
  let pt := seedGenEchoPt prims D S hsk h parts rs u
  calc _ = Pr{let a' ← $ᵗ (S → HashOutput)}[∃ p ∈ (Finset.univ : Finset C.Pair), pt p.1.1 p.1.2 ≠ pt p.1.2 p.1.1 ∧
        a' (pt p.1.1 p.1.2) = a' (pt p.1.2 p.1.1)] :=
        prEvent_congr _ _ _ fun a' => by simp [SeedGenCollide, pt]
    _ ≤ ∑ p : C.Pair, Pr{let a' ← $ᵗ (S → HashOutput)}[pt p.1.1 p.1.2 ≠ pt p.1.2 p.1.1 ∧
        a' (pt p.1.1 p.1.2) = a' (pt p.1.2 p.1.1)] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hne : pt p.1.1 p.1.2 = pt p.1.2 p.1.1
        · refine le_trans (le_of_eq ?_) (zero_le')
          refine prEvent_eq_zero_of_forall_mem_support _ _ fun a' _ ha' => ?_
          exact ha'.1 hne
        · rw [← probEvent_fun_collide hne]
          exact prEvent_mono _ _ _ fun a' ha' => ha'.2
    _ = _ := by simp

/-- An honest echo input toward a corrupt operator is an echo cell. -/
def SeedGenHonestHit (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (u : SeedGenFresh C) : Prop :=
  match π.2 with
  | none => False
  | some (_, rs, _) => ∃ i c : C.Party, SeedGenEchoCell D u (seedGenVisiblePoint prims D h parts rs i c)

theorem seedGenHonestHit_of_viewDiff (D : C.Coalition) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (a a' : S → HashOutput) {σ : Type}
    (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (u : SeedGenFresh C)
    (hv : SeedGenViewDiff
      (seedGenRefVisible prims D (seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a')) parts)
      (seedGenRefVisible prims D (seedGenFiniteTotal prims S a) parts) π) :
    SeedGenHonestHit prims D (seedGenFiniteTotal prims S a) parts π u := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · exact hv.elim
  simp only [SeedGenViewDiff] at hv
  simp only [SeedGenHonestHit]
  by_contra hn
  push Not at hn
  have hoff := seedGenFiniteTotal_mix_off prims D S u a a'
  refine hv (seedGenRefVisible_congr prims D _ _ (fun ph b c l => ?_) (fun ph k l => ?_) parts s rs ?_).symm
  · exact (hoff _ fun hc => by obtain ⟨l', hl'⟩ := seedGenEchoCell_sharedKeys hc; cases hl').symm
  · exact (hoff _ fun hc => by obtain ⟨l', hl'⟩ := seedGenEchoCell_sharedKeys hc; cases hl').symm
  · intro i c _ _
    exact (hoff _ (hn i c)).symm

theorem probEvent_seedGenHonestHit_le (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    {σ : Type} (π : σ × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :
    Pr{let u ← $ᵗ (SeedGenFresh C)}[SeedGenHonestHit prims D h parts π u] ≤
      ((C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  rcases π with ⟨st, _ | ⟨s, rs, es⟩⟩
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => ?_)) zero_le
    exact hu
  calc _ = Pr{let u ← $ᵗ (SeedGenFresh C)}[∃ p ∈ (Finset.univ : Finset (C.Party × C.Party)),
        SeedGenEchoCell D u (seedGenVisiblePoint prims D h parts rs p.1 p.2)] :=
        prEvent_congr _ _ _ fun u => by simp [SeedGenHonestHit]
    _ ≤ ∑ p : C.Party × C.Party, Pr{let u ← $ᵗ (SeedGenFresh C)}[
        SeedGenEchoCell D u (seedGenVisiblePoint prims D h parts rs p.1 p.2)] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _p : C.Party × C.Party, (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun p _ => probEvent_seedGenEchoCell_le D _
    _ = _ := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Committee.Party]

theorem probEvent_seedGenLogHit_le (D : C.Coalition) (log : List (Query C)) (m : ℕ)
    (hm : (log.filter fun v => ¬ IsFixed v).length ≤ m) :
    Pr{let u ← $ᵗ (SeedGenFresh C)}[∃ v ∈ log, SeedGenEchoCell D u v] ≤
      (m : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  let L := (log.filter fun v => ¬ IsFixed v).toFinset
  calc _ ≤ Pr{let u ← $ᵗ (SeedGenFresh C)}[∃ v ∈ L, SeedGenEchoCell D u v] := by
        refine prEvent_mono _ _ _ fun u hu => ?_
        obtain ⟨v, hv, hc⟩ := hu
        refine ⟨v, ?_, hc⟩
        simp only [L, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        refine ⟨hv, ?_⟩
        rintro ⟨input, rfl, -⟩
        obtain ⟨l, hl⟩ := seedGenEchoCell_sharedKeys hc
        cases hl
    _ ≤ ∑ v ∈ L, Pr{let u ← $ᵗ (SeedGenFresh C)}[SeedGenEchoCell D u v] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _v ∈ L, (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun v _ => probEvent_seedGenEchoCell_le D v
    _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (List.toFinset_card_le _).trans hm

theorem probEvent_bind_le_const {α β : Type} (oa : ProbComp α) (ob : α → ProbComp β) (P : β → Prop)
    (c : ℝ≥0∞) (h : ∀ a ∈ support oa, Pr{let z ← ob a}[P z] ≤ c) : Pr{let z ← oa >>= ob}[P z] ≤ c := by
  exact prEvent_bind_le_of_forall_le_of_support _ _ _ h

theorem probEvent_bind_mono_of {α β γ : Type} (oa : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (P : β → Prop) (Q : γ → Prop) (h : ∀ a, Pr{let z ← f a}[P z] ≤ Pr{let z ← g a}[Q z]) :
    Pr{let z ← oa >>= f}[P z] ≤ Pr{let z ← oa >>= g}[Q z] := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _

theorem probEvent_congr_evalDist {α : Type} {oa ob : ProbComp α} (h : oa =ᵈ ob) (P : α → Prop) :
    Pr{let z ← oa}[P z] = Pr{let z ← ob}[P z] :=
  h.prEvent_eq P

/-- The logged prefix of the reference run. -/
def seedGenPrefixLog (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (S : Finset (Query C)) (parts : C.Party → Parts C) (a : S → HashOutput) :
    ProbComp ((A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) ×
      List (Query C)) :=
  simulateQ (fixedLocal prims (seedGenFiniteTotal prims S a))
    (seedGenHashLog (seedGenRefPrefix prims D (seedGenFiniteTotal prims S a) A x z parts))

/-- The fresh table, the oracle with its independent copy, and the logged prefix. -/
def seedGenEchoJoint (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (S : Finset (Query C)) (parts : C.Party → Parts C) :
    ProbComp (SeedGenFresh C × ((S → HashOutput) × (S → HashOutput)) ×
      ((A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) ×
        List (Query C))) := do
  let u ← $ᵗ (SeedGenFresh C)
  let p ← $ᵗ ((S → HashOutput) × (S → HashOutput))
  let r ← seedGenPrefixLog prims D A x z S parts p.1
  pure (u, p, r)

theorem evalDist_seedGenEchoJoint_last (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    seedGenEchoJoint prims D A x z S parts =ᵈ
      (($ᵗ ((S → HashOutput) × (S → HashOutput))) >>= fun p => seedGenPrefixLog prims D A x z S parts p.1 >>= fun r =>
        ($ᵗ (SeedGenFresh C)) >>= fun u => pure (u, p, r)) := by
  unfold seedGenEchoJoint
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun p => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem evalDist_seedGenEchoJoint_copy (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    seedGenEchoJoint prims D A x z S parts =ᵈ
      (($ᵗ (SeedGenFresh C)) >>= fun u => ($ᵗ (S → HashOutput)) >>= fun a =>
        seedGenPrefixLog prims D A x z S parts a >>= fun r =>
        ($ᵗ (S → HashOutput)) >>= fun a' => pure (u, (a, a'), r)) := by
  unfold seedGenEchoJoint
  refine EvalDistEq.bind_right _ fun u => ?_
  rw [uniformSample_prod_bind]
  refine EvalDistEq.bind_right _ fun a => ?_
  dsimp only
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem probEvent_seedGenEchoJoint_collide_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) :
    Pr{let t ← seedGenEchoJoint prims D A x z S parts}[
      SeedGenCollide prims D S hsk (seedGenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1 t.2.1.2] ≤
      (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [probEvent_congr_evalDist (evalDist_seedGenEchoJoint_copy prims D A x z S parts)]
  refine probEvent_bind_le_const _ _ _ _ fun u _ => probEvent_bind_le_const _ _ _ _ fun a _ =>
    probEvent_bind_le_const _ _ _ _ fun r _ => ?_
  rw [bind_pure_comp, prEvent_map]
  have h := probEvent_seedGenCollide_le prims D S hsk (seedGenFiniteTotal prims S a) parts r.1 u
  exact h

theorem probEvent_seedGenEchoJoint_log_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) (q : ℕ)
    (hq : ∀ a, ∀ r ∈ support (seedGenPrefixLog prims D A x z S parts a), (r.2.filter fun v => ¬ IsFixed v).length ≤ q) :
    Pr{let t ← seedGenEchoJoint prims D A x z S parts}[∃ v ∈ t.2.2.2, SeedGenEchoCell D t.1 v] ≤
      (q : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  rw [probEvent_congr_evalDist (evalDist_seedGenEchoJoint_last prims D A x z S parts)]
  refine probEvent_bind_le_const _ _ _ _ fun p _ => probEvent_bind_le_const _ _ _ _ fun r hr => ?_
  rw [bind_pure_comp, prEvent_map]
  exact probEvent_seedGenLogHit_le D r.2 q (hq p.1 r hr)

theorem probEvent_seedGenEchoJoint_honest_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    Pr{let t ← seedGenEchoJoint prims D A x z S parts}[
      SeedGenHonestHit prims D (seedGenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1] ≤
      ((C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  rw [probEvent_congr_evalDist (evalDist_seedGenEchoJoint_last prims D A x z S parts)]
  refine probEvent_bind_le_const _ _ _ _ fun p _ => probEvent_bind_le_const _ _ _ _ fun r _ => ?_
  rw [bind_pure_comp, prEvent_map]
  have h := probEvent_seedGenHonestHit_le prims D (seedGenFiniteTotal prims S p.1) parts r.1
  exact h

open OracleComp.ProgramLogic.Relational in
/-- On the mixed oracle, an echo collision needs a collision of the copy, a logged echo cell, or an
honest echo cell. -/
theorem probEvent_seedGenIrr_mix_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) (u : SeedGenFresh C) (a a' : S → HashOutput) :
    Pr{let π ← simulateQ (fixedLocal prims (seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a')))
        (seedGenRefPrefix prims D (seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a'))
          A x z parts)}[
      seedGenIrr prims D (seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a'))
        parts π u] ≤
    Pr{let r ← simulateQ (fixedLocal prims (seedGenFiniteTotal prims S a))
        (seedGenHashLog (seedGenRefPrefix prims D (seedGenFiniteTotal prims S a) A x z parts))}[
      SeedGenCollide prims D S hsk (seedGenFiniteTotal prims S a) parts r.1 u a' ∨
        (∃ v ∈ r.2, SeedGenEchoCell D u v) ∨ SeedGenHonestHit prims D (seedGenFiniteTotal prims S a) parts r.1 u] := by
  set hm := seedGenFiniteTotal prims S (seedGenMix (fun s : S => SeedGenEchoCell D u s.1) a a') with hhm
  set ha := seedGenFiniteTotal prims S a with hha
  have hoff : ∀ v, ¬ SeedGenEchoCell D u v → hm v = ha v := seedGenFiniteTotal_mix_off prims D S u a a'
  have hc : ∀ ph b c l, hm (.commit ph b c l) = ha (.commit ph b c l) := fun ph b c l =>
    hoff _ fun hc => by obtain ⟨l', hl'⟩ := seedGenEchoCell_sharedKeys hc; cases hl'
  rw [seedGenRefPrefix_eq_V, seedGenRefPrefixV_congr prims D hm ha hc, seedGenRefPrefix_eq_V]
  have R := relTriple_seedGenRefPrefixV prims D ha hm ha (SeedGenEchoCell D u) hoff
    (seedGenRefVisible prims D hm parts) (seedGenRefVisible prims D ha parts) A x z parts
  refine prEvent_le_of_relTriple (relTriple_symm R) fun y r hry hy => ?_
  rcases hry with hl | hv | he
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr (seedGenHonestHit_of_viewDiff prims D S parts a a' r.1 u hv))
  · subst he
    exact Or.inl (seedGenIrr_mix_collide prims D S hsk parts a a' r.1 u hy)

/-- The prefix of the reference run. -/
def seedGenRefRun (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (S : Finset (Query C)) (parts : C.Party → Parts C) (a : S → HashOutput) :
    ProbComp (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :=
  simulateQ (fixedLocal prims (seedGenFiniteTotal prims S a))
    (seedGenRefPrefix prims D (seedGenFiniteTotal prims S a) A x z parts)

theorem probOutput_true_map_decide {α : Type} (oa : ProbComp α) (P : α → Prop) :
    Pr{let z ← (fun a => decide (P a)) <$> oa}[z = true] = Pr{let z ← oa}[P z] := by
  rw [prEvent_map]
  simp

/-- One fresh table: the echo collision on the prefix, through the mixed oracle. -/
theorem probEvent_seedGenIrr_le_u (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) (u : SeedGenFresh C) :
    Pr{let s ← ($ᵗ (S → HashOutput)) >>= fun a => (fun π => (a, π)) <$> seedGenRefRun prims D A x z S parts a}[
      seedGenIrr prims D (seedGenFiniteTotal prims S s.1) parts s.2 u] ≤
    Pr{let s ← ($ᵗ ((S → HashOutput) × (S → HashOutput))) >>= fun p =>
        (fun r => (p, r)) <$> seedGenPrefixLog prims D A x z S parts p.1}[
      SeedGenCollide prims D S hsk (seedGenFiniteTotal prims S s.1.1) parts s.2.1 u s.1.2 ∨
        (∃ v ∈ s.2.2, SeedGenEchoCell D u v) ∨
        SeedGenHonestHit prims D (seedGenFiniteTotal prims S s.1.1) parts s.2.1 u] := by
  let k : (S → HashOutput) → ProbComp Bool := fun b =>
    (fun π => decide (seedGenIrr prims D (seedGenFiniteTotal prims S b) parts π u)) <$> seedGenRefRun prims D A x z S parts b
  have hl : Pr{let s ← ($ᵗ (S → HashOutput)) >>= fun a => (fun π => (a, π)) <$> seedGenRefRun prims D A x z S parts a}[
      seedGenIrr prims D (seedGenFiniteTotal prims S s.1) parts s.2 u] =
      Pr{let z ← ($ᵗ (S → HashOutput)) >>= k}[z = true] := by
    rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun a => ?_
    rw [prEvent_map, probOutput_true_map_decide]
  rw [hl, ← (evalDist_bind_seedGenMix (fun s : S => SeedGenEchoCell D u s.1) k).prEvent_eq (· = true),
    OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun p => mul_le_mul_right ?_ _
  rw [probOutput_true_map_decide, prEvent_map]
  exact probEvent_seedGenIrr_mix_le prims D A x z S hsk parts u p.1 p.2

theorem evalDist_seedGenStageBSampler_reorder (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    ((fun w => (w.2.2.1, w.1, w.2.1)) <$> seedGenStageBSampler prims D A x z S parts) =ᵈ
      (($ᵗ (SeedGenFresh C)) >>= fun u => (fun s => (u, s)) <$>
        (($ᵗ (S → HashOutput)) >>= fun a => (fun π => (a, π)) <$> seedGenRefRun prims D A x z S parts a)) := by
  unfold seedGenStageBSampler seedGenRefRun
  simp only [map_bind, map_pure]
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  refine EvalDistEq.bind_right _ fun a => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun u => ?_
  rw [Functor.map_map, map_eq_bind_pure_comp]
  refine EvalDistEq.bind_right _ fun π => ?_
  exact evalDist_uniform_bind_const (α := SeedGenFresh C) (pure _)

theorem seedGenEchoJoint_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    seedGenEchoJoint prims D A x z S parts =
      ($ᵗ (SeedGenFresh C)) >>= fun u => (fun s => (u, s)) <$>
        (($ᵗ ((S → HashOutput) × (S → HashOutput))) >>= fun p =>
          (fun r => (p, r)) <$> seedGenPrefixLog prims D A x z S parts p.1) := by
  unfold seedGenEchoJoint
  simp only [map_bind, Functor.map_map, bind_pure_comp]

/-- On one choice of parts, an echo collision needs a collision of the independent copy, a logged
echo cell, or an honest echo cell. -/
theorem probEvent_seedGenEchoIrregular_le_joint (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) :
    Pr{let w ← seedGenStageBSampler prims D A x z S parts}[SeedGenEchoIrregular prims D A S (parts, w) w.2.2.1] ≤
    Pr{let t ← seedGenEchoJoint prims D A x z S parts}[
      SeedGenCollide prims D S hsk (seedGenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1 t.2.1.2 ∨
        (∃ v ∈ t.2.2.2, SeedGenEchoCell D t.1 v) ∨
        SeedGenHonestHit prims D (seedGenFiniteTotal prims S t.2.1.1) parts t.2.2.1 t.1] := by
  have h1 : Pr{let w ← seedGenStageBSampler prims D A x z S parts}[
      SeedGenEchoIrregular prims D A S (parts, w) w.2.2.1] =
      Pr{let t ← (fun w => (w.2.2.1, w.1, w.2.1)) <$> seedGenStageBSampler prims D A x z S parts}[
        seedGenIrr prims D (seedGenFiniteTotal prims S t.2.1) parts t.2.2 t.1] := by
    rw [prEvent_map]
    rfl
  rw [h1, probEvent_congr_evalDist (evalDist_seedGenStageBSampler_reorder prims D A x z S parts),
    seedGenEchoJoint_eq]
  refine probEvent_bind_mono_of _ _ _ _ _ fun u => ?_
  rw [prEvent_map, prEvent_map]
  have h := probEvent_seedGenIrr_le_u prims D A x z S hsk parts u
  exact h

theorem exists_mem_support_probComp {α : Type} (oa : ProbComp α) : ∃ x, x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨x, by simp⟩
  | query_bind t mx ih =>
      obtain ⟨x, hx⟩ := ih default
      exact ⟨x, (mem_support_bind_iff _ _ _).2 ⟨default, mem_support_query t default, hx⟩⟩

/-- The logged prefix has at most `q` counted calls. -/
theorem seedGenPrefixLog_length_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (a : S → HashOutput) (r) (hr : r ∈ support (seedGenPrefixLog prims D A x z S parts a)) :
    (r.2.filter fun v => ¬ IsFixed v).length ≤ q := by
  set h := seedGenFiniteTotal prims S a
  obtain ⟨y, hy⟩ := exists_mem_support_probComp (simulateQ (fixedLocal prims h)
    (seedGenHashLog (Z (r.1.1, seedGenRefOutputs prims D h (fun _ => 0) parts r.1.2))))
  have hk : (y.1, r.2 ++ y.2) ∈ support (setupReferenceKernel .seedGen prims D h (fun _ => 0) A x z Z parts) := by
    unfold setupReferenceKernel
    rw [seedGenReferenceLocalGame_eq_prefix, seedGenHashLog_bind]
    simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff]
    exact ⟨r, hr, y, hy, rfl⟩
  have := setupReferenceKernel_random_length_le .seedGen prims D h (fun _ => 0) A x z Z q hq parts _ hk
  simp only [List.filter_append, List.length_append] at this
  omega

/-- On one choice of parts, the echo collision costs `(1 + q + n²) |pairs| / 2^256`. -/
theorem probEvent_seedGenEchoIrregular_parts_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .seedGen ((sharedTerms i j).map f) ∈ S)
    (parts : C.Party → Parts C) :
    Pr{let w ← seedGenStageBSampler prims D A x z S parts}[SeedGenEchoIrregular prims D A S (parts, w) w.2.2.1] ≤
      ((1 + q + C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
  refine (probEvent_seedGenEchoIrregular_le_joint prims D A x z S hsk parts).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add le_rfl (prEvent_or_le (seedGenEchoJoint prims D A x z S parts) _ _)).trans ?_
  have h1 := probEvent_seedGenEchoJoint_collide_le prims D A x z S hsk parts
  have h2 := probEvent_seedGenEchoJoint_log_le prims D A x z S parts q
    (fun a r hr => seedGenPrefixLog_length_le prims D A x z Z q hq S parts a r hr)
  have h3 := probEvent_seedGenEchoJoint_honest_le prims D A x z S parts
  calc _ ≤ (Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ +
        ((q : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
          ((C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹)) :=
        add_le_add h1 (add_le_add h2 h3)
    _ = _ := by push_cast; ring

end EchoFresh

section Arith

variable {C : Committee}

theorem seedGenFinish_card_term : Fintype.card C.Term = termCount C := by
  simp [Committee.Term, Fintype.card_finset_len, termCount]

theorem seedGenFinish_card_pair : Fintype.card C.Pair = C.n.choose 2 := by
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
theorem seedGenEcho_arith (q : ℕ) :
    4 * ((1 + q + C.n * C.n) * C.n.choose 2) + 4 * (termCount C ^ 2 + 2 * C.n.choose 2 ^ 2 +
      q * (termCount C + C.n.choose 2)) ≤ (q + seedGenSecrets C) ^ 2 := by
  have hn : 1 ≤ C.n := by have := C.one_le_t; unfold Committee.n; omega
  have hP : 2 * C.n.choose 2 ≤ C.n * C.n := by
    rw [Nat.choose_two_right]
    have := Nat.div_mul_le_self (C.n * (C.n - 1)) 2
    have h2 : C.n * (C.n - 1) ≤ C.n * C.n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  set P := C.n.choose 2
  set T := termCount C
  set n := C.n
  have hs : 2 * T + 2 * (n * n) + P ≤ seedGenSecrets C := by
    unfold seedGenSecrets
    have : T ≤ n * T := Nat.le_mul_of_pos_left T hn
    nlinarith
  have hs' : 4 * T + 8 * P ≤ 2 * seedGenSecrets C := by omega
  set s := seedGenSecrets C
  have hsq : (2 * T + 2 * (n * n) + P) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs 2
  have hn2 : 1 ≤ n * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith [hsq, hP, hn2, Nat.zero_le (q * s), Nat.zero_le (T * P), Nat.zero_le (n * n * P)]

end Arith

section EchoFreshMain

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The echo-collision bound on a domain with every echo input. -/
theorem seedGenEchoFreshExt : SeedGenEchoFreshExt (C := C) (E := E) prims := by
  intro D A x z Z q hq S _ hsk
  have hb : Pr{let r ← seedGenPartsKernel (seedGenStageBSampler prims D A x z S)}[
      SeedGenEchoIrregular prims D A S r r.2.2.2.1] ≤
      ((1 + q + C.n * C.n : ℕ) : ℝ≥0∞) * ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) := by
    rw [probEvent_seedGenPartsKernel_eq_tsum (seedGenStageBSampler prims D A x z S)
      (fun parts w => SeedGenEchoIrregular prims D A S (parts, w) w.2.2.1)]
    calc _ ≤ ∑' parts, Pr{let z ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)}[z = parts] *
          (((1 + q + C.n * C.n : ℕ) : ℝ≥0∞) *
            ((Fintype.card C.Pair : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹)) :=
          ENNReal.tsum_le_tsum fun parts => mul_le_mul_right
            (probEvent_seedGenEchoIrregular_parts_le prims D A x z Z q hq S hsk parts) _
      _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          refine mul_le_of_le_one_left' ?_
          exact OracleComp.tsum_prEvent_le_one _
  rw [← mul_assoc, ← Nat.cast_mul] at hb
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)) hb
  rw [toReal_nat_mul_inv_card] at ht
  refine ht.trans ?_
  have ha := seedGenEcho_arith (C := C) q
  unfold seedGenHashError seedGenStageAError seedGenClashCount seedGenGuessNames
  rw [seedGenFinish_card_pair, seedGenFinish_card_term]
  have ha' : (4 * ((1 + q + C.n * C.n) * C.n.choose 2) + 4 * (termCount C ^ 2 + 2 * C.n.choose 2 ^ 2 +
      q * (termCount C + C.n.choose 2)) : ℝ) ≤ ((q + seedGenSecrets C) ^ 2 : ℕ) := by exact_mod_cast ha
  push_cast at ha' ⊢
  rw [div_le_iff₀ (by positivity)]
  have h256 : (0 : ℝ) < 2 ^ 256 := by positivity
  field_simp
  nlinarith [ha']

end EchoFreshMain

section Main

variable {C : Committee} {E : Type} (prims : Primitives)

/-- `SeedGenSecurityStatement`, from the known half `SeedGenKnownMismatch`. -/
theorem seedGenSecurityComplete (hK : SeedGenKnownMismatch (C := C) (E := E) prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  seedGenSecurity_of_halves prims
    (seedGenHiddenDistance_of_fresh prims (seedGenHiddenFresh_of_echoFreshExt prims (seedGenEchoFreshExt prims))) hK

end Main

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.seedGenSecurityComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.seedGenSecurityComplete
