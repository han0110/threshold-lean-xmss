import ThresholdLeanXmssSecurity.Proof.SeedGenSecurity
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The stages of the hidden half of the setup security

This module holds the stages of the hidden half on the relabeled reference runs
(`setupSwappedMixture`). `setupSwapped_le_of_ext` of `Proof/SeedGenFinish.lean` uses them, and
`setupHiddenFresh_of_echoFreshExt` uses its bound to prove `SetupHiddenFresh`.

The hidden half is reduced to one echo-collision event, `SetupEchoIrregular`.

1. Stage A (`setupStageA`) replaces the relabeled oracle by the independent oracle. The
   relabeled oracle answers the canonical hidden inputs with the dealer's table. The two runs can
   differ only in two cases. The parts clash (`SeedGenClash`, at most `seedGenClashCount / 2^256`),
   or a call of the adversary or the distinguisher hits a canonical hidden input (at most
   `q (|terms| + |pairs|) / 2^256`). Without a clash, no honest derivation of an exposed key reads a
   canonical hidden input.
2. Stage B (`setupStageB_parts`) works on the independent run. There the table enters only the
   hidden coordinates of the outputs and the receivers. The run splits into a table-free
   transcript and the outputs of the table. The fresh keys of `seedGenHiddenZ` and the table are two
   independent fresh tables, so the gap is at most the probability that their receivers differ.
3. The receivers of two tables agree unless one of them makes an echo collision on two honest
   operators that share a hidden term (`setupReferenceData_receivers_hidden`).
4. `SetupEchoIrregular` is such a collision on the independent run (`setupReceiversGap_irregular`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Gaps of mixtures -/

section Mixture

/-- Two mixtures over one sampler whose branches are pointwise `e`-close are `E[e]`-close. -/
theorem probOutput_bind_le_add_tsum {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool) (e : α → ℝ≥0∞)
    (h : ∀ a, Pr{let z ← f a}[z = true] ≤ Pr{let z ← g a}[z = true] + e a) :
    Pr{let z ← oa >>= f}[z = true] ≤ Pr{let z ← oa >>= g}[z = true] + ∑' a, Pr{let z ← oa}[z = a] * e a := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_add]
  gcongr
  exact h a

theorem abs_probOutput_bind_sub_le {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool) (e : α → ℝ≥0∞)
    (hfg : ∀ a, Pr{let z ← f a}[z = true] ≤ Pr{let z ← g a}[z = true] + e a)
    (hgf : ∀ a, Pr{let z ← g a}[z = true] ≤ Pr{let z ← f a}[z = true] + e a)
    (hfin : ∑' a, Pr{let z ← oa}[z = a] * e a ≠ ⊤) :
    |(Pr{let z ← oa >>= f}[z = true]).toReal - (Pr{let z ← oa >>= g}[z = true]).toReal| ≤ (∑' a, Pr{let z ← oa}[z = a] * e a).toReal := by
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), hfin⟩)
    (probOutput_bind_le_add_tsum oa f g e hfg)
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), hfin⟩)
    (probOutput_bind_le_add_tsum oa g f e hgf)
  rw [ENNReal.toReal_add (prEvent_ne_top _) hfin] at h₁ h₂
  rw [abs_le]
  constructor <;> linarith

end Mixture

/-! ## Two fixed oracles that differ on a set of points -/

section FixedSwap

open OracleComp.ProgramLogic.Relational

variable {C : Committee} (prims : Primitives)

/-- Two fixed oracles that agree off `P` run a local computation identically until the logged
computation queries a point of `P`. -/
theorem relTriple_fixedLocal_swap (h₁ h₂ : Query C → HashOutput) (P : Query C → Prop)
    (hP : ∀ v, ¬ P v → h₁ v = h₂ v) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    RelTriple (simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)) (simulateQ (fixedLocal prims h₁) oa)
      (fun x y => (∃ v ∈ x.2, P v) ∨ x.1 = y) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [seedGenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr rfl)
  | query_bind t k ih =>
    rw [seedGenHashLog_bind,
      show seedGenHashLog (liftM (OracleSpec.query t) : OracleComp (LocalSpec C) _) = _ from seedGenHashLog_query t]
    simp only [simulateQ_bind, bind_map_left, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, simulateQ_pure]
    have hcont : ∀ a, RelTriple (simulateQ (fixedLocal prims h₂) (seedGenHashLog (k a)) >>= fun x =>
        (pure (x.1, seedGenLocalHashInputs t ++ x.2) : ProbComp _)) (simulateQ (fixedLocal prims h₁) (k a))
        (fun x y => (∃ v ∈ x.2, P v) ∨ x.1 = y) := by
      intro a
      rw [← bind_pure (simulateQ (fixedLocal prims h₁) (k a))]
      refine relTriple_bind (ih a) fun x y hxy => relTriple_pure_pure ?_
      rcases hxy with ⟨v, hv, hp⟩ | he
      · exact Or.inl ⟨v, List.mem_append_right _ hv, hp⟩
      · exact Or.inr he
    by_cases hb : ∃ v ∈ seedGenLocalHashInputs t, P v
    · refine relTriple_of_support_left fun z hz _ => Or.inl ?_
      obtain ⟨v, hv, hp⟩ := hb
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨a, -, x, -, rfl⟩ := hz
      exact ⟨v, List.mem_append_left _ hv, hp⟩
    · have he : fixedLocal prims h₂ t = fixedLocal prims h₁ t := by
        rcases t with n | q | x
        · rfl
        · have hq : h₁ q = h₂ q := hP q fun hq => hb ⟨q, by simp [seedGenLocalHashInputs], hq⟩
          change (pure (h₂ q) : ProbComp _) = pure (h₁ q)
          rw [hq]
        · have hq : h₁ (.streamKey x.2.1) = h₂ (.streamKey x.2.1) :=
            hP _ fun hq => hb ⟨_, by simp [seedGenLocalHashInputs], hq⟩
          change (pure (prims.aes.eval (truncateHash (h₂ (.streamKey x.2.1))) x.2.2) : ProbComp _) =
            pure (prims.aes.eval (truncateHash (h₁ (.streamKey x.2.1))) x.2.2)
          rw [hq]
      rw [he]
      exact relTriple_bind (relTriple_refl _) fun a b hab => by
        cases hab
        exact hcont a

theorem fst_simulateQ_seedGenHashLog (h : Query C → HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    Prod.fst <$> simulateQ (fixedLocal prims h) (seedGenHashLog oa) = simulateQ (fixedLocal prims h) oa := by
  rw [← simulateQ_map, seedGenHashLog_fst]

/-- The one-sided gaps of two fixed oracles that agree off `P`, in both directions. -/
theorem probOutput_fixedLocal_swap_le (h₁ h₂ : Query C → HashOutput) (P : Query C → Prop)
    (hP : ∀ v, ¬ P v → h₁ v = h₂ v) (oa : OracleComp (LocalSpec C) Bool) :
    Pr{let z ← simulateQ (fixedLocal prims h₁) oa}[z = true] ≤ Pr{let z ← simulateQ (fixedLocal prims h₂) oa}[z = true] +
        Pr{let r ← simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)}[∃ v ∈ r.2, P v] ∧
      Pr{let z ← simulateQ (fixedLocal prims h₂) oa}[z = true] ≤ Pr{let z ← simulateQ (fixedLocal prims h₁) oa}[z = true] +
        Pr{let r ← simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)}[∃ v ∈ r.2, P v] := by
  have hc := relTriple_fixedLocal_swap prims h₁ h₂ P hP oa
  have hl : Pr{let r : Bool × List (Query C) ← simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)}[
      r.1 = true] = Pr{let z ← simulateQ (fixedLocal prims h₂) oa}[z = true] := by
    rw [← fst_simulateQ_seedGenHashLog prims h₂ oa, prEvent_map]
  constructor
  · rw [← hl]
    calc _ ≤ Pr{let r : Bool × List (Query C) ← simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)}[
          r.1 = true ∨ ∃ v ∈ r.2, P v] :=
          prEvent_le_of_relTriple (relTriple_symm hc) fun b a hab hb => by
            rcases hab with hbad | he
            · exact Or.inr hbad
            · exact Or.inl (he.trans hb)
      _ ≤ _ := prEvent_or_le _ _ _
  · rw [← hl]
    calc _ ≤ Pr{let r : Bool × List (Query C) ← simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)}[
          r.1 = true ∧ ¬ ∃ v ∈ r.2, P v] +
          Pr{let r : Bool × List (Query C) ← simulateQ (fixedLocal prims h₂) (seedGenHashLog oa)}[
            ∃ v ∈ r.2, P v] :=
          le_trans (prEvent_mono _ _ _ fun r hr => by
            by_cases hb : ∃ v ∈ r.2, P v
            · exact Or.inr hb
            · exact Or.inl ⟨hr, hb⟩) (prEvent_or_le _ _ _)
      _ ≤ _ := by
          gcongr
          exact prEvent_le_of_relTriple hc fun a b hab ha => (hab.resolve_left ha.2).symm.trans ha.1

end FixedSwap

/-! ## Clashes of private parts

A clash is an equality of two distinct uniform coordinates of the parts that the hidden half reads:
the term part of the first honest holder of `T` against the part of `T'` at the same holder position,
and the two pair parts of two distinct pairs. Without a clash, the canonical inputs are distinct and
no honest derivation of an exposed key reads a canonical hidden input. -/

section Clash

variable {C : Committee}

/-- The holders of `T`, in operator order. -/
def seedGenHolderList (T : C.Term) : List C.Party := C.parties.filter (· ∈ C.holders T)

/-- The holder of `T'` at the position of the first honest holder of `T`. -/
def seedGenAligned (D : C.Coalition) (T T' : C.Term) : C.Party :=
  (seedGenHolderList T').getD ((seedGenHolderList T).idxOf (seedGenFirstHonest D (C.holders T))) (firstParty C)

/-- A clash of two distinct private coordinates. -/
def SeedGenClash (D : C.Coalition) (parts : C.Party → Parts C) : Prop :=
  (∃ T T' : C.Term, T ≠ T' ∧
    (parts (seedGenFirstHonest D (C.holders T))).term T = (parts (seedGenAligned D T T')).term T') ∨
  (∃ p p' : C.Pair, p ≠ p' ∧ ((parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2 ∨
    (parts p.1.2).pair p.1.1 = (parts p'.1.2).pair p'.1.1))

theorem list_map_eq_getD {α β : Type} {l l' : List α} {f g : α → β} (h : l.map f = l'.map g)
    [DecidableEq α] {k : α} (hk : k ∈ l) (d : α) : f k = g (l'.getD (l.idxOf k) d) := by
  have hm : l.idxOf k < l.length := List.idxOf_lt_length_iff.mpr hk
  have hlen : l.length = l'.length := by simpa using congrArg List.length h
  have he := congrArg (fun m : List β => m[l.idxOf k]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hm, List.getElem?_eq_getElem (hlen ▸ hm),
    Option.map_some, Option.some.injEq, List.getElem_idxOf hm] at he
  rw [he, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hm), Option.getD_some]

theorem seedGenFirstHonest_mem_holderList (D : C.Coalition) (T : C.Term) :
    seedGenFirstHonest D (C.holders T) ∈ seedGenHolderList T :=
  List.mem_filter.mpr ⟨by simp [Committee.parties], by simpa using (seedGenFirstHonest_holder D T).1⟩

/-- Equal term derivation inputs of two distinct terms clash, when the first honest holder of `T` reads
its own part. -/
theorem seedGenClash_of_term_eq (D : C.Coalition) (parts : C.Party → Parts C) (view : C.Party → Parts C)
    (T T' : C.Term) (hne : T ≠ T')
    (hview : view (seedGenFirstHonest D (C.holders T)) = parts (seedGenFirstHonest D (C.holders T)))
    (h : (seedGenHolderList T).map (fun j => (view j).term T) =
      (seedGenHolderList T').map (fun j => (parts j).term T')) :
    SeedGenClash D parts := by
  have he := list_map_eq_getD h (seedGenFirstHonest_mem_holderList D T) (firstParty C)
  rw [hview] at he
  exact Or.inl ⟨T, T', hne, he⟩

/-- Equal pair derivation inputs of two distinct pairs clash, when one member reads its own part. -/
theorem seedGenClash_of_pair_eq (D : C.Coalition) (parts : C.Party → Parts C) (view : C.Party → Parts C)
    (p p' : C.Pair) (hne : p ≠ p') (hview : view p.1.1 = parts p.1.1 ∨ view p.1.2 = parts p.1.2)
    (h : [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1] =
      [(parts p'.1.1).pair p'.1.2, (parts p'.1.2).pair p'.1.1]) :
    SeedGenClash D parts := by
  simp only [List.cons.injEq, and_true] at h
  rcases hview with hv | hv
  · exact Or.inr ⟨p, p', hne, Or.inl (hv ▸ h.1)⟩
  · exact Or.inr ⟨p, p', hne, Or.inr (hv ▸ h.2)⟩

/-- Without a clash, the canonical inputs are distinct. -/
theorem setupNamedInput_injective_of_clash (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (hc : ¬ SeedGenClash D parts) :
    Function.Injective (setupNamedInput phase parts) := by
  intro a b hab
  cases a with
  | parameter =>
    cases b <;> simp_all [setupNamedInput, parameterInput, termInput, pairInput]
  | term T =>
    cases b with
    | parameter => simp_all [setupNamedInput, parameterInput, termInput]
    | term T' =>
      by_contra hne
      have hT : T ≠ T' := fun h => hne (h ▸ rfl)
      simp only [setupNamedInput, termInput, Query.derive.injEq, true_and] at hab
      exact hc (seedGenClash_of_term_eq D parts parts T T' hT rfl hab)
    | pair p => simp_all [setupNamedInput, termInput, pairInput]
  | pair p =>
    cases b with
    | parameter => simp_all [setupNamedInput, parameterInput, pairInput]
    | term T' => simp_all [setupNamedInput, termInput, pairInput]
    | pair p' =>
      by_contra hne
      have hp : p ≠ p' := fun h => hne (h ▸ rfl)
      simp only [setupNamedInput, pairInput, Query.derive.injEq, true_and] at hab
      exact hc (seedGenClash_of_pair_eq D parts parts p p' hp (Or.inl rfl) hab)

theorem setupHiddenInput_derive (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) {v : Query C}
    (h : SetupHiddenInput phase D parts v) :
    (∃ T, ¬ KnownTo D.1 T ∧ v = termInput phase parts T) ∨
      (∃ p : C.Pair, p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ v = pairInput phase parts p) := by
  obtain ⟨name, hn, rfl⟩ := h
  cases name with
  | parameter => exact hn.elim
  | term T => exact Or.inl ⟨T, hn, rfl⟩
  | pair p => exact Or.inr ⟨p, hn.1, hn.2, rfl⟩

theorem not_setupHiddenInput_of_not_derive (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) {v : Query C}
    (h : ∀ k l, v ≠ .derive phase k l) : ¬ SetupHiddenInput phase D parts v := by
  intro hv
  rcases setupHiddenInput_derive (phase := phase) D parts hv with ⟨T, -, rfl⟩ | ⟨p, -, -, rfl⟩
  · exact h _ _ rfl
  · exact h _ _ rfl

theorem not_setupHiddenInput_parameter (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) (l : List HashOutput) :
    ¬ SetupHiddenInput phase D parts (.derive phase .parameter l) := by
  intro hv
  rcases setupHiddenInput_derive (phase := phase) D parts hv with ⟨T, -, he⟩ | ⟨p, -, -, he⟩
  · simp [termInput] at he
  · simp [pairInput] at he

/-- Without a clash, the derivation input of an exposed term is never a canonical hidden input. -/
theorem not_setupHiddenInput_knownTerm (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (hc : ¬ SeedGenClash D parts) (view : C.Party → Parts C) (T : C.Term) (hT : KnownTo D.1 T)
    (hview : view (seedGenFirstHonest D (C.holders T)) = parts (seedGenFirstHonest D (C.holders T))) :
    ¬ SetupHiddenInput phase D parts (.derive phase .term ((seedGenHolderList T).map fun j => (view j).term T)) := by
  intro hv
  rcases setupHiddenInput_derive (phase := phase) D parts hv with ⟨T', hT', he⟩ | ⟨p, -, -, he⟩
  · have hne : T ≠ T' := fun h => hT' (h ▸ hT)
    simp only [termInput, Query.derive.injEq, true_and] at he
    exact hc (seedGenClash_of_term_eq D parts view T T' hne hview he)
  · simp [pairInput] at he

/-- Without a clash, the derivation input of a pair with a corrupt member, read by its honest
member, is never a canonical hidden input. -/
theorem not_setupHiddenInput_crossPair (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (hc : ¬ SeedGenClash D parts) (view : C.Party → Parts C) (p : C.Pair)
    (hp : p.1.1 ∈ D.1 ∨ p.1.2 ∈ D.1) (hview : view p.1.1 = parts p.1.1 ∨ view p.1.2 = parts p.1.2) :
    ¬ SetupHiddenInput phase D parts (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1]) := by
  intro hv
  rcases setupHiddenInput_derive (phase := phase) D parts hv with ⟨T', -, he⟩ | ⟨p', h1, h2, he⟩
  · simp [termInput] at he
  · have hne : p ≠ p' := by
      rintro rfl
      rcases hp with hp | hp
      · exact h1 hp
      · exact h2 hp
    simp only [pairInput, Query.derive.injEq, true_and] at he
    exact hc (seedGenClash_of_pair_eq D parts view p p' hne hview he)

/-- The bound of a clash: one term coordinate pair for each ordered pair of terms, and two pair
coordinate pairs for each ordered pair of pairs. -/
def seedGenClashCount (C : Committee) : ℕ := Fintype.card C.Term ^ 2 + 2 * Fintype.card C.Pair ^ 2

theorem probEvent_seedGenClash_le (D : C.Coalition) :
    Pr{let z ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[SeedGenClash D z] ≤
      (seedGenClashCount C : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hterm : ∀ T T' : C.Term, Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      T ≠ T' ∧
      (parts (seedGenFirstHonest D (C.holders T))).term T = (parts (seedGenAligned D T T')).term T'] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    intro T T'
    by_cases hTT : T = T'
    · simp [hTT]
    calc _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts (seedGenFirstHonest D (C.holders T))).term T =
          (parts (seedGenAligned D T T')).term T'] := prEvent_mono _ _ _ fun _ h => h.2
      _ = _ := probEvent_parts_collision _ _ (seedGenFirstHonest D (C.holders T)) (some T) none
          (fun c parts => by simp [shiftAt, shiftParts]) (fun c parts => by
            by_cases hb : seedGenAligned D T T' = seedGenFirstHonest D (C.holders T) <;>
              simp [shiftAt, shiftParts, hb, hTT])
  have hpair : ∀ p p' : C.Pair, Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      p ≠ p' ∧ ((parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2 ∨
      (parts p.1.2).pair p.1.1 = (parts p'.1.2).pair p'.1.1)] ≤ 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    intro p p'
    by_cases hpp : p = p'
    · simp [hpp]
    have hne : ¬ (p'.1.1 = p.1.1 ∧ p'.1.2 = p.1.2) := fun ⟨h1, h2⟩ =>
      hpp (Subtype.ext (Prod.ext h1.symm h2.symm))
    calc _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2] +
          Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts p.1.2).pair p.1.1 = (parts p'.1.2).pair p'.1.1] :=
          (prEvent_mono _ _ _ fun _ h => h.2).trans (prEvent_or_le _ _ _)
      _ = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ + (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
          congr 1
          · exact probEvent_parts_collision _ _ p.1.1 none (some p.1.2)
              (fun c parts => by simp [shiftAt, shiftParts]) (fun c parts => by
                by_cases h1 : p'.1.1 = p.1.1
                · have h2 : p'.1.2 ≠ p.1.2 := fun h2 => hne ⟨h1, h2⟩
                  simp [shiftAt, shiftParts, h1, Ne.symm h2]
                · simp [shiftAt, h1])
          · have hne' : ¬ (p'.1.2 = p.1.2 ∧ p'.1.1 = p.1.1) := fun ⟨h1, h2⟩ => hne ⟨h2, h1⟩
            exact probEvent_parts_collision _ _ p.1.2 none (some p.1.1)
              (fun c parts => by simp [shiftAt, shiftParts]) (fun c parts => by
                by_cases h1 : p'.1.2 = p.1.2
                · have h2 : p'.1.1 ≠ p.1.1 := fun h2 => hne' ⟨h1, h2⟩
                  simp [shiftAt, shiftParts, h1, Ne.symm h2]
                · simp [shiftAt, h1])
      _ = _ := by rw [two_mul]
  calc _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
        (∃ T ∈ (Finset.univ : Finset C.Term), ∃ T' ∈ (Finset.univ : Finset C.Term), T ≠ T' ∧
          (parts (seedGenFirstHonest D (C.holders T))).term T = (parts (seedGenAligned D T T')).term T') ∨
        (∃ p ∈ (Finset.univ : Finset C.Pair), ∃ p' ∈ (Finset.univ : Finset C.Pair), p ≠ p' ∧
          ((parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2 ∨
            (parts p.1.2).pair p.1.1 = (parts p'.1.2).pair p'.1.1))] :=
        prEvent_mono _ _ _ fun parts h => by
          simpa only [SeedGenClash, Finset.mem_univ, true_and] using h
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ (∑ T : C.Term, ∑ T' : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        ∑ p : C.Pair, ∑ p' : C.Pair, 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        gcongr
        · refine (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun T _ => ?_)
          exact (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun T' _ => hterm T T')
        · refine (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          exact (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun p' _ => hpair p p')
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, seedGenClashCount]
        push_cast
        ring

end Clash

/-! ## Guessing a canonical hidden input, counted by the names -/

section Guess

variable {C : Committee} {E : Type}

/-- The names whose canonical inputs a guess must hit: every term and every pair. -/
def seedGenGuessNames (C : Committee) : ℕ := Fintype.card C.Term + Fintype.card C.Pair

theorem probEvent_setupHiddenInput_kernel_names (phase : Phase) (coalition : C.Coalition) (m : ℕ)
    (K : (C.Party → Parts C) → ProbComp (Fin m → Query C)) (hinv : SeedGenPrivateInvariant coalition K) :
    Pr{let p ← seedGenPartsKernel K}[∃ i : Fin m, SetupHiddenInput phase coalition p.1 (p.2 i)] ≤
      ((m * seedGenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr{let p ← seedGenPartsKernel K}[
        ∃ i ∈ (Finset.univ : Finset (Fin m)), SetupHiddenInput phase coalition p.1 (p.2 i)] := by simp
    _ ≤ ∑ i : Fin m, Pr{let p ← seedGenPartsKernel K}[SetupHiddenInput phase coalition p.1 (p.2 i)] :=
      prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _i : Fin m, ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum fun i _ => probEvent_setupHiddenInput_kernel_one phase coalition K hinv (fun r => r i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        seedGenGuessNames]
      rw [← mul_assoc]

theorem probEvent_setupHiddenInput_kernel_list_names (phase : Phase) {α : Type} (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp α) (hinv : SeedGenPrivateInvariant coalition K)
    (queries : α → List (Query C)) (m : ℕ)
    (hbound : ∀ parts r, r ∈ support (K parts) → (queries r).length ≤ m) :
    Pr{let p ← seedGenPartsKernel K}[∃ v ∈ queries p.2, SetupHiddenInput phase coalition p.1 v] ≤
      ((m * seedGenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let targets (r : α) (i : Fin m) := (queries r).getD i.val (.streamKey 0)
  let K' (parts : C.Party → Parts C) := targets <$> K parts
  have hinv' : SeedGenPrivateInvariant coalition K' := by
    constructor
    · intro a T hT c parts
      dsimp only [K']
      rw [hinv.1 a T hT c parts]
    · intro p ha hb c parts
      dsimp only [K']
      rw [hinv.2 p ha hb c parts]
  have he : seedGenPartsKernel K' =
      (fun p : (C.Party → Parts C) × α => (p.1, targets p.2)) <$> seedGenPartsKernel K := by
    simp only [seedGenPartsKernel, K', map_bind, bind_map_left, map_pure]
  have hb := probEvent_setupHiddenInput_kernel_names (phase := phase) coalition m K' hinv'
  rw [he, prEvent_map] at hb
  apply le_trans (prEvent_mono_of_support _ _ _ (fun p hp hh => ?_)) hb
  rcases p with ⟨parts, r⟩
  have hr : r ∈ support (K parts) := by
    simp only [seedGenPartsKernel, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hp
    obtain ⟨p', _, r', hr', he₁, he₂⟩ := hp
    cases he₁
    cases he₂
    exact hr'
  obtain ⟨v, hv, hh⟩ := hh
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hv
  refine ⟨⟨j, Nat.lt_of_lt_of_le hj (hbound parts r hr)⟩, ?_⟩
  simpa only [targets, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, he] using hh

/-- The reference transcript guesses a canonical hidden input with probability at most
`q * (|terms| + |pairs|) / 2^256`. -/
theorem probEvent_setupReference_hidden_guess_names (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    Pr{let p ← seedGenPartsKernel (setupReferenceKernel (phase := phase) prims coalition h table A x z Z)}[
      ∃ v ∈ p.2.2, SetupHiddenInput phase coalition p.1 v] ≤
      ((q * seedGenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hb := probEvent_setupHiddenInput_kernel_list_names (phase := phase) coalition
    (setupReferenceKernel (phase := phase) prims coalition h table A x z Z)
    (setupReferenceKernel_privateInvariant (phase := phase) prims coalition h table A x z Z)
    (fun r => r.2.filter fun v => ¬ IsFixed v) q
    (setupReferenceKernel_random_length_le (phase := phase) prims coalition h table A x z Z q hq)
  apply le_trans (prEvent_mono _ _ _ (fun p hh => ?_)) hb
  obtain ⟨v, hv, name, hn, he⟩ := hh
  refine ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, name, hn, he⟩
  apply decide_eq_true
  rw [← he]
  exact setupNamedInput_not_fixed phase p.1 name

end Guess

/-! ## The reference run reads no canonical hidden input -/

section OracleCongr

variable {C : Committee} {E : Type} (prims : Primitives)

theorem setupReferenceKeys_oracle_congr (phase : Phase) (prims : Primitives) (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (hc : ¬ SeedGenClash D parts) (hh : ∀ v, ¬ SetupHiddenInput phase D parts v → h₁ v = h₂ v)
    (i : C.Party) (hi : i ∉ D.1) :
    setupReferenceKeys phase prims D h₁ table parts revealed i = setupReferenceKeys phase prims D h₂ table parts revealed i := by
  simp only [setupReferenceKeys, seedGenMaskKeys, D_deriveKeys]
  have hview : ∀ k, k ∉ D.1 → setupCorruptView phase D parts revealed i k = parts k := by
    intro k hk
    simp [setupCorruptView, hk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · dsimp only
    split_ifs
    · exact hh _ (not_setupHiddenInput_parameter (phase := phase) D parts _)
    · rfl
  · funext T
    dsimp only
    split_ifs with hT hiT
    · exact hh _ (not_setupHiddenInput_knownTerm (phase := phase) D parts hc _ T hT
        (hview _ (seedGenFirstHonest_holder D T).2))
    · rfl
    · rfl
    · rfl
  · funext j
    dsimp only
    split_ifs with h1 h2
    · rfl
    · have hj : j ∈ D.1 := h2.resolve_left hi
      apply hh
      apply not_setupHiddenInput_crossPair (phase := phase) D parts hc
      · unfold Committee.pairOf
        split_ifs <;> simp [hj]
      · unfold Committee.pairOf
        split_ifs
        · exact Or.inl (hview i hi)
        · exact Or.inr (hview i hi)
    · rfl

theorem setupReferenceData_oracle_congr (phase : Phase) (prims : Primitives) (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (hc : ¬ SeedGenClash D parts) (hh : ∀ v, ¬ SetupHiddenInput phase D parts v → h₁ v = h₂ v) :
    setupReferenceData (phase := phase) prims D h₁ table parts commitSent revealSent =
      setupReferenceData (phase := phase) prims D h₂ table parts commitSent revealSent := by
  have hcommit : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l) := fun ph a b l =>
    hh _ (not_setupHiddenInput_of_not_derive (phase := phase) D parts fun _ _ he => by cases he)
  have hshared : ∀ ph l, h₁ (.sharedKeys ph l) = h₂ (.sharedKeys ph l) := fun ph l =>
    hh _ (not_setupHiddenInput_of_not_derive (phase := phase) D parts fun _ _ he => by cases he)
  have hactive : ∀ i, setupReferenceActive (phase := phase) D h₁ commitSent revealSent i ↔
      setupReferenceActive (phase := phase) D h₂ commitSent revealSent i := by
    intro i
    simp only [setupReferenceActive, setupReferenceOpenCheck, hcommit]
  funext i
  rw [setupReferenceData_active, setupReferenceData_active]
  by_cases ha : setupReferenceActive (phase := phase) D h₁ commitSent revealSent i
  · rw [ite_eq_left ha, ite_eq_left ((hactive i).1 ha)]
    rw [setupReferenceKeys_oracle_congr (phase := phase) prims D h₁ h₂ table parts _ hc hh i ha.1]
    simp only [sharedQueries, D_mapM, D_hashQuery, hshared]
  · rw [ite_eq_right ha, ite_eq_right (fun h => ha ((hactive i).2 h))]

theorem setupFixedCommitView_oracle_congr (phase : Phase) (prims : Primitives) (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (parts : C.Party → Parts C) (hh : ∀ v, ¬ SetupHiddenInput phase D parts v → h₁ v = h₂ v) :
    setupFixedCommitView phase (E := E) prims D h₁ parts = setupFixedCommitView phase prims D h₂ parts := by
  have hcommit : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l) := fun ph a b l =>
    hh _ (not_setupHiddenInput_of_not_derive (phase := phase) D parts fun _ _ he => by cases he)
  funext c i
  simp only [setupFixedCommitView, D_commitQueries, hcommit]

/-- Without a clash, the reference run reads its oracle only away from the canonical hidden inputs,
apart from the oracle calls of the adversary and the distinguisher. -/
theorem setupReferenceLocalGame_oracle_congr (phase : Phase) (prims : Primitives) (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C)
    (hc : ¬ SeedGenClash D parts) (hh : ∀ v, ¬ SetupHiddenInput phase D parts v → h₁ v = h₂ v) :
    setupReferenceLocalGame (phase := phase) prims D h₁ table A x z Z parts =
      setupReferenceLocalGame (phase := phase) prims D h₂ table A x z Z parts := by
  simp only [setupReferenceLocalGame, setupReferencePostCommit,
    setupFixedCommitView_oracle_congr (phase := phase) prims D h₁ h₂ parts hh,
    setupReferenceData_oracle_congr (phase := phase) prims D h₁ h₂ table parts _ _ hc hh]

end OracleCongr

/-! ## Stage A: from the relabeled oracle to an independent dealer table

The relabeled reference run answers the canonical hidden inputs with the dealer's table. The
independent reference run answers them with the oracle's own cells, so the dealer's table is
independent of the oracle. The two runs agree unless the parts clash or a call of the adversary or
the distinguisher hits a canonical hidden input. -/

section StageA

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The reference mixture whose dealer table is independent of the oracle. -/
def setupIndepMixture (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) :
    ProbComp Bool := do
  let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
  let h := seedGenFiniteTotal prims S p.1
  simulateQ (fixedLocal prims h) (setupReferenceLocalGame (phase := phase) prims D h p.2 A x z Z parts)

/-- The hit probability of one reference run with the independent table. -/
def setupIndepHit (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) (p : (S → HashOutput) × (KeyName C → HashOutput)) : ℝ≥0∞ :=
  Pr{let r ← simulateQ (fixedLocal prims (seedGenFiniteTotal prims S p.1))
      (seedGenHashLog (setupReferenceLocalGame (phase := phase) prims D (seedGenFiniteTotal prims S p.1) p.2 A x z Z parts))}[
    ∃ v ∈ r.2, SetupHiddenInput phase D parts v]

theorem setupStageA_parts (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, setupNamedInput phase parts name ∈ S) (parts : C.Party → Parts C)
    (hc : ¬ SeedGenClash D parts) (p : (S → HashOutput) × (KeyName C → HashOutput)) :
    let hs := seedGenFiniteTotal prims S (setupFiniteHiddenSwap phase D S parts (hmem parts) p).1
    let h₀ := seedGenFiniteTotal prims S p.1
    Pr{let y ← simulateQ (fixedLocal prims hs) (setupReferenceLocalGame (phase := phase) prims D hs p.2 A x z Z parts)}[y = true] ≤
        Pr{let y ← simulateQ (fixedLocal prims h₀) (setupReferenceLocalGame (phase := phase) prims D h₀ p.2 A x z Z parts)}[y = true] +
          setupIndepHit (phase := phase) prims D A x z Z S parts p ∧
      Pr{let y ← simulateQ (fixedLocal prims h₀) (setupReferenceLocalGame (phase := phase) prims D h₀ p.2 A x z Z parts)}[y = true] ≤
        Pr{let y ← simulateQ (fixedLocal prims hs) (setupReferenceLocalGame (phase := phase) prims D hs p.2 A x z Z parts)}[y = true] +
          setupIndepHit (phase := phase) prims D A x z Z S parts p := by
  intro hs h₀
  have hh : ∀ v, ¬ SetupHiddenInput phase D parts v → hs v = h₀ v := fun v hv =>
    setupFiniteHiddenSwap_total_off phase prims D S parts (hmem parts) p v hv
  rw [setupReferenceLocalGame_oracle_congr (phase := phase) prims D hs h₀ p.2 A x z Z parts hc hh]
  exact probOutput_fixedLocal_swap_le prims hs h₀ (SetupHiddenInput phase D parts) hh _

theorem probEvent_seedGenPartsKernel_eq_tsum {α : Type} (K : (C.Party → Parts C) → ProbComp α)
    (P : (C.Party → Parts C) → α → Prop) :
    Pr{let r ← seedGenPartsKernel K}[P r.1 r.2] =
      ∑' parts, Pr{let z ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)}[z = parts] *
        Pr{let z ← K parts}[P parts z] := by
  unfold seedGenPartsKernel
  rw [OracleComp.prEvent_bind_eq_tsum]
  refine tsum_congr fun parts => ?_
  congr 1
  rw [bind_pure_comp, prEvent_map]

theorem tsum_setupIndepHit_le (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    ∑' parts, Pr{let z ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)}[z = parts] *
      ∑' p, Pr{let z ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))}[z = p] * setupIndepHit (phase := phase) prims D A x z Z S parts p ≤
      ((q * seedGenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  calc _ = ∑' p, Pr{let z ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))}[z = p] *
        Pr{let r ← seedGenPartsKernel (setupReferenceKernel (phase := phase) prims D (seedGenFiniteTotal prims S p.1) p.2 A x z Z)}[
          ∃ v ∈ r.2.2, SetupHiddenInput phase D r.1 v] := by
        refine tsum_congr fun p => ?_
        rw [probEvent_seedGenPartsKernel_eq_tsum (setupReferenceKernel (phase := phase) prims D (seedGenFiniteTotal prims S p.1) p.2
          A x z Z) (fun parts r => ∃ v ∈ r.2, SetupHiddenInput phase D parts v), ← ENNReal.tsum_mul_left]
        refine tsum_congr fun parts => ?_
        simp only [setupIndepHit, setupReferenceKernel]
        ring
    _ ≤ ∑' p, Pr{let z ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))}[z = p] *
        (((q * seedGenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) :=
        ENNReal.tsum_le_tsum fun p => by
          gcongr
          exact probEvent_setupReference_hidden_guess_names (phase := phase) prims D _ _ A x z Z q hq
    _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := by
  unfold HashOutput
  exact Fintype.card_bitVec 256

theorem toReal_nat_mul_inv_card (k : ℕ) :
    ((k : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹).toReal = (k : ℝ) / 2 ^ 256 := by
  rw [card_hashOutput, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]

/-- Stage A. The relabeled reference mixture and the independent one are close. -/
theorem setupStageA (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, setupNamedInput phase parts name ∈ S) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    |(Pr{let y ← setupSwappedMixture (phase := phase) prims D A x z Z S hmem}[y = true]).toReal -
        (Pr{let y ← setupIndepMixture (phase := phase) prims D A x z Z S}[y = true]).toReal| ≤
      ((seedGenClashCount C + q * seedGenGuessNames C : ℕ) : ℝ) / 2 ^ 256 := by
  set e : (C.Party → Parts C) → ℝ≥0∞ := fun parts => (if SeedGenClash D parts then 1 else 0) +
    ∑' p, Pr{let z ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))}[z = p] * setupIndepHit (phase := phase) prims D A x z Z S parts p
    with he
  have hsum : ∑' parts, Pr{let z ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)}[z = parts] * e parts ≤
      ((seedGenClashCount C + q * seedGenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    simp only [he, mul_add, ENNReal.tsum_add]
    rw [Nat.cast_add, add_mul]
    gcongr
    · calc _ = Pr{let z ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)}[SeedGenClash D z] := by
            rw [OracleComp.prEvent_eq_tsum_ite]
            refine tsum_congr fun parts => ?_
            split_ifs <;> simp
        _ ≤ _ := probEvent_seedGenClash_le D
    · exact tsum_setupIndepHit_le (phase := phase) prims D A x z Z S q hq
  have hfin : ∑' parts, Pr{let z ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)}[z = parts] * e parts ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)) hsum
  have hbranch : ∀ parts, ¬ SeedGenClash D parts →
      (∀ p : (S → HashOutput) × (KeyName C → HashOutput),
        let hs := seedGenFiniteTotal prims S (setupFiniteHiddenSwap phase D S parts (hmem parts) p).1
        let h₀ := seedGenFiniteTotal prims S p.1
        Pr{let y ← simulateQ (fixedLocal prims hs) (setupReferenceLocalGame (phase := phase) prims D hs p.2 A x z Z parts)}[y = true] ≤
            Pr{let y ← simulateQ (fixedLocal prims h₀) (setupReferenceLocalGame (phase := phase) prims D h₀ p.2 A x z Z parts)}[y = true] +
              setupIndepHit (phase := phase) prims D A x z Z S parts p ∧
          Pr{let y ← simulateQ (fixedLocal prims h₀) (setupReferenceLocalGame (phase := phase) prims D h₀ p.2 A x z Z parts)}[y = true] ≤
            Pr{let y ← simulateQ (fixedLocal prims hs) (setupReferenceLocalGame (phase := phase) prims D hs p.2 A x z Z parts)}[y = true] +
              setupIndepHit (phase := phase) prims D A x z Z S parts p) :=
    fun parts hc p => setupStageA_parts (phase := phase) prims D A x z Z S hmem parts hc p
  have h := abs_probOutput_bind_sub_le (OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C))
    (fun parts => do
      let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
      let ht := if Function.Injective (setupNamedInput phase parts) then
        (setupFiniteHiddenSwap phase D S parts (hmem parts) p).1 else p.1
      let h := seedGenFiniteTotal prims S ht
      let table := if Function.Injective (setupNamedInput phase parts) then p.2 else
        fun name => h (setupNamedInput phase parts name)
      simulateQ (fixedLocal prims h) (setupReferenceLocalGame (phase := phase) prims D h table A x z Z parts))
    (fun parts => do
      let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
      let h := seedGenFiniteTotal prims S p.1
      simulateQ (fixedLocal prims h) (setupReferenceLocalGame (phase := phase) prims D h p.2 A x z Z parts)) e
    (fun parts => by
      by_cases hc : SeedGenClash D parts
      · exact le_trans (prEvent_le_one _) (le_add_left (by simp [he, hc]))
      · have hinj := setupNamedInput_injective_of_clash (phase := phase) D parts hc
        simp only [ite_eq_left hinj]
        refine (probOutput_bind_le_add_tsum _ _ _ _ fun p => (hbranch parts hc p).1).trans ?_
        gcongr
        simp [he, hc])
    (fun parts => by
      by_cases hc : SeedGenClash D parts
      · exact le_trans (prEvent_le_one _) (le_add_left (by simp [he, hc]))
      · have hinj := setupNamedInput_injective_of_clash (phase := phase) D parts hc
        simp only [ite_eq_left hinj]
        refine (probOutput_bind_le_add_tsum _ _ _ _ fun p => (hbranch parts hc p).2).trans ?_
        gcongr
        simp [he, hc])
    hfin
  refine h.trans ?_
  rw [← toReal_nat_mul_inv_card]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)) hsum

theorem isQueryBoundP_liftComp_bind {α β : Type} (oa : ProbComp α) (k : α → OracleComp (LocalSpec C) β)
    (n : ℕ) (hk : ∀ a, IsQueryBoundP (k a) Counted n) :
    IsQueryBoundP (liftComp oa (LocalSpec C) >>= k) Counted n := by
  have h := isQueryBoundP_bind (isQueryBoundP_liftComp_counted oa) (fun a _ => hk a)
  rwa [Nat.zero_add] at h

/-- `seedGenHiddenZ` with its two samplers as parameters. A statement that shows the uniform sampler of
`C.Term → HashOutput` inside a query bound makes the elaborator time out, so the bound is proved for
any sampler. -/
def seedGenHiddenZGen (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C))
    (s₁ : ProbComp (C.Term → HashOutput)) (s₂ : ProbComp (C.Pair → HashOutput)) : Distinguisher C σ (Keys C) :=
  fun r => do
    let seeds ← liftComp s₁ (LocalSpec C)
    let pairs ← liftComp s₂ (LocalSpec C)
    Z (r.1, fun i => (r.2 i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 seeds pairs i))

theorem seedGenHiddenZ_eq_gen (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C)) :
    seedGenHiddenZ D Z = seedGenHiddenZGen D Z ($ᵗ _) ($ᵗ _) := rfl

/-- Fresh hidden keys cost the distinguisher no counted call. -/
theorem isQueryBounded_seedGenHiddenZ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    IsQueryBounded A (seedGenHiddenZ D Z) setupRounds q := by
  rw [seedGenHiddenZ_eq_gen]
  generalize ($ᵗ (C.Term → HashOutput) : ProbComp _) = s₁
  generalize ($ᵗ (C.Pair → HashOutput) : ProbComp _) = s₂
  obtain ⟨start, step, final, hsum, hq⟩ := hq
  refine ⟨start, step, final, hsum, ?_⟩
  refine ⟨hq.1, hq.2.1, hq.2.2.1, fun r => ?_⟩
  exact isQueryBoundP_liftComp_bind s₁ _ final fun _ => isQueryBoundP_liftComp_bind s₂ _ final fun _ =>
    hq.2.2.2 _

end StageA

/-! ## The reference run as a table-free transcript and table-dependent outputs -/

section Transcript

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The corrupt recipients' echo messages, which no table changes. -/
def setupRefVisible (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (sent rsent : C.Party → Mail C E) : C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    (setupEchoDataStep phase i (setupReferenceData (phase := phase) prims D h (fun _ => 0) parts sent rsent i)).outbox c else none

/-- The reference run up to the last adversary round. It records the final adversary state and, when
an honest operator reaches the echo, the three corrupt mails. -/
def setupRefPrefix (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) := do
  let state ← A.start (corruptInputs D x) z
  let r ← A.round state (setupFixedCommitView phase prims D h parts)
  if ∀ i, i ∉ D.1 → seedGenCommitAborted D r.2 i = true then pure (r.1, none) else do
    let r' ← A.round r.1 (setupReferenceRevealView phase D parts r.2)
    if ∀ i, i ∉ D.1 → ¬ setupReferenceActive (phase := phase) D h r.2 r'.2 i then pure (r'.1, none) else do
      let r'' ← A.round r'.1 (setupRefVisible (phase := phase) prims D h parts r.2 r'.2)
      pure (r''.1, some (r.2, r'.2, r''.2))

/-- The honest outputs of a transcript under a table. -/
def setupRefOutputs (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : C.Party → Option (Keys C) :=
  match m with
  | none => fun _ => none
  | some (sent, rsent, esent) => setupEchoDataOutput phase D (setupReferenceData (phase := phase) prims D h table parts sent rsent) esent

theorem setupReferenceLocalGame_eq_prefix (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    setupReferenceLocalGame (phase := phase) prims D h table A x z Z parts =
      setupRefPrefix (phase := phase) prims D h A x z parts >>= fun π => Z (π.1, setupRefOutputs (phase := phase) prims D h table parts π.2) := by
  unfold setupReferenceLocalGame setupRefPrefix
  simp only [bind_assoc]
  refine bind_congr fun state => bind_congr fun r => ?_
  unfold setupReferencePostCommit
  split_ifs with ha
  · simp [setupRefOutputs]
  · simp only [bind_assoc]
    refine bind_congr fun r' => ?_
    unfold setupFinishLocal
    have hnone : (∀ i, i ∉ D.1 → setupReferenceData (phase := phase) prims D h table parts r.2 r'.2 i = none) ↔
        ∀ i, i ∉ D.1 → ¬ setupReferenceActive (phase := phase) D h r.2 r'.2 i := by
      refine forall_congr' fun i => forall_congr' fun _ => ?_
      rw [setupReferenceData_active]
      split_ifs <;> simp_all
    have hvis : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
        (setupEchoDataStep phase (E := E) i (setupReferenceData (phase := phase) prims D h table parts r.2 r'.2 i)).outbox c
        else none) = setupRefVisible (phase := phase) prims D h parts r.2 r'.2 := by
      funext c i
      unfold setupRefVisible
      split_ifs with hc
      · exact setupReferenceData_visible (phase := phase) prims D h table (fun _ => 0) parts r.2 r'.2 i c hc.1
      · rfl
    simp only [hnone]
    split_ifs with hb
    · simp [setupRefOutputs]
    · rw [hvis]
      simp [setupRefOutputs]

/-- The keys that an honest operator outputs under a table, if it accepts. -/
def setupRefKeysOf (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (i : C.Party) : Keys C :=
  match m with
  | none => default
  | some (_, rsent, _) => keysOf (setupReferenceKeys phase prims D h table parts (fun i j => rsent j i) i)

/-- The receivers of one table with the keys of another. -/
def setupRefMixedOutputs (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (table keys : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : C.Party → Option (Keys C) :=
  fun i => if (setupRefOutputs (phase := phase) prims D h table parts m i).isSome then
    some (setupRefKeysOf (phase := phase) prims D h keys parts m i) else none

theorem setupRefOutputs_eq_mixed (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :
    setupRefOutputs (phase := phase) prims D h table parts m = setupRefMixedOutputs (phase := phase) prims D h table table parts m := by
  funext i
  unfold setupRefMixedOutputs
  rcases m with _ | ⟨sent, rsent, esent⟩
  · rfl
  · simp only [setupRefOutputs, setupRefKeysOf, setupEchoDataOutput]
    rw [setupReferenceData_active]
    split_ifs <;> simp_all

theorem setupRefOutputs_honest (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (i : C.Party)
    (hs : (setupRefOutputs (phase := phase) prims D h table parts m i).isSome) : i ∉ D.1 := by
  rcases m with _ | ⟨sent, rsent, esent⟩
  · simp [setupRefOutputs] at hs
  · intro hi
    simp only [setupRefOutputs, setupEchoDataOutput] at hs
    split at hs
    · simp at hs
    · simp [hi] at hs

/-- The table of fresh term seeds and pair keys. -/
def seedGenTableOf (s : C.Term → HashOutput) (p : C.Pair → HashOutput) : KeyName C → HashOutput
  | .parameter => 0
  | .term T => s T
  | .pair q => p q

/-- `seedGenHiddenZ` turns the outputs of one table into the keys of the fresh table. -/
theorem setupRefMixedOutputs_overlay (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput)
    (table keys : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (s : C.Term → HashOutput) (p : C.Pair → HashOutput) :
    (fun i => (setupRefMixedOutputs (phase := phase) prims D h table keys parts m i).map fun k =>
      seedGenHiddenOverlay D i k (dealtKeys 0 s p i)) =
      setupRefMixedOutputs (phase := phase) prims D h table (seedGenTableOf s p) parts m := by
  funext i
  unfold setupRefMixedOutputs
  split_ifs with hs
  · have hi := setupRefOutputs_honest (phase := phase) prims D h table parts m i hs
    rcases m with _ | ⟨sent, rsent, esent⟩
    · simp [setupRefOutputs] at hs
    · simp only [Option.map_some, setupRefKeysOf, setupReferenceKeys, seedGenMaskKeys, keysOf,
        seedGenHiddenOverlay, dealtKeys, Option.some.injEq]
      congr 1
      · funext T
        split_ifs <;> simp_all [seedGenTableOf]
      · funext j
        split_ifs <;> simp_all [seedGenTableOf]
  · rfl

/-- The term and pair coordinates of a table. -/
def seedGenRestrict (τ : KeyName C → HashOutput) : (C.Term → HashOutput) × (C.Pair → HashOutput) :=
  (fun T => τ (.term T), fun q => τ (.pair q))

theorem setupReferenceKeys_restrict (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (τ : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) :
    setupReferenceKeys phase prims D h τ parts revealed =
      setupReferenceKeys phase prims D h (seedGenTableOf (seedGenRestrict τ).1 (seedGenRestrict τ).2) parts revealed := by
  funext i
  simp only [setupReferenceKeys, seedGenMaskKeys, seedGenTableOf, seedGenRestrict]

theorem setupRefMixedOutputs_restrict (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput)
    (table keys : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :
    setupRefMixedOutputs (phase := phase) prims D h table keys parts m =
      setupRefMixedOutputs (phase := phase) prims D h (seedGenTableOf (seedGenRestrict table).1 (seedGenRestrict table).2)
        (seedGenTableOf (seedGenRestrict keys).1 (seedGenRestrict keys).2) parts m := by
  have hd : ∀ sent rsent : C.Party → Mail C E, setupReferenceData (phase := phase) prims D h table parts sent rsent =
      setupReferenceData (phase := phase) prims D h (seedGenTableOf (seedGenRestrict table).1 (seedGenRestrict table).2)
        parts sent rsent := by
    intro sent rsent
    unfold setupReferenceData
    rw [setupReferenceKeys_restrict (phase := phase) prims D h table]
  funext i
  rcases m with _ | ⟨sent, rsent, esent⟩
  · rfl
  · simp only [setupRefMixedOutputs, setupRefOutputs, setupRefKeysOf, hd]
    rw [setupReferenceKeys_restrict (phase := phase) prims D h keys]
    rfl

/-- The receivers decide the mixed outputs. -/
theorem setupRefMixedOutputs_receivers (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput)
    (table table' keys : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (hr : (fun i => (setupRefOutputs (phase := phase) prims D h table parts m i).isSome) =
      fun i => (setupRefOutputs (phase := phase) prims D h table' parts m i).isSome) :
    setupRefMixedOutputs (phase := phase) prims D h table keys parts m = setupRefMixedOutputs (phase := phase) prims D h table' keys parts m := by
  funext i
  simp only [setupRefMixedOutputs, congrFun hr i]

theorem evalDist_seedGenRestrict :
    (seedGenRestrict <$> ($ᵗ (KeyName C → HashOutput))) =ᵈ
      $ᵗ ((C.Term → HashOutput) × (C.Pair → HashOutput)) := by
  let e : C.Term ⊕ C.Pair → KeyName C := Sum.elim KeyName.term KeyName.pair
  have he : Function.Injective e := by
    rintro (a | a) (b | b) hab <;> simp_all [e]
  have h₁ := evalDistEq_uniformSample_map_comp_injective (R := HashOutput) he
  let φ := Equiv.sumArrowEquivProdArrow C.Term C.Pair HashOutput
  have hφ : seedGenRestrict = φ ∘ fun g : KeyName C → HashOutput => g ∘ e := by
    funext g
    rfl
  have hmap : seedGenRestrict <$> ($ᵗ (KeyName C → HashOutput)) =
      φ <$> ((fun g : KeyName C → HashOutput => g ∘ e) <$> ($ᵗ (KeyName C → HashOutput))) := by
    rw [Functor.map_map, hφ]
    rfl
  rw [hmap]
  exact (h₁.map φ).trans (SampleableType.map_uniformSample_evalDistEq_of_bijective φ.bijective)

end Transcript

/-! ## Receivers under two tables, up to echo collisions of pairs that share a hidden term -/

section Receivers

variable {C : Committee} {E : Type} (prims : Primitives)

/-- Two operators share a term that no corrupt operator holds. -/
def SeedGenShareHidden (D : C.Coalition) (i j : C.Party) : Prop :=
  ∃ T, ¬ KnownTo D.1 T ∧ i ∈ C.holders T ∧ j ∈ C.holders T

theorem setup_echo_eq_invariant_pair (phase : Phase) (prims : Primitives) (co : C.Coalition) (h : Query C → HashOutput) (i j : C.Party)
    (ki kj ki' kj' : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hpi : ki.1 = ki'.1) (hpj : kj.1 = kj'.1)
    (hki : ∀ T, KnownTo co.1 T → ki.2.1 T = ki'.2.1 T)
    (hkj : ∀ T, KnownTo co.1 T → kj.2.1 T = kj'.2.1 T)
    (hhidden : ∀ T, ¬ KnownTo co.1 T → i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T)
    (hhidden' : ∀ T, ¬ KnownTo co.1 T → i ∈ C.holders T → j ∈ C.holders T → ki'.2.1 T = kj'.2.1 T)
    (hreg : SeedGenShareHidden co i j →
      (h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys phase ((sharedTerms j i).map kj.2.1)) ∧
      (h (.sharedKeys phase ((sharedTerms i j).map ki'.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj'.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki'.2.1) =
        Query.sharedKeys phase ((sharedTerms j i).map kj'.2.1))) :
    (echoOf phase ki (D prims h (sharedQueries phase i ki)) j =
      echoOf phase kj (D prims h (sharedQueries phase j kj)) i) ↔
    (echoOf phase ki' (D prims h (sharedQueries phase i ki')) j =
      echoOf phase kj' (D prims h (sharedQueries phase j kj')) i) := by
  by_cases hs : SeedGenShareHidden co i j
  · exact setup_echo_eq_hidden_invariant phase prims co h h i j ki kj ki' kj' hpi hpj hki hkj hhidden hhidden'
      (hreg hs).1 (hreg hs).2
  · have hknown : ∀ T, i ∈ C.holders T → j ∈ C.holders T → KnownTo co.1 T := fun T hi hj =>
      by_contra fun hT => hs ⟨T, hT, hi, hj⟩
    have hli : (sharedTerms i j).map ki.2.1 = (sharedTerms i j).map ki'.2.1 :=
      List.map_congr_left fun T hT => by
        simp only [sharedTerms, List.mem_filter, decide_eq_true_eq] at hT
        exact hki T (hknown T hT.2.1 hT.2.2)
    have hlj : (sharedTerms j i).map kj.2.1 = (sharedTerms j i).map kj'.2.1 :=
      List.map_congr_left fun T hT => by
        simp only [sharedTerms, List.mem_filter, decide_eq_true_eq] at hT
        exact hkj T (hknown T hT.2.2 hT.2.1)
    simp only [echoOf, D_sharedQueries_at, hli, hlj, hpi, hpj]

/-- No echo collision on a pair of honest operators that share a hidden term. -/
def SetupEchoRegularHidden (phase : Phase) (co : C.Coalition) (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : Prop :=
  ∀ i j, i ∉ co.1 → j ∉ co.1 → SeedGenShareHidden co i j →
    h (.sharedKeys phase ((sharedTerms i j).map (keys i).2.1)) =
      h (.sharedKeys phase ((sharedTerms j i).map (keys j).2.1)) →
    Query.sharedKeys (C := C) phase ((sharedTerms i j).map (keys i).2.1) =
      Query.sharedKeys phase ((sharedTerms j i).map (keys j).2.1)

theorem setup_echoCheck_invariant_hidden (phase : Phase) (prims : Primitives) (co : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys keys' : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hp : ∀ i, i ∉ co.1 → (keys i).1 = (keys' i).1)
    (hk : ∀ i T, i ∉ co.1 → KnownTo co.1 T → (keys i).2.1 T = (keys' i).2.1 T)
    (hh : ∀ i j T, i ∉ co.1 → j ∉ co.1 → ¬ KnownTo co.1 T →
      i ∈ C.holders T → j ∈ C.holders T → (keys i).2.1 T = (keys j).2.1 T)
    (hh' : ∀ i j T, i ∉ co.1 → j ∉ co.1 → ¬ KnownTo co.1 T →
      i ∈ C.holders T → j ∈ C.holders T → (keys' i).2.1 T = (keys' j).2.1 T)
    (hc : ∀ i j, i ∉ co.1 → j ∈ co.1 →
      h (.sharedKeys phase ((sharedTerms i j).map (keys i).2.1)) =
        h (.sharedKeys phase ((sharedTerms i j).map (keys' i).2.1)))
    (hn : SetupEchoRegularHidden (phase := phase) co h keys) (hn' : SetupEchoRegularHidden (phase := phase) co h keys')
    (i : C.Party) (hi : i ∉ co.1) :
    echoCheck phase i (keys i) (D prims h (sharedQueries phase i (keys i)))
      (setupEchoInbox phase prims co active sent h keys i) ↔
    echoCheck phase i (keys' i) (D prims h (sharedQueries phase i (keys' i)))
      (setupEchoInbox phase prims co active sent h keys' i) := by
  unfold echoCheck
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hji
  by_cases hj : j ∈ co.1
  · simp only [setupEchoInbox, ite_eq_left hj]
    have he : echoOf phase (keys i) (D prims h (sharedQueries phase i (keys i))) j =
        echoOf phase (keys' i) (D prims h (sharedQueries phase i (keys' i))) j := by
      simp only [echoOf, D_sharedQueries_at, hp i hi, hc i j hi hj]
    rw [he]
  · simp only [setupEchoInbox, ite_eq_right hj]
    by_cases ha : active j
    · simp only [ite_eq_left ha, echoOutbox, ite_eq_right (Ne.symm hji), Msg.hashesOf]
      apply eq_comm.trans
      apply Iff.trans _ eq_comm
      exact setup_echo_eq_invariant_pair (phase := phase) prims co h i j
        (keys i) (keys j) (keys' i) (keys' j) (hp i hi) (hp j hj)
        (fun T hT => hk i T hi hT) (fun T hT => hk j T hj hT)
        (fun T hT => hh i j T hi hj hT) (fun T hT => hh' i j T hi hj hT)
        (fun hs => ⟨hn i j hi hj hs, hn' i j hi hj hs⟩)
    · simp [ha, Msg.hashesOf, echoOf]

/-- Two tables give the same receivers unless one of them makes an echo collision on a pair of
honest operators that share a hidden term. -/
theorem setupReferenceData_receivers_hidden (phase : Phase) (prims : Primitives) (co : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent echoSent : C.Party → Mail C E)
    (hl : SetupEchoRegularHidden (phase := phase) co h (setupReferenceKeys phase prims co h left parts (fun i j => revealSent j i)))
    (hr : SetupEchoRegularHidden (phase := phase) co h (setupReferenceKeys phase prims co h right parts (fun i j => revealSent j i)))
    (i : C.Party) :
    (setupEchoDataOutput phase co (setupReferenceData (phase := phase) prims co h left parts commitSent revealSent) echoSent i).isSome =
      (setupEchoDataOutput phase co (setupReferenceData (phase := phase) prims co h right parts commitSent revealSent) echoSent i).isSome := by
  let active := setupReferenceActive (phase := phase) co h commitSent revealSent
  let kl := setupReferenceKeys phase prims co h left parts (fun i j => revealSent j i)
  let kr := setupReferenceKeys phase prims co h right parts (fun i j => revealSent j i)
  have hsteps (table : KeyName C → HashOutput) :
      (fun j => setupEchoDataStep phase (E := E) j (setupReferenceData (phase := phase) prims co h table parts commitSent revealSent j)) =
        setupEchoStep phase prims co active h (setupReferenceKeys phase prims co h table parts (fun i j => revealSent j i)) :=
    funext fun j => setupReferenceData_echoStep (phase := phase) prims co h table parts commitSent revealSent j
  unfold setupEchoDataOutput
  rw [setupReferenceData_active, setupReferenceData_active]
  by_cases ha : active i
  · change setupReferenceActive (phase := phase) co h commitSent revealSent i at ha
    simp only [ite_eq_left ha]
    have hi := ha.1
    simp only [ite_eq_right hi, hsteps, roundInbox_setupEchoStep]
    have hab : (fun j => Msg.isAbort (setupEchoInbox phase prims co active echoSent h kl i j)) =
        (fun j => Msg.isAbort (setupEchoInbox phase prims co active echoSent h kr i j)) :=
      funext fun j => setupEchoInbox_isAbort phase prims co active echoSent h h kl kr i j
    have hc := setup_echoCheck_invariant_hidden (phase := phase) prims co active echoSent h kl kr
      (fun _ _ => rfl)
      (fun j T _ hT => setupReferenceKeys_known phase prims co h left right parts _ j T hT)
      (fun j k T _ _ hT hj hk => setupReferenceKeys_coherent phase prims co h left parts _ j k T hT hj hk)
      (fun j k T _ _ hT hj hk => setupReferenceKeys_coherent phase prims co h right parts _ j k T hT hj hk)
      (fun j c _ hc => setupReferenceKeys_shared_corrupt phase prims co h left right parts _ j c hc)
      hl hr i hi
    change (if C.parties.any (fun j => Msg.isAbort (setupEchoInbox phase prims co active echoSent h kl i j)) then none
      else if echoCheck phase i (kl i) (D prims h (sharedQueries phase i (kl i)))
        (setupEchoInbox phase prims co active echoSent h kl i) then some (keysOf (kl i)) else none).isSome = _
    rw [hab, hc]
    split_ifs <;> rfl
  · change ¬ setupReferenceActive (phase := phase) co h commitSent revealSent i at ha
    simp only [ite_eq_right ha, Option.isSome_none]

end Receivers

/-! ## Stage B: the independent dealer table against fresh keys

On the independent reference run, the dealer's table enters only the hidden coordinates of the
outputs and the honest echo comparisons. The stage hypothesis is the echo-collision bound, stated with
the unused portion of half the error after stage A on both distinguishers. -/

section StageB

variable {C : Committee} {E : Type} (prims : Primitives)

/-- Fresh term seeds and pair keys. -/
abbrev SeedGenFresh (C : Committee) := (C.Term → HashOutput) × (C.Pair → HashOutput)

/-- The transcript of the independent reference run, with two independent fresh tables. -/
def setupStageBSampler (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    ProbComp ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) ×
      (C.Party → Mail C E))) × SeedGenFresh C × SeedGenFresh C) := do
  let a ← $ᵗ (S → HashOutput)
  let π ← simulateQ (fixedLocal prims (seedGenFiniteTotal prims S a))
    (setupRefPrefix (phase := phase) prims D (seedGenFiniteTotal prims S a) A x z parts)
  let u ← $ᵗ (SeedGenFresh C)
  let v ← $ᵗ (SeedGenFresh C)
  pure (a, π, u, v)

/-- The distinguisher on the receivers of the table `u` and the keys of the table `v`. -/
def setupStageBRun (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (w : (S → HashOutput) × (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) ×
      (C.Party → Mail C E))) × SeedGenFresh C × SeedGenFresh C) (u v : SeedGenFresh C) : ProbComp Bool :=
  simulateQ (fixedLocal prims (seedGenFiniteTotal prims S w.1))
    (Z (w.2.1.1, setupRefMixedOutputs (phase := phase) prims D (seedGenFiniteTotal prims S w.1) (seedGenTableOf u.1 u.2)
      (seedGenTableOf v.1 v.2) parts w.2.1.2))

theorem evalDist_seedGenRestrict_bind {β : Type} (F : SeedGenFresh C → ProbComp β) :
    (($ᵗ (KeyName C → HashOutput)) >>= fun t => F (seedGenRestrict t)) =ᵈ (($ᵗ (SeedGenFresh C)) >>= F) := by
  have h := (evalDist_seedGenRestrict (C := C)).bind_left F
  rwa [bind_map_left] at h

theorem uniformSample_prod_bind {α β γ : Type} [SampleableType α] [SampleableType β]
    (f : α × β → ProbComp γ) :
    ($ᵗ (α × β)) >>= f = ($ᵗ α) >>= fun a => ($ᵗ β) >>= fun b => f (a, b) := by
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) >>= f = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

/-- The independent run with a table `t`, as the transcript and the outputs of `t`. -/
theorem evalDist_setupIndep_body (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (W : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) :
    (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
      simulateQ (fixedLocal prims (seedGenFiniteTotal prims S p.1))
        (setupReferenceLocalGame (phase := phase) prims D (seedGenFiniteTotal prims S p.1) p.2 A x z W parts)) =ᵈ
    (($ᵗ (S → HashOutput)) >>= fun a =>
      simulateQ (fixedLocal prims (seedGenFiniteTotal prims S a))
        (setupRefPrefix (phase := phase) prims D (seedGenFiniteTotal prims S a) A x z parts) >>= fun π =>
      ($ᵗ (SeedGenFresh C)) >>= fun u =>
      simulateQ (fixedLocal prims (seedGenFiniteTotal prims S a))
        (W (π.1, setupRefMixedOutputs (phase := phase) prims D (seedGenFiniteTotal prims S a) (seedGenTableOf u.1 u.2)
          (seedGenTableOf u.1 u.2) parts π.2))) := by
  rw [uniformSample_prod_bind]
  refine EvalDistEq.bind_right _ fun a => ?_
  simp only [setupReferenceLocalGame_eq_prefix, simulateQ_bind, setupRefOutputs_eq_mixed]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun π => ?_
  refine EvalDistEq.trans ?_ (evalDist_seedGenRestrict_bind _)
  refine EvalDistEq.bind_right _ fun t => ?_
  rw [setupRefMixedOutputs_restrict (phase := phase) prims D _ t t]

theorem evalDist_setupIndep_Z (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) :
    (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
      simulateQ (fixedLocal prims (seedGenFiniteTotal prims S p.1))
        (setupReferenceLocalGame (phase := phase) prims D (seedGenFiniteTotal prims S p.1) p.2 A x z Z parts)) =ᵈ
    (setupStageBSampler (phase := phase) prims D A x z S parts >>= fun w =>
      setupStageBRun (phase := phase) prims D A Z S parts w w.2.2.2 w.2.2.2) := by
  refine (evalDist_setupIndep_body (phase := phase) prims D A x z Z S parts).trans ?_
  unfold setupStageBSampler
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun π => ?_
  simp only [setupStageBRun]
  exact (evalDist_uniform_bind_const _).symm

theorem evalDist_setupIndep_hiddenZ (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) :
    (($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
      simulateQ (fixedLocal prims (seedGenFiniteTotal prims S p.1))
        (setupReferenceLocalGame (phase := phase) prims D (seedGenFiniteTotal prims S p.1) p.2 A x z (seedGenHiddenZ D Z) parts)) =ᵈ
    (setupStageBSampler (phase := phase) prims D A x z S parts >>= fun w =>
      setupStageBRun (phase := phase) prims D A Z S parts w w.2.2.1 w.2.2.2) := by
  refine (evalDist_setupIndep_body (phase := phase) prims D A x z (seedGenHiddenZ D Z) S parts).trans ?_
  unfold setupStageBSampler
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun π => EvalDistEq.bind_right _ fun u => ?_
  rw [seedGenHiddenZ_eq_gen]
  simp only [seedGenHiddenZGen, simulateQ_bind, simulateQ_fixedLocal_private]
  rw [uniformSample_prod_bind]
  refine EvalDistEq.bind_right _ fun s => EvalDistEq.bind_right _ fun p => ?_
  unfold setupStageBRun
  rw [setupRefMixedOutputs_overlay]

/-- The honest operators that accept under a table. -/
def setupRefReceivers (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : C.Party → Bool :=
  fun i => (setupRefOutputs (phase := phase) prims D h table parts m i).isSome

/-- The receivers of the two fresh tables differ. -/
def SetupReceiversGap (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (S : Finset (Query C))
    (r : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × SeedGenFresh C × SeedGenFresh C)) : Prop :=
  setupRefReceivers (phase := phase) prims D (seedGenFiniteTotal prims S r.2.1) (seedGenTableOf r.2.2.2.1.1 r.2.2.2.1.2) r.1 r.2.2.1.2 ≠
    setupRefReceivers (phase := phase) prims D (seedGenFiniteTotal prims S r.2.1) (seedGenTableOf r.2.2.2.2.1 r.2.2.2.2.2) r.1 r.2.2.1.2

theorem setupStageBRun_le (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (w : (S → HashOutput) × (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) ×
      (C.Party → Mail C E))) × SeedGenFresh C × SeedGenFresh C) (u u' v : SeedGenFresh C) :
    Pr{let z ← setupStageBRun (phase := phase) prims D A Z S parts w u v}[z = true] ≤ Pr{let z ← setupStageBRun (phase := phase) prims D A Z S parts w u' v}[z = true] +
      (if setupRefReceivers (phase := phase) prims D (seedGenFiniteTotal prims S w.1) (seedGenTableOf u.1 u.2) parts w.2.1.2 ≠
        setupRefReceivers (phase := phase) prims D (seedGenFiniteTotal prims S w.1) (seedGenTableOf u'.1 u'.2) parts w.2.1.2
        then 1 else 0) := by
  split_ifs with hg
  · exact le_trans (prEvent_le_one _) le_add_self
  · rw [add_zero]
    unfold setupStageBRun
    rw [setupRefMixedOutputs_receivers (phase := phase) prims D _ _ (seedGenTableOf u'.1 u'.2) _ parts _ (not_not.mp hg)]

/-- Stage B on one choice of parts: the gap is at most the probability that the receivers differ. -/
theorem setupStageB_parts (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) (left right : _ → SeedGenFresh C)
    (hg : ∀ w, setupRefReceivers (phase := phase) prims D (seedGenFiniteTotal prims S w.1) (seedGenTableOf (left w).1 (left w).2)
        parts w.2.1.2 ≠ setupRefReceivers (phase := phase) prims D (seedGenFiniteTotal prims S w.1)
          (seedGenTableOf (right w).1 (right w).2) parts w.2.1.2 → SetupReceiversGap (phase := phase) prims D A S (parts, w)) :
    Pr{let y ← setupStageBSampler (phase := phase) prims D A x z S parts >>= fun w =>
        setupStageBRun (phase := phase) prims D A Z S parts w (left w) w.2.2.2}[y = true] ≤
      Pr{let y ← setupStageBSampler (phase := phase) prims D A x z S parts >>= fun w =>
        setupStageBRun (phase := phase) prims D A Z S parts w (right w) w.2.2.2}[y = true] +
      Pr{let w ← setupStageBSampler (phase := phase) prims D A x z S parts}[SetupReceiversGap (phase := phase) prims D A S (parts, w)] := by
  refine (probOutput_bind_le_add_tsum _ _ _ _ fun w =>
    setupStageBRun_le (phase := phase) prims D A Z S parts w (left w) (right w) w.2.2.2).trans ?_
  gcongr
  rw [OracleComp.prEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun w => ?_
  split_ifs with h₁ h₂
  · simp
  · exact absurd (hg w h₁) h₂
  · simp
  · simp

/-- Stage A on one distinguisher costs the clashes and the guesses. -/
def seedGenStageAError (C : Committee) (q : ℕ) : ℝ := ((seedGenClashCount C + q * seedGenGuessNames C : ℕ) : ℝ) / 2 ^ 256

/-- The fresh table `u` makes an echo collision on a pair of honest operators that share a hidden
term, in a transcript that reaches the echo. -/
def SetupEchoIrregular (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (S : Finset (Query C))
    (r : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × SeedGenFresh C × SeedGenFresh C))
    (u : SeedGenFresh C) : Prop :=
  match r.2.2.1.2 with
  | none => False
  | some (_, rsent, _) => ¬ SetupEchoRegularHidden (phase := phase) D (seedGenFiniteTotal prims S r.2.1)
      (setupReferenceKeys phase prims D (seedGenFiniteTotal prims S r.2.1) (seedGenTableOf u.1 u.2) r.1
        (fun i j => rsent j i))

theorem setupReceiversGap_irregular (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (S : Finset (Query C))
    (r : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × SeedGenFresh C × SeedGenFresh C))
    (hg : SetupReceiversGap (phase := phase) prims D A S r) :
    SetupEchoIrregular (phase := phase) prims D A S r r.2.2.2.1 ∨ SetupEchoIrregular (phase := phase) prims D A S r r.2.2.2.2 := by
  rcases r with ⟨parts, a, ⟨st, m⟩, u, v⟩
  rcases m with _ | ⟨sent, rsent, esent⟩
  · exact absurd rfl hg
  · by_contra hn
    push Not at hn
    simp only [SetupEchoIrregular, not_not] at hn
    apply hg
    funext i
    exact setupReferenceData_receivers_hidden (phase := phase) prims D _ _ _ parts sent rsent esent hn.1 hn.2 i

theorem probEvent_setupEchoIrregular_swap (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) :
    Pr{let r ← seedGenPartsKernel (setupStageBSampler (phase := phase) prims D A x z S)}[SetupEchoIrregular (phase := phase) prims D A S r r.2.2.2.2] =
      Pr{let r ← seedGenPartsKernel (setupStageBSampler (phase := phase) prims D A x z S)}[
        SetupEchoIrregular (phase := phase) prims D A S r r.2.2.2.1] := by
  let sw : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × SeedGenFresh C × SeedGenFresh C) → _ :=
    fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.2, r.2.2.2.1)
  have he : (sw <$> seedGenPartsKernel (setupStageBSampler (phase := phase) prims D A x z S)) =ᵈ
      seedGenPartsKernel (setupStageBSampler (phase := phase) prims D A x z S) := by
    unfold seedGenPartsKernel setupStageBSampler
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun parts => EvalDistEq.bind_right _ fun a =>
      EvalDistEq.bind_right _ fun π => ?_
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  have hp : ∀ P : _ → Prop, Pr{let y ← sw <$> seedGenPartsKernel (setupStageBSampler (phase := phase) prims D A x z S)}[P y] =
      Pr{let y ← seedGenPartsKernel (setupStageBSampler (phase := phase) prims D A x z S)}[P y] := fun P =>
    he.prEvent_eq P
  rw [← hp, prEvent_map]
  rfl

end StageB

section Main

variable {C : Committee} {E : Type} (prims : Primitives)

end Main

/-- info: 'ThresholdLeanXmssSecurity.setupStageA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setupStageA

end ThresholdLeanXmssSecurity
