import ThresholdLeanXmssSecurity.Proof.KeygenSecurity
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# Keygen security: the two hybrid halves

This module works on the two open halves of `keygenSecurityProof`:
`KeygenHiddenFreshSwapped` (the hidden half on the relabeled reference runs) and
`KeygenKnownMismatch` (the known half on the simulator's emulation).

The hidden half is reduced to one echo-collision bound, `KeygenEchoFresh`.

1. Stage A (`keygenStageA`, proved). The relabeled oracle answers the canonical hidden inputs with
   the dealer's table. Replace it by the independent oracle. The two runs agree unless the parts
   clash (`KeygenClash`, at most `keygenClashCount / 2^256`) or a call of the adversary or the
   distinguisher hits a canonical hidden input (at most `q (|terms| + |pairs|) / 2^256`). Without a
   clash, no honest derivation of an exposed key reads a canonical hidden input.
2. Stage B (`keygenIndepEcho_of_acceptGap`, proved). On the independent run, the table enters only
   the hidden coordinates of the outputs and the receivers. The run splits into a table-free
   transcript and the outputs of the table. The fresh keys of `keygenHiddenZ` and the table are two
   independent fresh tables, so the gap is at most the probability that their receivers differ.
3. The receivers of two tables agree unless one of them makes an echo collision on two honest
   operators that share a hidden term (`keygenReferenceData_receivers_hidden`, proved).
4. Open: `KeygenEchoFresh`, the probability of such a collision on the independent run.

The known half `KeygenKnownMismatch` stays open.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Gaps of mixtures -/

section Mixture

/-- Two mixtures over one sampler whose branches are pointwise `e`-close are `E[e]`-close. -/
theorem probOutput_bind_le_add_tsum {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool) (e : α → ℝ≥0∞)
    (h : ∀ a, Pr[= true | f a] ≤ Pr[= true | g a] + e a) :
    Pr[= true | oa >>= f] ≤ Pr[= true | oa >>= g] + ∑' a, Pr[= a | oa] * e a := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_add]
  gcongr
  exact h a

theorem abs_probOutput_bind_sub_le {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool) (e : α → ℝ≥0∞)
    (hfg : ∀ a, Pr[= true | f a] ≤ Pr[= true | g a] + e a)
    (hgf : ∀ a, Pr[= true | g a] ≤ Pr[= true | f a] + e a)
    (hfin : ∑' a, Pr[= a | oa] * e a ≠ ⊤) :
    |(Pr[= true | oa >>= f]).toReal - (Pr[= true | oa >>= g]).toReal| ≤ (∑' a, Pr[= a | oa] * e a).toReal := by
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, hfin⟩)
    (probOutput_bind_le_add_tsum oa f g e hfg)
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, hfin⟩)
    (probOutput_bind_le_add_tsum oa g f e hgf)
  rw [ENNReal.toReal_add probOutput_ne_top hfin] at h₁ h₂
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
    RelTriple (simulateQ (fixedLocal prims h₂) (keygenHashLog oa)) (simulateQ (fixedLocal prims h₁) oa)
      (fun x y => (∃ v ∈ x.2, P v) ∨ x.1 = y) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [keygenHashLog_pure, simulateQ_pure]
    exact relTriple_pure_pure (Or.inr rfl)
  | query_bind t k ih =>
    rw [keygenHashLog_bind,
      show keygenHashLog (liftM (OracleSpec.query t) : OracleComp (LocalSpec C) _) = _ from keygenHashLog_query t]
    simp only [simulateQ_bind, bind_map_left, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, simulateQ_pure]
    have hcont : ∀ a, RelTriple (simulateQ (fixedLocal prims h₂) (keygenHashLog (k a)) >>= fun x =>
        (pure (x.1, keygenLocalHashInputs t ++ x.2) : ProbComp _)) (simulateQ (fixedLocal prims h₁) (k a))
        (fun x y => (∃ v ∈ x.2, P v) ∨ x.1 = y) := by
      intro a
      rw [← bind_pure (simulateQ (fixedLocal prims h₁) (k a))]
      refine relTriple_bind (ih a) fun x y hxy => relTriple_pure_pure ?_
      rcases hxy with ⟨v, hv, hp⟩ | he
      · exact Or.inl ⟨v, List.mem_append_right _ hv, hp⟩
      · exact Or.inr he
    by_cases hb : ∃ v ∈ keygenLocalHashInputs t, P v
    · refine relTriple_of_support_left fun z hz _ => Or.inl ?_
      obtain ⟨v, hv, hp⟩ := hb
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨a, -, x, -, rfl⟩ := hz
      exact ⟨v, List.mem_append_left _ hv, hp⟩
    · have he : fixedLocal prims h₂ t = fixedLocal prims h₁ t := by
        rcases t with n | q | x
        · rfl
        · have hq : h₁ q = h₂ q := hP q fun hq => hb ⟨q, by simp [keygenLocalHashInputs], hq⟩
          change (pure (h₂ q) : ProbComp _) = pure (h₁ q)
          rw [hq]
        · have hq : h₁ (.streamKey x.2.1) = h₂ (.streamKey x.2.1) :=
            hP _ fun hq => hb ⟨_, by simp [keygenLocalHashInputs], hq⟩
          change (pure (prims.aes.eval (truncateHash (h₂ (.streamKey x.2.1))) x.2.2) : ProbComp _) =
            pure (prims.aes.eval (truncateHash (h₁ (.streamKey x.2.1))) x.2.2)
          rw [hq]
      rw [he]
      exact relTriple_bind (relTriple_refl _) fun a b hab => by
        cases hab
        exact hcont a

theorem fst_simulateQ_keygenHashLog (h : Query C → HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    Prod.fst <$> simulateQ (fixedLocal prims h) (keygenHashLog oa) = simulateQ (fixedLocal prims h) oa := by
  rw [← simulateQ_map, keygenHashLog_fst]

/-- The acceptance gap of two fixed oracles that agree off `P` is at most the probability that the
logged run queries a point of `P`. -/
theorem abs_probOutput_fixedLocal_swap_le (h₁ h₂ : Query C → HashOutput) (P : Query C → Prop)
    (hP : ∀ v, ¬ P v → h₁ v = h₂ v) (oa : OracleComp (LocalSpec C) Bool) :
    |(Pr[= true | simulateQ (fixedLocal prims h₁) oa]).toReal -
        (Pr[= true | simulateQ (fixedLocal prims h₂) oa]).toReal| ≤
      (Pr[fun r => ∃ v ∈ r.2, P v | simulateQ (fixedLocal prims h₂) (keygenHashLog oa)]).toReal := by
  have h := abs_probEvent_sub_le_of_relTriple (fun r : Bool × List (Query C) => ∃ v ∈ r.2, P v)
    (fun r => r.1 = true) (fun b => b = true) (relTriple_post_mono
      (relTriple_fixedLocal_swap prims h₁ h₂ P hP oa) fun x y hxy => by
        rcases hxy with hb | he
        · exact Or.inl hb
        · exact Or.inr (by rw [he]))
  have hl : Pr[fun r : Bool × List (Query C) => r.1 = true |
      simulateQ (fixedLocal prims h₂) (keygenHashLog oa)] = Pr[= true | simulateQ (fixedLocal prims h₂) oa] := by
    rw [← fst_simulateQ_keygenHashLog prims h₂ oa, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  rw [hl, probEvent_eq_eq_probOutput] at h
  rwa [abs_sub_comm]

/-- The one-sided gaps of two fixed oracles that agree off `P`, in both directions. -/
theorem probOutput_fixedLocal_swap_le (h₁ h₂ : Query C → HashOutput) (P : Query C → Prop)
    (hP : ∀ v, ¬ P v → h₁ v = h₂ v) (oa : OracleComp (LocalSpec C) Bool) :
    Pr[= true | simulateQ (fixedLocal prims h₁) oa] ≤ Pr[= true | simulateQ (fixedLocal prims h₂) oa] +
        Pr[fun r => ∃ v ∈ r.2, P v | simulateQ (fixedLocal prims h₂) (keygenHashLog oa)] ∧
      Pr[= true | simulateQ (fixedLocal prims h₂) oa] ≤ Pr[= true | simulateQ (fixedLocal prims h₁) oa] +
        Pr[fun r => ∃ v ∈ r.2, P v | simulateQ (fixedLocal prims h₂) (keygenHashLog oa)] := by
  have hc := relTriple_fixedLocal_swap prims h₁ h₂ P hP oa
  have hl : Pr[fun r : Bool × List (Query C) => r.1 = true |
      simulateQ (fixedLocal prims h₂) (keygenHashLog oa)] = Pr[= true | simulateQ (fixedLocal prims h₂) oa] := by
    rw [← fst_simulateQ_keygenHashLog prims h₂ oa, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  constructor
  · rw [← probEvent_eq_eq_probOutput, ← hl]
    calc _ ≤ Pr[fun r : Bool × List (Query C) => r.1 = true ∨ ∃ v ∈ r.2, P v |
          simulateQ (fixedLocal prims h₂) (keygenHashLog oa)] :=
          probEvent_le_of_relTriple (relTriple_symm hc) fun b a hab hb => by
            rcases hab with hbad | he
            · exact Or.inr hbad
            · exact Or.inl (he.trans hb)
      _ ≤ _ := probEvent_or_le _ _ _
  · rw [← hl, ← probEvent_eq_eq_probOutput]
    calc _ ≤ Pr[fun r : Bool × List (Query C) => r.1 = true ∧ ¬ ∃ v ∈ r.2, P v |
          simulateQ (fixedLocal prims h₂) (keygenHashLog oa)] +
          Pr[fun r : Bool × List (Query C) => ∃ v ∈ r.2, P v |
            simulateQ (fixedLocal prims h₂) (keygenHashLog oa)] :=
          le_trans (probEvent_mono fun r _ hr => by
            by_cases hb : ∃ v ∈ r.2, P v
            · exact Or.inr hb
            · exact Or.inl ⟨hr, hb⟩) (probEvent_or_le _ _ _)
      _ ≤ _ := by
          gcongr
          exact probEvent_le_of_relTriple hc fun a b hab ha => (hab.resolve_left ha.2).symm.trans ha.1

end FixedSwap

/-! ## Clashes of private parts

A clash is an equality of two distinct uniform coordinates of the parts that the hidden half reads:
the term part of the first honest holder of `T` against the part of `T'` at the same holder position,
and the two pair parts of two distinct pairs. Without a clash, the canonical inputs are distinct and
no honest derivation of an exposed key reads a canonical hidden input. -/

section Clash

variable {C : Committee}

/-- The holders of `T`, in operator order. -/
def keygenHolderList (T : C.Term) : List C.Party := C.parties.filter (· ∈ C.holders T)

/-- The holder of `T'` at the position of the first honest holder of `T`. -/
def keygenAligned (D : C.Coalition) (T T' : C.Term) : C.Party :=
  (keygenHolderList T').getD ((keygenHolderList T).idxOf (keygenFirstHonest D (C.holders T))) (firstParty C)

/-- A clash of two distinct private coordinates. -/
def KeygenClash (D : C.Coalition) (parts : C.Party → Parts C) : Prop :=
  (∃ T T' : C.Term, T ≠ T' ∧
    (parts (keygenFirstHonest D (C.holders T))).term T = (parts (keygenAligned D T T')).term T') ∨
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

theorem keygenFirstHonest_mem_holderList (D : C.Coalition) (T : C.Term) :
    keygenFirstHonest D (C.holders T) ∈ keygenHolderList T :=
  List.mem_filter.mpr ⟨by simp [Committee.parties], by simpa using (keygenFirstHonest_holder D T).1⟩

/-- Equal term derivation inputs of two distinct terms clash, when the first honest holder of `T` reads
its own part. -/
theorem keygenClash_of_term_eq (D : C.Coalition) (parts : C.Party → Parts C) (view : C.Party → Parts C)
    (T T' : C.Term) (hne : T ≠ T')
    (hview : view (keygenFirstHonest D (C.holders T)) = parts (keygenFirstHonest D (C.holders T)))
    (h : (keygenHolderList T).map (fun j => (view j).term T) =
      (keygenHolderList T').map (fun j => (parts j).term T')) :
    KeygenClash D parts := by
  have he := list_map_eq_getD h (keygenFirstHonest_mem_holderList D T) (firstParty C)
  rw [hview] at he
  exact Or.inl ⟨T, T', hne, he⟩

/-- Equal pair derivation inputs of two distinct pairs clash, when one member reads its own part. -/
theorem keygenClash_of_pair_eq (D : C.Coalition) (parts : C.Party → Parts C) (view : C.Party → Parts C)
    (p p' : C.Pair) (hne : p ≠ p') (hview : view p.1.1 = parts p.1.1 ∨ view p.1.2 = parts p.1.2)
    (h : [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1] =
      [(parts p'.1.1).pair p'.1.2, (parts p'.1.2).pair p'.1.1]) :
    KeygenClash D parts := by
  simp only [List.cons.injEq, and_true] at h
  rcases hview with hv | hv
  · exact Or.inr ⟨p, p', hne, Or.inl (hv ▸ h.1)⟩
  · exact Or.inr ⟨p, p', hne, Or.inr (hv ▸ h.2)⟩

set_option linter.unusedSimpArgs false in
/-- Without a clash, the canonical inputs are distinct. -/
theorem keygenNamedInput_injective_of_clash (D : C.Coalition) (parts : C.Party → Parts C)
    (hc : ¬ KeygenClash D parts) :
    Function.Injective (keygenNamedInput parts) := by
  intro a b hab
  cases a with
  | parameter =>
    cases b <;> simp_all [keygenNamedInput, parameterInput, termInput, pairInput]
  | term T =>
    cases b with
    | parameter => simp_all [keygenNamedInput, parameterInput, termInput, pairInput]
    | term T' =>
      by_contra hne
      have hT : T ≠ T' := fun h => hne (h ▸ rfl)
      simp only [keygenNamedInput, termInput, Query.derive.injEq, true_and] at hab
      exact hc (keygenClash_of_term_eq D parts parts T T' hT rfl hab)
    | pair p => simp_all [keygenNamedInput, parameterInput, termInput, pairInput]
  | pair p =>
    cases b with
    | parameter => simp_all [keygenNamedInput, parameterInput, termInput, pairInput]
    | term T' => simp_all [keygenNamedInput, parameterInput, termInput, pairInput]
    | pair p' =>
      by_contra hne
      have hp : p ≠ p' := fun h => hne (h ▸ rfl)
      simp only [keygenNamedInput, pairInput, Query.derive.injEq, true_and] at hab
      exact hc (keygenClash_of_pair_eq D parts parts p p' hp (Or.inl rfl) hab)

theorem keygenHiddenInput_derive (D : C.Coalition) (parts : C.Party → Parts C) {v : Query C}
    (h : KeygenHiddenInput D parts v) :
    (∃ T, ¬ KnownTo D.1 T ∧ v = termInput .keygen parts T) ∨
      (∃ p : C.Pair, p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ v = pairInput .keygen parts p) := by
  obtain ⟨name, hn, rfl⟩ := h
  cases name with
  | parameter => exact hn.elim
  | term T => exact Or.inl ⟨T, hn, rfl⟩
  | pair p => exact Or.inr ⟨p, hn.1, hn.2, rfl⟩

theorem not_keygenHiddenInput_of_not_derive (D : C.Coalition) (parts : C.Party → Parts C) {v : Query C}
    (h : ∀ k l, v ≠ .derive .keygen k l) : ¬ KeygenHiddenInput D parts v := by
  intro hv
  rcases keygenHiddenInput_derive D parts hv with ⟨T, -, rfl⟩ | ⟨p, -, -, rfl⟩
  · exact h _ _ rfl
  · exact h _ _ rfl

theorem not_keygenHiddenInput_parameter (D : C.Coalition) (parts : C.Party → Parts C) (l : List HashOutput) :
    ¬ KeygenHiddenInput D parts (.derive .keygen .parameter l) := by
  intro hv
  rcases keygenHiddenInput_derive D parts hv with ⟨T, -, he⟩ | ⟨p, -, -, he⟩
  · simp [termInput] at he
  · simp [pairInput] at he

/-- Without a clash, the derivation input of an exposed term is never a canonical hidden input. -/
theorem not_keygenHiddenInput_knownTerm (D : C.Coalition) (parts : C.Party → Parts C)
    (hc : ¬ KeygenClash D parts) (view : C.Party → Parts C) (T : C.Term) (hT : KnownTo D.1 T)
    (hview : view (keygenFirstHonest D (C.holders T)) = parts (keygenFirstHonest D (C.holders T))) :
    ¬ KeygenHiddenInput D parts (.derive .keygen .term ((keygenHolderList T).map fun j => (view j).term T)) := by
  intro hv
  rcases keygenHiddenInput_derive D parts hv with ⟨T', hT', he⟩ | ⟨p, -, -, he⟩
  · have hne : T ≠ T' := fun h => hT' (h ▸ hT)
    simp only [termInput, Query.derive.injEq, true_and] at he
    exact hc (keygenClash_of_term_eq D parts view T T' hne hview he)
  · simp [pairInput] at he

/-- Without a clash, the derivation input of a pair with a corrupt member, read by its honest
member, is never a canonical hidden input. -/
theorem not_keygenHiddenInput_crossPair (D : C.Coalition) (parts : C.Party → Parts C)
    (hc : ¬ KeygenClash D parts) (view : C.Party → Parts C) (p : C.Pair)
    (hp : p.1.1 ∈ D.1 ∨ p.1.2 ∈ D.1) (hview : view p.1.1 = parts p.1.1 ∨ view p.1.2 = parts p.1.2) :
    ¬ KeygenHiddenInput D parts (.derive .keygen .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1]) := by
  intro hv
  rcases keygenHiddenInput_derive D parts hv with ⟨T', -, he⟩ | ⟨p', h1, h2, he⟩
  · simp [termInput] at he
  · have hne : p ≠ p' := by
      rintro rfl
      rcases hp with hp | hp
      · exact h1 hp
      · exact h2 hp
    simp only [pairInput, Query.derive.injEq, true_and] at he
    exact hc (keygenClash_of_pair_eq D parts view p p' hne hview he)

/-- The bound of a clash: one term coordinate pair for each ordered pair of terms, and two pair
coordinate pairs for each ordered pair of pairs. -/
def keygenClashCount (C : Committee) : ℕ := Fintype.card C.Term ^ 2 + 2 * Fintype.card C.Pair ^ 2

theorem probEvent_keygenClash_le (D : C.Coalition) :
    Pr[KeygenClash D | Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (keygenClashCount C : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hterm : ∀ T T' : C.Term, Pr[fun parts => T ≠ T' ∧
      (parts (keygenFirstHonest D (C.holders T))).term T = (parts (keygenAligned D T T')).term T' |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    intro T T'
    by_cases hTT : T = T'
    · simp [hTT]
    calc _ ≤ Pr[fun parts => (parts (keygenFirstHonest D (C.holders T))).term T =
          (parts (keygenAligned D T T')).term T' |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := probEvent_mono fun _ _ h => h.2
      _ = _ := probEvent_parts_collision _ _ (keygenFirstHonest D (C.holders T)) (some T) none
          (fun c parts => by simp [shiftAt, shiftParts]) (fun c parts => by
            by_cases hb : keygenAligned D T T' = keygenFirstHonest D (C.holders T) <;>
              simp [shiftAt, shiftParts, hb, hTT])
  have hpair : ∀ p p' : C.Pair, Pr[fun parts => p ≠ p' ∧ ((parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2 ∨
      (parts p.1.2).pair p.1.1 = (parts p'.1.2).pair p'.1.1) |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤ 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    intro p p'
    by_cases hpp : p = p'
    · simp [hpp]
    have hne : ¬ (p'.1.1 = p.1.1 ∧ p'.1.2 = p.1.2) := fun ⟨h1, h2⟩ =>
      hpp (Subtype.ext (Prod.ext h1.symm h2.symm))
    calc _ ≤ Pr[fun parts => (parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2 |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] +
          Pr[fun parts => (parts p.1.2).pair p.1.1 = (parts p'.1.2).pair p'.1.1 |
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] :=
          (probEvent_mono fun _ _ h => h.2).trans (probEvent_or_le _ _ _)
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
  calc _ ≤ Pr[fun parts => (∃ T ∈ (Finset.univ : Finset C.Term), ∃ T' ∈ (Finset.univ : Finset C.Term), T ≠ T' ∧
          (parts (keygenFirstHonest D (C.holders T))).term T = (parts (keygenAligned D T T')).term T') ∨
        (∃ p ∈ (Finset.univ : Finset C.Pair), ∃ p' ∈ (Finset.univ : Finset C.Pair), p ≠ p' ∧
          ((parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2 ∨
            (parts p.1.2).pair p.1.1 = (parts p'.1.2).pair p'.1.1)) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] :=
        probEvent_mono fun parts _ h => by
          simpa only [KeygenClash, Finset.mem_univ, true_and] using h
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ (∑ T : C.Term, ∑ T' : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        ∑ p : C.Pair, ∑ p' : C.Pair, 2 * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        gcongr
        · refine (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun T _ => ?_)
          exact (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun T' _ => hterm T T')
        · refine (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          exact (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun p' _ => hpair p p')
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, keygenClashCount]
        push_cast
        ring

end Clash

/-! ## Guessing a canonical hidden input, counted by the names -/

section Guess

variable {C : Committee} {E : Type}

/-- The names whose canonical inputs a guess must hit: every term and every pair. -/
def keygenGuessNames (C : Committee) : ℕ := Fintype.card C.Term + Fintype.card C.Pair

theorem probEvent_keygenHiddenInput_kernel_names (coalition : C.Coalition) (m : ℕ)
    (K : (C.Party → Parts C) → ProbComp (Fin m → Query C)) (hinv : KeygenPrivateInvariant coalition K) :
    Pr[fun p => ∃ i : Fin m, KeygenHiddenInput coalition p.1 (p.2 i) | keygenPartsKernel K] ≤
      ((m * keygenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun p => ∃ i ∈ (Finset.univ : Finset (Fin m)), KeygenHiddenInput coalition p.1 (p.2 i) |
        keygenPartsKernel K] := by simp
    _ ≤ ∑ i : Fin m, Pr[fun p => KeygenHiddenInput coalition p.1 (p.2 i) | keygenPartsKernel K] :=
      probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _i : Fin m, ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum fun i _ => probEvent_keygenHiddenInput_kernel_one coalition K hinv (fun r => r i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        keygenGuessNames]
      rw [← mul_assoc]

theorem probEvent_keygenHiddenInput_kernel_list_names {α : Type} (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant coalition K)
    (queries : α → List (Query C)) (m : ℕ)
    (hbound : ∀ parts r, r ∈ support (K parts) → (queries r).length ≤ m) :
    Pr[fun p => ∃ v ∈ queries p.2, KeygenHiddenInput coalition p.1 v | keygenPartsKernel K] ≤
      ((m * keygenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let targets (r : α) (i : Fin m) := (queries r).getD i.val (.streamKey 0)
  let K' (parts : C.Party → Parts C) := targets <$> K parts
  have hinv' : KeygenPrivateInvariant coalition K' := by
    constructor
    · intro a T hT c parts
      dsimp only [K']
      rw [hinv.1 a T hT c parts]
    · intro p ha hb c parts
      dsimp only [K']
      rw [hinv.2 p ha hb c parts]
  have he : keygenPartsKernel K' =
      (fun p : (C.Party → Parts C) × α => (p.1, targets p.2)) <$> keygenPartsKernel K := by
    simp only [keygenPartsKernel, K', map_bind, bind_map_left, map_pure]
  have hb := probEvent_keygenHiddenInput_kernel_names coalition m K' hinv'
  rw [he, probEvent_map] at hb
  apply le_trans (probEvent_mono (fun p hp hh => ?_)) hb
  rcases p with ⟨parts, r⟩
  have hr : r ∈ support (K parts) := by
    simp only [keygenPartsKernel, support_bind, Set.mem_iUnion, support_pure,
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
theorem probEvent_keygenReference_hidden_guess_names (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    Pr[fun p => ∃ v ∈ p.2.2, KeygenHiddenInput coalition p.1 v |
      keygenPartsKernel (keygenReferenceKernel prims coalition h table A x z Z)] ≤
      ((q * keygenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hb := probEvent_keygenHiddenInput_kernel_list_names coalition
    (keygenReferenceKernel prims coalition h table A x z Z)
    (keygenReferenceKernel_privateInvariant prims coalition h table A x z Z)
    (fun r => r.2.filter fun v => ¬ IsFixed v) q
    (keygenReferenceKernel_random_length_le prims coalition h table A x z Z q hq)
  apply le_trans (probEvent_mono (fun p _ hh => ?_)) hb
  obtain ⟨v, hv, name, hn, he⟩ := hh
  refine ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, name, hn, he⟩
  apply decide_eq_true
  rw [← he]
  exact keygenNamedInput_not_fixed p.1 name

end Guess

/-! ## The reference run reads no canonical hidden input -/

section OracleCongr

variable {C : Committee} {E : Type} (prims : Primitives)

theorem keygenReferenceKeys_oracle_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (hc : ¬ KeygenClash D parts) (hh : ∀ v, ¬ KeygenHiddenInput D parts v → h₁ v = h₂ v)
    (i : C.Party) (hi : i ∉ D.1) :
    keygenReferenceKeys prims D h₁ table parts revealed i = keygenReferenceKeys prims D h₂ table parts revealed i := by
  simp only [keygenReferenceKeys, keygenMaskKeys, D_deriveKeys, ite_true]
  have hview : ∀ k, k ∉ D.1 → keygenCorruptView D parts revealed i k = parts k := by
    intro k hk
    simp [keygenCorruptView, hk]
  refine Prod.ext (hh _ (not_keygenHiddenInput_parameter D parts _)) (Prod.ext ?_ ?_)
  · funext T
    dsimp only
    split_ifs with hT hiT
    · exact hh _ (not_keygenHiddenInput_knownTerm D parts hc _ T hT
        (hview _ (keygenFirstHonest_holder D T).2))
    · rfl
    · rfl
    · rfl
  · funext j
    dsimp only
    split_ifs with h1 h2
    · rfl
    · have hj : j ∈ D.1 := h2.resolve_left hi
      apply hh
      apply not_keygenHiddenInput_crossPair D parts hc
      · unfold Committee.pairOf
        split_ifs <;> simp [hj]
      · unfold Committee.pairOf
        split_ifs
        · exact Or.inl (hview i hi)
        · exact Or.inr (hview i hi)
    · rfl

theorem keygenReferenceData_oracle_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (hc : ¬ KeygenClash D parts) (hh : ∀ v, ¬ KeygenHiddenInput D parts v → h₁ v = h₂ v) :
    keygenReferenceData prims D h₁ table parts commitSent revealSent =
      keygenReferenceData prims D h₂ table parts commitSent revealSent := by
  have hcommit : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l) := fun ph a b l =>
    hh _ (not_keygenHiddenInput_of_not_derive D parts fun _ _ he => by cases he)
  have hshared : ∀ ph l, h₁ (.sharedKeys ph l) = h₂ (.sharedKeys ph l) := fun ph l =>
    hh _ (not_keygenHiddenInput_of_not_derive D parts fun _ _ he => by cases he)
  have hactive : ∀ i, keygenReferenceActive D h₁ commitSent revealSent i ↔
      keygenReferenceActive D h₂ commitSent revealSent i := by
    intro i
    simp only [keygenReferenceActive, keygenReferenceOpenCheck, hcommit]
  funext i
  rw [keygenReferenceData_active, keygenReferenceData_active]
  by_cases ha : keygenReferenceActive D h₁ commitSent revealSent i
  · rw [if_pos ha, if_pos ((hactive i).1 ha)]
    rw [keygenReferenceKeys_oracle_congr prims D h₁ h₂ table parts _ hc hh i ha.1]
    simp only [sharedQueries, D_mapM, D_hashQuery, hshared]
  · rw [if_neg ha, if_neg (fun h => ha ((hactive i).2 h))]

theorem keygenFixedCommitView_oracle_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (parts : C.Party → Parts C) (hh : ∀ v, ¬ KeygenHiddenInput D parts v → h₁ v = h₂ v) :
    keygenFixedCommitView (E := E) prims D h₁ parts = keygenFixedCommitView prims D h₂ parts := by
  have hcommit : ∀ ph a b l, h₁ (.commit ph a b l) = h₂ (.commit ph a b l) := fun ph a b l =>
    hh _ (not_keygenHiddenInput_of_not_derive D parts fun _ _ he => by cases he)
  funext c i
  simp only [keygenFixedCommitView, D_commitQueries, hcommit]

/-- Without a clash, the reference run reads its oracle only away from the canonical hidden inputs,
apart from the oracle calls of the adversary and the distinguisher. -/
theorem keygenReferenceLocalGame_oracle_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C)
    (hc : ¬ KeygenClash D parts) (hh : ∀ v, ¬ KeygenHiddenInput D parts v → h₁ v = h₂ v) :
    keygenReferenceLocalGame prims D h₁ table A x z Z parts =
      keygenReferenceLocalGame prims D h₂ table A x z Z parts := by
  simp only [keygenReferenceLocalGame, keygenReferencePostCommit,
    keygenFixedCommitView_oracle_congr prims D h₁ h₂ parts hh,
    keygenReferenceData_oracle_congr prims D h₁ h₂ table parts _ _ hc hh]

end OracleCongr

/-! ## Stage A: from the relabeled oracle to an independent dealer table

The relabeled reference run answers the canonical hidden inputs with the dealer's table. The
independent reference run answers them with the oracle's own cells, so the dealer's table is
independent of the oracle. The two runs agree unless the parts clash or a call of the adversary or
the distinguisher hits a canonical hidden input. -/

section StageA

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The reference mixture whose dealer table is independent of the oracle. -/
def keygenIndepMixture (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) :
    ProbComp Bool := do
  let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
  let h := keygenFiniteTotal prims S p.1
  simulateQ (fixedLocal prims h) (keygenReferenceLocalGame prims D h p.2 A x z Z parts)

/-- The hit probability of one reference run with the independent table. -/
def keygenIndepHit (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) (p : (S → HashOutput) × (KeyName C → HashOutput)) : ℝ≥0∞ :=
  Pr[fun r => ∃ v ∈ r.2, KeygenHiddenInput D parts v |
    simulateQ (fixedLocal prims (keygenFiniteTotal prims S p.1))
      (keygenHashLog (keygenReferenceLocalGame prims D (keygenFiniteTotal prims S p.1) p.2 A x z Z parts))]

theorem keygenStageA_parts (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, keygenNamedInput parts name ∈ S) (parts : C.Party → Parts C)
    (hc : ¬ KeygenClash D parts) (p : (S → HashOutput) × (KeyName C → HashOutput)) :
    let hs := keygenFiniteTotal prims S (keygenFiniteHiddenSwap D S parts (hmem parts) p).1
    let h₀ := keygenFiniteTotal prims S p.1
    Pr[= true | simulateQ (fixedLocal prims hs) (keygenReferenceLocalGame prims D hs p.2 A x z Z parts)] ≤
        Pr[= true | simulateQ (fixedLocal prims h₀) (keygenReferenceLocalGame prims D h₀ p.2 A x z Z parts)] +
          keygenIndepHit prims D A x z Z S parts p ∧
      Pr[= true | simulateQ (fixedLocal prims h₀) (keygenReferenceLocalGame prims D h₀ p.2 A x z Z parts)] ≤
        Pr[= true | simulateQ (fixedLocal prims hs) (keygenReferenceLocalGame prims D hs p.2 A x z Z parts)] +
          keygenIndepHit prims D A x z Z S parts p := by
  intro hs h₀
  have hh : ∀ v, ¬ KeygenHiddenInput D parts v → hs v = h₀ v := fun v hv =>
    keygenFiniteHiddenSwap_total_off prims D S parts (hmem parts) p v hv
  rw [keygenReferenceLocalGame_oracle_congr prims D hs h₀ p.2 A x z Z parts hc hh]
  exact probOutput_fixedLocal_swap_le prims hs h₀ (KeygenHiddenInput D parts) hh _

theorem probEvent_keygenPartsKernel_eq_tsum {α : Type} (K : (C.Party → Parts C) → ProbComp α)
    (P : (C.Party → Parts C) → α → Prop) :
    Pr[fun r => P r.1 r.2 | keygenPartsKernel K] =
      ∑' parts, Pr[= parts | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] *
        Pr[P parts | K parts] := by
  unfold keygenPartsKernel
  rw [probEvent_bind_eq_tsum]
  refine tsum_congr fun parts => ?_
  congr 1
  rw [bind_pure_comp, probEvent_map]
  rfl

theorem tsum_keygenIndepHit_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    ∑' parts, Pr[= parts | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] *
      ∑' p, Pr[= p | $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))] * keygenIndepHit prims D A x z Z S parts p ≤
      ((q * keygenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  calc _ = ∑' p, Pr[= p | $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))] *
        Pr[fun r => ∃ v ∈ r.2.2, KeygenHiddenInput D r.1 v | keygenPartsKernel
          (keygenReferenceKernel prims D (keygenFiniteTotal prims S p.1) p.2 A x z Z)] := by
        refine tsum_congr fun p => ?_
        rw [probEvent_keygenPartsKernel_eq_tsum (keygenReferenceKernel prims D (keygenFiniteTotal prims S p.1) p.2
          A x z Z) (fun parts r => ∃ v ∈ r.2, KeygenHiddenInput D parts v), ← ENNReal.tsum_mul_left]
        refine tsum_congr fun parts => ?_
        simp only [keygenIndepHit, keygenReferenceKernel]
        ring
    _ ≤ ∑' p, Pr[= p | $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))] *
        (((q * keygenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) :=
        ENNReal.tsum_le_tsum fun p => by
          gcongr
          exact probEvent_keygenReference_hidden_guess_names prims D _ _ A x z Z q hq
    _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := by
  unfold HashOutput hashOutputBits
  exact card_bitVec 256

theorem toReal_nat_mul_inv_card (k : ℕ) :
    ((k : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹).toReal = (k : ℝ) / 2 ^ 256 := by
  rw [card_hashOutput, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]

/-- Stage A. The relabeled reference mixture and the independent one are close. -/
theorem keygenStageA (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (hmem : ∀ parts name, keygenNamedInput parts name ∈ S) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    |(Pr[= true | keygenSwappedMixture prims D A x z Z S hmem]).toReal -
        (Pr[= true | keygenIndepMixture prims D A x z Z S]).toReal| ≤
      ((keygenClashCount C + q * keygenGuessNames C : ℕ) : ℝ) / 2 ^ 256 := by
  set e : (C.Party → Parts C) → ℝ≥0∞ := fun parts => (if KeygenClash D parts then 1 else 0) +
    ∑' p, Pr[= p | $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))] * keygenIndepHit prims D A x z Z S parts p
    with he
  have hsum : ∑' parts, Pr[= parts | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] * e parts ≤
      ((keygenClashCount C + q * keygenGuessNames C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    simp only [he, mul_add, ENNReal.tsum_add]
    rw [Nat.cast_add, add_mul]
    gcongr
    · calc _ = Pr[KeygenClash D | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] := by
            rw [probEvent_eq_tsum_ite]
            refine tsum_congr fun parts => ?_
            split_ifs <;> simp
        _ ≤ _ := probEvent_keygenClash_le D
    · exact tsum_keygenIndepHit_le prims D A x z Z S q hq
  have hfin : ∑' parts, Pr[= parts | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] * e parts ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)) hsum
  have hbranch : ∀ parts, ¬ KeygenClash D parts →
      (∀ p : (S → HashOutput) × (KeyName C → HashOutput),
        let hs := keygenFiniteTotal prims S (keygenFiniteHiddenSwap D S parts (hmem parts) p).1
        let h₀ := keygenFiniteTotal prims S p.1
        Pr[= true | simulateQ (fixedLocal prims hs) (keygenReferenceLocalGame prims D hs p.2 A x z Z parts)] ≤
            Pr[= true | simulateQ (fixedLocal prims h₀) (keygenReferenceLocalGame prims D h₀ p.2 A x z Z parts)] +
              keygenIndepHit prims D A x z Z S parts p ∧
          Pr[= true | simulateQ (fixedLocal prims h₀) (keygenReferenceLocalGame prims D h₀ p.2 A x z Z parts)] ≤
            Pr[= true | simulateQ (fixedLocal prims hs) (keygenReferenceLocalGame prims D hs p.2 A x z Z parts)] +
              keygenIndepHit prims D A x z Z S parts p) :=
    fun parts hc p => keygenStageA_parts prims D A x z Z S hmem parts hc p
  have h := abs_probOutput_bind_sub_le (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
    (fun parts => do
      let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
      let ht := if Function.Injective (keygenNamedInput parts) then
        (keygenFiniteHiddenSwap D S parts (hmem parts) p).1 else p.1
      let h := keygenFiniteTotal prims S ht
      let table := if Function.Injective (keygenNamedInput parts) then p.2 else
        fun name => h (keygenNamedInput parts name)
      simulateQ (fixedLocal prims h) (keygenReferenceLocalGame prims D h table A x z Z parts))
    (fun parts => do
      let p ← $ᵗ ((S → HashOutput) × (KeyName C → HashOutput))
      let h := keygenFiniteTotal prims S p.1
      simulateQ (fixedLocal prims h) (keygenReferenceLocalGame prims D h p.2 A x z Z parts)) e
    (fun parts => by
      by_cases hc : KeygenClash D parts
      · exact le_trans probOutput_le_one (le_add_left (by simp [he, hc]))
      · have hinj := keygenNamedInput_injective_of_clash D parts hc
        simp only [if_pos hinj]
        refine (probOutput_bind_le_add_tsum _ _ _ _ fun p => (hbranch parts hc p).1).trans ?_
        gcongr
        simp [he, hc])
    (fun parts => by
      by_cases hc : KeygenClash D parts
      · exact le_trans probOutput_le_one (le_add_left (by simp [he, hc]))
      · have hinj := keygenNamedInput_injective_of_clash D parts hc
        simp only [if_pos hinj]
        refine (probOutput_bind_le_add_tsum _ _ _ _ fun p => (hbranch parts hc p).2).trans ?_
        gcongr
        simp [he, hc])
    hfin
  refine h.trans ?_
  rw [← toReal_nat_mul_inv_card]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)) hsum

theorem isQueryBoundP_liftComp_counted {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) Counted 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [Counted]), fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

theorem isQueryBoundP_liftComp_bind {α β : Type} (oa : ProbComp α) (k : α → OracleComp (LocalSpec C) β)
    (n : ℕ) (hk : ∀ a, IsQueryBoundP (k a) Counted n) :
    IsQueryBoundP (liftComp oa (LocalSpec C) >>= k) Counted n := by
  have h := isQueryBoundP_bind (isQueryBoundP_liftComp_counted oa) (fun a _ => hk a)
  rwa [Nat.zero_add] at h

/-- `keygenHiddenZ` with its two samplers as parameters. A statement that shows the uniform sampler of
`C.Term → HashOutput` inside a query bound makes the elaborator time out, so the bound is proved for
any sampler. -/
def keygenHiddenZGen (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C))
    (s₁ : ProbComp (C.Term → HashOutput)) (s₂ : ProbComp (C.Pair → HashOutput)) : Distinguisher C σ (Keys C) :=
  fun r => do
    let seeds ← liftComp s₁ (LocalSpec C)
    let pairs ← liftComp s₂ (LocalSpec C)
    Z (r.1, fun i => (r.2 i).map fun k => keygenHiddenOverlay D i k (dealtKeys 0 seeds pairs i))

theorem keygenHiddenZ_eq_gen (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C)) :
    keygenHiddenZ D Z = keygenHiddenZGen D Z ($ᵗ _) ($ᵗ _) := rfl

/-- Fresh hidden keys cost the distinguisher no counted call. -/
theorem isQueryBounded_keygenHiddenZ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    IsQueryBounded A (keygenHiddenZ D Z) setupRounds q := by
  rw [keygenHiddenZ_eq_gen]
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
def keygenRefVisible (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (sent rsent : C.Party → Mail C E) : C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    (keygenEchoDataStep i (keygenReferenceData prims D h (fun _ => 0) parts sent rsent i)).outbox c else none

/-- The reference run up to the last adversary round. It records the final adversary state and, when
an honest operator reaches the echo, the three corrupt mails. -/
def keygenRefPrefix (D : C.Coalition) (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) := do
  let state ← A.start (corruptInputs D x) z
  let r ← A.round state (keygenFixedCommitView prims D h parts)
  if ∀ i, i ∉ D.1 → keygenCommitAborted D r.2 i = true then pure (r.1, none) else do
    let r' ← A.round r.1 (keygenReferenceRevealView D parts r.2)
    if ∀ i, i ∉ D.1 → ¬ keygenReferenceActive D h r.2 r'.2 i then pure (r'.1, none) else do
      let r'' ← A.round r'.1 (keygenRefVisible prims D h parts r.2 r'.2)
      pure (r''.1, some (r.2, r'.2, r''.2))

/-- The honest outputs of a transcript under a table. -/
def keygenRefOutputs (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : C.Party → Option (Keys C) :=
  match m with
  | none => fun _ => none
  | some (sent, rsent, esent) => keygenEchoDataOutput D (keygenReferenceData prims D h table parts sent rsent) esent

theorem keygenReferenceLocalGame_eq_prefix (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    keygenReferenceLocalGame prims D h table A x z Z parts =
      keygenRefPrefix prims D h A x z parts >>= fun π => Z (π.1, keygenRefOutputs prims D h table parts π.2) := by
  unfold keygenReferenceLocalGame keygenRefPrefix
  simp only [bind_assoc]
  refine bind_congr fun state => bind_congr fun r => ?_
  unfold keygenReferencePostCommit
  split_ifs with ha
  · simp [keygenRefOutputs]
  · simp only [bind_assoc]
    refine bind_congr fun r' => ?_
    unfold keygenFinishLocal
    have hnone : (∀ i, i ∉ D.1 → keygenReferenceData prims D h table parts r.2 r'.2 i = none) ↔
        ∀ i, i ∉ D.1 → ¬ keygenReferenceActive D h r.2 r'.2 i := by
      refine forall_congr' fun i => forall_congr' fun _ => ?_
      rw [keygenReferenceData_active]
      split_ifs <;> simp_all
    have hvis : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
        (keygenEchoDataStep (E := E) i (keygenReferenceData prims D h table parts r.2 r'.2 i)).outbox c
        else none) = keygenRefVisible prims D h parts r.2 r'.2 := by
      funext c i
      unfold keygenRefVisible
      split_ifs with hc
      · exact keygenReferenceData_visible prims D h table (fun _ => 0) parts r.2 r'.2 i c hc.1
      · rfl
    simp only [hnone]
    split_ifs with hb
    · simp [keygenRefOutputs]
    · rw [hvis]
      simp [keygenRefOutputs]

/-- The keys that an honest operator outputs under a table, if it accepts. -/
def keygenRefKeysOf (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (i : C.Party) : Keys C :=
  match m with
  | none => default
  | some (_, rsent, _) => keysOf (keygenReferenceKeys prims D h table parts (fun i j => rsent j i) i)

/-- The receivers of one table with the keys of another. -/
def keygenRefMixedOutputs (D : C.Coalition) (h : Query C → HashOutput) (table keys : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : C.Party → Option (Keys C) :=
  fun i => if (keygenRefOutputs prims D h table parts m i).isSome then
    some (keygenRefKeysOf prims D h keys parts m i) else none

theorem keygenRefOutputs_eq_mixed (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :
    keygenRefOutputs prims D h table parts m = keygenRefMixedOutputs prims D h table table parts m := by
  funext i
  unfold keygenRefMixedOutputs
  rcases m with _ | ⟨sent, rsent, esent⟩
  · rfl
  · simp only [keygenRefOutputs, keygenRefKeysOf, keygenEchoDataOutput]
    rw [keygenReferenceData_active]
    split_ifs <;> simp_all

theorem keygenRefOutputs_honest (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) (i : C.Party)
    (hs : (keygenRefOutputs prims D h table parts m i).isSome) : i ∉ D.1 := by
  rcases m with _ | ⟨sent, rsent, esent⟩
  · simp [keygenRefOutputs] at hs
  · intro hi
    simp only [keygenRefOutputs, keygenEchoDataOutput] at hs
    split at hs
    · simp at hs
    · simp [hi] at hs

/-- The table of fresh term seeds and pair keys. -/
def keygenTableOf (s : C.Term → HashOutput) (p : C.Pair → HashOutput) : KeyName C → HashOutput
  | .parameter => 0
  | .term T => s T
  | .pair q => p q

/-- `keygenHiddenZ` turns the outputs of one table into the keys of the fresh table. -/
theorem keygenRefMixedOutputs_overlay (D : C.Coalition) (h : Query C → HashOutput)
    (table keys : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (s : C.Term → HashOutput) (p : C.Pair → HashOutput) :
    (fun i => (keygenRefMixedOutputs prims D h table keys parts m i).map fun k =>
      keygenHiddenOverlay D i k (dealtKeys 0 s p i)) =
      keygenRefMixedOutputs prims D h table (keygenTableOf s p) parts m := by
  funext i
  unfold keygenRefMixedOutputs
  split_ifs with hs
  · have hi := keygenRefOutputs_honest prims D h table parts m i hs
    rcases m with _ | ⟨sent, rsent, esent⟩
    · simp [keygenRefOutputs] at hs
    · simp only [Option.map_some, keygenRefKeysOf, keygenReferenceKeys, keygenMaskKeys, keysOf,
        keygenHiddenOverlay, dealtKeys, Option.some.injEq]
      congr 1
      · funext T
        split_ifs <;> simp_all [keygenTableOf]
      · funext j
        split_ifs <;> simp_all [keygenTableOf]
  · rfl

/-- The term and pair coordinates of a table. -/
def keygenRestrict (τ : KeyName C → HashOutput) : (C.Term → HashOutput) × (C.Pair → HashOutput) :=
  (fun T => τ (.term T), fun q => τ (.pair q))

theorem keygenReferenceKeys_restrict (D : C.Coalition) (h : Query C → HashOutput) (τ : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) :
    keygenReferenceKeys prims D h τ parts revealed =
      keygenReferenceKeys prims D h (keygenTableOf (keygenRestrict τ).1 (keygenRestrict τ).2) parts revealed := by
  funext i
  simp only [keygenReferenceKeys, keygenMaskKeys, keygenTableOf, keygenRestrict]

theorem keygenRefMixedOutputs_restrict (D : C.Coalition) (h : Query C → HashOutput)
    (table keys : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) :
    keygenRefMixedOutputs prims D h table keys parts m =
      keygenRefMixedOutputs prims D h (keygenTableOf (keygenRestrict table).1 (keygenRestrict table).2)
        (keygenTableOf (keygenRestrict keys).1 (keygenRestrict keys).2) parts m := by
  have hd : ∀ sent rsent : C.Party → Mail C E, keygenReferenceData prims D h table parts sent rsent =
      keygenReferenceData prims D h (keygenTableOf (keygenRestrict table).1 (keygenRestrict table).2)
        parts sent rsent := by
    intro sent rsent
    unfold keygenReferenceData
    rw [keygenReferenceKeys_restrict prims D h table]
  funext i
  rcases m with _ | ⟨sent, rsent, esent⟩
  · rfl
  · simp only [keygenRefMixedOutputs, keygenRefOutputs, keygenRefKeysOf, hd]
    rw [keygenReferenceKeys_restrict prims D h keys]

/-- The receivers decide the mixed outputs. -/
theorem keygenRefMixedOutputs_receivers (D : C.Coalition) (h : Query C → HashOutput)
    (table table' keys : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E)))
    (hr : (fun i => (keygenRefOutputs prims D h table parts m i).isSome) =
      fun i => (keygenRefOutputs prims D h table' parts m i).isSome) :
    keygenRefMixedOutputs prims D h table keys parts m = keygenRefMixedOutputs prims D h table' keys parts m := by
  funext i
  simp only [keygenRefMixedOutputs, congrFun hr i]

theorem evalDist_keygenRestrict :
    𝒟[keygenRestrict <$> ($ᵗ (KeyName C → HashOutput))] =
      𝒟[$ᵗ ((C.Term → HashOutput) × (C.Pair → HashOutput))] := by
  let e : C.Term ⊕ C.Pair → KeyName C := Sum.elim KeyName.term KeyName.pair
  have he : Function.Injective e := by
    rintro (a | a) (b | b) hab <;> simp_all [e]
  have h₁ := evalDist_uniformSample_map_comp_injective (R := HashOutput) he
  let φ := Equiv.sumArrowEquivProdArrow C.Term C.Pair HashOutput
  have hφ : keygenRestrict = φ ∘ fun g : KeyName C → HashOutput => g ∘ e := by
    funext g
    rfl
  calc 𝒟[keygenRestrict <$> ($ᵗ (KeyName C → HashOutput))]
      = 𝒟[φ <$> (do let g ← $ᵗ (KeyName C → HashOutput); pure (g ∘ e))] := by
        rw [hφ, map_bind]
        simp only [map_pure, bind_pure_comp]
        rfl
    _ = φ <$> 𝒟[do let g ← $ᵗ (KeyName C → HashOutput); pure (g ∘ e)] := evalDist_map _ _
    _ = φ <$> 𝒟[$ᵗ (C.Term ⊕ C.Pair → HashOutput)] := by rw [h₁]
    _ = 𝒟[φ <$> ($ᵗ (C.Term ⊕ C.Pair → HashOutput))] := (evalDist_map _ _).symm
    _ = _ := evalDist_ext fun y => probOutput_map_bijective_uniform_cross (α := C.Term ⊕ C.Pair → HashOutput)
        φ φ.bijective y

end Transcript

/-! ## Receivers under two tables, up to echo collisions of pairs that share a hidden term -/

section Receivers

variable {C : Committee} {E : Type} (prims : Primitives)

/-- Two operators share a term that no corrupt operator holds. -/
def KeygenShareHidden (D : C.Coalition) (i j : C.Party) : Prop :=
  ∃ T, ¬ KnownTo D.1 T ∧ i ∈ C.holders T ∧ j ∈ C.holders T

theorem keygen_echo_eq_invariant_pair (co : C.Coalition) (h : Query C → HashOutput) (i j : C.Party)
    (ki kj ki' kj' : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hpi : ki.1 = ki'.1) (hpj : kj.1 = kj'.1)
    (hki : ∀ T, KnownTo co.1 T → ki.2.1 T = ki'.2.1 T)
    (hkj : ∀ T, KnownTo co.1 T → kj.2.1 T = kj'.2.1 T)
    (hhidden : ∀ T, ¬ KnownTo co.1 T → i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T)
    (hhidden' : ∀ T, ¬ KnownTo co.1 T → i ∈ C.holders T → j ∈ C.holders T → ki'.2.1 T = kj'.2.1 T)
    (hreg : KeygenShareHidden co i j →
      (h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) ∧
      (h (.sharedKeys .keygen ((sharedTerms i j).map ki'.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj'.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki'.2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map kj'.2.1))) :
    (echoOf .keygen ki (D prims h (sharedQueries .keygen i ki)) j =
      echoOf .keygen kj (D prims h (sharedQueries .keygen j kj)) i) ↔
    (echoOf .keygen ki' (D prims h (sharedQueries .keygen i ki')) j =
      echoOf .keygen kj' (D prims h (sharedQueries .keygen j kj')) i) := by
  by_cases hs : KeygenShareHidden co i j
  · exact keygen_echo_eq_hidden_invariant prims co h h i j ki kj ki' kj' hpi hpj hki hkj hhidden hhidden'
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
    simp only [echoOf, ite_true, D_sharedQueries_at, hli, hlj, hpi, hpj]

/-- No echo collision on a pair of honest operators that share a hidden term. -/
def KeygenEchoRegularHidden (co : C.Coalition) (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : Prop :=
  ∀ i j, i ∉ co.1 → j ∉ co.1 → KeygenShareHidden co i j →
    h (.sharedKeys .keygen ((sharedTerms i j).map (keys i).2.1)) =
      h (.sharedKeys .keygen ((sharedTerms j i).map (keys j).2.1)) →
    Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map (keys i).2.1) =
      Query.sharedKeys .keygen ((sharedTerms j i).map (keys j).2.1)

theorem keygen_echoCheck_invariant_hidden (co : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys keys' : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hp : ∀ i, i ∉ co.1 → (keys i).1 = (keys' i).1)
    (hk : ∀ i T, i ∉ co.1 → KnownTo co.1 T → (keys i).2.1 T = (keys' i).2.1 T)
    (hh : ∀ i j T, i ∉ co.1 → j ∉ co.1 → ¬ KnownTo co.1 T →
      i ∈ C.holders T → j ∈ C.holders T → (keys i).2.1 T = (keys j).2.1 T)
    (hh' : ∀ i j T, i ∉ co.1 → j ∉ co.1 → ¬ KnownTo co.1 T →
      i ∈ C.holders T → j ∈ C.holders T → (keys' i).2.1 T = (keys' j).2.1 T)
    (hc : ∀ i j, i ∉ co.1 → j ∈ co.1 →
      h (.sharedKeys .keygen ((sharedTerms i j).map (keys i).2.1)) =
        h (.sharedKeys .keygen ((sharedTerms i j).map (keys' i).2.1)))
    (hn : KeygenEchoRegularHidden co h keys) (hn' : KeygenEchoRegularHidden co h keys')
    (i : C.Party) (hi : i ∉ co.1) :
    echoCheck .keygen i (keys i) (D prims h (sharedQueries .keygen i (keys i)))
      (keygenEchoInbox prims co active sent h keys i) ↔
    echoCheck .keygen i (keys' i) (D prims h (sharedQueries .keygen i (keys' i)))
      (keygenEchoInbox prims co active sent h keys' i) := by
  unfold echoCheck
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hji
  by_cases hj : j ∈ co.1
  · simp only [keygenEchoInbox, if_pos hj]
    have he : echoOf .keygen (keys i) (D prims h (sharedQueries .keygen i (keys i))) j =
        echoOf .keygen (keys' i) (D prims h (sharedQueries .keygen i (keys' i))) j := by
      simp only [echoOf, ite_true, List.singleton_append, List.cons.injEq, and_true,
        D_sharedQueries_at]
      exact ⟨hp i hi, hc i j hi hj⟩
    rw [he]
  · simp only [keygenEchoInbox, if_neg hj]
    by_cases ha : active j
    · simp only [if_pos ha, echoOutbox, if_neg (Ne.symm hji), Msg.hashesOf]
      apply eq_comm.trans
      apply Iff.trans _ eq_comm
      exact keygen_echo_eq_invariant_pair prims co h i j
        (keys i) (keys j) (keys' i) (keys' j) (hp i hi) (hp j hj)
        (fun T hT => hk i T hi hT) (fun T hT => hk j T hj hT)
        (fun T hT => hh i j T hi hj hT) (fun T hT => hh' i j T hi hj hT)
        (fun hs => ⟨hn i j hi hj hs, hn' i j hi hj hs⟩)
    · simp [ha, Msg.hashesOf, echoOf]

/-- Two tables give the same receivers unless one of them makes an echo collision on a pair of
honest operators that share a hidden term. -/
theorem keygenReferenceData_receivers_hidden (co : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent echoSent : C.Party → Mail C E)
    (hl : KeygenEchoRegularHidden co h (keygenReferenceKeys prims co h left parts (fun i j => revealSent j i)))
    (hr : KeygenEchoRegularHidden co h (keygenReferenceKeys prims co h right parts (fun i j => revealSent j i)))
    (i : C.Party) :
    (keygenEchoDataOutput co (keygenReferenceData prims co h left parts commitSent revealSent) echoSent i).isSome =
      (keygenEchoDataOutput co (keygenReferenceData prims co h right parts commitSent revealSent) echoSent i).isSome := by
  let active := keygenReferenceActive co h commitSent revealSent
  let kl := keygenReferenceKeys prims co h left parts (fun i j => revealSent j i)
  let kr := keygenReferenceKeys prims co h right parts (fun i j => revealSent j i)
  have hsteps (table : KeyName C → HashOutput) :
      (fun j => keygenEchoDataStep (E := E) j (keygenReferenceData prims co h table parts commitSent revealSent j)) =
        keygenEchoStep prims co active h (keygenReferenceKeys prims co h table parts (fun i j => revealSent j i)) :=
    funext fun j => keygenReferenceData_echoStep prims co h table parts commitSent revealSent j
  unfold keygenEchoDataOutput
  rw [keygenReferenceData_active, keygenReferenceData_active]
  by_cases ha : active i
  · change keygenReferenceActive co h commitSent revealSent i at ha
    simp only [if_pos ha]
    have hi := ha.1
    simp only [if_neg hi, hsteps, roundInbox_keygenEchoStep]
    have hab : (fun j => Msg.isAbort (keygenEchoInbox prims co active echoSent h kl i j)) =
        (fun j => Msg.isAbort (keygenEchoInbox prims co active echoSent h kr i j)) :=
      funext fun j => keygenEchoInbox_isAbort prims co active echoSent h h kl kr i j
    have hc := keygen_echoCheck_invariant_hidden prims co active echoSent h kl kr
      (fun _ _ => rfl)
      (fun j T _ hT => keygenReferenceKeys_known prims co h left right parts _ j T hT)
      (fun j k T _ _ hT hj hk => keygenReferenceKeys_coherent prims co h left parts _ j k T hT hj hk)
      (fun j k T _ _ hT hj hk => keygenReferenceKeys_coherent prims co h right parts _ j k T hT hj hk)
      (fun j c _ hc => keygenReferenceKeys_shared_corrupt prims co h left right parts _ j c hc)
      hl hr i hi
    change (if C.parties.any (fun j => Msg.isAbort (keygenEchoInbox prims co active echoSent h kl i j)) then none
      else if echoCheck .keygen i (kl i) (D prims h (sharedQueries .keygen i (kl i)))
        (keygenEchoInbox prims co active echoSent h kl i) then some (keysOf (kl i)) else none).isSome = _
    rw [hab, hc]
    split_ifs <;> rfl
  · change ¬ keygenReferenceActive co h commitSent revealSent i at ha
    simp only [if_neg ha, Option.isSome_none]

end Receivers

/-! ## Stage B: the independent dealer table against fresh keys

On the independent reference run, the dealer's table enters only the hidden coordinates of the
outputs and the honest echo comparisons. The open stage is the echo-collision bound, stated with what
remains of half the error after stage A on both distinguishers. -/

section StageB

variable {C : Committee} {E : Type} (prims : Primitives)

/-- Fresh term seeds and pair keys. -/
abbrev KeygenFresh (C : Committee) := (C.Term → HashOutput) × (C.Pair → HashOutput)

/-- The transcript of the independent reference run, with two independent fresh tables. -/
def keygenStageBSampler (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) (parts : C.Party → Parts C) :
    ProbComp ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) ×
      (C.Party → Mail C E))) × KeygenFresh C × KeygenFresh C) := do
  let a ← $ᵗ (S → HashOutput)
  let π ← simulateQ (fixedLocal prims (keygenFiniteTotal prims S a))
    (keygenRefPrefix prims D (keygenFiniteTotal prims S a) A x z parts)
  let u ← $ᵗ (KeygenFresh C)
  let v ← $ᵗ (KeygenFresh C)
  pure (a, π, u, v)

/-- The distinguisher on the receivers of the table `u` and the keys of the table `v`. -/
def keygenStageBRun (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (w : (S → HashOutput) × (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) ×
      (C.Party → Mail C E))) × KeygenFresh C × KeygenFresh C) (u v : KeygenFresh C) : ProbComp Bool :=
  simulateQ (fixedLocal prims (keygenFiniteTotal prims S w.1))
    (Z (w.2.1.1, keygenRefMixedOutputs prims D (keygenFiniteTotal prims S w.1) (keygenTableOf u.1 u.2)
      (keygenTableOf v.1 v.2) parts w.2.1.2))

theorem evalDist_uniform_bind_const {α β : Type} [SampleableType α] (m : ProbComp β) :
    𝒟[($ᵗ α) >>= fun _ => m] = 𝒟[m] :=
  evalDist_ext fun y => by simp [probOutput_bind_const]

theorem evalDist_keygenRestrict_bind {β : Type} (F : KeygenFresh C → ProbComp β) :
    𝒟[($ᵗ (KeyName C → HashOutput)) >>= fun t => F (keygenRestrict t)] = 𝒟[($ᵗ (KeygenFresh C)) >>= F] := by
  rw [← bind_map_left, evalDist_bind, evalDist_keygenRestrict, ← evalDist_bind]

theorem keygenTableOf_restrict (u : KeygenFresh C) : keygenRestrict (keygenTableOf u.1 u.2) = u := rfl

theorem uniformSample_prod_bind {α β γ : Type} [SampleableType α] [SampleableType β]
    (f : α × β → ProbComp γ) :
    ($ᵗ (α × β)) >>= f = ($ᵗ α) >>= fun a => ($ᵗ β) >>= fun b => f (a, b) := by
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) >>= f = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

/-- The independent run with a table `t`, as the transcript and the outputs of `t`. -/
theorem evalDist_keygenIndep_body (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (W : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) :
    𝒟[($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
      simulateQ (fixedLocal prims (keygenFiniteTotal prims S p.1))
        (keygenReferenceLocalGame prims D (keygenFiniteTotal prims S p.1) p.2 A x z W parts)] =
    𝒟[($ᵗ (S → HashOutput)) >>= fun a =>
      simulateQ (fixedLocal prims (keygenFiniteTotal prims S a))
        (keygenRefPrefix prims D (keygenFiniteTotal prims S a) A x z parts) >>= fun π =>
      ($ᵗ (KeygenFresh C)) >>= fun u =>
      simulateQ (fixedLocal prims (keygenFiniteTotal prims S a))
        (W (π.1, keygenRefMixedOutputs prims D (keygenFiniteTotal prims S a) (keygenTableOf u.1 u.2)
          (keygenTableOf u.1 u.2) parts π.2))] := by
  rw [uniformSample_prod_bind]
  refine evalDist_bind_congr' _ fun a => ?_
  simp only [keygenReferenceLocalGame_eq_prefix, simulateQ_bind, keygenRefOutputs_eq_mixed]
  rw [DeferredSampling.evalDist_bind_comm]
  refine evalDist_bind_congr' _ fun π => ?_
  rw [← evalDist_keygenRestrict_bind]
  refine evalDist_bind_congr' _ fun t => ?_
  rw [keygenRefMixedOutputs_restrict prims D _ t t]

theorem evalDist_keygenIndep_Z (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) :
    𝒟[($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
      simulateQ (fixedLocal prims (keygenFiniteTotal prims S p.1))
        (keygenReferenceLocalGame prims D (keygenFiniteTotal prims S p.1) p.2 A x z Z parts)] =
    𝒟[keygenStageBSampler prims D A x z S parts >>= fun w =>
      keygenStageBRun prims D A Z S parts w w.2.2.2 w.2.2.2] := by
  rw [evalDist_keygenIndep_body]
  unfold keygenStageBSampler
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' _ fun a => evalDist_bind_congr' _ fun π => ?_
  simp only [keygenStageBRun]
  rw [evalDist_uniform_bind_const]

theorem evalDist_keygenIndep_hiddenZ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) :
    𝒟[($ᵗ ((S → HashOutput) × (KeyName C → HashOutput))) >>= fun p =>
      simulateQ (fixedLocal prims (keygenFiniteTotal prims S p.1))
        (keygenReferenceLocalGame prims D (keygenFiniteTotal prims S p.1) p.2 A x z (keygenHiddenZ D Z) parts)] =
    𝒟[keygenStageBSampler prims D A x z S parts >>= fun w =>
      keygenStageBRun prims D A Z S parts w w.2.2.1 w.2.2.2] := by
  rw [evalDist_keygenIndep_body]
  unfold keygenStageBSampler
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' _ fun a => evalDist_bind_congr' _ fun π => evalDist_bind_congr' _ fun u => ?_
  rw [keygenHiddenZ_eq_gen]
  simp only [keygenHiddenZGen, simulateQ_bind, simulateQ_fixedLocal_private]
  rw [uniformSample_prod_bind]
  refine evalDist_bind_congr' _ fun s => evalDist_bind_congr' _ fun p => ?_
  unfold keygenStageBRun
  rw [keygenRefMixedOutputs_overlay]

/-- The honest operators that accept under a table. -/
def keygenRefReceivers (D : C.Coalition) (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C)
    (m : Option ((C.Party → Mail C E) × (C.Party → Mail C E) × (C.Party → Mail C E))) : C.Party → Bool :=
  fun i => (keygenRefOutputs prims D h table parts m i).isSome

/-- The receivers of the two fresh tables differ. -/
def KeygenReceiversGap (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (S : Finset (Query C))
    (r : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × KeygenFresh C × KeygenFresh C)) : Prop :=
  keygenRefReceivers prims D (keygenFiniteTotal prims S r.2.1) (keygenTableOf r.2.2.2.1.1 r.2.2.2.1.2) r.1 r.2.2.1.2 ≠
    keygenRefReceivers prims D (keygenFiniteTotal prims S r.2.1) (keygenTableOf r.2.2.2.2.1 r.2.2.2.2.2) r.1 r.2.2.1.2

theorem keygenStageBRun_le (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (w : (S → HashOutput) × (A.State × Option ((C.Party → Mail C E) × (C.Party → Mail C E) ×
      (C.Party → Mail C E))) × KeygenFresh C × KeygenFresh C) (u u' v : KeygenFresh C) :
    Pr[= true | keygenStageBRun prims D A Z S parts w u v] ≤ Pr[= true | keygenStageBRun prims D A Z S parts w u' v] +
      (if keygenRefReceivers prims D (keygenFiniteTotal prims S w.1) (keygenTableOf u.1 u.2) parts w.2.1.2 ≠
        keygenRefReceivers prims D (keygenFiniteTotal prims S w.1) (keygenTableOf u'.1 u'.2) parts w.2.1.2
        then 1 else 0) := by
  split_ifs with hg
  · exact le_trans probOutput_le_one le_add_self
  · rw [add_zero]
    unfold keygenStageBRun
    rw [keygenRefMixedOutputs_receivers prims D _ _ (keygenTableOf u'.1 u'.2) _ parts _ (not_not.mp hg)]

/-- Stage B on one choice of parts: the gap is at most the probability that the receivers differ. -/
theorem keygenStageB_parts (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) (S : Finset (Query C))
    (parts : C.Party → Parts C) (left right : _ → KeygenFresh C)
    (hg : ∀ w, keygenRefReceivers prims D (keygenFiniteTotal prims S w.1) (keygenTableOf (left w).1 (left w).2)
        parts w.2.1.2 ≠ keygenRefReceivers prims D (keygenFiniteTotal prims S w.1)
          (keygenTableOf (right w).1 (right w).2) parts w.2.1.2 → KeygenReceiversGap prims D A S (parts, w)) :
    Pr[= true | keygenStageBSampler prims D A x z S parts >>= fun w =>
        keygenStageBRun prims D A Z S parts w (left w) w.2.2.2] ≤
      Pr[= true | keygenStageBSampler prims D A x z S parts >>= fun w =>
        keygenStageBRun prims D A Z S parts w (right w) w.2.2.2] +
      Pr[fun w => KeygenReceiversGap prims D A S (parts, w) | keygenStageBSampler prims D A x z S parts] := by
  refine (probOutput_bind_le_add_tsum _ _ _ _ fun w =>
    keygenStageBRun_le prims D A Z S parts w (left w) (right w) w.2.2.2).trans ?_
  gcongr
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun w => ?_
  split_ifs with h₁ h₂
  · simp
  · exact absurd (hg w h₁) h₂
  · simp
  · simp

/-- Stage A on one distinguisher costs the clashes and the guesses. -/
def keygenStageAError (C : Committee) (q : ℕ) : ℝ := ((keygenClashCount C + q * keygenGuessNames C : ℕ) : ℝ) / 2 ^ 256

/-- The open stage: on the independent reference run, replacing the hidden keys by fresh ones moves
the acceptance by at most what remains of half the error after stage A on both distinguishers. -/
def KeygenIndepEcho (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∀ (S : Finset (Query C)), (∀ parts name, keygenNamedInput parts name ∈ S) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z)) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z))) →
      |(Pr[= true | keygenIndepMixture prims D A x z Z S]).toReal -
        (Pr[= true | keygenIndepMixture prims D A x z (keygenHiddenZ D Z) S]).toReal| ≤
        keygenHashError C q / 2 - 2 * keygenStageAError C q

/-- The hidden half on the relabeled reference runs, from stage A and the open stage B. -/
theorem keygenHiddenFreshSwapped_of_indepEcho (hB : KeygenIndepEcho (C := C) (E := E) prims) :
    KeygenHiddenFreshSwapped (C := C) (E := E) prims := by
  intro D A x z Z q hq S hmem h₁ h₂
  have hA₁ := keygenStageA prims D A x z Z S hmem q hq
  have hA₂ := keygenStageA prims D A x z (keygenHiddenZ D Z) S hmem q (isQueryBounded_keygenHiddenZ D A Z q hq)
  have hb := hB D A x z Z q hq S (hmem · ·) h₁ h₂
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

/-- The open core of the hidden half: on the independent reference run, two independent fresh tables
give different receivers with probability at most what remains of half the error. The receivers
depend on a table only through the honest echo comparisons, so this is the echo-collision bound. -/
def KeygenAcceptGap (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∀ (S : Finset (Query C)), (∀ parts name, keygenNamedInput parts name ∈ S) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z)) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z))) →
      (Pr[KeygenReceiversGap prims D A S | keygenPartsKernel (keygenStageBSampler prims D A x z S)]).toReal ≤
        keygenHashError C q / 2 - 2 * keygenStageAError C q

/-- The fresh table `u` makes an echo collision on a pair of honest operators that share a hidden
term, in a transcript that reaches the echo. -/
def KeygenEchoIrregular (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (S : Finset (Query C))
    (r : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × KeygenFresh C × KeygenFresh C))
    (u : KeygenFresh C) : Prop :=
  match r.2.2.1.2 with
  | none => False
  | some (_, rsent, _) => ¬ KeygenEchoRegularHidden D (keygenFiniteTotal prims S r.2.1)
      (keygenReferenceKeys prims D (keygenFiniteTotal prims S r.2.1) (keygenTableOf u.1 u.2) r.1
        (fun i j => rsent j i))

theorem keygenReceiversGap_irregular (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (S : Finset (Query C))
    (r : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × KeygenFresh C × KeygenFresh C))
    (hg : KeygenReceiversGap prims D A S r) :
    KeygenEchoIrregular prims D A S r r.2.2.2.1 ∨ KeygenEchoIrregular prims D A S r r.2.2.2.2 := by
  rcases r with ⟨parts, a, ⟨st, m⟩, u, v⟩
  rcases m with _ | ⟨sent, rsent, esent⟩
  · exact absurd rfl hg
  · by_contra hn
    push Not at hn
    simp only [KeygenEchoIrregular, not_not] at hn
    apply hg
    funext i
    exact keygenReferenceData_receivers_hidden prims D _ _ _ parts sent rsent esent hn.1 hn.2 i

theorem probEvent_keygenEchoIrregular_swap (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (S : Finset (Query C)) :
    Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.2 | keygenPartsKernel (keygenStageBSampler prims D A x z S)] =
      Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.1 |
        keygenPartsKernel (keygenStageBSampler prims D A x z S)] := by
  let sw : (C.Party → Parts C) × ((S → HashOutput) × (A.State × Option ((C.Party → Mail C E) ×
      (C.Party → Mail C E) × (C.Party → Mail C E))) × KeygenFresh C × KeygenFresh C) → _ :=
    fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.2, r.2.2.2.1)
  have he : 𝒟[sw <$> keygenPartsKernel (keygenStageBSampler prims D A x z S)] =
      𝒟[keygenPartsKernel (keygenStageBSampler prims D A x z S)] := by
    unfold keygenPartsKernel keygenStageBSampler
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
    refine evalDist_bind_congr' _ fun parts => evalDist_bind_congr' _ fun a =>
      evalDist_bind_congr' _ fun π => ?_
    exact DeferredSampling.evalDist_bind_comm _ _ _
  have hp : ∀ P : _ → Prop, Pr[P | sw <$> keygenPartsKernel (keygenStageBSampler prims D A x z S)] =
      Pr[P | keygenPartsKernel (keygenStageBSampler prims D A x z S)] := fun P => by
    simp only [probEvent_eq_tsum_ite, probOutput_def, he]
  rw [← hp, probEvent_map]
  rfl

theorem keygenIndepEcho_of_acceptGap (hG : KeygenAcceptGap (C := C) (E := E) prims) :
    KeygenIndepEcho (C := C) (E := E) prims := by
  intro D A x z Z q hq S hmem h₁ h₂
  refine le_trans ?_ (hG D A x z Z q hq S hmem h₁ h₂)
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

/-- The open core of the hidden half, as an echo-collision bound. On the independent reference run,
a fresh table makes the honest echo inputs of two honest operators that share a hidden term distinct
but with equal hashes with probability at most a quarter of what remains of the error. -/
def KeygenEchoFresh (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∀ (S : Finset (Query C)), (∀ parts name, keygenNamedInput parts name ∈ S) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z Z)) →
      KeygenWorldCovered S (free (keygenNormalizedLocalGame D A x z (keygenHiddenZ D Z))) →
      (Pr[fun r => KeygenEchoIrregular prims D A S r r.2.2.2.1 |
        keygenPartsKernel (keygenStageBSampler prims D A x z S)]).toReal ≤
        (keygenHashError C q / 2 - 2 * keygenStageAError C q) / 2

theorem keygenAcceptGap_of_echoFresh (hF : KeygenEchoFresh (C := C) (E := E) prims) :
    KeygenAcceptGap (C := C) (E := E) prims := by
  intro D A x z Z q hq S hmem h₁ h₂
  have hb := hF D A x z Z q hq S hmem h₁ h₂
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

end StageB

section Main

variable {C : Committee} {E : Type} (prims : Primitives)

/-- `KeygenSecurityStatement`, open at the echo-collision core of the hidden half and at the known
half. -/
theorem keygenSecurityFull (hF : KeygenEchoFresh (C := C) (E := E) prims)
    (hK : KeygenKnownMismatch (C := C) (E := E) prims) :
    KeygenSecurityStatement (C := C) (E := E) prims :=
  keygenSecurityProof prims (keygenHiddenFreshSwapped_of_indepEcho prims
    (keygenIndepEcho_of_acceptGap prims (keygenAcceptGap_of_echoFresh prims hF))) hK

/-- The hidden half, open only at the echo-collision bound. -/
theorem keygenHiddenFreshSwapped_of_echoFresh (hF : KeygenEchoFresh (C := C) (E := E) prims) :
    KeygenHiddenFreshSwapped (C := C) (E := E) prims :=
  keygenHiddenFreshSwapped_of_indepEcho prims
    (keygenIndepEcho_of_acceptGap prims (keygenAcceptGap_of_echoFresh prims hF))

end Main

/-- info: 'ThresholdLeanXmssSecurity.keygenSecurityFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenSecurityFull

/-- info: 'ThresholdLeanXmssSecurity.keygenHiddenFreshSwapped_of_echoFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenHiddenFreshSwapped_of_echoFresh

/-- info: 'ThresholdLeanXmssSecurity.keygenStageA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenStageA

end ThresholdLeanXmssSecurity
