import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareMarks

/-!
# Wrong-point witnesses for lazy signing shares

A non-lucky first bad leaves a fully cached point with the wrong low-half XOR.
The cached full outputs at such a point persist. Before the first bad, every
undone point has an absent term. These invariants concern only share execution;
no source, fixed-pad or target-table relation is assumed.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShare.Witness
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def Wrong (τ : CPoint → SigningShareLazy.Digest) (sh : ShareState C) : Prop :=
  ∃ p : CPoint, (∀ T, sh.cache (T, p) ≠ none) ∧ SigningShareLazy.sum C.terms sh p ≠ τ p

def Viol (sh : ShareState C) : Prop :=
  ∃ g k l, sh.bad = some (g, k, l) ∧ ¬(k = .read ∧ l = true)

def ShareOK (τ : CPoint → SigningShareLazy.Digest) (sh : ShareState C) : Prop :=
  (sh.bad = none → ∀ p, p ∉ sh.done → ∃ T, sh.cache (T, p) = none) ∧
    (Viol sh → Wrong τ sh)

def lazyFinish (b : C.Term) (p : CPoint) (target : SigningShareLazy.Digest)
    (sh : ShareState C) : ProbComp SigningShareLazy.HashOutput :=
  (fun h => SigningShareLazy.pair.symm (SigningShareLazy.lowHash h,
    target ^^^ SigningShareLazy.others C.terms sh p b)) <$> ($ᵗ SigningShareLazy.HashOutput)

theorem lazyHandler_eq_handler (τ : CPoint → SigningShareLazy.Digest) :
    lazyHandler (C := C) τ = Marks.handler τ (fun _ => $ᵗ SigningShareLazy.HashOutput) lazyFinish := rfl

theorem shareOK_init (τ : CPoint → SigningShareLazy.Digest) :
    ShareOK (C := C) τ (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
  constructor
  · intro _ p _
    obtain ⟨T, _⟩ := exists_lacked_term (C := C) ∅ (by simp)
    exact ⟨T, rfl⟩
  · rintro ⟨g, k, l, hb, _⟩
    simp [SigningShareLazy.init] at hb

/- Ports of the private A179 slack_some/slack_none at SigningShareLazy:854–860. -/
theorem slack_some (order : List C.Term) (sh : ShareState C) (p : CPoint) (b : C.Term)
    (h : SigningShareLazy.slack order sh p = some b) :
    b ∈ order ∧ sh.cache (b, p) = none := by
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem slack_none (order : List C.Term) (sh : ShareState C) (p : CPoint) :
    SigningShareLazy.slack order sh p = none ↔ ∀ b ∈ order, sh.cache (b, p) ≠ none := by
  simp [SigningShareLazy.slack, List.find?_eq_none]

/-- Full outputs, including the high halves, are retained at cached entries. -/
def Extends (sh sh' : ShareState C) : Prop :=
  ∀ y v, sh.cache y = some v → sh'.cache y = some v

theorem Extends.refl (sh : ShareState C) : Extends sh sh := fun _ _ h => h

theorem Extends.trans {sh mid sh' : ShareState C} (h : Extends sh mid)
    (h' : Extends mid sh') : Extends sh sh' := fun y v hv => h' y v (h y v hv)

theorem extends_put (sh : ShareState C) (b : C.Term) (p : CPoint)
    (v : SigningShareLazy.HashOutput) (hn : sh.cache (b, p) = none) :
    Extends sh (SigningShareLazy.put sh b p v) := by
  intro y w hw
  by_cases hy : y = (b, p)
  · subst y
    simp [hn] at hw
  · simpa [SigningShareLazy.put, Function.update, hy] using hw

theorem sum_eq_of_row (sh sh' : ShareState C) (p : CPoint)
    (h : ∀ T, sh'.cache (T, p) = sh.cache (T, p)) :
    SigningShareLazy.sum C.terms sh' p = SigningShareLazy.sum C.terms sh p := by
  unfold SigningShareLazy.sum
  congr 1
  funext T
  simp only [SigningShareLazy.low, h T]

/-- A fully cached wrong point survives every extension of its full outputs. -/
theorem Wrong.extends {τ : CPoint → SigningShareLazy.Digest} {sh sh' : ShareState C}
    (h : Wrong τ sh) (he : Extends sh sh') : Wrong τ sh' := by
  obtain ⟨p, hp, hs⟩ := h
  have hc : ∀ T, sh'.cache (T, p) = sh.cache (T, p) := by
    intro T
    cases hT : sh.cache (T, p) with
    | none => exact (hp T hT).elim
    | some v => exact he (T, p) v hT
  exact ⟨p, fun T => by rw [hc T]; exact hp T, by rw [sum_eq_of_row sh sh' p hc]; exact hs⟩

def readNext (τ : CPoint → SigningShareLazy.Digest) (sh : ShareState C)
    (b : C.Term) (p : CPoint) (tag : Bool) (v : SigningShareLazy.HashOutput) : ShareState C :=
  { SigningShareLazy.put sh b p v with bad := (sh.bad <|>
      (SigningShareLazy.setsBad C.terms τ (.read b p tag) sh).map
        (fun r => (r.1, r.2, decide (SigningShareLazy.sum C.terms (SigningShareLazy.put sh b p v) p = τ p)))) }


/-- The no-slack part of A179 good_put uses only the pre-bad missing-slot clause. -/
theorem read_missing (τ : CPoint → SigningShareLazy.Digest) (sh : ShareState C)
    (h : ShareOK τ sh) (b : C.Term) (p : CPoint) (tag : Bool)
    (v : SigningShareLazy.HashOutput) (hc : sh.cache (b, p) = none)
    (hb : (readNext τ sh b p tag v).bad = none) :
    ∀ p', p' ∉ sh.done → ∃ T, (SigningShareLazy.put sh b p v).cache (T, p') = none := by
  have hold : sh.bad = none := by
    cases hh : sh.bad <;> simp_all [readNext]
  have hsets : SigningShareLazy.setsBad C.terms τ (.read b p tag) sh = none := by
    simpa [readNext, hold] using hb
  intro p' hp'
  by_cases he : p' = p
  · subst p'
    have hn : ¬∀ a ∈ C.terms, a ≠ b → sh.cache (a, p) ≠ none := by
      intro ha
      have hlast : sh.cache (b, p) = none ∧ p ∉ sh.done ∧
          ∀ a ∈ C.terms, a ≠ b → sh.cache (a, p) ≠ none := ⟨hc, hp', ha⟩
      simp only [SigningShareLazy.setsBad, if_pos hlast, Option.some_ne_none] at hsets
    push Not at hn
    obtain ⟨a, _, hab, ha⟩ := hn
    exact ⟨a, by simp [SigningShareLazy.put, Function.update, hab, ha]⟩
  · obtain ⟨a, ha⟩ := h.1 hold p' hp'
    exact ⟨a, by simp [SigningShareLazy.put, Function.update, he, ha]⟩

/-- The last fresh read records exactly whether its now-full row is lucky. -/
theorem read_shareOK (τ : CPoint → SigningShareLazy.Digest) (sh : ShareState C)
    (h : ShareOK τ sh) (b : C.Term) (p : CPoint) (tag : Bool)
    (v : SigningShareLazy.HashOutput) (hc : sh.cache (b, p) = none) :
    ShareOK τ (readNext τ sh b p tag v) := by
  refine ⟨fun hb p' hp' => read_missing τ sh h b p tag v hc hb p' hp', ?_⟩
  intro hv
  have he : Extends sh (readNext τ sh b p tag v) := extends_put sh b p v hc
  cases hold : sh.bad with
  | some old =>
      apply Wrong.extends (h.2 ?_) he
      obtain ⟨g, k, l, hb, hnot⟩ := hv
      refine ⟨g, k, l, ?_, hnot⟩
      simpa [readNext, hold] using hb
  | none =>
      obtain ⟨g, k, l, hb, hnot⟩ := hv
      simp only [readNext, hold, SigningShareLazy.setsBad] at hb
      split at hb
      · rename_i hlast
        simp only [Option.map_some] at hb
        obtain ⟨rfl, rfl, hl⟩ := hb
        refine ⟨p, ?_, ?_⟩
        · intro T
          by_cases ht : T = b
          · subst T
            simp [readNext, SigningShareLazy.put]
          · simpa [readNext, SigningShareLazy.put, Function.update, ht] using hlast.2.2 T (mem_terms T) ht
        · intro hs
          apply hnot
          have hs' : SigningShareLazy.sum C.terms (SigningShareLazy.put sh b p v) p = τ p := hs
          exact ⟨rfl, by simp [hs']⟩
      · simp at hb

def finishValue (sh : ShareState C) (b : C.Term) (p : CPoint)
    (target : SigningShareLazy.Digest) (hi : SigningShareLazy.HashOutput) : SigningShareLazy.HashOutput :=
  SigningShareLazy.pair.symm (SigningShareLazy.lowHash hi,
    target ^^^ SigningShareLazy.others C.terms sh p b)

def completeNext (τ : CPoint → SigningShareLazy.Digest) (sh filled : ShareState C)
    (b : C.Term) (p : CPoint) (target : SigningShareLazy.Digest)
    (hi : SigningShareLazy.HashOutput) (tag : Bool) : ShareState C :=
  { SigningShareLazy.put filled b p (finishValue filled b p target hi) with
    done := insert p filled.done
    bad := (sh.bad <|> (if target = τ p then none else some (tag, .complete, false))) }

/-- The lazy slack output enforces the requested XOR for every sampled high half. -/
theorem finishValue_sum (sh : ShareState C) (b : C.Term) (p : CPoint)
    (target : SigningShareLazy.Digest) (hi : SigningShareLazy.HashOutput) :
    SigningShareLazy.sum C.terms (SigningShareLazy.put sh b p (finishValue sh b p target hi)) p = target := by
  rw [SigningShareLazy.sum_put C.terms terms_nodup b (mem_terms b)]
  simp [finishValue, BitVec.xor_assoc]

/-- Completing around an absent slack preserves all old outputs and fills its row. -/
theorem complete_frame (τ : CPoint → SigningShareLazy.Digest) (sh filled : ShareState C)
    (b : C.Term) (p : CPoint) (target : SigningShareLazy.Digest)
    (hi : SigningShareLazy.HashOutput) (tag : Bool)
    (hs : SigningShareLazy.slack C.terms sh p = some b)
    (hf : filled ∈ support (SigningShareLazy.fillTerms
      (fun _ => $ᵗ SigningShareLazy.HashOutput) p (C.terms.filter (· ≠ b)) sh)) :
    Extends sh (completeNext τ sh filled b p target hi tag) ∧
    (∀ T, (completeNext τ sh filled b p target hi tag).cache (T, p) ≠ none) ∧
    (∀ y, y.2 ≠ p → (completeNext τ sh filled b p target hi tag).cache y = sh.cache y) ∧
    filled.done = sh.done := by
  have fr := SigningCompilerShare.fillTerms_frame _ p (C.terms.filter (· ≠ b)) sh filled hf
  have hb : filled.cache (b, p) = none := by
    rw [fr.2.2.2.1 (b, p) (Or.inr (by simp))]
    exact (slack_some C.terms sh p b hs).2
  refine ⟨?_, ?_, ?_, fr.1⟩
  · exact (show Extends sh filled from fr.2.2.1).trans
      (extends_put filled b p (finishValue filled b p target hi) hb)
  · intro T
    by_cases ht : T = b
    · subst T
      simp [completeNext, SigningShareLazy.put]
    · simpa [completeNext, SigningShareLazy.put, Function.update, ht] using
        fr.2.2.2.2 T (by simp [ht, mem_terms])
  · intro y hy
    have hne : y ≠ (b, p) := fun he => hy (congrArg Prod.snd he)
    simp only [completeNext, SigningShareLazy.put, Function.update_of_ne hne]
    exact fr.2.2.2.1 y (Or.inl hy)

theorem complete_shareOK (τ : CPoint → SigningShareLazy.Digest) (sh filled : ShareState C)
    (h : ShareOK τ sh) (b : C.Term) (p : CPoint) (target : SigningShareLazy.Digest)
    (hi : SigningShareLazy.HashOutput) (tag : Bool)
    (hs : SigningShareLazy.slack C.terms sh p = some b)
    (hf : filled ∈ support (SigningShareLazy.fillTerms
      (fun _ => $ᵗ SigningShareLazy.HashOutput) p (C.terms.filter (· ≠ b)) sh)) :
    ShareOK τ (completeNext τ sh filled b p target hi tag) := by
  have fr := complete_frame τ sh filled b p target hi tag hs hf
  constructor
  · intro hb p' hp'
    have hold : sh.bad = none := by
      cases hh : sh.bad <;> simp_all [completeNext]
    have hpp : p' ≠ p := by
      intro he
      subst p'
      exact hp' (Finset.mem_insert_self ..)
    have hpd : p' ∉ sh.done := by
      intro hd
      apply hp'
      change p' ∈ insert p filled.done
      rw [fr.2.2.2]
      exact Finset.mem_insert_of_mem hd
    obtain ⟨T, hT⟩ := h.1 hold p' hpd
    exact ⟨T, (fr.2.2.1 (T, p') hpp).trans hT⟩
  · intro hv
    cases hold : sh.bad with
    | some old =>
        apply Wrong.extends (h.2 ?_) fr.1
        obtain ⟨g, k, l, hb, hnot⟩ := hv
        exact ⟨g, k, l, by simpa [completeNext, hold] using hb, hnot⟩
    | none =>
        by_cases ht : target = τ p
        · obtain ⟨g, k, l, hb, _⟩ := hv
          simp [completeNext, hold, ht] at hb
        · refine ⟨p, fr.2.1, ?_⟩
          change SigningShareLazy.sum C.terms
            (SigningShareLazy.put filled b p (finishValue filled b p target hi)) p ≠ τ p
          rw [finishValue_sum]
          exact ht

/-- A no-slack completion cannot be a first bad under the missing-slot clause. -/
theorem noSlack_shareOK (τ : CPoint → SigningShareLazy.Digest) (sh : ShareState C)
    (h : ShareOK τ sh) (p : CPoint) (tag : Bool) (hd : p ∉ sh.done)
    (hs : SigningShareLazy.slack C.terms sh p = none) :
    ShareOK τ { sh with bad := sh.bad <|> some (tag, .complete, false) } := by
  have hn : sh.bad ≠ none := by
    intro hb
    obtain ⟨T, hT⟩ := h.1 hb p hd
    exact (slack_none C.terms sh p).mp hs T (mem_terms T) hT
  cases hb : sh.bad with
  | none => exact (hn hb).elim
  | some old =>
      have he : { sh with bad := sh.bad <|> some (tag, .complete, false) } = sh := by
        simp only [hb]
        cases sh
        simp_all
      rw [← hb, he]
      exact h

/-- Every supported lazy share step preserves the first-bad wrong-point witness. -/
theorem lazy_shareOK (τ : CPoint → SigningShareLazy.Digest)
    (t : SigningShareLazy.ShareQuery C.Term CPoint Bool) (sh : ShareState C)
    (h : ShareOK τ sh) :
    ∀ z ∈ support ((SigningShareLazy.lazyImpl C.terms τ t).run sh), ShareOK τ z.2 := by
  intro z hz
  cases t with
  | view =>
      simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run,
        mem_support_pure_iff] at hz
      subst z
      exact h
  | read b p tag =>
      cases hc : sh.cache (b, p) with
      | some v =>
          simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run,
            hc, mem_support_pure_iff] at hz
          subst z
          exact h
      | none =>
          simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run,
            hc, mem_support_bind_iff, mem_support_pure_iff] at hz
          obtain ⟨v, _, rfl⟩ := hz
          exact read_shareOK τ sh h b p tag v hc
  | complete p target tag =>
      by_cases hd : p ∈ sh.done
      · simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run,
          hd, if_true, mem_support_pure_iff] at hz
        subst z
        exact h
      · cases hs : SigningShareLazy.slack C.terms sh p with
        | none =>
            simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run,
              hd, if_false, hs, mem_support_pure_iff] at hz
            subst z
            exact noSlack_shareOK τ sh h p tag hd hs
        | some b =>
            simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run,
              hd, if_false, hs, mem_support_bind_iff, mem_support_pure_iff] at hz
            obtain ⟨filled, hf, value, hv, rfl⟩ := hz
            obtain ⟨hi, _, rfl⟩ := mem_support_map_peel _ _ hv
            exact complete_shareOK τ sh filled h b p target hi tag hs hf

/-- Arbitrary share programs retain the lazy first-bad witness invariant. -/
theorem simulate_shareOK {α : Type} (τ : CPoint → SigningShareLazy.Digest)
    (oa : OracleComp (RunSpec C) α) (sh : ShareState C) (h : ShareOK τ sh) :
    ∀ z ∈ support ((simulateQ (lazyHandler τ) oa).run sh), ShareOK τ z.2 := by
  intro z hz
  induction oa using OracleComp.inductionOn generalizing sh with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
      subst z
      exact h
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨mid, hm, hz⟩ := hz
      apply ih mid.1 mid.2 _ hz
      cases t with
      | inl n =>
          simp only [lazyHandler, QueryImpl.add_apply_inl, SigningShareLazy.unifImpl,
            StateT.run, support_map] at hm
          obtain ⟨a, _, rfl⟩ := hm
          exact h
      | inr t => exact lazy_shareOK τ t sh h mid hm

/-- The first bad is either retained verbatim or tagged by the current query. -/
theorem badFrom_update (m : Bool) (sh sh' : ShareState C)
    (next : Option (SigningShareLazy.ImplBad Bool))
    (hn : ∀ r, next = some r → r.1 = m)
    (hb : sh'.bad = (sh.bad <|> next)) :
    ∀ r, sh'.bad = some r → sh.bad = some r ∨ r.1 = m := by
  intro r hr
  rw [hb] at hr
  cases hold : sh.bad with
  | none => exact Or.inr (hn r (by simpa [hold] using hr))
  | some old => exact Or.inl (by simpa [hold] using hr)

/-- Origin-identity mirror of B4 impl_tagLe, for arbitrary draw and finish laws. -/
theorem impl_tagFrom (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (m : Bool) (t : SigningShareLazy.ShareQuery C.Term CPoint Bool)
    (ht : Marks.TagIs m (.inr t)) (sh : ShareState C)
    (z : ShareSpec C t × ShareState C)
    (hz : z ∈ support ((SigningShareLazy.impl C.terms τ draw finish t).run sh)) :
    ∀ r, z.2.bad = some r → sh.bad = some r ∨ r.1 = m := by
  cases t with
  | view =>
      simp only [SigningShareLazy.impl, StateT.run, mem_support_pure_iff] at hz
      subst z
      exact fun _ h => Or.inl h
  | read b p tag =>
      change tag = m at ht
      subst tag
      cases hc : sh.cache (b, p) with
      | some value =>
          simp only [SigningShareLazy.impl, StateT.run, hc, mem_support_pure_iff] at hz
          subst z
          exact fun _ h => Or.inl h
      | none =>
          simp only [SigningShareLazy.impl, StateT.run, hc, mem_support_bind_iff,
            mem_support_pure_iff] at hz
          obtain ⟨v, _, rfl⟩ := hz
          apply badFrom_update m sh _ _ _ rfl
          intro r hb
          simp only [SigningShareLazy.setsBad] at hb
          split at hb <;> simp_all
          exact (congrArg Prod.fst hb).symm
  | complete p target tag =>
      change tag = m at ht
      subst tag
      by_cases hd : p ∈ sh.done
      · simp only [SigningShareLazy.impl, StateT.run, hd, if_true, mem_support_pure_iff] at hz
        subst z
        exact fun _ h => Or.inl h
      · cases hs : SigningShareLazy.slack C.terms sh p with
        | none =>
            simp only [SigningShareLazy.impl, StateT.run, hd, if_false, hs,
              mem_support_pure_iff] at hz
            subst z
            apply badFrom_update m sh _ _ _ rfl
            intro r hb
            cases hb
            rfl
        | some b =>
            simp only [SigningShareLazy.impl, StateT.run, hd, if_false, hs,
              mem_support_bind_iff, mem_support_pure_iff] at hz
            obtain ⟨filled, _, value, _, rfl⟩ := hz
            apply badFrom_update m sh _ _ _ rfl
            intro r hb
            split at hb <;> simp_all
            exact (congrArg Prod.fst hb).symm

/-- Across a constant-tag program, a final bad record is old or has that tag. -/
theorem simulate_tagFrom {α : Type} (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (m : Bool) (oa : OracleComp (RunSpec C) α) (ha : Queries (Marks.TagIs m) oa)
    (sh : ShareState C) (z : α × ShareState C)
    (hz : z ∈ support ((simulateQ (Marks.handler τ draw finish) oa).run sh)) :
    ∀ r, z.2.bad = some r → sh.bad = some r ∨ r.1 = m := by
  induction oa using OracleComp.inductionOn generalizing sh with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
      subst z
      exact fun _ h => Or.inl h
  | query_bind t next ih =>
      have hh := (isQueryBound_query_bind_iff ..).mp ha
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨mid, hm, hz⟩ := hz
      intro r hr
      rcases ih mid.1 (hh.2 mid.1) mid.2 hz r hr with hold | htag
      · cases t with
        | inl n =>
            simp only [Marks.handler, QueryImpl.add_apply_inl, SigningShareLazy.unifImpl,
              StateT.run, support_map] at hm
            obtain ⟨a, _, rfl⟩ := hm
            exact Or.inl hold
        | inr t => exact impl_tagFrom τ draw finish m t hh.1 sh mid hm r hold
      · exact Or.inr htag

end ThresholdLeanXmssSecurity.SigningCompilerShare.Witness

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.lazyHandler_eq_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.lazyHandler_eq_handler

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.shareOK_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.shareOK_init

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.lazy_shareOK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.lazy_shareOK

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.simulate_shareOK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.simulate_shareOK

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.simulate_tagFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Witness.simulate_tagFrom
