import ThresholdLeanXmssSecurity.Proof.LifetimeJointHop
import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenCapQuiet
import XmssSecurity.Proof.QueryBoundSupport

/-!
# Counts from a budget on complete execution paths

The counted trace of a prefix consumes its actual number of calls. Its
continuation retains the unused budget on that same path.

* `earlyCached_le` gives the hidden-input prequery estimate from one bound on
  `setupEarly`; `joint_setupHit_bound_path` gives the selected setup's key-hit
  estimate from that prefix's path budget.
* `flagProgram_bound_path` gives `(3*Q*m + 4*m^2)/2^256` from `ReferenceBudget`,
  one bound on each complete fixed reference prefix and its selected tail.
  The three `Q*m` contributions protect prefix inputs, tail inputs and keys.
* No estimate requires a bound on an adversary state outside the relevant
  prefix's support. Applying the counting lemmas to a lifetime requires the
  source-to-prefix and source-to-reference budget transports for that instance.

The threshold counting and private-shift arguments are those of `Tree`,
`TreeKeyHit`, `TreeKeyAimed` and `LifetimeJointHop`. Their per-state bounds are
replaced here by supported-prefix residual bounds.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimePathCount
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} {E α β : Type}

/-- The actual counted prefix leaves exactly its unused path budget. -/
theorem hashLog_residual (oa : OracleComp (LocalSpec C) α) (k : α → OracleComp (LocalSpec C) β) :
    ∀ Q, IsQueryBoundP (oa >>= k) Counted Q →
      ∀ r ∈ support (prssHashLog oa), r.2.length ≤ Q ∧
        IsQueryBoundP (k r.1) Counted (Q - r.2.length) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro Q h r hr
      simp only [prssHashLog_pure, mem_support_pure_iff] at hr
      subst r
      simp only [pure_bind] at h
      exact ⟨Nat.zero_le _, h⟩
  | query_bind t next ih =>
      intro Q h r hr
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
      simp only [prssHashLog_bind, prssHashLog_query, bind_assoc, pure_bind,
        mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨y, _, z, hz, rfl⟩ := hr
      obtain ⟨hlen, hrest⟩ := ih y _ (h.2 y) z hz
      rw [List.length_append, prssCountedHashInputs_length]
      by_cases ht : Counted t
      · simp only [if_pos ht] at hlen hrest ⊢
        have pos : 0 < Q := h.1.resolve_left (fun hn => hn ht)
        exact ⟨by omega, hrest.mono (by omega)⟩
      · simp only [if_neg ht, zero_add] at hlen hrest ⊢
        exact ⟨hlen, hrest⟩

/-- The two setup rounds use their joint path budget, including early aborts. -/
theorem earlyRounds_log_length (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : (prssLoggedAdversary A).State) (data : C.Party → Parts C × List HashOutput)
    (Q : ℕ) (hQ : IsQueryBoundP (prssEarlyDataRounds D A state.1 data) Counted Q)
    (r : (prssLoggedAdversary A).State × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (hr : r ∈ support (prssEarlyDataRounds D (prssLoggedAdversary A) state data)) :
    r.1.2.length ≤ state.2.length + Q := by
  change A.State × List (Query C) at state
  change (A.State × List (Query C)) × (C.Party → Mail C E) × Option (C.Party → Mail C E) at r
  unfold prssEarlyDataRounds at hQ hr
  simp only [prssLoggedAdversary, bind_assoc, pure_bind] at hr
  change r ∈ support (prssHashLog (A.round state.1 (prssCommitVisible D data)) >>= _) at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨first, hfirst, hr⟩ := hr
  obtain ⟨hlen, hrest⟩ := hashLog_residual (A.round state.1 (prssCommitVisible D data)) _ Q hQ first hfirst
  dsimp only at hrest hr
  by_cases halt : ∀ i, i ∉ D.1 → ¬ prssCommitActive D first.1.2 i
  · rw [if_pos halt] at hr
    simp only [mem_support_pure_iff] at hr
    subst r
    simp only [List.length_append]
    omega
  · rw [if_neg halt] at hrest hr
    simp only [pure_bind] at hrest
    change r ∈ support (prssHashLog (A.round first.1.1
      (prssRevealVisible D (prssCommitActive D first.1.2) (fun i => (data i).1))) >>= _) at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨last, hlast, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    have hl := prssHashLog_length _ _ (IsQueryBoundP.of_bind_left hrest) last hlast
    simp only [List.length_append]
    omega

/-- A supported start result retains the rest of the setup's path budget. -/
theorem early_budget (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) (Q : ℕ)
    (hQ : IsQueryBoundP (setupEarly D A start) Counted Q)
    (state : (prssLoggedAdversary A).State) (hs : state ∈ support (prssHashLog start)) :
    state.2.length ≤ Q ∧ ∀ data ∈ support (prssInitialData D),
      IsQueryBoundP (prssEarlyDataRounds D A state.1 data) Counted (Q - state.2.length) := by
  unfold setupEarly at hQ
  obtain ⟨hlen, hrest⟩ := hashLog_residual start _ Q hQ state hs
  refine ⟨hlen, fun data hd => ?_⟩
  exact IsQueryBoundP.of_bind_left
    (IsQueryBoundP.continuation_mono_of_mem_support Counted _ _ _ hrest data hd)

/-- Truncation keeps every observed query when the complete prefix fits `Q`. -/
theorem earlyObserve_trace_take (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q)
    (i : C.Party) (pick : Query C → HashOutput) (out : Parts C → Finset HashOutput → α) :
    prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => out parts ((r.1.2.map pick).toFinset)) =
      prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => out parts (prssTraceCandidates Q pick r.1.2)) := by
  unfold prssEarlyObserve
  apply bind_congr_of_forall_mem_support
  intro state hs
  obtain ⟨hlen, hrest⟩ := early_budget D A start Q hQ state hs
  apply bind_congr_of_forall_mem_support
  intro data hd
  apply bind_congr_of_forall_mem_support
  intro r hr
  have hb := earlyRounds_log_length D A state data _ (hrest data hd) r hr
  dsimp only
  rw [prssTraceCandidates_all Q pick r.1.2 (by omega)]

/-- The setup estimate with one bound on the complete prefix. -/
theorem earlyTrace_term_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (hT : Hidden D (.term T)) (pick : Query C → HashOutput) :
    Pr[= true | (simulateQ (localAnswer prims)
      (prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => decide (parts.term T ∈ (r.1.2.map pick).toFinset)))).run' ∅] ≤
      (Q : ℝ≥0∞) / 2 ^ 256 := by
  rw [earlyObserve_trace_take D A start Q hQ i pick
    (fun parts guesses => decide (parts.term T ∈ guesses))]
  exact prob_prssEarlyObserve_hiddenTerm_le prims D (prssLoggedAdversary A) (prssHashLog start)
    i hi T hT (fun r => prssTraceCandidates Q pick r.1.2) Q
    (fun r => prssTraceCandidates_card Q pick r.1.2)


/-- The setup estimate with one bound on the complete prefix. -/
theorem earlyTrace_pair_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q) (i : C.Party) (hi : i ∉ D.1)
    (j : C.Party) (hj : j ∉ D.1) (pick : Query C → HashOutput) :
    Pr[= true | (simulateQ (localAnswer prims)
      (prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => decide (parts.pair j ∈ (r.1.2.map pick).toFinset)))).run' ∅] ≤
      (Q : ℝ≥0∞) / 2 ^ 256 := by
  rw [earlyObserve_trace_take D A start Q hQ i pick
    (fun parts guesses => decide (parts.pair j ∈ guesses))]
  exact prob_prssEarlyObserve_hiddenPair_le prims D (prssLoggedAdversary A) (prssHashLog start)
    i hi j hj (fun r => prssTraceCandidates Q pick r.1.2) Q
    (fun r => prssTraceCandidates_card Q pick r.1.2)


/-- The setup estimate with one bound on the complete prefix. -/
theorem earlyInput_term_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q) (T : C.Term) (hT : Hidden D (.term T))
    (i : C.Party) (hi : i ∈ C.holders T) :
    Pr[fun r => prssTermInput r.1 T ∈ r.2.1.2 |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅] ≤
      (Q : ℝ≥0∞) / 2 ^ 256 := by
  let pick : Query C → HashOutput := prssDerivePick ((C.parties.filter (· ∈ C.holders T)).idxOf i)
  have hb := earlyTrace_term_le prims D A start Q hQ
    i (hidden_term_holders D hT i hi) T hT pick
  rw [prssEarlyObserve_eq_map] at hb
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at hb
  rw [← probEvent_eq_eq_probOutput, probEvent_map] at hb
  rw [StateT.run'_eq, probEvent_map]
  refine le_trans (probEvent_mono ?_) hb
  rintro ⟨r,cache⟩ _ hr
  dsimp only [Function.comp_def] at hr
  simp only [Function.comp_def, decide_eq_true_eq, List.mem_toFinset, List.mem_map]
  exact ⟨prssTermInput r.1 T, hr, prssTermInput_pick r.1 T i hi⟩


/-- The setup estimate with one bound on the complete prefix. -/
theorem earlyInput_pair_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q) (p : C.Pair) (hp : Hidden D (.pair p)) :
    Pr[fun r => prssPairInput r.1 p ∈ r.2.1.2 |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅] ≤
      (Q : ℝ≥0∞) / 2 ^ 256 := by
  have hb := earlyTrace_pair_le prims D A start Q hQ
    p.1.1 hp.1 p.1.2 hp.2 (prssDerivePick 0)
  rw [prssEarlyObserve_eq_map] at hb
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at hb
  rw [← probEvent_eq_eq_probOutput, probEvent_map] at hb
  rw [StateT.run'_eq, probEvent_map]
  refine le_trans (probEvent_mono ?_) hb
  rintro ⟨r,cache⟩ _ hr
  dsimp only [Function.comp_def] at hr
  simp only [Function.comp_def, decide_eq_true_eq, List.mem_toFinset, List.mem_map]
  exact ⟨prssPairInput r.1 p, hr, prssPairInput_pick r.1 p⟩


/-- The setup estimate with one bound on the complete prefix. -/
theorem earlyInputBad_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q) :
    Pr[fun r => prssEarlyInputBad D r.1 r.2.1.2 |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅] ≤
      (Q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 := by
  let run := (simulateQ (localAnswer prims)
    (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅
  let Result := (C.Party → Parts C) × (prssLoggedAdversary A).State ×
    (C.Party → Mail C E) × Option (C.Party → Mail C E)
  let event : C.Term ⊕ C.Pair → Result → Prop := fun name r => match name with
    | .inl T => Hidden D (.term T) ∧ prssTermInput r.1 T ∈ r.2.1.2
    | .inr p => Hidden D (.pair p) ∧ prssPairInput r.1 p ∈ r.2.1.2
  have hb (name : C.Term ⊕ C.Pair) : Pr[event name | run] ≤ (Q : ℝ≥0∞) / 2 ^ 256 := by
    cases name with
    | inl T =>
      by_cases hh : Hidden D (.term T)
      · obtain ⟨i,hi⟩ := prss_exists_holder T
        simpa only [event, hh, true_and] using
          earlyInput_term_le prims D A start Q hQ T hh i hi
      · simp [event, hh, probEvent_def]
    | inr p =>
      by_cases hh : Hidden D (.pair p)
      · simpa only [event, hh, true_and] using
          earlyInput_pair_le prims D A start Q hQ p hh
      · simp [event, hh, probEvent_def]
  have he (r : Result) : prssEarlyInputBad D r.1 r.2.1.2 ↔ ∃ name ∈ (Finset.univ : Finset (C.Term ⊕ C.Pair)), event name r := by
    simp only [Finset.mem_univ, true_and, Sum.exists, event, prssEarlyInputBad]
  change Pr[fun r => prssEarlyInputBad D r.1 r.2.1.2 | run] ≤ _
  calc
    _ = Pr[fun r => ∃ name ∈ (Finset.univ : Finset (C.Term ⊕ C.Pair)), event name r | run] :=
      probEvent_ext fun r _ => he r
    _ ≤ ∑ name : C.Term ⊕ C.Pair, Pr[event name | run] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _name : C.Term ⊕ C.Pair, (Q : ℝ≥0∞) / 2 ^ 256 := Finset.sum_le_sum fun name _ => hb name
    _ = (Q : ℝ≥0∞) * (Fintype.card C.Term + Fintype.card C.Pair) / 2 ^ 256 := by
      simp [Fintype.card_sum, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ _ := by
      rw [card_term]
      gcongr
      exact card_pair_le C


/-- The setup estimate with one bound on the complete prefix. -/
theorem earlyCachedInput_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q) :
    Pr[fun r =>
      (∃ T : C.Term, Hidden D (.term T) ∧ r.2 (prssTermInput r.1.1 T) ≠ none) ∨
      (∃ p : C.Pair, Hidden D (.pair p) ∧ r.2 (prssPairInput r.1.1 p) ≠ none) |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run ∅] ≤
      (Q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 := by
  have hb := earlyInputBad_le prims D A start Q hQ
  rw [StateT.run'_eq, probEvent_map] at hb
  refine le_trans (probEvent_mono ?_) hb
  intro r hr hbad
  have hf := prssEarlyTable_derive_fresh prims D A start r hr
  rcases hbad with ⟨T,hT,hcached⟩ | ⟨p,hp,hcached⟩
  · left
    refine ⟨T,hT,?_⟩
    by_contra hnot
    exact hcached (hf .prss .term _ hnot)
  · right
    refine ⟨p,hp,?_⟩
    by_contra hnot
    exact hcached (hf .prss .pair _ hnot)


/-- The setup estimate with one bound on the complete prefix. -/
theorem earlyCached_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q) :
    Pr[EarlyCached D | (simulateQ (localAnswer prims) (setupEarly D A start)).run ∅] ≤
      (Q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 := by
  have h := earlyCachedInput_le prims D A start Q hQ
  have ht : prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start) =
      (fun r => ((fun i => (r.1 i).1), r.2)) <$> setupEarly D (prssLoggedAdversary A) (prssHashLog start) := by
    simp [prssEarlyTable, setupEarly, map_bind]
  have hu := congrArg (fun oa => (simulateQ (localAnswer prims) oa).run (∅ : HashCache C))
    (setupEarly_logged D A start)
  simp only [simulateQ_map, StateT.run_map] at hu
  rw [ht, simulateQ_map, StateT.run_map, probEvent_map] at h
  let Q : ((C.Party → Parts C) × A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) ×
      HashCache C → Prop := fun r =>
    (∃ T : C.Term, Hidden D (.term T) ∧ r.2 (prssTermInput r.1.1 T) ≠ none) ∨
      (∃ p : C.Pair, Hidden D (.pair p) ∧ r.2 (prssPairInput r.1.1 p) ≠ none)
  calc _ = Pr[Q | (fun p => ((fun i => (p.1.1 i).1, p.1.2), p.2)) <$>
        (simulateQ (localAnswer prims) (setupEarly D A start)).run ∅] := by
        rw [probEvent_map]
        rfl
    _ = _ := by rw [← hu, probEvent_map]; rfl
    _ ≤ _ := h


/-- The logged setup prefix uses at most its complete path budget. -/
theorem early_log_length (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A start) Counted Q)
    (r : ((C.Party → Parts C × List HashOutput) × (prssLoggedAdversary A).State ×
      (C.Party → Mail C E) × Option (C.Party → Mail C E)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (setupEarly D (prssLoggedAdversary A) (prssHashLog start))).run ∅)) :
    r.1.2.1.2.length ≤ Q := by
  have hr' : r.1 ∈ support (setupEarly D (prssLoggedAdversary A) (prssHashLog start)) := by
    refine support_simulateQ_run'_subset (localAnswer prims) _ (∅ : HashCache C) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  simp only [setupEarly, mem_support_bind_iff, mem_support_pure_iff] at hr'
  obtain ⟨state, hs, data, hd, rounds, hh, he⟩ := hr'
  obtain ⟨hlen, hrest⟩ := early_budget D A start Q hQ state hs
  have hb := earlyRounds_log_length D A state data _ (hrest data hd) rounds hh
  rw [he]
  dsimp only
  omega

/-- Cached hidden stream-key hits at the actual setup boundary, from a complete
prefix budget rather than bounds on arbitrary states of the adversary. -/
theorem setupHit_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Q : ℕ) (hQ : IsQueryBoundP (setupEarly D A (A.start (corruptInputs D x) z)) Counted Q) :
    Pr[fun r => KeyHit D (rowsOf r.1.2) r.2 | worldRun prims (setupPrefix D A x z)] ≤
      ((2 * Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [worldRun_setupPrefix, ← setupEarly_logged_eq D A, bind_map_left, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_add _ _ _ (EarlyCached D)
    (((Fintype.card C.Term + Fintype.card C.Pair) * Q : ℕ) / 2 ^ 256)
    fun a ha hb => ?_).trans ?_
  · have hS : ∀ k, a.2 (.streamKey k) ≠ none → k ∈ logStreamKeys a.1.2.1.2 := by
      intro k hk
      by_contra hm
      exact hk (setupEarly_streamKey_fresh prims D A _ a ha k fun h => hm (mem_logStreamKeys h))
    refine (prob_setupReveal_hit_le prims D (a.1.1, a.1.2.1.1, a.1.2.2) a.2 _ hS hb).trans ?_
    have hl := (logStreamKeys_card a.1.2.1.2).trans (early_log_length prims D A _ Q hQ a ha)
    gcongr
    push_cast
    gcongr
  · have hu := congrArg (fun oa => (simulateQ (localAnswer prims) oa).run (∅ : HashCache C))
      (setupEarly_logged_eq D A (A.start (corruptInputs D x) z))
    simp only [simulateQ_map, StateT.run_map] at hu
    have he : Pr[EarlyCached D | (simulateQ (localAnswer prims)
        (setupEarly D (prssLoggedAdversary A) (prssHashLog (A.start (corruptInputs D x) z)))).run ∅] =
        Pr[EarlyCached D | (simulateQ (localAnswer prims) (setupEarly D A (A.start (corruptInputs D x) z))).run ∅] := by
      rw [← hu, probEvent_map]
      rfl
    rw [he]
    refine (add_le_add (earlyCached_le prims D A _ Q hQ)
      le_rfl).trans ?_
    rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ?_ _
    have hT := card_term C
    have hP := card_pair_le C
    have hn : Q * (C.n.choose (C.t - 1) + C.n.choose 2) +
        (Fintype.card C.Term + Fintype.card C.Pair) * Q ≤
        2 * Q * prssKeyCount C := by
      have hm : Fintype.card C.Term + Fintype.card C.Pair ≤ prssKeyCount C := by
        unfold prssKeyCount termCount; omega
      have hm' : C.n.choose (C.t - 1) + C.n.choose 2 = prssKeyCount C := rfl
      rw [hm']
      nlinarith [Nat.mul_le_mul_left Q hm]
    exact_mod_cast hn

/-- Only supported outcomes contribute to the mean. -/
theorem mean_mono_support {α : Type} (p : ProbComp α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ support p, f a ≤ g a) : aimedMean p f ≤ aimedMean p g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ support p
  · gcongr; exact h a ha
  · simp only [probOutput_eq_zero_of_not_mem_support ha, zero_mul, le_refl]

/-- Removing the adversary tag preserves a predicate-targeted bound. -/
theorem counted_of_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    ∀ Q, IsQueryBoundP (worldRoles.adversary p) WorldCounted Q → IsQueryBoundP p Counted Q := by
  induction p using OracleComp.inductionOn with
  | pure a => intro Q _; trivial
  | query_bind t k ih =>
      intro Q h
      have e : worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
          worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
            fun u => worldRoles.adversary (k u) := by
        simp only [worldRoles, counted, liftComp_bind]
        exact simulateQ_bind _ _ _
      rw [e, adversary_query] at h
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

section Aimed
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (pre : LifetimeBridge.Selector C)
variable (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
open LifetimeJointHop LifetimeBridge

/-- A path budget on the fixed reference prefix and its selected continuation.
It places no condition on an adversary state outside that prefix's support. -/
def ReferenceBudget (Q : ℕ) : Prop :=
  ∀ (h : Query C → HashOutput) (normal : KeyName C → HashOutput) (parts : C.Party → Parts C),
    IsQueryBoundP (worldRoles.adversary (early D pre A h parts) >>=
      referenceTail prims K circuits settings D A Z h normal parts) WorldCounted Q

variable (Q : ℕ) (budget : ReferenceBudget prims K circuits settings D pre A Z Q)
include budget

theorem reference_early_bound (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    IsQueryBoundP (early D pre A h parts) Counted Q :=
  counted_of_adversary _ Q (IsQueryBoundP.of_bind_left (budget h (fun _ => 0) parts))

theorem reference_tail_bound (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (r : LifetimeBridge.JointInput C × Early A)
    (hr : r ∈ support (early D pre A h parts)) :
    IsQueryBoundP (referenceTail prims K circuits settings D A Z h normal parts r) WorldCounted Q := by
  apply IsQueryBoundP.continuation_mono_of_mem_support WorldCounted _ _ Q (budget h normal parts) r
  rwa [LifetimeKeygenCapQuiet.support_adversary]

/-- Protected derivation inputs in the complete reference prefix cost `Q*m`. -/
theorem prefix_hit_bound (h : Query C → HashOutput) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (KeygenFresh C)) (prefixHit prims D pre A h parts)) ≤
      ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold prefixHit
  rw [aimedMean_parts_event]
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by rw [early_exposed]))
  intro parts r hr
  apply aimedSetupLog_length_le _ _ _ r (support_simulateQ_subset _ _ hr)
  apply IsQueryBoundP.of_imp (p' := Counted) _
    (reference_early_bound prims K circuits settings D pre A Z Q budget h parts)
  intro t ht
  rcases t with n | v | a
  · exact ht.elim
  · cases v <;> simp_all [aimedLocalSetup, aimedSetupQuery, Counted]
  · exact ht.elim

/-- The selected reference tail uses the budget of its own supported prefix. -/
theorem tail_log_bound (h : Query C → HashOutput) (keys : KeyName C × HashOutput → Digest)
    (normal : KeyName C → HashOutput) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v | (do
      let r ← keygenPartsKernel (tailLog prims K circuits settings D pre A Z h keys normal)
      let u ← $ᵗ (KeygenFresh C)
      pure (r, u))] ≤ ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by
      simp only [tailLog, early_exposed, referenceTail, aimedReferenceTail_exposed]))
  intro parts out hout
  simp only [tailLog, support_bind, Set.mem_iUnion] at hout
  obtain ⟨r, earlyRun, hr⟩ := hout
  exact aimedSetupLog_length_le _ _
    (aimedKeyLocal_setup_bound prims D keys _ _
      (reference_tail_bound prims K circuits settings D pre A Z Q budget h normal parts r
        (support_simulateQ_subset _ _ earlyRun))
      (aimedReferenceTail_noSetup prims K circuits settings r.1.2.1 r.1.2.2.1 D A r.1.1 Z h
        normal parts r.2)) out (support_simulateQ_subset _ _ hr)

/-- The prefix and tail protection estimates each charge at most one full path. -/
theorem reference_error_bound (h : Query C → HashOutput) (normal : KeyName C → HashOutput) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (referenceError prims K circuits settings D pre A Z h normal) ≤
      ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold referenceError
  rw [aimedMean_add]
  apply add_le_add
  · exact prefix_hit_bound prims K circuits settings D pre A Z Q budget h
  · unfold tailHit aimedTailHit
    have hmove {α β γ : Type} (p : ProbComp α) (q : ProbComp β) (k : α → ProbComp γ)
        (f : α → γ → β → ℝ≥0∞) :
        aimedMean p (fun a => aimedMean (k a) (fun c => aimedMean q (f a c))) =
          aimedMean q (fun b => aimedMean p (fun a => aimedMean (k a) (fun c => f a c b))) := by
      simp_rw [aimedMean_comm (k _) q]
      rw [aimedMean_comm]
    simp_rw [aimedMean_comm ($ᵗ (KeygenFresh C)) ($ᵗ (KeyName C × HashOutput → Digest))]
    rw [hmove (p := Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (q := $ᵗ (KeyName C × HashOutput → Digest))]
    apply aimedMean_le_const
    intro keys
    have hb := tail_log_bound prims K circuits settings D pre A Z Q budget h keys normal
    rw [← aimedMean_parts_event
      (tailLog prims K circuits settings D pre A Z h keys normal)
      (fun parts u out => ∃ v ∈ out.2, AimedPrefixCell D parts u v)] at hb
    unfold tailLog referenceTail at hb
    simp only [← aimedMean_probEvent] at hb
    simpa only [aimedMean_comm ($ᵗ (KeygenFresh C))] using hb

omit budget in
theorem refresh_guess_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (tailQ : ℕ)
    (htail : IsQueryBoundP (aimedReferenceTail prims K circuits settings top tree D A x Z
      (prssHashAt prims (prssExtend S a)) normal parts r) WorldCounted tailQ) :
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => Pr[fun y => y.2 = true |
      aimedEagerFlag prims D (prssExtend S a)
        (rowsOf (aimedFixedBoundary prims D (prssExtend S (aimedRefresh D S parts hmem a echo u))
          (prssDataMask D (prssDataAt (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts)) r).2)
        (aimedReferenceTail prims K circuits settings top tree D A x Z
          (prssHashAt prims (prssExtend S a)) normal parts r)]) ≤
      ((tailQ : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 := by
  rw [aimedMean_probEvent]
  exact probEvent_aimedEagerFresh_le prims D (prssExtend S a) _
    (fun u n k hk hn => aimedRefresh_boundary_hidden prims D S parts hmem hc a echo u r n k hk hn) _ _
    htail


omit budget in
theorem refresh_finish_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a : S → HashOutput)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (tailQ : ℕ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (htail : IsQueryBoundP (aimedReferenceTail prims K circuits settings top tree D A x Z
      (prssHashAt prims (prssExtend S a)) normal parts r) WorldCounted tailQ) :
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo =>
      let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
      aimedFinishProbability prims K circuits settings top tree D A x Z h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r))) ≤
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    ((tailQ : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 +
    aimedMean ($ᵗ (KeygenFresh C))
      (aimedTailHit prims K circuits settings top tree D A x Z (prssHashAt prims (prssExtend S a)) normal parts r) := by
  have hb := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u => aimedMean_mono ($ᵗ (S → HashOutput))
    (fun echo => probEvent_aimedRefresh_finish_le prims K circuits settings top tree D A x Z S normal
      parts hmem hsk hc a echo u r hni hn0))
  simp only [aimedMean_add, aimedMean_const] at hb
  refine hb.trans (add_le_add (add_le_add
    (probEvent_aimedBoundaryException_le prims D S hsk (prssHashAt prims (prssExtend S a)) parts r) ?_) ?_)
  · rw [aimedMean_comm]
    exact aimedMean_le_const _ _ _ (fun echo => refresh_guess_le prims K circuits settings
      top tree D A x Z S normal parts hmem hc a echo r tailQ htail)
  · unfold aimedTailHit
    rw [aimed_prssLocalAt_hashAt]


theorem parts_le (S : Finset (Query C)) (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0) :
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts) ≤
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    ((Q : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 +
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      referenceError prims K circuits settings D pre A Z
        (prssHashAt prims (prssExtend S a)) normal parts) := by
  rw [actualProbability_refresh prims K circuits settings D pre A Z S parts hmem hc,
    aimedMean_comm]
  rw [← aimedMean_const ($ᵗ (S → HashOutput))
    (((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
      ((Q : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256),
    ← aimedMean_add]
  apply aimedMean_mono
  intro a
  have hp := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u => aimedMean_mono ($ᵗ (S → HashOutput))
    (fun echo => actualProbability_prefix_le prims K circuits settings D pre A Z S parts hmem a echo u))
  simp only [aimedMean_add, aimedMean_const] at hp
  let initial := simulateQ (prssLocalAt prims (prssExtend S a))
    (early D pre A (prssExtend S a) parts)
  have hf := mean_mono_support initial (fun r hr => refresh_finish_le prims K circuits settings
    r.1.2.1 r.1.2.2.1 D A r.1.1 Z S normal parts hmem hsk hc a r.2 Q hni hn0
      (reference_tail_bound prims K circuits settings D pre A Z Q budget
        (prssHashAt prims (prssExtend S a)) normal parts r (by
          rw [early_hashAt]
          exact support_simulateQ_subset _ _ hr)))
  simp only [aimedMean_add, aimedMean_const] at hf
  have hmove {f : KeygenFresh C → (S → HashOutput) → (JointInput C × Early A) → ℝ≥0∞} :
      aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput))
        (fun echo => aimedMean initial (f u echo))) =
      aimedMean initial (fun r => aimedMean ($ᵗ (KeygenFresh C))
        (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo => f u echo r))) := by
    simp_rw [aimedMean_comm ($ᵗ (S → HashOutput)) initial]
    rw [aimedMean_comm]
  rw [hmove] at hp
  unfold finish at hp
  have hb := hp.trans (add_le_add hf le_rfl)
  unfold referenceError tailHit prefixHit
  unfold prefixHit at hb
  simp only [early_hashAt, aimed_prssLocalAt_hashAt]
  exact hb.trans_eq ((add_right_comm _ _ _).trans (add_assoc _ _ _))

theorem actual_total_le (S : Finset (Query C)) (normal : KeyName C → HashOutput)
    (hmem : ∀ parts n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts)) ≤
      (((3 * Q) *
        prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let cost : ℝ≥0∞ :=
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    ((Q : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256
  have hp (parts : C.Party → Parts C) :
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts) ≤
      (if KeygenClash D parts then 1 else 0) + (cost + aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        referenceError prims K circuits settings D pre A Z
          (prssHashAt prims (prssExtend S a)) normal parts)) := by
    by_cases hc : KeygenClash D parts
    · rw [if_pos hc]
      exact (aimedMean_le_const _ 1 _ (fun a => actualProbability_le_one prims K circuits settings
        D pre A Z _ parts)).trans (le_add_right le_rfl)
    · rw [if_neg hc, zero_add]
      exact parts_le prims K circuits settings D pre A Z Q budget S normal parts
        (hmem parts) hsk hc hni hn0
  have hb := aimedMean_mono (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) hp
  simp only [aimedMean_add, aimedMean_const, aimedMean_event] at hb
  have hc : Pr[KeygenClash D | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] ≤
      (keygenClashCount C : ℝ≥0∞) / 2 ^ 256 := by
    simpa only [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using probEvent_keygenClash_le D
  have he : aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a => referenceError prims K circuits settings
        D pre A Z (prssHashAt prims (prssExtend S a)) normal parts)) ≤
      ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [aimedMean_comm]
    exact aimedMean_le_const _ _ _ (fun a => reference_error_bound prims K circuits settings D pre A Z Q budget
      (prssHashAt prims (prssExtend S a)) normal)
  refine (hb.trans (add_le_add hc (add_le_add le_rfl he))).trans ?_
  dsimp only [cost]
  simp only [← ENNReal.add_div]
  gcongr
  norm_cast
  have hb := aimed_boundary_zero_error_arith (C := C)
  rw [keygenFinish_card_pair]
  nlinarith


/-- The aimed-call estimate needs only the complete reference-path budget.
Its three uses of `Q` protect prefix derivation inputs, tail derivation inputs,
and the hidden stream keys. -/
theorem flagProgram_bound_path :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true |
      (simulateQ (lazyKeyWorld prims D) (flagProgram K circuits settings D pre A Z)).run' (∅, ∅)] ≤
      ((3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  by_cases hm : prssKeyCount C < 2 ^ 256
  · obtain ⟨normal, hni, hn0⟩ := aimed_normalTable_exists D hm
    obtain ⟨cover, hcanonical, hecho⟩ := aimedCover_exists (C := C)
    obtain ⟨S, hS, he⟩ := flagProgram_eager_cover prims K circuits settings D pre A Z cover
    rw [probEvent_congr_evalDist he, eagerProbability_eq]
    exact actual_total_le prims K circuits settings D pre A Z Q budget S normal
      (fun parts n _ => hS (hcanonical parts n)) (fun i j f => hS (hecho i j f)) hni hn0
  · have hm' : 2 ^ 256 ≤ prssKeyCount C := Nat.le_of_not_gt hm
    have hn : 2 ^ 256 ≤ 3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 := by
      nlinarith [Nat.zero_le (3 * Q * prssKeyCount C)]
    calc
      _ ≤ 1 := probEvent_le_one
      _ = (2 ^ 256 : ℝ≥0∞) / 2 ^ 256 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast hn) _

omit budget in
/-- The selected ceremony's actual setup has the same path-budget hit estimate.
The prefix retains the selected metadata and adversary state together. -/
theorem joint_setupHit_bound_path
    (hQ : IsQueryBoundP (setupEarly D (remember D pre A) (do
      let input ← jointPrefix pre
      let state ← A.start (corruptInputs D input.1) input.2.2.2
      pure (input, state))) Counted Q) :
    Pr[fun r => KeyHit D (rowsOf r.1.2) r.2 | worldRun prims (setup D pre A)] ≤
      ((2 * Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [setup_eq_remember D pre A (dealtKeys 0 (fun _ => 0) (fun _ => 0)) []]
  exact setupHit_le prims D (remember D pre A) _ [] Q hQ

end Aimed
/-- info: 'ThresholdLeanXmssSecurity.LifetimePathCount.hashLog_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hashLog_residual

/-- info: 'ThresholdLeanXmssSecurity.LifetimePathCount.early_log_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms early_log_length

/-- info: 'ThresholdLeanXmssSecurity.LifetimePathCount.earlyCached_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms earlyCached_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimePathCount.joint_setupHit_bound_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_setupHit_bound_path

/-- info: 'ThresholdLeanXmssSecurity.LifetimePathCount.flagProgram_bound_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flagProgram_bound_path

end ThresholdLeanXmssSecurity.LifetimePathCount
