import ThresholdLeanXmssSecurity.Proof.SigningOpening

/-!
# The capped hit bound with a ledger

This module holds the form of `SigningCappedExpectProof.probEvent_capped_expect_le` whose count is
a ledger in a ghost state. The ledger reads the query, the state and the revealed secrets. So a
call can be charged in one state and free in another.

* `ledgerHybrid` is `revealImpl` with a write-only ghost state. The handler never reads the ghost.
* `ledgerPotential` is the flag plus `f` while the ledger is within the budget `B`, and zero above.
* `expectedFinal_ledger_flag_le` shows that a raised flag adds at most one to the expected
  potential, and nothing above the budget.
* `expectedFinal_ledger_le_aux` bounds the averaged expected potential by
  `f + (B - ledger g) / |T|`.
* `probEvent_ledger_expect_le` bounds the flag or `E`, with the ledger within `B`, by `B / |T|`.

The proofs copy those of `SigningCappedExpectProof.expectedFinal_flag_le`,
`SigningCappedExpectProof.expectedFinal_capped_le_aux` and
`SigningCappedExpectProof.probEvent_capped_expect_le`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningLedgerExpect

open SigningOpeningProof

section Ledger

attribute [local instance] Classical.propDecidable

variable {κ σ β K T G : Type} {spec : OracleSpec κ}
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T] [SampleableType (K → T)]
  (impl : QueryImpl spec (StateT σ ProbComp)) (counted : κ → σ → Prop) (inputSide : κ → Prop)
  (keyOf : κ → K) (point : κ → T) (aux : κ → σ × (K → Option T) → G → G)

/-- The hybrid of `revealImpl` with a write-only ghost state. At a backend call the ghost reads the
query, the backend state and the revealed secrets before the call. A reveal keeps the ghost. -/
def ledgerHybrid (s : K → T) :
    QueryImpl (spec + RevealSpec K T) (StateT ((σ × (K → Option T) × Bool) × G) ProbComp) :=
  QueryImpl.extendState (revealImpl impl counted inputSide (fun _ _ _ => False) keyOf point s)
    fun t st _ _ g => match t with
      | .inl t => aux t (st.1, st.2.1) g
      | .inr _ => g

/-- The potential of the ledger hybrid. It is one when the flag is up, plus `f`, while the ledger
is within the budget `B`. It is zero above the budget. -/
def ledgerPotential (ledger : G → ℕ) (B : ℕ) (f : σ × G → ℝ≥0∞)
    (st : (σ × (K → Option T) × Bool) × G) : ℝ≥0∞ :=
  if ledger st.2 ≤ B then (if st.1.2.2 = true then 1 else 0) + f (st.1.1, st.2) else 0

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A backend call of the ledger hybrid. -/
theorem ledgerHybrid_inl_run (s : K → T) (t : κ)
    (k : spec t → OracleComp (spec + RevealSpec K T) β) (σ₀ : σ) (stored : K → Option T)
    (b : Bool) (g : G) :
    (simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s)
        (liftM ((spec + RevealSpec K T).query (.inl t)) >>= k)).run ((σ₀, stored, b), g) =
      (impl t).run σ₀ >>= fun x =>
        (simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s) (k x.1)).run
          ((x.2, stored, b || decide (counted t σ₀ ∧ inputSide t ∧
            stored (keyOf t) = none ∧ s (keyOf t) = point t)), aux t (σ₀, stored) g) := by
  simp [ledgerHybrid, QueryImpl.extendState, revealImpl, StateT.run_mk]

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A reveal of the ledger hybrid. -/
theorem ledgerHybrid_inr_run (s : K → T) (key : K) (k : T → OracleComp (spec + RevealSpec K T) β)
    (σ₀ : σ) (stored : K → Option T) (b : Bool) (g : G) :
    (simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s)
        (liftM ((spec + RevealSpec K T).query (.inr key)) >>= k)).run ((σ₀, stored, b), g) =
      (simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s)
          (k ((stored key).getD (s key)))).run
        ((σ₀, Function.update stored key (some ((stored key).getD (s key))), b), g) := by
  simp [ledgerHybrid, QueryImpl.extendState, revealImpl, StateT.run_mk]

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A run reads the secrets only at keys that are not revealed yet. -/
theorem ledgerHybrid_run_congr (s s' : K → T) (oa : OracleComp (spec + RevealSpec K T) β) :
    ∀ (σ₀ : σ) (stored : K → Option T) (b : Bool) (g : G), (∀ k, stored k = none → s k = s' k) →
      (simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s) oa).run
          ((σ₀, stored, b), g) =
        (simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s') oa).run
          ((σ₀, stored, b), g) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; simp
  | query_bind t k ih =>
    intro σ₀ stored b g hs
    rcases t with t | key
    · rw [ledgerHybrid_inl_run, ledgerHybrid_inl_run]
      refine bind_congr fun x => ?_
      have hflag : decide (counted t σ₀ ∧ inputSide t ∧ stored (keyOf t) = none ∧
            s (keyOf t) = point t) =
          decide (counted t σ₀ ∧ inputSide t ∧ stored (keyOf t) = none ∧
            s' (keyOf t) = point t) := by
        by_cases h : stored (keyOf t) = none
        · rw [hs _ h]
        · simp [h]
      rw [hflag]
      exact ih x.1 _ _ _ _ hs
    · rw [ledgerHybrid_inr_run, ledgerHybrid_inr_run]
      have hv : (stored key).getD (s key) = (stored key).getD (s' key) := by
        cases h : stored key with
        | none => simp [hs _ h]
        | some v => simp
      rw [hv]
      refine ih _ _ _ _ _ fun k' hk' => hs k' ?_
      by_cases hk : k' = key
      · subst hk; simp at hk'
      · simpa [Function.update_of_ne hk] using hk'

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A raised flag adds at most one to the expected potential, and nothing above the budget. The
handler never reads the flag, and the ledger never falls. -/
theorem expectedFinal_ledger_flag_le (charged : κ → σ × (K → Option T) → G → Prop)
    (ledger : G → ℕ) (B : ℕ) (f : σ × G → ℝ≥0∞)
    (hledger : ∀ t st g, ledger (aux t st g) = ledger g + if charged t st g then 1 else 0)
    (s : K → T) (oa : OracleComp (spec + RevealSpec K T) β) :
    ∀ (σ₀ : σ) (stored : K → Option T) (b : Bool) (g : G),
      XmssSecurity.expectedFinal (ledgerHybrid impl counted inputSide keyOf point aux s)
          (ledgerPotential ledger B f) oa ((σ₀, stored, true), g) ≤
        (if ledger g ≤ B then 1 else 0) + XmssSecurity.expectedFinal
          (ledgerHybrid impl counted inputSide keyOf point aux s) (ledgerPotential ledger B f) oa
          ((σ₀, stored, b), g) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro σ₀ stored b g
    simp only [XmssSecurity.expectedFinal_pure, ledgerPotential]
    split_ifs <;> simp
  | query_bind t k ih =>
    intro σ₀ stored b g
    simp only [XmssSecurity.expectedFinal] at ih ⊢
    rcases t with t | key
    · rw [ledgerHybrid_inl_run, ledgerHybrid_inl_run, OracleComp.tsum_prEvent_bind_mul,
        OracleComp.tsum_prEvent_bind_mul]
      simp only [Bool.true_or]
      generalize (b || decide (counted t σ₀ ∧ inputSide t ∧
        stored (keyOf t) = none ∧ s (keyOf t) = point t)) = b'
      have hc : (if ledger (aux t (σ₀, stored) g) ≤ B then (1 : ℝ≥0∞) else 0) ≤
          if ledger g ≤ B then 1 else 0 := by
        rw [hledger]
        split_ifs <;> simp <;> omega
      have hle := fun x : spec t × σ => (ih x.1 x.2 stored b' (aux t (σ₀, stored) g)).trans
        (add_le_add_left hc _)
      refine (tsum_le_tsum fun x => mul_le_mul_right (hle x) _).trans ?_
      simp only [mul_add, tsum_add]
      gcongr
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
    · rw [ledgerHybrid_inr_run, ledgerHybrid_inr_run]
      exact ih _ _ _ _ _

/-- The ledger form of `SigningCappedExpectProof.expectedFinal_capped_le_aux`. The averaged
expected potential is at most `f + (B - ledger g) / |T|`. -/
theorem expectedFinal_ledger_le_aux (charged : κ → σ × (K → Option T) → G → Prop)
    (ledger : G → ℕ) (B : ℕ) (Inv : σ × G → Prop) (f : σ × G → ℝ≥0∞)
    (hledger : ∀ t st g, ledger (aux t st g) = ledger g + if charged t st g then 1 else 0)
    (hflag : ∀ t st stored g, counted t st → inputSide t → stored (keyOf t) = none →
      charged t (st, stored) g)
    (hinv : ∀ t st stored g, Inv (st, g) →
      ∀ x ∈ support ((impl t).run st), Inv (x.2, aux t (st, stored) g))
    (hstep : ∀ t st stored g, Inv (st, g) →
      ∑' x, Pr{let z ← (impl t).run st}[z = x] * f (x.2, aux t (st, stored) g) ≤
        f (st, g) + if charged t (st, stored) g ∧ ledger g < B ∧
            ¬(inputSide t ∧ stored (keyOf t) = none) then (Fintype.card T : ℝ≥0∞)⁻¹ else 0)
    (oa : OracleComp (spec + RevealSpec K T) β) :
    ∀ (σ₀ : σ) (stored : K → Option T) (g : G), Inv (σ₀, g) →
      ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * XmssSecurity.expectedFinal
          (ledgerHybrid impl counted inputSide keyOf point aux s) (ledgerPotential ledger B f) oa
          ((σ₀, stored, false), g) ≤
        f (σ₀, g) + (B - ledger g : ℕ) * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro σ₀ stored g _
    simp only [XmssSecurity.expectedFinal_pure]
    rw [ENNReal.tsum_mul_right]
    refine (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)).trans (le_trans ?_ le_self_add)
    simp only [ledgerPotential, Bool.false_eq_true, ite_false, zero_add]
    split_ifs <;> simp
  | query_bind t k ih =>
    intro σ₀ stored g hst
    set ε : ℝ≥0∞ := (Fintype.card T : ℝ≥0∞)⁻¹
    rcases t with t | key
    · set I := fun s => ledgerHybrid impl counted inputSide keyOf point aux s
      set Φ := ledgerPotential (K := K) (T := T) ledger B f
      set mx := (impl t).run σ₀
      set g' := aux t (σ₀, stored) g
      set P : (K → T) → Prop := fun s => counted t σ₀ ∧ inputSide t ∧
        stored (keyOf t) = none ∧ s (keyOf t) = point t with hPdef
      set G' : (K → T) → spec t × σ → Bool → ℝ≥0∞ := fun s x b =>
        XmssSecurity.expectedFinal (I s) Φ (k x.1) ((x.2, stored, b), g') with hGdef
      set c : ℝ≥0∞ := if ledger g' ≤ B then 1 else 0 with hc
      set A : ℝ≥0∞ := if counted t σ₀ ∧ inputSide t ∧ stored (keyOf t) = none then c * ε else 0
        with hA
      set D : ℝ≥0∞ := if charged t (σ₀, stored) g ∧ ledger g < B ∧
        ¬(inputSide t ∧ stored (keyOf t) = none) then ε else 0 with hD
      have hrun : ∀ s, XmssSecurity.expectedFinal (I s) Φ
          (liftM ((spec + RevealSpec K T).query (.inl t)) >>= k) ((σ₀, stored, false), g) =
          ∑' x, Pr{let z ← mx}[z = x] * G' s x (decide (P s)) := by
        intro s
        simp only [XmssSecurity.expectedFinal, I, hGdef]
        rw [ledgerHybrid_inl_run, OracleComp.tsum_prEvent_bind_mul]
        simp only [Bool.false_or, hPdef]
        rfl
      have hflagle : ∀ s x, G' s x (decide (P s)) ≤ (if P s then c else 0) + G' s x false := by
        intro s x
        by_cases h : P s
        · simp only [h, decide_true, ite_true, hGdef]
          exact expectedFinal_ledger_flag_le impl counted inputSide keyOf point aux charged ledger B
            f hledger s (k x.1) x.2 stored false g'
        · simp [h]
      have hhit : ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * (if P s then c else 0) ≤ A := by
        by_cases hc' : counted t σ₀ ∧ inputSide t ∧ stored (keyOf t) = none
        · rw [hA, ite_eq_left hc']
          calc _ = ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * (if P s then 1 else 0) * c := by
                refine tsum_congr fun s => ?_
                split_ifs <;> simp
            _ = c * ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * (if P s then 1 else 0) := by
                rw [ENNReal.tsum_mul_right, mul_comm]
            _ ≤ c * ε := by
                gcongr
                simp only [mul_ite, mul_one, mul_zero]
                rw [← OracleComp.prEvent_eq_tsum_ite]
                exact (prEvent_mono_of_support _ _ _ fun s _ h => h.2.2.2).trans
                  (le_of_eq (probEvent_uniform_key_eq (keyOf t) (point t)))
        · rw [hA, ite_eq_right hc']
          have : ∀ s, ¬P s := fun s h => hc' ⟨h.1, h.2.1, h.2.2.1⟩
          simp [this]
      have hcont : ∑' x, Pr{let z ← mx}[z = x] * ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * G' s x false ≤
          f (σ₀, g) + D + (B - ledger g' : ℕ) * ε := by
        calc _ ≤ ∑' x, Pr{let z ← mx}[z = x] * (f (x.2, g') + (B - ledger g' : ℕ) * ε) := by
              refine tsum_le_tsum fun x => ?_
              by_cases hx : x ∈ support mx
              · gcongr
                exact ih x.1 x.2 stored g' (hinv t σ₀ stored g hst x hx)
              · simp [prEvent_eq_zero_of_not_mem_support _ hx]
          _ = ∑' x, Pr{let z ← mx}[z = x] * f (x.2, g') +
              ∑' x, Pr{let z ← mx}[z = x] * ((B - ledger g' : ℕ) * ε) := by
              simp only [mul_add, tsum_add]
          _ ≤ _ := by
              refine add_le_add (hstep t σ₀ stored g hst) ?_
              rw [ENNReal.tsum_mul_right]
              exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
      have hsum : A + D + (B - ledger g' : ℕ) * ε ≤ (B - ledger g : ℕ) * ε := by
        have hl' : ledger g' = ledger g + if charged t (σ₀, stored) g then 1 else 0 :=
          hledger _ _ _
        by_cases hch : charged t (σ₀, stored) g
        · rw [ite_eq_left hch] at hl'
          by_cases hlB : ledger g < B
          · have hc1 : c = 1 := by rw [hc, ite_eq_left (by omega)]
            have hAD : A + D ≤ ε := by
              rw [hA, hD, hc1, one_mul]
              split_ifs with h1 h2 h2
              · exact absurd h1.2 h2.2.2
              all_goals simp
            calc _ ≤ ε + (B - ledger g' : ℕ) * ε := by gcongr
              _ = (B - ledger g : ℕ) * ε := by
                  rw [← one_add_mul]
                  congr 1
                  rw [hl']
                  exact_mod_cast (by omega : 1 + (B - (ledger g + 1)) = B - ledger g)
          · have hc0 : c = 0 := by rw [hc, ite_eq_right (by omega)]
            rw [hA, hD, hc0, zero_mul, ite_self,
              ite_eq_right (fun h : _ ∧ ledger g < B ∧ _ => hlB h.2.1), hl', add_zero, zero_add]
            gcongr
            omega
        · rw [ite_eq_right hch, add_zero] at hl'
          rw [hA, hD, ite_eq_right (fun h => hch (hflag t σ₀ stored g h.1 h.2.1 h.2.2)),
            ite_eq_right (fun h => hch h.1), hl']
          simp
      calc _ = ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * ∑' x, Pr{let z ← mx}[z = x] * G' s x (decide (P s)) := by
            exact tsum_congr fun s => congrArg _ (hrun s)
        _ ≤ ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * ∑' x, Pr{let z ← mx}[z = x] *
            ((if P s then c else 0) + G' s x false) := by
            gcongr with s x
            exact hflagle s x
        _ ≤ ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * (if P s then c else 0) +
            ∑' x, Pr{let z ← mx}[z = x] * ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * G' s x false := by
            simp only [mul_add, tsum_add]
            refine add_le_add ?_ (le_of_eq ?_)
            · gcongr with s
              rw [ENNReal.tsum_mul_right]
              exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
            · simp only [← ENNReal.tsum_mul_left]
              rw [tsum_comm]
              simp only [mul_left_comm]
        _ ≤ A + (f (σ₀, g) + D + (B - ledger g' : ℕ) * ε) := add_le_add hhit hcont
        _ = f (σ₀, g) + (A + D + (B - ledger g' : ℕ) * ε) := by ring
        _ ≤ f (σ₀, g) + (B - ledger g : ℕ) * ε := by gcongr
    · simp only [XmssSecurity.expectedFinal] at ih ⊢
      cases hstored : stored key with
      | some v =>
        simp only [ledgerHybrid_inr_run, hstored, Option.getD_some]
        exact ih v σ₀ _ g hst
      | none =>
        simp only [ledgerHybrid_inr_run, hstored, Option.getD_none]
        set H : T → (K → T) → ℝ≥0∞ := fun v s => ∑' r, Pr{let z ←
          ((simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s) (k v)).run
            ((σ₀, Function.update stored key (some v), false), g))}[z = r] *
              ledgerPotential ledger B f r.2 with hHdef
        have hH : ∀ v s w, H v (Function.update s key w) = H v s := by
          intro v s w
          simp only [hHdef]
          rw [ledgerHybrid_run_congr impl counted inputSide keyOf point aux
            (Function.update s key w) s (k v) σ₀ _ false g]
          intro k' hk'
          have hne : k' ≠ key := by
            rintro rfl
            simp at hk'
          exact Function.update_of_ne hne _ _
        have hih : ∀ v, ∑ s, Pr{let z ← $ᵗ (K → T)}[z = s] * H v s ≤
            f (σ₀, g) + (B - ledger g : ℕ) * ε := by
          intro v
          have := ih v σ₀ (Function.update stored key (some v)) g hst
          rwa [tsum_fintype] at this
        rw [tsum_fintype]
        exact sum_uniform_reveal_le key H _ hH hih

/-- The expectation form of the capped hit bound with a ledger in place of the count. A call is
charged by a predicate on the query, the state and the revealed secrets. Each call that can raise
the flag is charged. The potential rises by at most `1 / |T|` at a charged call below the budget `B`
that cannot raise the flag, and it does not rise at another call. Then the flag or `E`, with the
ledger within `B`, has probability at most `B / |T|`. -/
theorem probEvent_ledger_expect_le (charged : κ → σ × (K → Option T) → G → Prop) (ledger : G → ℕ)
    (B : ℕ) (Inv : σ × G → Prop) (f : σ × G → ℝ≥0∞)
    (hledger : ∀ t st g, ledger (aux t st g) = ledger g + if charged t st g then 1 else 0)
    (hflag : ∀ t st stored g, counted t st → inputSide t → stored (keyOf t) = none →
      charged t (st, stored) g)
    (hinv : ∀ t st stored g, Inv (st, g) →
      ∀ x ∈ support ((impl t).run st), Inv (x.2, aux t (st, stored) g))
    (hstep : ∀ t st stored g, Inv (st, g) →
      ∑' x, Pr{let z ← (impl t).run st}[z = x] * f (x.2, aux t (st, stored) g) ≤
        f (st, g) + if charged t (st, stored) g ∧ ledger g < B ∧
            ¬(inputSide t ∧ stored (keyOf t) = none) then (Fintype.card T : ℝ≥0∞)⁻¹ else 0)
    (E : σ × G → Prop) (hE : ∀ st g, E (st, g) → ledger g ≤ B → 1 ≤ f (st, g))
    (oa : OracleComp (spec + RevealSpec K T) β) (σ₀ : σ) (g₀ : G) (hσ₀ : Inv (σ₀, g₀))
    (hf₀ : f (σ₀, g₀) = 0) (hl₀ : ledger g₀ = 0) :
    Pr{let r ←
      ($ᵗ (K → T) >>= fun s =>
        (simulateQ (ledgerHybrid impl counted inputSide keyOf point aux s) oa).run
          ((σ₀, fun _ => none, false), g₀))}[(r.2.1.2.2 = true ∨ E (r.2.1.1, r.2.2)) ∧ ledger r.2.2 ≤ B] ≤ B * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have hΦ : ∀ st : (σ × (K → Option T) × Bool) × G,
      ((st.1.2.2 = true ∨ E (st.1.1, st.2)) ∧ ledger st.2 ≤ B) →
        1 ≤ ledgerPotential ledger B f st := by
    rintro st ⟨h | h, hB⟩
    · simp [ledgerPotential, h, hB]
    · rw [ledgerPotential, ite_eq_left hB]
      exact (hE _ _ h hB).trans le_add_self
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc _ ≤ ∑' s, Pr{let z ← $ᵗ (K → T)}[z = s] * XmssSecurity.expectedFinal
        (ledgerHybrid impl counted inputSide keyOf point aux s) (ledgerPotential ledger B f) oa
        ((σ₀, fun _ => none, false), g₀) := by
        refine tsum_le_tsum fun s => ?_
        gcongr
        simpa using XmssSecurity.const_mul_probEvent_le_expectedFinal _ (ledgerPotential ledger B f)
          (fun st => (st.1.2.2 = true ∨ E (st.1.1, st.2)) ∧ ledger st.2 ≤ B) 1 hΦ oa _
    _ ≤ f (σ₀, g₀) + (B - ledger g₀ : ℕ) * (Fintype.card T : ℝ≥0∞)⁻¹ :=
        expectedFinal_ledger_le_aux impl counted inputSide keyOf point aux charged ledger B Inv f
          hledger hflag hinv hstep oa _ _ _ hσ₀
    _ = _ := by simp [hf₀, hl₀]

end Ledger

end SigningLedgerExpect

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningLedgerExpect.ledgerHybrid_inl_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLedgerExpect.ledgerHybrid_inl_run

/-- info: 'ThresholdLeanXmssSecurity.SigningLedgerExpect.ledgerHybrid_inr_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLedgerExpect.ledgerHybrid_inr_run

/-- info: 'ThresholdLeanXmssSecurity.SigningLedgerExpect.ledgerHybrid_run_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLedgerExpect.ledgerHybrid_run_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningLedgerExpect.expectedFinal_ledger_flag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLedgerExpect.expectedFinal_ledger_flag_le

/-- info: 'ThresholdLeanXmssSecurity.SigningLedgerExpect.expectedFinal_ledger_le_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLedgerExpect.expectedFinal_ledger_le_aux

/-- info: 'ThresholdLeanXmssSecurity.SigningLedgerExpect.probEvent_ledger_expect_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLedgerExpect.probEvent_ledger_expect_le
