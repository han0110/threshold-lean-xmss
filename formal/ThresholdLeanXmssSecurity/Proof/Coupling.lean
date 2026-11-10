import ThresholdLeanXmssSecurity.Proof.Execution
import VCVio.ProgramLogic.Relational.Basic

/-!
# Round-by-round couplings of executions

Generic tools for game hops over `executeRounds` against an arbitrary rushing adversary.

* Couplings up to a bad event bound the gap of two acceptance probabilities by the bad probability
  (`abs_probEvent_sub_le_of_relTriple`).
* Lockstep: two runs of `executeRounds` related round by round, up to a sticky bad event on the left
  handler state (`relTriple_executeRounds`), exactly (`evalDist_executeRounds_eq`), and in the world
  for every distinguisher (`abs_accepts_lockstep_sub_le`, `abs_accepts_distinguish_sub_le`).
  A handler moves into the roles with `simulateQ_executeRounds` and `simulateQ_executePhase`.
* Shift: a uniform mask shifted by a value fixed before the mask is drawn couples with the mask
  (`relTriple_uniform_shift`, `relTriple_run_uniform_shift`, `evalDist_uniform_shift`).
* Hit: `q` counted calls hit one of `k` secret uniform points that the handler never reads with
  probability at most `q * k / |P|` (`probEvent_hit_uniform_le`), so `q * k / 2 ^ 256` for hash outputs
  and for the whole real execution of a `q`-query adversary (`probEvent_hit_realExecution_le`).
  The secrets must be independent of the run, as in a hybrid where they are not used yet.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Couplings up to bad -/

section UpToBad

variable {α β : Type}

/-- A coupling whose pairs are bad on the left or agree on the two events bounds the gap of the two
events by the bad probability. -/
theorem abs_probEvent_sub_le_of_relTriple {oa : ProbComp α} {ob : ProbComp β} (Bad P : α → Prop)
    (Q : β → Prop) (h : RelTriple oa ob fun a b => Bad a ∨ (P a ↔ Q b)) :
    |Pr[P | oa].toReal - Pr[Q | ob].toReal| ≤ Pr[Bad | oa].toReal := by
  have h1 : Pr[fun a => P a ∧ ¬ Bad a | oa] ≤ Pr[Q | ob] :=
    probEvent_le_of_relTriple h fun a b hab hp => (hab.resolve_left hp.2).1 hp.1
  have h2 : Pr[Q | ob] ≤ Pr[fun a => P a ∨ Bad a | oa] :=
    probEvent_le_of_relTriple (relTriple_symm h) fun b a hab hq => by
      rcases hab with hb | hb
      · exact Or.inr hb
      · exact Or.inl (hb.2 hq)
  have h3 : Pr[P | oa] ≤ Pr[fun a => P a ∧ ¬ Bad a | oa] + Pr[Bad | oa] :=
    le_trans (probEvent_mono fun a _ ha => by
      by_cases hb : Bad a
      · exact Or.inr hb
      · exact Or.inl ⟨ha, hb⟩) (probEvent_or_le oa _ Bad)
  have h4 : Pr[fun a => P a ∨ Bad a | oa] ≤ Pr[P | oa] + Pr[Bad | oa] := probEvent_or_le oa _ _
  have t1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
    (h3.trans (add_le_add h1 le_rfl))
  have t2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) (h2.trans h4)
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at t1 t2
  rw [abs_le]
  constructor <;> linarith

/-- A postcondition that holds for every left output and every right value holds on a coupling. -/
theorem relTriple_of_support_left {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    (h : ∀ a ∈ support oa, ∀ b, R a b) : RelTriple oa ob R := by
  obtain ⟨c, -⟩ := relTriple_iff_relWP.1 (relTriple_true oa ob)
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => h z.1 ?_ z.2⟩
  have hz' : z.1 ∈ support (Prod.fst <$> c.1) := by rw [support_map]; exact ⟨z, hz, rfl⟩
  rw [c.2.map_fst] at hz'
  exact (mem_support_evalDist_iff _ _).1 hz'

end UpToBad

/-! ## Lockstep runs of `executeRounds` -/

section Lockstep

variable {E : Type}

/-- Every honest operator of a step vector has stopped. -/
def AllDone {ι α : Type} {G : OracleSpec ι} (D : C.Coalition) (steps : C.Party → Step C E G α) : Prop :=
  ∀ i, i ∉ D.1 → (steps i).isDone

/-- One more step of fuel stops when every honest operator stopped, and otherwise runs one round. -/
theorem executeRounds_succ {m : Type → Type} [Monad m] {Ia I O L R α : Type} (Ro : Roles C m)
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    executeRounds Ro D A F (fuel + 1) state steps =
      if AllDone D steps then pure (state, fun i => (steps i).output) else
        stepRound Ro D A F state steps >>= fun p => executeRounds Ro D A F fuel p.1 p.2.1 := by
  simp only [executeRounds, AllDone]; congr

variable {σ₁ σ₂ Ia₁ Ia₂ I₁ I₂ O₁ O₂ L₁ L₂ R₁ R₂ α₁ α₂ : Type}
  (Ro₁ : Roles C (StateT σ₁ ProbComp)) (Ro₂ : Roles C (StateT σ₂ ProbComp))
  (D₁ D₂ : C.Coalition) (A₁ : Adversary C E Ia₁ L₁ R₁) (A₂ : Adversary C E Ia₂ L₂ R₂)
  (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂)

/-- A sticky bad event on the left handler state survives the remaining rounds. -/
theorem executeRounds_sticky (Bad : σ₁ → Prop)
    (hsticky : ∀ st (steps : C.Party → Step C E (CallSpec I₁ O₁) α₁) s, Bad s → ∀ x ∈ support ((stepRound Ro₁ D₁ A₁ F₁ st steps).run s), Bad x.2) :
    ∀ (fuel : ℕ) (st : A₁.State) (steps : C.Party → Step C E (CallSpec I₁ O₁) α₁) (s : σ₁), Bad s →
      ∀ x ∈ support ((executeRounds Ro₁ D₁ A₁ F₁ fuel st steps).run s), Bad x.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro st steps s hs x hx
    simp only [executeRounds, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hs
  | succ fuel ih =>
    intro st steps s hs x hx
    rw [executeRounds_succ] at hx
    split_ifs at hx
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hs
    · rw [StateT.run_bind, support_bind] at hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨p, hp, hx⟩ := hx
      exact ih _ _ _ (hsticky st steps s hs p hp) x hx

/-- Lockstep up to bad. Two runs of `executeRounds`, with any roles, coalitions, adversaries and
functionalities on `StateT` handlers, whose related configurations stop together, end related, and
step to related configurations unless the sticky left bad event fires, end related unless bad. -/
theorem relTriple_executeRounds (Bad : σ₁ → Prop)
    (R : (A₁.State × (C.Party → Step C E (CallSpec I₁ O₁) α₁)) × σ₁ →
      (A₂.State × (C.Party → Step C E (CallSpec I₂ O₂) α₂)) × σ₂ → Prop)
    (Q : (A₁.State × (C.Party → Option α₁)) × σ₁ → (A₂.State × (C.Party → Option α₂)) × σ₂ → Prop)
    (hsticky : ∀ st (steps : C.Party → Step C E (CallSpec I₁ O₁) α₁) s, Bad s →
      ∀ x ∈ support ((stepRound Ro₁ D₁ A₁ F₁ st steps).run s), Bad x.2)
    (hdone : ∀ c₁ c₂, R c₁ c₂ → ¬ Bad c₁.2 → (AllDone D₁ c₁.1.2 ↔ AllDone D₂ c₂.1.2))
    (hout : ∀ c₁ c₂, R c₁ c₂ → ¬ Bad c₁.2 →
      Q ((c₁.1.1, fun i => (c₁.1.2 i).output), c₁.2) ((c₂.1.1, fun i => (c₂.1.2 i).output), c₂.2))
    (hstep : ∀ c₁ c₂, R c₁ c₂ → ¬ Bad c₁.2 → ¬ AllDone D₁ c₁.1.2 →
      RelTriple ((stepRound Ro₁ D₁ A₁ F₁ c₁.1.1 c₁.1.2).run c₁.2)
        ((stepRound Ro₂ D₂ A₂ F₂ c₂.1.1 c₂.1.2).run c₂.2)
        fun x y => Bad x.2 ∨ R ((x.1.1, x.1.2.1), x.2) ((y.1.1, y.1.2.1), y.2)) :
    ∀ fuel c₁ c₂, Bad c₁.2 ∨ R c₁ c₂ →
      RelTriple ((executeRounds Ro₁ D₁ A₁ F₁ fuel c₁.1.1 c₁.1.2).run c₁.2)
        ((executeRounds Ro₂ D₂ A₂ F₂ fuel c₂.1.1 c₂.1.2).run c₂.2) fun x y => Bad x.2 ∨ Q x y := by
  intro fuel
  induction fuel with
  | zero =>
    intro c₁ c₂ hc
    by_cases hb : Bad c₁.2
    · exact relTriple_of_support_left fun x hx _ =>
        Or.inl (executeRounds_sticky Ro₁ D₁ A₁ F₁ Bad hsticky 0 _ _ _ hb x hx)
    · simp only [executeRounds, StateT.run_pure]
      exact relTriple_pure_pure (Or.inr (hout c₁ c₂ (hc.resolve_left hb) hb))
  | succ fuel ih =>
    intro c₁ c₂ hc
    by_cases hb : Bad c₁.2
    · exact relTriple_of_support_left fun x hx _ =>
        Or.inl (executeRounds_sticky Ro₁ D₁ A₁ F₁ Bad hsticky _ _ _ _ hb x hx)
    have hR := hc.resolve_left hb
    rw [executeRounds_succ, executeRounds_succ]
    by_cases hd : AllDone D₁ c₁.1.2
    · rw [if_pos hd, if_pos ((hdone c₁ c₂ hR hb).1 hd)]
      simp only [StateT.run_pure]
      exact relTriple_pure_pure (Or.inr (hout c₁ c₂ hR hb))
    · rw [if_neg hd, if_neg (fun h => hd ((hdone c₁ c₂ hR hb).2 h)), StateT.run_bind, StateT.run_bind]
      exact relTriple_bind (hstep c₁ c₂ hR hb hd) fun x y hxy =>
        ih ((x.1.1, x.1.2.1), x.2) ((y.1.1, y.1.2.1), y.2) hxy

/-- Exact lockstep. Two runs of `executeRounds` whose related configurations stop together, show the
same view, and step to related configurations, show the same distribution of the view. -/
theorem evalDist_executeRounds_eq {V : Type}
    (R : (A₁.State × (C.Party → Step C E (CallSpec I₁ O₁) α₁)) × σ₁ →
      (A₂.State × (C.Party → Step C E (CallSpec I₂ O₂) α₂)) × σ₂ → Prop)
    (view₁ : (A₁.State × (C.Party → Option α₁)) × σ₁ → V) (view₂ : (A₂.State × (C.Party → Option α₂)) × σ₂ → V)
    (hdone : ∀ c₁ c₂, R c₁ c₂ → (AllDone D₁ c₁.1.2 ↔ AllDone D₂ c₂.1.2))
    (hout : ∀ c₁ c₂, R c₁ c₂ →
      view₁ ((c₁.1.1, fun i => (c₁.1.2 i).output), c₁.2) = view₂ ((c₂.1.1, fun i => (c₂.1.2 i).output), c₂.2))
    (hstep : ∀ c₁ c₂, R c₁ c₂ → ¬ AllDone D₁ c₁.1.2 →
      RelTriple ((stepRound Ro₁ D₁ A₁ F₁ c₁.1.1 c₁.1.2).run c₁.2)
        ((stepRound Ro₂ D₂ A₂ F₂ c₂.1.1 c₂.1.2).run c₂.2)
        fun x y => R ((x.1.1, x.1.2.1), x.2) ((y.1.1, y.1.2.1), y.2))
    (fuel : ℕ) (c₁ c₂) (hc : R c₁ c₂) :
    𝒟[view₁ <$> (executeRounds Ro₁ D₁ A₁ F₁ fuel c₁.1.1 c₁.1.2).run c₁.2] =
      𝒟[view₂ <$> (executeRounds Ro₂ D₂ A₂ F₂ fuel c₂.1.1 c₂.1.2).run c₂.2] := by
  refine evalDist_map_eq_of_relTriple (relTriple_post_mono (relTriple_executeRounds Ro₁ Ro₂ D₁ D₂ A₁ A₂ F₁ F₂
    (fun _ => False) R (fun a b => view₁ a = view₂ b) (fun _ _ _ h => h.elim) (fun c₁ c₂ h _ => hdone c₁ c₂ h)
    (fun c₁ c₂ h _ => hout c₁ c₂ h) (fun c₁ c₂ h _ hd => relTriple_post_mono (hstep c₁ c₂ h hd) fun _ _ => Or.inr)
    fuel c₁ c₂ (Or.inr hc)) fun _ _ h => h.resolve_left id)

end Lockstep

/-! ## Shifted masks -/

section Shift

variable {M γ δ : Type} [AddGroup M] [SampleableType M]

/-- A uniform mask on the right shifted by a value `v` fixed before it is drawn couples with the
unshifted mask on the left. -/
theorem relTriple_uniform_shift (v : M) {f : M → ProbComp γ} {g : M → ProbComp δ} {S : γ → δ → Prop}
    (h : ∀ r, RelTriple (f r) (g (r + v)) S) : RelTriple ($ᵗ M >>= f) ($ᵗ M >>= g) S :=
  relTriple_bind_uniformSample_bij (f := fun r => r + v) h (Equiv.addRight v).bijective

/-- A uniform mask shifted by a value fixed before it is drawn has the distribution of the mask. -/
theorem evalDist_uniform_shift (v : M) (k : M → ProbComp γ) :
    𝒟[$ᵗ M >>= fun r => k (r + v)] = 𝒟[$ᵗ M >>= k] :=
  evalDist_eq_of_relTriple_eqRel (relTriple_uniform_shift v fun r => relTriple_refl (k (r + v)))

/-- The shift on a handler state: after a uniform mask drawn by `StateT`, continuations related at
the mask and the mask shifted by `v` give related runs. -/
theorem relTriple_run_uniform_shift {σ₁ σ₂ : Type} (v : M) (k₁ : M → StateT σ₁ ProbComp γ)
    (k₂ : M → StateT σ₂ ProbComp δ) (s₁ : σ₁) (s₂ : σ₂) {S : γ × σ₁ → δ × σ₂ → Prop}
    (h : ∀ r, RelTriple ((k₁ r).run s₁) ((k₂ (r + v)).run s₂) S) :
    RelTriple ((liftM ($ᵗ M) >>= k₁ : StateT σ₁ ProbComp γ).run s₁)
      ((liftM ($ᵗ M) >>= k₂ : StateT σ₂ ProbComp δ).run s₂) S := by
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
  exact relTriple_uniform_shift v h

end Shift

/-! ## Hitting a hidden secret -/

section Hit

open ENNReal

variable {κ σ S β : Type} {spec : OracleSpec κ}

/-- The handler `impl` with a flag that records whether a call `t` hit the secret `s`. -/
def flagImpl (impl : QueryImpl spec (StateT σ ProbComp)) (hit : κ → S → Prop) (s : S) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) := fun t =>
  StateT.mk fun p => (fun x => (x.1, (x.2, p.2 || decide (hit t s)))) <$> (impl t).run p.1

/-- A flagged call raises the flag exactly when it hits the secret. -/
theorem flagImpl_query_bind_run (impl : QueryImpl spec (StateT σ ProbComp)) (hit : κ → S → Prop) (s : S)
    (t : κ) (k : spec t → OracleComp spec β) (σ₀ : σ) :
    (simulateQ (flagImpl impl hit s) (liftM (spec.query t) >>= k)).run (σ₀, false) =
      (impl t).run σ₀ >>= fun x => (simulateQ (flagImpl impl hit s) (k x.1)).run (x.2, decide (hit t s)) := by
  simp [flagImpl]
  congr

/-- A secret drawn from `sd`, which each counted call hits with probability at most `ε` and which
the handler never reads, is hit by a computation with at most `n` counted calls with probability at
most `n * ε`. -/
theorem probEvent_flag_le (impl : QueryImpl spec (StateT σ ProbComp)) (hit : κ → S → Prop)
    (sd : ProbComp S) (p : κ → Prop) [DecidablePred p] (ε : ℝ≥0∞) (hp : ∀ t s, hit t s → p t)
    (hε : ∀ t, p t → Pr[hit t | sd] ≤ ε) (oa : OracleComp spec β) :
    ∀ (n : ℕ) (σ₀ : σ), IsQueryBoundP oa p n →
      Pr[fun r => r.2.2 = true | sd >>= fun s => (simulateQ (flagImpl impl hit s) oa).run (σ₀, false)] ≤
        n * ε := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n σ₀ _
    simp [Function.comp_def]
  | query_bind t k ih =>
    intro n σ₀ hq
    rw [isQueryBoundP_query_bind_iff] at hq
    set g : S → spec t × σ → ℝ≥0∞ := fun s x =>
      Pr[fun r => r.2.2 = true | (simulateQ (flagImpl impl hit s) (k x.1)).run (x.2, false)] with hg
    have key : ∀ s, Pr[fun r => r.2.2 = true |
        (simulateQ (flagImpl impl hit s) (liftM (spec.query t) >>= k)).run (σ₀, false)] ≤
        (if hit t s then 1 else 0) + ∑' x, Pr[= x | (impl t).run σ₀] * g s x := by
      intro s
      rw [flagImpl_query_bind_run, probEvent_bind_eq_tsum]
      by_cases hs : hit t s
      · rw [if_pos hs]
        refine le_trans ?_ le_self_add
        calc _ ≤ ∑' x, Pr[= x | (impl t).run σ₀] * 1 :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact probEvent_le_one
          _ ≤ 1 := by simp
      · simp [hs, hg]
    have hsum : ∑' x, Pr[= x | (impl t).run σ₀] * (∑' s, Pr[= s | sd] * g s x) ≤
        (if p t then n - 1 else n : ℕ) * ε := by
      calc _ ≤ ∑' x, Pr[= x | (impl t).run σ₀] * ((if p t then n - 1 else n : ℕ) * ε) := by
            refine ENNReal.tsum_le_tsum fun x => ?_
            gcongr
            have := ih x.1 _ x.2 (hq.2 x.1)
            rwa [probEvent_bind_eq_tsum] at this
        _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
    have hhit : ∑' s, Pr[= s | sd] * (if hit t s then 1 else 0) ≤ if p t then ε else 0 := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← probEvent_eq_tsum_ite]
      split_ifs with hpt
      · exact hε t hpt
      · exact le_of_eq (probEvent_eq_zero fun s _ hs => hpt (hp t s hs))
    calc _ = ∑' s, Pr[= s | sd] * Pr[fun r => r.2.2 = true |
          (simulateQ (flagImpl impl hit s) (liftM (spec.query t) >>= k)).run (σ₀, false)] :=
          probEvent_bind_eq_tsum _ _ _
      _ ≤ ∑' s, Pr[= s | sd] * ((if hit t s then 1 else 0) + ∑' x, Pr[= x | (impl t).run σ₀] * g s x) :=
          ENNReal.tsum_le_tsum fun s => by gcongr; exact key s
      _ = ∑' s, Pr[= s | sd] * (if hit t s then 1 else 0) +
          ∑' x, Pr[= x | (impl t).run σ₀] * (∑' s, Pr[= s | sd] * g s x) := by
          simp only [mul_add, ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          simp only [mul_left_comm]
      _ ≤ (if p t then ε else 0) + (if p t then n - 1 else n : ℕ) * ε := add_le_add hhit hsum
      _ ≤ n * ε := by
          split_ifs with hpt
          · have hn := hq.1.resolve_left (not_not.mpr hpt)
            rw [← one_add_mul]
            gcongr
            exact_mod_cast (by omega : 1 + (n - 1) ≤ n)
          · simp

variable {P : Type} [Fintype P] [DecidableEq P] [SampleableType P]

/-- One coordinate of `k` uniform secret points equals a fixed point with probability `1 / |P|`. -/
theorem probEvent_uniform_coord_eq {k : ℕ} (j : Fin k) (x : P) :
    Pr[fun s => s j = x | $ᵗ (Fin k → P)] = (Fintype.card P : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample]
  have hfil : (Finset.univ.filter fun s : Fin k → P => s j = x).card = Fintype.card P ^ (k - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset P) j (Finset.mem_univ x)
    simpa using this
  have hk : k = (k - 1) + 1 := by have := j.2; omega
  have hP : (Fintype.card P : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨x⟩
    exact_mod_cast this.ne'
  rw [hfil, Fintype.card_fun, Fintype.card_fin, hk, pow_succ, Nat.cast_mul, Nat.add_sub_cancel]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP))))
    (Or.inl (by simp))]
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP)))
    (ENNReal.natCast_ne_top _), one_mul]

/-- Some of `k` uniform secret points equals a fixed point with probability at most `k / |P|`. -/
theorem probEvent_uniform_exists_eq_le (k : ℕ) (x : P) :
    Pr[fun s => ∃ j, s j = x | $ᵗ (Fin k → P)] ≤ k * (Fintype.card P : ℝ≥0∞)⁻¹ := by
  calc _ = Pr[fun s => ∃ j ∈ (Finset.univ : Finset (Fin k)), s j = x | $ᵗ (Fin k → P)] := by simp
    _ ≤ ∑ j : Fin k, Pr[fun s => s j = x | $ᵗ (Fin k → P)] := probEvent_exists_finset_le_sum _ _ _
    _ = k * (Fintype.card P : ℝ≥0∞)⁻¹ := by
      simp only [probEvent_uniform_coord_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A computation with at most `q` counted calls, each aimed at one point, run on a handler that
never reads the `k` uniform secret points, hits one of them with probability at most `q * k / |P|`. -/
theorem probEvent_hit_uniform_le (impl : QueryImpl spec (StateT σ ProbComp)) (p : κ → Prop) [DecidablePred p]
    (point : κ → P) (k : ℕ) (oa : OracleComp spec β) (q : ℕ) (hq : IsQueryBoundP oa p q) (σ₀ : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (Fin k → P) >>= fun s =>
      (simulateQ (flagImpl impl (fun t s => p t ∧ ∃ j, s j = point t) s) oa).run (σ₀, false)] ≤
        q * (k * (Fintype.card P : ℝ≥0∞)⁻¹) :=
  probEvent_flag_le impl _ _ p _ (fun _ _ h => h.1)
    (fun t _ => le_trans (probEvent_mono fun _ _ h => h.2) (probEvent_uniform_exists_eq_le k (point t))) oa q σ₀ hq

/-- The 256-bit case: `q` counted calls hit one of `k` secret uniform hash outputs with probability at
most `q * k / 2 ^ 256`. -/
theorem probEvent_hit_hashOutput_le (impl : QueryImpl spec (StateT σ ProbComp)) (p : κ → Prop) [DecidablePred p]
    (point : κ → HashOutput) (k : ℕ) (oa : OracleComp spec β) (q : ℕ) (hq : IsQueryBoundP oa p q) (σ₀ : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (Fin k → HashOutput) >>= fun s =>
      (simulateQ (flagImpl impl (fun t s => p t ∧ ∃ j, s j = point t) s) oa).run (σ₀, false)] ≤
        q * k / 2 ^ 256 := by
  refine (probEvent_hit_uniform_le impl p point k oa q hq σ₀).trans (le_of_eq ?_)
  have hcard : Fintype.card HashOutput = 2 ^ 256 := by unfold HashOutput hashOutputBits; exact card_bitVec 256
  rw [hcard, ← mul_assoc, div_eq_mul_inv]
  norm_num

end Hit

/-! ## Moving a handler into the roles -/

section Transport

variable {E : Type} {κ : Type} {spec : OracleSpec κ} {n : Type → Type} [Monad n] [LawfulMonad n]
  (impl : QueryImpl spec n)

/-- The roles that run each step through the handler `impl`. -/
def simRoles (Ro : Roles C (OracleComp spec)) : Roles C n :=
  ⟨fun oa => simulateQ impl (Ro.adversary oa), fun oa => simulateQ impl (Ro.honest oa)⟩

/-- A handler commutes with the run of a state-passing simulation. -/
theorem simulateQ_run_simulateQ {κ' τ β : Type} {spec' : OracleSpec κ'}
    (J : QueryImpl spec' (StateT τ (OracleComp spec))) (X : OracleComp spec' β) (s : τ) :
    simulateQ impl ((simulateQ J X).run s) =
      (simulateQ (fun t => (StateT.mk fun s => simulateQ impl ((J t).run s) : StateT τ n _)) X).run s := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, ih]
    rfl

variable {Ia I O L R α : Type}

/-- A handler applied to a functionality run runs each of its steps through it. -/
theorem simulateQ_runFunctionality (Ro : Roles C (OracleComp spec)) (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) (state : A.State) (inputs : C.Party → Option I) :
    simulateQ impl (runFunctionality Ro D A F state inputs) =
      runFunctionality (simRoles impl Ro) D A F state inputs := by
  unfold runFunctionality
  split_ifs
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_run_simulateQ, pure_bind]
    refine congrArg (fun J : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT A.State n) =>
      (StateT.run (simulateQ J (F.run D inputs)) state) >>=
        fun x => (pure (x.2, x.1) : n (A.State × (C.Party → Option O)))) ?_
    funext t
    rcases t with t | l
    · show (StateT.mk fun s => simulateQ impl
          ((StateT.lift (Ro.honest (OracleComp.lift (OracleSpec.query t))) : StateT A.State _ _).run s)) =
        StateT.lift (simulateQ impl (Ro.honest (OracleComp.lift (OracleSpec.query t))))
      ext s : 1
      simp [StateT.run_lift]
    · show (StateT.mk fun s => simulateQ impl
          (Ro.adversary (A.answer s l) >>= fun p => pure (p.2, p.1))) =
        (StateT.mk fun s => simulateQ impl (Ro.adversary (A.answer s l)) >>= fun p => pure (p.2, p.1))
      ext s : 1
      simp
  · simp

/-- A handler applied to a round runs each of its steps through it. -/
theorem simulateQ_stepRound (Ro : Roles C (OracleComp spec)) (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) :
    simulateQ impl (stepRound Ro D A F state steps) = stepRound (simRoles impl Ro) D A F state steps := by
  unfold stepRound
  split_ifs
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_runFunctionality, simulateQ_sequenceFin]
    refine bind_congr fun x => ?_
    congr 2; funext i
    rcases steps i with out | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> simp [simRoles]
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin]
    refine bind_congr fun x => ?_
    congr 2; funext i
    rcases steps i with out | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> simp [simRoles]

/-- A handler applied to the rounds runs each step of the rounds through it. -/
theorem simulateQ_executeRounds (Ro : Roles C (OracleComp spec)) (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
      simulateQ impl (executeRounds Ro D A F fuel state steps) =
        executeRounds (simRoles impl Ro) D A F fuel state steps
  | 0, state, steps => by simp [executeRounds]
  | fuel + 1, state, steps => by
    rw [executeRounds_succ, executeRounds_succ]
    split_ifs
    · simp
    · simp only [simulateQ_bind, simulateQ_stepRound, simulateQ_executeRounds Ro D A F fuel]

/-- A handler applied to a phase runs each step of the phase through it. -/
theorem simulateQ_executePhase (Ro : Roles C (OracleComp spec)) (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E (CallSpec I O) α) :
    simulateQ impl (executePhase Ro D A F fuel state program) =
      executePhase (simRoles impl Ro) D A F fuel state program := by
  simp only [executePhase, startSteps, simulateQ_bind, simulateQ_sequenceFin, simulateQ_executeRounds]
  congr 2; funext i
  split_ifs <;> simp [simRoles]

end Transport

/-! ## Acceptance in the world -/

section World

variable (prims : Primitives)

/-- The run of a world computation on the cache-only handler, from the empty cache. -/
abbrev worldRun {β : Type} (oa : OracleComp (WorldSpec C) β) : ProbComp (β × HashCache C) :=
  (simulateQ (worldAnswer (C := C) prims) oa).run ∅

/-- Acceptance reads the cache-only run of the world. -/
theorem accepts_eq_worldRun (oa : OracleComp (WorldSpec C) Bool) :
    accepts prims oa = Pr[fun r => r.1 = true | worldRun prims oa].toReal := by
  unfold accepts
  have h := congrArg (fun m => Pr[fun b => b = true | m]) (fst_map_runWorld prims oa)
  simp only [probEvent_map] at h
  rw [show (fun r : Bool × ℕ => r.1 = true) = (fun b => b = true) ∘ (fun r => r.1) from rfl, h,
    StateT.run'_eq, probEvent_map]
  rfl

/-- The run of a computation followed by a continuation, paired with the run of the first part. -/
theorem worldRun_bind {β : Type} (oa : OracleComp (WorldSpec C) β) (k : β → OracleComp (WorldSpec C) Bool) :
    worldRun prims (oa >>= k) = Prod.snd <$> (worldRun prims oa >>= fun x =>
      (fun r => (x, r)) <$> (simulateQ (worldAnswer (C := C) prims) (k x.1)).run x.2) := by
  simp only [worldRun, simulateQ_bind, StateT.run_bind, map_bind, Functor.map_map]
  simp

/-- Up to bad in the world. Two runs coupled so that their outputs and caches are related unless a
bad event on the left cache fires, followed by continuations that accept alike from related points,
accept with probabilities at most the bad probability apart. -/
theorem abs_accepts_bind_sub_le {β γ : Type} (oa : OracleComp (WorldSpec C) β) (ob : OracleComp (WorldSpec C) γ)
    (ka : β → OracleComp (WorldSpec C) Bool) (kb : γ → OracleComp (WorldSpec C) Bool)
    (Bad : HashCache C → Prop) (Q : β × HashCache C → γ × HashCache C → Prop)
    (h : RelTriple (worldRun prims oa) (worldRun prims ob) fun x y => Bad x.2 ∨ Q x y)
    (hk : ∀ x y, Q x y → RelTriple ((simulateQ (worldAnswer (C := C) prims) (ka x.1)).run x.2)
      ((simulateQ (worldAnswer (C := C) prims) (kb y.1)).run y.2) fun a b => a.1 = b.1) :
    |accepts prims (oa >>= ka) - accepts prims (ob >>= kb)| ≤
      Pr[fun x => Bad x.2 | worldRun prims oa].toReal := by
  rw [accepts_eq_worldRun, accepts_eq_worldRun, worldRun_bind, worldRun_bind, probEvent_map, probEvent_map]
  have hbad : Pr[fun x => Bad x.2 | worldRun prims oa] =
      Pr[fun r => Bad r.1.2 | worldRun prims oa >>= fun x =>
        (fun r => (x, r)) <$> (simulateQ (worldAnswer (C := C) prims) (ka x.1)).run x.2] := by
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine tsum_congr fun x => ?_
    simp only [probEvent_map, Function.comp_def]
    split_ifs with hx <;> simp [hx]
  rw [hbad]
  refine abs_probEvent_sub_le_of_relTriple _ _ _ (relTriple_bind h fun x y hxy => ?_)
  by_cases hb : Bad x.2
  · exact relTriple_of_support_left fun r hr _ => by
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨a, -, rfl⟩ := hr
      exact Or.inl hb
  · exact relTriple_map (relTriple_post_mono (hk x y (hxy.resolve_left hb)) fun a b hab => by
      simp [hab])

/-- Two executions whose joint outputs and caches agree unless a bad event on the left cache fires
give every distinguisher acceptance probabilities at most the bad probability apart. -/
theorem abs_accepts_distinguish_sub_le {σ O : Type} (oa ob : OracleComp (WorldSpec C) (σ × (C.Party → Option O)))
    (Z : Distinguisher C σ O) (Bad : HashCache C → Prop)
    (h : RelTriple (worldRun prims oa) (worldRun prims ob) fun x y => Bad x.2 ∨ x = y) :
    |accepts prims (distinguish oa Z) - accepts prims (distinguish ob Z)| ≤
      Pr[fun x => Bad x.2 | worldRun prims oa].toReal := by
  refine abs_accepts_bind_sub_le prims oa ob _ _ Bad Eq h fun x y hxy => ?_
  subst hxy
  exact relTriple_post_mono (relTriple_refl _) fun a b hab => by rw [show a = b from hab]

/-- The calls of a world computation that the budget counts, namely the counted calls of the counted
copy and its programming queries. -/
def WorldCounted : (WorldSpec C).Domain → Prop
  | .inl (.inl u) => Counted u
  | .inl (.inr _) => True
  | .inr _ => False

/-- The adversary role keeps the counted calls of a computation. -/
theorem isQueryBoundP_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) : IsQueryBoundP (worldRoles.adversary oa) WorldCounted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- The honest role makes no counted call. -/
theorem isQueryBoundP_free {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ) :
    IsQueryBoundP (free oa) WorldCounted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e]
    exact ⟨Or.inl not_false, fun u => ih u _⟩

/-- A sequence of computations without counted calls makes no counted call. -/
theorem isQueryBoundP_sequenceFin {κ β : Type} {spec : OracleSpec κ} {p : κ → Prop} [DecidablePred p] :
    ∀ {N : ℕ} (f : Fin N → OracleComp spec β), (∀ i, IsQueryBoundP (f i) p 0) →
      IsQueryBoundP (Concrete.sequenceFin f) p 0
  | 0, f, _ => by simp [Concrete.sequenceFin]
  | N + 1, f, h => by
    simp only [Concrete.sequenceFin]
    exact isQueryBoundP_bind (h 0) fun _ _ => isQueryBoundP_bind
      (m := 0) (isQueryBoundP_sequenceFin (fun i : Fin N => f i.succ) fun i => h i.succ) fun _ _ => isQueryBoundP_pure _ _ 0

variable {E Ia I O L R α : Type}

/-- A step of the world execution costs at most one round of the adversary or one functionality. -/
theorem isQueryBoundP_stepRound (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (step : ℕ) (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality worldRoles D A F state inputs) WorldCounted step)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    IsQueryBoundP (stepRound worldRoles D A F state steps) WorldCounted step := by
  unfold stepRound
  split_ifs
  · refine (isQueryBoundP_bind (hF _ _) fun x _ => isQueryBoundP_bind (isQueryBoundP_sequenceFin _ fun j => ?_)
      fun _ _ => isQueryBoundP_pure _ _ 0).mono (by simp)
    rcases steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
    · trivial
    · trivial
    · dsimp only
      split_ifs
      · trivial
      · exact isQueryBoundP_free _ _
  · refine (isQueryBoundP_bind (isQueryBoundP_adversary _ _ (hround _ _)) fun x _ =>
      isQueryBoundP_bind (isQueryBoundP_sequenceFin _ fun j => ?_) fun _ _ => isQueryBoundP_pure _ _ 0).mono
      (by simp)
    rcases steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
    · trivial
    · dsimp only
      split_ifs
      · trivial
      · exact isQueryBoundP_free _ _
    · trivial

/-- The rounds of the world execution cost at most `fuel` steps. -/
theorem isQueryBoundP_executeRounds (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (step : ℕ) (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality worldRoles D A F state inputs) WorldCounted step) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
      IsQueryBoundP (executeRounds worldRoles D A F fuel state steps) WorldCounted (fuel * step)
  | 0, state, steps => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps => by
    rw [executeRounds_succ]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact (isQueryBoundP_bind (isQueryBoundP_stepRound D A F step hround hF state steps) fun p _ =>
        isQueryBoundP_executeRounds D A F step hround hF fuel _ _).mono (by rw [Nat.succ_mul, Nat.add_comm])

/-- A `q`-query adversary and distinguisher make at most `q` counted calls in the whole real
execution, when each functionality run costs at most one step of the adversary. -/
theorem isQueryBoundP_distinguish_realExecution {Ih Oh : Type} (D : C.Coalition) (A : Adversary C E I L R)
    (Fh : Functionality C Ih Oh L R) (fuel : ℕ) (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (x : C.Party → I) (z : Aux) (Z : Distinguisher C A.State O) (q : ℕ) (hq : IsQueryBounded A Z fuel q)
    (hF : ∀ step, (∀ state l, IsQueryBoundP (A.answer state l) Counted step) →
      ∀ state inputs, IsQueryBoundP (runFunctionality worldRoles D A Fh state inputs) WorldCounted step) :
    IsQueryBoundP (distinguish (realExecution D A Fh fuel program x z) Z) WorldCounted q := by
  obtain ⟨start, step, final, hle, hstart, hround, hanswer, hfinal⟩ := hq
  refine IsQueryBoundP.mono ?_ hle
  unfold distinguish realExecution executePhase
  simp only [bind_assoc]
  rw [Nat.add_assoc]
  refine isQueryBoundP_bind (isQueryBoundP_adversary _ _ (hstart _ _)) fun st _ => ?_
  rw [show fuel * step + final = 0 + (fuel * step + final) from (Nat.zero_add _).symm]
  refine isQueryBoundP_bind (isQueryBoundP_sequenceFin _ fun i => ?_) fun steps _ => ?_
  · split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_free _ _
  · exact isQueryBoundP_bind (isQueryBoundP_executeRounds D A Fh step (hround) (hF step hanswer) fuel _ _)
      fun r _ => isQueryBoundP_adversary _ _ (hfinal _)

/-- The real network has no functionality, so its functionality step costs nothing. -/
theorem isQueryBoundP_runFunctionality_noFunctionality (D : C.Coalition)
    (A : Adversary C E Ia PEmpty PEmpty) (state : A.State) (inputs : C.Party → Option PEmpty) (n : ℕ) :
    IsQueryBoundP (runFunctionality worldRoles D A (noFunctionality (C := C)) state inputs) WorldCounted n := by
  unfold runFunctionality
  split_ifs
  · exact isQueryBoundP_pure _ _ _
  · simp

/-- Item 3 on the world. In a run of a `q`-query adversary and distinguisher on any handler that never
reads the `k` secret uniform hash outputs, a counted call aimed at one of them occurs with
probability at most `q * k / 2 ^ 256`. -/
theorem probEvent_hit_realExecution_le {σ Ih Oh : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (point : (WorldSpec C).Domain → HashOutput) (k : ℕ) (D : C.Coalition) (A : Adversary C E I L R)
    (Fh : Functionality C Ih Oh L R) (fuel : ℕ) (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (x : C.Party → I) (z : Aux) (Z : Distinguisher C A.State O) (q : ℕ) (hq : IsQueryBounded A Z fuel q)
    (hF : ∀ step, (∀ state l, IsQueryBoundP (A.answer state l) Counted step) →
      ∀ state inputs, IsQueryBoundP (runFunctionality worldRoles D A Fh state inputs) WorldCounted step)
    (σ₀ : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (Fin k → HashOutput) >>= fun s =>
      (simulateQ (flagImpl impl (fun t s => WorldCounted t ∧ ∃ j, s j = point t) s)
        (distinguish (realExecution D A Fh fuel program x z) Z)).run (σ₀, false)] ≤ q * k / 2 ^ 256 :=
  probEvent_hit_hashOutput_le impl WorldCounted point k _ q
    (isQueryBoundP_distinguish_realExecution D A Fh fuel program x z Z q hq hF) σ₀

/-- Lockstep in the world. Two executions that start from related configurations and then run
`executeRounds` with any roles and functionalities against one adversary, whose rounds on the world
handler stay related until a sticky bad event on the left cache, and whose related configurations
end with equal joint outputs and caches, give every distinguisher acceptance probabilities at most
the bad probability apart. -/
theorem abs_accepts_lockstep_sub_le {E Ia I₁ I₂ O₁ O₂ L R α : Type}
    (Ro₁ Ro₂ : Roles C (OracleComp (WorldSpec C))) (D₁ D₂ : C.Coalition) (A : Adversary C E Ia L R)
    (F₁ : Functionality C I₁ O₁ L R) (F₂ : Functionality C I₂ O₂ L R) (fuel : ℕ)
    (pa : OracleComp (WorldSpec C) (A.State × (C.Party → Step C E (CallSpec I₁ O₁) α)))
    (pb : OracleComp (WorldSpec C) (A.State × (C.Party → Step C E (CallSpec I₂ O₂) α)))
    (Z : Distinguisher C A.State α) (Bad : HashCache C → Prop)
    (Rel : (A.State × (C.Party → Step C E (CallSpec I₁ O₁) α)) × HashCache C →
      (A.State × (C.Party → Step C E (CallSpec I₂ O₂) α)) × HashCache C → Prop)
    (hpre : RelTriple (worldRun prims pa) (worldRun prims pb) fun x y => Bad x.2 ∨ Rel x y)
    (hsticky : ∀ st (steps : C.Party → Step C E (CallSpec I₁ O₁) α) s, Bad s →
      ∀ x ∈ support ((stepRound (simRoles (worldAnswer prims) Ro₁) D₁ A F₁ st steps).run s), Bad x.2)
    (hdone : ∀ c₁ c₂, Rel c₁ c₂ → ¬ Bad c₁.2 → (AllDone D₁ c₁.1.2 ↔ AllDone D₂ c₂.1.2))
    (hout : ∀ c₁ c₂, Rel c₁ c₂ → ¬ Bad c₁.2 →
      ((c₁.1.1, fun i => (c₁.1.2 i).output), c₁.2) = ((c₂.1.1, fun i => (c₂.1.2 i).output), c₂.2))
    (hstep : ∀ c₁ c₂, Rel c₁ c₂ → ¬ Bad c₁.2 → ¬ AllDone D₁ c₁.1.2 →
      RelTriple ((stepRound (simRoles (worldAnswer prims) Ro₁) D₁ A F₁ c₁.1.1 c₁.1.2).run c₁.2)
        ((stepRound (simRoles (worldAnswer prims) Ro₂) D₂ A F₂ c₂.1.1 c₂.1.2).run c₂.2)
        fun x y => Bad x.2 ∨ Rel ((x.1.1, x.1.2.1), x.2) ((y.1.1, y.1.2.1), y.2)) :
    |accepts prims (distinguish (pa >>= fun c => executeRounds Ro₁ D₁ A F₁ fuel c.1 c.2) Z) -
        accepts prims (distinguish (pb >>= fun c => executeRounds Ro₂ D₂ A F₂ fuel c.1 c.2) Z)| ≤
      Pr[fun x => Bad x.2 | worldRun prims (pa >>= fun c => executeRounds Ro₁ D₁ A F₁ fuel c.1 c.2)].toReal := by
  refine abs_accepts_distinguish_sub_le prims _ _ Z Bad ?_
  simp only [worldRun, simulateQ_bind, StateT.run_bind, simulateQ_executeRounds]
  exact relTriple_bind hpre fun x y hxy =>
    relTriple_executeRounds (simRoles (worldAnswer prims) Ro₁) (simRoles (worldAnswer prims) Ro₂) D₁ D₂ A A
      F₁ F₂ Bad Rel (fun a b => a = b) hsticky hdone hout hstep fuel x y hxy

end World

/-- info: 'ThresholdLeanXmssSecurity.abs_accepts_lockstep_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_accepts_lockstep_sub_le

/-- info: 'ThresholdLeanXmssSecurity.relTriple_executeRounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_executeRounds

/-- info: 'ThresholdLeanXmssSecurity.evalDist_executeRounds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_executeRounds_eq

/-- info: 'ThresholdLeanXmssSecurity.relTriple_run_uniform_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_run_uniform_shift

/-- info: 'ThresholdLeanXmssSecurity.probEvent_hit_realExecution_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_hit_realExecution_le

end ThresholdLeanXmssSecurity
