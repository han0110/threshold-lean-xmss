import ThresholdLeanXmssSecurity.Proof.CheckLast
import ThresholdLeanXmssSecurity.Proof.Coupling

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra Bit E] [SampleableType E]

-- Target: checkSoundStage (prims : Primitives) (K : Constants C E) : CheckSoundStage prims K.

/-- An accepted opening fixes the honest shares to one polynomial. -/
theorem openAgrees_honest_polynomial (K : Constants C E) (D : C.Coalition)
    (v : C.Party → ℕ → E) (i : C.Party) (inbox : Mail C E)
    (hin : ∀ j, j ∉ D.1 → j ≠ i → inbox j = openOutbox j (v j) i)
    (hag : OpenAgrees K i (v i) inbox) (g : ℕ) (hg : g < 3) :
    ∃ P : Polynomial E, P.natDegree ≤ C.t - 1 ∧
      P.eval 0 = openValue K i (v i) inbox g ∧
      ∀ j, j ∉ D.1 → v j g = P.eval (K.point j) := by
  let P := Lagrange.interpolate (firstParties C) K.point (fun j => openShare i (v i) inbox j g)
  refine ⟨P, ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_le_of_degree_le
    simpa only [card_firstParties] using Lagrange.degree_interpolate_le
      (fun j => openShare i (v i) inbox j g) K.point.injective.injOn (s := firstParties C)
  · exact eval_interpolate_first K _ 0
  · intro j hj
    rw [show P.eval (K.point j) = _ from eval_interpolate_first K _ (K.point j), ← hag j g hg]
    by_cases he : j = i
    · subst j
      simp [openShare]
    · rw [openShare, if_neg he, hin j hj he]
      simp [openOutbox, Ne.symm he, Msg.elementAt, vector, hg]

/-- Every accepted opening is the fixed interpolation of the honest shares. -/
theorem openValue_eq_interpolate (K : Constants C E) (D : C.Coalition)
    (v : C.Party → ℕ → E) (i : C.Party) (inbox : Mail C E)
    (hin : ∀ j, j ∉ D.1 → j ≠ i → inbox j = openOutbox j (v j) i)
    (hag : OpenAgrees K i (v i) inbox) (g : ℕ) (hg : g < 3) :
    openValue K i (v i) inbox g = interpolate K D.1 (fun j => v j g) 0 := by
  obtain ⟨P, hP, hP0, hPj⟩ := openAgrees_honest_polynomial K D v i inbox hin hag g hg
  rw [interpolate_honest_polynomial K D P hP _ hPj, hP0]

/-- Public linear combinations commute with the fixed honest interpolation. -/
theorem interpolate_lin (K : Constants C E) (D : Finset C.Party)
    (a b : C.Party → E) (u v x : E) :
    interpolate K D (fun i => u * a i + v * b i) x =
      u * interpolate K D a x + v * interpolate K D b x := by
  simp only [interpolate, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Different accepting operators open the same values, without comparing digests. -/
theorem accepted_openValues_agree (K : Constants C E) (D : C.Coalition)
    (v : C.Party → ℕ → E) (i j : C.Party) (inboxI inboxJ : Mail C E)
    (hinI : ∀ k, k ∉ D.1 → k ≠ i → inboxI k = openOutbox k (v k) i)
    (hinJ : ∀ k, k ∉ D.1 → k ≠ j → inboxJ k = openOutbox k (v k) j)
    (hagI : OpenAgrees K i (v i) inboxI) (hagJ : OpenAgrees K j (v j) inboxJ)
    (g : ℕ) (hg : g < 3) :
    openValue K i (v i) inboxI g = openValue K j (v j) inboxJ g := by
  rw [openValue_eq_interpolate K D v i inboxI hinI hagI g hg,
    openValue_eq_interpolate K D v j inboxJ hinJ hagJ g hg]

/-- The final three effective values depend only on the pre-challenge shares. -/
theorem interpolate_finalOpenVector (K : Constants C E) (D : Finset C.Party)
    (wa wb a b d q0 q2 : C.Party → E) (r : E) (g : ℕ) :
    interpolate K D (fun i => finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r g) 0 =
      finalOpenVector (interpolate K D wa 0) (interpolate K D wb 0)
        (interpolate K D a 0) (interpolate K D b 0) (interpolate K D d 0)
        (interpolate K D q0 0) (interpolate K D q2 0) r g := by
  rcases g with _ | _ | g <;>
    simp only [finalOpenVector, interpolate, mul_add, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Holder-specific errors reduce to two scalars fixed before the final challenge. -/
theorem final_accept_effective_root (K : Constants C E) (D : C.Coalition)
    (wa wb a b d q0 q2 : C.Party → E) (r : E) (i : C.Party) (inbox : Mail C E)
    (hin : ∀ j, j ∉ D.1 → j ≠ i → inbox j =
      openOutbox j (finalOpenVector (wa j) (wb j) (a j) (b j) (d j) (q0 j) (q2 j) r) i)
    (hag : OpenAgrees K i (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r) inbox)
    (haccept :
      openValue K i (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r) inbox 0 *
        openValue K i (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r) inbox 1 =
      openValue K i (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r) inbox 2) :
    let I := fun f : C.Party → E => interpolate K D.1 f 0
    r * (I d - I a * I b) + (1 + r) * (I q0 - I wa * I wb) +
      r * (1 + r) * (I q2 - (I wa + I a) * (I wb + I b)) = 0 := by
  let v := fun j => finalOpenVector (wa j) (wb j) (a j) (b j) (d j) (q0 j) (q2 j) r
  have ho (g : ℕ) (hg : g < 3) := openValue_eq_interpolate K D v i inbox hin hag g hg
  rw [ho 0 (by omega), ho 1 (by omega), ho 2 (by omega)] at haccept
  simp only [v] at haccept
  rw [interpolate_finalOpenVector, interpolate_finalOpenVector, interpolate_finalOpenVector] at haccept
  simp only [finalOpenVector] at haccept
  dsimp only
  have h := final_residual_identity (interpolate K D.1 a 0) (interpolate K D.1 b 0)
    (interpolate K D.1 wa 0) (interpolate K D.1 wb 0) (interpolate K D.1 d 0)
    (interpolate K D.1 q0 0 - interpolate K D.1 wa 0 * interpolate K D.1 wb 0)
    (interpolate K D.1 q2 0 - (interpolate K D.1 wa 0 + interpolate K D.1 a 0) *
      (interpolate K D.1 wb 0 + interpolate K D.1 b 0)) r
  linear_combination -h - haccept

/-- The same effective error applies to every honest recipient of the final network round. -/
theorem finalRoundOutputs_effective_root (K : Constants C E) (D : C.Coalition)
    (live : C.Party → Prop) (sent : C.Party → Mail C E)
    (wa wb a b d q0 q2 : C.Party → E) (r : E) (i : C.Party)
    (hi : finalRoundOutputs K D live
      (fun j => finalOpenVector (wa j) (wb j) (a j) (b j) (d j) (q0 j) (q2 j) r) sent i = some ()) :
    let I := fun f : C.Party → E => interpolate K D.1 f 0
    r * (I d - I a * I b) + (1 + r) * (I q0 - I wa * I wb) +
      r * (1 + r) * (I q2 - (I wa + I a) * (I wb + I b)) = 0 := by
  let v := fun j => finalOpenVector (wa j) (wb j) (a j) (b j) (d j) (q0 j) (q2 j) r
  have ha : i ∉ D.1 ∧ live i ∧ finalRoundAccept K D live v sent i := by
    simpa [finalRoundOutputs] using hi
  have hl := finalRoundAccept_all_live K D live v sent i ha.2.2
  exact final_accept_effective_root K D wa wb a b d q0 q2 r i (finalInbox D live v sent i)
    (fun j hj _ => by simp [finalInbox, hj, hl j hj, v]) ha.2.2.2.1 ha.2.2.2.2

/-- The cached final challenge bounds even a rushing, selectively aborting final reply. -/
theorem finalChallenge_effective_soundness (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (tag label : ℕ) (coin : List E) (Ks : Finset HashOutput) (cache : HashCache C)
    (hfresh : cache (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v))) = none)
    (hexpand : ∀ key idx, cache (.expand key idx) ≠ none → key ∈ Ks)
    (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0)
    (reply : E → HashCache C → ProbComp ((C.Party → Prop) × (C.Party → Mail C E))) :
    Pr[fun out : C.Party → Option Unit => ∃ i, out i = some () |
      (simulateQ (localAnswer prims)
        (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache >>= fun p =>
      match p.1 with
      | none => pure (fun _ : C.Party => (none : Option Unit))
      | some r => do
        let ans ← reply r p.2
        pure (finalRoundOutputs K D ans.1
          (fun j => finalOpenVector (wa j) (wb j) (a j) (b j) (d j) (q0 j) (q2 j) r) ans.2)] ≤
      Ks.card / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ) := by
  apply finalChallenge_adaptive_soundness prims K tag label coin Ks cache hfresh hexpand
    (interpolate K D.1 a 0) (interpolate K D.1 b 0) (interpolate K D.1 d 0)
    (interpolate K D.1 q0 0 - interpolate K D.1 wa 0 * interpolate K D.1 wb 0)
    (interpolate K D.1 q2 0 - (interpolate K D.1 wa 0 + interpolate K D.1 a 0) *
      (interpolate K D.1 wb 0 + interpolate K D.1 b 0)) hwrong
  intro p out hout ha
  rcases p with ⟨_ | r, cache'⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    simp at ha
  · simp only [support_bind, support_pure, Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hout
    obtain ⟨ans, _, rfl⟩ := hout
    obtain ⟨i, hi⟩ := ha
    exact ⟨r, rfl, finalRoundOutputs_effective_root K D ans.1 ans.2 wa wb a b d q0 q2 r i hi⟩

/-- Slice updates commute with the fixed honest interpolation, including inconsistent claims. -/
theorem interpolate_sliceClaim (K : Constants C E) (D : Finset C.Party)
    (τ : List E) (j : ℕ) (r : E) (V q0 qInf : C.Party → E) :
    interpolate K D (fun i => sliceClaim τ j r (V i) (q0 i) (qInf i)) 0 =
      sliceClaim τ j r (interpolate K D V 0) (interpolate K D q0 0) (interpolate K D qInf 0) := by
  simp only [sliceClaim, interpolate, div_eq_mul_inv, mul_add, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Halving updates commute with the same interpolation. -/
theorem interpolate_halvingClaim (K : Constants C E) (D : Finset C.Party)
    (r : E) (V q0 q2 : C.Party → E) :
    interpolate K D (fun i => q0 i + (V i + q2 i) * r + q2 i * r ^ 2) 0 =
      interpolate K D q0 0 + (interpolate K D V 0 + interpolate K D q2 0) * r +
        interpolate K D q2 0 * r ^ 2 := by
  simp only [interpolate, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- The vectors and the claim use the same effective values throughout the halving loop. -/
theorem interpolate_halvFold (K : Constants C E) (D : Finset C.Party)
    (len : ℕ) (r : E) (A : C.Party → ℕ → E) (k : ℕ) :
    interpolate K D (fun i => halvFold len r (A i) k) 0 =
      halvFold len r (fun k => interpolate K D (fun i => A i k) 0) k := by
  by_cases hk : k + halvedLength len < len <;>
    simp only [halvFold, hk, if_true, if_false, interpolate, mul_add, add_mul,
      add_zero, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_assoc]

/-- Gruen's exceptional set still has size two for arbitrary holder-specific offsets. -/
theorem slice_effective_card_le_two (K : Constants C E) (D : C.Coalition)
    (τ : List E) (j : ℕ) (V q0 qInf : C.Party → E) (t0 t1 t2 : E)
    (hc : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    (hwrong : interpolate K D.1 V 0 ≠ t0 + τ.getD (sliceBits - 1 - j) 0 * (t0 + t1 + t2)) :
    (univ.filter fun r : E =>
      interpolate K D.1 (fun i => sliceClaim τ j r (V i) (q0 i) (qInf i)) 0 =
        t0 + t1 * r + t2 * r ^ 2).card ≤ 2 := by
  letI : CharP E 2 := charP_two
  simp_rw [interpolate_sliceClaim]
  simpa only [sliceClaim, add_sub_cancel] using
    gruen_slice_step (τ.getD (sliceBits - 1 - j) 0) (interpolate K D.1 V 0)
      t0 t1 t2 (interpolate K D.1 q0 0 - t0) (interpolate K D.1 qInf 0 - t2) hc hwrong

/-- GS20 Lemma 9 applies after reducing the two multiplication outputs to effective scalars. -/
theorem halving_effective_card_le_two (K : Constants C E) (D : C.Coalition)
    (lo hi lo' hi' : List E) (V q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 V 0 ≠
      (List.zipWith (· * ·) lo lo').sum + (List.zipWith (· * ·) hi hi').sum)
    (hlen : lo.length = hi.length ∧ lo'.length = hi'.length ∧ lo.length = lo'.length) :
    (univ.filter fun r : E =>
      interpolate K D.1 (fun i => q0 i + (V i + q2 i) * r + q2 i * r ^ 2) 0 =
        (List.zipWith (· * ·) (List.zipWith (fun a b => a + r * (a + b)) lo hi)
          (List.zipWith (fun a b => a + r * (a + b)) lo' hi')).sum).card ≤ 2 := by
  letI : CharP E 2 := charP_two
  simp_rw [interpolate_halvingClaim]
  simpa only [add_assoc, add_sub_cancel] using
    gs20_lemma9_halving_step lo hi lo' hi' (interpolate K D.1 V 0)
      (interpolate K D.1 q0 0 - (List.zipWith (· * ·) lo lo').sum)
      (interpolate K D.1 q2 0 -
        (List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum)
      hwrong hlen

/-- A fresh cached challenge contributes its exceptional set and the remaining continuation error. -/
theorem challengeQuery_step_soundness {β : Type} (prims : Primitives) (K : Constants C E)
    (tag label : ℕ) (coin : List E) (Ks : Finset HashOutput) (cache : HashCache C)
    (hfresh : cache (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v))) = none)
    (hexpand : ∀ key idx, cache (.expand key idx) ≠ none → key ∈ Ks)
    (bad : E → Prop) (m : ℕ) (hcard : (univ.filter bad).card ≤ m)
    (cont : Option E × HashCache C → ProbComp β) (accept : β → Prop) (ε : ℝ≥0∞)
    (hnext : ∀ p, p ∈ support ((simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache) →
      (∀ r, p.1 = some r → ¬ bad r) → Pr[accept | cont p] ≤ ε) :
    Pr[accept | (simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache >>= cont] ≤
      (Ks.card / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ)) + ε := by
  have hbad := challengeQuery_mem_le_of_fresh prims K tag label coin Ks cache hfresh hexpand (univ.filter bad)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbad
  have hbad' : Pr[fun p => ∃ r, bad r ∧ p.1 = some r |
      (simulateQ (localAnswer prims)
        (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache] ≤
      Ks.card / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ) := by
    refine hbad.trans ?_
    gcongr
  have h := probEvent_bind_le_add (mx := (simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache)
    (my := cont) (p := fun p => ¬ ∃ r, bad r ∧ p.1 = some r) (q := fun out => ¬ accept out)
    (by simpa using hbad') (fun p hs hp => by
      simpa using hnext p hs (fun r hr hb => hp ⟨r, hb, hr⟩))
  simpa using h

/-- Agreement and a rejecting ideal leak give an actual nonzero tuple error. -/
theorem multVerify_reject_wrong_tuple (D : C.Coalition)
    (inputs : C.Party → Option (List (Tuple C)))
    (hagree : MultVerifyAgree D inputs) (hreject : (multVerifyLeak D inputs).2.2 = false) :
    ∃ m < (firstInput inputs).length, ∃ g < (tupleAt inputs m).count,
      shareValue (tupleAt inputs m).z g -
        shareValue (tupleAt inputs m).x g * shareValue (tupleAt inputs m).y g ≠ 0 := by
  have hn : ¬ ∀ τ ∈ (List.range (firstInput inputs).length).map (tupleAt inputs),
      ∀ g < τ.count, shareValue τ.z g = shareValue τ.x g * shareValue τ.y g := by
    intro hc
    have ha : (multVerifyLeak D inputs).2.2 = true := by
      simp only [multVerifyLeak, decide_eq_true_eq]
      exact ⟨hagree, hc⟩
    exact Bool.false_ne_true (hreject.symm.trans ha)
  push Not at hn
  obtain ⟨τ, hτ, g, hg, hne⟩ := hn
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hτ
  exact ⟨m, List.mem_range.mp hm, g, hg, sub_ne_zero.mpr hne⟩

/-- A uniform coin is protected against every earlier counted query in an independent trace. -/
theorem independent_coin_trace_bound (K : Constants C E) (tag label : ℕ)
    (trace : ProbComp (List (Query C))) (q : ℕ)
    (htrace : ∀ l ∈ support trace, l.length ≤ q) :
    Pr[fun p : List (Query C) × E => Query.coinKey tag label (List.ofFn (K.encode p.2)) ∈ p.1 |
      (do let l ← trace; let r ← $ᵗ E; pure (l, r))] ≤ (q : ℝ≥0∞) / Fintype.card E :=
  independent_trace_guess_bound _ (coin_input_injective K tag label) trace q htrace

/-- The concrete final network execution can accept only at an effective error root. -/
theorem finalOpen_support_effective_root {Ia : Type} (prims : Primitives)
    (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (live : C.Party → Prop)
    (hlive : ∃ i, i ∉ D.1 ∧ live i) (wa wb a b d q0 q2 : C.Party → E) (r : E)
    (cache : HashCache C) (out : A.State × (C.Party → Option Unit))
    (hout : out ∈ support ((simulateQ (localAnswer prims)
      (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
        (fun i => if live i then finalOpenProgram K i
          (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r) else failure))).run' cache))
    (ha : ∃ i, out.2 i = some ()) :
    let I := fun f : C.Party → E => interpolate K D.1 f 0
    r * (I d - I a * I b) + (1 + r) * (I q0 - I wa * I wb) +
      r * (1 + r) * (I q2 - (I wa + I a) * (I wb + I b)) = 0 := by
  rw [finalOpen_round K D A fuel st live _ hlive] at hout
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind,
    simulateQ_pure, StateT.run_pure, map_pure, support_bind,
    Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨p, _, rfl⟩ := hout
  obtain ⟨i, hi⟩ := ha
  exact finalRoundOutputs_effective_root K D live p.1.2 wa wb a b d q0 q2 r i hi

/-- Soundness of the actual last challenge and opening, from arbitrary fixed pre-challenge shares. -/
theorem finalOpen_challenge_soundness {Ia : Type} (prims : Primitives)
    (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (live : C.Party → Prop) (hlive : ∃ i, i ∉ D.1 ∧ live i)
    (tag label : ℕ) (coin : List E) (Ks : Finset HashOutput) (cache : HashCache C)
    (hfresh : cache (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v))) = none)
    (hexpand : ∀ key idx, cache (.expand key idx) ≠ none → key ∈ Ks)
    (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0) :
    Pr[fun out : A.State × (C.Party → Option Unit) => ∃ i, out.2 i = some () |
      (simulateQ (localAnswer prims)
        (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache >>= fun p =>
      match p.1 with
      | none => pure (st, fun _ : C.Party => (none : Option Unit))
      | some r => (simulateQ (localAnswer prims)
          (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
            (fun i => if live i then finalOpenProgram K i
              (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r)
              else failure))).run' p.2] ≤
      Ks.card / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ) := by
  apply finalChallenge_adaptive_soundness prims K tag label coin Ks cache hfresh hexpand
    (interpolate K D.1 a 0) (interpolate K D.1 b 0) (interpolate K D.1 d 0)
    (interpolate K D.1 q0 0 - interpolate K D.1 wa 0 * interpolate K D.1 wb 0)
    (interpolate K D.1 q2 0 - (interpolate K D.1 wa 0 + interpolate K D.1 a 0) *
      (interpolate K D.1 wb 0 + interpolate K D.1 b 0)) hwrong
  intro p out hout ha
  rcases p with ⟨_ | r, cache'⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    simp at ha
  · exact ⟨r, rfl, finalOpen_support_effective_root prims K D A fuel st live hlive
      wa wb a b d q0 q2 r cache' out hout ha⟩

/-- The hash-cache entry introduced by a local query, when the query is counted. -/
def soundQueryProjection : (LocalSpec C).Domain → Option (Query C)
  | .inl _ => none
  | .inr (.inl q) => if IsFixed q then none else some q
  | .inr (.inr x) => some (.streamKey x.2.1)

lemma soundQueryProjection_counted (t : (LocalSpec C).Domain)
    (ht : (soundQueryProjection t).isSome) : Counted t := by
  rcases t with n | q | x
  · simp [soundQueryProjection] at ht
  · cases q <;> simp_all [soundQueryProjection, Counted, IsFixed]
  · trivial

lemma hashAnswer_sound_entries (prims : Primitives) (q : Query C) (cache : HashCache C)
    (p : HashOutput × HashCache C) (hp : p ∈ support ((hashAnswer prims q).run cache))
    (q' : Query C) (hq' : p.2 q' ≠ none) :
    cache q' ≠ none ∨ (q' = q ∧ ¬ IsFixed q) := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact Or.inl hq'
  · have he : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q) =
        hashAnswer prims q := (simulateQ_query _ _).trans (id_map _)
    exact (support_hashQuery_entries prims hq cache p (by rwa [he]) q' hq').imp_right (fun h => ⟨h, hq⟩)

lemma localAnswer_sound_covered (prims : Primitives) (cache : HashCache C)
    (l : List (Query C)) (hc : ∀ q, cache q ≠ none → q ∈ l)
    (t : (LocalSpec C).Domain) (p : (LocalSpec C).Range t × HashCache C)
    (hp : p ∈ support ((localAnswer prims t).run cache)) :
    ∀ q, p.2 q ≠ none → q ∈ (soundQueryProjection t).toList ++ l := by
  rcases t with n | q | x
  · simp [localAnswer, unifFwdImpl] at hp
    obtain ⟨_, rfl⟩ := hp
    simpa only [soundQueryProjection, Option.toList_none, List.nil_append] using hc
  · intro q' hq'
    rcases hashAnswer_sound_entries prims q cache p hp q' hq' with hs | ⟨rfl, hq⟩
    · exact List.mem_append_right _ (hc q' hs)
    · simp [soundQueryProjection, hq]
  · simp [localAnswer, prgAnswer] at hp
    obtain ⟨p, hp, rfl⟩ := hp
    intro q' hq'
    rcases hashAnswer_sound_entries prims (.streamKey x.2.1) cache p hp q' hq' with hs | ⟨rfl, _⟩
    · exact List.mem_append_right _ (hc q' hs)
    · simp [soundQueryProjection]

theorem projectQueries_sound_covered {α : Type} (prims : Primitives)
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (l : List (Query C))
    (hc : ∀ q, cache q ≠ none → q ∈ l) (z : α × HashCache C × List (Query C))
    (hz : z ∈ support ((simulateQ (projectQueries (localAnswer prims) soundQueryProjection) oa).run (cache, l))) :
    ∀ q, z.2.1 q ≠ none → q ∈ z.2.2 := by
  induction oa using OracleComp.inductionOn generalizing cache l z with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hc
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, projectQueries_run,
      bind_map_left, support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact ih p.1 p.2 ((soundQueryProjection t).toList ++ l)
      (localAnswer_sound_covered prims cache l hc t p hp) z hz

/-- Every cache reached by an adaptive local prefix has a cover bounded by its counted queries. -/
theorem localProgram_sound_covered {α : Type} (prims : Primitives)
    (oa : OracleComp (LocalSpec C) α) (q : ℕ) (hq : IsQueryBoundP oa Counted q)
    (cache : HashCache C) (seen : Finset (Query C)) (hc : ∀ k, cache k ≠ none → k ∈ seen)
    (p : α × HashCache C) (hp : p ∈ support ((simulateQ (localAnswer prims) oa).run cache)) :
    ∃ seen' : Finset (Query C), (∀ k, p.2 k ≠ none → k ∈ seen') ∧ seen'.card ≤ seen.card + q := by
  rw [← projectQueries_forget (localAnswer prims) soundQueryProjection oa cache seen.toList, support_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  refine ⟨z.2.2.toFinset, ?_, ?_⟩
  · intro k hk
    exact List.mem_toFinset.mpr (projectQueries_sound_covered prims oa cache seen.toList
      (fun k hk => Finset.mem_toList.mpr (hc k hk)) z hz k hk)
  · have hb := projectQueries_length (localAnswer prims) Counted soundQueryProjection
      soundQueryProjection_counted hq cache seen.toList hz
    exact (List.toFinset_card_le z.2.2).trans (by simpa using hb)

/-- Future coin inputs can have been queried by the adversary. Honest expansions are
tracked by key, so their many indices cost only one key per coin. -/
def SoundCache (L : ℕ) (cache : HashCache C) (seen : Finset (Query C))
    (keys : Finset HashOutput) : Prop :=
  (∀ tag label bits, L ≤ label → cache (.coinKey tag label bits) ≠ none →
    Query.coinKey tag label bits ∈ seen) ∧
  (∀ key idx, cache (.expand key idx) ≠ none → key ∈ keys ∨ Query.expand key idx ∈ seen)

lemma SoundCache.of_covered (L : ℕ) (cache : HashCache C) (seen : Finset (Query C))
    (hc : ∀ k, cache k ≠ none → k ∈ seen) : SoundCache L cache seen ∅ := by
  exact ⟨fun _ _ _ _ h => hc _ h, fun _ _ h => Or.inr (hc _ h)⟩

lemma SoundCache.fresh {L : ℕ} {cache : HashCache C} {seen : Finset (Query C)}
    {keys : Finset HashOutput} (hc : SoundCache L cache seen keys)
    (tag label : ℕ) (bits : List Bit) (hL : L ≤ label)
    (hn : Query.coinKey tag label bits ∉ seen) : cache (.coinKey tag label bits) = none := by
  by_contra h
  exact hn (hc.1 tag label bits hL h)

def soundExpansionKey : Query C → HashOutput
  | .expand key _ => key
  | _ => default

lemma SoundCache.expansions {L : ℕ} {cache : HashCache C} {seen : Finset (Query C)}
    {keys : Finset HashOutput} (hc : SoundCache L cache seen keys) :
    ∀ key idx, cache (.expand key idx) ≠ none → key ∈ keys ∪ seen.image soundExpansionKey := by
  intro key idx h
  rcases hc.2 key idx h with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨.expand key idx, h, rfl⟩)

lemma soundExpansionKeys_card (seen : Finset (Query C)) (keys : Finset HashOutput) :
    (keys ∪ seen.image soundExpansionKey).card ≤ keys.card + seen.card :=
  Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left (Finset.card_image_le) _)

theorem SoundCache.challenge (prims : Primitives) (K : Constants C E)
    {L : ℕ} {cache : HashCache C} {seen : Finset (Query C)} {keys : Finset HashOutput}
    (hc : SoundCache L cache seen keys) (tag label : ℕ) (v : List E) (hL : L ≤ label)
    (p : Option E × HashCache C)
    (hp : p ∈ support ((simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag label v) (LocalSpec C))).run cache)) :
    ∃ key, SoundCache (label + 1) p.2 seen (insert key keys) := by
  rw [simulateQ_localAnswer_liftComp, challengeQuery, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hp
  obtain ⟨⟨key, cache'⟩, hkey, hp⟩ := hp
  have hq : ¬ IsFixed (Query.coinKey (C := C) tag label (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  have hk := support_hashQuery_entries prims hq cache _ hkey
  have he := support_findChallenge_entries prims K key _ _ _ _ hp
  refine ⟨key, ?_, ?_⟩
  · intro tg lab bits hl hb
    rcases he _ hb with h | ⟨idx, h⟩
    · rcases hk _ h with h | h
      · exact hc.1 tg lab bits (by omega) h
      · have := (Query.coinKey.inj h).2.1
        omega
    · cases h
  · intro k idx hb
    rcases he _ hb with h | ⟨idx', h⟩
    · rcases hk _ h with h | h
      · exact (hc.2 k idx h).imp_left (Finset.mem_insert_of_mem)
      · cases h
    · have hkk := (Query.expand.inj h).1
      exact Or.inl (hkk ▸ Finset.mem_insert_self _ _)

lemma localAnswer_sound_entries (prims : Primitives) (cache : HashCache C)
    (t : (LocalSpec C).Domain) (p : (LocalSpec C).Range t × HashCache C)
    (hp : p ∈ support ((localAnswer prims t).run cache)) :
    ∀ q, p.2 q ≠ none → cache q ≠ none ∨ q ∈ (soundQueryProjection t).toList := by
  rcases t with n | q | x
  · simp [localAnswer, unifFwdImpl] at hp
    obtain ⟨_, rfl⟩ := hp
    exact fun _ h => Or.inl h
  · intro q' hq'
    rcases hashAnswer_sound_entries prims q cache p hp q' hq' with hs | ⟨rfl, hq⟩
    · exact Or.inl hs
    · exact Or.inr (by simp [soundQueryProjection, hq])
  · simp [localAnswer, prgAnswer] at hp
    obtain ⟨p, hp, rfl⟩ := hp
    intro q' hq'
    rcases hashAnswer_sound_entries prims (.streamKey x.2.1) cache p hp q' hq' with hs | ⟨rfl, _⟩
    · exact Or.inl hs
    · exact Or.inr (by simp [soundQueryProjection])

theorem projectQueries_sound_entries {α : Type} (prims : Primitives)
    (oa : OracleComp (LocalSpec C) α) (base : Query C → Prop)
    (cache : HashCache C) (l : List (Query C)) (hc : ∀ q, cache q ≠ none → base q ∨ q ∈ l)
    (z : α × HashCache C × List (Query C))
    (hz : z ∈ support ((simulateQ (projectQueries (localAnswer prims) soundQueryProjection) oa).run (cache, l))) :
    ∀ q, z.2.1 q ≠ none → base q ∨ q ∈ z.2.2 := by
  induction oa using OracleComp.inductionOn generalizing cache l z with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hc
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, projectQueries_run,
      bind_map_left, support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨p, hp, hz⟩ := hz
    apply ih p.1 p.2 ((soundQueryProjection t).toList ++ l) _ z hz
    intro q hq
    rcases localAnswer_sound_entries prims cache t p hp q hq with h | h
    · exact (hc q h).imp_right (List.mem_append_right _)
    · exact Or.inr (List.mem_append_left _ h)

theorem SoundCache.local {α : Type} (prims : Primitives)
    (oa : OracleComp (LocalSpec C) α) (q : ℕ) (hq : IsQueryBoundP oa Counted q)
    {L : ℕ} {cache : HashCache C} {seen : Finset (Query C)} {keys : Finset HashOutput}
    (hc : SoundCache L cache seen keys)
    (p : α × HashCache C) (hp : p ∈ support ((simulateQ (localAnswer prims) oa).run cache)) :
    ∃ seen' : Finset (Query C), SoundCache L p.2 seen' keys ∧ seen'.card ≤ seen.card + q := by
  rw [← projectQueries_forget (localAnswer prims) soundQueryProjection oa cache [], support_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  have he := projectQueries_sound_entries prims oa (fun k => cache k ≠ none) cache []
    (fun _ h => Or.inl h) z hz
  have hlog := projectQueries_length (localAnswer prims) Counted soundQueryProjection
    soundQueryProjection_counted hq cache [] hz
  refine ⟨seen ∪ z.2.2.toFinset, ⟨?_, ?_⟩, ?_⟩
  · intro tag label bits hL hk
    rcases he _ hk with h | h
    · exact Finset.mem_union_left _ (hc.1 _ _ _ hL h)
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h)
  · intro key idx hk
    rcases he _ hk with h | h
    · exact (hc.2 _ _ h).imp_right (Finset.mem_union_left _)
    · exact Or.inr (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left
      ((List.toFinset_card_le _).trans (by simpa using hlog)) _)

lemma coinInput_one_injective (K : Constants C E) (tag label : ℕ) :
    Function.Injective (fun v : Fin 1 → E => Query.coinKey (C := C) tag label
      ((List.ofFn v).flatMap fun v => List.ofFn (K.encode v))) := by
  intro a b h
  have he := (Query.coinKey.inj h).2.2
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at he
  have hab := K.encode.injective (List.ofFn_injective he)
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using hab

/-- One whole coin: earlier input guesses, cached expansion keys, exceptional challenges,
and the continuation are charged separately. -/
theorem sound_coin_challenge {β : Type} (prims : Primitives) (K : Constants C E)
    (n : ℕ) (hn : n = 1) (tag L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (bad : E → Prop) (m : ℕ)
    (hcard : (univ.filter bad).card ≤ m)
    (cont : (Fin n → E) → Option E × HashCache C → ProbComp β)
    (accept : β → Prop) (ε : ℝ≥0∞)
    (hnext : ∀ v p, p ∈ support ((simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag L (List.ofFn v)) (LocalSpec C))).run cache) →
      (∀ r, p.1 = some r → ¬ bad r) → Pr[accept | cont v p] ≤ ε) :
    Pr[accept | (do
      let v ← $ᵗ (Fin n → E)
      (simulateQ (localAnswer prims)
        (liftComp (challengeQuery K tag L (List.ofFn v)) (LocalSpec C))).run cache >>= cont v)] ≤
      seen.card / Fintype.card E +
        ((keys.card + seen.card) / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ) + ε) := by
  let fresh := fun v : Fin n → E => Query.coinKey tag L
    ((List.ofFn v).flatMap fun v => List.ofFn (K.encode v)) ∉ seen
  have hinj : Function.Injective (fun v : Fin n → E => Query.coinKey (C := C) tag L
      ((List.ofFn v).flatMap fun v => List.ofFn (K.encode v))) := by
    subst n
    exact coinInput_one_injective K tag L
  have hguess : Pr[fun v => ¬ fresh v | $ᵗ (Fin n → E)] ≤
      seen.card / (Fintype.card E : ℝ≥0∞) := by
    simpa only [fresh, not_not, Fintype.card_fun, Fintype.card_fin, hn, pow_one] using
      probEvent_uniform_injective_mem _ hinj seen
  have h := probEvent_bind_le_add (p := fresh) (q := fun b => ¬ accept b)
    (my := fun v => (simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag L (List.ofFn v)) (LocalSpec C))).run cache >>= cont v)
    (ε₂ := (keys.card + seen.card) / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ) + ε)
    hguess (fun v _ hv => ?_)
  · simpa using h
  · have hb := challengeQuery_step_soundness prims K tag L (List.ofFn v)
      (keys ∪ seen.image soundExpansionKey) cache (hc.fresh _ _ _ le_rfl hv) hc.expansions
      bad m hcard (cont v) accept ε (hnext v)
    simp only [not_not]
    refine hb.trans ?_
    gcongr
    exact_mod_cast soundExpansionKeys_card seen keys

def soundChallengeNext {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (hs : C.Party → RunState C)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
    (p : A.State × Finset C.Party) (r : Option E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option Unit)) :=
  executePhase localRoles D A (checkFunctionalities K) fuel p.1
    (fun i => match r with
      | some r => if i ∈ p.2 then (g i r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure
      | none => failure)

lemma soundChallengeNext_none {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (hs : C.Party → RunState C)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit) (p : A.State × Finset C.Party) :
    soundChallengeNext K D A fuel hs g p none = pure (p.1, fun _ => none) := by
  exact executePhase_failure D A _ _ _

lemma soundChallengeNext_missing {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (hs : C.Party → RunState C)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit) (p : A.State × Finset C.Party)
    (hmiss : ¬ ∃ i, i ∉ D.1 ∧ i ∈ p.2) (r : Option E) :
    soundChallengeNext K D A fuel hs g p r = pure (p.1, fun _ => none) := by
  unfold soundChallengeNext
  rw [executePhase_congr_honest D A _ _ p.1 _ (fun _ => failure), executePhase_failure]
  intro i hi
  have hn : i ∉ p.2 := fun h => hmiss ⟨i, hi, h⟩
  cases r <;> simp [hn]

theorem sound_afterChallenge {Ia : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
    (v : List E) (p : A.State × Finset C.Party) :
    SameLocalOutput prims
      (executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterChallenge K (hs i) (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)))
      (liftComp (challengeQuery K tag L v) (LocalSpec C) >>= soundChallengeNext K D A fuel hs g p) := by
  by_cases hp : ∃ i, i ∉ D.1 ∧ i ∈ p.2
  · exact SameLocalOutput.of_sameRun prims
      (executePhase_afterChallenge_common' prims K D A fuel p.1 hs tag L htag v p.2 hp g)
  · have he : executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterChallenge K (hs i) (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)) =
        pure (p.1, fun _ : C.Party => (none : Option Unit)) := by
      rw [executePhase_congr_honest D A _ _ p.1 _ (fun _ => failure), executePhase_failure]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ p.2) := fun h => hp ⟨i, h⟩
      simp [hn, afterChallenge]
    have hg : soundChallengeNext K D A fuel hs g p =
        fun _ => pure (p.1, fun _ : C.Party => (none : Option Unit)) :=
      funext (soundChallengeNext_missing K D A fuel hs g p hp)
    rw [he, hg]
    intro cache
    exact (local_prefetch_output prims _ (pure (p.1, fun _ : C.Party => (none : Option Unit))) cache).symm

set_option maxHeartbeats 1000000 in
theorem sound_challenge_normalize {Ia : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (live : C.Party → Prop) [DecidablePred live]
    (hall : ∀ i, i ∉ D.1 → live i) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit) :
    SameLocalOutput prims
      (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
        (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i) else failure))
      (do
        let v ← liftComp ($ᵗ (Fin (firstInput fun i : C.Party => if i ∈ D.1 then
          (none : Option ℕ) else some 1) → E)) (LocalSpec C)
        let r ← liftComp (challengeQuery K tag L (List.ofFn v)) (LocalSpec C)
        let p ← (leftAdversary (leftAdversary A)).answer st (List.ofFn v)
        soundChallengeNext K D A fuel hs g p r) := by
  rw [executePhase_challenge_live K D A fuel st live hs g, if_pos hall,
    runFunctionality_coin_local D (leftAdversary (leftAdversary A)) st _
      (by intro i hi; simp [hi])]
  simp only [bind_assoc, pure_bind]
  refine SameLocalOutput.bind_right prims _ ?_
  intro v
  have h₁ := SameLocalOutput.bind_right prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (fun p => sound_afterChallenge prims K D A fuel hs tag L htag g (List.ofFn v) p)
  have h₂ := SameLocalOutput.of_sameRun prims (sameRun_swap prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (liftComp (challengeQuery K tag L (List.ofFn v)) (LocalSpec C))
    (fun p r => soundChallengeNext K D A fuel hs g p r))
  intro cache
  simpa only [leftAdversary, bind_assoc, pure_bind] using (h₁ cache).trans (h₂ cache)

lemma sound_coinReply_bound {Ia : Type} (A : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step) (st : A.State) (v : List E) :
    IsQueryBoundP ((leftAdversary (leftAdversary A)).answer st v) Counted step := by
  dsimp only [leftAdversary]
  simp only [bind_assoc, pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

set_option maxHeartbeats 1000000 in
theorem sound_challenge_phase {Ia : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (live : C.Party → Prop) [DecidablePred live] (hall : ∀ i, i ∉ D.1 → live i)
    (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (bad : E → Prop) (m : ℕ)
    (hcard : (univ.filter bad).card ≤ m) (ε : ℝ≥0∞)
    (hnext : ∀ p r key cache' seen', SoundCache (L + 1) cache' seen' (insert key keys) →
      seen'.card ≤ seen.card + step → ¬ bad r →
      Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
        (simulateQ (localAnswer prims) (soundChallengeNext K D A fuel hs g p (some r))).run' cache'] ≤ ε) :
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
          (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i)
            else failure))).run' cache] ≤
      seen.card / Fintype.card E +
        ((keys.card + seen.card) / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ) + ε) := by
  rw [probEvent_def, sound_challenge_normalize prims K D A fuel st live hall hs tag L htag g cache,
    ← probEvent_def]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, run_liftComp_prob, bind_map_left]
  apply sound_coin_challenge prims K _ (firstInput_honest_const D 1) tag L cache seen keys hc bad m hcard
  intro v p hp hgood
  obtain ⟨key, hcache⟩ := hc.challenge prims K tag L (List.ofFn v) le_rfl p hp
  apply probEvent_bind_le_of_forall_le
  intro ans hans
  have hans' : ans ∈ support ((simulateQ (localAnswer prims)
      ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))).run p.2) := by
    simpa only [simulateQ_bind, StateT.run_bind] using hans
  obtain ⟨seen', hcache', hcard'⟩ := hcache.local prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v)) step
    (sound_coinReply_bound A step ha st _) ans hans'
  cases hr : p.1 with
  | none => simp [soundChallengeNext_none]
  | some r =>
    have h := hnext ans.1 r key ans.2 seen' hcache' hcard' (hgood r hr)
    simpa only [hr, StateT.run'_eq] using h

/-- The padded halving vectors have the same quadratic identity after interpolation. -/
theorem sound_halvFold_card (K : Constants C E) (D : C.Coalition) (len : ℕ)
    (A B : C.Party → ℕ → E) (V q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 V 0 ≠ ∑ k ∈ range len,
      interpolate K D.1 (fun i => A i k) 0 * interpolate K D.1 (fun i => B i k) 0) :
    (univ.filter fun r : E =>
      interpolate K D.1 (fun i => q0 i + (V i + q2 i) * r + q2 i * r ^ 2) 0 =
        ∑ k ∈ range (halvedLength len),
          interpolate K D.1 (fun i => halvFold len r (A i) k) 0 *
          interpolate K D.1 (fun i => halvFold len r (B i) k) 0).card ≤ 2 := by
  letI : CharP E 2 := charP_two
  let a := fun k => interpolate K D.1 (fun i => A i k) 0
  let b := fun k => interpolate K D.1 (fun i => B i k) 0
  let hi := fun (v : ℕ → E) k => if k + halvedLength len < len then v (k + halvedLength len) else 0
  let t0 := ∑ k ∈ range (halvedLength len), a k * b k
  let t2 := ∑ k ∈ range (halvedLength len), (a k + hi a k) * (b k + hi b k)
  have hid (r : E) : (∑ k ∈ range (halvedLength len), halvFold len r a k * halvFold len r b k) =
      t0 + ((∑ k ∈ range len, a k * b k) + t2) * r + t2 * r ^ 2 := by
    simpa only [halvFold, t0, t2, hi, sum_range_padded a b len] using
      sum_range_halving_fold a b (hi a) (hi b) (halvedLength len) r
  simp_rw [interpolate_halvingClaim, interpolate_halvFold]
  apply card_filter_le_two_of_quadratic (interpolate K D.1 q0 0 - t0)
    (interpolate K D.1 V 0 + interpolate K D.1 q2 0 - ((∑ k ∈ range len, a k * b k) + t2))
    (interpolate K D.1 q2 0 - t2)
  · by_contra! h
    apply hwrong
    change interpolate K D.1 V 0 = ∑ k ∈ range len, a k * b k
    linear_combination h.2.1 - h.2.2
  · intro r hr
    change interpolate K D.1 q0 0 + (interpolate K D.1 V 0 + interpolate K D.1 q2 0) * r +
      interpolate K D.1 q2 0 * r ^ 2 = ∑ k ∈ range (halvedLength len),
        halvFold len r a k * halvFold len r b k at hr
    rw [hid] at hr
    linear_combination hr

/-- No choice of the opening messages can make a nonroot final challenge accept. -/
theorem sound_finalChallenge_phase {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) :
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 2) st
          (fun i => if live i then
            (finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)).run' (hs i)
            else failure))).run' cache] ≤
      seen.card / Fintype.card E +
        ((keys.card + seen.card) / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ)) := by
  classical
  let I := fun f : C.Party → E => interpolate K D.1 f 0
  let bad := fun r => r * (I d - I a * I b) + (1 + r) * (I q0 - I wa * I wb) +
    r * (1 + r) * (I q2 - (I wa + I a) * (I wb + I b)) = 0
  change Pr[_ | (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) ((fuel + 1) + 1) st
      (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= fun r =>
        StateT.lift (finalOpenProgram K i
          (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r))).run' (hs i)
        else failure))).run' cache] ≤ _
  by_cases hall : ∀ i, i ∉ D.1 → live i
  · have hcard : (univ.filter bad).card ≤ 2 :=
      final_residual_card_le_two (I a) (I b) (I d) (I q0 - I wa * I wb)
        (I q2 - (I wa + I a) * (I wb + I b)) hwrong
    simpa only [add_zero, Nat.cast_ofNat] using sound_challenge_phase prims K D A (fuel + 1) step ha st live hall
      hs tag L htag _ cache seen keys hc bad 2 (by convert hcard using 1; congr 2) 0 (by
        intro p r key cache' seen' hc' hs' hgood
        by_cases hlive : ∃ i, i ∉ D.1 ∧ i ∈ p.2
        · apply le_of_eq
          apply probEvent_eq_zero
          intro out hout hout'
          apply hgood
          apply finalOpen_support_effective_root prims K D A fuel p.1 (· ∈ p.2) hlive
            wa wb a b d q0 q2 r cache' out
          · simp only [soundChallengeNext, StateT.run'_eq, StateT.run_lift,
              map_bind, map_pure, bind_pure] at hout
            convert hout using 1; congr 7
            funext i
            by_cases hi : i ∈ p.2 <;> simp [hi]
          · exact ⟨hout'.choose, hout'.choose_spec.2⟩
        · rw [soundChallengeNext_missing K D A _ _ _ p hlive]
          simp)
  · rw [executePhase_challenge_live, if_neg hall]
    simp

lemma SoundCache.mono_label {L L' : ℕ} {cache : HashCache C} {seen : Finset (Query C)}
    {keys : Finset HashOutput} (hc : SoundCache L cache seen keys) (hL : L ≤ L') :
    SoundCache L' cache seen keys :=
  ⟨fun _ _ _ h => hc.1 _ _ _ (hL.trans h), hc.2⟩

/-- A digest computation cannot populate either kind of challenge-cache entry. -/
theorem SoundCache.digest (prims : Primitives) {L : ℕ} {cache : HashCache C}
    {seen : Finset (Query C)} {keys : Finset HashOutput} (hc : SoundCache L cache seen keys)
    (salt history : List Bit) (p : HashOutput × HashCache C)
    (hp : p ∈ support ((simulateQ (localAnswer prims)
      (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C))).run cache)) :
    SoundCache L p.2 seen keys := by
  simp only [oneDigestQuery, liftComp_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_localAnswer_hash, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  have hh := support_hashQuery_entries prims (q := Query.history history)
    (by rintro ⟨_, h, _⟩; cases h) cache q (by simpa [hashQuery] using hq)
  have hd := support_hashQuery_entries prims (q := Query.digest salt q.1)
    (by rintro ⟨_, h, _⟩; cases h) q.2 p (by simpa [hashQuery] using hp)
  constructor
  · intro tag label bits hl h
    rcases hd _ h with h | h
    · rcases hh _ h with h | h
      · exact hc.1 _ _ _ hl h
      · cases h
    · cases h
  · intro key idx h
    rcases hd _ h with h | h
    · rcases hh _ h with h | h
      · exact hc.2 _ _ h
      · cases h
    · cases h

/-- Cache invariants compose through arbitrary local sequencing. -/
theorem sound_preserves_bind {α β : Type} (prims : Primitives) (P : HashCache C → Prop)
    (oa : OracleComp (LocalSpec C) α) (f : α → OracleComp (LocalSpec C) β)
    (ha : ∀ cache, P cache → ∀ p ∈ support ((simulateQ (localAnswer prims) oa).run cache), P p.2)
    (hf : ∀ a cache, P cache → ∀ p ∈ support ((simulateQ (localAnswer prims) (f a)).run cache), P p.2)
    (cache : HashCache C) (hc : P cache)
    (p : β × HashCache C) (hp : p ∈ support ((simulateQ (localAnswer prims) (oa >>= f)).run cache)) :
    P p.2 := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  exact hf q.1 q.2 (ha cache hc q hq) p hp

lemma sound_preserves_pure {α : Type} (prims : Primitives) (P : HashCache C → Prop)
    (a : α) (cache : HashCache C) (hc : P cache)
    (p : α × HashCache C) (hp : p ∈ support ((simulateQ (localAnswer prims) (pure a)).run cache)) :
    P p.2 := by
  simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hp ▸ hc

lemma sound_preserves_sequenceFin {α : Type} (prims : Primitives) (P : HashCache C → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) α),
    (∀ i cache, P cache → ∀ p ∈ support ((simulateQ (localAnswer prims) (f i)).run cache), P p.2) →
    ∀ cache, P cache → ∀ p ∈ support ((simulateQ (localAnswer prims) (Concrete.sequenceFin f)).run cache), P p.2
  | 0, _, _ => sound_preserves_pure prims P _
  | n + 1, f, hf => sound_preserves_bind prims P _ _ (hf 0)
      (fun _ => sound_preserves_bind prims P _ _
        (sound_preserves_sequenceFin prims P (fun i : Fin n => f i.succ) (fun i => hf i.succ))
        (fun _ => sound_preserves_pure prims P _))

lemma sound_preserves_queryColumns {α β : Type} {n : ℕ} (prims : Primitives)
    (P : HashCache C → Prop) (f : Fin n → α → OracleComp (LocalSpec C) β)
    (hf : ∀ i a cache, P cache → ∀ p ∈ support ((simulateQ (localAnswer prims) (f i a)).run cache), P p.2) :
    ∀ xs cache, P cache → ∀ p ∈ support ((simulateQ (localAnswer prims) (queryColumns f xs)).run cache), P p.2
  | [] => sound_preserves_pure prims P _
  | a :: as => sound_preserves_bind prims P _ _
      (sound_preserves_sequenceFin prims P _ (fun i => hf i a))
      (fun _ => sound_preserves_bind prims P _ _ (sound_preserves_queryColumns prims P f hf as)
        (fun _ => sound_preserves_pure prims P _))

lemma SoundCache.digestColumns (prims : Primitives) {L : ℕ} {cache : HashCache C}
    {seen : Finset (Query C)} {keys : Finset HashOutput} (hc : SoundCache L cache seen keys)
    (D : C.Coalition) (salts : C.Party → Shares C Bit) (history : C.Party → C.Term → List Bit)
    (p : (C.Party → List HashOutput) × HashCache C)
    (hp : p ∈ support ((simulateQ (localAnswer prims)
      (queryColumns (fun i T => honestDigestColumn D T salts history i) C.terms)).run cache)) :
    SoundCache L p.2 seen keys := by
  apply sound_preserves_queryColumns prims (fun c => SoundCache L c seen keys) _ _ _ cache hc p hp
  intro i T cache hc p hp
  unfold honestDigestColumn at hp
  split_ifs at hp with h
  · exact hc.digest prims _ _ p hp
  · exact sound_preserves_pure prims (fun c => SoundCache L c seen keys) _ cache hc p hp

/-- A counted adversarial prefix spends only its own query budget. -/
theorem sound_prefix {α β : Type} (prims : Primitives)
    (oa : OracleComp (LocalSpec C) α) (f : α → OracleComp (LocalSpec C) β)
    (step : ℕ) (hq : IsQueryBoundP oa Counted step)
    (L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (accept : β → Prop) (ε : ℝ≥0∞)
    (h : ∀ a cache' seen', SoundCache L cache' seen' keys → seen'.card ≤ seen.card + step →
      Pr[accept | (simulateQ (localAnswer prims) (f a)).run' cache'] ≤ ε) :
    Pr[accept | (simulateQ (localAnswer prims) (oa >>= f)).run' cache] ≤ ε := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply probEvent_bind_le_of_forall_le
  intro p hp
  obtain ⟨seen', hc', hn⟩ := hc.local prims oa step hq p hp
  exact h p.1 p.2 seen' hc' hn

lemma sound_sample {α β : Type} [SampleableType α] (prims : Primitives)
    (f : α → OracleComp (LocalSpec C) β) (cache : HashCache C) (accept : β → Prop) (ε : ℝ≥0∞)
    (h : ∀ a, Pr[accept | (simulateQ (localAnswer prims) (f a)).run' cache] ≤ ε) :
    Pr[accept | (simulateQ (localAnswer prims) (liftComp ($ᵗ α) (LocalSpec C) >>= f)).run' cache] ≤ ε := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, run_liftComp_prob, bind_map_left]
  exact probEvent_bind_le_of_forall_le (fun a _ => h a)

/-- The common per-challenge error, with global query and key bounds. -/
def soundError (E : Type) [Fintype E] (q H m : ℕ) : ℝ≥0∞ :=
  q / Fintype.card E + ((H + q : ℕ) / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ))

lemma soundError_mono (q H m : ℕ) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hs : seen.card ≤ q) (hk : keys.card ≤ H) :
    (seen.card / Fintype.card E +
      ((keys.card + seen.card) / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ)) : ℝ≥0∞) ≤
        soundError E q H m := by
  unfold soundError
  push_cast
  gcongr

set_option maxHeartbeats 1000000 in
/-- Salts and digest messages leave the final scalar test as the only accepting route. -/
theorem sound_digest_phase {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step q H : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (salts : C.Party → Shares C Bit) (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (hq : seen.card + step ≤ q) (hk : keys.card ≤ H) :
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 3) st
          (fun i => (compareDigests (localContext i) (salts i) >>= fun _ =>
            finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)).run' (hs i)))).run' cache] ≤
      soundError E q H 2 := by
  have he := SameLocalOutput.of_sameRun prims (executePhase_digestColumns prims K D A (fuel + 3)
    st salts hs (fun i _ => finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)))
  rw [probEvent_def, he cache, ← probEvent_def]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply probEvent_bind_le_of_forall_le
  intro ds hds
  have hc' := hc.digestColumns prims D salts (fun i => (hs i).history) ds hds
  change Pr[_ | (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) ((fuel + 2) + 1) st _)).run' ds.2] ≤ _
  rw [executePhase_afterDigests_round]
  apply sound_prefix prims _ _ step (hr st _) L ds.2 seen keys hc'
  intro p cache' seen' hc'' hseen
  exact (sound_finalChallenge_phase prims K D A fuel step ha p.1 _ hs tag L htag
    wa wb a b d q0 q2 hwrong cache' seen' keys hc'').trans
    (soundError_mono (E := E) q H 2 seen' keys (by omega) hk)

set_option maxHeartbeats 1000000 in
theorem sound_salt_phase {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step q H : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (hq : seen.card + 2 * step ≤ q) (hk : keys.card ≤ H) :
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 4) st
          (fun i => ((hybridCheckGadgets K i).randBits 256 >>= fun salts =>
            compareDigests (localContext i) salts.1 >>= fun _ =>
            finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)).run' (hs i)))).run' cache] ≤
      soundError E q H 2 := by
  have he := SameLocalOutput.of_sameRun prims (executePhase_randBits_first prims K D A (fuel + 3)
    st 256 hs (fun i salts => compareDigests (localContext i) salts >>= fun _ =>
      finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)))
  rw [probEvent_def, he cache, ← probEvent_def]
  apply sound_prefix prims _ _ step (saltReply_queryBound A st step ha) L cache seen keys hc
  intro p cache' seen' hc' hseen
  apply sound_sample prims
  intro fresh
  apply sound_digest_phase prims K D A fuel step q H hr ha p.1 _ tag (L + 1)
    (fun i hi => by simp [htag i hi]) _ wa wb a b d q0 q2 hwrong cache' seen' keys
    (hc'.mono_label (by omega)) (by omega) hk

lemma sound_maskReply_bound {Ia : Type} (A : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step) (st : A.State) :
    IsQueryBoundP ((leftAdversary (rightAdversary A)).answer st ()) Counted step := by
  dsimp only [leftAdversary, rightAdversary]
  simp only [bind_assoc, pure_bind]
  simpa using ha st (.inr (.inl ()))

lemma sound_extendReply_bound {Ia : Type} (A : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step) (st : A.State)
    (view : C.Party → List (Product C E)) :
    IsQueryBoundP ((rightAdversary (leftAdversary A)).answer st view) Counted step := by
  dsimp only [leftAdversary, rightAdversary]
  simp only [bind_assoc, pure_bind]
  simpa using ha st (.inl (.inr view))

set_option maxHeartbeats 1000000 in
/-- The complete randomization, salts, digests, challenge, and final opening segment. -/
theorem sound_finalStep {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step q H : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (Av Bv : C.Party → ℕ → E) (V : C.Party → E)
    (hwrong : interpolate K D.1 V 0 ≠
      interpolate K D.1 (fun i => Av i 0) 0 * interpolate K D.1 (fun i => Bv i 0) 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (hq : seen.card + 4 * step ≤ q) (hk : keys.card ≤ H) :
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 6) st
          (fun i => if live i then
            (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i)
            else failure))).run' cache] ≤ soundError E q H 2 := by
  by_cases hall : ∀ i, i ∉ D.1 → live i
  · rw [executePhase_congr_honest D A _ _ st _
      (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i))
      (fun i hi => if_pos (hall i hi))]
    have he := SameLocalOutput.of_sameRun prims (finalStep_masks prims K D A (fuel + 4) st Av Bv V hs)
    rw [probEvent_def, he cache, ← probEvent_def]
    apply sound_prefix prims _ _ step (sound_maskReply_bound A step ha st) L cache seen keys hc
    intro p cache1 seen1 hc1 hn1
    apply sound_prefix prims _ _ step (sound_extendReply_bound A step ha _ _) L cache1 seen1 keys hc1
    intro pa cache2 seen2 hc2 hn2
    apply sound_sample prims
    intro w
    apply sound_sample prims
    intro z
    by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
    · rw [finalMasked_all K D A _ _ _ _ _ _ _ _ _ _ _ _ _ hrec]
      exact sound_salt_phase prims K D A fuel step q H hr ha pa.1 _ tag (L + 2)
        (fun i hi => by simp [finalHs, finalState, htag i hi]) _ _ _ _ _ _ _ hwrong cache2 seen2 keys
        (hc2.mono_label (by omega)) (by omega) hk
    · rw [show fuel + 4 = (fuel + 3) + 1 by omega,
        finalMasked_missing K D A _ _ _ _ _ _ _ _ _ _ _ _ _ (by push Not at hrec; exact hrec)]
      simp
  · rw [show fuel + 6 = (fuel + 5) + 1 by omega,
      finalStep_missing K D A _ _ _ _ _ _ _ (by push Not at hall; exact hall)]
    simp

/-- Soundness invariant for a remaining halving suffix. -/
def SoundHalvRest {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q H width n j F : ℕ) : Prop :=
  ∀ (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C) (tag L : ℕ),
    (∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L) →
    ∀ (A B : C.Party → ℕ → E) (V : C.Party → E),
    interpolate K D.1 V 0 ≠ ∑ k ∈ range (halvedLength^[j] width),
      interpolate K D.1 (fun i => A i k) 0 * interpolate K D.1 (fun i => B i k) 0 →
    ∀ (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput),
    SoundCache L cache seen keys → seen.card + (2 * n + 4) * step ≤ q → keys.card + n ≤ H →
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if live i then (halvProg K width n j (A i) (B i) (V i) i).run' (hs i)
            else failure))).run' cache] ≤ (n + 1 : ℕ) * soundError E q H 2

set_option maxHeartbeats 500000 in
theorem sound_halvRest_zero {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q H width fuel : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width) :
    SoundHalvRest prims K D Ad step q H width 0 (halvingSteps width) (fuel + 6) := by
  intro st live _ hs tag L htag A B V hwrong cache seen keys hc hq hk
  rw [iterate_halvingSteps width hw] at hwrong
  simp only [sum_range_one] at hwrong
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.cast_one, one_mul, halvProg_zero] using
    sound_finalStep prims K D Ad fuel step q H hr ha st live hs tag L htag A B V hwrong cache seen keys hc hq hk

set_option maxHeartbeats 500000 in
theorem sound_halvRest_succ {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q H width n j F : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    (hIH : SoundHalvRest prims K D Ad step q H width n (j + 1) F) :
    SoundHalvRest prims K D Ad step q H width (n + 1) j (F + 1 + 1) := by
  intro st live _ hs tag L htag A B V hwrong cache seen keys hc hq hk
  by_cases hall : ∀ i, i ∉ D.1 → live i
  swap
  · rw [halvExtend_missing K D Ad _ st live hall hs width n j A B V]
    simp
  rw [halvExtend_local K D Ad _ st live hall hs width n j A B V]
  apply sound_prefix prims _ _ step (sound_extendReply_bound Ad step ha _ _) L cache seen keys hc
  intro pa cache1 seen1 hc1 hn1
  apply sound_sample prims
  intro fresh
  rw [halvAfter_form]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  swap
  · rw [executePhase_challenge_live, if_neg hrec]
    simp
  let q0 := fun i => conv K (localContext i)
    (halvOut K D (halvedLength^[j] width) A B pa fresh i) 0
  let q2 := fun i => conv K (localContext i)
    (halvOut K D (halvedLength^[j] width) A B pa fresh i) 1
  let bad := fun r : E =>
    interpolate K D.1 (fun i => q0 i + (V i + q2 i) * r + q2 i * r ^ 2) 0 =
      ∑ k ∈ range (halvedLength (halvedLength^[j] width)),
        interpolate K D.1 (fun i => halvFold (halvedLength^[j] width) r (A i) k) 0 *
        interpolate K D.1 (fun i => halvFold (halvedLength^[j] width) r (B i) k) 0
  have hcard : (univ.filter bad).card ≤ 2 := sound_halvFold_card K D _ A B V q0 q2 hwrong
  let hs1 : C.Party → RunState C := fun i =>
    ⟨recordHistory K i (hs i).history (halvOut K D (halvedLength^[j] width) A B pa fresh i) 2,
      (hs i).label + 1, (hs i).tag⟩
  let g := halvCont K width n j A B V (halvOut K D (halvedLength^[j] width) A B pa fresh)
  apply le_trans (sound_challenge_phase prims K D Ad F step ha pa.1
    (fun i => i ∈ pa.2.2.2.2) hrec hs1 tag (L + 1)
    (fun i hi => by simp [hs1, htag i hi]) g cache1 seen1 keys (hc1.mono_label (by omega))
    bad 2 (by convert hcard using 1; congr 2) ((n + 1 : ℕ) * soundError E q H 2) ?_) ?_
  · intro p r key cache' seen' hc' hn' hgood
    unfold soundChallengeNext
    apply hIH p.1 (fun i => i ∈ p.2) _ tag ((L + 1) + 1)
      (fun i hi => by simp [hs1, htag i hi])
    · simpa only [Function.iterate_succ_apply'] using hgood
    · exact hc'
    · simp only [Nat.add_mul, Nat.mul_add] at hq ⊢
      omega
    · have hh := Finset.card_insert_le key keys
      omega
  · have hmono := soundError_mono (E := E) q H 2 seen1 keys (by simp only [Nat.add_mul, Nat.mul_add] at hq; omega) (by omega)
    calc
      _ = (seen1.card / Fintype.card E +
        ((keys.card + seen1.card) / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ))) +
          (n + 1 : ℕ) * soundError E q H 2 := by simp only [Nat.cast_ofNat, add_assoc]
      _ ≤ soundError E q H 2 + (n + 1 : ℕ) * soundError E q H 2 := by simpa only [Nat.cast_ofNat] using add_le_add hmono (le_refl ((n + 1 : ℕ) * soundError E q H 2))
      _ = _ := by push_cast; ring


set_option maxHeartbeats 500000 in
theorem sound_halvRest_all {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q H width : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width) :
    ∀ n j fuel, j + n = halvingSteps width →
      SoundHalvRest prims K D Ad step q H width n j (fuel + 2 * n + 6)
  | 0, j, fuel, hj => by
    have hj' : j = halvingSteps width := by omega
    subst j
    exact sound_halvRest_zero prims K D Ad step q H width fuel hr ha hw
  | n + 1, j, fuel, hj => by
    rw [show fuel + 2 * (n + 1) + 6 = (fuel + 2 * n + 6) + 1 + 1 by omega]
    exact sound_halvRest_succ prims K D Ad step q H width n j _ ha
      (sound_halvRest_all prims K D Ad step q H width hr ha hw n (j + 1) fuel (by omega))

/-- Effective replicated values commute with the public slice fold. -/
lemma interpolate_conv_sliceFold (K : Constants C E) (D : Finset C.Party)
    (count j : ℕ) (r : E) (xs : C.Party → Shares C E) (k : ℕ) :
    interpolate K D (fun i => conv K (localContext i) (sliceFold count j r (xs i)) k) 0 =
      interpolate K D (fun i => conv K (localContext i) (xs i) k) 0 +
        r * (interpolate K D (fun i => conv K (localContext i) (xs i) k) 0 +
          interpolate K D (fun i => conv K (localContext i) (xs i) (k + sliceHalf count j)) 0) := by
  simp only [sliceFold, conv, interpolate, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Gruen's slice error bound for the actual party-indexed folded vectors. -/
theorem sound_sliceFold_card (K : Constants C E) (D : C.Coalition) (τ : List E)
    (count j : ℕ) (hw : 0 < sliceWidth count) (hj : j < sliceBits)
    (xs ys : C.Party → Shares C E) (V q0 qInf : C.Party → E)
    (hc : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    (hwrong : interpolate K D.1 V 0 ≠ ∑ k ∈ range (sliceLen count j),
      sliceWeight τ count j k * interpolate K D.1 (fun i => conv K (localContext i) (xs i) k) 0 *
        interpolate K D.1 (fun i => conv K (localContext i) (ys i) k) 0) :
    (univ.filter fun r : E => interpolate K D.1 (fun i => sliceClaim τ j r (V i) (q0 i) (qInf i)) 0 =
      ∑ k ∈ range (sliceLen count (j + 1)), sliceWeight τ count (j + 1) k *
        interpolate K D.1 (fun i => conv K (localContext i) (sliceFold count j r (xs i)) k) 0 *
        interpolate K D.1 (fun i => conv K (localContext i) (sliceFold count j r (ys i)) k) 0).card ≤ 2 := by
  letI : CharP E 2 := charP_two
  let w := sliceBits - 1 - j
  let N := sliceWidth count * 2 ^ w
  let a := fun k => interpolate K D.1 (fun i => conv K (localContext i) (xs i) k) 0
  let b := fun k => interpolate K D.1 (fun i => conv K (localContext i) (ys i) k) 0
  let rest := fun k => coinProduct τ 0 w (k / sliceWidth count)
  let t0 := ∑ k ∈ range N, rest k * a k * b k
  let thi := ∑ k ∈ range N, rest k * a (k + N) * b (k + N)
  let tInf := ∑ k ∈ range N, rest k * (a k + a (k + N)) * (b k + b (k + N))
  have hw0 : sliceBits - j = w + 1 := by omega
  have hw1 : sliceBits - (j + 1) = w := by omega
  have hs := slice_sum_split τ (sliceWidth count) w hw a b
  have hfull : (∑ k ∈ range (sliceLen count j), sliceWeight τ count j k * a k * b k) =
      t0 + τ.getD w 0 * thi := by
    simpa only [sliceLen, sliceWeight, hw0, t0, thi, N, rest] using hs
  have hf (r : E) : (∑ k ∈ range N, rest k * (a k + r * (a k + a (k + N))) *
      (b k + r * (b k + b (k + N)))) = t0 + (t0 + thi + tInf) * r + tInf * r ^ 2 := by
    have h := sum_range_halving_fold (fun k => rest k * a k) b
      (fun k => rest k * a (k + N)) (fun k => b (k + N)) N r
    simpa only [t0, thi, tInf, mul_add, mul_assoc, mul_left_comm, mul_comm] using h
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  have he : t0 + τ.getD w 0 * (t0 + (t0 + thi + tInf) + tInf) = t0 + τ.getD w 0 * thi := by
    linear_combination (τ.getD w 0 * (t0 + tInf)) * two
  have hh : interpolate K D.1 V 0 ≠ t0 + τ.getD w 0 * (t0 + (t0 + thi + tInf) + tInf) := by
    rw [he, ← hfull]
    exact hwrong
  have hcard := slice_effective_card_le_two K D τ j V q0 qInf t0 (t0 + thi + tInf) tInf hc hh
  convert hcard using 1
  congr 1
  ext r
  simp only [mem_filter, mem_univ, true_and, interpolate_conv_sliceFold,
    sliceLen, sliceWeight, hw1]
  exact (congrArg (fun z => interpolate K D.1 (fun i => sliceClaim τ j r (V i) (q0 i) (qInf i)) 0 = z) (hf r)).to_iff

/-- Soundness invariant for the slice suffix followed by all halving rounds. -/
def SoundSliceRest {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q H count n j F : ℕ) : Prop :=
  ∀ (st : Ad.State) (live : C.Party → Prop) [DecidablePred live]
    (hs : C.Party → RunState C) (tag L : ℕ),
    (∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L) →
    ∀ (xs ys : C.Party → Shares C E) (V : C.Party → E),
    interpolate K D.1 V 0 ≠ ∑ k ∈ range (sliceLen count j), sliceWeight τ count j k *
      interpolate K D.1 (fun i => conv K (localContext i) (xs i) k) 0 *
      interpolate K D.1 (fun i => conv K (localContext i) (ys i) k) 0 →
    ∀ (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput),
    SoundCache L cache seen keys →
    seen.card + (2 * (n + halvingSteps (sliceWidth count)) + 4) * step ≤ q →
    keys.card + n + halvingSteps (sliceWidth count) ≤ H →
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if live i then (sliceProg K τ count n j (xs i) (ys i) (V i) i).run' (hs i)
            else failure))).run' cache] ≤ (n + halvingSteps (sliceWidth count) + 1 : ℕ) * soundError E q H 2

set_option maxHeartbeats 500000 in
theorem sound_sliceRest_zero {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q H count fuel : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count) :
    SoundSliceRest prims K D Ad τ step q H count 0 sliceBits
      (fuel + 2 * halvingSteps (sliceWidth count) + 6) := by
  intro st live _ hs tag L htag xs ys V hwrong cache seen keys hc hq hk
  simp only [sliceLen, sliceWeight, Nat.sub_self, pow_zero, mul_one, coinProduct, Finset.range_zero,
    Finset.prod_empty, one_mul] at hwrong
  simp only [sliceProg_zero]
  simpa only [Nat.zero_add] using sound_halvRest_all prims K D Ad step q H (sliceWidth count) hr ha hw
    (halvingSteps (sliceWidth count)) 0 fuel (by omega) st live hs tag L htag
    (fun i => conv K (localContext i) (xs i)) (fun i => conv K (localContext i) (ys i)) V
    hwrong cache seen keys hc (by simpa only [Nat.zero_add] using hq) hk

set_option maxHeartbeats 500000 in
theorem sound_sliceRest_succ {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q H count n j F : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    (hw : 0 < sliceWidth count) (hj : j < sliceBits) (hτ : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    (hIH : SoundSliceRest prims K D Ad τ step q H count n (j + 1) F) :
    SoundSliceRest prims K D Ad τ step q H count (n + 1) j (F + 1 + 1) := by
  intro st live _ hs tag L htag xs ys V hwrong cache seen keys hc hq hk
  by_cases hall : ∀ i, i ∉ D.1 → live i
  swap
  · rw [sliceExtend_missing K D Ad _ st live hall hs τ count n j xs ys V]
    simp
  rw [sliceExtend_local K D Ad _ st live hall hs τ count n j xs ys V]
  apply sound_prefix prims _ _ step (sound_extendReply_bound Ad step ha _ _) L cache seen keys hc
  intro pa cache1 seen1 hc1 hn1
  apply sound_sample prims
  intro fresh
  rw [sliceAfter_form]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  swap
  · rw [executePhase_challenge_live, if_neg hrec]
    simp
  let q0 := fun i => conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 0
  let qInf := fun i => conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 1
  let bad := fun r : E =>
    interpolate K D.1 (fun i => sliceClaim τ j r (V i) (q0 i) (qInf i)) 0 =
      ∑ k ∈ range (sliceLen count (j + 1)), sliceWeight τ count (j + 1) k *
        interpolate K D.1 (fun i => conv K (localContext i) (sliceFold count j r (xs i)) k) 0 *
        interpolate K D.1 (fun i => conv K (localContext i) (sliceFold count j r (ys i)) k) 0
  have hcard : (univ.filter bad).card ≤ 2 := sound_sliceFold_card K D τ count j hw hj xs ys V q0 qInf hτ hwrong
  let hs1 : C.Party → RunState C := fun i =>
    ⟨recordHistory K i (hs i).history (sliceOut K D τ count j xs ys pa fresh i) 2,
      (hs i).label + 1, (hs i).tag⟩
  let g := sliceCont K τ count n j xs ys V (sliceOut K D τ count j xs ys pa fresh)
  apply le_trans (sound_challenge_phase prims K D Ad F step ha pa.1
    (fun i => i ∈ pa.2.2.2.2) hrec hs1 tag (L + 1)
    (fun i hi => by simp [hs1, htag i hi]) g cache1 seen1 keys (hc1.mono_label (by omega))
    bad 2 (by convert hcard using 1; congr 2)
    ((n + halvingSteps (sliceWidth count) + 1 : ℕ) * soundError E q H 2) ?_) ?_
  · intro p r key cache' seen' hc' hn' hgood
    unfold soundChallengeNext
    apply hIH p.1 (fun i => i ∈ p.2) _ tag ((L + 1) + 1)
      (fun i hi => by simp [hs1, htag i hi])
    · exact hgood
    · exact hc'
    · simp only [Nat.add_mul, Nat.mul_add] at hq ⊢
      omega
    · have hh := Finset.card_insert_le key keys
      omega
  · have hmono := soundError_mono (E := E) q H 2 seen1 keys
      (by simp only [Nat.add_mul, Nat.mul_add] at hq; omega) (by omega)
    calc
      _ = (seen1.card / Fintype.card E +
        ((keys.card + seen1.card) / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ))) +
          (n + halvingSteps (sliceWidth count) + 1 : ℕ) * soundError E q H 2 := by
            simp only [Nat.cast_ofNat, add_assoc]
      _ ≤ soundError E q H 2 + (n + halvingSteps (sliceWidth count) + 1 : ℕ) * soundError E q H 2 := by
        simpa only [Nat.cast_ofNat] using add_le_add hmono
          (le_refl ((n + halvingSteps (sliceWidth count) + 1 : ℕ) * soundError E q H 2))
      _ = _ := by push_cast; ring

set_option maxHeartbeats 500000 in
theorem sound_sliceRest_all {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q H count : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0) :
    ∀ n j fuel, j + n = sliceBits → SoundSliceRest prims K D Ad τ step q H count n j
      (fuel + 2 * (n + halvingSteps (sliceWidth count)) + 6)
  | 0, j, fuel, hj => by
    have hj' : j = sliceBits := by omega
    subst j
    simpa only [Nat.zero_add] using sound_sliceRest_zero prims K D Ad τ step q H count fuel hr ha hw
  | n + 1, j, fuel, hj => by
    rw [show fuel + 2 * (n + 1 + halvingSteps (sliceWidth count)) + 6 =
      (fuel + 2 * (n + halvingSteps (sliceWidth count)) + 6) + 1 + 1 by omega]
    exact sound_sliceRest_succ prims K D Ad τ step q H count n j _ ha hw (by omega)
      (hτ _ (by omega))
      (sound_sliceRest_all prims K D Ad τ step q H count hr ha hw hτ n (j + 1) fuel (by omega))

lemma sound_element_uniform (K : Constants C E) :
    𝒟[elementOfHash K <$> ($ᵗ HashOutput)] = 𝒟[$ᵗ E] := by
  apply evalDist_ext
  intro x
  rw [← probEvent_eq_eq_probOutput, probEvent_elementOfHash, ← probEvent_uniformSample,
    probEvent_eq_eq_probOutput]

lemma sound_uniform_list_succ (n : ℕ) :
    𝒟[List.ofFn <$> ($ᵗ (Fin (n + 1) → E))] =
      𝒟[do let a ← $ᵗ E; let t ← $ᵗ (Fin n → E); pure (a :: List.ofFn t)] := by
  let e : (E × (Fin n → E)) ≃ (Fin (n + 1) → E) :=
    ⟨fun p => Fin.cases p.1 p.2, fun f => (f 0, fun i => f i.succ),
      (by intro p; rfl), (by intro f; funext i; cases i using Fin.cases <;> rfl)⟩
  have h := evalDist_map_bijective_uniform_cross (E × (Fin n → E)) e e.bijective
  rw [evalDist_map, ← h, ← evalDist_map]
  simp only [Functor.map_map, List.ofFn_succ]
  change 𝒟[(fun a : E × (Fin n → E) => a.1 :: List.ofFn a.2) <$>
    (Prod.mk <$> ($ᵗ E) <*> ($ᵗ (Fin n → E)))] = _
  simp only [seq_eq_bind_map, bind_map_left, map_bind, Functor.map_map, bind_pure_comp]

/-- Unused expansion positions give independent uniform field elements. -/
theorem sound_expand_uniform (prims : Primitives) (K : Constants C E) (key : HashOutput) :
    ∀ n index (cache : HashCache C), (∀ i ≥ index, cache (.expand key i) = none) →
    𝒟[(simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      ((List.range' index n).mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run' cache] =
      𝒟[List.ofFn <$> ($ᵗ (Fin n → E))]
  | 0, index, cache, hfresh => by
    simp only [List.range'_zero, List.mapM_nil, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    apply evalDist_ext
    intro xs
    rw [show List.ofFn = (fun _ : Fin 0 → E => ([] : List E)) by funext f; simp]
    simp [probOutput_map_const]
  | n + 1, index, cache, hfresh => by
    rw [sound_uniform_list_succ]
    simp only [List.range'_succ, List.mapM_cons, simulateQ_bind, simulateQ_map, StateT.run'_eq,
      StateT.run_bind, StateT.run_map, map_bind]
    rw [simulateQ_hashQuery_run_fresh prims (by rintro ⟨_, h, _⟩; cases h) (hfresh index le_rfl)]
    simp only [bind_map_left]
    have htail : ∀ u : HashOutput,
        𝒟[(simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
          ((List.range' (index + 1) n).mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run'
            (cache.cacheQuery (.expand key index) u)] = 𝒟[List.ofFn <$> ($ᵗ (Fin n → E))] := by
      intro u
      apply sound_expand_uniform prims K key n (index + 1)
      intro i hi
      rw [QueryCache.cacheQuery, Function.update_of_ne (by simp; omega)]
      exact hfresh i (by omega)
    calc
      _ = 𝒟[do let u ← $ᵗ HashOutput; let t ← $ᵗ (Fin n → E); pure (elementOfHash K u :: List.ofFn t)] := by
        apply evalDist_bind_congr'
        intro u
        simp only [simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp]
        rw [← Functor.map_map, ← StateT.run'_eq, evalDist_map, htail, ← evalDist_map, Functor.map_map]
      _ = _ := by
        have hh := congrArg (fun d : SPMF E => d >>= fun a =>
          𝒟[do let t ← $ᵗ (Fin n → E); pure (a :: List.ofFn t)]) (sound_element_uniform K)
        simpa only [evalDist_map, evalDist_bind, bind_map_left] using hh

theorem SoundCache.start (prims : Primitives) (K : Constants C E)
    {L : ℕ} {cache : HashCache C} {seen : Finset (Query C)} {keys : Finset HashOutput}
    (hc : SoundCache L cache seen keys) (tag label d : ℕ) (v : List E) (hL : L ≤ label)
    (p : List E × HashCache C)
    (hp : p ∈ support ((simulateQ (localAnswer prims)
      (liftComp (startQuery K tag label v d) (LocalSpec C))).run cache)) :
    ∃ key, SoundCache (label + 1) p.2 seen (insert key keys) := by
  rw [simulateQ_localAnswer_liftComp, startQuery, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hp
  obtain ⟨⟨key, cache'⟩, hkey, hp⟩ := hp
  have hq : ¬ IsFixed (Query.coinKey (C := C) tag label (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  have hk := support_hashQuery_entries prims hq cache _ hkey
  have he := support_expand_entries prims K key _ _ _ hp
  refine ⟨key, ?_, ?_⟩
  · intro tg lab bits hl hb
    rcases he _ hb with h | ⟨idx, h⟩
    · rcases hk _ h with h | h
      · exact hc.1 tg lab bits (by omega) h
      · have := (Query.coinKey.inj h).2.1
        omega
    · cases h
  · intro k idx hb
    rcases he _ hb with h | ⟨idx', h⟩
    · rcases hk _ h with h | h
      · exact (hc.2 k idx h).imp_left (Finset.mem_insert_of_mem)
      · cases h
    · have hkk := (Query.expand.inj h).1
      exact Or.inl (hkk ▸ Finset.mem_insert_self _ _)

/-- The initial expansion has only a cached-key error and its uniform weight error. -/
theorem sound_startQuery_bad (prims : Primitives) (K : Constants C E)
    (tag label d : ℕ) (coin : List E) (Ks : Finset HashOutput) (cache : HashCache C)
    (hfresh : cache (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v))) = none)
    (hexpand : ∀ key idx, cache (.expand key idx) ≠ none → key ∈ Ks)
    (bad : List E → Prop) (δ : ℝ≥0∞)
    (hbad : Pr[fun v : Fin d → E => bad (List.ofFn v) | $ᵗ (Fin d → E)] ≤ δ) :
    Pr[fun p => bad p.1 | (simulateQ (localAnswer prims)
      (liftComp (startQuery K tag label coin d) (LocalSpec C))).run cache] ≤ Ks.card / 2 ^ 256 + δ := by
  have hq : ¬ IsFixed (C := C) (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  rw [simulateQ_localAnswer_liftComp, startQuery, simulateQ_bind, StateT.run_bind]
  have h := probEvent_bind_le_add (p := fun p : HashOutput × HashCache C => p.1 ∉ Ks)
    (q := fun p : List E × HashCache C => ¬ bad p.1)
    (ε₁ := Ks.card / 2 ^ 256) (ε₂ := δ)
    (my := fun p => (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      ((List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand p.1 k))).run p.2)
    (by simpa using probEvent_hash_fresh_mem prims hq hfresh Ks) (fun p hp hk => ?_)
  · simpa using h
  · simp only [not_not]
    have hf : ∀ i ≥ 0, p.2 (.expand p.1 i) = none := by
      intro i _
      by_contra hn
      rcases support_hashQuery_entries prims hq cache p hp _ hn with h | h
      · exact hk (hexpand _ _ h)
      · cases h
    have he := sound_expand_uniform prims K p.1 d 0 p.2 hf
    rw [← List.range_eq_range'] at he
    have he' : Pr[bad | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        ((List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand p.1 k))).run' p.2] ≤ δ := by
      rw [probEvent_def, he, ← probEvent_def, probEvent_map]
      exact hbad
    simpa only [StateT.run'_eq, probEvent_map, Function.comp_def] using he'

/-- The initial sampled coin and expansion followed by any adaptive continuation. -/
theorem sound_coin_start {β : Type} (prims : Primitives) (K : Constants C E)
    (n : ℕ) (hn : n = 1) (tag L d : ℕ) (cache : HashCache C)
    (seen : Finset (Query C)) (keys : Finset HashOutput) (hc : SoundCache L cache seen keys)
    (bad : List E → Prop) (δ : ℝ≥0∞)
    (hbad : Pr[fun v : Fin d → E => bad (List.ofFn v) | $ᵗ (Fin d → E)] ≤ δ)
    (cont : (Fin n → E) → List E × HashCache C → ProbComp β)
    (accept : β → Prop) (ε : ℝ≥0∞)
    (hnext : ∀ v p, p ∈ support ((simulateQ (localAnswer prims)
      (liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C))).run cache) →
      ¬ bad p.1 → Pr[accept | cont v p] ≤ ε) :
    Pr[accept | (do
      let v ← $ᵗ (Fin n → E)
      (simulateQ (localAnswer prims)
        (liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C))).run cache >>= cont v)] ≤
      seen.card / Fintype.card E + ((keys.card + seen.card) / 2 ^ 256 + δ + ε) := by
  let fresh := fun v : Fin n → E => Query.coinKey tag L
    ((List.ofFn v).flatMap fun v => List.ofFn (K.encode v)) ∉ seen
  have hinj : Function.Injective (fun v : Fin n → E => Query.coinKey (C := C) tag L
      ((List.ofFn v).flatMap fun v => List.ofFn (K.encode v))) := by
    subst n
    exact coinInput_one_injective K tag L
  have hguess : Pr[fun v => ¬ fresh v | $ᵗ (Fin n → E)] ≤
      seen.card / (Fintype.card E : ℝ≥0∞) := by
    simpa only [fresh, not_not, Fintype.card_fun, Fintype.card_fin, hn, pow_one] using
      probEvent_uniform_injective_mem _ hinj seen
  have h := probEvent_bind_le_add (p := fresh) (q := fun b => ¬ accept b)
    (my := fun v => (simulateQ (localAnswer prims)
      (liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C))).run cache >>= cont v)
    (ε₂ := (keys.card + seen.card) / 2 ^ 256 + δ + ε) hguess (fun v _ hv => ?_)
  · simpa using h
  · have hb := sound_startQuery_bad prims K tag L d (List.ofFn v)
      (keys ∪ seen.image soundExpansionKey) cache (hc.fresh _ _ _ le_rfl hv) hc.expansions bad δ hbad
    have hb' : Pr[fun p => bad p.1 | (simulateQ (localAnswer prims)
        (liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C))).run cache] ≤
        (keys.card + seen.card) / 2 ^ 256 + δ := by
      refine hb.trans ?_
      gcongr
      exact_mod_cast soundExpansionKeys_card seen keys
    simpa using probEvent_bind_le_add (p := fun p => ¬ bad p.1) (q := fun b => ¬ accept b)
      (my := cont v) (by simpa using hb') (fun p hp hg => by simpa using hnext v p hp hg)

def soundStartNext {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (hs : C.Party → RunState C)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (p : A.State × Finset C.Party) (τ : List E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option Unit)) :=
  executePhase localRoles D A (checkFunctionalities K) fuel p.1
    (fun i => if i ∈ p.2 then (g i τ).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure)

lemma soundStartNext_missing {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (hs : C.Party → RunState C)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit) (p : A.State × Finset C.Party)
    (hmiss : ¬ ∃ i, i ∉ D.1 ∧ i ∈ p.2) (τ : List E) :
    soundStartNext K D A fuel hs g p τ = pure (p.1, fun _ => none) := by
  unfold soundStartNext
  rw [executePhase_congr_honest D A _ _ p.1 _ (fun _ => failure), executePhase_failure]
  intro i hi
  exact if_neg (fun h => hmiss ⟨i, hi, h⟩)

set_option maxHeartbeats 500000 in
theorem sound_afterStart {Ia : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel d : ℕ) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (v : List E) (p : A.State × Finset C.Party) :
    SameLocalOutput prims
      (executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterStart K (hs i) d (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)))
      (liftComp (startQuery K tag L v d) (LocalSpec C) >>= soundStartNext K D A fuel hs g p) := by
  by_cases hp : ∃ i, i ∉ D.1 ∧ i ∈ p.2
  · exact SameLocalOutput.of_sameRun prims
      (executePhase_afterStart_common prims K D A fuel d p.1 hs tag L htag v p.2 hp g)
  · have he : executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterStart K (hs i) d (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)) =
        pure (p.1, fun _ : C.Party => (none : Option Unit)) := by
      rw [executePhase_congr_honest D A _ _ p.1 _ (fun _ => failure), executePhase_failure]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ p.2) := fun h => hp ⟨i, h⟩
      simp [hn, afterStart]
    have hg : soundStartNext K D A fuel hs g p =
        fun _ => pure (p.1, fun _ : C.Party => (none : Option Unit)) :=
      funext (soundStartNext_missing K D A fuel hs g p hp)
    rw [he, hg]
    intro cache
    exact (local_prefetch_output prims _ (pure (p.1, fun _ : C.Party => (none : Option Unit))) cache).symm

set_option maxHeartbeats 500000 in
theorem sound_start_normalize {Ia : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel d : ℕ) (st : A.State)
    (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit) :
    SameLocalOutput prims
      (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
        (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key d) >>= g i).run' (hs i)))
      (do
        let v ← liftComp ($ᵗ (Fin (firstInput fun i : C.Party => if i ∈ D.1 then
          (none : Option ℕ) else some 1) → E)) (LocalSpec C)
        let τ ← liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C)
        let p ← (leftAdversary (leftAdversary A)).answer st (List.ofFn v)
        soundStartNext K D A fuel hs g p τ) := by
  rw [executePhase_start K D A fuel st hs d g,
    runFunctionality_coin_local D (leftAdversary (leftAdversary A)) st _
      (by intro i hi; simp [hi])]
  simp only [bind_assoc, pure_bind]
  refine SameLocalOutput.bind_right prims _ ?_
  intro v
  have h₁ := SameLocalOutput.bind_right prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (fun p => sound_afterStart prims K D A fuel d hs tag L htag g (List.ofFn v) p)
  have h₂ := SameLocalOutput.of_sameRun prims (sameRun_swap prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C))
    (fun p τ => soundStartNext K D A fuel hs g p τ))
  intro cache
  simpa only [leftAdversary, bind_assoc, pure_bind] using (h₁ cache).trans (h₂ cache)

set_option maxHeartbeats 500000 in
theorem sound_start_phase {Ia : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel step d : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (bad : List E → Prop) (δ : ℝ≥0∞)
    (hbad : Pr[fun v : Fin d → E => bad (List.ofFn v) | $ᵗ (Fin d → E)] ≤ δ) (ε : ℝ≥0∞)
    (hnext : ∀ p τ key cache' seen', SoundCache (L + 1) cache' seen' (insert key keys) →
      seen'.card ≤ seen.card + step → ¬ bad τ →
      Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
        (simulateQ (localAnswer prims) (soundStartNext K D A fuel hs g p τ)).run' cache'] ≤ ε) :
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
          (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key d) >>= g i).run' (hs i)))).run' cache] ≤
      seen.card / Fintype.card E + ((keys.card + seen.card) / 2 ^ 256 + δ + ε) := by
  rw [probEvent_def, sound_start_normalize prims K D A fuel d st hs tag L htag g cache,
    ← probEvent_def]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, run_liftComp_prob, bind_map_left]
  apply sound_coin_start prims K _ (firstInput_honest_const D 1) tag L d cache seen keys hc bad δ hbad
  intro v p hp hgood
  obtain ⟨key, hcache⟩ := hc.start prims K tag L d (List.ofFn v) le_rfl p hp
  apply probEvent_bind_le_of_forall_le
  intro ans hans
  have hans' : ans ∈ support ((simulateQ (localAnswer prims)
      ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))).run p.2) := by
    simpa only [simulateQ_bind, StateT.run_bind] using hans
  obtain ⟨seen', hcache', hcard'⟩ := hcache.local prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v)) step
    (sound_coinReply_bound A step ha st _) ans hans'
  exact hnext ans.1 p.1 key ans.2 seen' hcache' hcard' hgood

lemma sound_sum_blocks (f : ℕ → E) (n B : ℕ) :
    (∑ k ∈ range (n * B), f k) = ∑ a ∈ range n, ∑ b ∈ range B, f (a * B + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

lemma sound_coinProduct_split (τ : List E) (s t h w : ℕ) (hh : h < 2 ^ s) :
    coinProduct τ 0 (s + t) (w * 2 ^ s + h) =
      coinProduct τ 0 s h * coinProduct τ s t w := by
  unfold coinProduct
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.mul_comm w, Nat.testBit_two_pow_mul_add w hh i,
      if_pos (Finset.mem_range.mp hi)]
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Nat.mul_comm w, Nat.testBit_two_pow_mul_add w hh (s + i),
      show ¬ s + i < s by omega, if_false, Nat.add_sub_cancel_left, Nat.zero_add]

lemma sound_layout (count h w b : ℕ) (hw : w < sliceLength count) (hb : b < 2 ^ wordBits) :
    let k := h * sliceWidth count + w * 2 ^ wordBits + b
    sliceOf count k = h ∧ wordOf count k = w ∧ (bitOf k).val = b := by
  have hW : 0 < sliceLength count := by omega
  have hB : 0 < 2 ^ wordBits := by positivity
  have htail : w * 2 ^ wordBits + b < sliceWidth count := by
    unfold sliceWidth
    nlinarith
  dsimp only
  constructor
  · unfold sliceOf
    rw [Nat.add_assoc, Nat.mul_comm h, Nat.mul_add_div (by exact Nat.mul_pos hB hW),
      Nat.div_eq_of_lt htail, Nat.add_zero]
  · constructor
    · unfold wordOf sliceWidth
      rw [show h * (2 ^ wordBits * sliceLength count) + w * 2 ^ wordBits + b =
        2 ^ wordBits * (h * sliceLength count + w) + b by ring,
        Nat.mul_add_div hB, Nat.div_eq_of_lt hb, Nat.add_zero]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hw]
    · unfold bitOf sliceWidth
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb]

/-- The coefficient belonging to one word of tuple errors. -/
def soundWordError (K : Constants C E) (count : ℕ) (e : ℕ → Bit) (h w : ℕ) : E :=
  ∑ b : Fin (2 ^ wordBits), e (h * sliceWidth count + w * 2 ^ wordBits + b) • K.weight b

def soundWeightError (K : Constants C E) (count : ℕ) (e : ℕ → Bit) (a : ℕ) : E :=
  if a / 2 ^ sliceBits < sliceLength count then
    soundWordError K count e (a % 2 ^ sliceBits) (a / 2 ^ sliceBits) else 0

lemma soundWeightError_nonzero (K : Constants C E) (count : ℕ) (e : ℕ → Bit)
    (herror : ∃ k < 2 ^ sliceBits * sliceWidth count, e k ≠ 0) :
    ∃ a < 2 ^ coins count, soundWeightError K count e a ≠ 0 := by
  obtain ⟨k, hk, he⟩ := herror
  have hB : 0 < 2 ^ wordBits := by positivity
  have hS : 0 < 2 ^ sliceBits := by positivity
  have hW : 0 < sliceWidth count := by nlinarith
  let h := k / sliceWidth count
  let w := k / 2 ^ wordBits % sliceLength count
  let b := k % 2 ^ wordBits
  have hh : h < 2 ^ sliceBits := (Nat.div_lt_iff_lt_mul hW).mpr hk
  have hw : w < sliceLength count := Nat.mod_lt _ (by unfold sliceWidth at hW; nlinarith)
  have hb : b < 2 ^ wordBits := Nat.mod_lt _ hB
  have hidx : h * sliceWidth count + w * 2 ^ wordBits + b = k := by
    dsimp only [h, w, b]
    unfold sliceWidth
    rw [← Nat.div_div_eq_div_mul]
    have hd := Nat.mod_add_div (k / 2 ^ wordBits) (sliceLength count)
    have hb' := Nat.mod_add_div k (2 ^ wordBits)
    nlinarith
  refine ⟨w * 2 ^ sliceBits + h, ?_, ?_⟩
  · apply lt_of_lt_of_le _ (Nat.le_pow_clog (by norm_num) (2 ^ sliceBits * sliceLength count))
    nlinarith
  · have hd : (w * 2 ^ sliceBits + h) / 2 ^ sliceBits = w := by
      rw [Nat.mul_comm w, Nat.mul_add_div hS, Nat.div_eq_of_lt hh, Nat.add_zero]
    have hm : (w * 2 ^ sliceBits + h) % 2 ^ sliceBits = h := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hh]
    simp only [soundWeightError, hd, hm, if_pos hw]
    apply check_word_weight_ne_zero K
    intro hz
    have hz' := congrFun hz (⟨b, hb⟩ : Fin (2 ^ wordBits))
    exact he (by simpa only [Pi.zero_apply, hidx] using hz')

/-- The actual slice/word/bit layout is the multilinear polynomial of its word errors. -/
theorem soundWeightError_sum (K : Constants C E) (count : ℕ) (hcount : count ≠ 0)
    (e : ℕ → Bit) (τ : List E) :
    (∑ a ∈ range (2 ^ coins count), coinProduct τ 0 (coins count) a * soundWeightError K count e a) =
      ∑ k ∈ range (2 ^ sliceBits * sliceWidth count),
        coinProduct τ 0 sliceBits (sliceOf count k) * wordWeightOf K τ count k * algebraMap Bit E (e k) := by
  have hS : 0 < 2 ^ sliceBits := by positivity
  have hs : sliceBits ≤ coins count := sliceBits_le_coins hcount
  have hp : 2 ^ sliceBits * sliceLength count ≤ 2 ^ coins count := Nat.le_pow_clog (by norm_num) _
  have hcut : (∑ a ∈ range (2 ^ coins count), coinProduct τ 0 (coins count) a * soundWeightError K count e a) =
      ∑ a ∈ range (sliceLength count * 2 ^ sliceBits),
        coinProduct τ 0 (coins count) a * soundWeightError K count e a := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by nlinarith))
    intro a ha hnot
    have ha' : sliceLength count * 2 ^ sliceBits ≤ a := by simpa using hnot
    have hn : ¬ a / 2 ^ sliceBits < sliceLength count := by
      rw [Nat.div_lt_iff_lt_mul hS]
      omega
    simp [soundWeightError, hn]
  rw [hcut, sound_sum_blocks]
  have hcoeff : ∀ w < sliceLength count, ∀ h < 2 ^ sliceBits,
      coinProduct τ 0 (coins count) (w * 2 ^ sliceBits + h) *
          soundWeightError K count e (w * 2 ^ sliceBits + h) =
        coinProduct τ 0 sliceBits h * coinProduct τ sliceBits (coins count - sliceBits) w *
          soundWordError K count e h w := by
    intro w hw h hh
    have hd : (w * 2 ^ sliceBits + h) / 2 ^ sliceBits = w := by
      rw [Nat.mul_comm w, Nat.mul_add_div hS, Nat.div_eq_of_lt hh, Nat.add_zero]
    have hm : (w * 2 ^ sliceBits + h) % 2 ^ sliceBits = h := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hh]
    rw [soundWeightError, hd, hm, if_pos hw,
      show coins count = sliceBits + (coins count - sliceBits) from (Nat.add_sub_of_le hs).symm,
      sound_coinProduct_split τ _ _ _ _ hh]
    simp only [Nat.add_sub_cancel_left]
  simp_rw [Finset.sum_congr rfl (fun w hw => Finset.sum_congr rfl
    (fun h hh => hcoeff w (Finset.mem_range.mp hw) h (Finset.mem_range.mp hh)))]
  rw [Finset.sum_comm, sound_sum_blocks]
  apply Finset.sum_congr rfl
  intro h hh
  rw [show sliceWidth count = sliceLength count * 2 ^ wordBits by unfold sliceWidth; ring,
    sound_sum_blocks]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Fin.sum_univ_eq_sum_range]
  unfold soundWordError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hl := sound_layout count h w b (Finset.mem_range.mp hw) b.2
  have hbit : bitOf (h * sliceWidth count + w * 2 ^ wordBits + b) = b := Fin.ext hl.2.2
  rw [show h * (sliceLength count * 2 ^ wordBits) + (w * 2 ^ wordBits + b) =
    h * sliceWidth count + w * 2 ^ wordBits + b by unfold sliceWidth; ring]
  simp only [wordWeightOf, hl.1, hl.2.1, hbit, Algebra.smul_def]
  ring

/-- GS20 Lemma 8 for an unrestricted uniform expansion; rejection of zero slice coins only helps. -/
theorem sound_delinearization (K : Constants C E) (d : ℕ) (δ : ℕ → E)
    (hδ : ∃ a < 2 ^ d, δ a ≠ 0) :
    Pr[fun v : Fin d → E => ∑ a ∈ range (2 ^ d), coinProduct (List.ofFn v) 0 d a * δ a = 0 |
      $ᵗ (Fin d → E)] ≤ (d : ℝ≥0∞) / (Fintype.card E - 2 : ℕ) := by
  let P := fun v : Fin d → E => ∑ a ∈ range (2 ^ d), coinProduct (List.ofFn v) 0 d a * δ a = 0
  let e : {τ : (Fin 0 → {c : E // c ≠ 0}) × (Fin d → E) // P τ.2} ≃ {v : Fin d → E // P v} :=
    ⟨fun τ => ⟨τ.1.2, τ.2⟩, fun v => ⟨(Fin.elim0, v.1), v.2⟩,
      (by intro x; apply Subtype.ext; apply Prod.ext; exact Subsingleton.elim _ _; rfl),
      (by intro x; rfl)⟩
  have hcard : (univ.filter fun τ : (Fin 0 → {c : E // c ≠ 0}) × (Fin d → E) => P τ.2).card =
      (univ.filter P).card := by
    simpa only [Fintype.card_subtype] using Fintype.card_congr e
  have hb := delinearization_card_bound K 0 d (Nat.zero_le d) δ hδ
  simp only [Nat.sub_zero, pow_zero, one_mul, List.ofFn_zero, List.nil_append] at hb
  change ((univ.filter fun τ : (Fin 0 → {c : E // c ≠ 0}) × (Fin d → E) => P τ.2).card : ℝ) /
    (Fintype.card E : ℝ) ^ d ≤ d / (Fintype.card E - 2 : ℝ) at hb
  rw [hcard] at hb
  have hE : 2 < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  have hden : (Fintype.card E - 2 : ℕ) ≠ 0 := by omega
  apply (ENNReal.toReal_le_toReal (by exact probEvent_ne_top)
    (ENNReal.div_ne_top (by simp) (by exact_mod_cast hden))).mp
  simpa only [probEvent_uniformSample, ENNReal.toReal_div, ENNReal.toReal_natCast,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ENNReal.toReal_pow, Nat.cast_sub (by omega : 2 ≤ Fintype.card E),
    Nat.cast_ofNat, P] using hb

lemma sound_interpolate_conv (K : Constants C E) (D : C.Coalition)
    (xs : C.Party → Shares C E) (X : Shares C E)
    (hx : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → xs i T = X T) (k : ℕ) :
    interpolate K D.1 (fun i => conv K (localContext i) (xs i) k) 0 = shareValue X k := by
  letI : CharP E 2 := charP_two
  obtain ⟨P, hP, h0, hPi⟩ := isShamir_conv (K := K) X k
  unfold shareValue
  rw [← h0]
  apply interpolate_honest_polynomial K D P hP
  intro i hi
  rw [← hPi i]
  exact conv_congr i _ _ k (fun T hT => congrFun (hx i hi T hT) k)

/-- The scalar error at the first slice is exactly the weighted bit-error polynomial. -/
theorem sound_initial_identity (K : Constants C E) (D : C.Coalition) (count : ℕ) (hcount : count ≠ 0)
    (X Y Z : Shares C Bit) (xs ys zs : C.Party → Shares C E)
    (hx : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → xs i T = fun k => algebraMap Bit E (X T k))
    (hy : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ys i T = fun k => algebraMap Bit E (Y T k))
    (hz : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → zs i T = fun k => algebraMap Bit E (Z T k))
    (τ : List E) :
    interpolate K D.1 (fun i => conv K (localContext i) (claimOf K τ count (zs i)) 0) 0 -
      (∑ k ∈ range (sliceLen count 0), sliceWeight τ count 0 k *
        interpolate K D.1 (fun i => conv K (localContext i)
          (fun T k => wordWeightOf K τ count k * xs i T k) k) 0 *
        interpolate K D.1 (fun i => conv K (localContext i) (ys i) k) 0) =
      ∑ a ∈ range (2 ^ coins count), coinProduct τ 0 (coins count) a *
        soundWeightError K count (fun k => shareValue Z k - shareValue X k * shareValue Y k) a := by
  rw [soundWeightError_sum K count hcount]
  have hZ := sound_interpolate_conv K D (fun i => claimOf K τ count (zs i))
    (claimOf K τ count (fun T k => algebraMap Bit E (Z T k)))
    (fun i hi T hT => by funext k; simp only [claimOf]; rw [hz i hi T hT]) 0
  have hX : ∀ k, interpolate K D.1 (fun i => conv K (localContext i)
      (fun T k => wordWeightOf K τ count k * xs i T k) k) 0 =
        wordWeightOf K τ count k * algebraMap Bit E (shareValue X k) := by
    intro k
    rw [sound_interpolate_conv K D _ (fun T k => wordWeightOf K τ count k * algebraMap Bit E (X T k))
      (fun i hi T hT => by rw [hx i hi T hT]) k]
    simp only [shareValue, map_sum, Finset.mul_sum]
  have hY : ∀ k, interpolate K D.1 (fun i => conv K (localContext i) (ys i) k) 0 =
      algebraMap Bit E (shareValue Y k) := by
    intro k
    rw [sound_interpolate_conv K D ys (fun T k => algebraMap Bit E (Y T k)) hy k]
    simp only [shareValue, map_sum]
  rw [hZ]
  simp only [shareValue, claimOf, Finset.mul_sum, map_sum, hX, hY, sliceLen, sliceWeight,
    Nat.sub_zero, mul_comm (sliceWidth count) (2 ^ sliceBits)]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [map_sub, map_mul, map_sum, sliceOf, ← Finset.mul_sum]
  ring

lemma sound_flatPos_surj : ∀ (counts : List ℕ) (m g : ℕ), m < counts.length → g < counts.getD m 0 →
    ∃ k < counts.sum, flatPos counts k = some (m, g)
  | [], m, g, hm, hg => by simp at hm
  | c :: cs, 0, g, hm, hg => by
    have hg' : g < c := by simpa using hg
    exact ⟨g, by simp; omega, by simp [flatPos, hg']⟩
  | c :: cs, m + 1, g, hm, hg => by
    obtain ⟨k, hk, he⟩ := sound_flatPos_surj cs m g (by simpa using hm) (by simpa using hg)
    refine ⟨c + k, by simp; omega, ?_⟩
    simp [flatPos, he]

lemma sound_padding (count : ℕ) : count ≤ 2 ^ sliceBits * sliceWidth count := by
  unfold sliceWidth sliceLength wordBits sliceBits
  norm_num
  omega

/-- The canonical flattened bit sharing, including the zero padding. -/
def soundFlatShare (D : C.Coalition) (counts : List ℕ) (x : C.Party → List (Tuple C))
    (part : Tuple C → Shares C Bit) : Shares C Bit := fun T k =>
  match flatPos counts k with
  | some (m, g) => part (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m) T g
  | none => 0

lemma soundFlatShare_held (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x)
    (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → liftedPart (E := E) (x i) part T =
      fun k => algebraMap Bit E (soundFlatShare D counts x part T k) := by
  intro i hi T hT
  funext k
  rw [lifted_real_at K hx hagree part hpart T i hT hi k]
  unfold soundFlatShare
  cases flatPos counts k <;> simp

def soundInitialBad (K : Constants C E) (D : C.Coalition) (count : ℕ)
    (xs ys zs : C.Party → Shares C E) (τ : List E) : Prop :=
  interpolate K D.1 (fun i => conv K (localContext i) (claimOf K τ count (zs i)) 0) 0 =
    ∑ k ∈ range (sliceLen count 0), sliceWeight τ count 0 k *
      interpolate K D.1 (fun i => conv K (localContext i)
        (fun T k => wordWeightOf K τ count k * xs i T k) k) 0 *
      interpolate K D.1 (fun i => conv K (localContext i) (ys i) k) 0

/-- An invalid tuple gives a nonzero word coefficient, hence the GS20 weight-coin bound. -/
theorem sound_initial_weights (K : Constants C E) (counts : List ℕ) (D : C.Coalition)
    (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x) (hpos : counts.sum ≠ 0)
    (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (hwrong : ∃ m < (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length,
      ∃ g < (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count,
        shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z g -
          shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x g *
            shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y g ≠ 0) :
    Pr[fun v : Fin (coins counts.sum) → E => soundInitialBad K D counts.sum
      (fun i => liftedPart (x i) (·.x)) (fun i => liftedPart (x i) (·.y))
      (fun i => liftedPart (x i) (·.z)) (List.ofFn v) | $ᵗ (Fin (coins counts.sum) → E)] ≤
        (coins counts.sum : ℝ≥0∞) / (Fintype.card E - 2 : ℕ) := by
  let X := soundFlatShare D counts x (·.x)
  let Y := soundFlatShare D counts x (·.y)
  let Z := soundFlatShare D counts x (·.z)
  let e := fun k => shareValue Z k - shareValue X k * shareValue Y k
  have he : ∃ k < 2 ^ sliceBits * sliceWidth counts.sum, e k ≠ 0 := by
    obtain ⟨m, hm, g, hg, hn⟩ := hwrong
    rw [firstInput_length K hx] at hm
    rw [tupleAt_count K hx] at hg
    obtain ⟨k, hk, hflat⟩ := sound_flatPos_surj counts m g hm hg
    refine ⟨k, hk.trans_le (sound_padding _), ?_⟩
    simpa only [e, X, Y, Z, shareValue, soundFlatShare, hflat] using hn
  have hb := sound_delinearization K (coins counts.sum) (soundWeightError K counts.sum e)
    (soundWeightError_nonzero K counts.sum e he)
  refine le_trans (probEvent_mono (mx := $ᵗ (Fin (coins counts.sum) → E)) fun v hv hbad => ?_) hb
  have hid := sound_initial_identity K D counts.sum hpos X Y Z
    (fun i => liftedPart (x i) (·.x)) (fun i => liftedPart (x i) (·.y)) (fun i => liftedPart (x i) (·.z))
    (soundFlatShare_held K hx hagree _ (Or.inl rfl))
    (soundFlatShare_held K hx hagree _ (Or.inr (Or.inl rfl)))
    (soundFlatShare_held K hx hagree _ (Or.inr (Or.inr rfl))) (List.ofFn v)
  exact hid.symm.trans (sub_eq_zero.mpr hbad)

lemma soundError_ne_top (K : Constants C E) (q H m : ℕ) : soundError E q H m ≠ ∞ := by
  have hE : 2 < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  have h0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E ≠ 0)
  have h2 : ((Fintype.card E - 2 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E - 2 ≠ 0)
  unfold soundError
  finiteness

lemma soundError_toReal (K : Constants C E) (q H m : ℕ) :
    (soundError E q H m).toReal =
      (q : ℝ) / Fintype.card E + ((H + q : ℕ) / (2 : ℝ) ^ 256 + (m : ℝ) / (Fintype.card E - 2 : ℝ)) := by
  have hE : 2 < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  have h0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E ≠ 0)
  have h2 : ((Fintype.card E - 2 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E - 2 ≠ 0)
  unfold soundError
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    Nat.cast_sub (by omega : 2 ≤ Fintype.card E), Nat.cast_ofNat]

/-- The accumulated per-coin errors are the two errors fixed in the statement. -/
lemma sound_error_sum (K : Constants C E) (count q : ℕ) :
    soundError E q (halvings count + 2) (coins count) +
      (halvings count + 1 : ℕ) * soundError E q (halvings count + 2) 2 =
    ENNReal.ofReal (checkErrorOf (E := E) (coins count) (halvings count) q + soundHashError count q) := by
  have hnonneg := add_nonneg (checkErrorOf_nonneg K (coins count) (halvings count) q)
    (soundHashError_nonneg count q)
  apply (ENNReal.toReal_eq_toReal_iff' (by
    exact ENNReal.add_ne_top.mpr ⟨soundError_ne_top K _ _ _, ENNReal.mul_ne_top (by simp) (soundError_ne_top K _ _ _)⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add (soundError_ne_top K _ _ _) (ENNReal.mul_ne_top (by simp) (soundError_ne_top K _ _ _)),
    ENNReal.toReal_mul, soundError_toReal K, soundError_toReal K, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hnonneg]
  unfold checkErrorOf soundHashError
  push_cast
  ring

/-- The complete round invariant, from a cache covered by the adversary query trace. -/
def CheckSoundRoundInduction (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (step q : ℕ) (st : A.State)
    (cache : HashCache C) (seen : Finset (Query C)),
    TupleInputs K counts D x → counts.sum ≠ 0 →
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) →
    (∀ state l, IsQueryBoundP (A.answer state l) Counted step) →
    (∀ k, cache k ≠ none → k ∈ seen) → seen.card + checkRounds counts.sum * step ≤ q →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    (∃ m < (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length,
      ∃ g < (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count,
        shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z g -
          shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x g *
            shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y g ≠ 0) →
    Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
            (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), 0, 0⟩))).run' cache] ≤
      ENNReal.ofReal (checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q +
        soundHashError counts.sum q)

set_option maxHeartbeats 1000000 in
/-- The initial weight draw, all slice and halving steps, and the final segment. -/
theorem checkSoundRoundInduction (prims : Primitives) (K : Constants C E) : CheckSoundRoundInduction prims K := by
  intro counts D A x step q st cache seen hx hpos hr ha hc hb hagree hwrong
  let H := halvings counts.sum + 2
  let F := 1 + 2 * (sliceBits + halvingSteps (sliceWidth counts.sum)) + 6
  let hs : C.Party → RunState C := fun i => ⟨filledHistory K i (x i), 0, 0⟩
  let g : C.Party → List E → RunM C E (CheckSpec C E) Unit := fun i τ => do
    StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
    sliceProg K τ counts.sum sliceBits 0 (fun T k => wordWeightOf K τ counts.sum k * liftedPart (x i) (·.x) T k)
      (liftedPart (x i) (·.y)) (conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0) i
  let bad := soundInitialBad K D counts.sum (fun i => liftedPart (x i) (·.x))
    (fun i => liftedPart (x i) (·.y)) (fun i => liftedPart (x i) (·.z))
  have hF : checkRounds counts.sum = F + 1 := by unfold F checkRounds halvings; omega
  rw [hF]
  change Pr[_ | (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) (F + 1) st
      (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key (coins counts.sum)) >>= g i).run'
        (hs i)))).run' cache] ≤ _
  apply le_trans (sound_start_phase prims K D A F step (coins counts.sum) ha st hs 0 0
    (fun i hi => ⟨rfl, rfl⟩) g cache seen ∅ (SoundCache.of_covered 0 cache seen hc) bad
    ((coins counts.sum : ℝ≥0∞) / (Fintype.card E - 2 : ℕ))
    (sound_initial_weights K counts D x hx hpos hagree hwrong)
    ((halvings counts.sum + 1 : ℕ) * soundError E q H 2) ?_) ?_
  · intro p τ key cache' seen' hc' hn' hgood
    unfold soundStartNext
    simp only [g, require_bind_run']
    by_cases hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0
    · simp only [if_pos hτ]
      apply sound_sliceRest_all prims K D A τ step q H counts.sum hr ha (sliceWidth_pos hpos) hτ
        sliceBits 0 1 (by omega) p.1 (fun i => i ∈ p.2)
        (fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) 0 1
        (fun i hi => ⟨rfl, rfl⟩)
      · exact hgood
      · exact hc'
      · simp only [checkRounds, halvings, Nat.add_mul, Nat.mul_add] at hb ⊢
        omega
      · simp [H, halvings]
        omega
    · simp only [if_neg hτ, ite_self, executePhase_failure]
      simp
  · have hmono := soundError_mono (E := E) q H (coins counts.sum) seen ∅ (by omega) (by simp)
    calc
      _ ≤ soundError E q H (coins counts.sum) +
          (halvings counts.sum + 1 : ℕ) * soundError E q H 2 := by
        simpa only [add_assoc] using add_le_add hmono
          (le_refl ((halvings counts.sum + 1 : ℕ) * soundError E q H 2))
      _ = _ := sound_error_sum K counts.sum q

/-- Soundness of the real check against every adversary satisfying the statement's query bound. -/

theorem checkSoundStage (prims : Primitives) (K : Constants C E)
    : CheckSoundStage prims K := by
  intro counts D A x z Z q hx hq hpos _ hagree hreject
  obtain ⟨start, step, final, hbudget, hstart, hr, ha, _⟩ := hq
  have hwrong := multVerify_reject_wrong_tuple D _ hagree hreject
  have hbound : Pr[fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some () |
      (simulateQ (localAnswer prims) (checkRealRun K (checkRounds counts.sum) D A x z)).run' ∅] ≤
      ENNReal.ofReal (checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q +
        soundHashError counts.sum q) := by
    unfold checkRealRun
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    obtain ⟨seen, hseen, hcard⟩ := localProgram_sound_covered prims
      (A.start (corruptInputs D x) z) start (hstart _ _) ∅ ∅ (by simp) p hp
    have hb : seen.card + checkRounds counts.sum * step ≤ q := by
      simp only [Finset.card_empty, zero_add] at hcard
      omega
    have h := checkSoundRoundInduction prims K counts D A x step q p.1 p.2 seen hx hpos hr ha hseen hb hagree hwrong
    rw [executePhase_congr_honest D A _ _ p.1 _ _ (fun i hi =>
      checkProtocol_startProg K i (x i) counts (hx.1 i hi) hpos)]
    exact h
  have hnonneg := add_nonneg (checkErrorOf_nonneg K (coins counts.sum) (halvings counts.sum) q)
    (soundHashError_nonneg counts.sum q)
  exact (ENNReal.toReal_le_toReal probEvent_ne_top ENNReal.ofReal_ne_top).mpr hbound |>.trans_eq
    (ENNReal.toReal_ofReal hnonneg)

/-- info: 'ThresholdLeanXmssSecurity.openValue_eq_interpolate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms openValue_eq_interpolate

/-- info: 'ThresholdLeanXmssSecurity.slice_effective_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slice_effective_card_le_two

/-- info: 'ThresholdLeanXmssSecurity.halving_effective_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms halving_effective_card_le_two

/-- info: 'ThresholdLeanXmssSecurity.finalOpen_challenge_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finalOpen_challenge_soundness

/-- info: 'ThresholdLeanXmssSecurity.localProgram_sound_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localProgram_sound_covered

/-- info: 'ThresholdLeanXmssSecurity.checkSoundStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkSoundStage

end ThresholdLeanXmssSecurity
