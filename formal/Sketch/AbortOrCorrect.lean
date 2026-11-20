import Sketch.Part2

/-!
# An honest tree run aborts or gives the ceremony output

`realTreeAbortOrCorrect` proves `RealTreeAbortOrCorrect` for each `prims`. A bad common coin of a
check makes every operator abort in the same round, so the honest run gives the output of the dealer
at every operator or no output at every operator. The copies of the bound lemmas of `Proof/Tree.lean`
below charge nothing for such a coin, because their event is false when no operator has an output.
`fixedLocal_support_run` moves the result from the random oracle to a fixed good `H`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

section Fixed

variable {C : Committee} (prims : Primitives)

/-- An answer of `H` under a good `h` that agrees with the cache is an answer of the random oracle. -/
theorem hashAnswer_mem (h : Query C → HashOutput) (hg : Good prims h) (q : Query C) (s : HashCache C)
    (ha : Agrees h s) : ∃ s', (h q, s') ∈ support ((hashAnswer prims q).run s) ∧ s ≤ s' ∧ Agrees h s' := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    refine ⟨s, ?_, le_rfl, ha⟩
    rw [hashAnswer_of_isFixed prims hm, hg input hm]
    simp
  · rw [hashAnswer_of_not_isFixed prims hq]
    rcases hs : s q with _ | v
    · refine ⟨s.cacheQuery q (h q), ?_, QueryCache.le_cacheQuery _ hs, fun q' v' hq' => ?_⟩
      · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs]
        erw [support_map, Set.mem_image]
        exact ⟨h q, by simp, rfl⟩
      · by_cases e : q' = q
        · subst e; simp at hq'; exact hq'
        · rw [QueryCache.cacheQuery_of_ne _ _ e] at hq'
          exact ha q' v' hq'
    · refine ⟨s, ?_, le_rfl, ha⟩
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs, ha q v hs]
      simp

/-- An answer of a local query under a good `h` that agrees with the cache is an answer of
`localAnswer`. -/
theorem localAnswer_mem (h : Query C → HashOutput) (hg : Good prims h) (t : (LocalSpec C).Domain)
    (s : HashCache C) (ha : Agrees h s) (u : (LocalSpec C).Range t) (hu : u ∈ support (fixedLocal prims h t)) :
    ∃ s', (u, s') ∈ support ((localAnswer prims t).run s) ∧ s ≤ s' ∧ Agrees h s' := by
  rcases t with n | q | x
  · refine ⟨s, ?_, le_rfl, ha⟩
    change (u, s) ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s)
    simp [unifFwdImpl]
  · change u ∈ support (pure (h q) : ProbComp _) at hu
    have hu' : u = h q := by simpa using hu
    subst hu'
    exact hashAnswer_mem prims h hg q s ha
  · change u ∈ support (pure (prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2) : ProbComp _) at hu
    have hu' : u = prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2 := by simpa using hu
    subst hu'
    obtain ⟨s', hs', hle, ha'⟩ := hashAnswer_mem prims h hg (.streamKey x.2.1) s ha
    refine ⟨s', ?_, hle, ha'⟩
    change _ ∈ support ((prgAnswer prims x).run s)
    unfold prgAnswer
    rw [StateT.run_bind]
    simp only [support_bind, Set.mem_iUnion]
    exact ⟨_, hs', by simp⟩

/-- Every run with `H` fixed to a good `h` is a run of the random oracle from each cache that
agrees with `h`, with an end cache that agrees with `h`. -/
theorem fixedLocal_support_run (h : Query C → HashOutput) (hg : Good prims h) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    ∀ s, Agrees h s → ∀ a ∈ support (simulateQ (fixedLocal prims h) oa),
      ∃ s', (a, s') ∈ support ((simulateQ (localAnswer prims) oa).run s) ∧ s ≤ s' ∧ Agrees h s' := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s ha a hx
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨s, by simp, le_rfl, ha⟩
  | query_bind t k ih =>
    intro s ha a hx
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      support_bind, Set.mem_iUnion] at hx
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨s₁, h₁, hle₁, ha₁⟩ := localAnswer_mem prims h hg t s ha u hu
    obtain ⟨s₂, h₂, hle₂, ha₂⟩ := ih u s₁ ha₁ a hx
    refine ⟨s₂, ?_, hle₁.trans hle₂, ha₂⟩
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion]
    exact ⟨(u, s₁), h₁, h₂⟩

end Fixed

section CoinSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- An event that is false when no operator has an output has probability zero after a common
failure. -/
theorem probEvent_failure_zero [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (event : (C.Party → Option α) → Prop) (hnone : ¬ event fun _ => none) (s : HashCache C) (ε : ℝ≥0∞) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun _ => (failure : PartyM C E (CallSpec I O) α)) >>= honestRounds F reply fuel)).run' s}[event z] ≤
      ε := by
  rw [honestRounds_failure]
  simp [hnone]

/-- `challenge_step` of `Proof/Tree.lean` with no charge. A failed challenge makes every operator
abort, and the event is false then. -/
theorem challenge_step_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → E → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (hnone : ¬ event fun _ => none)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (r : E) (Ks' : Finset HashOutput) (s' : HashCache C), Ks'.card ≤ Ks.card + 1 →
      CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i r (nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (challenge K (realCheckBuildingBlocks K (prssCtx keys kT kP i))).run (st i) >>= fun p =>
        g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε := by
  simp only [realChallenge_run, hL, hT, bind_assoc]
  refine coinPart_step prims K keys kT kP F reply fuel lab (fun i v => oracleStep (challengeQuery K tg lab v) >>=
    fun x => (match x with | some r => pure (r, nextLabel (st i)) | none => failure) >>= fun p => g i p.1 p.2)
    event s hn _ fun v s' hn' hle hfr => ?_
  have hs' := cacheOK_of_frame hs hfr
  refine (probEvent_honest_common prims F reply fuel (challengeQuery K tg lab v) _ event
    (fun _ => False) s' ε fun z hz _ => ?_).trans (by simp)
  rcases hr : z.1 with _ | r
  · simp only [failure_bind]
    exact probEvent_failure_zero prims F reply fuel event hnone z.2 ε
  obtain ⟨k, hk⟩ := challengeQuery_cache prims K tg lab v Ks Lk hLk s' hs' z hz
  obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
  simp only [pure_bind]
  exact h r (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn'' (hle.trans hle')

/-- `tau_step` of `Proof/Tree.lean` with no charge and with every coin `τ` in the continuation. -/
theorem tau_step_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (d : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → List E → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (τ : List E) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i τ (nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (coinKey K (realCheckBuildingBlocks K (prssCtx keys kT kP i)) >>= fun key =>
        expand K key d).run (st i) >>= fun p => g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤
      ε := by
  simp only [realTau_run, hL, hT, bind_assoc, pure_bind]
  refine coinPart_step prims K keys kT kP F reply fuel lab (fun i v => oracleStep (tauQuery K tg lab v d) >>=
    fun τ => g i τ (nextLabel (st i))) event s hn _ fun v s' hn' hle hfr => ?_
  have hs' := cacheOK_of_frame hs hfr
  refine (probEvent_honest_common prims F reply fuel (tauQuery K tg lab v d) _ event
    (fun _ => False) s' ε fun z hz _ => ?_).trans (by simp)
  obtain ⟨k, hk⟩ := tauQuery_cache_Ks prims K tg lab v d Ks Lk hLk s' hs' z hz
  obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
  exact h z.1 (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn'' (hle.trans hle')

theorem challenge_step_abort' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → E × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (hnone : ¬ event fun _ => none)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (r : E) (Ks' : Finset HashOutput) (s' : HashCache C), Ks'.card ≤ Ks.card + 1 →
      CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (r, nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (challenge K (realCheckBuildingBlocks K (prssCtx keys kT kP i))).run (st i) >>= g i) >>=
        honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε :=
  challenge_step_abort prims K keys kT kP F reply fuel st lab tg hL hT (fun i a b => g i (a, b)) event hnone s hn Ks Lk
    hLk hs ε h

theorem tau_step_abort' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (d : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → List E × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (τ : List E) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (τ, nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (coinKey K (realCheckBuildingBlocks K (prssCtx keys kT kP i)) >>= fun key =>
        expand K key d).run (st i) >>= g i) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε :=
  tau_step_abort prims K keys kT kP F reply fuel d st lab tg hL hT (fun i a b => g i (a, b)) event s hn Ks Lk hLk hs ε h

end CoinSteps

section RealFinal

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- `real_final_bound` of `Proof/Tree.lean` with no charge. -/
theorem real_final_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (A B : C.Party → ℕ → E) (D : C.Party → E) (a b : E)
    (hA : IsShamir K (fun i => A i 0) a) (hB : IsShamir K (fun i => B i 0) b) (hD : IsShamir K D (a * b))
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg : ℕ)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (hnone : ¬ event fun _ => none)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 4) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ⟨hist' i, lab + 4, tg⟩) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (finalStep K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i))
        (A i, B i, D i)).run ⟨hist i, lab, tg⟩ >>= fun p => g i p.2) >>= honestRounds F reply (fuel + 4))).run' s}[event z] ≤ ε := by
  have := charP_two (E := E)
  simp only [finalStep, StateT.run_bind, bind_assoc, realCheckBuildingBlocks_randElements,
      realCheckBuildingBlocks_randBits]
  refine rand_step' prims keys kT kP F reply (fuel + 4) (elementCodec K) (FrameR.elementDraw K) 1 2 _ lab
    (fun _ => rfl) _ event s hn _ fun r₁ zz₁ s₁ hn₁ hle₁ hfr₁ => ?_
  dsimp only [nextLabel]
  simp only [conv_prssCtx]
  set wa := fun i => conv K (localContext i) (honestR r₁ i) 0
  set wb := fun i => conv K (localContext i) (honestR r₁ i) 1
  refine extendMult_step' prims K keys kT kP F reply (fuel + 3) (fun i => [.shamir (fun _ => wa i) (fun _ => wb i) 1,
    .shamir (fun _ => wa i + A i 0) (fun _ => wb i + B i 0) 1]) 2 (fun _ => rfl) _ (lab + 1) (fun _ => rfl) _
    event s₁ hn₁ _ fun Z₂ hZ₂ s₂ hn₂ hle₂ hfr₂ => ?_
  dsimp only
  refine rand_step' prims keys kT kP F reply (fuel + 3) bitCodec (FrameR.bitDraw) 2 256 _ (lab + 1 + 1)
    (fun _ => rfl) _ event s₂ hn₂ _ fun r₃ zz₃ s₃ hn₃ hle₃ hfr₃ => ?_
  dsimp only [nextLabel]
  have hs₃ : CacheOK Ks Lk s₃ := cacheOK_of_frame (cacheOK_of_frame (cacheOK_of_frame hs hfr₁) hfr₂) hfr₃
  have hh₄ := histAgree_record K hist hh (fun i T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) Z₂ 2
    (fun i T g hi hg => by simp [hi, hg])
  refine digest_step' prims keys kT kP F reply (fuel + 2) _ hh₄ (fun i => honestR r₃ i) r₃
    (fun i T hT => by simp [honestR, hT]) _ event s₃ hn₃ Ks Lk hs₃ _ fun s₄ hs₄ hn₄ hle₄ => ?_
  dsimp only
  refine challenge_step_abort' prims K keys kT kP F reply (fuel + 1) _ (lab + 1 + 1 + 1) tg (fun _ => rfl) (fun _ => rfl) _
    event hnone s₄ hn₄ Ks Lk (by omega) hs₄ ε fun r Ks' s₅ hKs' hs₅ hn₅ hle₅ => ?_
  dsimp only [nextLabel]
  simp only [StateT.run_lift, bind_assoc, pure_bind, openSh_prssCtx]
  have hwa : IsShamir K wa (∑ T, r₁ T 0) := isShamir_honestR K r₁ 0
  have hwb : IsShamir K wb (∑ T, r₁ T 1) := isShamir_honestR K r₁ 1
  have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
      (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) k) (∑ T, Z₂ T k) := fun k hk =>
    (isShamir_conv Z₂ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
  have hq0 : ∑ T, Z₂ T 0 = (∑ T, r₁ T 0) * (∑ T, r₁ T 1) := by
    rw [hZ₂ 0]
    simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext, Finset.sum_range_one]
    exact sum_lagrangeAll_shamir K hwa hwb
  have hq1 : ∑ T, Z₂ T 1 = ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) := by
    rw [hZ₂ 1]
    simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
      localContext, Finset.sum_range_one]
    exact sum_lagrangeAll_shamir K (hwa.add hA) (hwb.add hB)
  set vals : ℕ → E := fun k => match k with
    | 0 => (∑ T, r₁ T 0) + r * ((∑ T, r₁ T 0) + a)
    | 1 => (∑ T, r₁ T 1) + r * ((∑ T, r₁ T 1) + b)
    | _ => (∑ T, r₁ T 0) * (∑ T, r₁ T 1) +
        (a * b + (∑ T, r₁ T 0) * (∑ T, r₁ T 1) + ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b)) * r +
        ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) * r ^ 2 with hvals
  have hv : ∀ k < 3, IsShamir K (fun i => (fun k => match k with
      | 0 => wa i + r * (wa i + A i 0)
      | 1 => wb i + r * (wb i + B i 0)
      | _ => conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 0 +
          (D i + conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 0 +
            conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 1) * r +
          conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 1 * r ^ 2 : ℕ → E) k)
      (vals k) := by
    intro k hk
    interval_cases k
    · exact (hwa.add ((hwa.add hA).mul_left r)).congr (fun i => rfl) rfl
    · exact (hwb.add ((hwb.add hB).mul_left r)).congr (fun i => rfl) rfl
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine ((h0.add (((hD.add h0).add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
      rw [hq0, hq1]; rfl
  have hfinal : vals 0 * vals 1 = vals 2 := by
    have two : (2 : E) = 0 := CharTwo.two_eq_zero
    simp only [hvals]
    linear_combination (-(a * b * r)) * two
  refine openSh_step prims K F reply fuel _ vals 3 hv _ event s₅ ε ?_
  have hc : ∀ i, openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 0 *
      openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 1 =
      openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 2 := fun i => by
    have hval := (openShN_honest K _ vals 3 hv i).2
    rw [hval 0 (by norm_num), hval 1 (by norm_num), hval 2 (by norm_num), hfinal]
  simp only [require_bind_of (hc _)]
  exact h _ Ks' s₅ hKs' hs₅ hn₅ (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans hle₅))))

end RealFinal

section RealHalving

open Finset

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- `real_halving_bound` of `Proof/Tree.lean` with no charge. -/
theorem real_halving_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (width : ℕ)
    (hwidth : 1 ≤ width) :
    ∀ (n j₀ : ℕ), j₀ + n = halvingSteps width → ∀ (A B : C.Party → ℕ → E) (D : C.Party → E) (Av Bv : ℕ → E),
      (∀ k, IsShamir K (fun i => A i k) (Av k)) → (∀ k, IsShamir K (fun i => B i k) (Bv k)) →
      IsShamir K D (∑ k ∈ range (halvedLength^[j₀] width), Av k * Bv k) →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop), ¬ event (fun _ => none) → ∀ (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + n + 1 → CacheOK Ks' (lab + 2 * n + 4) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i ⟨hist' i, lab + 2 * n + 4, tg⟩) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (halvingStep K (prssCtx keys kT kP i)
          (realCheckBuildingBlocks K (prssCtx keys kT kP i)) width) (A i, B i, D i)).run ⟨hist i, lab, tg⟩ >>= fun x =>
            (finalStep K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i)) x.1).run
                x.2 >>=
              fun p => g i p.2) >>= honestRounds F reply (fuel + 2 * n + 4))).run' s}[event z] ≤ ε := by
  intro n
  induction n with
  | zero =>
    intro j₀ hj A B D Av Bv hA hB hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, Nat.mul_zero, Nat.add_zero]
    rw [Nat.add_zero] at hj
    subst hj
    rw [iterate_halvingSteps width hwidth, Finset.sum_range_one] at hD
    exact real_final_abort prims K keys kT kP F reply fuel A B D (Av 0) (Bv 0) (hA 0) (hB 0) hD hist hh lab tg g
      event hnone s hn Ks Lk hLk hs ε fun hist' Ks' s' h1 h2 h3 h4 => h hist' Ks' s' (by omega) h2 h3 h4
  | succ n ih =>
    intro j₀ hj A B D Av Bv hA hB hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    have := charP_two (E := E)
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 4 = (fuel + 2 * n + 5) + 1 by ring]
    simp only [List.foldlM_cons, halvingStep, bind_assoc, pure_bind, StateT.run_bind]
    set ℓ := halvedLength^[j₀] width with hℓ
    set half := halvedLength ℓ with hhalf
    let hiv := fun (v : ℕ → E) k => if k + half < ℓ then v (k + half) else 0
    refine extendMult_step' prims K keys kT kP F reply (fuel + 2 * n + 5) (fun i => [.shamir (A i) (B i) half,
      .shamir (fun k => A i k + hiv (A i) k) (fun k => B i k + hiv (B i) k) half]) 2 (fun _ => rfl) _ lab
      (fun _ => rfl) _ event s hn _ fun Z₁ hZ₁ s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hs₁ := cacheOK_of_frame hs hfr₁
    refine challenge_step_abort' prims K keys kT kP F reply (fuel + 2 * n + 4) _ (lab + 1) tg (by intro; rfl)
      (by intro; rfl) _ event hnone s₁ hn₁ Ks Lk (by omega) hs₁ ε ?_
    intro r Ks₂ s₂ hKs₂ hs₂ hn₂ hle₂
    dsimp only [nextLabel]
    have hhi : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => hiv (f i) k) (hiv a k) := fun f a hf k => (hf (k + half)).ite K _
    have hfold : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => f i k + r * (f i k + hiv (f i) k)) (a k + r * (a k + hiv a k)) :=
      fun f a hf k => (hf k).add (((hf k).add (hhi f a hf k)).mul_left r)
    have hsum : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => f i k + hiv (f i) k) (a k + hiv a k) :=
      fun f a hf k => (hf k).add (hhi f a hf k)
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₁ T g else 0) k) (∑ T, Z₁ T k) := fun k hk =>
      (isShamir_conv Z₁ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₁ T 0 = ∑ k ∈ range half, Av k * Bv k := by
      rw [hZ₁ 0]
      simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext]
      exact sum_lagrangeAll_shamir_sum K hA hB half
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, (Av k + hiv Av k) * (Bv k + hiv Bv k) := by
      rw [hZ₁ 1]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
        localContext]
      exact sum_lagrangeAll_shamir_sum K (hsum A Av hA) (hsum B Bv hB) half
    simp only [conv_prssCtx]
    refine ih (j₀ + 1) (by omega) _ _ _ (fun k => Av k + r * (Av k + hiv Av k))
      (fun k => Bv k + r * (Bv k + hiv Bv k)) (hfold A Av hA) (hfold B Bv hB) ?_ _
      (histAgree_record K hist hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (lab + 1 + 1) tg (lab + 1 + 1)
      (c + 1) Ks₂ le_rfl (by omega) s₂ hn₂ hs₂ fuel g event hnone ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine ((h0.add ((hD.add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
      rw [hq0, hq1, Function.iterate_succ_apply', ← hℓ, ← hhalf, sum_range_halving_fold, sum_range_padded Av Bv ℓ]
    · have hlab : lab + 1 + 1 + 2 * n + 4 = lab + 2 * (n + 1) + 4 := by ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans (hle₂.trans h4))

end RealHalving

section RealSlice

open Finset

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- `real_slice_bound` of `Proof/Tree.lean` with no charge. -/
theorem real_slice_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (τ : List E) (count : ℕ)
    (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0) (hwidth : 0 < sliceWidth count) :
    ∀ (n j₀ : ℕ), j₀ + n = sliceBits → ∀ (xs ys : C.Party → Shares C E) (D : C.Party → E) (XS YS : Shares C E),
      (∀ i T, i ∈ C.holders T → xs i T = XS T ∧ ys i T = YS T) →
      IsShamir K D (∑ k ∈ range (sliceWidth count * 2 ^ (sliceBits - j₀)),
        coinProduct τ 0 (sliceBits - j₀) (k / sliceWidth count) * (∑ T, XS T k) * ∑ T, YS T k) →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop), ¬ event (fun _ => none) → ∀ (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + n + halvingSteps (sliceWidth count) + 1 →
        CacheOK Ks' (lab + 2 * n + 2 * halvingSteps (sliceWidth count) + 4) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i ⟨hist' i, lab + 2 * n + 2 * halvingSteps (sliceWidth count) + 4, tg⟩) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (sliceStep K (prssCtx keys kT kP i)
          (realCheckBuildingBlocks K (prssCtx keys kT kP i)) τ count) (xs i, ys i, D i)).run ⟨hist i, lab, tg⟩ >>= fun p =>
            ((List.range (halvingSteps (sliceWidth count))).foldlM (halvingStep K (prssCtx keys kT kP i)
              (realCheckBuildingBlocks K (prssCtx keys kT kP i)) (sliceWidth count))
              (conv K (prssCtx keys kT kP i) p.1.1, conv K (prssCtx keys kT kP i) p.1.2.1, p.1.2.2)).run p.2 >>= fun x =>
            (finalStep K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i)) x.1).run
                x.2 >>=
              fun q => g i q.2) >>=
          honestRounds F reply (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 4))).run' s}[event z] ≤ ε := by
  have := charP_two (E := E)
  intro n
  induction n with
  | zero =>
    intro j₀ hj xs ys D XS YS hxy hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, Nat.mul_zero, Nat.add_zero]
    rw [Nat.add_zero] at hj
    subst hj
    rw [List.range_eq_range']
    simp only [conv_prssCtx]
    refine real_halving_abort prims K keys kT kP F reply (sliceWidth count) hwidth _ 0 (by omega) _ _ D
      (fun k => ∑ T, XS T k) (fun k => ∑ T, YS T k) (fun k => (isShamir_conv XS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).1]).symm) rfl)
      (fun k => (isShamir_conv YS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).2]).symm) rfl) ?_ hist hh lab tg Lk c Ks hLk hKs s hn hs
      fuel g event hnone ε fun hist' Ks' s' h1 h2 h3 h4 => h hist' Ks' s' (by omega) h2 h3 h4
    refine hD.congr (fun i => rfl) ?_
    simp only [Nat.sub_self, pow_zero, mul_one, Function.iterate_zero, id, coinProduct_zero_width, one_mul]
  | succ n ih =>
    intro j₀ hj xs ys D XS YS hxy hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 2 * halvingSteps (sliceWidth count) + 4 =
      (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 5) + 1 by ring]
    simp only [List.foldlM_cons, sliceStep, bind_assoc, pure_bind, StateT.run_bind]
    set width := sliceWidth count with hwidth_def
    set half := width * 2 ^ (sliceBits - 1 - j₀) with hhalf
    set rest := fun k => coinProduct τ 0 (sliceBits - 1 - j₀) (k / width) with hrest
    refine extendMult_step' prims K keys kT kP F reply (fuel + 2 * n + 2 * halvingSteps width + 5)
      (fun i => [.replicated (fun T k => rest k * xs i T k) (ys i) half,
        .replicated (fun T k => rest k * (xs i T k + xs i T (k + half))) (fun T k => ys i T k + ys i T (k + half)) half])
      2 (fun _ => rfl) _ lab (fun _ => rfl) _ event s hn _ fun Z₁ hZ₁ s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hs₁ := cacheOK_of_frame hs hfr₁
    refine challenge_step_abort' prims K keys kT kP F reply (fuel + 2 * n + 2 * halvingSteps width + 4) _
      (lab + 1) tg (by intro; rfl) (by intro; rfl) _ event hnone s₁ hn₁ Ks Lk (by omega) hs₁ ε ?_
    intro r Ks₂ s₂ hKs₂ hs₂ hn₂ hle₂
    dsimp only [nextLabel]
    have hw : sliceBits - 1 - j₀ = n := by omega
    set cc := τ.getD (sliceBits - 1 - j₀) 0 with hcc
    have hc : cc ≠ 0 := hτ _ (by omega)
    let Xv := fun k => ∑ T, XS T k
    let Yv := fun k => ∑ T, YS T k
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₁ T g else 0) k) (∑ T, Z₁ T k) := fun k hk =>
      (isShamir_conv Z₁ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₁ T 0 = ∑ k ∈ range half, rest k * Xv k * Yv k := by
      rw [hZ₁ 0]
      simp only [extendMultShare, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * XS T k) YS half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => (hxy i T hT).2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum]
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, rest k * (Xv k + Xv (k + half)) * (Yv k + Yv (k + half)) := by
      rw [hZ₁ 1]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * (XS T k + XS T (k + half)))
        (fun T k => YS T k + YS T (k + half)) half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => by funext k; rw [(hxy i T hT).2])]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsplit := slice_sum_split τ width (sliceBits - 1 - j₀) hwidth Xv Yv
    rw [show sliceBits - 1 - j₀ + 1 = sliceBits - j₀ by omega] at hsplit
    simp only [conv_prssCtx]
    refine ih (j₀ + 1) (by omega) _ _ _ (fun T k => XS T k + r * (XS T k + XS T (k + half)))
      (fun T k => YS T k + r * (YS T k + YS T (k + half)))
      (fun i T hT => ⟨by funext k; rw [(hxy i T hT).1], by funext k; rw [(hxy i T hT).2]⟩) ?_ _
      (histAgree_record K hist hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (lab + 1 + 1) tg (lab + 1 + 1)
      (c + 1) Ks₂ le_rfl (by omega) s₂ hn₂ hs₂ fuel g event hnone ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine (((h0.mul_left (1 + r)).add (((hD.add h0).div cc).mul_left r)).add (h1.mul_left (r * (1 + r)))).congr
        (fun i => rfl) ?_
      rw [hq0, hq1, show sliceBits - (j₀ + 1) = sliceBits - 1 - j₀ by omega]
      rw [sum_range_slice_fold rest Xv Yv half r cc _ hc hsplit]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    · have hlab : lab + 1 + 1 + 2 * n + 2 * halvingSteps width + 4 =
          lab + 2 * (n + 1) + 2 * halvingSteps width + 4 := by ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans (hle₂.trans h4))

end RealSlice

section RealCheck

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- `real_check_bound` of `Proof/Tree.lean` with no charge. A coin `τ` with a zero makes every
operator abort. -/
theorem real_check_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R)
    (tuples : C.Party → List (Tuple C)) (cnt : ℕ) (hcnt : ∀ i, ((tuples i).map (·.count)).sum = cnt) (hpos : cnt ≠ 0)
    (LX LY LZ : Shares C E)
    (hag : ∀ i T, i ∈ C.holders T → liftedPart (E := E) (tuples i) (·.x) T = LX T ∧
      liftedPart (E := E) (tuples i) (·.y) T = LY T ∧ liftedPart (E := E) (tuples i) (·.z) T = LZ T)
    (hprod : ∀ k, ∑ T, LZ T k = (∑ T, LX T k) * ∑ T, LY T k)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (hnone : ¬ event fun _ => none) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + halvings cnt + 2 → CacheOK Ks' (lab + 2 * halvings cnt + 5) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ⟨hist' i, lab + 2 * halvings cnt + 5, tg⟩) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (check K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i))
        (tuples i)).run ⟨hist i, lab, tg⟩ >>= fun p => g i p.2) >>=
          honestRounds F reply (fuel + 2 * halvings cnt + 5))).run' s}[event z] ≤ ε := by
  have := charP_two (E := E)
  have hne : ∀ i, ((tuples i).map (·.count)).sum ≠ 0 := fun i => by rw [hcnt i]; exact hpos
  simp only [check_eq _ _ _ _ (hne _), hcnt, StateT.run_bind, bind_assoc]
  rw [show fuel + 2 * halvings cnt + 5 = (fuel + 2 * halvings cnt + 4) + 1 by ring]
  simp only [tau_split]
  refine tau_step_abort' prims K keys kT kP F reply (fuel + 2 * halvings cnt + 4) (coins cnt) _
    lab tg (by intro; rfl) (by intro; rfl) _ event s hn Ks Lk hLk hs _ ?_
  intro τ Ks₁ s₁ hKs₁ hs₁ hn₁ hle₁
  dsimp only [nextLabel]
  by_cases hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0
  swap
  · simp only [StateT.run_lift, require, hτ, ↓reduceIte, failure_bind]
    exact probEvent_failure_zero prims F reply _ event hnone s₁ ε
  simp only [StateT.run_lift, require_bind_of hτ, pure_bind]
  have hR : halvings cnt = sliceBits + halvingSteps (sliceWidth cnt) := rfl
  rw [show List.range sliceBits = List.range' 0 sliceBits from List.range_eq_range',
    show halvings cnt - sliceBits = halvingSteps (sliceWidth cnt) by omega,
    show fuel + 2 * halvings cnt + 4 = fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth cnt) + 4 by omega]
  refine real_slice_abort prims K keys kT kP F reply τ cnt hτ (sliceWidth_pos hpos) sliceBits 0 (by simp) _ _ _
    (fun T k => wordWeightOf K τ cnt k * LX T k) LY
    (fun i T hT => ⟨by funext k; simp only [(hag i T hT).1], (hag i T hT).2.1⟩) ?_ hist hh (lab + 1) tg (lab + 1)
    (c + 1) Ks₁ le_rfl (by omega) s₁ hn₁ hs₁ fuel g event hnone ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
  · refine (isShamir_conv (claimOf K τ cnt LZ) 0).congr (fun i => (conv_congr i _ _ 0 fun T hT => by
      simp only [claimOf, (hag i T hT).2.2]).symm) ?_
    simp only [claimOf, Nat.sub_zero]
    rw [Finset.sum_comm, mul_comm (sliceWidth cnt)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, hprod k, ← Finset.mul_sum]
    simp only [sliceOf]
    ring
  · have hlab : lab + 1 + 2 * sliceBits + 2 * halvingSteps (sliceWidth cnt) + 4 = lab + 2 * halvings cnt + 5 := by
      omega
    rw [hlab] at h2 ⊢
    exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans h4)

end RealCheck

section Tail

open Finset

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- `real_check_any` of `Proof/Tree.lean` with no charge. -/
theorem real_check_any_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R)
    (tuples : C.Party → List (Tuple C)) (cnt : ℕ) (hcnt : ∀ i, ((tuples i).map (·.count)).sum = cnt)
    (LX LY LZ : Shares C E)
    (hag : ∀ i T, i ∈ C.holders T → liftedPart (E := E) (tuples i) (·.x) T = LX T ∧
      liftedPart (E := E) (tuples i) (·.y) T = LY T ∧ liftedPart (E := E) (tuples i) (·.z) T = LZ T)
    (hprod : ∀ k, ∑ T, LZ T k = (∑ T, LX T k) * ∑ T, LY T k)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → Unit × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (hnone : ¬ event fun _ => none) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + checkKeys cnt → CacheOK Ks' (lab + checkLabels cnt) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((), ⟨hist' i, lab + checkLabels cnt, tg⟩)) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (check K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i))
        (tuples i)).run ⟨hist i, lab, tg⟩ >>= g i) >>=
          honestRounds F reply (fuel + checkLabels cnt))).run' s}[event z] ≤ ε := by
  by_cases hpos : cnt = 0
  · have h0 : ∀ i, ((tuples i).map (·.count)).sum = 0 := fun i => by rw [hcnt i, hpos]
    simp only [check_zero_run _ _ _ _ (h0 _), pure_bind, checkLabels, checkKeys, hpos, ↓reduceIte,
      Nat.add_zero] at h ⊢
    exact h hist Ks s (by omega) (hs.mono_label hLk) hn le_rfl
  · simp only [checkLabels, checkKeys, hpos, ↓reduceIte] at h ⊢
    exact real_check_abort prims K keys kT kP F reply tuples cnt hcnt hpos LX LY LZ hag hprod hist hh lab tg Lk c Ks
      hLk hKs s hn hs fuel (fun i st => g i ((), st)) event hnone ε h

/-- `tail_bound` of `Proof/Tree.lean` with no charge. -/
theorem tail_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit))
    (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit)) (Ts : List (Tuple C))
    (hinv : LayerInv jobs x (depth jobs) p W Ts) (cnt : ℕ)
    (hcnt : (Ts.map (·.count)).sum + (ThresholdLeanXmssSecurity.outputsOf jobs).length = cnt)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (hnone : ¬ event fun _ => none) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + checkKeys cnt → CacheOK Ks' (lab + 1 + checkLabels cnt) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (mainOutputs jobs x, ⟨hist' i, lab + 1 + checkLabels cnt, tg⟩)) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (tailBody K (realRunBuildingBlocks K (prssCtx keys kT kP i) mode) jobs (p i)).run
        ⟨hist i, lab, tg⟩ >>= g i) >>= honestRounds F reply (fuel + 1 + checkLabels cnt + 1))).run' s}[event z] ≤ ε := by
  set n := (ThresholdLeanXmssSecurity.outputsOf jobs).length with hn_def
  simp only [tailBody, StateT.run_bind, bind_assoc]
  refine rerand_step prims K keys kT kP F reply (fuel + 1 + checkLabels cnt) mode
    (fun i => outputShares K jobs (p i).1) n _ lab (fun _ => rfl) _ event s hn _ fun z hz s₁ hn₁ hle₁ hfr₁ => ?_
  dsimp only
  have hO : ∀ i T, i ∈ C.holders T → outputShares K jobs (p i).1 T = outputShares K jobs W T :=
    fun i T h => outputShares_congr K jobs _ _ T (hinv.agree i T h)
  have hsum : ∀ k, ∑ T, z T k = shareValue (outputShares K jobs W) k := fun k => by
    rw [hz k, sum_ownerSum K _ _ hO]
  set zv : C.Party → Shares C Bit := fun i T k => if i ∈ C.holders T ∧ k < n then z T k else 0 with hzv
  set w : Shares C Bit := fun T k => if k < n then z T k else 0 with hw
  set Ts' := Ts ++ [(⟨outputShares K jobs W, one K, w, n, .peer⟩ : Tuple C)] with hTs'
  have hlen' : ∀ i, ((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)]).length = Ts'.length :=
    fun i => by simp [hTs', hinv.length_tuples]
  have hag' : ∀ i, ∀ m (hm : m < Ts'.length), TupleAgrees i
      (((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)])[m]'(by rw [hlen' i]; exact hm)) Ts'[m] :=
    fun i => tupleAgrees_append i _ _ _ _ (hinv.length_tuples i) (hinv.agree_tuples i)
      ⟨fun T hT => ⟨hO i T hT, rfl, funext fun g => by simp [hzv, hw, hT]⟩, rfl, rfl⟩
  have hprodTs : ∀ τ ∈ Ts', IsProduct τ := by
    intro τ hτ
    rcases List.mem_append.1 hτ with hτ | hτ
    · exact hinv.product τ hτ
    · simp only [List.mem_singleton] at hτ
      subst hτ
      intro g hg
      rw [shareValue_one, mul_one, ← hsum g]
      simp only [shareValue, hw, hg, ↓reduceIte]
  have hcnt' : ∀ i, (((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)]).map (·.count)).sum = cnt :=
    fun i => by
      rw [map_count_of_agree i _ _ (hlen' i) (hag' i), hTs', List.map_append, List.sum_append, ← hcnt]
      simp
  have hh₁ := histAgree_recordMode K .peer hist hh zv z n (fun i T g hi hg => by simp [hzv, hi, hg])
  simp only [realRunBuildingBlocks]
  rw [show fuel + 1 + checkLabels cnt = (fuel + 1) + checkLabels cnt from rfl]
  refine real_check_any_abort prims K keys kT kP F reply _ cnt hcnt' (liftedPart Ts' (·.x)) (liftedPart Ts' (·.y))
    (liftedPart Ts' (·.z)) (fun i T hT => liftedPart_agree' i _ Ts' (hlen' i) (hag' i) T hT)
    (liftedPart_product Ts' hprodTs) _ hh₁ (lab + 1) tg Lk c Ks (by omega) hKs s₁ hn₁ (cacheOK_of_frame hs hfr₁)
    (fuel + 1) _ event hnone ε fun hist' Ks' s₂ hKs₂ hs₂ hn₂ hle₂ => ?_
  dsimp only
  simp only [StateT.run_lift, bind_assoc, pure_bind, openRep_prssCtx]
  refine openRep_step prims K F reply fuel zv w n (fun i T g hi hg => by simp [hzv, hw, hi, hg]) _ event s₂ hn₂ ε
    fun V hV s₃ hn₃ hle₃ hfr₃ => ?_
  have hA : ∀ i, ThresholdLeanXmssSecurity.assemble jobs (V i) = mainOutputs jobs x := fun i =>
    assemble_eq K jobs x p W Ts hinv (V i) fun g hg => by
      rw [hV i g hg, ← hsum g]; simp only [hw]; exact Finset.sum_congr rfl fun T _ => ite_eq_left_of_eq_true _ _ (eq_true hg)
  simp only [hA]
  have hs₃ : CacheOK Ks' (lab + 1 + checkLabels cnt) s₃ := cacheOK_of_frame hs₂ hfr₃
  exact h hist' Ks' s₃ hKs₂ hs₃ hn₃ (hle₁.trans (hle₂.trans hle₃))

/-- `layers_bound` of `Proof/Tree.lean` with no charge. -/
theorem layers_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit)) :
    ∀ (k l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
      (Ts : List (Tuple C)), l + k = depth jobs → LayerInv jobs x l p W Ts →
      (Ts.map (·.count)).sum = ((List.range l).map fun l' => (gatesAt jobs l').length).sum →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
      (event : (C.Party → Option α) → Prop), ¬ event (fun _ => none) → ∀ (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + checkKeys (tupleCount jobs) →
        CacheOK Ks' (lab + k + 1 + checkLabels (tupleCount jobs)) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i (mainOutputs jobs x, ⟨hist' i, lab + k + 1 + checkLabels (tupleCount jobs), tg⟩)) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' l k).foldlM (layerBody K (realRunBuildingBlocks K (prssCtx keys kT kP i) mode) jobs)
          (p i)).run ⟨hist i, lab, tg⟩ >>= fun q =>
            (tailBody K (realRunBuildingBlocks K (prssCtx keys kT kP i) mode) jobs q.1).run q.2 >>= g i) >>=
          honestRounds F reply (fuel + k * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1))).run' s}[event z] ≤ ε := by
  intro k
  induction k with
  | zero =>
    intro l p W Ts hl hinv hTs hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, zero_mul, Nat.add_zero] at h ⊢
    rw [Nat.add_zero] at hl
    subst hl
    exact tail_abort prims K keys kT kP F reply mode jobs x p W Ts hinv (tupleCount jobs)
      (by rw [hTs, tupleCount_eq]) hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
  | succ k ih =>
    intro l p W Ts hl hinv hTs hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    rw [List.range'_succ, show fuel + (k + 1) * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1 =
      (fuel + k * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1) + mode.rounds by ring]
    simp only [List.foldlM_cons, layerBody, StateT.run_bind, bind_assoc, pure_bind]
    refine mult_step prims K keys kT kP F reply _ mode (fun i => layerX K jobs l (p i).1)
      (fun i => layerY K jobs l (p i).1) (gatesAt jobs l).length _ lab (fun _ => rfl) _ event s hn _
      fun z hz s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hinv' := layerInv_step K jobs x mode l p W Ts hinv z hz
    simp only [realRunBuildingBlocks] at hinv' ⊢
    refine ih (l + 1) _ _ _ (by omega) hinv' ?_ _
      (histAgree_recordMode K mode hist hh _ z _ fun i T g hi hg => by simp [hi, hg]) (lab + 1) tg Lk c Ks
      (by omega) hKs s₁ hn₁ (cacheOK_of_frame hs hfr₁) fuel g event hnone ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · rw [List.map_append, List.sum_append, hTs, List.range_succ, List.map_append, List.sum_append]
      simp
    · have hlab : lab + 1 + k + 1 + checkLabels (tupleCount jobs) = lab + (k + 1) + 1 + checkLabels (tupleCount jobs) := by
        ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' h1 h2 h3 (hle₁.trans h4)

end Tail

section Chunks

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E)

/-- `batch_step` of `Proof/Tree.lean` with no charge. -/
theorem batch_step_abort [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (jobs : List Job)
    (lab tg Lk c : ℕ) (Ks : Finset HashOutput) (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (hnone : ¬ event fun _ => none) (ε : ℝ≥0∞)
    (h : ∀ (outs : List (List Bit)) (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
        outs = jobs.map fun job => D prims h' (evalJob circuits parameter seeds job)) →
      Ks'.card ≤ c + checkKeys (tupleCount (jobs.map (circuits parameter ·.kind))) →
      CacheOK Ks' (lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
        checkLabels (tupleCount (jobs.map (circuits parameter ·.kind)))) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (outs, ⟨hist' i, lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))), tg⟩)) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (jobs.mapM (inputShares (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i))) >>=
        fun inputs => (runJobs K (realRunBuildingBlocks K (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) mode)
          (jobs.map (circuits parameter ·.kind)) inputs).run ⟨fun _ => [], lab, tg⟩ >>= g i) >>=
        honestRounds F reply (fuel + depth (jobs.map (circuits parameter ·.kind)) * mode.rounds + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1))).run' s}[event z] ≤ ε := by
  set circs := jobs.map (circuits parameter ·.kind) with hcircs
  simp only [inputShares_fun, mapM_oracleStep]
  refine draw_step2 prims F reply _ (fun i => jobs.mapM (inputQuery (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i)))
    (fun i => FrameR.mapM _ (fun job => FrameR.inputQuery prims _ job) _) _ event s hn _
    fun w s₁ hw hn₁ hle₁ hfr₁ => ?_
  have hwv : ∀ h' s'', Good prims h' → s₁ ≤ s'' → Agrees h' s'' → ∀ i, w i = batchInputs h' seeds jobs i := by
    intro h' s'' hg hle ha i
    rw [hw h' s'' hg hle ha i, D_mapM]
    exact List.map_congr_left fun job _ => funext fun T => D_inputQuery prims h' parameter seeds pairKeys kT kP i job T
  obtain ⟨h₁, hg₁, ha₁⟩ : ∃ h₁, Good prims h₁ ∧ Agrees h₁ s₁ := ⟨hashOf prims s₁, good_hashOf prims s₁,
    agrees_hashOf prims hn₁⟩
  have hw₁ : w = batchInputs h₁ seeds jobs := funext (hwv h₁ s₁ hg₁ le_rfl ha₁)
  rw [hw₁]
  simp only [runJobs_eq, StateT.run_bind, bind_assoc]
  rw [List.range_eq_range']
  have hW := layerInv_zero (jobs := circs) (x := batchInputs h₁ seeds jobs)
    (batchInputs_main h₁ seeds circuits parameter jobs)
  refine layers_abort prims K (dealtKeys parameter seeds pairKeys) kT kP F reply mode circs (batchInputs h₁ seeds jobs)
    (depth circs) 0 _ _ [] (by simp) hW (by simp) (fun _ _ => []) (fun _ _ _ _ _ => rfl) lab tg Lk c Ks hLk hKs s₁ hn₁
    (cacheOK_of_frame hs hfr₁) fuel g event hnone ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
  refine h _ hist' Ks' s' (fun h' s'' hg hle ha => ?_) h1 (by simpa using h2) h3 (hle₁.trans h4)
  rw [← mainOutputs_batch prims h' seeds circuits parameter jobs, ← hw₁]
  congr 1
  exact funext (hwv h' s'' hg (h4.trans hle) ha)

end Chunks

section ChunksStep

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (mode : ReshareMode)

/-- `chunks_step` of `Proof/Tree.lean` with no charge. -/
theorem chunks_abort [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) {α : Type} :
    ∀ (js : List (List Job)) (lab k Lk c : ℕ) (Ks : Finset HashOutput), Lk ≤ lab → Ks.card ≤ c →
      ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → List (Option (List (List Bit))) × (ℕ × ℕ) → PartyM C E RealSpec α)
      (event : (C.Party → Option α) → Prop), ¬ event (fun _ => none) → ∀ (ε : ℝ≥0∞),
      (∀ (outs : List (Option (List (List Bit)))) (Ks' : Finset HashOutput) (s' : HashCache C),
        (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
          outs = js.map fun jobs => some (jobs.map fun job => D prims h' (evalJob circuits parameter seeds job))) →
        Ks'.card ≤ c + (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum →
        CacheOK Ks' (lab + (js.map (batchLabels circuits parameter)).sum) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i (outs, (lab + (js.map (batchLabels circuits parameter)).sum, k + js.length))) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => (js.mapM (realBatch K circuits mode (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i)
          parameter)).run (lab, k) >>= g i) >>=
          honestRounds F reply (fuel + (js.map (batchRounds circuits mode parameter)).sum))).run' s}[event z] ≤ ε := by
  intro js
  induction js with
  | nil =>
    intro lab k Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    simp only [List.mapM_nil, StateT.run_pure, pure_bind, List.map_nil, List.sum_nil, Nat.add_zero,
      List.length_nil] at h ⊢
    exact h [] Ks s (fun _ _ _ _ _ => rfl) hKs (hs.mono_label hLk) hn le_rfl
  | cons jobs js ih =>
    intro lab k Lk c Ks hLk hKs s hn hs fuel g event hnone ε h
    simp only [List.mapM_cons, StateT.run_bind, realBatch_run, bind_assoc, pure_bind, StateT.run_pure]
    rw [show fuel + ((jobs :: js).map (batchRounds circuits mode parameter)).sum =
      (fuel + (js.map (batchRounds circuits mode parameter)).sum) + depth (jobs.map (circuits parameter ·.kind)) * mode.rounds +
        1 + checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1 by
      simp only [List.map_cons, List.sum_cons, batchRounds, batchCount]; ring]
    refine batch_step_abort prims K F reply mode circuits parameter seeds pairKeys kT kP jobs lab k Lk c Ks hLk hKs s hn hs
      _ _ event hnone ε ?_
    · intro outs hist' Ks' s' houts hKs' hs' hn' hle'
      dsimp only
      refine ih _ (k + 1) _ (c + checkKeys (batchCount circuits parameter jobs)) Ks' le_rfl hKs' s' hn' hs' fuel _ event hnone ε ?_
      intro outs' Ks'' s'' houts' hKs'' hs'' hn'' hle''
      dsimp only
      have hlab : lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + (js.map (batchLabels circuits parameter)).sum =
          lab + ((jobs :: js).map (batchLabels circuits parameter)).sum := by
        simp only [List.map_cons, List.sum_cons, batchLabels, batchCount]; ring
      have hk : k + 1 + js.length = k + (jobs :: js).length := by simp; ring
      rw [hlab, hk]
      refine h _ Ks'' s'' (fun h' s₃ hg hle ha => ?_) (by simp only [List.map_cons, List.sum_cons]; omega) (hlab ▸ hs'') hn''
        (hle'.trans hle'')
      rw [List.map_cons, houts h' s₃ hg (hle''.trans hle) ha, houts' h' s₃ hg hle ha]

end ChunksStep

section Body

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `setup_chunks_step` of `Proof/Tree.lean` with no charge. -/
theorem setup_chunks_abort [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (mode : ReshareMode) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    {α : Type} (js : List (List Job)) (lab k Lk c : ℕ) (Ks : Finset HashOutput) (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (Option (List (List Bit))) × (ℕ × ℕ) → PartyM C E RealSpec α)
    (event : (C.Party → Option α) → Prop) (hnone : ¬ event fun _ => none) (ε : ℝ≥0∞)
    (h : ∀ (outs : List (Option (List (List Bit)))) (Ks' : Finset HashOutput) (s' : HashCache C),
      (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
        outs = js.map fun jobs => some (jobs.map fun job => D prims h' (evalJob circuits parameter seeds job))) →
      Ks'.card ≤ c + (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum →
      CacheOK Ks' (lab + (js.map (batchLabels circuits parameter)).sum) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (outs, (lab + (js.map (batchLabels circuits parameter)).sum, k + js.length))) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => prssSetup i >>= fun prss =>
        (js.mapM (realBatch K circuits mode ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run (lab, k) >>=
          g i) >>=
        honestRounds F reply (fuel + (js.map (batchRounds circuits mode parameter)).sum + 3))).run' s}[event z] ≤ ε := by
  refine setup_step_cacheOK prims F reply _ _ event Ks Lk s hn hs _ fun kT kP s₁ hn₁ hle₁ hs₁ => ?_
  exact chunks_abort prims K circuits mode F reply parameter seeds pairKeys kT kP js lab k Lk c Ks hLk hKs s₁ hn₁ hs₁
    fuel g event hnone ε fun outs Ks' s' houts hKs' hs' hn' hle' => h outs Ks' s' houts hKs' hs' hn' (hle₁.trans hle')

/-- `top_body_bound` of `Proof/Tree.lean` with no charge. -/
theorem top_body_abort [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top .top)
    (hsize : 0 < settings.batchSize) (fuel : ℕ) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize topJobs).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          topRest (E := E) parameter p.1 p.2) >>=
        honestRounds F reply (fuel + ((chunks settings.batchSize topJobs).map
          (batchRounds circuits settings.mode parameter)).sum))).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ 0 := by
  refine chunks_abort prims K circuits settings.mode F reply parameter seeds pairKeys kT kP _ 0 0 0 0 ∅ le_rfl (by simp)
    s hn hs fuel (fun i p => topRest parameter p.1 p.2) _ (by simp) 0 fun outs Ks' s' houts hKs' hs' hn' hle' => ?_
  dsimp only
  obtain ⟨h₀, hg₀, ha₀⟩ : ∃ h₀, Good prims h₀ ∧ Agrees h₀ s' := ⟨hashOf prims s', good_hashOf prims s',
    agrees_hashOf prims hn'⟩
  set W := topJobs.map fun job => D prims h₀ (evalJob circuits parameter seeds job) with hW
  have hfold : outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some W := by
    rw [houts h₀ s' hg₀ le_rfl ha₀]
    have := foldlM_some_append ((chunks settings.batchSize topJobs).map fun js =>
      js.map fun job => D prims h₀ (evalJob circuits parameter seeds job)) []
    simp only [List.map_map, Function.comp_def] at this
    rw [this, List.nil_append, flatten_chunks_map _ hsize]
  simp only [topRest, hfold]
  refine common_step prims F reply fuel _ (FrameR.tweakable _) _ _ s' hn' 0 fun v s'' hv hn'' hle'' _ => ?_
  rw [honestRounds_pure]
  obtain ⟨h₁, hg₁, ha₁⟩ : ∃ h₁, Good prims h₁ ∧ Agrees h₁ s'' := ⟨hashOf prims s'', good_hashOf prims s'',
    agrees_hashOf prims hn''⟩
  have hW₁ : W = topJobs.map fun job => D prims h₁ (evalJob circuits parameter seeds job) := by
    have e₀ := houts h₀ s' hg₀ le_rfl ha₀
    have e₁ := houts h₁ s'' hg₁ hle'' ha₁
    rw [e₀] at e₁
    have := congrArg (fun L => (L.map fun o => o.getD []).flatten) e₁
    simp only [List.map_map, Function.comp_def, Option.getD_some, flatten_chunks_map _ hsize] at this
    exact this
  have ho₁ := ho h₁ s'' hg₁ (hle'.trans hle'') ha₁
  rw [ceremonyAt_top prims circuits parameter seeds h₁ top, ← hW₁, ← hv h₁ s'' hg₁ le_rfl ha₁] at ho₁
  rw [ho₁]
  simp

end Body

section BottomBody

attribute [local irreducible] D

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (circuits : Circuits) (K : Constants C E) (settings : Settings)

/-- `bottom_body_bound` of `Proof/Tree.lean` with no charge. -/
theorem bottom_body_abort [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (b : Fin (2 ^ layerHeight)) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top (.bottom b))
    (hsize : 0 < settings.batchSize) (fuel Y : ℕ)
    (hY : ∀ enc, ((chunks settings.batchSize (signJobs b enc)).map (batchRounds circuits settings.mode parameter)).sum ≤ Y) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize (bottomJobs b)).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          bottomRest parameter top b (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2) >>=
        honestRounds F reply (fuel + Y + 3 + ((chunks settings.batchSize (bottomJobs b)).map
          (batchRounds circuits settings.mode parameter)).sum))).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ 0 := by
  refine chunks_abort prims K circuits settings.mode F reply parameter seeds pairKeys kT kP _ 0 0 0 0 ∅ le_rfl (by simp)
    s hn hs (fuel + Y + 3) (fun i p => bottomRest parameter top b
      (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2)
      _ (by simp) 0 fun outs Ks₁ s₁ houts hKs₁ hs₁ hn₁ hle₁ => ?_
  dsimp only
  let h₁ := hashOf prims s₁
  have hg₁ := good_hashOf prims s₁
  have ha₁ := agrees_hashOf prims hn₁
  set W := (bottomJobs b).map fun job => D prims h₁ (evalJob circuits parameter seeds job) with hW
  have hfold : outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some W := by
    rw [houts h₁ s₁ hg₁ le_rfl ha₁, chunks_outputs _ hsize]
  have hW' : ∀ h s', Good prims h → s₁ ≤ s' → Agrees h s' →
      W = (bottomJobs b).map fun job => D prims h (evalJob circuits parameter seeds job) := by
    intro h s' hg hle ha
    have hf := hfold
    rw [houts h s' hg hle ha, chunks_outputs _ hsize] at hf
    exact (Option.some.inj hf).symm
  simp only [bottomRest, hfold]
  refine common_step prims F reply (fuel + Y + 3) _ (FrameR.tweakable _) _ _ s₁ hn₁ 0
    fun root s₂ hr hn₂ hle₂ hfr₂ => ?_
  refine common_step prims F reply (fuel + Y + 3) _ (FrameR.tweakable _) _ _ s₂ hn₂ 0
    fun base s₃ hb hn₃ hle₃ hfr₃ => ?_
  refine common_step prims F reply (fuel + Y + 3) _ (FrameR.tweakable _) _ _ s₃ hn₃ 0
    fun g s₄ hg hn₄ hle₄ hfr₄ => ?_
  have ho₄ : ∀ h s', Good prims h → s₄ ≤ s' → Agrees h s' →
      o₀ = bottomResult prims circuits parameter seeds h top b W root g := by
    intro h s' hgood hle ha
    rw [ho h s' hgood (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans hle)))) ha]
    exact ceremonyAt_bottom_values prims circuits parameter seeds h top b W root base g
      (hW' h s' hgood (hle₂.trans (hle₃.trans (hle₄.trans hle))) ha)
      (hr h s' hgood (hle₃.trans (hle₄.trans hle)) ha)
      (hb h s' hgood (hle₄.trans hle) ha) (hg h s' hgood hle ha)
  rcases g with _ | ⟨randomness, encoding⟩
  · have ho' := ho₄ (hashOf prims s₄) s₄ (good_hashOf prims s₄) le_rfl (agrees_hashOf prims hn₄)
    simp only [bottomResult, id_bind_eq, id_pure_eq] at ho'
    rw [ho', honestRounds_failure]
    simp
  · have hs₄ := cacheOK_of_frame (cacheOK_of_frame (cacheOK_of_frame hs₁ hfr₂) hfr₃) hfr₄
    have hfuel : fuel + Y + 3 = (fuel + (Y - ((chunks settings.batchSize (signJobs b encoding)).map
        (batchRounds circuits settings.mode parameter)).sum)) +
          ((chunks settings.batchSize (signJobs b encoding)).map (batchRounds circuits settings.mode parameter)).sum + 3 := by
      have := hY encoding; omega
    rw [hfuel]
    simp only [signRun, bind_assoc]
    refine setup_chunks_abort prims K circuits F reply settings.mode parameter seeds pairKeys _
      _ _ _ _ Ks₁ le_rfl hKs₁ s₄ hn₄ hs₄ _ (fun _ p => bottomRest2 parameter top b W root randomness p.1)
        _ (by simp) 0 fun vals Ks₅ s₅ hvals hKs₅ hs₅ hn₅ hle₅ => ?_
    dsimp only
    let h₅ := hashOf prims s₅
    set V := (signJobs b encoding).map fun job => D prims h₅ (evalJob circuits parameter seeds job) with hV
    have hvfold : vals.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some V := by
      rw [hvals h₅ s₅ (good_hashOf prims s₅) le_rfl (agrees_hashOf prims hn₅), chunks_outputs _ hsize]
    have hV' : ∀ h s', Good prims h → s₅ ≤ s' → Agrees h s' →
        V = (signJobs b encoding).map fun job => D prims h (evalJob circuits parameter seeds job) := by
      intro h s' hg hle ha
      have hf := hvfold
      rw [hvals h s' hg hle ha, chunks_outputs _ hsize] at hf
      exact (Option.some.inj hf).symm
    simp only [bottomRest2, hvfold]
    refine common_step prims F reply _ _ (FrameR.tweakable _) _ _ s₅ hn₅ 0
      fun path s₆ hp hn₆ hle₆ _ => ?_
    refine common_step prims F reply _ _ (FrameR.tweakable _) _ _ s₆ hn₆ 0
      fun topRoot s₇ ht hn₇ hle₇ _ => ?_
    let h₇ := hashOf prims s₇
    have hgood := good_hashOf prims s₇
    have ha := agrees_hashOf prims hn₇
    have ho' := ho₄ h₇ s₇ hgood (hle₅.trans (hle₆.trans hle₇)) ha
    have hpath := hp h₇ s₇ hgood hle₇ ha
    have htop := ht h₇ s₇ hgood le_rfl ha
    have hval := hV' h₇ s₇ hgood (hle₆.trans hle₇) ha
    unfold bottomResult at ho'
    simp only [id_bind_eq, id_pure_eq] at ho'
    rw [evalRun_eq, ← hval] at ho'
    simp only [] at ho'
    erw [← hpath, ← htop] at ho'
    split_ifs with hbad
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hbad)] at ho'
      rw [ho', honestRounds_failure]
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hbad)] at ho'
      rw [ho', honestRounds_pure]
      simp

end BottomBody

section TreeRest

attribute [local irreducible] Finset.univ D

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `treeRest_bound` of `Proof/Tree.lean` with no charge. -/
theorem treeRest_abort [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree)
    (hsize : 0 < settings.batchSize) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => treeRest K circuits settings parameter seeds pairKeys top tree i (prssKeysOf kT kP i)) >>=
        honestRounds F reply (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) + 3))).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ 0 := by
  let M := maxBatch circuits settings (runRounds settings.mode)
  have hround := chunks_rounds_le circuits settings parameter
  cases tree with
  | top =>
    let js := chunks settings.batchSize topJobs
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    have hx : X ≤ ceremonyBatches settings * M :=
      (hround 0 (fun _ => digit 0) js (fun jobs hj => Or.inl hj)).trans
        (Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings .top))
    have hfuel : ceremonyBatches settings * M + 3 = (ceremonyBatches settings * M + 3 - X) + X := by omega
    change Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize topJobs).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          topRest (E := E) parameter p.1 p.2) >>=
        honestRounds F reply (ceremonyBatches settings * M + 3))).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ _
    rw [hfuel]
    exact top_body_abort prims K circuits settings F reply parameter seeds pairKeys kT kP top o₀ s hn hs ho hsize
      (ceremonyBatches settings * M + 3 - X)
  | bottom b =>
    let js := chunks settings.batchSize (bottomJobs b)
    let B := (chunks settings.batchSize (signJobs b fun _ => digit 0)).length
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    let Y := B * M
    have hX : X ≤ js.length * M := hround b (fun _ => digit 0) js (fun jobs hj => Or.inr (Or.inl hj))
    have hY : ∀ enc, ((chunks settings.batchSize (signJobs b enc)).map
        (batchRounds circuits settings.mode parameter)).sum ≤ Y := by
      intro enc
      have h := hround b enc (chunks settings.batchSize (signJobs b enc)) (fun jobs hj => Or.inr (Or.inr hj))
      rw [length_chunks_signJobs settings b b enc (fun _ => digit 0)] at h
      exact h
    have hXY : X + Y ≤ ceremonyBatches settings * M := by
      calc X + Y ≤ js.length * M + B * M := add_le_add hX le_rfl
        _ = (treeBatches settings (.bottom b)) * M := by change js.length * M + B * M = (js.length + B) * M; ring
        _ ≤ _ := Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings (.bottom b))
    have hfuel : ceremonyBatches settings * M + 3 = (ceremonyBatches settings * M - (X + Y)) + Y + 3 + X := by omega
    change Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize (bottomJobs b)).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          bottomRest parameter top b (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2) >>=
        honestRounds F reply (ceremonyBatches settings * M + 3))).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ _
    rw [hfuel]
    exact bottom_body_abort (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      F reply parameter seeds pairKeys kT kP top b o₀ s hn hs ho hsize (ceremonyBatches settings * M - (X + Y)) Y hY

/-- `realTree_bound` of `Proof/Tree.lean` with no charge. -/
theorem realTree_abort [Nonempty C.Party] (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree)
    (hsize : 0 < settings.batchSize) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (realTree K circuits settings top tree parameter seeds pairKeys)).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ 0 := by
  unfold realTree
  simp only [newTree_eq]
  rw [show setupRounds + ceremonyFuel circuits settings =
    (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) + 3) + 3 by
      unfold ceremonyFuel setupRounds; omega]
  refine setup_step prims noFunctionality (fun l => l.elim) _ _ _ s hn _
    fun kT kP s' hn' hle hfr => ?_
  exact treeRest_abort prims K circuits settings noFunctionality (fun l => l.elim)
    parameter seeds pairKeys kT kP top tree o₀ s' hn' (cacheOK_of_frame hs hfr)
      (fun h s'' hg hle' ha => ho h s'' hg (hle.trans hle') ha) hsize

end TreeRest

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- An honest run of a tree from a cache with no MPC entry and no coin entry gives, with probability
one, the output of the dealer at every operator or no output at every operator. -/
def RealTreeAbortBound (prims : Primitives) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (o₀ : Option TreeOutput) (s : HashCache C),
    NoMpc s → CacheOK ∅ 0 s →
    (∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree) →
    Pr{let z ← (simulateQ (localAnswer prims)
      (realTree K circuits settings top tree parameter seeds pairKeys)).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ 0

omit [Fintype E] [DecidableEq E] in
theorem realTreeAbortOrCorrect_of_bound (prims : Primitives)
    (hbound : RealTreeAbortBound K circuits settings prims) : RealTreeAbortOrCorrect K circuits settings prims := by
  intro hsize top tree parameter seeds pairKeys h hg o ho i
  set a := D prims h ((fun r (_ : C.Party) => r.1) <$> dealerCeremony circuits settings parameter seeds top tree)
  have ha : a ∈ support (simulateQ (fixedLocal prims h) (idealTree circuits settings parameter seeds top tree)) := by
    rw [idealTree, simulateQ_fixedLocal_liftComp]
    simp [a]
  obtain ⟨s₀, hs₀, -, ha₀⟩ := fixedLocal_support_run prims h hg _ ∅ (fun _ _ hq => by cases hq) a ha
  obtain ⟨hn₀, hc₀, o₀, -, ho₀⟩ := idealTree_value prims circuits settings parameter seeds top tree hsize _ hs₀
  obtain ⟨s₁, hs₁, -, -⟩ := fixedLocal_support_run prims h hg _ s₀ ha₀ o ho
  have hzero := hbound hsize top tree parameter seeds pairKeys o₀ s₀ hn₀ hc₀ ho₀
  have hnot : ¬ (o ≠ (fun _ => o₀) ∧ o ≠ fun _ => none) := by
    intro hev
    refine (lt_of_lt_of_le ((OracleComp.prEvent_pos_iff _ _).2 ⟨o, ?_, hev⟩) hzero).false
    rw [StateT.run'_eq, support_map]
    exact ⟨(o, s₁), hs₁, rfl⟩
  have hceq : o₀ = ceremonyAt prims circuits parameter seeds h top tree := ho₀ h s₀ hg le_rfl ha₀
  by_cases e : o = fun _ => none
  · exact Or.inl (congrFun e i)
  · have : o = fun _ => o₀ := by by_contra e'; exact hnot ⟨e', e⟩
    exact Or.inr (by rw [this, hceq])

theorem realTreeAbortBound (prims : Primitives) : RealTreeAbortBound K circuits settings prims := by
  intro hsize top tree parameter seeds pairKeys o₀ s hn hs ho
  let : Nonempty C.Party := ⟨⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩⟩
  exact realTree_abort prims K circuits settings parameter seeds pairKeys top tree o₀ s hn hs ho hsize

/-- In an honest run of a tree with `H` fixed to a good function, each operator ends with no output
or with the output of the ceremony. -/
theorem realTreeAbortOrCorrect (prims : Primitives) : RealTreeAbortOrCorrect K circuits settings prims :=
  realTreeAbortOrCorrect_of_bound K circuits settings prims (realTreeAbortBound K circuits settings prims)

/-- `DkgCompleteness` holds. -/
theorem dkgCompleteness : DkgCompleteness K circuits settings runLimit := fun batch runs prims compute b =>
  dkgCompleteness_of_abortOrCorrect K circuits settings runLimit (realTreeAbortOrCorrect K circuits settings)
    batch runs prims compute b

/-- info: 'ThresholdLeanXmss.Sketch.dkgCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dkgCompleteness

/-- info: 'ThresholdLeanXmss.Sketch.realTreeAbortOrCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realTreeAbortOrCorrect

end Assembly

end ThresholdLeanXmss.Sketch
