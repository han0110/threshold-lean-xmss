import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Phase

/-!
# Lazy sampling for an observer

`SameRun` compares the result and the final cache. The ideal run of a ceremony asks `H` at points
that the real run does not reach, because `F_ceremony` computes every output first. So the two
caches differ, and only an observer that continues the run can compare them (BR93, lazy sampling).

* `ObsEq oa ob` states that each continuation gives the same distribution of its result after `oa`
  and after `ob`, from each cache with no entry of the fixed part of `Th`.
* `obsEq_drop` removes a computation with no used result.
* `obsEq_hash` replaces a computation of `H` by another one with the same value for each fixed `H`.
  The points that the two computations ask can differ.
* `copy_birthday` is the birthday bound of the copy hashes. It counts only the calls of `H` in the
  copy domain, because only two copies can collide in `OpenRep` (MPClan, App. B).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-! ## The relation -/

section ObsEq

variable {α β : Type}

/-- Two computations are the same for every observer. From each cache with no entry of the fixed part
of `Th`, each continuation gives the same distribution of its result. -/
def ObsEq (oa ob : OracleComp (LocalSpec C) α) : Prop :=
  ∀ s : HashCache C, NoMpc s → ∀ {γ : Type} (k : α → OracleComp (LocalSpec C) γ),
    (simulateQ (localAnswer prims) (oa >>= k)).run' s =ᵈ (simulateQ (localAnswer prims) (ob >>= k)).run' s

variable {prims}

theorem SameRun.obsEq {oa ob : OracleComp (LocalSpec C) α} (h : SameRun prims oa ob) : ObsEq prims oa ob :=
  fun s _ _ k => by
    have := (h.bind fun a => SameRun.refl prims (k a)) s
    simpa only [StateT.run'_eq] using this.map Prod.fst

theorem ObsEq.refl (oa : OracleComp (LocalSpec C) α) : ObsEq prims oa oa := fun _ _ _ _ => .rfl

theorem ObsEq.symm {oa ob : OracleComp (LocalSpec C) α} (h : ObsEq prims oa ob) : ObsEq prims ob oa :=
  fun s hs _ k => (h s hs k).symm

theorem ObsEq.trans {oa ob oc : OracleComp (LocalSpec C) α} (h : ObsEq prims oa ob) (h' : ObsEq prims ob oc) :
    ObsEq prims oa oc := fun s hs _ k => (h s hs k).trans (h' s hs k)

theorem ObsEq.of_eq {oa ob : OracleComp (LocalSpec C) α} (h : oa = ob) : ObsEq prims oa ob := h ▸ ObsEq.refl oa

theorem ObsEq.bind_left {oa ob : OracleComp (LocalSpec C) α} (h : ObsEq prims oa ob)
    (f : α → OracleComp (LocalSpec C) β) : ObsEq prims (oa >>= f) (ob >>= f) := fun s hs _ k => by
  simpa only [bind_assoc] using h s hs fun a => f a >>= k

/-- Continuations that are the same on each possible result of a common prefix. -/
theorem ObsEq.bind_support (oa : OracleComp (LocalSpec C) α) {f g : α → OracleComp (LocalSpec C) β}
    (h : ∀ a ∈ support oa, ObsEq prims (f a) (g a)) : ObsEq prims (oa >>= f) (oa >>= g) := by
  intro s hs γ k
  simp only [bind_assoc, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  have hmem : z.1 ∈ support oa := by
    apply support_simulateQ_run'_subset (localAnswer (C := C) prims) oa s
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  have hn : NoMpc z.2 := (localRun_support oa s z hz).2.1 hs
  have := h z.1 hmem z.2 hn k
  simpa only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] using this

theorem ObsEq.bind_right (oa : OracleComp (LocalSpec C) α) {f g : α → OracleComp (LocalSpec C) β}
    (h : ∀ a, ObsEq prims (f a) (g a)) : ObsEq prims (oa >>= f) (oa >>= g) :=
  ObsEq.bind_support oa fun a _ => h a

/-- Two computations that are the same for every observer accept with the same probability. -/
theorem ObsEq.prob_eq {oa ob : OracleComp (LocalSpec C) Bool} (h : ObsEq prims oa ob) :
    Pr{let b ← (simulateQ (localAnswer prims) oa).run' ∅}[b = true] =
      Pr{let b ← (simulateQ (localAnswer prims) ob).run' ∅}[b = true] := by
  have := h ∅ noMpc_empty (fun b => pure b)
  simp only [bind_pure] at this
  exact this.prEvent_eq _

variable (prims)

/-- A computation with no used result does not change what an observer sees (BR93). -/
theorem obsEq_drop (m : OracleComp (LocalSpec C) β) (oa : OracleComp (LocalSpec C) α) :
    ObsEq prims (m >>= fun _ => oa) oa := by
  intro s _ γ k
  rw [bind_assoc]
  generalize oa >>= k = X
  have h := sameRun_swap prims m X (fun _ c => pure c)
  have h1 := (h s).map Prod.fst
  simp only [bind_pure] at h1
  refine (by simpa only [StateT.run'_eq] using h1 : _ =ᵈ _).trans ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind,
    map_pure]
  rw [map_eq_bind_pure_comp]
  exact EvalDistEq.bind_right ((simulateQ (localAnswer prims) X).run s) fun p =>
    OracleComp.EvalDistEq.bind_const _ _

/-- Two computations of `H` whose continuations are the same on their values for each fixed `H`
(BR93). The points that they ask can differ, because an observer does not see which points the cache
holds. -/
theorem obsEq_hash {β₁ β₂ γ : Type} (u : OracleComp (RoSpec C) β₁) (v : OracleComp (RoSpec C) β₂)
    (K₁ : β₁ → OracleComp (LocalSpec C) γ) (K₂ : β₂ → OracleComp (LocalSpec C) γ)
    (h : ∀ h' : Query C → HashOutput, Good prims h' → ObsEq prims (K₁ (D prims h' u)) (K₂ (D prims h' v))) :
    ObsEq prims (liftComp u (LocalSpec C) >>= K₁) (liftComp v (LocalSpec C) >>= K₂) := by
  have h1 : ObsEq prims (liftComp u (LocalSpec C) >>= K₁)
      (liftComp u (LocalSpec C) >>= fun a => liftComp v (LocalSpec C) >>= fun _ => K₁ a) :=
    ObsEq.bind_right _ fun a => (obsEq_drop prims (liftComp v (LocalSpec C)) (K₁ a)).symm
  have h2 : ObsEq prims (liftComp u (LocalSpec C) >>= fun _ => liftComp v (LocalSpec C) >>= fun b => K₂ b)
      (liftComp v (LocalSpec C) >>= K₂) := obsEq_drop prims _ _
  refine h1.trans (ObsEq.trans ?_ h2)
  intro s hs γ k
  simp only [bind_assoc, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun p hp => ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun q hq => ?_
  obtain ⟨-, hn1, hd1⟩ := localRun_support (prims := prims) _ s p hp
  obtain ⟨hle2, hn2, hd2⟩ := localRun_support (prims := prims) _ p.2 q hq
  have hn := hn2 (hn1 hs)
  have hg := good_hashOf prims q.2
  have ha := agrees_hashOf prims hn
  have e1 := hd1 _ hg (ha.mono hle2)
  have e2 := hd2 _ hg ha
  rw [simulateQ_fixedLocal_liftComp, support_pure, Set.mem_singleton_iff] at e1 e2
  rw [e1, e2]
  have := h _ hg q.2 hn k
  simpa only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] using this

end ObsEq

/-! ## The birthday bound of the copy hashes -/

section CopyBirthday

/-- A call of `H` in the copy domain. -/
def CopyCall : (LocalSpec C).Domain → Prop
  | .inr (.inl (.copy _)) => True
  | _ => False

/-- A copy call is a counted call. -/
theorem counted_of_copyCall (t : (LocalSpec C).Domain) (h : CopyCall t) : Counted t := by
  rcases t with n | q | x
  · exact h
  · cases q <;> first | exact h.elim | trivial
  · exact h.elim

/-- The entries of a cache in the copy domain. -/
private def copyPart (s : HashCache C) : HashCache C := QueryCache.ofFn fun (q : Query C) =>
  match q with
  | .copy a => s (.copy a)
  | _ => none

private theorem copyPart_cacheQuery_copy (s : HashCache C) (a : List Bit) (u : HashOutput) :
    copyPart (s.cacheQuery (.copy a) u) = (copyPart s).cacheQuery (.copy a) u := by
  refine QueryCache.ext fun q => ?_
  by_cases hq : q = .copy a
  · subst hq
    simp [copyPart]
  · rw [QueryCache.cacheQuery_of_ne _ _ hq]
    cases q <;> simp_all [copyPart]

private theorem copyPart_cacheQuery_of_ne (s : HashCache C) (q : Query C) (hq : ∀ a, q ≠ .copy a)
    (u : HashOutput) : copyPart (s.cacheQuery q u) = copyPart s := by
  refine QueryCache.ext fun q' => ?_
  cases q' <;> simp [copyPart, QueryCache.cacheQuery_of_ne _ _ (Ne.symm (hq _))]

private theorem cacheHasCollision_copyPart (s : HashCache C) (h : MainCopyCollision s) :
    CacheHasCollision (copyPart s) :=
  mainCopyCollision_implies_cacheCollision _ h

/-- A lookup out of the copy domain keeps the copy entries. -/
private theorem copy_hash_step_ne {α : Type} (s : HashCache C) (q : Query C) (hq : ∀ a, q ≠ .copy a)
    (f : HashOutput → HashCache C → ProbComp (α × HashCache C)) (ε : ℝ≥0∞)
    (hf : ∀ u s', copyPart s' = copyPart s → Pr{let z ← f u s'}[CacheHasCollision (copyPart z.2)] ≤ ε) :
    Pr{let z ← ((Query C →ₒ HashOutput).randomOracle q).run s >>= fun r => f r.1 r.2}[
      CacheHasCollision (copyPart z.2)] ≤ ε := by
  cases hsq : s q with
  | some u =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hsq, pure_bind]
    exact hf u s rfl
  | none =>
    have heq : ((Query C →ₒ HashOutput).randomOracle q).run s =
        (fun u => (u, s.cacheQuery q u)) <$> ($ᵗ HashOutput) := by
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hsq]
      rfl
    rw [heq, bind_map_left]
    exact prEvent_bind_le_of_forall_le _ _ _ fun u => hf u _ (copyPart_cacheQuery_of_ne s q hq u)

/-- `main_birthday_hash_step` of `Proof/Main.lean` for a lookup in the copy domain and the copy
entries. -/
private theorem copy_hash_step {α : Type} (s : HashCache C) (hs : ¬ CacheHasCollision (copyPart s))
    (k : ℕ) (hb : MainCacheBound (copyPart s) k) (a : List Bit)
    (f : HashOutput → HashCache C → ProbComp (α × HashCache C)) (ε : ℝ≥0∞)
    (hf : ∀ u s', ¬ CacheHasCollision (copyPart s') → MainCacheBound (copyPart s') (k + 1) →
      Pr{let z ← f u s'}[CacheHasCollision (copyPart z.2)] ≤ ε) :
    Pr{let z ← ((Query C →ₒ HashOutput).randomOracle (.copy a)).run s >>= fun r => f r.1 r.2}[
      CacheHasCollision (copyPart z.2)] ≤ (k : ℝ≥0∞) / Fintype.card HashOutput + ε := by
  cases hsq : s (.copy a) with
  | some u =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hsq, pure_bind]
    exact (hf u s hs (mainCacheBound_mono hb (Nat.le_succ k))).trans le_add_self
  | none =>
    have heq : ((Query C →ₒ HashOutput).randomOracle (.copy a)).run s =
        (fun u => (u, s.cacheQuery (.copy a) u)) <$> ($ᵗ HashOutput) := by
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hsq]
      rfl
    rw [heq, bind_map_left]
    refine (prEvent_bind_le_prEvent_add_of_support ($ᵗ HashOutput) (fun u => f u (s.cacheQuery (.copy a) u))
      (fun u => CacheHasCollision (copyPart (s.cacheQuery (.copy a) u))) (fun z => CacheHasCollision (copyPart z.2))
      fun u _ hu => hf u _ hu (by rw [copyPart_cacheQuery_copy]; exact mainCacheBound_insert hb _ u)).trans
      (add_le_add ?_ le_rfl)
    simpa only [copyPart_cacheQuery_copy] using main_cache_fresh_collision_bound _ hs k hb (.copy a)

/-- `main_local_birthday` of `Proof/Main.lean` for the copy entries and the copy calls. -/
private theorem copy_local_birthday {α : Type} (oa : OracleComp (LocalSpec C) α) (n k : ℕ)
    (h : IsQueryBoundP oa CopyCall n) (s : HashCache C) (hs : ¬ CacheHasCollision (copyPart s))
    (hb : MainCacheBound (copyPart s) k) :
    Pr{let z ← (simulateQ (localAnswer prims) oa).run s}[CacheHasCollision (copyPart z.2)] ≤
      ((n * (k + n) : ℕ) : ℝ≥0∞) / Fintype.card HashOutput := by
  induction oa using OracleComp.inductionOn generalizing n k s with
  | pure a => simp [hs]
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases t with t | (q | x)
    · have heq : (localAnswer (C := C) prims (.inl t)).run s =
          (fun u => (u, s)) <$> (OracleComp.lift (OracleSpec.query (spec := unifSpec) t)) := by
        simp [localAnswer, unifFwdImpl]
      change Pr{let z ← (localAnswer prims (.inl t)).run s >>= fun r =>
        (simulateQ (localAnswer prims) (f r.1)).run r.2}[CacheHasCollision (copyPart z.2)] ≤ _
      rw [heq]
      erw [bind_map_left]
      exact prEvent_bind_le_of_forall_le _ _ _ fun u => ih u n k (by simpa [CopyCall] using h.2 u) s hs hb
    · change Pr{let z ← (hashAnswer prims q).run s >>= fun r =>
        (simulateQ (localAnswer prims) (f r.1)).run r.2}[CacheHasCollision (copyPart z.2)] ≤ _
      by_cases hfixed : IsFixed q
      · obtain ⟨input, rfl, hinput⟩ := hfixed
        rw [hashAnswer_of_isFixed prims hinput, StateT.run_pure, pure_bind]
        exact ih _ n k (by simpa [CopyCall] using h.2 (prims.Th input)) s hs hb
      rw [hashAnswer_of_not_isFixed prims hfixed]
      by_cases hcopy : ∃ a, q = .copy a
      · obtain ⟨a, rfl⟩ := hcopy
        have hc : CopyCall (C := C) (.inr (.inl (.copy a))) := trivial
        have hn : 0 < n := h.1.resolve_left (not_not.mpr hc)
        refine (copy_hash_step s hs k hb a _ _ (fun u s' hs' hb' =>
          ih u (n - 1) (k + 1) (by simpa only [hc, ↓reduceIte] using h.2 u) s' hs' hb')).trans ?_
        exact main_birthday_arith n k hn _
      · push Not at hcopy
        have hc : ¬ CopyCall (C := C) (.inr (.inl q)) := by
          cases q <;> simp_all [CopyCall]
        exact copy_hash_step_ne s q hcopy _ _ fun u s' he =>
          ih u n k (by simpa only [hc, ↓reduceIte] using h.2 u) s' (he ▸ hs) (he ▸ hb)
    · change Pr{let z ← (prgAnswer prims x).run s >>= fun r =>
        (simulateQ (localAnswer prims) (f r.1)).run r.2}[CacheHasCollision (copyPart z.2)] ≤ _
      simp only [prgAnswer, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, hashAnswer]
      have hc : ¬ CopyCall (C := C) (.inr (.inr x)) := id
      exact copy_hash_step_ne s (.streamKey x.2.1) (fun _ => by simp)
        (fun u s' => (simulateQ (localAnswer prims) (f (prims.aes.eval (truncateHash u) x.2.2))).run s') _
        fun u s' he => ih _ n k (by simpa only [hc, ↓reduceIte] using h.2 (prims.aes.eval (truncateHash u) x.2.2))
          s' (he ▸ hs) (he ▸ hb)

/-- A computation with at most `n` calls in the copy domain gives two equal copy hashes with
probability at most `n² / 2^256`, from the empty cache. The other calls are free. -/
theorem copy_birthday {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ) (h : IsQueryBoundP oa CopyCall n) :
    (Pr{let z ← (simulateQ (localAnswer prims) oa).run ∅}[MainCopyCollision z.2]).toReal ≤
      ((n ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
  have h0 : ¬ CacheHasCollision (copyPart (∅ : HashCache C)) := by
    rintro ⟨q₁, q₂, u₁, u₂, hne, h₁, h₂, heq⟩
    cases q₁ <;> simp [copyPart] at h₁
  have hb : MainCacheBound (copyPart (∅ : HashCache C)) 0 := ⟨∅, by simp, fun q hq => by cases q <;> simp [copyPart] at hq⟩
  have hh := (prEvent_mono _ _ _ (fun z hz => cacheHasCollision_copyPart z.2 hz)).trans
    (copy_local_birthday prims oa n 0 h ∅ h0 hb)
  have hcard : Fintype.card HashOutput = 2 ^ 256 := Fintype.card_bitVec 256
  simp only [zero_add, ← pow_two, hcard] at hh
  have ht : (((n ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by exact_mod_cast (pow_ne_zero 256 (by decide : (2 : ℕ) ≠ 0)))
  have hr := ENNReal.toReal_mono ht hh
  norm_num at hr ⊢
  exact hr

end CopyBirthday

end ThresholdLeanXmssSecurity
