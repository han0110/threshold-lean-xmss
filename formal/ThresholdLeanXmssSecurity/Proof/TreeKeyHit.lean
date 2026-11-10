import ThresholdLeanXmssSecurity.Proof.TreeKeyStages
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The hits of the stream key

Stage 3 of `TreeKey.lean`, `TreeKeyHitBound`, in two parts. The prefix makes at most `start + 2 step`
counted calls, and the rest of the run makes at most `(ceremonyFuel - 2) step + final`.

1. `TreeKeyBoundaryHitBound` (proved, `treeKeyBoundaryHitBound`). The cache at the boundary holds the
   stream key of a hidden key of a row. Either a hidden canonical input is cached early
   (`prob_earlyCached_le`), or its fresh answer falls in the stream keys of the counted log
   (`prob_setupReveal_hit_le`).
2. `TreeKeyAfterHitBound` (open). The cache at the boundary does not hold it, and the cache at the end
   does. This needs the secrecy of the hidden keys after the boundary.

`treeKeyHitBound_of_stages` sums the two parts.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

open scoped ENNReal

section BoundaryCache

variable {C : Committee} {E : Type}

/-- The logged boundary forgets its log to the boundary. -/
theorem setupEarly_logged_eq (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) :
    (fun r => (r.1, r.2.1.1, r.2.2)) <$> setupEarly D (prssLoggedAdversary A) (prssHashLog start) =
      setupEarly D A start := by
  unfold setupEarly
  simp only [map_bind, map_pure]
  conv_rhs => rw [← prssHashLog_fst start, bind_map_left]
  refine bind_congr fun state => bind_congr fun data => ?_
  rw [← prssEarlyDataRounds_logged D A state data, bind_map_left]

/-- At the logged boundary, a stream key out of the log is not cached. -/
theorem setupEarly_streamKey_fresh (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (r : ((C.Party → Parts C × List HashOutput) × (prssLoggedAdversary A).State ×
      (C.Party → Mail C E) × Option (C.Party → Mail C E)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (setupEarly D (prssLoggedAdversary A) (prssHashLog start))).run ∅)) :
    ∀ k, Query.streamKey k ∉ r.1.2.1.2 → r.2 (.streamKey k) = none := by
  simp only [setupEarly, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨state, hs, data, hd, rounds, hh, rfl⟩ := hr
  intro k hnot
  have hrounds := prssEarlyDataRounds_cache_other prims D A state.1 data.1 data.2 rounds hh
  have hdata := prssInitialData_cache_other prims D (.streamKey k)
    (by intros; simp) state.2 data hd
  have hstart := prssHashLog_cache_other prims start ∅ state hs (.streamKey k)
    (fun hm => hnot (hrounds.1 _ hm))
  exact (hrounds.2 _ hnot).trans (hdata.trans hstart)

/-- A call that can cache `target`. -/
def TargetCall (target : Query C) (t : (LocalSpec C).Domain) : Prop := target ∈ prssCountedHashInputs t

/-- A call of `H` at `target`, or a stream call. -/
def RoTargetCall (target : Query C) : (RoSpec C).Domain → Prop
  | .inl q => q = target
  | .inr _ => True

/-- A computation with no call that can cache `target` keeps its cache entry. -/
theorem cache_target_of_qb0 (prims : Primitives) (target : Query C) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (h : IsQueryBoundP oa (TargetCall target) 0) :
    ∀ (cache : HashCache C) (r : α × HashCache C),
      r ∈ support ((simulateQ (localAnswer prims) oa).run cache) → r.2 target = cache target := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro cache r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl
  | query_bind t k ih =>
    intro cache r hr
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ TargetCall target t := by
      rcases h.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (TargetCall target) 0 := fun u => by
      have := h.2 u
      rwa [if_neg ht] at this
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind,
      Set.mem_iUnion] at hr
    obtain ⟨p, hp, hr⟩ := hr
    exact (ih p.1 (hk p.1) p.2 r hr).trans (prssLocalAnswer_other prims t target ht cache p hp)

theorem qb0_hashQuery_target (target q : Query C) (h : q ≠ target) :
    IsQueryBoundP (hashQuery q) (RoTargetCall target) 0 := by
  unfold hashQuery
  erw [isQueryBoundP_query_iff]
  intro hq
  exact absurd hq h

theorem qb0_liftComp_ro_target (target : Query C) {α : Type} (oa : OracleComp (RoSpec C) α)
    (h : IsQueryBoundP oa (RoTargetCall target) 0) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) (TargetCall target) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ RoTargetCall target t := by
      rcases h.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ?_, fun u => ?_⟩
    · rcases t with q | x
      · simp only [RoTargetCall] at ht
        change target ∉ (if Counted (Sum.inr (Sum.inl q) : (LocalSpec C).Domain) then [q] else [])
        split_ifs <;> simp [Ne.symm ht]
      · exact absurd trivial ht
    · have := h.2 u
      rw [if_neg ht] at this
      simpa only [Nat.zero_sub, ite_self] using ih u this

theorem qb0_deriveKeys_target (k : HashOutput) (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) (RoTargetCall (.streamKey k)) 0 := by
  unfold deriveKeys
  dsimp only
  split_ifs
  all_goals first | refine qb0_bind (qb0_hashQuery_target _ _ (by simp)) fun _ => ?_ | simp only [pure_bind]
  all_goals refine qb0_bind (qb0_mapM _ (fun T => ?_) _) fun _ =>
    qb0_bind (qb0_mapM _ (fun j => ?_) _) fun _ => by simp
  all_goals split_ifs
  all_goals first | exact qb0_hashQuery_target _ _ (by simp) | simp

/-- The reveal round caches no stream key. -/
theorem qb0_prssRevealRows_streamKey (k : HashOutput) (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) :
    IsQueryBoundP (prssRevealRows D active parts committed sent) (TargetCall (.streamKey k)) 0 := by
  unfold prssRevealRows
  refine isQueryBoundP_sequenceFin _ fun i => ?_
  split_ifs
  · simp
  · unfold prssRevealData
    split_ifs
    · simp
    · unfold prssPostRevealData
      refine qb0_bind (qb0_liftComp_ro_target _ _
        (qb0_mapM _ (fun j => qb0_hashQuery_target _ _ (by simp)) _)) fun _ => ?_
      split_ifs
      · exact qb0_bind (qb0_liftComp_ro_target _ _ (qb0_deriveKeys_target _ _ _ _)) fun _ =>
          qb0_bind (qb0_liftComp_ro_target _ _
            (qb0_mapM _ (fun j => qb0_hashQuery_target _ _ (by simp)) _)) fun _ => by simp
      · simp
  · simp

/-- The potential that the answer at `x` falls in `S`. -/
def setHitPotential (x : Query C) (S : Finset HashOutput) (s : HashCache C) : ℝ≥0∞ :=
  match s x with
  | some u => if u ∈ S then 1 else 0
  | none => S.card / 2 ^ 256

theorem setHitPotential_fresh (prims : Primitives) {x : Query C}
    (hx : ∃ ph k v, x = .derive ph k v) (S : Finset HashOutput) (s : HashCache C) :
    ∑' r, Pr[= r | (localAnswer prims (.inr (.inl x))).run s] * setHitPotential x S r.2 ≤
      setHitPotential x S s := by
  obtain ⟨ph, k, v, rfl⟩ := hx
  change ∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle (.derive ph k v)).run s] *
    setHitPotential _ S r.2 ≤ _
  cases hs : s (.derive ph k v) with
  | some u =>
    rw [randomOracle, QueryImpl.withCaching_run_some _ hs]
    simp [setHitPotential, hs]
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ hs, tsum_probOutput_map_mul]
    simp only [setHitPotential, QueryCache.cacheQuery_self, hs, mul_ite, mul_one, mul_zero]
    rw [tsum_eq_sum (s := S) (by intro b hb; simp [hb])]
    simp [uniformSampleImpl, HashOutput, hashOutputBits, div_eq_mul_inv]
    gcongr
    · intro u hu
      simp only [Finset.mem_filter] at hu
      exact hu.1
    · norm_num

theorem setHitPotential_step (prims : Primitives) {x : Query C}
    (hx : ∃ ph k v, x = .derive ph k v) (S : Finset HashOutput) (t : (LocalSpec C).Domain)
    (s : HashCache C) :
    ∑' r, Pr[= r | (localAnswer prims t).run s] * setHitPotential x S r.2 ≤ setHitPotential x S s := by
  by_cases htx : t = .inr (.inl x)
  · subst htx
    exact setHitPotential_fresh prims hx S s
  have hout : x ∉ prssCountedHashInputs t := by
    obtain ⟨ph, k, v, rfl⟩ := hx
    rcases t with n | q | w
    · simp [prssCountedHashInputs]
    · simp only [prssCountedHashInputs]
      split_ifs
      · simp only [List.mem_singleton]
        rintro rfl
        exact htx rfl
      · simp
    · simp [prssCountedHashInputs]
  refine tsum_probOutput_mul_le_of_eq _ _ _ fun r hr => ?_
  unfold setHitPotential
  rw [prssLocalAnswer_other prims t x hout s r hr]

/-- The answer at a fresh derivation input falls in `S` with probability at most `|S| / 2 ^ 256`. -/
theorem prob_setHit_le (prims : Primitives) {β : Type} (oa : OracleComp (LocalSpec C) β)
    {x : Query C} (hx : ∃ ph k v, x = .derive ph k v) (S : Finset HashOutput) (s : HashCache C)
    (hs : s x = none) :
    Pr[fun r => ∃ u, r.2 x = some u ∧ u ∈ S | (simulateQ (localAnswer prims) oa).run s] ≤
      S.card / 2 ^ 256 := by
  have h := probEvent_run_le_potential (localAnswer prims) (fun s' => ∃ u, s' x = some u ∧ u ∈ S)
    (setHitPotential x S) (fun s' hs' => ?_) (setHitPotential_step prims hx S) oa s
  · refine h.trans (le_of_eq ?_)
    simp [setHitPotential, hs]
  · obtain ⟨u, hu, huS⟩ := hs'
    simp [setHitPotential, hu, huS]

/-- Some fresh derivation input of `X` has its answer in `S` with probability at most
`|X| |S| / 2 ^ 256`. -/
theorem prob_setHit_finset_le (prims : Primitives) {β : Type} (oa : OracleComp (LocalSpec C) β)
    (X : Finset (Query C)) (hX : ∀ x ∈ X, ∃ ph k v, x = .derive ph k v) (S : Finset HashOutput)
    (s : HashCache C) (hs : ∀ x ∈ X, s x = none) :
    Pr[fun r => ∃ x ∈ X, ∃ u, r.2 x = some u ∧ u ∈ S | (simulateQ (localAnswer prims) oa).run s] ≤
      (X.card * S.card : ℝ≥0∞) / 2 ^ 256 := by
  refine (probEvent_exists_finset_le_sum _ _ _).trans ?_
  calc _ ≤ ∑ x ∈ X, (S.card : ℝ≥0∞) / 2 ^ 256 :=
        Finset.sum_le_sum fun x hxX => prob_setHit_le prims oa (hX x hxX) S s (hs x hxX)
    _ = _ := by simp [div_eq_mul_inv, mul_assoc]

/-- With no hidden canonical input cached at the boundary, the reveal round ends with the stream key of
a hidden key of a row cached only when the fresh answer at a hidden input falls in the stream keys `S`
of the boundary. -/
theorem prob_setupReveal_hit_le (prims : Primitives) (D : C.Coalition) {σ : Type}
    (t : (C.Party → Parts C × List HashOutput) × σ × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (s : HashCache C) (S : Finset HashOutput) (hS : ∀ k, s (.streamKey k) ≠ none → k ∈ S)
    (hfresh : ¬ EarlyCached D (t, s)) :
    Pr[fun r => KeyHit D (rowsOf r.1.2) r.2 | (simulateQ (localAnswer prims) (setupReveal D t)).run s] ≤
      ((Fintype.card C.Term + Fintype.card C.Pair) * S.card : ℝ≥0∞) / 2 ^ 256 := by
  rcases t with ⟨data, st, sent, _ | sent'⟩
  · refine le_of_eq_of_le (probEvent_eq_zero fun r hr hhit => ?_) zero_le
    simp only [setupReveal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    obtain ⟨n, k, ⟨i, keys, shared, hrow, -⟩, -⟩ := hhit
    simp [rowsOf] at hrow
  · simp only [setupReveal, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    set parts : C.Party → Parts C := fun i => (data i).1
    set active := prssCommitActive D sent
    set X := hiddenInputs D parts
    refine (probEvent_bind_le_of_start _ _ _ (fun r => ∃ x ∈ X, ∃ u, r.2 x = some u ∧ u ∈ S)
      fun r hr b hb hhit => ?_).trans ?_
    · simp only [support_pure, Set.mem_singleton_iff] at hb
      subst hb
      obtain ⟨n, k, hk, hn, hc⟩ := hhit
      obtain ⟨i, -, ha, y, hy, hyk⟩ := rowKey_query prims D active parts _ sent' s r hr n k hk
      obtain ⟨-, hym⟩ := hidden_rowQuery D active parts sent' i ha n hn y hy
      refine ⟨y, hym, k, hyk, hS k ?_⟩
      rw [← cache_target_of_qb0 prims (.streamKey k) _
        (qb0_prssRevealRows_streamKey k D active parts _ sent') s r hr]
      exact hc
    · have hs : ∀ x ∈ X, s x = none := by
        intro x hx
        simp only [X, hiddenInputs, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hx
        by_contra hne
        rcases hx with ⟨T, ⟨-, hT⟩, rfl⟩ | ⟨p, ⟨-, hp⟩, rfl⟩
        · exact hfresh (Or.inl ⟨T, hT, hne⟩)
        · exact hfresh (Or.inr ⟨p, hp, hne⟩)
      refine (prob_setHit_finset_le prims _ X (hiddenInputs_derive D parts) S s hs).trans ?_
      gcongr
      exact_mod_cast hiddenInputs_card D parts

/-- The log of the logged boundary has at most `start + 2 step` entries. -/
theorem setupEarly_log_length (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (r : ((C.Party → Parts C × List HashOutput) × (prssLoggedAdversary A).State ×
      (C.Party → Mail C E) × Option (C.Party → Mail C E)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (setupEarly D (prssLoggedAdversary A) (prssHashLog start))).run ∅)) :
    r.1.2.1.2.length ≤ initial + 2 * step := by
  have hr' : r.1 ∈ support (setupEarly D (prssLoggedAdversary A) (prssHashLog start)) := by
    refine support_simulateQ_run'_subset (localAnswer prims) _ (∅ : HashCache C) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  simp only [setupEarly, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr'
  obtain ⟨state, hs, data, -, rounds, hh, he⟩ := hr'
  rw [he]
  have hs' := prssHashLog_length start initial hstart state hs
  have hb := prssEarlyDataRounds_log_length D A step hstep state data rounds hh
  dsimp only
  omega

/-- The stream keys of a log. -/
def logStreamKeys (log : List (Query C)) : Finset HashOutput :=
  (log.filterMap fun q => match q with
    | .streamKey k => some k
    | _ => none).toFinset

theorem logStreamKeys_card (log : List (Query C)) : (logStreamKeys log).card ≤ log.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem mem_logStreamKeys {log : List (Query C)} {k : HashOutput} (h : Query.streamKey k ∈ log) :
    k ∈ logStreamKeys log := by
  simp only [logStreamKeys, List.mem_toFinset, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

end BoundaryCache

section HitStages

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Part 1, the boundary hit. The cache at the boundary holds the stream key of a hidden key of a row
with probability at most `2 (start + 2 step) m / 2 ^ 256`. -/
def TreeKeyBoundaryHitBound : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (start step : ℕ), IsQueryBoundP (A.start (corruptInputs D x) z) Counted start →
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) →
    Pr[fun r => KeyHit D (rowsOf r.1.2) r.2 | worldRun prims (setupPrefix D A x z)] ≤
      ((2 * (start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Part 1. The prequery term of `prob_earlyCached_le` and the fresh answers at the hidden inputs that
fall in the at most `start + 2 step` stream keys of the log. -/
theorem treeKeyBoundaryHitBound : TreeKeyBoundaryHitBound (C := C) (E := E) prims := by
  intro D A x z start step hstart hstep
  rw [worldRun_setupPrefix, ← setupEarly_logged_eq D A, bind_map_left, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_add _ _ _ (EarlyCached D)
    (((Fintype.card C.Term + Fintype.card C.Pair) * (start + 2 * step) : ℕ) / 2 ^ 256)
    fun a ha hb => ?_).trans ?_
  · have hS : ∀ k, a.2 (.streamKey k) ≠ none → k ∈ logStreamKeys a.1.2.1.2 := by
      intro k hk
      by_contra hm
      exact hk (setupEarly_streamKey_fresh prims D A _ a ha k fun h => hm (mem_logStreamKeys h))
    refine (prob_setupReveal_hit_le prims D (a.1.1, a.1.2.1.1, a.1.2.2) a.2 _ hS hb).trans ?_
    have hl := (logStreamKeys_card a.1.2.1.2).trans (setupEarly_log_length prims D A _ start step hstart hstep a ha)
    gcongr
    push_cast
    gcongr
    exact_mod_cast hl
  · have hu := congrArg (fun oa => (simulateQ (localAnswer prims) oa).run (∅ : HashCache C))
      (setupEarly_logged_eq D A (A.start (corruptInputs D x) z))
    simp only [simulateQ_map, StateT.run_map] at hu
    have he : Pr[EarlyCached D | (simulateQ (localAnswer prims)
        (setupEarly D (prssLoggedAdversary A) (prssHashLog (A.start (corruptInputs D x) z)))).run ∅] =
        Pr[EarlyCached D | (simulateQ (localAnswer prims) (setupEarly D A (A.start (corruptInputs D x) z))).run ∅] := by
      rw [← hu, probEvent_map]
      rfl
    rw [he]
    refine (add_le_add (prob_earlyCached_le prims D A _ start step (start + 2 * step) hstart hstep le_rfl)
      le_rfl).trans ?_
    rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ?_ _
    have hT := card_term C
    have hP := card_pair_le C
    have hn : (start + 2 * step) * (C.n.choose (C.t - 1) + C.n.choose 2) +
        (Fintype.card C.Term + Fintype.card C.Pair) * (start + 2 * step) ≤
        2 * (start + 2 * step) * prssKeyCount C := by
      have hm : Fintype.card C.Term + Fintype.card C.Pair ≤ prssKeyCount C := by
        unfold prssKeyCount termCount; omega
      have hm' : C.n.choose (C.t - 1) + C.n.choose 2 = prssKeyCount C := rfl
      rw [hm']
      nlinarith [Nat.mul_le_mul_left (start + 2 * step) hm]
    exact_mod_cast hn

/-- Part 2, the hit after the boundary. With the keys apart and no boundary hit, the cache ends with
the stream key of a hidden key of a row with probability at most
`((start + (3 (ceremonyFuel - 2) + 2) step + 3 final) m + 4 m ^ 2) / 2 ^ 256`. The prefix calls stay
in the bound, because a prefix call can query a hidden canonical input. -/
def TreeKeyAfterHitBound : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (start step final : ℕ), DealtInputs D x →
    (∀ x z, IsQueryBoundP (A.start x z) Counted start) →
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) →
    (∀ r, IsQueryBoundP (Z r) Counted final) →
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧
        KeyHit D (rowsOf y.1.1.2) y.2.2.hash |
      boundaryRun prims K circuits settings top tree D A x z Z] ≤
      (((start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) * prssKeyCount C +
        4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

omit [Fintype E] [DecidableEq E] in
/-- `TreeKeyHitBound` from its two parts. -/
theorem treeKeyHitBound_of_stages (hBoundary : TreeKeyBoundaryHitBound (C := C) (E := E) prims)
    (hAfter : TreeKeyAfterHitBound prims K circuits settings) :
    TreeKeyHitBound prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq
  obtain ⟨start, step, final, hle, hstart, hround, -, hfinal⟩ := hq
  have hfuel : 2 ≤ ceremonyFuel circuits settings := by unfold ceremonyFuel setupRounds; omega
  generalize hP : boundaryRun prims K circuits settings top tree D A x z Z = P
  have h1 : Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P] ≤
      Pr[fun y => KeyHit D (rowsOf y.1.1.2) y.1.2 | P] +
        Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧
          KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P] :=
    le_trans (probEvent_mono fun y _ hy => by
      by_cases h : KeyHit D (rowsOf y.1.1.2) y.1.2
      · exact Or.inl h
      · exact Or.inr ⟨hy.1, h, hy.2⟩) (probEvent_or_le _ _ _)
  have h2 : Pr[fun y => KeyHit D (rowsOf y.1.1.2) y.1.2 | P] ≤
      Pr[fun r => KeyHit D (rowsOf r.1.2) r.2 | worldRun prims (setupPrefix D A x z)] := by
    rw [← hP]
    exact probEvent_pair_fst_le _ _
      (fun r : (A.State × Option (RevealRows C)) × HashCache C => KeyHit D (rowsOf r.1.2) r.2)
  have hB := hBoundary D A x z start step (hstart _ _) hround
  have hA := hAfter hb top tree D A x z Z start step final hx hstart hround hfinal
  rw [hP] at hA
  have hsum : ((2 * (start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      (((start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) * prssKeyCount C +
        4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((3 * q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hF : (ceremonyFuel circuits settings - 2) * step + 2 * step =
        ceremonyFuel circuits settings * step := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hfuel]
    have hn : 2 * (start + 2 * step) * prssKeyCount C +
        ((start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) * prssKeyCount C +
          4 * prssKeyCount C ^ 2) ≤ 3 * q * prssKeyCount C + 4 * prssKeyCount C ^ 2 := by
      have hq2 : 2 * (start + 2 * step) + (start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step +
          3 * final) ≤ 3 * q := by
        have h3 : (3 * (ceremonyFuel circuits settings - 2) + 2) * step =
            3 * ((ceremonyFuel circuits settings - 2) * step) + 2 * step := by ring
        omega
      nlinarith [Nat.mul_le_mul_right (prssKeyCount C) hq2]
    rw [← ENNReal.add_div, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (by exact_mod_cast hn) _
  have hE := (h1.trans (add_le_add h2 hA)).trans ((add_le_add hB le_rfl).trans hsum)
  have hr := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)) hE
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
  exact hr

omit [Fintype E] [DecidableEq E] in
/-- Stage 3, with part 1 proved and part 2 open. -/
theorem treeKeyHitBound (hAfter : TreeKeyAfterHitBound prims K circuits settings) :
    TreeKeyHitBound prims K circuits settings :=
  treeKeyHitBound_of_stages prims K circuits settings (treeKeyBoundaryHitBound prims) hAfter

/-- `TreeSecurityStatement` from the simulation hop and part 2 of the hits. -/
theorem treeSecurityOfSimOnly (hAfter : TreeKeyAfterHitBound prims K circuits settings)
    (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurityOfSimFull prims K circuits settings (treeKeyHitBound prims K circuits settings hAfter) hSim

end HitStages

/-- info: 'ThresholdLeanXmssSecurity.treeKeyBoundaryHitBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeKeyBoundaryHitBound

/-- info: 'ThresholdLeanXmssSecurity.treeKeyHitBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeKeyHitBound

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityOfSimOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityOfSimOnly

end ThresholdLeanXmssSecurity
