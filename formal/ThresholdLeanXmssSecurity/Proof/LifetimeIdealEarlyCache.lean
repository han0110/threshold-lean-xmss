import ThresholdLeanXmssSecurity.Proof.LifetimeIdealOverlapFinal
import ThresholdLeanXmssSecurity.Proof.LifetimeIdealOverlap
import XmssSecurity.Proof.QueryBoundSupport

/-!
# The derivation cache before the selected run

The all-answer lifetime budget bounds the hash cache of every supported prefix of the
four-copy left world. The selected run samples fresh PRSS parts after this prefix, and its
initial commitment queries do not change any derivation entry.

The cache counts use `splitRegion_step_bound`; the sampling estimates use the existing
PRSS coordinate splitting and single-coordinate guessing bounds.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache

open LifetimePrfTransportProof LifetimeIdealOverlap LifetimeIdealOverlapFinal
open LifetimeIdealKeyLink (advQ emulQ freeQ targetQ)

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee}

theorem splitRegion_true (cache : HashCache C) :
    splitRegionCache (fun _ => True) cache = cache := by
  funext q
  simp [splitRegionCache]

theorem regionCounted_le_local (t : (LocalSpec C).Domain) :
    SplitRegionCounted (fun _ => True) t → LocalCounted t := by
  rcases t with u | q | x <;> simp [SplitRegionCounted, splitLocalHashInput,
    LocalCounted, LifetimeCounted]

/-- A local query adds at most its actual all-party charge to the hash cache. -/
theorem local_cache_bound (prims : Primitives) (t : (LocalSpec C).Domain)
    (cache : HashCache C) (k : ℕ) (hk : SplitCacheBound cache k)
    (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) :
    SplitCacheBound r.2 (k + if LocalCounted t then 1 else 0) := by
  have hb := splitRegion_step_bound prims (fun _ => True) t cache k
    (by simpa only [splitRegion_true] using hk) r hr
  rw [splitRegion_true] at hb
  apply hb.mono
  by_cases ht : SplitRegionCounted (fun _ => True) t
  · simp [ht, regionCounted_le_local t ht]
  · simp only [if_neg ht]
    omega

theorem onCache_bound (prims : Primitives) (t : (LocalSpec C).Domain)
    (s : IdealState C) (k : ℕ) (hk : SplitCacheBound s.1 k)
    (r : (LocalSpec C).Range t × IdealState C)
    (hr : r ∈ support ((onCache (localAnswer prims t)).run s)) :
    SplitCacheBound r.2.1 (k + if LocalCounted t then 1 else 0) := by
  simp only [onCache, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact local_cache_bound prims t s.1 k hk u hu

/-- A private stream table does not affect the counted hash-cache bound. -/
theorem withHidden_bound (prims : Primitives) (D : C.Coalition)
    (hidden : PrgInput C → StateT (IdealState C) ProbComp Bit)
    (frame : ∀ x s, ∀ r ∈ support ((hidden x).run s), r.2.1 = s.1)
    (t : (LocalSpec C).Domain) (s : IdealState C) (k : ℕ) (hk : SplitCacheBound s.1 k)
    (r : (LocalSpec C).Range t × IdealState C)
    (hr : r ∈ support ((withHidden prims D hidden t).run s)) :
    SplitCacheBound r.2.1 (k + if LocalCounted t then 1 else 0) := by
  rcases t with u | q | x
  · exact onCache_bound prims _ s k hk r hr
  · exact onCache_bound prims _ s k hk r hr
  · change r ∈ support ((if Hidden D x.1 then hidden x else
      onCache (localAnswer prims (.inr (.inr x)))).run s) at hr
    split_ifs at hr with hx
    · rw [frame x s r hr]
      exact hk.mono (Nat.le_add_right _ _)
    · exact onCache_bound prims _ s k hk r hr

/-- Each of the actual four-copy handlers increases the hash-cache bound by at
most the charge of the source query. -/
theorem leftImpl_bound (prims : Primitives) (D : C.Coalition)
    (t : (Spec4 C).Domain) (s : IdealState C) (k : ℕ) (hk : SplitCacheBound s.1 k)
    (r : (Spec4 C).Range t × IdealState C)
    (hr : r ∈ support ((leftImpl prims D t).run s)) :
    SplitCacheBound r.2.1 (k + if Counted4 t then 1 else 0) := by
  rcases t with ((t | t) | t) | t
  · exact onCache_bound prims t s k hk r hr
  · exact withHidden_bound prims D _ (fun x s r hr => firstTable_cache _ s r hr) t s k hk r hr
  · exact withHidden_bound prims D _ (fun x s r hr => flagged_cache _ s
      (secondTable_cache _ s) r hr) t s k hk r hr
  · exact withHidden_bound prims D _ (fun x s r hr => secondTable_cache _ s r hr) t s k hk r hr

/-- A supported prefix has a cache bounded by the calls it consumed and leaves
the rest of its original all-answer budget to the actual continuation. -/
theorem prefix_cache_budget (prims : Primitives) (D : C.Coalition) {α β : Type}
    (p : OracleComp (Spec4 C) α) (f : α → OracleComp (Spec4 C) β) :
    ∀ Q, IsQueryBoundP (p >>= f) Counted4 Q →
    ∀ (s : IdealState C) k, SplitCacheBound s.1 k →
    ∀ r ∈ support ((simulateQ (leftImpl prims D) p).run s),
      ∃ m, m ≤ Q ∧ SplitCacheBound r.2.1 (k + m) ∧
        IsQueryBoundP (f r.1) Counted4 (Q - m) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    intro Q h s k hk r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    simp only [pure_bind] at h
    exact ⟨0, Nat.zero_le _, by simpa using hk, by simpa using h⟩
  | query_bind t next ih =>
    intro Q h s k hk r hr
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    change r ∈ support ((leftImpl prims D t >>= fun u =>
      simulateQ (leftImpl prims D) (next u)).run s) at hr
    rw [StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    have hs := leftImpl_bound prims D t s k hk u hu
    obtain ⟨m, hm, cache, tail⟩ := ih u.1 _ (h.2 u.1) u.2 _ hs r hr
    by_cases ht : Counted4 t
    · have pos : 0 < Q := h.1.resolve_left (fun hn => hn ht)
      simp only [if_pos ht] at hm cache tail
      refine ⟨1 + m, by omega, ?_, ?_⟩
      · simpa only [Nat.add_assoc] using cache
      · exact tail.mono (by omega)
    · simp only [if_neg ht, Nat.add_zero] at hm cache tail
      exact ⟨m, hm, cache, tail⟩

/-- A fixed query guesses the selected run's fresh derivation input with
probability at most one over the size of a PRSS contribution. -/
theorem prob_hiddenInput_eq_le (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (q : Query C) :
    Pr[fun parts => LifetimeIdealKeyLink.hiddenInput parts name = q | prssSampleParts D] ≤
      1 / 2 ^ 256 := by
  cases name with
  | parameter => exact hidden.elim
  | term T =>
    obtain ⟨i, hi⟩ := prss_exists_holder T
    have honest : i ∉ D.1 := fun hd => hidden ⟨i, hd, hi⟩
    let pick := prssDerivePick (C := C) ((C.parties.filter (· ∈ C.holders T)).idxOf i)
    have sub : ∀ parts, LifetimeIdealKeyLink.hiddenInput parts (.term T) = q →
        (parts i).term T = pick q := by
      intro parts he
      exact (prssTermInput_pick parts T i hi).symm.trans (congrArg pick he)
    refine (probEvent_mono (fun parts _ he => sub parts he)).trans ?_
    apply prob_prssSampleParts_split D i honest
    intro xs
    simp only [Function.update_self]
    exact prob_sampleParts_term_eq_le T (fun _ => pick q) (fun _ _ => rfl)
  | pair pair =>
    have honest : pair.1.1 ∉ D.1 := hidden.1
    have sub : ∀ parts, LifetimeIdealKeyLink.hiddenInput parts (.pair pair) = q →
        (parts pair.1.1).pair pair.1.2 = prssDerivePick 0 q := by
      intro parts he
      exact (prssPairInput_pick parts pair).symm.trans (congrArg (prssDerivePick 0) he)
    refine (probEvent_mono (fun parts _ he => sub parts he)).trans ?_
    apply prob_prssSampleParts_split D pair.1.1 honest
    intro xs
    simp only [Function.update_self]
    exact prob_sampleParts_pair_eq_le pair.1.2 (fun _ => prssDerivePick 0 q) (fun _ _ => rfl)

/-- A cache with at most `k` entries contains a newly sampled hidden input with
probability at most `k / 2^256`. The cache is fixed before sampling the parts. -/
theorem prob_hiddenInput_cached_le (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (cache : HashCache C) (k : ℕ) (bound : SplitCacheBound cache k) :
    Pr[fun parts => (cache (LifetimeIdealKeyLink.hiddenInput parts name)).isSome |
      prssSampleParts D] ≤ (k : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨S, card, covers⟩ := bound
  have sub : ∀ parts, (cache (LifetimeIdealKeyLink.hiddenInput parts name)).isSome →
      ∃ q ∈ S, LifetimeIdealKeyLink.hiddenInput parts name = q := by
    intro parts hp
    refine ⟨_, covers _ ?_, rfl⟩
    exact Option.isSome_iff_ne_none.mp hp
  refine (probEvent_mono (fun parts _ hp => sub parts hp)).trans
    ((probEvent_exists_finset_le_sum _ _ _).trans ?_)
  calc
    _ ≤ ∑ q ∈ S, (1 : ℝ≥0∞) / 2 ^ 256 :=
      Finset.sum_le_sum fun q _ => prob_hiddenInput_eq_le D name hidden q
    _ = (S.card : ℝ≥0∞) / 2 ^ 256 := by simp [nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast card) _

/-- A copy making no stream calls has exactly the local-cache law. -/
theorem copy_local_eq (prims : Primitives) (D : C.Coalition)
    (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)))
    (hemb : emb = advQ ∨ emb = emulQ ∨ emb = freeQ ∨ emb = targetQ) {α : Type}
    (p : OracleComp (LocalSpec C) α) (hp : IsQueryBoundP p LocalStream 0)
    (s : IdealState C) :
    (simulateQ (leftImpl prims D) (simulateQ emb p)).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (simulateQ (localAnswer prims) p).run s.1 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ LocalStream t := hp.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [LifetimeIdealKeyLink.leftImpl_local prims D t ht emb hemb]
    simp only [onCache, StateT.run_mk, bind_map_left, map_bind]
    refine bind_congr fun r => ?_
    exact ih r.1 (by simpa [ht] using hp.2 r.1) (r.2, s.2)

/-- Initial commitments preserve derivation entries, so a fresh hidden input
hits the preceding cache with probability at most its size over `2^256`. -/
theorem initialData_cached_le (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (hidden : Hidden D name) (s : IdealState C) (k : ℕ)
    (bound : SplitCacheBound s.1 k) :
    Pr[fun r => (r.2.1 (LifetimeIdealKeyLink.hiddenInput (fun i => (r.1 i).1) name)).isSome |
      (simulateQ (leftImpl prims D) (targetCopy4 (prssInitialData D))).run s] ≤
        (k : ℝ≥0∞) / 2 ^ 256 := by
  rw [show targetCopy4 (prssInitialData D) = simulateQ targetQ (prssInitialData D) from rfl,
    copy_local_eq prims D targetQ (Or.inr (Or.inr (Or.inr rfl))) _
      (qb0_prssInitialData D), probEvent_map]
  have frame : ∀ r ∈ support ((simulateQ (localAnswer prims) (prssInitialData D)).run s.1),
      r.2 (LifetimeIdealKeyLink.hiddenInput (fun i => (r.1 i).1) name) =
        s.1 (LifetimeIdealKeyLink.hiddenInput (fun i => (r.1 i).1) name) := by
    intro r hr
    apply prssInitialData_cache_other prims D _ _ s.1 r hr
    intro i j values
    obtain ⟨ph, kn, vs, he⟩ := hiddenInput_derive (fun i => (r.1 i).1) name
    rw [he]
    simp
  calc
    _ = Pr[fun r => (s.1 (LifetimeIdealKeyLink.hiddenInput (fun i => (r.1 i).1) name)).isSome |
        (simulateQ (localAnswer prims) (prssInitialData D)).run s.1] :=
      probEvent_congr' (fun r hr => by dsimp; rw [frame r hr]) rfl
    _ = Pr[fun parts => (s.1 (LifetimeIdealKeyLink.hiddenInput parts name)).isSome |
        prssSampleParts D] := by
      have he := probEvent_congr'
        (p := fun parts => (s.1 (LifetimeIdealKeyLink.hiddenInput parts name)).isSome)
        (fun _ _ => Iff.rfl) (evalDist_prssInitialData_parts prims D s.1)
      simpa only [probEvent_map, Function.comp_def] using he
    _ ≤ _ := prob_hiddenInput_cached_le D name hidden s.1 k bound

/-- Passing a counted prefix transfers its consumed budget into the cache
bound and leaves the remaining budget to the continuation. -/
theorem cacheRisk_bind (prims : Primitives) (D : C.Coalition) {α β : Type}
    (p : OracleComp (Spec4 C) α) (f : α → OracleComp (Spec4 C) β)
    (event : β × IdealState C → Prop)
    (tail : ∀ a (s : IdealState C) k Q, SplitCacheBound s.1 k →
      IsQueryBoundP (f a) Counted4 Q →
      Pr[event | (simulateQ (leftImpl prims D) (f a)).run s] ≤
        ((k + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    ∀ (s : IdealState C) k Q, SplitCacheBound s.1 k →
      IsQueryBoundP (p >>= f) Counted4 Q →
      Pr[event | (simulateQ (leftImpl prims D) (p >>= f)).run s] ≤
        ((k + Q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  intro s k Q hk hQ
  rw [simulateQ_bind, StateT.run_bind]
  refine probEvent_bind_le_of_forall_le fun r hr => ?_
  obtain ⟨m, hm, cache, budget⟩ := prefix_cache_budget prims D p f Q hQ s k hk r hr
  have h := tail r.1 r.2 (k + m) (Q - m) cache budget
  simpa only [show k + m + (Q - m) = k + Q by omega] using h

section Setup

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The exact setup cut satisfies the early-cache bound from every bounded
starting cache and every all-answer budget. -/
theorem setupCut_bound (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (attempts : ℕ) (D : C.Coalition) (n : ℕ)
    (A : LifetimeAdversary C E) (name : KeyName C) (hidden : Hidden D name) :
    ∀ (s : IdealState C) k Q, SplitCacheBound s.1 k →
      IsQueryBoundP (setupCut K circuits settings attempts D n A) Counted4 Q →
      Pr[RunEarlyCached name | (simulateQ (leftImpl prims D)
        (setupCut K circuits settings attempts D n A)).run s] ≤
          ((k + Q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold setupCut
  apply cacheRisk_bind prims D
  intro state
  apply cacheRisk_bind prims D
  rintro ⟨state', outputs⟩ s k Q cache budget
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => simp [RunEarlyCached]
  | some h =>
    simp only [hh] at budget ⊢
    split_ifs at budget ⊢ with hall
    · revert s k Q cache budget
      apply cacheRisk_bind prims D
      rintro ⟨pause, st⟩ s k Q cache budget
      cases pause with
      | done result => simp [LifetimeRunBoundary.Pause.atStart, RunEarlyCached]
      | wait query next =>
        cases query <;> simp only [LifetimeRunBoundary.Pause.atStart] at budget ⊢
        all_goals try { simp [RunEarlyCached]; done }
        split_ifs at budget ⊢ with admitted
        · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, probEvent_map]
          have he := initialData_cached_le prims D name hidden s k cache
          exact (le_of_eq_of_le (by
            apply probEvent_congr' _ rfl
            intro r _
            simp [RunEarlyCached]) he).trans
            (ENNReal.div_le_div_right (by exact_mod_cast (Nat.le_add_right k Q)) _)
        · simp [RunEarlyCached]
    · simp [RunEarlyCached]

variable (K : Constants C E) (settings : Settings) (attempts : ℕ) (D : C.Coalition)
variable (A : LifetimeAdversary C E) (aes : Aes)
variable (circuitsOf : (HashInput → HashOutput) → Circuits)

/-- The early-cache estimate for the original lifetime budget. -/
theorem runEarlyCachedBound (Q : ℕ) :
    RunEarlyCachedBound K settings attempts D A aes circuitsOf Q := by
  intro hQ _ n values name
  have budget := program4Budget K settings attempts D A circuitsOf Q hQ n values
  rw [program4_cut] at budget
  have cutBudget := OracleComp.IsQueryBoundP.of_bind_left budget
  have empty : SplitCacheBound (idealStart (C := C)).1 0 := by
    refine ⟨∅, by simp, ?_⟩
    simp [idealStart]
  simpa only [Nat.zero_add] using setupCut_bound ⟨thOf values, aes⟩ K
    (circuitsOf (thOf values)) settings attempts D n A name.1 name.2 idealStart 0 Q empty cutBudget

/-- The original ideal-world key-overlap estimate, assembled from the early
cache and fresh-answer estimates at the same run boundary. -/
theorem hiddenKeyOverlapBound (Q : ℕ) :
    LifetimeIdealBad.HiddenKeyOverlapBound K settings attempts D A aes circuitsOf Q :=
  hiddenKeyOverlapBound_of_early K settings attempts D A aes circuitsOf Q
    (runEarlyCachedBound K settings attempts D A aes circuitsOf Q)

/-- The original ideal bad-event allowance follows with no additional term. -/
theorem idealBadBound (Q : ℕ) :
    IdealBadBound K settings attempts aes circuitsOf D A Q :=
  LifetimeIdealBad.idealBadBound_of_hiddenKeyOverlap K settings attempts D A aes circuitsOf Q
    (hiddenKeyOverlapBound K settings attempts D A aes circuitsOf Q)

end Setup

end ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.leftImpl_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.leftImpl_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.prefix_cache_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.prefix_cache_budget

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.prob_hiddenInput_cached_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.prob_hiddenInput_cached_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.copy_local_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.copy_local_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.initialData_cached_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.initialData_cached_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.setupCut_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.setupCut_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.runEarlyCachedBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.runEarlyCachedBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.hiddenKeyOverlapBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.hiddenKeyOverlapBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.idealBadBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeIdealEarlyCache.idealBadBound
