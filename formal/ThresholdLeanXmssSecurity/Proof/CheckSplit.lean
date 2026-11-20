import ThresholdLeanXmssSecurity.Proof.CheckFinish
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# The split case of the check

Equal salted digests of different histories give a collision of the hash cache
(`splitHistories_cacheCollision`). Equal recorded histories determine the values that a corrupt
filler supplied, so the honest views agree. `SplitCacheBound` and `splitHash_insert_birthday` give
the adaptive birthday bound of the history and digest cache, and `splitRegion_random_bind` counts the
hash calls of a split region. `splitRisk_nonneg` states that the error term `splitRisk` is not
negative.
-/

noncomputable section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset
open scoped ENNReal

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra Bit E] [SampleableType E]

/-- Equal salted digests of different histories imply a cache collision, even with different salts. -/
lemma splitHistories_cacheCollision (cache : HashCache C)
    (a b s t : List Bit) (ha hb d : HashOutput) (hab : a ≠ b)
    (hha : cache (.history a) = some ha) (hhb : cache (.history b) = some hb)
    (hda : cache (.digest s ha) = some d) (hdb : cache (.digest t hb) = some d) :
    CacheHasCollision cache := by
  by_cases hh : ha = hb
  · exact ⟨.history a, .history b, ha, hb, by simpa using hab, hha, hhb, heq_of_eq hh⟩
  · exact ⟨.digest s ha, .digest t hb, d, d,
      fun he => hh (Query.digest.inj he).2, hda, hdb, HEq.rfl⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- Equal recorded prefixes determine all values that a corrupt filler supplied. -/
lemma split_filledValues_of_history (K : Constants C E) (D : C.Coalition) (T : C.Term)
    (a b : List (Tuple C)) (hc : a.map (·.count) = b.map (·.count))
    (hm : a.map (·.mode) = b.map (·.mode))
    (hh : (a.flatMap fun τ => ((List.range τ.count).filter fun g =>
        (filler K τ.mode T g).isSome).map (τ.z T)) =
      (b.flatMap fun τ => ((List.range τ.count).filter fun g =>
        (filler K τ.mode T g).isSome).map (τ.z T))) :
    a.map (fun τ => vector τ.count fun g =>
      if ∃ j ∈ D.1, filler K τ.mode T g = some j then τ.z T g else 0) =
    b.map (fun τ => vector τ.count fun g =>
      if ∃ j ∈ D.1, filler K τ.mode T g = some j then τ.z T g else 0) := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => simp at hc
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hc hm
      simp only [List.flatMap_cons] at hh
      have hl : (((List.range a.count).filter fun g => (filler K a.mode T g).isSome).map (a.z T)).length =
          (((List.range b.count).filter fun g => (filler K b.mode T g).isSome).map (b.z T)).length := by
        simp only [List.length_map, hc.1, hm.1]
      obtain ⟨hhead, htail⟩ := List.append_inj hh hl
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih bs hc.2 hm.2 htail⟩
      rw [hc.1]
      unfold vector
      apply List.map_congr_left
      intro g hg
      rw [hm.1]
      by_cases hf : ∃ j ∈ D.1, filler K b.mode T g = some j
      · simp only [if_pos hf]
        rw [hc.1, hm.1] at hhead
        apply List.map_inj_left.mp hhead g
        obtain ⟨j, _, hj⟩ := hf
        simp only [List.mem_filter, hj, Option.isSome_some, and_true]
        exact hg
      · simp only [if_neg hf]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma split_filledHistory_consistent (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (T : C.Term) (hh : ConsistentAt D (fun i T => filledHistory K i (x i) T) T) :
    ConsistentAt D (fun i T => (x i).map fun τ =>
      (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) T := by
  apply hx.2.2 T
  intro i hiT j hjT hi hj
  apply split_filledValues_of_history K D T (x i) (x j)
    ((hx.1 i hi).trans (hx.1 j hj).symm) (hx.2.1 i j hi hj)
  simpa only [filledHistory, if_pos hiT, if_pos hjT] using hh i hiT j hjT hi hj

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma split_agree_of_vectors (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (hv : ∀ T, ConsistentAt D (fun i T => (x i).map fun τ =>
      (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) T) :
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) := by
  intro k hk T i hiT j hjT hi hj g hg
  have hk' : k < counts.length := by simpa only [firstInput_length K hx] using hk
  have hi' : k < (x i).length := by
    rw [← List.length_map (f := (·.count)), hx.1 i hi]
    exact hk'
  have hj' : k < (x j).length := by
    rw [← List.length_map (f := (·.count)), hx.1 j hj]
    exact hk'
  have hci : ((x i)[k]).count = counts.getD k 0 := by
    have h := tupleInputs_count_at K hx i hi k
    simpa only [List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some,
      ← List.getD_eq_getElem?_getD] using congrArg (fun o => o.getD 0) h
  have hcj : ((x j)[k]).count = counts.getD k 0 := by
    have h := tupleInputs_count_at K hx j hj k
    simpa only [List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some,
      ← List.getD_eq_getElem?_getD] using congrArg (fun o => o.getD 0) h
  have hg' : g < counts.getD k 0 := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some, tupleAt_count K hx] using hg
  have he := congrArg (fun l => l[k]?) (hv T i hiT j hjT hi hj)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
    Option.map_some, Option.some.injEq] at he
  have hgi : g < ((x i)[k]).count := by rw [hci]; exact hg'
  have he' : ((x i)[k].x T g, (x i)[k].y T g, (x i)[k].z T g) =
      ((x j)[k].x T g, (x j)[k].y T g, (x j)[k].z T g) :=
    Prod.ext (vector_point (congrArg Prod.fst he) hgi)
    (Prod.ext (vector_point (congrArg (fun p => p.2.1) he) hgi)
      (vector_point (congrArg (fun p => p.2.2) he) hgi))
  simpa only [if_neg hi, if_neg hj, Option.bind_some, List.getElem?_eq_getElem hi',
    List.getElem?_eq_getElem hj', Option.map_some, Option.some.injEq] using he'

omit [SampleableType E] in
/-- Split copies already give unequal recorded histories on a known term. -/
lemma splitInit_histories_ne (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (hsplit : ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    ∃ T, KnownTo D.1 T ∧ ∃ i j, i ∉ D.1 ∧ j ∉ D.1 ∧
      i ∈ C.holders T ∧ j ∈ C.holders T ∧
      filledHistory K i (x i) T ≠ filledHistory K j (x j) T := by
  by_contra h
  push Not at h
  apply hsplit
  apply split_agree_of_vectors K counts D x hx
  intro T
  by_cases hT : KnownTo D.1 T
  · apply split_filledHistory_consistent K counts D x hx T
    intro i hiT j hjT hi hj
    exact h T hT i j hi hj hiT hjT
  · exact tupleInputs_unknown_vectors K hx T hT

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma splitInit_history_length (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (T : C.Term) (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    (filledHistory K i (x i) T).length = (filledHistory K j (x j) T).length := by
  have hp := map_pair_eq (x i) (x j) (·.count) (·.mode)
    ((hx.1 i hi).trans (hx.1 j hj).symm) (hx.2.1 i j hi hj)
  have he := congrArg (fun l : List (ℕ × ReshareMode) =>
    (l.map fun p => ((List.range p.1).filter fun g => (filler K p.2 T g).isSome).length).sum) hp
  simpa only [filledHistory, if_pos hiT, if_pos hjT, List.length_flatMap,
    List.length_map, List.map_map, Function.comp_def] using he

/-- A split prefix cannot be repaired by choosing separate suffixes at the two holders. -/
lemma split_history_append_ne {α : Type} {a b : List α}
    (hlen : a.length = b.length) (hne : a ≠ b) (c d : List α) : a ++ c ≠ b ++ d := by
  exact fun h => hne (List.append_inj_left h hlen)

/-- Two honest holders of a known term have distinct histories of equal length. -/
def SplitHistories (D : C.Coalition) (h : C.Party → C.Term → List Bit) : Prop :=
  ∃ T, KnownTo D.1 T ∧ ∃ i j, i ∉ D.1 ∧ j ∉ D.1 ∧ i ∈ C.holders T ∧ j ∈ C.holders T ∧
    (h i T).length = (h j T).length ∧ h i T ≠ h j T

omit [SampleableType E] in
lemma splitInit_histories (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (hsplit : ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    SplitHistories D (fun i => filledHistory K i (x i)) := by
  obtain ⟨T, hT, i, j, hi, hj, hiT, hjT, hne⟩ := splitInit_histories_ne K counts D x hx hsplit
  exact ⟨T, hT, i, j, hi, hj, hiT, hjT,
    splitInit_history_length K counts D x hx T i j hi hj hiT hjT, hne⟩

def SplitCacheBound (cache : HashCache C) (k : ℕ) : Prop :=
  ∃ S : Finset (Query C), S.card ≤ k ∧ ∀ q, cache q ≠ none → q ∈ S

lemma SplitCacheBound.insert {cache : HashCache C} {k : ℕ}
    (h : SplitCacheBound cache k) (q : Query C) (u : HashOutput) :
    SplitCacheBound (cache.cacheQuery q u) (k + 1) := by
  obtain ⟨S, hs, hc⟩ := h
  refine ⟨Insert.insert q S, (Finset.card_insert_le q S).trans (by omega), ?_⟩
  intro t ht
  by_cases he : t = q
  · exact he ▸ Finset.mem_insert_self _ _
  · rw [QueryCache.cacheQuery_of_ne cache u he] at ht
    exact Finset.mem_insert_of_mem (hc t ht)

lemma splitHash_insert_collision (cache : HashCache C) (q : Query C) (u : HashOutput)
    (hno : ¬ CacheHasCollision cache) (hbad : CacheHasCollision (cache.cacheQuery q u)) :
    ∃ t, cache t = some u := by
  obtain ⟨a, b, v, w, hab, ha, hb, hvw⟩ := hbad
  have hvw' : v = w := eq_of_heq hvw
  subst w
  by_cases haq : a = q
  · subst a
    have hbq : b ≠ q := Ne.symm hab
    simp only [QueryCache.cacheQuery_self, Option.some.injEq] at ha
    rw [QueryCache.cacheQuery_of_ne cache u hbq] at hb
    exact ⟨b, by simpa only [← ha] using hb⟩
  · rw [QueryCache.cacheQuery_of_ne cache u haq] at ha
    by_cases hbq : b = q
    · subst b
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hb
      exact ⟨a, by simpa only [← hb] using ha⟩
    · rw [QueryCache.cacheQuery_of_ne cache u hbq] at hb
      exact False.elim (hno ⟨a, b, v, v, hab, ha, hb, HEq.rfl⟩)

lemma splitHash_insert_birthday (cache : HashCache C) (q : Query C) (k : ℕ)
    (hno : ¬ CacheHasCollision cache) (hk : SplitCacheBound cache k) :
    Pr{let u ← $ᵗ HashOutput}[CacheHasCollision (cache.cacheQuery q u)] ≤
      (k : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨S, hs, hc⟩ := hk
  let V := S.image (fun t => (cache t).getD 0)
  have hcard : Fintype.card HashOutput = 2 ^ 256 := by
    unfold HashOutput
    exact Fintype.card_bitVec 256
  calc
    _ ≤ Pr{let u : HashOutput ← $ᵗ HashOutput}[u ∈ V] := by
      apply prEvent_mono_of_support
      intro u _ hu
      obtain ⟨t, ht⟩ := splitHash_insert_collision cache q u hno hu
      exact Finset.mem_image.mpr ⟨t, hc t (by rw [ht]; exact Option.some_ne_none u),
        by simp only [ht, Option.getD_some]⟩
    _ ≤ (V.card : ℝ≥0∞) / Fintype.card HashOutput :=
      probEvent_uniform_injective_mem id Function.injective_id V
    _ ≤ (k : ℝ≥0∞) / 2 ^ 256 := by
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      gcongr
      exact_mod_cast (Finset.card_image_le.trans hs)

lemma SplitCacheBound.mono {cache : HashCache C} {k l : ℕ}
    (h : SplitCacheBound cache k) (hkl : k ≤ l) : SplitCacheBound cache l := by
  obtain ⟨S, hs, hc⟩ := h
  exact ⟨S, hs.trans hkl, hc⟩

/-- Keep only the oracle domain whose output collisions are being charged. -/
def splitRegionCache (P : Query C → Prop) (cache : HashCache C) : HashCache C :=
  QueryCache.ofFn fun q => if P q then cache q else none

lemma splitRegionCache_insert (P : Query C → Prop) (cache : HashCache C)
    (q : Query C) (u : HashOutput) (hq : P q) :
    splitRegionCache P (cache.cacheQuery q u) = (splitRegionCache P cache).cacheQuery q u := by
  refine QueryCache.ext fun t => ?_
  by_cases ht : t = q
  · subst t
    simp [splitRegionCache, hq]
  · simp only [splitRegionCache, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ ht]

lemma splitRegionCache_insert_irrelevant (P : Query C → Prop) (cache : HashCache C)
    (q : Query C) (u : HashOutput) (hq : ¬ P q) :
    splitRegionCache P (cache.cacheQuery q u) = splitRegionCache P cache := by
  refine QueryCache.ext fun t => ?_
  by_cases ht : t = q
  · subst t
    simp [splitRegionCache, hq]
  · simp only [splitRegionCache, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ ht]

def splitLocalHashInput : (LocalSpec C).Domain → Option (Query C)
  | .inl _ => none
  | .inr (.inl q) => if IsFixed q then none else some q
  | .inr (.inr x) => some (.streamKey x.2.1)

def SplitRegionCounted (P : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q, splitLocalHashInput t = some q ∧ P q

lemma splitLocalHashInput_none (prims : Primitives) (t : (LocalSpec C).Domain)
    (h : splitLocalHashInput t = none) : ∃ p, localAnswer prims t = StateT.lift p := by
  rcases t with n | q | x
  · exact ⟨_, rfl⟩
  · simp only [splitLocalHashInput, ite_eq_left_iff, reduceCtorEq, imp_false, not_not] at h
    obtain ⟨input, rfl, hi⟩ := h
    refine ⟨pure (prims.Th input), ?_⟩
    change hashAnswer prims (.hash input) = _
    rw [hashAnswer_of_isFixed prims hi]
    rfl
  · simp [splitLocalHashInput] at h

lemma splitLocalHashInput_some (prims : Primitives) (t : (LocalSpec C).Domain)
    (q : Query C) (h : splitLocalHashInput t = some q) :
    ∃ f : HashOutput → (LocalSpec C).Range t,
      localAnswer prims t = f <$> (Query C →ₒ HashOutput).randomOracle q := by
  rcases t with n | r | x
  · simp [splitLocalHashInput] at h
  · by_cases hr : IsFixed r
    · simp [splitLocalHashInput, hr] at h
    · simp only [splitLocalHashInput, if_neg hr, Option.some.injEq] at h
      subst q
      refine ⟨id, ?_⟩
      change hashAnswer prims r = _
      rw [hashAnswer_of_not_isFixed prims hr]
      exact (id_map _).symm
  · simp only [splitLocalHashInput, Option.some.injEq] at h
    subst q
    refine ⟨fun d => prims.aes.eval (truncateHash d) x.2.2, ?_⟩
    change prgAnswer prims x = _
    simp only [prgAnswer, hashAnswer, map_eq_bind_pure_comp]
    rfl

lemma splitRegion_random_bind {α : Type} (P : Query C → Prop) (q : Query C)
    (f : HashOutput → StateT (HashCache C) ProbComp α) (cache : HashCache C) (k : ℕ)
    (hno : ¬ CacheHasCollision (splitRegionCache P cache))
    (hk : SplitCacheBound (splitRegionCache P cache) k) (ε : ℝ≥0∞)
    (hf : ∀ u s, ¬ CacheHasCollision (splitRegionCache P s) →
      SplitCacheBound (splitRegionCache P s) (k + if P q then 1 else 0) →
      Pr{let z ← (f u).run s}[CacheHasCollision (splitRegionCache P z.2)] ≤ ε) :
    Pr{let z ←
      (((Query C →ₒ HashOutput).randomOracle q) >>= f).run cache}[CacheHasCollision (splitRegionCache P z.2)] ≤
      (if P q then (k : ℝ≥0∞) / 2 ^ 256 else 0) + ε := by
  rw [StateT.run_bind]
  cases he : cache q with
  | some u =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ he, pure_bind]
    exact (hf u cache hno (hk.mono (Nat.le_add_right _ _))).trans le_add_self
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ he, bind_map_left]
    by_cases hq : P q
    · simp only [if_pos hq] at hf ⊢
      have h := (prEvent_bind_le_prEvent_add_of_support ($ᵗ HashOutput)
        (fun u => (f u).run (cache.cacheQuery q u))
        (fun u => CacheHasCollision (splitRegionCache P (cache.cacheQuery q u)))
        (fun z => CacheHasCollision (splitRegionCache P z.2))
        (by
          intro u _ hu
          apply hf u _ hu
          rw [splitRegionCache_insert P cache q u hq]
          exact hk.insert q u)).trans
        (add_le_add (by simpa only [splitRegionCache_insert P cache q _ hq]
            using splitHash_insert_birthday (splitRegionCache P cache) q k hno hk) le_rfl)
      simpa only [uniformSampleImpl] using h
    · simp only [if_neg hq, Nat.add_zero] at hf ⊢
      rw [zero_add]
      apply prEvent_bind_le_of_forall_le_of_support
      intro u _
      apply hf u _
      · simpa only [splitRegionCache_insert_irrelevant P cache q u hq] using hno
      · simpa only [splitRegionCache_insert_irrelevant P cache q u hq] using hk

lemma splitRegionCounted_counted (P : Query C → Prop) (t : (LocalSpec C).Domain)
    (h : SplitRegionCounted P t) : Counted t := by
  obtain ⟨q, hq, _⟩ := h
  rcases t with n | r | x
  · simp [splitLocalHashInput] at hq
  · cases r <;> simp_all [splitLocalHashInput, Counted, IsFixed]
  · trivial

lemma counted_splitRegionBound (P : Query C → Prop) {α : Type}
    {oa : OracleComp (LocalSpec C) α} {n : ℕ} (h : IsQueryBoundP oa Counted n) :
    IsQueryBoundP oa (SplitRegionCounted P) n :=
  IsQueryBoundP.of_imp (splitRegionCounted_counted P) h

def SplitHashDomain : Query C → Prop
  | .history _ => True
  | .digest _ _ => True
  | _ => False

lemma splitRisk_nonneg (k n : ℕ) : 0 ≤ splitRisk k n := by
  unfold splitRisk
  have : (k : ℝ) ≤ ((k + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right k n
  apply div_nonneg _ (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

end ThresholdLeanXmssSecurity

end

/-- info: 'ThresholdLeanXmssSecurity.splitHash_insert_birthday' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.splitHash_insert_birthday
