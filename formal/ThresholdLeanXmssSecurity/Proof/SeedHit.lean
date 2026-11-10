import ThresholdLeanXmssSecurity.Proof.SigningCore

/-!
# The cost of a call on a hidden key

`SeedHitBound` of `Proof/SigningCore.lean` (`seedHitBound`), step 1 of the signing plan of
`formal/PROOF.md`, with the slots and the resampling of one key of `Proof/Tprf.lean`.

* Two equal keys cost `(C(n, t - 1) choose 2 + C(n, 2) choose 2) / 2^256` (`probEvent_keyCollision`).
  The dealer makes the `C(n, t - 1)` calls of its first PRF value before the forger runs
  (`dealer_count`), and these calls pay for the collisions (`seedHit_arith`).
* For distinct keys, the world runs on split caches (`runSigningWorld_eq_split`). The honest
  computations read the keys only through their slots (`split_tsigOracles`, `split_referenceTree`),
  so the run with another value of a hidden key is the same until a call hits it or a corruption
  reveals it (`fusedImpl_upd_eq`).
* So the first hits of a key, summed over all its values, cost at most the rest of the budget of the
  calls (`sum_ff_le`), and each key costs `(q - C(n, t - 1)) / 2^256` (`keyHitBound`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.constructorNameAsVariable false

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SeedHitProof

variable {C : Committee} (prims : Primitives)

/-! ## The arithmetic -/

theorem pair_le_term (C : Committee) : C.n.choose 2 ≤ C.n.choose (C.t - 1) := by
  have h : C.n / 2 = C.t - 1 := by
    have := C.one_le_t
    unfold Committee.n
    omega
  rw [← h]
  exact Nat.choose_le_middle 2 C.n

theorem seedHit_arith (C : Committee) (q : ℕ) (hq : C.n.choose (C.t - 1) ≤ q) :
    ((C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2) +
        (C.n.choose (C.t - 1) + C.n.choose 2) * (q - C.n.choose (C.t - 1)) ≤
      (C.n.choose (C.t - 1) + C.n ^ 2) * q := by
  set T := C.n.choose (C.t - 1)
  set P := C.n.choose 2
  have hPT : P ≤ T := pair_le_term C
  have hP : P ≤ C.n ^ 2 := choose_two_le_sq _
  have hT2 : 2 * T.choose 2 ≤ T ^ 2 := two_mul_choose_two_le T
  have hP2 : 2 * P.choose 2 ≤ P ^ 2 := two_mul_choose_two_le P
  obtain ⟨r, rfl⟩ : ∃ r, q = T + r := ⟨q - T, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hPP : P * P ≤ T * P := Nat.mul_le_mul_right P hPT
  have hPq : P * (T + r) ≤ C.n ^ 2 * (T + r) := Nat.mul_le_mul_right _ hP
  nlinarith

/-! ## The two stages -/

/-- The dealer makes the `C(n, t - 1)` calls of its first PRF value before the forger runs. -/
def DealerBudget (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q →
    Pr[fun z => z.2.1.2 = true | flaggedRun prims A] ≠ 0 → C.n.choose (C.t - 1) ≤ q

/-- For distinct keys, each key is hit by at most `q - C(n, t - 1)` calls over all its values. -/
def DistinctFlagBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q →
    Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true | flaggedRun prims A] ≤
      ((Fintype.card (KeySlot C) * (q - C.n.choose (C.t - 1)) : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem probEvent_flaggedRun_keys (A : TsigAdversary C) (P : Keys3 C → Prop) :
    Pr[fun z => P z.1 | flaggedRun prims A] = Pr[P | keyGen3 (C := C)] := by
  classical
  unfold flaggedRun
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun x => ?_
  rw [probEvent_map]
  by_cases hx : P x
  · simp [Function.comp_def, hx]
  · simp [Function.comp_def, hx]

theorem seedHitBound_of_stages (hD : DealerBudget prims C) (hF : DistinctFlagBound prims C) :
    SeedHitBound prims C := by
  intro A q hq
  rcases eq_or_ne (Pr[fun z => z.2.1.2 = true | flaggedRun prims A]) 0 with h0 | h0
  · rw [h0]; unfold seedHitError; simp only [ENNReal.toReal_zero]; positivity
  have hTq := hD A q hq h0
  have hsplit : Pr[fun z => z.2.1.2 = true | flaggedRun prims A] ≤
      Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3] +
        Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true | flaggedRun prims A] := by
    rw [← probEvent_flaggedRun_keys prims A (fun x => KeyCollision x.2.1 x.2.2)]
    refine le_trans (probEvent_mono fun z _ h => ?_) (probEvent_or_le _ _ _)
    by_cases hc : KeyCollision z.1.2.1 z.1.2.2
    · exact Or.inl hc
    · exact Or.inr ⟨hc, h⟩
  have hcoll : Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3] ≤
      (((C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [ENNReal.div_eq_inv_mul, mul_comm]
    exact probEvent_keyCollision
  have hcard : Fintype.card (KeySlot C) = C.n.choose (C.t - 1) + C.n.choose 2 := by
    rw [Fintype.card_sum, card_term, card_pair]
  have htot : Pr[fun z => z.2.1.2 = true | flaggedRun prims A] ≤
      (((C.n.choose (C.t - 1) + C.n ^ 2) * q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    refine hsplit.trans ((add_le_add hcoll (hF A q hq)).trans ?_)
    rw [← ENNReal.add_div, ← Nat.cast_add, hcard]
    gcongr
    exact_mod_cast seedHit_arith C q hTq
  exact toReal_le_div htot

/-! ## The signing world with the count in the state -/

/-- The oracles of `signingWorld` without the count. -/
def signImpl : QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp) :=
  signingLocalAnswer (C := C) prims + programAnswer (C := C) + signingLocalAnswer (C := C) prims

/-- The cost of a query in `signingWorld`. -/
def signCost : (WorldSpec C).Domain → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inr (.inl _) => 0
  | _ => 1

theorem signingWorld_eq : signingWorld (C := C) prims = (signImpl prims).withAddCost signCost := by
  funext t
  rcases t with ((n | u) | x) | (n | u) <;> rfl

/-- An implementation with the count of `signCost` in its state. -/
def withCount {σ : Type} (I : QueryImpl (WorldSpec C) (StateT σ ProbComp)) :
    QueryImpl (WorldSpec C) (StateT (σ × ℕ) ProbComp) := fun t =>
  StateT.mk fun p => (fun z => (z.1, (z.2, p.2 + signCost t))) <$> (I t).run p.1

theorem withCount_run {α : Type} (oa : OracleComp (WorldSpec C) α) (c : HashCache C) (n : ℕ) :
    (simulateQ (withCount (signImpl prims)) oa).run (c, n) =
      (fun z => (z.1.1, (z.2, n + Multiplicative.toAdd z.1.2))) <$>
        (simulateQ (signingWorld prims) oa).run.run c := by
  induction oa using OracleComp.inductionOn generalizing c n with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, WriterT.run_bind, signingWorld_eq, QueryImpl.withAddCost_apply, withCount,
      StateT.run_mk, bind_map_left, map_bind, ih, AddWriterT.run_addTell, liftM, WriterT.run_monadLift,
      StateT.run_map, pure_bind, Functor.map_map]
    refine bind_congr fun a => ?_
    simp only [mul_one, toAdd_mul, toAdd_ofAdd, add_assoc]

/-! ## The world on split caches -/

section Routed

variable (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)

open Classical in
/-- The local oracles of the signing world with the slots in their own cache. -/
def routedLocal : QueryImpl (LocalSpec C) (StateT (HashCache C × SlotCache C) ProbComp)
  | .inr (.inl u) => if h : ∃ s, slotInput seeds pairKeys s = u then onTable (slotOracle h.choose)
      else onCache ((Query C →ₒ HashOutput).randomOracle u)
  | t => onCache (signingLocalAnswer prims t)

open Classical in
/-- The cache of `H` from the cache off the slots and the cache of the slots. -/
def mergeCache (p : HashCache C × SlotCache C) : HashCache C := fun u =>
  if h : ∃ s, slotInput seeds pairKeys s = u then p.2 h.choose else p.1 u

theorem mergeCache_splitCache (g : HashCache C) : mergeCache seeds pairKeys (splitCache seeds pairKeys g) = g := by
  funext u
  unfold mergeCache
  split_ifs with h
  · show g (slotInput seeds pairKeys h.choose) = g u
    rw [h.choose_spec]
  · simp only [splitCache, if_neg h]

/-- Programming on the merged cache. The game never programs. -/
def routedProgram : QueryImpl (ProgramSpec C) (StateT (HashCache C × SlotCache C) ProbComp) := fun x =>
  StateT.mk fun p => Prod.map id (splitCache seeds pairKeys) <$> (programAnswer x).run (mergeCache seeds pairKeys p)

/-- The oracles of the signing world on split caches. -/
def routedImpl : QueryImpl (WorldSpec C) (StateT (HashCache C × SlotCache C) ProbComp) :=
  routedLocal prims seeds pairKeys + routedProgram seeds pairKeys + routedLocal prims seeds pairKeys

theorem stateMap_ro_of_not_slot {u : Query C} (hu : ∀ s, slotInput seeds pairKeys s ≠ u) :
    StateMap (splitCache seeds pairKeys) ((Query C →ₒ HashOutput).randomOracle u)
      (onCache ((Query C →ₒ HashOutput).randomOracle u)) := by
  intro g
  rw [show splitCache seeds pairKeys g = ((splitCache seeds pairKeys g).1, (splitCache seeds pairKeys g).2) from rfl,
    onCache_run]
  have hc := splitCache_fst_of_not_slot seeds pairKeys hu g
  cases hg : g u with
  | some v =>
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hg,
      QueryImpl.withCaching_run_some _ (hc.trans hg), map_pure, Prod.map_apply, id, Prod.mk.eta]
  | none =>
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hg,
      QueryImpl.withCaching_run_none _ (hc.trans hg), Functor.map_map, Prod.map_apply, id,
      splitCache_cacheQuery_of_not_slot seeds pairKeys hu]

theorem stateMap_routedLocal (hinj : Function.Injective (slotInput seeds pairKeys)) (t : (LocalSpec C).Domain) :
    StateMap (splitCache seeds pairKeys) (signingLocalAnswer prims t) (routedLocal prims seeds pairKeys t) := by
  rcases t with n | u | x
  · exact stateMap_routedAnswer prims seeds pairKeys hinj (.inl n)
  · by_cases h : ∃ s, slotInput seeds pairKeys s = u
    · obtain ⟨s₀, rfl⟩ := h
      have hc : (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀).choose = s₀ :=
        hinj (Exists.choose_spec (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀))
      have e : routedLocal prims seeds pairKeys (.inr (.inl (slotInput seeds pairKeys s₀))) =
          onTable (slotOracle s₀) := by
        simp only [routedLocal, dif_pos (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀), hc]
        rfl
      rw [e]
      have h2 := stateMap_hash_slot prims seeds pairKeys hinj s₀
      rwa [hashAnswer_eq_randomOracle prims fun input h => absurd h (slotInput_ne_hash seeds pairKeys s₀ input)] at h2
    · have e : routedLocal prims seeds pairKeys (.inr (.inl u)) =
          onCache ((Query C →ₒ HashOutput).randomOracle u) := by
        simp only [routedLocal, dif_neg h]
        rfl
      rw [e]
      exact stateMap_ro_of_not_slot seeds pairKeys fun s hs => h ⟨s, hs⟩
  · exact stateMap_routedAnswer prims seeds pairKeys hinj (.inr (.inr x))

theorem stateMap_routedImpl (hinj : Function.Injective (slotInput seeds pairKeys)) (t : (WorldSpec C).Domain) :
    StateMap (splitCache seeds pairKeys) (signImpl prims t) (routedImpl prims seeds pairKeys t) := by
  rcases t with (t | x) | t
  · exact stateMap_routedLocal prims seeds pairKeys hinj t
  · intro g
    change (Prod.map id (splitCache seeds pairKeys) <$> (programAnswer x).run
      (mergeCache seeds pairKeys (splitCache seeds pairKeys g))) = _
    rw [mergeCache_splitCache]
    rfl
  · exact stateMap_routedLocal prims seeds pairKeys hinj t

theorem stateMap_withCount {σ₁ σ₂ : Type} (φ : σ₁ → σ₂) (I₁ : QueryImpl (WorldSpec C) (StateT σ₁ ProbComp))
    (I₂ : QueryImpl (WorldSpec C) (StateT σ₂ ProbComp)) (h : ∀ t, StateMap φ (I₁ t) (I₂ t)) (t : (WorldSpec C).Domain) :
    StateMap (Prod.map φ id) (withCount I₁ t) (withCount I₂ t) := by
  rintro ⟨s, n⟩
  simp only [withCount, StateT.run_mk, Prod.map_fst, Prod.map_snd, id, h t s, Functor.map_map]
  rfl

/-- The world on split caches with its count. -/
abbrev splitWorld : QueryImpl (WorldSpec C) (StateT ((HashCache C × SlotCache C) × ℕ) ProbComp) :=
  withCount (routedImpl prims seeds pairKeys)

theorem runSigningWorld_eq_split (hinj : Function.Injective (slotInput seeds pairKeys)) {α : Type}
    (oa : OracleComp (WorldSpec C) α) :
    runSigningWorld prims oa =
      (fun z => (z.1, z.2.2)) <$> (simulateQ (splitWorld prims seeds pairKeys) oa).run ((∅, ∅), 0) := by
  have h := StateMap.simulateQ (stateMap_withCount _ _ _ (stateMap_routedImpl prims seeds pairKeys hinj)) oa
    ((∅ : HashCache C), 0)
  simp only [Prod.map, id, splitCache_empty] at h
  rw [h, withCount_run, runSigningWorld, StateT.run'_eq]
  simp only [Functor.map_map, zero_add]
  rfl

end Routed

/-! ## The keys of the first hit -/

/-- The oracles of `flaggedOracles` that also record the keys that the first flagged call hits. -/
def ffOracles (x : Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT ((TsigState C × Bool) × Finset (KeySlot C)) (OracleComp (WorldSpec C)))
  | .inl t => StateT.mk fun p => (fun a => (a, ((p.1.1, p.1.2 || hiddenHit x p.1.1.corrupt t),
      if p.1.2 then p.2 else p.2 ∪ firedBy x.2.1 x.2.2 p.1.1.corrupt (.inl t)))) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))
  | .inr q => StateT.mk fun p => (fun z => (z.1, ((z.2, p.1.2), p.2))) <$>
      (tsigOracles (fun oa => honestLift oa) dealt q).run p.1.1

theorem ffOracles_forget (x : Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TsigState C × Bool) (F : Finset (KeySlot C)) :
    (fun z => (z.1, z.2.1)) <$> (ffOracles x dealt t).run (s, F) = (flaggedOracles x dealt t).run s := by
  rcases t with t | q
  · simp [ffOracles, flaggedOracles, Functor.map_map]
  · simp [ffOracles, flaggedOracles, Functor.map_map]

/-- `flaggedAfter` with the keys of the first hit. -/
def ffAfter (A : TsigAdversary C) (x : Keys3 C) : OracleComp (WorldSpec C) ((Bool × Bool) × Finset (KeySlot C)) := do
  let value := fun p => liftFree (prfValue x.2.1 p)
  let some (.top top) ← referenceTree (fun oa => liftFree (tweakable oa)) value x.1 emptyTop .top
    | pure ((false, false), ∅)
  let dealt := dealtWith (fun oa => liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
  let r ← (simulateQ (ffOracles x dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run
    ((tsigInit, false), ∅)
  (fun w => ((w.1, r.2.1.2), r.2.2)) <$> tsigFinish dealt (r.1, r.2.1.1)

theorem ffAfter_forget (A : TsigAdversary C) (x : Keys3 C) :
    Prod.fst <$> ffAfter A x = flaggedAfter A x := by
  unfold ffAfter flaggedAfter
  rw [map_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp
  · simp only [map_bind, Functor.map_map]
    rw [← simulateQ_run_forget _ _ (ffOracles_forget x _) _ _ ∅, bind_map_left]
  · simp

/-- An invariant of each step holds after a simulation. -/
theorem support_simulateQ_inv {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ α : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (h : ∀ t s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2) (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    ∀ z ∈ support ((simulateQ impl oa).run s), Inv z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    exact ih w.1 w.2 (h t s hs w hw) z hz

theorem hiddenHit_fired (x : Keys3 C) (D : Finset C.Party) (t : (LocalSpec C).Domain)
    (h : hiddenHit x D t = true) : (firedBy x.2.1 x.2.2 D (.inl t)).Nonempty := by
  rcases t with n | ((_ | ⟨s, y⟩ | ⟨k, y, m, J⟩ | _ | _ | _ | _ | _ | _ | _ | _) | z) <;>
    simp only [hiddenHit, decide_eq_true_eq, Bool.false_eq_true] at h
  · obtain ⟨T, rfl, hT⟩ := h
    exact ⟨.inl T, by simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hT, .inl (T, y), rfl, rfl⟩⟩
  · obtain ⟨p, rfl, hp⟩ := h
    exact ⟨.inr p, by simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hp, .inr (p, y, m, J), rfl, rfl⟩⟩

theorem ffOracles_inv (x : Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (p : (TsigState C × Bool) × Finset (KeySlot C))
    (hp : p.1.2 = true → p.2.Nonempty) :
    ∀ z ∈ support ((ffOracles x dealt t).run p), z.2.1.2 = true → z.2.2.Nonempty := by
  intro z hz
  rcases t with t | q
  · simp only [ffOracles, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨a, -, rfl⟩ := hz
    intro hf
    by_cases h1 : p.1.2 = true
    · simp only [h1, if_true]
      exact hp h1
    · simp only [h1, Bool.false_eq_true, if_false, Bool.false_or] at hf ⊢
      exact (hiddenHit_fired x _ t hf).mono Finset.subset_union_right
  · simp only [ffOracles, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨a, -, rfl⟩ := hz
    exact hp

theorem ffAfter_support (A : TsigAdversary C) (x : Keys3 C) :
    ∀ r ∈ support (ffAfter A x), r.1.2 = true → r.2.Nonempty := by
  intro r hr
  unfold ffAfter at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨o, -, hr⟩ := hr
  rcases o with _ | (top | tree)
  · simp at hr; subst hr; simp
  · simp only [mem_support_bind_iff, support_map, Set.mem_image] at hr
    obtain ⟨w, hw, w', -, rfl⟩ := hr
    exact support_simulateQ_inv _ (fun p => p.1.2 = true → p.2.Nonempty) (ffOracles_inv x _) _ _
      (by simp) w hw
  · simp at hr; subst hr; simp

theorem runSigningWorld_eq_withCount {α : Type} (oa : OracleComp (WorldSpec C) α) :
    runSigningWorld prims oa =
      (fun z => (z.1, z.2.2)) <$> (simulateQ (withCount (signImpl prims)) oa).run ((∅ : HashCache C), 0) := by
  rw [withCount_run, runSigningWorld, StateT.run'_eq, Functor.map_map]
  simp only [zero_add]
  rfl

theorem support_runSigningWorld {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ r ∈ support (runSigningWorld prims oa), r.1 ∈ support oa := by
  intro r hr
  rw [runSigningWorld_eq_withCount, support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  refine support_simulateQ_run'_subset (n := ProbComp) (withCount (signImpl prims)) oa ((∅ : HashCache C), 0) ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨z, hz, rfl⟩

/-- `flaggedRun` with the keys of the first hit. -/
def ffRun (A : TsigAdversary C) : ProbComp (Keys3 C × (((Bool × Bool) × Finset (KeySlot C)) × ℕ)) :=
  keyGen3 >>= fun x => (fun r => (x, r)) <$> runSigningWorld prims (ffAfter A x)

theorem flaggedRun_eq_ffRun (A : TsigAdversary C) :
    flaggedRun prims A = (fun z => (z.1, (z.2.1.1, z.2.2))) <$> ffRun prims A := by
  unfold flaggedRun ffRun
  rw [map_bind]
  refine bind_congr fun x => ?_
  rw [← ffAfter_forget, runSigningWorld_map, Functor.map_map, Functor.map_map]
  rfl

/-- Each key is the first hit with probability at most `(q - C(n, t - 1)) / 2^256` when the keys are
distinct. -/
def KeyHitBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q → ∀ σ : KeySlot C,
    Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2 | ffRun prims A] ≤
      ((q - C.n.choose (C.t - 1) : ℕ) : ℝ≥0∞) / 2 ^ 256

set_option maxRecDepth 100000 in
theorem distinctFlagBound_of_keyHit (h : KeyHitBound prims C) : DistinctFlagBound prims C := by
  intro A q hq
  rw [flaggedRun_eq_ffRun, probEvent_map]
  refine (probEvent_mono fun z hz hf => ?_).trans ((probEvent_exists_finset_le_sum Finset.univ _
    (fun σ z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2)).trans ?_)
  · simp only [Function.comp_apply] at hf
    unfold ffRun at hz
    simp only [mem_support_bind_iff, support_map, Set.mem_image] at hz
    obtain ⟨x, -, r, hr, rfl⟩ := hz
    have h1 : r.1 ∈ support (ffAfter A x) := support_runSigningWorld prims _ r hr
    have h2 : r.1.1.2 = true := hf.2
    obtain ⟨σ, hσ⟩ := ffAfter_support A x r.1 h1 h2
    exact ⟨σ, Finset.mem_univ _, hf.1, hσ⟩
  · refine (Finset.sum_le_sum fun σ _ => h A q hq σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, mul_div_assoc]

/-! ## The honest computations on the slots -/

/-- The state of the split world, the two caches and the count. -/
abbrev WState (C : Committee) := (HashCache C × SlotCache C) × ℕ

/-- A step on the two caches that costs one call. -/
def countStep {α : Type} (m : StateT (HashCache C × SlotCache C) ProbComp α) : StateT (WState C) ProbComp α :=
  StateT.mk fun p => (fun z => (z.1, (z.2, p.2 + 1))) <$> m.run p.1

/-- A call of the honest operators on a slot. -/
def slotC (s : Slot C) : StateT (WState C) ProbComp HashOutput := countStep (onTable (slotOracle s))

/-- A call of the honest operators on `Th`. -/
def hashC : QueryImpl HashSpec (StateT (WState C) ProbComp) := fun input =>
  countStep (onCache ((Query C →ₒ HashOutput).randomOracle (.hash input)))

/-- `F(x)` on the slots. -/
def prfC (x : Point) : StateT (WState C) ProbComp Digest := do
  let terms ← C.terms.mapM fun T => truncateHash <$> slotC (.inl (T, x))
  pure (terms.foldl (· ^^^ ·) 0)

/-- `Eval` on the slots. -/
def evalC (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) : StateT (WState C) ProbComp Digest := do
  let terms ← (C.terms.filter (· ∈ L J i)).mapM fun T => truncateHash <$> slotC (.inl (T, x))
  let masks ← (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).mapM fun j =>
    if h : j = i then pure 0 else truncateHash <$> slotC (.inr (C.pairOf i j (Ne.symm h), x, ec, J))
  pure ((terms ++ masks).foldl (· ^^^ ·) 0)

section Slots

variable (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)

/-- The free calls of `H` and `PRG` in the split world. -/
def freeRo : QueryImpl (RoSpec C) (StateT (WState C) ProbComp) := fun t =>
  splitWorld prims seeds pairKeys (.inr (.inr t))

theorem simulateQ_split_liftFree {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (splitWorld prims seeds pairKeys) (liftFree oa) = simulateQ (freeRo prims seeds pairKeys) oa := by
  refine Eq.trans ?_ ((simulateQ_free (fun t => splitWorld prims seeds pairKeys (.inl t))
    (fun t => splitWorld prims seeds pairKeys (.inr t)) (liftComp oa (LocalSpec C))).trans (simulateQ_liftComp_ro _ oa))
  congr 1
  funext t
  rcases t with t | t <;> rfl

theorem freeRo_eq (t : (RoSpec C).Domain) :
    freeRo prims seeds pairKeys t = countStep (routedLocal prims seeds pairKeys (.inr t)) := rfl

theorem freeRo_hash (input : HashInput) :
    freeRo prims seeds pairKeys (.inl (.hash input)) = hashC input := by
  have h : ¬∃ s, slotInput seeds pairKeys s = .hash input := fun ⟨s, hs⟩ => slotInput_ne_hash seeds pairKeys s input hs
  have e : routedLocal prims seeds pairKeys (.inr (.inl (.hash input))) =
      onCache ((Query C →ₒ HashOutput).randomOracle (.hash input)) := by
    simp only [routedLocal, dif_neg h]
    rfl
  rw [freeRo_eq, e]
  rfl

theorem freeRo_slot (hinj : Function.Injective (slotInput seeds pairKeys)) (s₀ : Slot C) :
    freeRo prims seeds pairKeys (.inl (slotInput seeds pairKeys s₀)) = slotC s₀ := by
  have hex : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀ := ⟨s₀, rfl⟩
  have hc : hex.choose = s₀ := hinj hex.choose_spec
  have e : routedLocal prims seeds pairKeys (.inr (.inl (slotInput seeds pairKeys s₀))) =
      onTable (slotOracle s₀) := by
    simp only [routedLocal, dif_pos hex, hc]
    rfl
  rw [freeRo_eq, e]
  rfl

theorem freeRo_hashQuery (u : Query C) :
    simulateQ (freeRo prims seeds pairKeys) (hashQuery u) = freeRo prims seeds pairKeys (.inl u) :=
  (simulateQ_query _ _).trans (id_map _)

theorem freeRo_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ (freeRo prims seeds pairKeys) (tweakable oa) = simulateQ hashC oa := by
  have h : (freeRo prims seeds pairKeys ∘ₛ fun input => hashQuery (C := C) (.hash input)) = hashC := by
    funext input
    exact (freeRo_hashQuery prims seeds pairKeys _).trans (freeRo_hash prims seeds pairKeys input)
  rw [tweakable, ← QueryImpl.simulateQ_compose, h]

theorem freeRo_prfValue (hinj : Function.Injective (slotInput seeds pairKeys)) (x : Point) :
    simulateQ (freeRo prims seeds pairKeys) (prfValue seeds x) = prfC x := by
  have hterms : ∀ T ∈ C.terms, simulateQ (freeRo prims seeds pairKeys) (prf (seeds T) x) =
      truncateHash <$> slotC (.inl (T, x)) := fun T _ => by
    simp only [prf, simulateQ_map]
    exact congrArg _ ((freeRo_hashQuery prims seeds pairKeys _).trans
      (freeRo_slot prims seeds pairKeys hinj (.inl (T, x))))
  simp only [prfValue, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure, prfC]
  rw [mapM_congr_mem hterms]

theorem freeRo_eval (hinj : Function.Injective (slotInput seeds pairKeys)) (parameter : PublicParameter)
    (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) :
    simulateQ (freeRo prims seeds pairKeys) (eval (dealtKeys parameter seeds pairKeys i) i J x ec) =
      evalC i J x ec := by
  have hterms : ∀ T ∈ C.terms.filter (· ∈ L J i),
      simulateQ (freeRo prims seeds pairKeys) (prf ((dealtKeys parameter seeds pairKeys i).seed T) x) =
      truncateHash <$> slotC (.inl (T, x)) := fun T hT => by
    rw [List.mem_filter] at hT
    simp only [prf, simulateQ_map, dealtKeys, if_pos (mem_holders_of_mem_L (of_decide_eq_true hT.2))]
    exact congrArg _ ((freeRo_hashQuery prims seeds pairKeys _).trans
      (freeRo_slot prims seeds pairKeys hinj (.inl (T, x))))
  have hmasks : ∀ j ∈ C.parties.filter (fun j => j ∈ J.1 ∧ j ≠ i),
      simulateQ (freeRo prims seeds pairKeys)
        (truncateHash <$> hashQuery (.mask ((dealtKeys parameter seeds pairKeys i).pairKey j) x ec J)) =
      (if h : j = i then pure 0 else truncateHash <$> slotC (.inr (C.pairOf i j (Ne.symm h), x, ec, J))) :=
    fun j hj => by
    rw [List.mem_filter] at hj
    have hji : j ≠ i := (of_decide_eq_true hj.2).2
    rw [dif_neg hji, simulateQ_map]
    simp only [dealtKeys, dif_neg hji]
    exact congrArg _ ((freeRo_hashQuery prims seeds pairKeys _).trans
      (freeRo_slot prims seeds pairKeys hinj (.inr (C.pairOf i j (Ne.symm hji), x, ec, J))))
  simp only [eval, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure, evalC]
  rw [mapM_congr_mem hterms, mapM_congr_mem hmasks]

end Slots

/-! ## The honest computations under a monad map -/

section Hom

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] (h : m →ᵐ n)

theorem hom_map {α β : Type} (f : α → β) (x : m α) : h (f <$> x) = f <$> h x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, MonadHom.mmap_bind]
  simp only [Function.comp_def, MonadHom.mmap_pure]

theorem hom_mapM {α β : Type} (f : α → m β) (xs : List α) :
    h (xs.mapM f) = xs.mapM (fun x => h (f x)) := by
  induction xs with
  | nil => exact h.toFun_pure' _
  | cons x xs ih => simp only [List.mapM_cons, MonadHom.mmap_bind, MonadHom.mmap_pure, ih]

omit [LawfulMonad m] [LawfulMonad n] in
theorem hom_sequenceFin {α : Type} : ∀ {k : ℕ} (f : Fin k → m α),
    h (Concrete.sequenceFin f) = Concrete.sequenceFin fun i => h (f i)
  | 0, f => by simp [Concrete.sequenceFin]
  | k + 1, f => by
    simp only [Concrete.sequenceFin, MonadHom.mmap_bind, MonadHom.mmap_pure]
    congr 1; funext a
    exact congrArg (· >>= _) (hom_sequenceFin (k := k) _)

omit [LawfulMonad m] [LawfulMonad n] in
theorem hom_ceremonyOutput (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit))))
    (top : TopTree) (tree : Tree) :
    h (ceremonyOutput lift parameter run top tree) =
      ceremonyOutput (fun oa => h (lift oa)) parameter (fun js => h (run js)) top tree := by
  cases tree with
  | top =>
    simp only [ceremonyOutput, MonadHom.mmap_bind]
    congr 1
    funext out
    cases out <;> simp only [MonadHom.mmap_pure, MonadHom.mmap_bind]
  | bottom b =>
    simp only [ceremonyOutput, MonadHom.mmap_bind]
    congr 1
    funext out
    cases out with
    | none => exact h.toFun_pure' _
    | some outputs =>
      simp only [MonadHom.mmap_bind]
      congr 1
      funext root
      congr 1
      funext base
      congr 1
      funext result
      cases result with
      | none => exact h.toFun_pure' _
      | some pair =>
        rcases pair with ⟨randomness, encoding⟩
        simp only [MonadHom.mmap_bind]
        congr 1
        funext values
        cases values with
        | none => exact h.toFun_pure' _
        | some vals =>
          simp only [MonadHom.mmap_bind]
          congr 1
          funext path
          congr 1
          funext topRoot
          split <;> exact h.toFun_pure' _

theorem hom_referenceJob (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (F : Point → m Digest)
    (P : PublicParameter) (job : Job) :
    h (referenceJob lift F P job) = referenceJob (fun oa => h (lift oa)) (fun x => h (F x)) P job := by
  unfold referenceJob
  rw [MonadHom.mmap_bind, hom_mapM]
  congr 1; funext values
  split <;> simp

theorem hom_referenceTree (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (F : Point → m Digest)
    (P : PublicParameter) (top : TopTree) (tree : Tree) :
    h (referenceTree lift F P top tree) = referenceTree (fun oa => h (lift oa)) (fun x => h (F x)) P top tree := by
  unfold referenceTree
  rw [hom_ceremonyOutput]
  congr 1; funext jobs
  rw [hom_map, hom_mapM]
  congr 2; funext job
  exact hom_referenceJob h lift F P job

theorem hom_signRound2With (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (part : Point → m Digest)
    (P : PublicParameter) (J : C.Quorum) (commitment : Digest) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) :
    h (signRound2With lift part P J commitment e message parts) =
      signRound2With (fun oa => h (lift oa)) (fun x => h (part x)) P J commitment e message parts := by
  unfold signRound2With
  rw [MonadHom.mmap_bind]
  congr 1; funext r
  rcases r with _ | ⟨_, encoding⟩
  · exact h.toFun_pure' _
  · simp only [MonadHom.mmap_bind, hom_sequenceFin, MonadHom.mmap_pure]
    congr 2
    funext l; split_ifs
    · exact hom_map h _ _
    · exact h.toFun_pure' _

/-- A dealt key under a monad map. -/
def Dealt.hmap (dealt : Dealt C m) : Dealt C n :=
  ⟨dealt.keys, dealt.parameter, dealt.top, fun x => h (dealt.value x), fun i J x ec => h (dealt.part i J x ec),
    fun b => h (dealt.bottom b)⟩

theorem hom_tsigOracles (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (dealt : Dealt C m)
    (q : (TsigSpec C).Domain) (s : TsigState C) :
    h ((tsigOracles lift dealt q).run s) = (tsigOracles (fun oa => h (lift oa)) (Dealt.hmap h dealt) q).run s := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp [Dealt.hmap]
  · simp only [tsigOracles, StateT.run_bind, StateT.run_monadLift, monadLift_self, MonadHom.mmap_bind,
      bind_assoc, pure_bind]
    congr 1; funext o
    rcases o with _ | tree
    · simp
    · simp [Dealt.hmap]
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp [Dealt.hmap]
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, MonadHom.mmap_bind,
        bind_assoc, pure_bind]
      congr 1; funext o
      rcases o with _ | tree
      · simp
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, MonadHom.mmap_bind,
          bind_assoc, pure_bind]
        congr 1; funext own
        have key := hom_signRound2With h lift (fun x => dealt.part i J x message) dealt.parameter J
          (tree.commitment e) e message (Function.update parts i own)
        refine congrArg₂ (fun a b => a >>= b) key (funext fun r => ?_)
        rcases r with _ | values
        · simp
        · simp

end Hom

/-! ## The dealt keys on the slots -/

/-- The calls of `H` and `PRG` without slots. -/
def roC : QueryImpl (RoSpec C) (StateT (WState C) ProbComp) := fun t =>
  countStep (onCache (signingLocalAnswer prims (.inr t)))

/-- The honest computations without slots. They only run computations of `Th`. -/
abbrev liftC {α : Type} (oa : OracleComp (RoSpec C) α) : StateT (WState C) ProbComp α := simulateQ (roC prims) oa

theorem roC_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ (roC prims) (tweakable oa) = simulateQ (hashC (C := C)) oa := by
  have h : (roC prims ∘ₛ fun input => hashQuery (C := C) (.hash input)) = hashC := by
    funext input
    exact (simulateQ_query _ _).trans (id_map _)
  rw [tweakable, ← QueryImpl.simulateQ_compose, h]

/-- `KeyGen` on the slots. Only the keys of the corrupt operators depend on the values of the keys. -/
def dealtC (keys : C.Party → Keys C) (P : PublicParameter) (top : TopTree) : Dealt C (StateT (WState C) ProbComp) :=
  ⟨keys, P, top, prfC, fun i J x ec => evalC i J x ec, fun b => (fun | some (.bottom tree) => some tree | _ => none) <$>
    referenceTree (fun oa => simulateQ hashC oa) prfC P top (.bottom b)⟩

theorem referenceTree_congr {m : Type → Type} [Monad m] (lift₁ lift₂ : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (F₁ F₂ : Point → m Digest) (hl : ∀ {α : Type} (oa : OracleComp HashSpec α), lift₁ oa = lift₂ oa)
    (hF : ∀ x, F₁ x = F₂ x) (P : PublicParameter) (top : TopTree) (tree : Tree) :
    referenceTree lift₁ F₁ P top tree = referenceTree lift₂ F₂ P top tree := by
  have e1 : @lift₁ = @lift₂ := by funext α oa; exact hl oa
  have e2 : F₁ = F₂ := funext hF
  rw [e1, e2]

section Dealt

variable (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)

theorem split_referenceTree (hinj : Function.Injective (slotInput seeds pairKeys)) (P : PublicParameter)
    (top : TopTree) (tree : Tree) :
    simulateQ (splitWorld prims seeds pairKeys)
        (referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue seeds p)) P top tree) =
      referenceTree (m := StateT (WState C) ProbComp) (fun oa => simulateQ (hashC (C := C)) oa) prfC P top tree := by
  have h := hom_referenceTree (simulateQ' (splitWorld prims seeds pairKeys)) (fun oa => liftFree (tweakable oa))
    (fun p => liftFree (prfValue seeds p)) P top tree
  refine h.trans (referenceTree_congr _ _ _ _ (fun oa => ?_) (fun x => ?_) P top tree)
  · exact (simulateQ_split_liftFree prims seeds pairKeys _).trans (freeRo_tweakable prims seeds pairKeys oa)
  · exact (simulateQ_split_liftFree prims seeds pairKeys _).trans (freeRo_prfValue prims seeds pairKeys hinj x)

set_option maxRecDepth 100000 in
theorem hmap_dealtWith (hinj : Function.Injective (slotInput seeds pairKeys)) (P : PublicParameter) (top : TopTree) :
    Dealt.hmap (simulateQ' (splitWorld prims seeds pairKeys))
        (dealtWith (fun oa => liftFree oa) P (dealtKeys P seeds pairKeys) top (fun p => liftFree (prfValue seeds p))) =
      dealtC (dealtKeys P seeds pairKeys) P top := by
  have hv : ∀ x, simulateQ (splitWorld prims seeds pairKeys) (liftFree (prfValue seeds x)) = prfC x := fun x =>
    (simulateQ_split_liftFree prims seeds pairKeys _).trans (freeRo_prfValue prims seeds pairKeys hinj x)
  have hp : ∀ i J x ec, simulateQ (splitWorld prims seeds pairKeys)
      (liftFree (eval (dealtKeys P seeds pairKeys i) i J x ec)) = evalC i J x ec := fun i J x ec =>
    (simulateQ_split_liftFree prims seeds pairKeys _).trans (freeRo_eval prims seeds pairKeys hinj P i J x ec)
  have hb : ∀ b, simulateQ (splitWorld prims seeds pairKeys)
      ((fun | some (.bottom tree) => some tree | _ => none) <$>
        referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue seeds p)) P top (.bottom b)) =
      (fun | some (.bottom tree) => some tree | _ => none) <$>
        referenceTree (m := StateT (WState C) ProbComp) (fun oa => simulateQ (hashC (C := C)) oa) prfC P top
          (.bottom b) := fun b =>
    (hom_map (simulateQ' (splitWorld prims seeds pairKeys)) _ _).trans
      (congrArg _ (split_referenceTree prims seeds pairKeys hinj P top _))
  simp only [Dealt.hmap, dealtC, dealtWith, Dealt.mk.injEq, true_and]
  exact ⟨funext hv, funext fun i => funext fun J => funext fun x => funext fun ec => hp i J x ec, funext hb⟩

theorem tsigOracles_lift_congr {m : Type → Type} [Monad m] (lift₁ lift₂ : ∀ {α : Type}, OracleComp (RoSpec C) α → m α)
    (dealt : Dealt C m)
    (h : ∀ P c e msg ρ, lift₁ (signCodeword (C := C) P c e msg ρ) = lift₂ (signCodeword (C := C) P c e msg ρ))
    (q : (TsigSpec C).Domain) : tsigOracles lift₁ dealt q = tsigOracles lift₂ dealt q := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · rfl
  · rfl
  · rfl
  · simp only [tsigOracles, signRound2With, h]

theorem split_tsigOracles (hinj : Function.Injective (slotInput seeds pairKeys)) (P : PublicParameter)
    (top : TopTree) (q : (TsigSpec C).Domain) (s : TsigState C) :
    simulateQ (splitWorld prims seeds pairKeys) ((tsigOracles (fun oa => honestLift oa)
        (dealtWith (fun oa => liftFree oa) P (dealtKeys P seeds pairKeys) top (fun p => liftFree (prfValue seeds p)))
          q).run s) =
      (tsigOracles (fun oa => liftC prims oa) (dealtC (dealtKeys P seeds pairKeys) P top) q).run s := by
  have h := hom_tsigOracles (simulateQ' (splitWorld prims seeds pairKeys)) (fun oa => honestLift oa)
    (dealtWith (fun oa => liftFree oa) P (dealtKeys P seeds pairKeys) top (fun p => liftFree (prfValue seeds p))) q s
  refine h.trans ?_
  rw [hmap_dealtWith prims seeds pairKeys hinj P top]
  refine congrArg (fun I => StateT.run I s) (tsigOracles_lift_congr _ _ _ (fun P c e msg ρ => ?_) q)
  exact ((simulateQ_split_liftFree prims seeds pairKeys _).trans (freeRo_tweakable prims seeds pairKeys _)).trans
    (roC_tweakable prims _).symm

theorem simulateQ_liftComp_sim {σ α : Type} (I : QueryImpl (SimulatorSpec C) (StateT σ ProbComp))
    (oa : OracleComp (LocalSpec C) α) :
    simulateQ I (liftComp oa (SimulatorSpec C)) =
      simulateQ ((fun t => I (.inl t)) : QueryImpl (LocalSpec C) (StateT σ ProbComp)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rw [liftComp_pure, simulateQ_pure, simulateQ_pure]
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, simulateQ_bind]
    simp only [ih]
    congr 1
    rw [liftComp_query]
    rcases t with t | t | t <;>
    exact ((simulateQ_query _ _).trans (id_map _)).trans ((simulateQ_query _ _).trans (id_map _)).symm

theorem simulateQ_adversary_split {σ α : Type} (W : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (oa : OracleComp (LocalSpec C) α) :
    simulateQ W (worldRoles.adversary oa) =
      simulateQ ((fun t => W (.inl (.inl t))) : QueryImpl (LocalSpec C) (StateT σ ProbComp)) oa := by
  refine Eq.trans ?_ ((simulateQ_counted (fun t => W (.inl t)) (fun t => W (.inr t))
    (liftComp oa (SimulatorSpec C))).trans (simulateQ_liftComp_sim _ oa))
  congr 1; funext t; rcases t with t | t <;> rfl

theorem simulateQ_adversary_query {σ : Type} (W : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (t : (LocalSpec C).Domain) :
    simulateQ W (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) = W (.inl (.inl t)) := by
  rw [simulateQ_adversary_split]
  exact (simulateQ_query _ _).trans (id_map _)

end Dealt

/-! ## The fused game -/

/-- The state of the fused game: the game state, the flag, the first hit keys, and the world. -/
abbrev GState (C : Committee) := ((TsigState C × Bool) × Finset (KeySlot C)) × WState C

/-- `KeyGen` of the game for the keys `x` and the top tree `top`. -/
abbrev dealtOf (x : Keys3 C) (top : TopTree) : Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith (fun oa => liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (fun p => liftFree (prfValue x.2.1 p))

/-- The oracles of the forger with the world on split caches. -/
def fusedImpl (x : Keys3 C) (top : TopTree) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT (GState C) ProbComp)
  | .inl t => StateT.mk fun p => (fun z => (z.1, (((p.1.1.1, p.1.1.2 || hiddenHit x p.1.1.1.corrupt t),
      if p.1.1.2 then p.1.2 else p.1.2 ∪ firedBy x.2.1 x.2.2 p.1.1.1.corrupt (.inl t)), z.2))) <$>
      (splitWorld prims x.2.1 x.2.2 (.inl (.inl t))).run p.2
  | .inr q => StateT.mk fun p => (fun z => (z.1.1, (((z.1.2, p.1.1.2), p.1.2), z.2))) <$>
      ((tsigOracles (fun oa => liftC prims oa) (dealtC (dealtKeys x.1 x.2.1 x.2.2) x.1 top) q).run p.1.1.1).run p.2

theorem fused_step (x : Keys3 C) (hinj : Function.Injective (slotInput x.2.1 x.2.2)) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : (TsigState C × Bool) × Finset (KeySlot C)) (c : WState C) :
    (simulateQ (splitWorld prims x.2.1 x.2.2) ((ffOracles x (dealtOf x top) t).run s)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (fusedImpl prims x top t).run (s, c) := by
  rcases t with t | q
  · simp only [ffOracles, fusedImpl, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]
    erw [simulateQ_adversary_query]
    rfl
  · simp only [ffOracles, fusedImpl, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]
    rw [split_tsigOracles prims x.2.1 x.2.2 hinj x.1 top q s.1.1]

theorem fused_run (x : Keys3 C) (hinj : Function.Injective (slotInput x.2.1 x.2.2)) (top : TopTree) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (s : (TsigState C × Bool) × Finset (KeySlot C)) (c : WState C) :
    (simulateQ (splitWorld prims x.2.1 x.2.2) ((simulateQ (ffOracles x (dealtOf x top)) oa).run s)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (fusedImpl prims x top) oa).run (s, c) :=
  simulateQ_fused _ _ _ (fused_step prims x hinj top) oa s c

/-! ## The fused game for another value of one key -/

/-- The keys `x` with the key `σ` set to `k`. -/
def xk (x : Keys3 C) (σ : KeySlot C) (k : HashOutput) : Keys3 C := (x.1, updSeeds σ k x.2.1, updPairs σ k x.2.2)

/-- The forger hits the key `σ` with the value `k`. -/
def HitT (σ : KeySlot C) (t : (LocalSpec C + TsigSpec C).Domain) (k : HashOutput) : Prop :=
  ∃ u, t = .inl (.inr (.inl u)) ∧ HitQuery σ u k

/-- `corrupt i` is accepted and reveals the key `σ`. -/
def RevealsT (σ : KeySlot C) (st : TsigState C) (t : (LocalSpec C + TsigSpec C).Domain) : Prop :=
  ∃ i, t = .inr (.corrupt i) ∧ ¬(C.t - 1 < (insert i st.corrupt).card) ∧ Revealed (insert i st.corrupt) σ

theorem hiddenHit_eq (x : Keys3 C) (D : Finset C.Party) (t : (LocalSpec C).Domain) :
    hiddenHit x D t = decide (firedBy x.2.1 x.2.2 D (.inl t)).Nonempty := by
  refine Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true (hiddenHit_fired x D t h), fun h => ?_⟩
  obtain ⟨σ, hσ⟩ := of_decide_eq_true h
  rcases t with n | u | y
  · simp [firedBy] at hσ
  swap
  · simp [firedBy] at hσ
  simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  obtain ⟨hr, s, rfl, hs⟩ := hσ
  subst hs
  rcases s with ⟨T, y⟩ | ⟨p, y, m, J⟩
  · simp only [hiddenHit, slotInput, decide_eq_true_eq]
    exact ⟨T, rfl, hr⟩
  · simp only [hiddenHit, slotInput, decide_eq_true_eq]
    exact ⟨p, rfl, hr⟩

theorem slot_iff_upd (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (σ : KeySlot C)
    (u : Query C) {k k' : HashOutput} (hk : ¬HitQuery σ u k) (s : Slot C)
    (hs : slotInput (updSeeds σ k seeds) (updPairs σ k pairKeys) s = u) :
    slotKey s ≠ σ ∧ slotInput (updSeeds σ k' seeds) (updPairs σ k' pairKeys) s = u := by
  have hne : slotKey s ≠ σ := fun h => hk ((exists_slot_iff_hitQuery seeds pairKeys σ u k).mp ⟨s, h, hs⟩)
  refine ⟨hne, ?_⟩
  rw [slotInput_upd_of_ne seeds pairKeys hne] at hs ⊢
  exact hs

theorem routedLocal_upd (x : Keys3 C) (σ : KeySlot C) {k k' : HashOutput}
    (hinj : Function.Injective (slotInput (xk x σ k).2.1 (xk x σ k).2.2))
    (hinj' : Function.Injective (slotInput (xk x σ k').2.1 (xk x σ k').2.2))
    (t : (LocalSpec C).Domain) (hk : ¬HitT σ (.inl t) k) (hk' : ¬HitT σ (.inl t) k') :
    routedLocal prims (xk x σ k).2.1 (xk x σ k).2.2 t = routedLocal prims (xk x σ k').2.1 (xk x σ k').2.2 t := by
  rcases t with n | u | y
  · rfl
  · have hu : ¬HitQuery σ u k := fun h => hk ⟨u, rfl, h⟩
    have hu' : ¬HitQuery σ u k' := fun h => hk' ⟨u, rfl, h⟩
    simp only [routedLocal, xk]
    by_cases h₁ : ∃ s, slotInput (updSeeds σ k x.2.1) (updPairs σ k x.2.2) s = u
    · obtain ⟨s, hs⟩ := h₁
      obtain ⟨-, hs'⟩ := slot_iff_upd x.2.1 x.2.2 σ u hu (k' := k') s hs
      have e₁ : ∃ s, slotInput (updSeeds σ k x.2.1) (updPairs σ k x.2.2) s = u := ⟨s, hs⟩
      have e₂ : ∃ s, slotInput (updSeeds σ k' x.2.1) (updPairs σ k' x.2.2) s = u := ⟨s, hs'⟩
      rw [dif_pos e₁, dif_pos e₂, hinj (e₁.choose_spec.trans hs.symm), hinj' (e₂.choose_spec.trans hs'.symm)]
    · have h₂ : ¬∃ s, slotInput (updSeeds σ k' x.2.1) (updPairs σ k' x.2.2) s = u := fun ⟨s, hs⟩ =>
        h₁ ⟨s, (slot_iff_upd x.2.1 x.2.2 σ u hu' (k' := k) s hs).2⟩
      rw [dif_neg h₁, dif_neg h₂]
  · rfl

theorem not_hit_of_not_hitT {σ : KeySlot C} {t : (LocalSpec C).Domain} {k : HashOutput} (h : ¬HitT σ (.inl t) k) :
    ¬Hit σ (.inl t) k := fun ⟨u, hu, hq⟩ => h ⟨u, by cases hu; rfl, hq⟩

set_option maxRecDepth 10000 in
theorem fusedImpl_upd_eq (x : Keys3 C) (σ : KeySlot C) (top : TopTree) {k k' : HashOutput}
    (hinj : Function.Injective (slotInput (xk x σ k).2.1 (xk x σ k).2.2))
    (hinj' : Function.Injective (slotInput (xk x σ k').2.1 (xk x σ k').2.2))
    (t : (LocalSpec C + TsigSpec C).Domain) (p : GState C) (hrev : ¬RevealsT σ p.1.1.1 t)
    (hk : ¬HitT σ t k) (hk' : ¬HitT σ t k') :
    (fusedImpl prims (xk x σ k) top t).run p = (fusedImpl prims (xk x σ k') top t).run p := by
  rcases t with t | q
  · have hw : splitWorld prims (xk x σ k).2.1 (xk x σ k).2.2 (.inl (.inl t)) =
        splitWorld prims (xk x σ k').2.1 (xk x σ k').2.2 (.inl (.inl t)) := by
      change withCount (routedImpl prims _ _) (.inl (.inl t)) = withCount (routedImpl prims _ _) (.inl (.inl t))
      unfold withCount
      rw [show routedImpl prims (xk x σ k).2.1 (xk x σ k).2.2 (.inl (.inl t)) =
          routedLocal prims (xk x σ k).2.1 (xk x σ k).2.2 t from rfl,
        show routedImpl prims (xk x σ k').2.1 (xk x σ k').2.2 (.inl (.inl t)) =
          routedLocal prims (xk x σ k').2.1 (xk x σ k').2.2 t from rfl,
        routedLocal_upd prims x σ hinj hinj' t hk hk']
    have hf := firedBy_upd x.2.1 x.2.2 σ p.1.1.1.corrupt (.inl t) (not_hit_of_not_hitT hk)
      (not_hit_of_not_hitT hk')
    simp only [fusedImpl, StateT.run_mk, hiddenHit_eq, hw]
    simp only [xk] at hf ⊢
    simp only [hf]
    rfl
  · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · simp only [fusedImpl, StateT.run_mk, tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs with h
      · rfl
      · have hi : ¬Revealed {i} σ := fun hi => hrev ⟨i, rfl, h, revealed_mono (by simp) hi⟩
        simp only [xk, dealtC]
        rw [dealtKeys_upd x.2.1 x.2.2 σ x.1 i hi, dealtKeys_upd x.2.1 x.2.2 σ x.1 i hi]
    · rfl
    · rfl
    · rfl

/-! ## Monotone parts of the state -/

theorem withCount_mono {σ α : Type} (I : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (oa : OracleComp (WorldSpec C) α)
    (p : σ × ℕ) : ∀ z ∈ support ((simulateQ (withCount I) oa).run p), p.2 ≤ z.2.2 := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact le_rfl
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    simp only [withCount, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨w', -, rfl⟩ := hw
    exact (Nat.le_add_right _ _).trans (ih _ _ z hz)

set_option maxRecDepth 10000 in
theorem tsigOracles_corrupt_cases (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → StateT (WState C) ProbComp α)
    (dealt : Dealt C (StateT (WState C) ProbComp)) (q : (TsigSpec C).Domain) (st : TsigState C) (c : WState C) :
    ∀ z ∈ support (((tsigOracles lift dealt q).run st).run c), z.1.2.corrupt = st.corrupt ∨ ∃ i, q = .corrupt i ∧ ¬(C.t - 1 < (insert i st.corrupt).card) ∧
        z.1.2.corrupt = insert i st.corrupt := by
  intro z hz
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp at hz; subst hz; exact Or.inl rfl
    · simp at hz; subst hz; exact Or.inr ⟨i, rfl, ‹_›, rfl⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
      mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    rcases w with ⟨_ | tree, c'⟩
    · simp at hz; subst hz; exact Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        mem_support_bind_iff, StateT.run_pure] at hz
      obtain ⟨w, -, hz⟩ := hz
      simp at hz; subst hz; exact Or.inl rfl
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp at hz; subst hz; exact Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self, pure_bind,
        mem_support_bind_iff, StateT.run_map, support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨a, -, hw⟩ := hw
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact Or.inl rfl
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp at hz; subst hz; exact Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      obtain ⟨w, -, hz⟩ := hz
      rcases w with ⟨_ | tree, c'⟩
      · simp at hz; subst hz; exact Or.inl rfl
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          mem_support_bind_iff] at hz
        obtain ⟨w, -, w', -, hz⟩ := hz
        rcases w' with ⟨_ | values, c''⟩
        · simp at hz; subst hz; exact Or.inl rfl
        · simp at hz; subst hz; exact Or.inl rfl

/-! ## The steps of the fused game -/

/-- The cost of a call of the forger that can hit a key. -/
def roCost : (LocalSpec C + TsigSpec C).Domain → ℕ
  | .inl (.inr (.inl _)) => 1
  | _ => 0

section Steps

variable (x : Keys3 C) (top : TopTree)

/-- A step either keeps the corrupt operators or accepts one more. It adds to the first hit keys
only keys that its call hits while they are not revealed and the flag is down. -/
theorem fused_cases (t : (LocalSpec C + TsigSpec C).Domain) (p : GState C) :
    ∀ z ∈ support ((fusedImpl prims x top t).run p),
      (z.2.1.1.1.corrupt = p.1.1.1.corrupt ∨ ∃ i, t = .inr (.corrupt i) ∧
        ¬(C.t - 1 < (insert i p.1.1.1.corrupt).card) ∧ z.2.1.1.1.corrupt = insert i p.1.1.1.corrupt) ∧
      (∀ σ, σ ∈ z.2.1.2 → σ ∈ p.1.2 ∨ (¬Revealed p.1.1.1.corrupt σ ∧
        ∃ u, t = .inl (.inr (.inl u)) ∧ ∃ s, slotKey s = σ ∧ slotInput x.2.1 x.2.2 s = u)) := by
  intro z hz
  rcases t with t | q
  · simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    refine ⟨Or.inl rfl, fun σ hσ => ?_⟩
    split_ifs at hσ
    · exact Or.inl hσ
    · rcases Finset.mem_union.mp hσ with h | h
      · exact Or.inl h
      · right
        rcases t with n | u | y
        · simp [firedBy] at h
        · simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and] at h
          exact ⟨h.1, u, rfl, h.2⟩
        · simp [firedBy] at h
  · simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨?_, fun σ hσ => Or.inl hσ⟩
    rcases tsigOracles_corrupt_cases _ _ q _ _ w hw with h | ⟨i, rfl, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, rfl, h1, h2⟩

theorem fused_count_mono (hinj : Function.Injective (slotInput x.2.1 x.2.2)) (t : (LocalSpec C + TsigSpec C).Domain)
    (p : GState C) : ∀ z ∈ support ((fusedImpl prims x top t).run p), p.2.2 ≤ z.2.2.2 := by
  intro z hz
  have h := fused_step prims x hinj top t p.1 p.2
  have hz' : ((z.1, z.2.1), z.2.2) ∈ support ((simulateQ (splitWorld prims x.2.1 x.2.2)
      ((ffOracles x (dealtOf x top) t).run p.1)).run p.2) := by
    rw [h, support_map]
    exact ⟨z, hz, rfl⟩
  exact withCount_mono (routedImpl prims x.2.1 x.2.2) _ p.2 ((z.1, z.2.1), z.2.2) hz'

/-- A call of `H` by the forger costs one call. -/
theorem fused_count_ro (u : Query C) (p : GState C) :
    ∀ z ∈ support ((fusedImpl prims x top (.inl (.inr (.inl u)))).run p), z.2.2.2 = p.2.2 + 1 := by
  intro z hz
  simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  change w ∈ support ((withCount (routedImpl prims x.2.1 x.2.2) (.inl (.inl (.inr (.inl u))))).run p.2) at hw
  simp only [withCount, StateT.run_mk, support_map, Set.mem_image] at hw
  obtain ⟨w', -, rfl⟩ := hw
  rfl

/-- After the flag, the first hit keys stay. -/
theorem fused_frozen (t : (LocalSpec C + TsigSpec C).Domain) (p : GState C) (hp : p.1.1.2 = true) :
    ∀ z ∈ support ((fusedImpl prims x top t).run p), z.2.1.1.2 = true ∧ z.2.1.2 = p.1.2 := by
  intro z hz
  rcases t with t | q
  · simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    simp [hp]
  · simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact ⟨hp, rfl⟩

/-- A key that is revealed and not a first hit stays so. -/
theorem fused_revealed_stays (σ : KeySlot C) (t : (LocalSpec C + TsigSpec C).Domain) (p : GState C)
    (hr : Revealed p.1.1.1.corrupt σ) (hσ : σ ∉ p.1.2) :
    ∀ z ∈ support ((fusedImpl prims x top t).run p), Revealed z.2.1.1.1.corrupt σ ∧ σ ∉ z.2.1.2 := by
  intro z hz
  obtain ⟨h1, h2⟩ := fused_cases prims x top t p z hz
  refine ⟨?_, fun h => ?_⟩
  · rcases h1 with h | ⟨i, -, -, h⟩
    · rw [h]; exact hr
    · rw [h]; exact revealed_mono (Finset.subset_insert _ _) hr
  · rcases h2 σ h with h | ⟨h, -⟩
    · exact hσ h
    · exact h hr

/-- A step that reveals `σ` leaves it out of the first hit keys for good. -/
theorem fused_reveals (σ : KeySlot C) (t : (LocalSpec C + TsigSpec C).Domain) (p : GState C)
    (hrev : RevealsT σ p.1.1.1 t) (hσ : σ ∉ p.1.2) :
    ∀ z ∈ support ((fusedImpl prims x top t).run p), Revealed z.2.1.1.1.corrupt σ ∧ σ ∉ z.2.1.2 := by
  intro z hz
  obtain ⟨i, rfl, hacc, hi⟩ := hrev
  obtain ⟨h1, h2⟩ := fused_cases prims x top _ p z hz
  have hc : z.2.1.1.1.corrupt = insert i p.1.1.1.corrupt := by
    simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind, if_neg hacc] at hw
    simp at hw
    subst hw
    rfl
  refine ⟨hc ▸ hi, fun h => ?_⟩
  rcases h2 σ h with h | ⟨-, u, hu, -⟩
  · exact hσ h
  · cases hu

/-- A step that does not hit `σ` and does not reveal it keeps it hidden and out of the first hit keys. -/
theorem fused_miss (σ : KeySlot C) (t : (LocalSpec C + TsigSpec C).Domain) (p : GState C)
    (hD : ¬Revealed p.1.1.1.corrupt σ) (hσ : σ ∉ p.1.2) (hrev : ¬RevealsT σ p.1.1.1 t)
    (hk : ∀ u, t = .inl (.inr (.inl u)) → ¬∃ s, slotKey s = σ ∧ slotInput x.2.1 x.2.2 s = u) :
    ∀ z ∈ support ((fusedImpl prims x top t).run p), ¬Revealed z.2.1.1.1.corrupt σ ∧ σ ∉ z.2.1.2 := by
  intro z hz
  obtain ⟨h1, h2⟩ := fused_cases prims x top t p z hz
  refine ⟨?_, fun h => ?_⟩
  · rcases h1 with h | ⟨i, rfl, hacc, h⟩
    · rw [h]; exact hD
    · rw [h]; exact fun hi => hrev ⟨i, rfl, hacc, hi⟩
  · rcases h2 σ h with h | ⟨-, u, rfl, hs⟩
    · exact hσ h
    · exact hk u rfl hs

/-- A call that hits the hidden key `σ` while the flag is down makes `σ` a first hit key. -/
theorem fused_hit (σ : KeySlot C) (u : Query C) (p : GState C) (hD : ¬Revealed p.1.1.1.corrupt σ)
    (hf : p.1.1.2 = false) (hs : ∃ s, slotKey s = σ ∧ slotInput x.2.1 x.2.2 s = u) :
    ∀ z ∈ support ((fusedImpl prims x top (.inl (.inr (.inl u)))).run p), σ ∈ z.2.1.2 := by
  intro z hz
  simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, -, rfl⟩ := hz
  simp only [hf, Bool.false_eq_true, if_false, Finset.mem_union, firedBy, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact Or.inr ⟨hD, hs⟩

theorem probComp_support_nonempty {α : Type} (mx : ProbComp α) : (support mx).Nonempty := by
  by_contra h
  have h1 := (probFailure_eq_one_iff_not_nonempty mx).mpr h
  simp at h1

/-- The count does not drop over a run. -/
theorem fused_sim_count_mono (hinj : Function.Injective (slotInput x.2.1 x.2.2)) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (p : GState C) :
    ∀ w ∈ support ((simulateQ (fusedImpl prims x top) oa).run p), p.2.2 ≤ w.2.2.2 :=
  support_simulateQ_inv _ (fun s => p.2.2 ≤ s.2.2) (fun t s hs z hz => hs.trans
    (fused_count_mono prims x top hinj t s z hz)) oa p le_rfl

/-- A revealed key or a raised flag keeps `σ` out of the first hit keys. -/
theorem fused_ff_zero (σ : KeySlot C) {α : Type} (oa : OracleComp (LocalSpec C + TsigSpec C) α) (p : GState C)
    (h : Revealed p.1.1.1.corrupt σ ∨ p.1.1.2 = true) (hσ : σ ∉ p.1.2) :
    Pr[fun z => σ ∈ z.2.1.2 | (simulateQ (fusedImpl prims x top) oa).run p] = 0 := by
  refine probEvent_eq_zero fun z hz => ?_
  have := support_simulateQ_inv _ (fun s : GState C => (Revealed s.1.1.1.corrupt σ ∨ s.1.1.2 = true) ∧ σ ∉ s.1.2)
    (fun t s hs w hw => ?_) oa p ⟨h, hσ⟩ z hz
  · exact this.2
  · rcases hs.1 with hr | hf
    · obtain ⟨h1, h2⟩ := fused_revealed_stays prims x top σ t s hr hs.2 w hw
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := fused_frozen prims x top t s hf w hw
      exact ⟨Or.inr h1, h2 ▸ hs.2⟩

theorem fused_count_ct (hinj : Function.Injective (slotInput x.2.1 x.2.2)) (t : (LocalSpec C + TsigSpec C).Domain)
    (p : GState C) : ∀ z ∈ support ((fusedImpl prims x top t).run p), p.2.2 + roCost t ≤ z.2.2.2 := by
  intro z hz
  rcases t with (n | u | y) | q
  · exact fused_count_mono prims x top hinj _ p z hz
  · simp only [fusedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    change w ∈ support ((withCount (routedImpl prims x.2.1 x.2.2) (.inl (.inl (.inr (.inl u))))).run p.2) at hw
    simp only [withCount, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨w', -, rfl⟩ := hw
    exact le_rfl
  · exact fused_count_mono prims x top hinj _ p z hz
  · exact fused_count_mono prims x top hinj _ p z hz

end Steps

/-! ## The sum over the values of one key -/

theorem hitT_iff (x : Keys3 C) (σ : KeySlot C) (k : HashOutput) (u : Query C) :
    (∃ s, slotKey s = σ ∧ slotInput (xk x σ k).2.1 (xk x σ k).2.2 s = u) ↔ HitQuery σ u k :=
  exists_slot_iff_hitQuery x.2.1 x.2.2 σ u k

open Classical in
/-- The weight of the first hits of `σ` over its values outside `V` is at most the rest of the budget. -/
theorem sum_ff_le (x : Keys3 C) (σ : KeySlot C) (top : TopTree) (q : ℕ) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) : ∀ (V : Finset HashOutput) (p : GState C),
    (∀ k ∉ V, Function.Injective (slotInput (xk x σ k).2.1 (xk x σ k).2.2)) →
    ¬Revealed p.1.1.1.corrupt σ → σ ∉ p.1.2 →
    (∀ k ∉ V, ∀ z ∈ support ((simulateQ (fusedImpl prims (xk x σ k) top) oa).run p), z.2.2.2 ≤ q) →
    ∑ k ∈ Finset.univ \ V, Pr[fun z => σ ∈ z.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) oa).run p] ≤
      ((q - p.2.2 : ℕ) : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro V p _ _ hσ _
    refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ?_) bot_le
    simp [hσ]
  | query_bind t cont ih =>
    intro V p hinj hD hσ hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, probEvent_bind_eq_tsum] at hq ⊢
    by_cases hf : p.1.1.2 = true
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ENNReal.tsum_eq_zero.mpr fun z => ?_) bot_le
      by_cases hz : z ∈ support ((fusedImpl prims (xk x σ k) top t).run p)
      · obtain ⟨h1, h2⟩ := fused_frozen prims _ top t p hf z hz
        rw [fused_ff_zero prims _ top σ _ z.2 (Or.inr h1) (h2 ▸ hσ), mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul]
    have hf' : p.1.1.2 = false := by simpa using hf
    by_cases hrev : RevealsT σ p.1.1.1 t
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ENNReal.tsum_eq_zero.mpr fun z => ?_) bot_le
      by_cases hz : z ∈ support ((fusedImpl prims (xk x σ k) top t).run p)
      · obtain ⟨h1, h2⟩ := fused_reveals prims _ top σ t p hrev hσ z hz
        rw [fused_ff_zero prims _ top σ _ z.2 (Or.inl h1) h2, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul]
    -- the values of `σ` that the call hits
    obtain ⟨H, hHdef⟩ : ∃ H : Finset HashOutput, H = Finset.univ.filter fun k => HitT σ t k := ⟨_, rfl⟩
    have hmemH : ∀ k, k ∈ H ↔ HitT σ t k := fun k => by simp [hHdef]
    have hH : H.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
      obtain ⟨u, rfl, hu⟩ := (hmemH a).mp ha
      obtain ⟨u', hu', hu''⟩ := (hmemH b).mp hb
      cases hu'
      exact hitQuery_unique hu hu''
    obtain ⟨V', hV'⟩ : ∃ V' : Finset HashOutput, V' = V ∪ H := ⟨_, rfl⟩
    have hsplit : Finset.univ \ V = (H \ V) ∪ (Finset.univ \ V') := by
      ext k
      subst hV'
      by_cases hk : k ∈ H <;> by_cases hkV : k ∈ V <;> simp [hk, hkV]
    have hdisj : Disjoint (H \ V) (Finset.univ \ V') := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      subst hV'
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hk hk'
      exact hk'.2 hk.1
    rw [hsplit, Finset.sum_union hdisj]
    -- the cost of the call
    obtain ⟨ct, hct⟩ : ∃ ct : ℕ, ct = roCost t := ⟨_, rfl⟩
    have hcount : ∀ k ∉ V, ∀ z ∈ support ((fusedImpl prims (xk x σ k) top t).run p), p.2.2 + ct ≤ z.2.2.2 :=
      fun k hk z hz => hct ▸ fused_count_ct prims _ top (hinj k hk) t p z hz
    -- the budget covers the call
    have hbud : ∀ k ∉ V, p.2.2 + ct ≤ q := by
      intro k hk
      obtain ⟨z, hz⟩ := probComp_support_nonempty ((fusedImpl prims (xk x σ k) top t).run p)
      obtain ⟨w, hw⟩ := probComp_support_nonempty ((simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2)
      have h1 := hq k hk w ((mem_support_bind_iff _ _ _).mpr ⟨z, hz, hw⟩)
      have h2 := fused_sim_count_mono prims _ top (hinj k hk) (cont z.1) z.2 w hw
      have h3 := hcount k hk z hz
      omega
    -- the hit part
    have hhit : ∑ k ∈ H \ V, (∑' z, Pr[= z | (fusedImpl prims (xk x σ k) top t).run p] *
        Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2]) ≤ ct := by
      rcases (H \ V).eq_empty_or_nonempty with he | ⟨k₀, hk₀⟩
      · rw [he, Finset.sum_empty]; exact zero_le
      have hct1 : ct = 1 := by
        obtain ⟨u, hu, -⟩ := (hmemH k₀).mp (Finset.mem_sdiff.mp hk₀).1
        rw [hct, hu]; rfl
      rw [hct1, Nat.cast_one]
      calc ∑ k ∈ H \ V, (∑' z, Pr[= z | (fusedImpl prims (xk x σ k) top t).run p] *
            Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2])
          ≤ ∑ k ∈ H \ V, (1 : ℝ≥0∞) := Finset.sum_le_sum fun k _ => by
            rw [← probEvent_bind_eq_tsum]; exact probEvent_le_one
        _ = ((H \ V).card : ℝ≥0∞) := by simp
        _ ≤ 1 := by exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hH
    -- the other values
    have hrest : ∑ k ∈ Finset.univ \ V', (∑' z, Pr[= z | (fusedImpl prims (xk x σ k) top t).run p] *
        Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2]) ≤
          ((q - (p.2.2 + ct) : ℕ) : ℝ≥0∞) := by
      rcases (Finset.univ \ V').eq_empty_or_nonempty with he | ⟨k₁, hk₁⟩
      · rw [he, Finset.sum_empty]; exact zero_le
      have hnot : ∀ k ∈ Finset.univ \ V', k ∉ V ∧ ¬HitT σ t k := fun k hk => by
        have := (Finset.mem_sdiff.mp hk).2
        rw [hV', Finset.mem_union, not_or] at this
        exact ⟨this.1, fun h => this.2 ((hmemH k).mpr h)⟩
      obtain ⟨hk₁V, hk₁H⟩ := hnot k₁ hk₁
      set M := (fusedImpl prims (xk x σ k₁) top t).run p with hM
      have hstep : ∀ k ∈ Finset.univ \ V', (fusedImpl prims (xk x σ k) top t).run p = M := fun k hk =>
        fusedImpl_upd_eq prims x σ top (hinj k (hnot k hk).1) (hinj k₁ hk₁V) t p hrev (hnot k hk).2 hk₁H
      have hz : ∀ z ∈ support M, ∑ k ∈ Finset.univ \ V',
          Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2] ≤
            ((q - (p.2.2 + ct) : ℕ) : ℝ≥0∞) := by
        intro z hzM
        obtain ⟨hzD, hzσ⟩ := fused_miss prims (xk x σ k₁) top σ t p hD hσ hrev
          (fun u hu hs => hk₁H ⟨u, hu, (hitT_iff x σ k₁ u).mp hs⟩) z hzM
        refine (ih z.1 V' z.2 (fun k hk => hinj k fun h => hk (hV' ▸ Finset.mem_union_left _ h)) hzD hzσ
          (fun k hk w hw => ?_)).trans ?_
        · have hkV : k ∉ V := fun h => hk (hV' ▸ Finset.mem_union_left _ h)
          refine hq k hkV w ((mem_support_bind_iff _ _ _).mpr ⟨z, ?_, hw⟩)
          rw [hstep k (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩)]
          exact hzM
        · have := hcount k₁ hk₁V z hzM
          exact_mod_cast (by omega : q - z.2.2.2 ≤ q - (p.2.2 + ct))
      calc ∑ k ∈ Finset.univ \ V', (∑' z, Pr[= z | (fusedImpl prims (xk x σ k) top t).run p] *
            Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2])
          = ∑ k ∈ Finset.univ \ V', (∑' z, Pr[= z | M] *
            Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2]) :=
            Finset.sum_congr rfl fun k hk => by rw [hstep k hk]
        _ = ∑' z, Pr[= z | M] * ∑ k ∈ Finset.univ \ V',
            Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (fusedImpl prims (xk x σ k) top) (cont z.1)).run z.2] := by
            rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
            exact tsum_congr fun z => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑' z, Pr[= z | M] * ((q - (p.2.2 + ct) : ℕ) : ℝ≥0∞) := ENNReal.tsum_le_tsum fun z => by
            by_cases hzM : z ∈ support M
            · exact mul_le_mul_right (hz z hzM) _
            · simp [probOutput_eq_zero_of_not_mem_support hzM]
        _ ≤ ((q - (p.2.2 + ct) : ℕ) : ℝ≥0∞) := by
            rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
    by_cases hne : (Finset.univ \ V).Nonempty
    · refine (add_le_add hhit hrest).trans ?_
      obtain ⟨k, hk⟩ := hne
      have := hbud k (Finset.mem_sdiff.mp hk).2
      rw [← Nat.cast_add]
      exact_mod_cast (by omega : ct + (q - (p.2.2 + ct)) ≤ q - p.2.2)
    · have hV : Finset.univ \ V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have h1 : H \ V = ∅ := Finset.subset_empty.mp (hV ▸ Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl V))
      have h2 : Finset.univ \ V' = ∅ := Finset.subset_empty.mp
        (hV ▸ Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (hV' ▸ Finset.subset_union_left))
      rw [h1, h2, Finset.sum_empty, add_zero]
      exact zero_le

/-! ## The calls of the dealer before the forger -/

theorem simulateQ_withCount_liftFree {σ α : Type} (I : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (oa : OracleComp (RoSpec C) α) :
    simulateQ (withCount I) (liftFree oa) =
      simulateQ ((fun t => withCount I (.inr (.inr t))) : QueryImpl (RoSpec C) (StateT (σ × ℕ) ProbComp)) oa := by
  refine Eq.trans ?_ ((simulateQ_free (fun t => withCount I (.inl t)) (fun t => withCount I (.inr t))
    (liftComp oa (LocalSpec C))).trans (simulateQ_liftComp_ro _ oa))
  congr 1
  funext t
  rcases t with t | t <;> rfl

/-- `mapM` of steps that each add one to the count adds the length of the list. -/
theorem mapM_count {σ α β : Type} (f : α → StateT (σ × ℕ) ProbComp β)
    (hf : ∀ a s, ∀ z ∈ support ((f a).run s), z.2.2 = s.2 + 1) :
    ∀ (l : List α) (s : σ × ℕ), ∀ z ∈ support ((l.mapM f).run s), z.2.2 = s.2 + l.length := by
  intro l
  induction l with
  | nil => intro s z hz; simp at hz; subst hz; rfl
  | cons a l ih =>
    intro s z hz
    simp only [List.mapM_cons, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨w, hw, w', hw', rfl⟩ := hz
    rw [ih w.2 w' hw', hf a s w hw, List.length_cons]
    omega

theorem prfValue_count {σ : Type} (I : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (seeds : C.Term → HashOutput)
    (y : Point) (s : σ × ℕ) : ∀ z ∈ support ((simulateQ (withCount I) (liftFree (prfValue seeds y))).run s),
      z.2.2 = s.2 + C.n.choose (C.t - 1) := by
  intro z hz
  rw [simulateQ_withCount_liftFree] at hz
  simp only [prfValue, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure, StateT.run_bind,
    mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hlen : C.terms.length = C.n.choose (C.t - 1) := by
    rw [Committee.terms, Finset.length_toList, Finset.card_univ, card_term]
  rw [← hlen]
  refine mapM_count _ (fun T s' z hz => ?_) C.terms s w hw
  simp only [prf, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  erw [simulateQ_query] at hz'
  simp only [OracleQuery.input_query, OracleQuery.cont_query, StateT.run_map, support_map,
    Set.mem_image] at hz'
  obtain ⟨w', hw', rfl⟩ := hz'
  change w' ∈ support ((fun z => (z.1, z.2, s'.2 + 1)) <$>
    (I (Sum.inr (Sum.inr (Sum.inl (Query.prf (seeds T) y))))).run s'.1) at hw'
  rw [support_map] at hw'
  obtain ⟨w'', -, rfl⟩ := hw'
  rfl

theorem topJobs_head : ∃ j rest pt, topJobs = j :: rest ∧ j.points = [pt] := by
  have hmem : (⟨.chainEnd (topKey ⟨0, by decide⟩) ⟨0, by decide⟩,
      [.chain topLayer (topKey ⟨0, by decide⟩) ⟨0, by decide⟩ (digit 0)]⟩ : Job) ∈ topJobs := by
    simp only [topJobs, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
  obtain ⟨j, rest, h⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have hj : j ∈ topJobs := h ▸ List.mem_cons_self
  simp only [topJobs, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hj
  obtain ⟨b, l, rfl⟩ := hj
  exact ⟨_, rest, _, h, rfl⟩

theorem dealer_first {m : Type → Type} [Monad m] [LawfulMonad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (F : Point → m Digest) (P : PublicParameter) :
    ∃ pt, ∃ R : Digest → m (Option TreeOutput), referenceTree lift F P emptyTop .top = F pt >>= R := by
  obtain ⟨j, rest, pt, h, hj⟩ := topJobs_head
  simp only [referenceTree, ceremonyOutput, h, List.mapM_cons, referenceJob, hj, List.mapM_nil, bind_assoc,
    map_bind, pure_bind]
  exact ⟨pt, _, rfl⟩

/-- The top tree of the dealer costs at least the `C(n, t - 1)` calls of its first PRF value. -/
theorem dealer_count {σ : Type} (I : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (x : Keys3 C) (s : σ × ℕ) :
    ∀ z ∈ support ((simulateQ (withCount I) (referenceTree (fun oa => liftFree (tweakable oa))
      (fun p => liftFree (prfValue x.2.1 p)) x.1 emptyTop .top)).run s), s.2 + C.n.choose (C.t - 1) ≤ z.2.2 := by
  intro z hz
  obtain ⟨pt, R, h⟩ := dealer_first (m := OracleComp (WorldSpec C)) (fun oa => liftFree (tweakable oa))
    (fun p => liftFree (prfValue x.2.1 p)) x.1
  rw [h, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [← prfValue_count I x.2.1 pt s w hw]
  exact withCount_mono I _ w.2 z hz

set_option maxRecDepth 100000 in
theorem dealerBudget : DealerBudget prims C := by
  intro A q hq _
  obtain ⟨x, hx⟩ := probComp_support_nonempty (keyGen3 (C := C))
  obtain ⟨r, hr⟩ := probComp_support_nonempty (runSigningWorld prims (gameAfter A x))
  have hrq := queryBound_gameAfter prims A q hq x hx r hr
  rw [runSigningWorld_eq_withCount, support_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  unfold gameAfter at hw
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
  obtain ⟨o, ho, hw⟩ := hw
  have h1 := dealer_count (signImpl prims) x ((∅ : HashCache C), 0) o ho
  have h2 := withCount_mono (signImpl prims) _ o.2 w hw
  simp only at hrq h1
  omega

/-! ## `ffAfter` in the split world -/

/-- The top tree of the dealer on the slots. -/
abbrev dealerSlot (P : PublicParameter) : ProbComp (Option TreeOutput × WState C) :=
  (referenceTree (m := StateT (WState C) ProbComp) (fun oa => simulateQ (hashC (C := C)) oa) prfC P emptyTop .top).run
    ((∅, ∅), 0)

/-- The run after the dealer, with the forger in the fused game. -/
def restOf (A : TsigAdversary C) (x : Keys3 C) :
    Option TreeOutput × WState C → ProbComp (((Bool × Bool) × Finset (KeySlot C)) × WState C)
  | (some (.top top), s) => (simulateQ (fusedImpl prims x top) (A ⟨top.root, x.1⟩ top)).run (((tsigInit, false), ∅), s) >>=
      fun z => (fun v => (((v.1.1, z.2.1.1.2), z.2.1.2), v.2)) <$>
        (simulateQ (splitWorld prims x.2.1 x.2.2) (tsigFinish (dealtOf x top) (z.1, z.2.1.1.1))).run z.2.2
  | (_, s) => pure (((false, false), ∅), s)

theorem split_ffAfter (A : TsigAdversary C) (x : Keys3 C) (hinj : Function.Injective (slotInput x.2.1 x.2.2)) :
    (simulateQ (splitWorld prims x.2.1 x.2.2) (ffAfter A x)).run ((∅, ∅), 0) =
      dealerSlot (C := C) x.1 >>= restOf prims A x := by
  unfold ffAfter
  rw [simulateQ_bind, StateT.run_bind, split_referenceTree prims x.2.1 x.2.2 hinj]
  refine bind_congr fun os => ?_
  rcases os with ⟨_ | (top | tree), s⟩
  · rfl
  · simp only [restOf, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map]
    rw [fused_run prims x hinj top, bind_map_left]
    rfl
  · rfl

theorem probEvent_bind_le_of_imp {α β : Type} (m : ProbComp α) (g : α → ProbComp β) (E : β → Prop) (E' : α → Prop)
    (h : ∀ a ∈ support m, ∀ b ∈ support (g a), E b → E' a) : Pr[E | m >>= g] ≤ Pr[E' | m] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support m
  · by_cases hE : E' a
    · rw [if_pos hE]
      exact mul_le_of_le_one_right' probEvent_le_one
    · rw [if_neg hE, probEvent_eq_zero fun b hb hb' => hE (h a ha b hb hb'), mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul]
    exact zero_le

theorem mem_support_keyGen3 (x : Keys3 C) : x ∈ support (keyGen3 (C := C)) := by
  simp [keyGen3]

set_option maxRecDepth 100000 in
/-- The budget of the game bounds the split run of `ffAfter`. -/
theorem split_budget (A : TsigAdversary C) (q : ℕ) (hq : HasSigningQueryBound prims (tsigGame A) q) (x : Keys3 C)
    (hinj : Function.Injective (slotInput x.2.1 x.2.2)) :
    ∀ w ∈ support (dealerSlot (C := C) x.1 >>= restOf prims A x), w.2.2 ≤ q := by
  intro w hw
  have hg : gameAfter A x = (fun w => w.1.1) <$> ffAfter A x := by
    rw [← flaggedAfter_forget, ← ffAfter_forget, Functor.map_map]
  have hr : (w.1.1.1, w.2.2) ∈ support (runSigningWorld prims (gameAfter A x)) := by
    rw [hg, runSigningWorld_map, support_map, runSigningWorld_eq_split prims x.2.1 x.2.2 hinj, support_map,
      split_ffAfter prims A x hinj]
    exact ⟨(w.1, w.2.2), ⟨w, hw, rfl⟩, rfl⟩
  exact queryBound_gameAfter prims A q hq x (mem_support_keyGen3 x) _ hr

theorem not_revealed_empty (σ : KeySlot C) : ¬Revealed (∅ : Finset C.Party) σ := by
  rcases σ with T | p <;> simp [Revealed]

set_option maxRecDepth 100000 in
/-- After each top tree of the dealer, the first hits of `σ` over its good values cost at most
`q - C(n, t - 1)`. -/
theorem rest_sum_le (A : TsigAdversary C) (q : ℕ) (hq : HasSigningQueryBound prims (tsigGame A) q) (x : Keys3 C)
    (σ : KeySlot C) (V : Finset HashOutput) (hV : ∀ u ∉ V, Function.Injective (slotInput (xk x σ u).2.1 (xk x σ u).2.2))
    (u₀ : HashOutput) (hu₀ : u₀ ∉ V) (os : Option TreeOutput × WState C) (hos : os ∈ support (dealerSlot (C := C) x.1)) :
    ∑ u ∈ Finset.univ \ V, Pr[fun w => σ ∈ w.1.2 | restOf prims A (xk x σ u) os] ≤
      ((q - C.n.choose (C.t - 1) : ℕ) : ℝ≥0∞) := by
  rcases os with ⟨_ | (top | tree), s⟩
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun u _ => ?_) zero_le
    simp [restOf]
  · have hC : C.n.choose (C.t - 1) ≤ s.2 := by
      have h := dealer_count (routedImpl prims (xk x σ u₀).2.1 (xk x σ u₀).2.2) (xk x σ u₀) (((∅, ∅), 0) : WState C)
        (some (.top top), s) (by rw [split_referenceTree prims _ _ (hV u₀ hu₀)]; exact hos)
      simpa using h
    have hbud : ∀ u ∉ V, ∀ z ∈ support ((simulateQ (fusedImpl prims (xk x σ u) top) (A ⟨top.root, x.1⟩ top)).run
        (((tsigInit, false), ∅), s)), z.2.2.2 ≤ q := by
      intro u hu z hz
      obtain ⟨v, hv⟩ := probComp_support_nonempty ((simulateQ (splitWorld prims (xk x σ u).2.1 (xk x σ u).2.2)
        (tsigFinish (dealtOf (xk x σ u) top) (z.1, z.2.1.1.1))).run z.2.2)
      have h1 := withCount_mono _ _ z.2.2 v hv
      have h2 := split_budget prims A q hq (xk x σ u) (hV u hu) (((v.1.1, z.2.1.1.2), z.2.1.2), v.2)
        ((mem_support_bind_iff _ _ _).mpr ⟨(some (.top top), s), hos, (mem_support_bind_iff _ _ _).mpr
          ⟨z, hz, by rw [support_map]; exact ⟨v, hv, rfl⟩⟩⟩)
      exact h1.trans h2
    calc ∑ u ∈ Finset.univ \ V, Pr[fun w => σ ∈ w.1.2 | restOf prims A (xk x σ u) (some (.top top), s)]
        ≤ ∑ u ∈ Finset.univ \ V, Pr[fun z => σ ∈ z.2.1.2 |
            (simulateQ (fusedImpl prims (xk x σ u) top) (A ⟨top.root, x.1⟩ top)).run (((tsigInit, false), ∅), s)] :=
          Finset.sum_le_sum fun u _ => probEvent_bind_le_of_imp _ _ _ _ fun z _ w hw hσ => by
            rw [support_map] at hw
            obtain ⟨v, -, rfl⟩ := hw
            exact hσ
      _ ≤ ((q - s.2 : ℕ) : ℝ≥0∞) := sum_ff_le prims x σ top q (A ⟨top.root, x.1⟩ top) V (((tsigInit, false), ∅), s) hV
          (not_revealed_empty σ) (Finset.notMem_empty σ) hbud
      _ ≤ ((q - C.n.choose (C.t - 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.sub_le_sub_left hC q
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun u _ => ?_) zero_le
    simp [restOf]

set_option maxRecDepth 100000 in
/-- Over all values of the key `σ`, its first hits with distinct keys cost at most `q - C(n, t - 1)`. -/
theorem core_sum (A : TsigAdversary C) (q : ℕ) (hq : HasSigningQueryBound prims (tsigGame A) q) (x : Keys3 C)
    (σ : KeySlot C) :
    ∑ u : HashOutput, Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2 |
      (fun r => (xk x σ u, r)) <$> runSigningWorld prims (ffAfter A (xk x σ u))] ≤
        ((q - C.n.choose (C.t - 1) : ℕ) : ℝ≥0∞) := by
  classical
  obtain ⟨V, hVdef⟩ : ∃ V : Finset HashOutput, V = Finset.univ.filter fun u =>
      KeyCollision (xk x σ u).2.1 (xk x σ u).2.2 := ⟨_, rfl⟩
  have hV : ∀ u ∉ V, Function.Injective (slotInput (xk x σ u).2.1 (xk x σ u).2.2) := fun u hu => by
    have h : ¬KeyCollision (xk x σ u).2.1 (xk x σ u).2.2 := fun h => hu (by rw [hVdef]; simpa using h)
    simp only [KeyCollision, not_or, not_not] at h
    exact slotInput_injective h.1 h.2
  have hterm : ∀ u, Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ σ ∈ z.2.1.2 |
      (fun r => (xk x σ u, r)) <$> runSigningWorld prims (ffAfter A (xk x σ u))] =
        if u ∈ V then 0 else Pr[fun w => σ ∈ w.1.2 | dealerSlot (C := C) x.1 >>= restOf prims A (xk x σ u)] := by
    intro u
    rw [probEvent_map]
    split_ifs with hu
    · refine probEvent_eq_zero fun r _ h => h.1 ?_
      rw [hVdef] at hu
      simpa using hu
    · have hc : ¬KeyCollision (xk x σ u).2.1 (xk x σ u).2.2 := fun h => hu (by rw [hVdef]; simpa using h)
      simp only [Function.comp_def, hc, not_false_eq_true, true_and]
      rw [runSigningWorld_eq_split prims _ _ (hV u hu), probEvent_map, split_ffAfter prims A _ (hV u hu)]
      rfl
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, ← Finset.sdiff_eq_filter]
  rcases (Finset.univ \ V).eq_empty_or_nonempty with he | ⟨u₀, hu₀⟩
  · rw [he, Finset.sum_empty]; exact zero_le
  have hu₀' : u₀ ∉ V := (Finset.mem_sdiff.mp hu₀).2
  simp only [probEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  calc ∑' os, ∑ u ∈ Finset.univ \ V, Pr[= os | dealerSlot (C := C) x.1] *
        Pr[fun w => σ ∈ w.1.2 | restOf prims A (xk x σ u) os]
      = ∑' os, Pr[= os | dealerSlot (C := C) x.1] *
          ∑ u ∈ Finset.univ \ V, Pr[fun w => σ ∈ w.1.2 | restOf prims A (xk x σ u) os] :=
        tsum_congr fun os => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑' os, Pr[= os | dealerSlot (C := C) x.1] * ((q - C.n.choose (C.t - 1) : ℕ) : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum fun os => by
          by_cases hos : os ∈ support (dealerSlot (C := C) x.1)
          · exact mul_le_mul_right (rest_sum_le prims A q hq x σ V hV u₀ hu₀' os hos) _
          · simp [probOutput_eq_zero_of_not_mem_support hos]
    _ ≤ ((q - C.n.choose (C.t - 1) : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem keyHitBound : KeyHitBound prims C := by
  intro A q hq σ
  have e : ffRun prims A = (do
      let P ← $ᵗ PublicParameter
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pk ← $ᵗ (C.Pair → HashOutput)
      (fun r => ((P, seeds, pk), r)) <$> runSigningWorld prims (ffAfter A (P, seeds, pk))) := by
    rw [bind_keyGen3]
    rfl
  rw [e, ← card_hashOutput]
  rcases σ with T | p
  · refine probEvent_bind_le_of_forall_le fun P _ => ?_
    refine probEvent_resample T _ _ _ fun g => sum_tsum_bind_le _ _ _ fun pk => ?_
    exact core_sum prims A q hq (P, g, pk) (.inl T)
  · refine probEvent_bind_le_of_forall_le fun P _ => probEvent_bind_le_of_forall_le fun seeds _ => ?_
    refine probEvent_resample p _ _ _ fun g => ?_
    exact core_sum prims A q hq (P, seeds, g) (.inr p)

end SeedHitProof

open SeedHitProof in
/-- `SeedHitBound`: a call of the forger on a hidden key costs `seedHitError`. -/
theorem seedHitBound (prims : Primitives) (C : Committee) : SeedHitBound prims C :=
  seedHitBound_of_stages prims (dealerBudget prims) (distinctFlagBound_of_keyHit prims (keyHitBound prims))

/-- info: 'ThresholdLeanXmssSecurity.seedHitBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedHitBound

end ThresholdLeanXmssSecurity
