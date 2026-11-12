import ThresholdLeanXmssSecurity.Proof.Gadgets
import VCVio.OracleComp.QueryTracking.LoggingOracle
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.CharP.Algebra

/-!
# The check

`MultVerifyCompletenessStatement` follows from the honest run of the check. `MultVerifyStatement`
(GS20, Lemmas 8 to 11, and CGH+18) reduces to its distance half `MultVerifyDistance`.
`canonicalCheckSimulator_queryBound` gives the query half. The supporting lemmas concern
the executions and estimates of `MultVerifyDistance`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

/-! ## Completeness, the ideal side and the reduction -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

theorem getElem?_vector {R : Type} (c : ℕ) (f : ℕ → R) {g : ℕ} (hg : g < c) :
    (vector c f)[g]? = some (f g) := by
  simp [vector, hg]

omit [Fintype E] [DecidableEq E] in
/-- On valid correct tuples with no corrupt operator, `F_multVerify` accepts at every operator. -/
theorem fmultVerify_honest (K : Constants C E) (counts : List ℕ) (x : C.Party → List (Tuple C))
    (hx : TupleInputs K counts noCoalition x ∧ CorrectTuples x) :
    simulateQ (replyImpl (C := C) (fun _ => (Finset.univ : Finset C.Party)))
      ((FmultVerify (C := C)).run noCoalition fun i => some (x i)) = pure fun _ => some () := by
  obtain ⟨⟨hcount, -, hcons⟩, hcorrect⟩ := hx
  have hF : (firstInput fun i => some (x i)).map (·.count) = counts ∨ firstInput (fun i => some (x i)) = [] := by
    rcases firstInput_some x with h | ⟨p, h⟩
    · exact Or.inr h
    · exact Or.inl (h ▸ hcount p (by simp [noCoalition]))
  simp [FmultVerify, leak, replyImpl]
  erw [QueryImpl.add_apply_inr]
  rw [map_pure]
  refine congrArg (pure (f := OracleComp (LocalSpec C))) (funext fun i => ?_)
  rw [if_pos]
  refine ⟨⟨?_, ?_⟩, Finset.mem_univ _⟩
  · intro k hk a b i hi j hj g hg
    have hFk : (firstInput fun i => some (x i))[k]?.map (·.count) = counts[k]? := by
      rcases hF with h | h
      · rw [← h, List.getElem?_map]
      · simp [h] at hk
    have hk' : k < counts.length := by
      rcases hF with h | h
      · rw [← h, List.length_map]; exact hk
      · simp [h] at hk
    have hlen : ∀ i, k < (x i).length := fun i => by
      rw [← List.length_map (f := (·.count)), hcount i (by simp [noCoalition])]; exact hk'
    have hc : ∀ i, ((x i)[k]'(hlen i)).count = counts[k] := fun i => by
      have := congrArg (·[k]?) (hcount i (by simp [noCoalition]))
      simp only [List.getElem?_map, List.getElem?_eq_getElem (hlen i), List.getElem?_eq_getElem hk',
        Option.map_some, Option.some.injEq] at this
      exact this
    have hg' : g < counts[k] := by
      simp only [List.getElem?_range hk, Option.map_some, Option.getD_some] at hg
      have : (tupleAt (fun i => some (x i)) k).count = counts[k] := by
        simp only [tupleAt, hFk, List.getElem?_eq_getElem hk', Option.getD_some]
      omega
    have hprem : ConsistentAt noCoalition (fun i T => (x i).map fun τ => vector τ.count fun g =>
        if ∃ j ∈ (noCoalition (C := C)).1, filler K τ.mode T g = some j then τ.z T g else 0) ⟨a, b⟩ := by
      intro i _ j _ _ _
      have h0 : ∀ i, (x i).map (fun τ => vector τ.count fun g =>
          if ∃ j ∈ (noCoalition (C := C)).1, filler K τ.mode ⟨a, b⟩ g = some j then τ.z ⟨a, b⟩ g else 0) =
            counts.map (fun c => vector c fun _ => (0 : Bit)) := fun i => by
        rw [← hcount i (by simp [noCoalition]), List.map_map]
        simp [noCoalition, Function.comp_def]
      exact (h0 i).trans (h0 j).symm
    have h := congrArg (·[k]?) (hcons ⟨a, b⟩ hprem i hi j hj (by simp [noCoalition]) (by simp [noCoalition]))
    simp only [List.getElem?_map, List.getElem?_eq_getElem (hlen i), List.getElem?_eq_getElem (hlen j),
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [List.getElem?_eq_getElem (hlen i), List.getElem?_eq_getElem (hlen j)]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    have e := fun (f : Tuple C → C.Term → ℕ → Bit) (h : vector ((x i)[k]'(hlen i)).count (f ((x i)[k]'(hlen i)) ⟨a, b⟩) =
        vector ((x j)[k]'(hlen j)).count (f ((x j)[k]'(hlen j)) ⟨a, b⟩)) => by
      have := congrArg (·[g]?) h
      rwa [getElem?_vector _ _ (hc i ▸ hg'), getElem?_vector _ _ (hc j ▸ hg'), Option.some.injEq] at this
    exact ⟨e (·.x) h1, e (·.y) h2, e (·.z) h3⟩
  · exact hcorrect

/-- A distribution is within its probability of missing `a` of the point `a`. -/
theorem tvDist_pure_le {α : Type} (mx : ProbComp α) (a : α) :
    tvDist mx (pure a) ≤ Pr[(· ≠ a) | mx].toReal := by
  have h2 : 𝒟[(mx >>= fun _ => pure a)] = 𝒟[(pure a : ProbComp α)] :=
    evalDist_ext fun y => by rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
  have hR : tvDist mx (pure a) = tvDist (mx >>= pure) (mx >>= fun _ => pure a) := by
    unfold tvDist
    rw [h2, bind_pure]
  rw [hR]
  exact tvDist_bind_left_event_le mx pure (fun _ => pure a) (· ≠ a) fun b hb => by
    rw [not_not] at hb
    rw [hb]

omit [DecidableEq E] in
/-- `MultVerifyCompletenessStatement` follows from the bound on the aborts of the honest network. -/
theorem multVerifyCompleteness_of_abort_bound (prims : Primitives) (K : Constants C E)
    [SampleableType E]
    (h : ∀ (counts : List ℕ) (x : C.Party → List (Tuple C)),
      TupleInputs K counts noCoalition x ∧ CorrectTuples x →
      Pr[(· ≠ fun _ => some ()) | (simulateQ (localAnswer prims)
          (honestStart (fun i => checkProtocol K i (x i)) >>=
            honestRounds (checkFunctionalities K) checkReply (checkRounds counts.sum))).run' ∅].toReal ≤
        abortErrorOf (E := E) (halvings counts.sum)) :
    MultVerifyCompletenessStatement prims K := by
  intro counts
  rw [completes_iff]
  intro x hx
  rw [fmultVerify_honest K counts x hx, simulateQ_pure]
  refine (tvDist_pure_le _ _).trans ?_
  convert h counts x hx using 3

end

end ThresholdLeanXmssSecurity

/-! ## Lockstep steps of the honest network -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} {I O L R α : Type}

/-- Every operator calls the functionality in the same step. -/
theorem honestRounds_call [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (input : C.Party → I) (f : (i : C.Party) → Option O → PartyM C E (CallSpec I O) α) :
    honestStart (fun i => call (input i) >>= f i) >>= honestRounds F reply (fuel + 1) =
      honestFunctionality F reply (fun i => some (input i)) >>= fun outputs =>
        honestStart (fun i => f i (outputs i)) >>= honestRounds F reply fuel := by
  have hstart : honestStart (fun i => call (input i) >>= f i) =
      pure fun i => (Step.call (input i) fun r => (f i r).run : Step C E (CallSpec I O) α) := by
    unfold honestStart
    simp only [advance_call_bind]
    exact sequenceFin_pure _
  rw [hstart, pure_bind, honestRounds_succ]
  · unfold honestStep
    rw [if_pos ⟨⟨Classical.arbitrary _, rfl⟩, fun _ => Or.inl rfl⟩, bind_assoc]
    rfl
  · exact fun h => h (Classical.arbitrary _)

/-- Every operator exchanges in the same round, and no message is an abort frame. -/
theorem honestRounds_exchange (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (outbox : C.Party → Mail C E) (f : C.Party → Mail C E → PartyM C E (CallSpec I O) α)
    [Nonempty C.Party] (habort : ∀ k j, Msg.isAbort (outbox k j) = false) :
    honestStart (fun i => exchange (outbox i) >>= f i) >>= honestRounds F reply (fuel + 1) =
      honestStart (fun j => f j fun k => outbox k j) >>= honestRounds F reply fuel := by
  have hstart : honestStart (fun i => exchange (outbox i) >>= f i) =
      pure fun i => (Step.wait (outbox i) (exchangeResume (f i)) : Step C E (CallSpec I O) α) := by
    unfold honestStart
    simp only [advance_exchange_bind]
    exact sequenceFin_pure _
  rw [hstart, pure_bind, honestRounds_succ]
  · rw [honestStep_exchange]
    unfold honestStart
    congr 2
    funext j
    rw [exchangeResume_of_no_abort _ _ fun k => habort k j]
  · exact fun h => h (Classical.arbitrary _)

/-- Every operator outputs. -/
theorem honestRounds_pure (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (a : C.Party → α) :
    honestStart (fun i => (pure (a i) : PartyM C E (CallSpec I O) α)) >>= honestRounds F reply fuel =
      pure fun i => some (a i) := by
  have hstart : honestStart (fun i => (pure (a i) : PartyM C E (CallSpec I O) α)) =
      pure fun i => (Step.done (some (a i)) : Step C E (CallSpec I O) α) := by
    unfold honestStart
    simp only [advance_run_pure]
    exact sequenceFin_pure _
  rw [hstart, pure_bind, honestRounds_done]
  · rfl
  · exact fun _ => trivial

end

end ThresholdLeanXmssSecurity

/-! ## The coins of the check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal

noncomputable section

def bitsEquiv (n : ℕ) : BitVec n ≃ (Fin n → Bool) where
  toFun h i := h.getLsbD i
  invFun f := (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
  left_inv h := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn]
    simp [hi]
  right_inv f := by
    funext i
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn]
    simp [i.isLt]

def boolBit : Bool ≃ Bit where
  toFun b := if b then 1 else 0
  invFun x := x = 1
  left_inv b := by cases b <;> decide
  right_inv x := by fin_cases x <;> decide

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E]

/-- A hash output splits into the element of its first bits and its other bits. -/
def hashSplit (K : Constants C E) : HashOutput ≃ E × (Fin 64 → Bool) :=
  (bitsEquiv 256).trans <| ((finSumFinEquiv (m := elementBits) (n := 64)).symm.arrowCongr (Equiv.refl Bool)).trans <|
    (Equiv.sumArrowEquivProdArrow _ _ _).trans <|
      Equiv.prodCongr ((Equiv.arrowCongr (Equiv.refl _) boolBit).trans K.encode.symm) (Equiv.refl _)

theorem hashSplit_fst (K : Constants C E) (h : HashOutput) : (hashSplit K h).1 = elementOfHash K h := by
  rfl

theorem card_field (K : Constants C E) : Fintype.card E = 2 ^ elementBits := by
  rw [Fintype.card_congr K.encode]; simp [ZMod.card]

/-- The element of a uniform hash output is uniform. -/
theorem probEvent_elementOfHash (K : Constants C E) (p : E → Prop) [DecidablePred p] :
    Pr[p | elementOfHash K <$> ($ᵗ HashOutput)] = (Finset.univ.filter p).card / Fintype.card E := by
  classical
  rw [probEvent_map, probEvent_uniformSample]
  have hcard : (Finset.univ.filter (p ∘ elementOfHash K)).card = (Finset.univ.filter p).card * 2 ^ 64 := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype,
      Fintype.card_congr ((hashSplit K).subtypeEquiv (p := fun h => (p ∘ elementOfHash K) h)
        (q := fun z => p z.1) fun h => by simp [Function.comp, hashSplit_fst]),
      Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := p))]
    simp
  have hH : Fintype.card HashOutput = Fintype.card E * 2 ^ 64 := by
    rw [card_field K, Fintype.card_congr (bitsEquiv hashOutputBits), Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; norm_num [elementBits, hashOutputBits]
  rw [hcard, hH]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

variable (prims : Primitives)

theorem card_zero_one [DecidableEq E] :
    (Finset.univ.filter fun e : E => ¬ (e ≠ 0 ∧ e ≠ 1)).card = 2 := by
  have : (Finset.univ.filter fun e : E => ¬ (e ≠ 0 ∧ e ≠ 1)) = {0, 1} := by
    ext e; simp [or_iff_not_imp_left]
  rw [this, Finset.card_pair zero_ne_one]

/-- A challenge search on a key with no cached expansion fails with probability `(2 / |E|) ^ tries`. -/
theorem probEvent_findChallenge_none [DecidableEq E] (K : Constants C E) (key : HashOutput) :
    ∀ (tries index : ℕ) (s : HashCache C), (∀ i ≥ index, s (.expand key i) = none) →
      Pr[fun z => z.1 = none | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key tries index)).run s] ≤ (2 / Fintype.card E) ^ tries := by
  classical
  intro tries
  induction tries with
  | zero => intro index s _; simp [findChallenge]
  | succ tries ih =>
    intro index s hs
    have hq : ¬ IsFixed (C := C) (.expand key index) := by rintro ⟨_, h, _⟩; cases h
    have hrun : (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (hashQuery (.expand key index))).run s =
        (fun u => (u, s.cacheQuery (.expand key index) u)) <$> ($ᵗ HashOutput) := by
      have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
          (hashQuery (.expand key index)) = hashAnswer prims (.expand key index) :=
        (simulateQ_query _ _).trans (id_map _)
      rw [h1, hashAnswer_of_not_isFixed prims hq, OracleSpec.randomOracle,
        QueryImpl.withCaching_run_none _ (hs index le_rfl)]
      rfl
    have h2 : (2 : ℝ≥0∞) / Fintype.card E = Pr[fun e => ¬ (e ≠ 0 ∧ e ≠ 1) | elementOfHash K <$> ($ᵗ HashOutput)] := by
      rw [probEvent_elementOfHash, card_zero_one]; norm_cast
    rw [findChallenge, simulateQ_bind, StateT.run_bind, hrun, bind_map_left, pow_succ']
    nth_rewrite 1 [h2]
    rw [probEvent_map]
    refine probEvent_bind_le_mul fun u _ => ?_
    dsimp only
    split
    · simp
    · rename_i h _
      rw [if_pos (by simpa using h)]
      refine ih (index + 1) _ fun i hi => ?_
      rw [QueryCache.cacheQuery, Function.update_of_ne (by simp; omega)]
      exact hs i (by omega)

theorem simulateQ_hashQuery_run_fresh {q : Query C} (hq : ¬ IsFixed q) {s : HashCache C} (hs : s q = none) :
    (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q)).run s =
      (fun u => (u, s.cacheQuery q u)) <$> ($ᵗ HashOutput) := by
  have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q) = hashAnswer prims q :=
    (simulateQ_query _ _).trans (id_map _)
  rw [h1, hashAnswer_of_not_isFixed prims hq, OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs]
  rfl

/-- The first `m` values of an expansion of a key with no cached expansion are all nonzero, except with
probability `m / |E|`. -/
theorem probEvent_expand_zero [DecidableEq E] (K : Constants C E) (key : HashOutput) :
    ∀ (count index m : ℕ) (s : HashCache C), m ≤ count → (∀ i ≥ index, s (.expand key i) = none) →
      Pr[fun z => ¬ ∀ b < m, z.1.getD b 0 ≠ 0 | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        ((List.range' index count).mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run s] ≤
        m / Fintype.card E := by
  intro count
  induction count with
  | zero => intro index m s hm _; simp [show m = 0 by omega]
  | succ count ih =>
    intro index m s hm hs
    have hq : ¬ IsFixed (C := C) (.expand key index) := by rintro ⟨_, h, _⟩; cases h
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    simp only [List.range'_succ, List.mapM_cons, simulateQ_bind, simulateQ_map, StateT.run_bind,
      StateT.run_map, simulateQ_hashQuery_run_fresh prims hq (hs index le_rfl)]
    rw [Functor.map_map, bind_map_left]
    have hsplit : (m : ℝ≥0∞) / Fintype.card E = 1 / Fintype.card E + ((m - 1 : ℕ) : ℝ≥0∞) / Fintype.card E := by
      rw [ENNReal.div_add_div_same]; congr 1; norm_cast; omega
    rw [hsplit]
    refine probEvent_bind_le_add (p := fun u => elementOfHash K u ≠ 0) ?_ fun u _ hu => ?_
    · have := probEvent_elementOfHash K (fun e => e = 0)
      rw [probEvent_map] at this
      simp only [not_not]
      convert this.le using 2
      all_goals try rfl
      · have : (Finset.univ.filter fun e : E => e = 0) = {0} := by ext; simp
        rw [this]; simp
    · simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, probEvent_map]
      refine le_trans (probEvent_mono fun z _ hz => ?_) (ih (index + 1) (m - 1) _ (by omega) fun i hi => ?_)
      · simp only [Function.comp_apply] at hz
        refine fun hall => hz fun b hb => ?_
        rcases b with _ | b
        · simpa using hu
        · simpa using hall b (by omega)
      · rw [QueryCache.cacheQuery, Function.update_of_ne (by simp; omega)]
        exact hs i (by omega)

/-- A fresh query of `H` lands in a set of `S` hash outputs with probability `|S| / 2 ^ 256`. -/
theorem probEvent_hash_fresh_mem {q : Query C} (hq : ¬ IsFixed q) {s : HashCache C} (hs : s q = none)
    (S : Finset HashOutput) :
    Pr[fun z => z.1 ∈ S | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q)).run s] ≤
      S.card / 2 ^ 256 := by
  classical
  rw [simulateQ_hashQuery_run_fresh prims hq hs, probEvent_map, probEvent_uniformSample]
  have hH : Fintype.card HashOutput = 2 ^ 256 := by
    rw [Fintype.card_congr (bitsEquiv hashOutputBits), Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; rfl
  rw [hH, Nat.cast_pow, Nat.cast_ofNat]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast Finset.card_le_card fun u hu => by simpa using hu

/-- A repeated query of `H` or `PRG` returns the first answer. -/
theorem roAnswer_dup (t : (RoSpec C).Domain) {γ : Type}
    (f : (RoSpec C).Range t → (RoSpec C).Range t → StateT (HashCache C) ProbComp γ) :
    ((hashAnswer (C := C) prims + prgAnswer (C := C) prims) t >>= fun a =>
        (hashAnswer (C := C) prims + prgAnswer (C := C) prims) t >>= fun b => f a b) =
      (hashAnswer (C := C) prims + prgAnswer (C := C) prims) t >>= fun a => f a a := by
  rcases t with q | x
  · exact hashAnswer_dup prims q f
  · change (prgAnswer prims x >>= fun a => prgAnswer prims x >>= fun b => f a b) =
      prgAnswer prims x >>= fun a => f a a
    simp only [prgAnswer, bind_assoc, pure_bind]
    exact hashAnswer_dup prims _ fun d d' => f _ _

theorem simulateQ_localAnswer_query_ro (t : (RoSpec C).Domain) :
    simulateQ (localAnswer (C := C) prims) (liftComp ((liftM (OracleSpec.query t) : OracleComp (RoSpec C) _)) (LocalSpec C)) =
      (hashAnswer (C := C) prims + prgAnswer (C := C) prims) t := by
  rw [simulateQ_localAnswer_liftComp]
  exact (simulateQ_query _ _).trans (id_map _)

theorem sameRun_query_dup (t : (RoSpec C).Domain) {γ : Type}
    (k : (RoSpec C).Range t → (RoSpec C).Range t → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (liftComp ((liftM (OracleSpec.query t) : OracleComp (RoSpec C) _)) (LocalSpec C) >>= fun a =>
        liftComp ((liftM (OracleSpec.query t) : OracleComp (RoSpec C) _)) (LocalSpec C) >>= fun b => k a b)
      (liftComp ((liftM (OracleSpec.query t) : OracleComp (RoSpec C) _)) (LocalSpec C) >>= fun a => k a a) := fun s => by
  simp only [simulateQ_bind, simulateQ_localAnswer_query_ro]
  rw [roAnswer_dup]

/-- A computation of `H` and `PRG` that runs twice returns the first results. -/
theorem sameRun_ro_dup {α γ : Type} (oa : OracleComp (RoSpec C) α) (k : α → α → OracleComp (LocalSpec C) γ) :
    SameRun prims (liftComp oa (LocalSpec C) >>= fun a => liftComp oa (LocalSpec C) >>= fun b => k a b)
      (liftComp oa (LocalSpec C) >>= fun a => k a a) := by
  induction oa using OracleComp.inductionOn generalizing γ with
  | pure a => simp only [liftComp_pure, pure_bind]; exact SameRun.refl _ _
  | query_bind t cont ih =>
    simp only [liftComp_bind, bind_assoc]
    set Q := ((liftM (OracleSpec.query t) : OracleComp (RoSpec C) _)).liftComp (LocalSpec C)
    have h1 : ∀ u, SameRun prims
        ((cont u).liftComp (LocalSpec C) >>= fun a => Q >>= fun x => (cont x).liftComp (LocalSpec C) >>= fun b => k a b)
        (Q >>= fun x => (cont u).liftComp (LocalSpec C) >>= fun a => (cont x).liftComp (LocalSpec C) >>= fun b => k a b) :=
      fun u => sameRun_swap prims _ Q _
    refine (SameRun.bind_right Q h1).trans ?_
    refine (sameRun_query_dup prims t fun u x =>
      (cont u).liftComp (LocalSpec C) >>= fun a => (cont x).liftComp (LocalSpec C) >>= fun b => k a b).trans ?_
    exact SameRun.bind_right Q fun u => ih u k

/-- Every operator runs the same computation of `H` and `PRG`, which runs once. -/
theorem sameRun_sequenceFin_const {β : Type} (oa : OracleComp (RoSpec C) β) :
    ∀ n : ℕ, SameRun prims (Concrete.sequenceFin fun _ : Fin (n + 1) => liftComp oa (LocalSpec C))
      (liftComp oa (LocalSpec C) >>= fun b => pure fun _ => b)
  | 0 => by
    simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
    refine SameRun.bind_right _ fun b => SameRun.of_eq ?_
    congr 1; funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => exact i.elim0
  | n + 1 => by
    rw [Concrete.sequenceFin]
    refine (SameRun.bind_right _ fun b => (sameRun_sequenceFin_const oa n).bind fun _ => SameRun.refl _ _).trans ?_
    simp only [bind_assoc, pure_bind]
    have hd := sameRun_ro_dup prims oa fun a b =>
      (pure fun i : Fin (n + 2) => (Fin.cases (motive := fun _ => β) a (fun _ => b) i) : OracleComp (LocalSpec C) _)
    refine SameRun.trans (SameRun.of_eq ?_) (hd.trans (SameRun.of_eq ?_))
    · rfl
    · refine bind_congr fun b => ?_
      congr 1; funext i; cases i using Fin.cases <;> rfl

/-- Every operator runs the same computation of `H` and `PRG` and then its own continuation. The
computation runs once. -/
theorem sameRun_sequenceFin_common {β γ : Type} {n : ℕ} (oa : OracleComp (RoSpec C) β)
    (B : Fin (n + 1) → β → OracleComp (LocalSpec C) γ) :
    SameRun prims (Concrete.sequenceFin fun j => liftComp oa (LocalSpec C) >>= B j)
      (liftComp oa (LocalSpec C) >>= fun b => Concrete.sequenceFin fun j => B j b) := by
  have h := sameRun_sequenceFin_dep prims (fun _ : Fin (n + 1) => liftComp oa (LocalSpec C)) B (fun _ _ v => v)
  simp only [bind_pure] at h
  refine h.trans ?_
  refine ((sameRun_sequenceFin_const prims oa n).bind fun x => SameRun.refl _ _).trans (SameRun.of_eq ?_)
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  exact bind_pure _

/-- A challenge on a fresh coin key fails with probability at most `|Ks| / 2 ^ 256 + (2 / |E|) ^ tries`,
when the cache holds expansions only of the keys in `Ks`. The first term is a key that collides with
an earlier key. -/
theorem probEvent_challenge_none [DecidableEq E] (K : Constants C E) {q : Query C} (hq : ¬ IsFixed q)
    (hq' : ∀ k i, q ≠ .expand k i)
    {s : HashCache C} (hs : s q = none) (Ks : Finset HashOutput)
    (hexpand : ∀ k i, s (.expand k i) ≠ none → k ∈ Ks) :
    Pr[fun z => z.1 = none | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (hashQuery q >>= fun key => findChallenge K key challengeTries 0)).run s] ≤
      Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries := by
  rw [simulateQ_bind, StateT.run_bind]
  have hev : ∀ mx : ProbComp (Option E × HashCache C),
      Pr[fun z => z.1 = none | mx] = Pr[fun z => ¬ (z.1 ≠ none) | mx] := fun mx => by simp
  rw [hev]
  refine probEvent_bind_le_add (p := fun z : HashOutput × HashCache C => z.1 ∉ Ks) ?_ fun z hz hkey => ?_
  · simp only [not_not]
    exact probEvent_hash_fresh_mem prims hq hs Ks
  · rw [← hev]
    refine probEvent_findChallenge_none prims K z.1 challengeTries 0 z.2 fun i _ => ?_
    by_contra hne
    have hz' := simulateQ_hashQuery_run_fresh prims hq hs ▸ hz
    rw [support_map] at hz'
    obtain ⟨u, -, rfl⟩ := hz'
    by_cases hqi : (Query.expand u i : Query C) = q
    · exact (hq' u i hqi.symm).elim
    · dsimp only at hne hkey
      unfold QueryCache.cacheQuery at hne; rw [Function.update_of_ne hqi] at hne
      exact hkey (hexpand u i hne)

end

end ThresholdLeanXmssSecurity

/-! ## Steps of the honest network with a bound -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal

noncomputable section

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

theorem sameRun_sequenceFin_common_pos {β γ : Type} : ∀ {n : ℕ} (_ : 0 < n) (oa : OracleComp (RoSpec C) β)
    (B : Fin n → β → OracleComp (LocalSpec C) γ),
    SameRun prims (Concrete.sequenceFin fun j => liftComp oa (LocalSpec C) >>= B j)
      (liftComp oa (LocalSpec C) >>= fun b => Concrete.sequenceFin fun j => B j b)
  | _ + 1, _, oa, B => sameRun_sequenceFin_common prims oa B

/-- The honest network after a call of all operators meets an event with probability at most `ε`
when it does so from every answer of the functionality. -/
theorem probEvent_honest_call [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (input : C.Party → I) (f : (i : C.Party) → Option O → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support ((simulateQ (localAnswer prims) (honestFunctionality F reply fun i => some (input i))).run s),
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => f i (z.1 i)) >>= honestRounds F reply fuel)).run' z.2] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => call (input i) >>= f i) >>= honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  rw [honestRounds_call, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  exact probEvent_bind_le_of_forall_le fun z hz => by
    have := h z hz
    rwa [StateT.run'_eq] at this

/-- The honest network after a computation `oa` of `H` and `PRG` that every operator runs. A bad
result of `oa` costs its probability, and each other result costs at most `ε`. -/
theorem probEvent_honest_common [Nonempty C.Party] {β : Type} (F : Functionality C I O L R) (reply : L → R)
    (fuel : ℕ) (oa : OracleComp (RoSpec C) β) (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (bad : β × HashCache C → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support ((simulateQ (localAnswer prims) (liftComp oa (LocalSpec C))).run s), ¬ bad z →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i z.1) >>= honestRounds F reply fuel)).run' z.2] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)).run' s] ≤
      Pr[bad | (simulateQ (localAnswer prims) (liftComp oa (LocalSpec C))).run s] + ε := by
  have hsame : SameRun prims (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)
      (liftComp oa (LocalSpec C) >>= fun b => honestStart (fun i => g i b) >>= honestRounds F reply fuel) := by
    have hstart : SameRun prims (honestStart fun i => oracleStep oa >>= g i)
        (liftComp oa (LocalSpec C) >>= fun b => honestStart fun i => g i b) := by
      unfold honestStart
      simp only [advance_oracleStep_bind]
      exact sameRun_sequenceFin_common_pos prims (Fin.pos (Classical.arbitrary C.Party)) oa _
    refine (hstart.bind fun _ => SameRun.refl _ _).trans (SameRun.of_eq ?_)
    rw [bind_assoc]
  have hrun : Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)).run' s] =
      Pr[event | (simulateQ (localAnswer prims) (liftComp oa (LocalSpec C) >>= fun b =>
        honestStart (fun i => g i b) >>= honestRounds F reply fuel)).run' s] := by
    simp only [StateT.run'_eq, probEvent_def, evalDist_map, hsame s]
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine probEvent_bind_le_probEvent_add fun z hz hbad => ?_
  have := h z hz hbad
  rwa [StateT.run'_eq] at this

end

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss Finset

noncomputable section

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

omit [Fintype E] [DecidableEq E] in
open Polynomial in
/-- The `t` honest shares fix the polynomial, so an accepted opening is its value at `0` (GS20,
Protocol 6, step 2). -/
theorem gs20_openSh_robust (K : Constants C E) (D : C.Coalition) (V : Polynomial E)
    (hV : V.natDegree ≤ C.t - 1) (share : C.Party → E) (honest : ∀ j ∉ D.1, share j = V.eval (K.point j))
    (accepted : ∀ j, share j =
      ∑ l ∈ univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K (K.point j) l * share l) :
    ∑ l ∈ univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * share l = V.eval 0 := by
  set S := univ.filter (fun l : C.Party => l.val < C.t)
  set W := Lagrange.interpolate S K.point share
  have hW : ∀ x, W.eval x = ∑ l ∈ S, lagrangeFirst K x l * share l := fun x => by
    simp only [W, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
      Lagrange.eval_basis_eq_prod, lagrangeFirst]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have ht := C.one_le_t
  have hS : S.card ≤ C.t := by
    calc S.card ≤ (range C.t).card :=
          Finset.card_le_card_of_injOn (fun l => l.val) (fun l hl => by simpa [S] using hl)
            (fun a _ b _ h => Fin.ext h)
      _ = C.t := card_range _
  have hWV : W = V := by
    refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (D.1ᶜ.map K.point) ?_ ?_
    · rw [card_map, card_compl, Fintype.card_fin]
      have hWdeg : W.degree < C.t :=
        (Lagrange.degree_interpolate_lt _ K.point.injective.injOn).trans_le (by exact_mod_cast hS)
      have hVdeg : V.degree < C.t :=
        (degree_le_of_natDegree_le hV).trans_lt (by exact_mod_cast (by omega : C.t - 1 < C.t))
      refine (degree_sub_le _ _).trans_lt ((max_lt hWdeg hVdeg).trans_le ?_)
      have := D.2
      exact_mod_cast (by simp only [Committee.n]; omega : C.t ≤ C.n - D.1.card)
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
      rw [hW, ← accepted, honest j (Finset.mem_compl.mp hj)]
  rw [← hW, hWV]

theorem card_first : (univ.filter fun l : C.Party => l.val < C.t).card = C.t := by
  have ht : C.t ≤ C.n := by have := C.one_le_t; simp only [Committee.n]; omega
  rw [Fin.card_filter_val_lt]
  omega

omit [Fintype E] [DecidableEq E] in
open Polynomial in
/-- The first `t` shares of a polynomial of degree at most `t - 1` give its value at every point. -/
theorem sum_lagrangeFirst_mul_eval (K : Constants C E) (V : Polynomial E) (hV : V.natDegree ≤ C.t - 1)
    (x : E) : ∑ l ∈ univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K x l * V.eval (K.point l) =
      V.eval x := by
  set S := univ.filter (fun l : C.Party => l.val < C.t)
  have ht := C.one_le_t
  have hdeg : V.degree < S.card := by
    rw [card_first]
    exact (degree_le_of_natDegree_le hV).trans_lt (by exact_mod_cast (by omega : C.t - 1 < C.t))
  conv_rhs => rw [Lagrange.eq_interpolate K.point.injective.injOn hdeg]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, Lagrange.eval_basis_eq_prod,
    lagrangeFirst]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

omit [Fintype E] [DecidableEq E] in
/-- `E` has characteristic `2`, since `Bit` maps into it. -/
theorem charP_two : CharP E 2 := charP_of_injective_algebraMap (algebraMap Bit E).injective 2

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A halving step of `check` with no errors keeps the claim `D = ∑ A k B k + ∑ A' k B' k` for the
low halves `A`, `B` and the high halves `A'`, `B'` (GS20, Protocol 14). -/
theorem sum_range_halving_fold [CharP E 2] (A B A' B' : ℕ → E) (n : ℕ) (ρ : E) :
    ∑ k ∈ range n, (A k + ρ * (A k + A' k)) * (B k + ρ * (B k + B' k)) =
      ∑ k ∈ range n, A k * B k +
        (∑ k ∈ range n, A k * B k + ∑ k ∈ range n, A' k * B' k +
          ∑ k ∈ range n, (A k + A' k) * (B k + B' k)) * ρ +
        (∑ k ∈ range n, (A k + A' k) * (B k + B' k)) * ρ ^ 2 := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  simp only [add_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (-(A' k * B' k * ρ)) * two

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A slice step of `check` with no errors keeps the claim `D = t(0) + c t(1)` (Gruen, Section 3). -/
theorem sum_range_slice_fold [CharP E 2] (rest xs ys : ℕ → E) (n : ℕ) (ρ c D : E) (hc : c ≠ 0)
    (hD : D = ∑ k ∈ range n, rest k * xs k * ys k + c * ∑ k ∈ range n, rest k * xs (k + n) * ys (k + n)) :
    (1 + ρ) * ∑ k ∈ range n, rest k * xs k * ys k +
        ρ * ((D + ∑ k ∈ range n, rest k * xs k * ys k) / c) +
        ρ * (1 + ρ) * ∑ k ∈ range n, rest k * (xs k + xs (k + n)) * (ys k + ys (k + n)) =
      ∑ k ∈ range n, rest k * (xs k + ρ * (xs k + xs (k + n))) * (ys k + ρ * (ys k + ys (k + n))) := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  have ht1 : (D + ∑ k ∈ range n, rest k * xs k * ys k) / c = ∑ k ∈ range n, rest k * xs (k + n) * ys (k + n) := by
    rw [div_eq_iff hc, hD]
    linear_combination (∑ k ∈ range n, rest k * xs k * ys k) * two
  rw [ht1]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (ρ * rest k * xs (k + n) * ys (k + n)) * two

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A halving step keeps the low half and pads the high half, so the length shrinks at most by half. -/
theorem halvedLength_le (length : ℕ) : halvedLength length ≤ length ∧ length ≤ 2 * halvedLength length := by
  unfold halvedLength; split_ifs <;> omega

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The inner product of a vector of `length` elements is the inner product of its low halves plus
that of its high halves, which read the padding as zeros. -/
theorem sum_range_padded (A B : ℕ → E) (length : ℕ) :
    let half := halvedLength length
    let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
    ∑ k ∈ range length, A k * B k = ∑ k ∈ range half, A k * B k + ∑ k ∈ range half, hi A k * hi B k := by
  intro half hi
  obtain ⟨h1, h2⟩ := halvedLength_le length
  have hsplit := Finset.sum_range_add (fun k => A k * B k) half (length - half)
  rw [show half + (length - half) = length by omega] at hsplit
  rw [hsplit]
  congr 1
  have hfilter : (range half).filter (fun k => k + half < length) = range (length - half) := by
    ext k; simp only [mem_filter, mem_range]; omega
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hi]
  split_ifs <;> simp [add_comm half k]

end

end ThresholdLeanXmssSecurity

/-! ## The functionalities of the check in an honest run -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

variable {C : Committee}

/-- The reply to the left functionality of a sum. -/
def leftReply {L₁ L₂ R₁ R₂ : Type} [Inhabited R₁] (reply : L₁ ⊕ L₂ → R₁ ⊕ R₂) (l : L₁) : R₁ :=
  match reply (.inl l) with
  | .inl r => r
  | .inr _ => default

/-- The reply to the right functionality of a sum. -/
def rightReply {L₁ L₂ R₁ R₂ : Type} [Inhabited R₂] (reply : L₁ ⊕ L₂ → R₁ ⊕ R₂) (l : L₂) : R₂ :=
  match reply (.inr l) with
  | .inr r => r
  | .inl _ => default

theorem honestFunctionality_sum_inl {I₁ O₁ L₁ R₁ I₂ O₂ L₂ R₂ : Type} [Inhabited R₁] [Inhabited R₂]
    (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂) (reply : L₁ ⊕ L₂ → R₁ ⊕ R₂)
    (inputs : C.Party → I₁) :
    honestFunctionality (F₁.sum F₂) reply (fun i => some (Sum.inl (inputs i))) =
      (fun out i => (out i).map Sum.inl) <$> honestFunctionality F₁ (leftReply reply) fun i => some (inputs i) := by
  simp only [honestFunctionality, Option.isSome_some, implies_true, not_true_eq_false, if_false,
    Functionality.sum, Option.mem_def, Option.some.injEq, forall_eq', Sum.isLeft_inl, Option.bind_some,
    Sum.getLeft?_inl]
  rw [if_pos trivial, simulateQ_map, ← QueryImpl.simulateQ_compose]
  congr 2
  funext t
  rcases t with t | l
  · rfl
  · simp only [QueryImpl.apply_compose]
    erw [QueryImpl.add_apply_inr]
    simp [leak, replyImpl, leftReply]
    erw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr, pure_bind]
    split <;> rename_i h <;> simp [h]

theorem honestFunctionality_sum_inr {I₁ O₁ L₁ R₁ I₂ O₂ L₂ R₂ : Type} [Inhabited R₁] [Inhabited R₂]
    (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂) (reply : L₁ ⊕ L₂ → R₁ ⊕ R₂)
    [Nonempty C.Party] (inputs : C.Party → I₂) :
    honestFunctionality (F₁.sum F₂) reply (fun i => some (Sum.inr (inputs i))) =
      (fun out i => (out i).map Sum.inr) <$> honestFunctionality F₂ (rightReply reply) fun i => some (inputs i) := by
  simp only [honestFunctionality, Option.isSome_some, implies_true, not_true_eq_false, if_false,
    Functionality.sum, Option.mem_def, Option.some.injEq, forall_eq', Sum.isLeft_inr, Sum.isRight_inr, Option.bind_some,
    Sum.getRight?_inr]
  rw [if_neg (fun h => by simpa using h (Classical.arbitrary _)), if_pos trivial, simulateQ_map, ← QueryImpl.simulateQ_compose]
  congr 2
  funext t
  rcases t with t | l
  · rfl
  · simp only [QueryImpl.apply_compose]
    erw [QueryImpl.add_apply_inr]
    simp [leak, replyImpl, rightReply]
    erw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr, pure_bind]
    split <;> rename_i h <;> simp [h]

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

attribute [local instance] inhabitedField

theorem firstInput_const [Nonempty C.Party] {I : Type} [Inhabited I] (a : I) :
    firstInput (C := C) (fun _ => some a) = a := by
  unfold firstInput
  have : C.parties ≠ [] := by
    intro h
    have hp := Fin.pos (Classical.arbitrary C.Party)
    simp only [Committee.parties, List.finRange_eq_nil_iff] at h
    omega
  obtain ⟨p, l, hl⟩ := List.exists_cons_of_ne_nil this
  rw [hl]
  rfl

/-- `F_coin` in an honest run gives the same values to every operator. -/
theorem honestFunctionality_coin [Nonempty C.Party] (K : Constants C E) (count : ℕ) :
    honestFunctionality (checkFunctionalities K) checkReply (fun _ => some (.inl (.inl count))) =
      (fun v (_ : C.Party) => some (Sum.inl (Sum.inl (List.ofFn v)))) <$>
        liftComp ($ᵗ (Fin count → E)) (LocalSpec C) := by
  unfold checkFunctionalities
  rw [honestFunctionality_sum_inl, honestFunctionality_sum_inl]
  simp only [honestFunctionality, Option.isSome_some, implies_true, not_true_eq_false, if_false, Fcoin, sample, leak]
  rw [simulateQ_bind, simulateQ_replyImpl_liftComp_prob]
  have h := firstInput_const (C := C) count
  generalize firstInput (C := C) (fun _ => some count) = N at h ⊢
  subst h
  simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun v => ?_
  simp [replyImpl, leftReply, checkReply, noCoalition]
  erw [QueryImpl.add_apply_inr]
  simp

/-- The additive share of operator `i` of product `g` in `F_extendMult`. -/
def extendMultShare (K : Constants C E) (i : C.Party) (products : List (Product C E)) (g : ℕ) : E :=
  match products[g]? with
  | some p => productShare K (localContext i) p
  | none => 0

theorem lackedTerm_empty : ∃ T, lackedTerm (C := C) ∅ = some T := by
  have ht := C.one_le_t
  let T : C.Term := ⟨Finset.univ.filter fun l : C.Party => l.val < C.t - 1, by
    rw [Fin.card_filter_val_lt]; simp only [Committee.n]; omega⟩
  have hsome : (lackedTerm (C := C) ∅).isSome := by
    unfold lackedTerm
    rw [List.find?_isSome]
    exact ⟨T, by simp [Committee.terms], by simp [KnownTo]⟩
  exact Option.isSome_iff_exists.mp hsome

/-- `F_extendMult` in an honest run gives every operator its held terms of one replicated sharing of
the products. -/
theorem support_extendMult [Nonempty C.Party] (K : Constants C E) (products : C.Party → List (Product C E))
    (z : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)))
    (hz : z ∈ support (honestFunctionality (checkFunctionalities K) checkReply
      (fun i => some (.inl (.inr (products i)))))) :
    ∃ Z : Shares C E, (∀ g < (firstInput fun i => some (products i)).length,
        ∑ T, Z T g = ∑ i, extendMultShare K i (products i) g) ∧
      ∀ i, z i = some (.inl (.inr fun T g =>
        if i ∈ C.holders T ∧ g < (firstInput fun i => some (products i)).length then Z T g else 0)) := by
  unfold checkFunctionalities at hz
  rw [honestFunctionality_sum_inl, honestFunctionality_sum_inr] at hz
  simp only [honestFunctionality, Option.isSome_some, implies_true, not_true_eq_false, if_false,
    FextendMult, Fmult, sample, leak] at hz
  simp only [simulateQ_bind, simulateQ_replyImpl_liftComp_prob] at hz
  erw [simulateQ_query] at hz
  simp only [replyImpl, rightReply, leftReply, checkReply] at hz
  erw [QueryImpl.add_apply_inr] at hz
  simp only [OracleQuery.cont_query, id_map, pure_bind, simulateQ_pure, support_map, Set.mem_image,
    support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz
  obtain ⟨x, ⟨x1, ⟨r, ⟨y, hy, rfl⟩, fresh, -, rfl⟩, rfl⟩, rfl⟩ := hz
  subst hy
  obtain ⟨T₀, hT₀⟩ := lackedTerm_empty (C := C)
  let base : Shares C E := fun T g =>
    if h : g < (firstInput fun i => some (products i)).length then fresh T ⟨g, h⟩ else 0
  refine ⟨fun T g => if T = T₀ then ∑ i, extendMultShare K i (products i) g - ∑ T' ∈ Finset.univ.erase T, base T' g
    else base T g, fun g hg => ?_, fun i => ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T₀)]
    dsimp only
    rw [if_pos rfl, Finset.sum_congr rfl fun T hT => if_neg (Finset.ne_of_mem_erase hT)]
    ring
  · simp only [noCoalition_val, Finset.notMem_empty, false_or, Finset.mem_univ, not_true_eq_false,
      if_false, Option.map_some, hT₀, KnownTo, false_and, exists_false, add_zero, Option.getD_some,
      Option.some.injEq, Finset.filter_true_of_mem, Option.some_inj]
    simp only [id, Finset.mem_univ, not_true_eq_false, if_false, Option.map_some, Option.some.injEq,
      Sum.inl.injEq, Sum.inr.injEq, not_false_eq_true, Pi.zero_apply, add_zero]
    funext T g
    by_cases hT : T = T₀
    · subst hT; simp only [extendMultShare, base]; simp; rfl
    · simp [hT, Ne.symm hT, base]

/-- `F_rand` in an honest run gives every operator its held terms of one replicated sharing. -/
theorem support_frand [Nonempty C.Party] {R : Type} [AddCommGroup R] [SampleableType R] (count : ℕ)
    (z : C.Party → Option (PrssOutput C R))
    (hz : z ∈ support (honestFunctionality (C := C) (Frand R) (fun _ => (0, 0)) (fun _ => some count))) :
    ∃ (r : Shares C R) (Z : C.Party → C.Party → ℕ → R), ∀ i,
      z i = some ((fun T => if i ∈ C.holders T then r T else fun _ => 0, Z i) : PrssOutput C R) := by
  simp only [honestFunctionality, Option.isSome_some, implies_true, not_true_eq_false, if_false,
    Frand, sample, leak] at hz
  simp only [simulateQ_bind, simulateQ_replyImpl_liftComp_prob] at hz
  erw [simulateQ_query] at hz
  simp only [replyImpl] at hz
  erw [QueryImpl.add_apply_inr] at hz
  simp only [OracleQuery.cont_query, id_map, pure_bind, simulateQ_pure, support_map, Set.mem_image,
    support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz
  obtain ⟨x, ⟨y, hy, rfl⟩, fresh, -, freshPair, -, rfl⟩ := hz
  subst hy
  refine ⟨fun T g => if h : g < firstInput (C := C) (fun _ => some count) then fresh T ⟨g, h⟩ else 0,
    fun i j => if h : i = j then fun _ => 0 else fun g =>
      if h' : g < firstInput (C := C) (fun _ => some count) then freshPair (C.pairOf i j h) ⟨g, h'⟩ else 0,
    fun i => ?_⟩
  simp [KnownTo]

theorem honestFunctionality_rand_elements [Nonempty C.Party] (K : Constants C E) (count : ℕ) :
    honestFunctionality (checkFunctionalities K) checkReply (fun _ => some (.inr (.inl count))) =
      (fun out i => (out i).map fun o => Sum.inr (Sum.inl o)) <$>
        honestFunctionality (C := C) (Frand E) (fun _ => (0, 0)) (fun _ => some count) := by
  unfold checkFunctionalities
  rw [honestFunctionality_sum_inr, honestFunctionality_sum_inl]
  have : leftReply (rightReply (checkReply (C := C) (E := E))) = fun _ => (0, 0) := by
    funext l; rfl
  rw [this, Functor.map_map]
  congr 1
  funext out i
  rw [Option.map_map]
  rfl

theorem honestFunctionality_rand_bits [Nonempty C.Party] (K : Constants C E) (count : ℕ) :
    honestFunctionality (checkFunctionalities K) checkReply (fun _ => some (.inr (.inr count))) =
      (fun out i => (out i).map fun o => Sum.inr (Sum.inr o)) <$>
        honestFunctionality (C := C) (Frand Bit) (fun _ => (0, 0)) (fun _ => some count) := by
  unfold checkFunctionalities
  rw [honestFunctionality_sum_inr, honestFunctionality_sum_inr]
  have : rightReply (rightReply (checkReply (C := C) (E := E))) = fun _ => (0, 0) := by
    funext l; rfl
  rw [this, Functor.map_map]
  congr 1
  funext out i
  rw [Option.map_map]
  rfl

end

end ThresholdLeanXmssSecurity

/-! ## The program of one operator in the check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

attribute [local instance] Classical.propDecidable

section CheckProgram

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C) (gadgets : CheckGadgets C E G)

/-- The values of a part of the tuples, as one vector over `E` for each term. -/
def liftedPart (tuples : List (Tuple C)) (part : Tuple C → Shares C Bit) : Shares C E := fun T k =>
  (tuples.flatMap fun τ => vector τ.count fun g => algebraMap Bit E (part τ T g)).getD k 0

/-- The weight `τ^w x^q` of tuple `k` that `x` keeps. -/
def wordWeightOf (τ : List E) (count k : ℕ) : E :=
  coinProduct τ sliceBits (coins count - sliceBits) (wordOf count k) * K.weight (bitOf k)

/-- The claim of the check, as a sharing with the same value at every position. -/
def claimOf (τ : List E) (count : ℕ) (Z : Shares C E) : Shares C E := fun T _ =>
  ∑ k ∈ Finset.range (2 ^ sliceBits * sliceWidth count),
    coinProduct τ 0 sliceBits (sliceOf count k) * wordWeightOf K τ count k * Z T k

/-- One slice step of `check`. -/
def sliceStep (τ : List E) (count : ℕ) :
    Shares C E × Shares C E × E → ℕ → RunM C E G (Shares C E × Shares C E × E) :=
  fun (xs, ys, D) j => do
    let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
    let rest := fun k => coinProduct τ 0 (sliceBits - 1 - j) (k / sliceWidth count)
    let t ← gadgets.extendMult [.replicated (fun T k => rest k * xs T k) ys half,
      .replicated (fun T k => rest k * (xs T k + xs T (k + half))) (fun T k => ys T k + ys T (k + half)) half]
    let r ← challenge K gadgets
    let t₀ := conv K ctx t 0
    let tInf := conv K ctx t 1
    let t₁ := (D + t₀) / τ.getD (sliceBits - 1 - j) 0
    let fold := fun (v : Shares C E) T k => v T k + r * (v T k + v T (k + half))
    pure (fold xs, fold ys, (1 + r) * t₀ + r * t₁ + r * (1 + r) * tInf)

/-- One halving step of `check`. -/
def halvingStep (width : ℕ) : (ℕ → E) × (ℕ → E) × E → ℕ → RunM C E G ((ℕ → E) × (ℕ → E) × E) :=
  fun (A, B, D) j => do
    let length := halvedLength^[j] width
    let half := halvedLength length
    let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
    let sum := fun (v : ℕ → E) k => v k + hi v k
    let p ← gadgets.extendMult [.shamir A B half, .shamir (sum A) (sum B) half]
    let r ← challenge K gadgets
    let fold := fun (v : ℕ → E) k => v k + r * (v k + hi v k)
    pure (fold A, fold B, conv K ctx p 0 + (D + conv K ctx p 1) * r + conv K ctx p 1 * r ^ 2)

/-- The randomization of `check` and its final test. -/
def finalStep : (ℕ → E) × (ℕ → E) × E → RunM C E G Unit := fun (A, B, D) => do
  let w ← gadgets.randElements 2
  let wa := conv K ctx w.1 0
  let wb := conv K ctx w.1 1
  let q ← gadgets.extendMult [.shamir (fun _ => wa) (fun _ => wb) 1,
    .shamir (fun _ => wa + A 0) (fun _ => wb + B 0) 1]
  let q₀ := conv K ctx q 0
  let q₂ := conv K ctx q 1
  let salts ← gadgets.randBits 256
  compareDigests ctx salts.1
  let r ← challenge K gadgets
  let opened ← StateT.lift (openSh K ctx (fun k => match k with
    | 0 => wa + r * (wa + A 0)
    | 1 => wb + r * (wb + B 0)
    | _ => q₀ + (D + q₀ + q₂) * r + q₂ * r ^ 2) 3)
  StateT.lift (require (opened 0 * opened 1 = opened 2))

theorem check_eq (tuples : List (Tuple C)) (h : (tuples.map (·.count)).sum ≠ 0) :
    check K ctx gadgets tuples = (do
      let count := (tuples.map (·.count)).sum
      let τ ← expand K (← coinKey K gadgets) (coins count)
      StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
      let p ← (List.range sliceBits).foldlM (sliceStep K ctx gadgets τ count)
        ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k : Shares C E), liftedPart tuples (·.y),
          conv K ctx (claimOf K τ count (liftedPart tuples (·.z))) 0)
      let p' ← (List.range (halvings count - sliceBits)).foldlM (halvingStep K ctx gadgets (sliceWidth count))
        (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
      finalStep K ctx gadgets p') := by
  simp only [check, if_neg h]
  rfl

end CheckProgram

end

end ThresholdLeanXmssSecurity

/-! ## The gadgets of the check as steps -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

attribute [local instance] Classical.propDecidable

section GadgetSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (i : C.Party)

/-- The running values after `record` of a reshare of `count` products in peer mode. -/
def recordHistory (h : C.Term → List Bit) (z : Shares C E) (count : ℕ) : C.Term → List Bit := fun T =>
  if i ∈ C.holders T then
    h T ++ ((List.range count).filter fun g => (filler K .peer T g).isSome).flatMap ((elementCodec K).toBits ∘ z T)
  else h T

/-- The input of the expansion and challenge search of a coin with the label `ρ`. -/
def challengeQuery (tag ρ : ℕ) (values : List E) : OracleComp (RoSpec C) (Option E) :=
  hashQuery (.coinKey tag ρ (values.flatMap fun v => List.ofFn (K.encode v))) >>= fun key =>
    findChallenge K key challengeTries 0

theorem oracleStep_bind {ι : Type} {G : OracleSpec ι} {α β : Type} (oa : OracleComp (RoSpec C) α)
    (ob : α → OracleComp (RoSpec C) β) :
    (oracleStep (C := C) (E := E) (G := G) (oa >>= ob)) = oracleStep oa >>= fun a => oracleStep (ob a) := by
  simp only [oracleStep, localStep, liftComp_bind]
  apply OptionT.ext
  simp [OptionT.run_bind, OptionT.run_lift]

theorem extendMult_run' {α : Type} (products : List (Product C E)) (f : Shares C E → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((hybridCheckGadgets K i).extendMult products >>= f).run' st =
      call (Sum.inl (Sum.inr products)) >>= fun o => match o with
        | some (.inl (.inr z)) => (f z).run' ⟨recordHistory K i st.history z products.length, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [hybridCheckGadgets, freshLabel, record, bind_assoc]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift, localContext]
  rfl

theorem coin_run' {α : Type} (count : ℕ) (f : List E → RunM C E (CheckSpec C E) α) (st : RunState C) :
    ((hybridCheckGadgets K i).coin count >>= f).run' st =
      call (Sum.inl (Sum.inl count)) >>= fun o => match o with
        | some (.inl (.inl v)) => (f v).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [hybridCheckGadgets, freshLabel, bind_assoc]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift]

theorem randElements_run' {α : Type} (count : ℕ) (f : PrssOutput C E → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((hybridCheckGadgets K i).randElements count >>= f).run' st =
      call (Sum.inr (Sum.inl count)) >>= fun o => match o with
        | some (.inr (.inl w)) => (f w).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [hybridCheckGadgets, freshLabel, bind_assoc]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | (w | w)) <;> simp [StateT.run_lift]

theorem randBits_run' {α : Type} (count : ℕ) (f : PrssOutput C Bit → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((hybridCheckGadgets K i).randBits count >>= f).run' st =
      call (Sum.inr (Sum.inr count)) >>= fun o => match o with
        | some (.inr (.inr w)) => (f w).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [hybridCheckGadgets, freshLabel, bind_assoc]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | (w | w)) <;> simp [StateT.run_lift]

theorem challenge_run' {α : Type} (f : E → RunM C E (CheckSpec C E) α) (st : RunState C) :
    (challenge K (hybridCheckGadgets K i) >>= f).run' st =
      call (Sum.inl (Sum.inl 1)) >>= fun o => match o with
        | some (.inl (.inl v)) => oracleStep (challengeQuery K st.tag st.label v) >>= fun r => match r with
          | some r => (f r).run' ⟨st.history, st.label + 1, st.tag⟩
          | none => failure
        | _ => failure := by
  simp only [challenge, coinKey, bind_assoc, hybridCheckGadgets, freshLabel, challengeQuery, oracleStep_bind]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, StateT.run_get]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift]
  refine bind_congr fun key => bind_congr fun r => ?_
  rcases r with _ | r <;> simp [StateT.run_lift]

end GadgetSteps

end

end ThresholdLeanXmssSecurity

/-! ## Steps of the honest network with own computations -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal

noncomputable section

section NetworkSteps

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- The honest network after an own computation of `H` and `PRG` of each operator. -/
theorem probEvent_honest_local {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : C.Party → OracleComp (RoSpec C) β) (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support ((simulateQ (localAnswer prims)
        (Concrete.sequenceFin fun i => liftComp (oa i) (LocalSpec C))).run s),
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (z.1 i)) >>= honestRounds F reply fuel)).run' z.2] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s] ≤ ε := by
  have hsame : SameRun prims (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)
      ((Concrete.sequenceFin fun i => liftComp (oa i) (LocalSpec C)) >>= fun b =>
        honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel) := by
    have hstart : SameRun prims (honestStart fun i => oracleStep (oa i) >>= g i)
        ((Concrete.sequenceFin fun i => liftComp (oa i) (LocalSpec C)) >>= fun b => honestStart fun i => g i (b i)) := by
      unfold honestStart
      simp only [advance_oracleStep_bind]
      have h := sameRun_sequenceFin_dep prims (fun i => liftComp (oa i) (LocalSpec C))
        (fun i u => advance (g i u).run) (fun _ _ v => v)
      refine (SameRun.of_eq ?_).trans (h.trans (SameRun.of_eq (bind_congr fun x => bind_pure _)))
      simp only [bind_pure]
    refine (hstart.bind fun _ => SameRun.refl _ _).trans (SameRun.of_eq ?_)
    rw [bind_assoc]
  have hrun : Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s] =
      Pr[event | (simulateQ (localAnswer prims) ((Concrete.sequenceFin fun i => liftComp (oa i) (LocalSpec C)) >>= fun b =>
        honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel)).run' s] := by
    simp only [StateT.run'_eq, probEvent_def, evalDist_map, hsame s]
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine probEvent_bind_le_of_forall_le fun z hz => ?_
  have := h z hz
  rwa [StateT.run'_eq] at this

theorem require_bind_of {ι : Type} {G : OracleSpec ι} {c : Prop} (hc : c) (f : Unit → PartyM C E G α) :
    require c >>= f = f () := by
  simp [require, hc]

/-- A computation in the local oracles that only samples. -/
def IsLocalProb {β : Type} (oa : OracleComp (LocalSpec C) β) : Prop := ∃ p : ProbComp β, oa = liftComp p _

theorem IsLocalProb.pure {β : Type} (b : β) : IsLocalProb (C := C) (pure b) := ⟨Pure.pure b, by simp⟩

theorem IsLocalProb.liftComp {β : Type} (p : ProbComp β) : IsLocalProb (C := C) (liftComp p _) := ⟨p, rfl⟩

theorem IsLocalProb.bind {β γ : Type} {oa : OracleComp (LocalSpec C) β} {f : β → OracleComp (LocalSpec C) γ}
    (h : IsLocalProb oa) (hf : ∀ b, IsLocalProb (f b)) : IsLocalProb (oa >>= f) := by
  obtain ⟨p, rfl⟩ := h
  choose q hq using hf
  exact ⟨p >>= q, by rw [liftComp_bind]; exact bind_congr hq⟩

theorem IsLocalProb.map {β γ : Type} {oa : OracleComp (LocalSpec C) β} (f : β → γ)
    (h : IsLocalProb oa) : IsLocalProb (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun b => IsLocalProb.pure _

theorem run_liftComp_prob {β : Type} (p : ProbComp β) (s : HashCache C) :
    (simulateQ (localAnswer prims) (liftComp p (LocalSpec C))).run s = (fun b => (b, s)) <$> p := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure b => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    simp only [ih]
    rw [liftComp_query]
    simp [localAnswer, unifFwdImpl]

/-- A computation that only samples keeps the cache. -/
theorem IsLocalProb.support_run {β : Type} {oa : OracleComp (LocalSpec C) β} (h : IsLocalProb oa)
    (s : HashCache C) : ∀ z ∈ support ((simulateQ (localAnswer prims) oa).run s), z.2 = s ∧ z.1 ∈ support oa := by
  obtain ⟨p, rfl⟩ := h
  intro z hz
  rw [run_liftComp_prob, support_map] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  exact ⟨rfl, by rw [support_liftComp]; exact hb⟩

end NetworkSteps

end

end ThresholdLeanXmssSecurity

/-! ## The functionalities of the check keep the cache -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal

noncomputable section

section FunctionalityCache

variable {C : Committee} {L R : Type}

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
  (prims : Primitives)

attribute [local instance] inhabitedField

theorem isLocalProb_frand [Nonempty C.Party] {R : Type} [AddCommGroup R] [SampleableType R] (count : ℕ) :
    IsLocalProb (honestFunctionality (C := C) (Frand R) (fun _ => (0, 0)) (fun _ => some count)) := by
  simp only [honestFunctionality, Option.isSome_some, implies_true, not_true_eq_false, if_false, Frand]
  simp only [simulateQ_bind, simulateQ_replyImpl_leak, simulateQ_replyImpl_sample, pure_bind, simulateQ_pure]
  exact IsLocalProb.bind (IsLocalProb.liftComp _) fun _ => IsLocalProb.bind (IsLocalProb.liftComp _) fun _ =>
    IsLocalProb.pure _

theorem isLocalProb_extendMult [Nonempty C.Party] (K : Constants C E) (products : C.Party → List (Product C E)) :
    IsLocalProb (honestFunctionality (checkFunctionalities K) checkReply
      (fun i => some (.inl (.inr (products i))))) := by
  unfold checkFunctionalities
  rw [honestFunctionality_sum_inl, honestFunctionality_sum_inr]
  refine IsLocalProb.map _ (IsLocalProb.map _ ?_)
  simp only [honestFunctionality, Option.isSome_some, implies_true, not_true_eq_false, if_false,
    FextendMult, Fmult]
  simp only [simulateQ_bind, simulateQ_replyImpl_leak, simulateQ_replyImpl_sample, pure_bind, simulateQ_pure]
  exact IsLocalProb.bind (IsLocalProb.liftComp _) fun _ => IsLocalProb.pure _

theorem firstInput_some_of_nonempty [Nonempty C.Party] {I : Type} [Inhabited I] (x : C.Party → I) :
    ∃ p, firstInput (fun i => some (x i)) = x p := by
  unfold firstInput
  have : C.parties ≠ [] := by
    intro h
    have hp := Fin.pos (Classical.arbitrary C.Party)
    simp only [Committee.parties, List.finRange_eq_nil_iff] at h
    omega
  obtain ⟨p, l, hl⟩ := List.exists_cons_of_ne_nil this
  exact ⟨p, by rw [hl]; rfl⟩

theorem check_coin_support [Nonempty C.Party] (K : Constants C E) (count : ℕ) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestFunctionality (checkFunctionalities K) checkReply
      (fun _ => some (.inl (.inl count))))).run s)) :
    z.2 = s ∧ ∃ v : List E, z.1 = fun _ => some (.inl (.inl v)) := by
  rw [honestFunctionality_coin] at hz
  obtain ⟨h1, h2⟩ := IsLocalProb.support_run prims (IsLocalProb.map _ (IsLocalProb.liftComp _)) s z hz
  refine ⟨h1, ?_⟩
  rw [support_map] at h2
  obtain ⟨v, -, hv⟩ := h2
  exact ⟨List.ofFn v, hv.symm⟩

theorem check_extendMult_support [Nonempty C.Party] (K : Constants C E) (products : C.Party → List (Product C E))
    (n : ℕ) (hlen : ∀ i, (products i).length = n) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestFunctionality (checkFunctionalities K) checkReply
      (fun i => some (.inl (.inr (products i)))))).run s)) :
    z.2 = s ∧ ∃ Z : Shares C E, (∀ g < n, ∑ T, Z T g = ∑ i, extendMultShare K i (products i) g) ∧
      ∀ i, z.1 i = some (.inl (.inr fun T g => if i ∈ C.holders T ∧ g < n then Z T g else 0)) := by
  obtain ⟨h1, h2⟩ := IsLocalProb.support_run prims (isLocalProb_extendMult K products) s z hz
  obtain ⟨p, hp⟩ := firstInput_some_of_nonempty products
  have hn : (firstInput fun i => some (products i)).length = n := by rw [hp, hlen]
  obtain ⟨Z, hZ, hz1⟩ := support_extendMult K products z.1 h2
  rw [hn] at hZ hz1
  exact ⟨h1, Z, hZ, hz1⟩

theorem check_rand_elements_support [Nonempty C.Party] (K : Constants C E) (count : ℕ) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestFunctionality (checkFunctionalities K) checkReply
      (fun _ => some (.inr (.inl count))))).run s)) :
    z.2 = s ∧ ∃ (r : Shares C E) (Zp : C.Party → C.Party → ℕ → E), ∀ i,
      z.1 i = some (.inr (.inl (fun T => if i ∈ C.holders T then r T else fun _ => 0, Zp i))) := by
  rw [honestFunctionality_rand_elements] at hz
  obtain ⟨h1, h2⟩ := IsLocalProb.support_run prims (IsLocalProb.map _ (isLocalProb_frand count)) s z hz
  refine ⟨h1, ?_⟩
  rw [support_map] at h2
  obtain ⟨o, ho, hoz⟩ := h2
  obtain ⟨r, Zp, hr⟩ := support_frand count o ho
  exact ⟨r, Zp, fun i => by rw [← hoz]; simp [hr i]⟩

theorem check_rand_bits_support [Nonempty C.Party] (K : Constants C E) (count : ℕ) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestFunctionality (checkFunctionalities K) checkReply
      (fun _ => some (.inr (.inr count))))).run s)) :
    z.2 = s ∧ ∃ (r : Shares C Bit) (Zp : C.Party → C.Party → ℕ → Bit), ∀ i,
      z.1 i = some (.inr (.inr (fun T => if i ∈ C.holders T then r T else fun _ => 0, Zp i))) := by
  rw [honestFunctionality_rand_bits] at hz
  obtain ⟨h1, h2⟩ := IsLocalProb.support_run prims (IsLocalProb.map _ (isLocalProb_frand count)) s z hz
  refine ⟨h1, ?_⟩
  rw [support_map] at h2
  obtain ⟨o, ho, hoz⟩ := h2
  obtain ⟨r, Zp, hr⟩ := support_frand count o ho
  exact ⟨r, Zp, fun i => by rw [← hoz]; simp [hr i]⟩

end FunctionalityCache

end

end ThresholdLeanXmssSecurity

/-! ## Shamir sharings of the check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss Finset Polynomial

noncomputable section

section Sharings

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The values `f i` are the shares of `v` on one polynomial of degree at most `t - 1`. -/
def IsShamir (f : C.Party → E) (v : E) : Prop :=
  ∃ P : Polynomial E, P.natDegree ≤ C.t - 1 ∧ P.eval 0 = v ∧ ∀ i, f i = P.eval (K.point i)

variable {K}

theorem IsShamir.lin {f g : C.Party → E} {a b : E} (hf : IsShamir K f a) (hg : IsShamir K g b) (c d : E) :
    IsShamir K (fun i => c * f i + d * g i) (c * a + d * b) := by
  obtain ⟨P, hP, hP0, hPi⟩ := hf
  obtain ⟨Q, hQ, hQ0, hQi⟩ := hg
  refine ⟨Polynomial.C c * P + Polynomial.C d * Q, ?_, by simp [hP0, hQ0], fun i => by simp [hPi, hQi]⟩
  exact (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hP) ((natDegree_C_mul_le _ _).trans hQ))

theorem IsShamir.const (c : E) : IsShamir K (fun _ => c) c :=
  ⟨Polynomial.C c, by simp, by simp, fun i => by simp⟩

theorem IsShamir.congr {f g : C.Party → E} {a b : E} (hf : IsShamir K f a) (hfg : ∀ i, f i = g i) (hab : a = b) :
    IsShamir K g b := by
  obtain ⟨P, hP, hP0, hPi⟩ := hf
  exact ⟨P, hP, hab ▸ hP0, fun i => (hfg i) ▸ hPi i⟩

theorem IsShamir.add {f g : C.Party → E} {a b : E} (hf : IsShamir K f a) (hg : IsShamir K g b) :
    IsShamir K (fun i => f i + g i) (a + b) :=
  (hf.lin hg 1 1).congr (fun i => by ring) (by ring)

theorem IsShamir.mul_left {f : C.Party → E} {a : E} (hf : IsShamir K f a) (c : E) :
    IsShamir K (fun i => c * f i) (c * a) :=
  (hf.lin (IsShamir.const 0) c 0).congr (fun i => by ring) (by ring)

theorem IsShamir.div {f : C.Party → E} {a : E} (hf : IsShamir K f a) (c : E) :
    IsShamir K (fun i => f i / c) (a / c) :=
  (hf.mul_left c⁻¹).congr (fun i => by ring) (by ring)

theorem IsShamir.unique {f : C.Party → E} {a b : E} (hf : IsShamir K f a) (hg : IsShamir K f b) : a = b := by
  obtain ⟨P, hP, hP0, hPi⟩ := hf
  obtain ⟨Q, hQ, hQ0, hQi⟩ := hg
  have ht := C.one_le_t
  have hPQ : P = Q := by
    refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (Finset.univ.map K.point) ?_ ?_
    · rw [card_map, card_univ, Fintype.card_fin]
      have hPdeg : P.degree < C.t := (degree_le_of_natDegree_le hP).trans_lt (by exact_mod_cast (by omega : C.t - 1 < C.t))
      have hQdeg : Q.degree < C.t := (degree_le_of_natDegree_le hQ).trans_lt (by exact_mod_cast (by omega : C.t - 1 < C.t))
      refine (degree_sub_le _ _).trans_lt ((max_lt hPdeg hQdeg).trans_le ?_)
      exact_mod_cast (by simp only [Committee.n]; omega : C.t ≤ C.n)
    · intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
      rw [← hPi, ← hQi]
  rw [← hP0, ← hQ0, hPQ]

theorem conv_congr (i : C.Party) (xv X : Shares C E) (k : ℕ) (h : ∀ T, i ∈ C.holders T → xv T k = X T k) :
    conv K (localContext i) xv k = conv K (localContext i) X k := by
  unfold conv
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [h T (by simpa [localContext] using hT)]

theorem isShamir_conv [CharP E 2] (X : Shares C E) (k : ℕ) :
    IsShamir K (fun i => conv K (localContext i) X k) (∑ T, X T k) := by
  obtain ⟨V, hV, hV0, hVi⟩ := cdi05_conv_correct K (fun T => X T k)
  exact ⟨V, hV, hV0, fun i => (hVi i) ▸ rfl⟩

/-- The honest holders of each term have the same running values. -/
def HistAgree (h : C.Party → C.Term → List Bit) : Prop :=
  ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, h i T = h j T

/-- The cache holds expansions only of the keys `Ks`, and coin keys only of labels below `L`. -/
def CacheOK (Ks : Finset HashOutput) (L : ℕ) (s : HashCache C) : Prop :=
  ∀ q, s q ≠ none → (∀ k idx, q = .expand k idx → k ∈ Ks) ∧ (∀ tag ρ v, q = .coinKey tag ρ v → ρ < L)

end Sharings

end

end ThresholdLeanXmssSecurity

/-! ## The coin steps of the check from a cache -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal

noncomputable section

section CoinSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] (prims : Primitives)
  (K : Constants C E)

/-- The input of the expansion of the coins `τ` of the weights, with the label `ρ`. -/
def tauQuery (tag ρ : ℕ) (values : List E) (count : ℕ) : OracleComp (RoSpec C) (List E) :=
  hashQuery (.coinKey tag ρ (values.flatMap fun v => List.ofFn (K.encode v))) >>= fun key =>
    (List.range count).mapM fun k => elementOfHash K <$> hashQuery (.expand key k)

theorem support_hashQuery_entries {q : Query C} (hq : ¬ IsFixed q) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q)).run s)) :
    ∀ q', z.2 q' ≠ none → s q' ≠ none ∨ q' = q := by
  intro q' hq'
  rcases hs : s q with _ | u
  · rw [simulateQ_hashQuery_run_fresh prims hq hs, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    by_cases h : q' = q
    · exact Or.inr h
    · left
      simpa [QueryCache.cacheQuery, Function.update_of_ne h] using hq'
  · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q) = hashAnswer prims q :=
      (simulateQ_query _ _).trans (id_map _)
    rw [h1, hashAnswer_run_cached prims hq hs, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hq'

theorem support_findChallenge_entries (key : HashOutput) :
    ∀ (tries index : ℕ) (s : HashCache C) z,
      z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key tries index)).run s) →
      ∀ q', z.2 q' ≠ none → s q' ≠ none ∨ ∃ i, q' = .expand key i := by
  intro tries
  induction tries with
  | zero =>
    intro index s z hz q' hq'
    simp only [findChallenge, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hq'
  | succ tries ih =>
    intro index s z hz q' hq'
    have hq : ¬ IsFixed (C := C) (.expand key index) := by rintro ⟨_, h, _⟩; cases h
    rw [findChallenge, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, s₁⟩, h₁, hz⟩ := hz
    have hs₁ := support_hashQuery_entries prims hq s _ h₁
    dsimp only at hz
    split at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rcases hs₁ q' hq' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨index, h⟩
    · rcases ih (index + 1) s₁ z hz q' hq' with h | ⟨i, h⟩
      · rcases hs₁ q' h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨index, h⟩
      · exact Or.inr ⟨i + 1 - 1, by simpa using h⟩

theorem support_expand_entries (key : HashOutput) :
    ∀ (L : List ℕ) (s : HashCache C) z,
      z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (L.mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run s) →
      ∀ q', z.2 q' ≠ none → s q' ≠ none ∨ ∃ i, q' = .expand key i := by
  intro L
  induction L with
  | nil =>
    intro s z hz q' hq'
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hq'
  | cons k L ih =>
    intro s z hz q' hq'
    have hq : ¬ IsFixed (C := C) (.expand key k) := by rintro ⟨_, h, _⟩; cases h
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, s₁⟩, h₁, hz⟩ := hz
    rw [simulateQ_map, StateT.run_map, support_map] at h₁
    obtain ⟨⟨u', s₁'⟩, h₁, hu⟩ := h₁
    simp only [Prod.mk.injEq] at hu
    obtain ⟨-, rfl⟩ := hu
    have hs₁ := support_hashQuery_entries prims hq s _ h₁
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨us, s₂⟩, h₂, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rcases ih s₁' _ h₂ q' hq' with h | h
    · rcases hs₁ q' h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨k, h⟩
    · exact Or.inr h

theorem coinKey_fresh {Ks : Finset HashOutput} {L ρ : ℕ} (hρ : L ≤ ρ) {s : HashCache C} (hs : CacheOK Ks L s)
    (tag : ℕ) (bits : List Bit) : s (.coinKey tag ρ bits) = none := by
  by_contra h
  have := (hs _ h).2 tag ρ bits rfl
  omega

/-- A challenge fails with probability at most `|Ks| / 2^256 + (2 / |E|)^tries`. -/
theorem challengeQuery_none_le (tag ρ : ℕ) (v : List E) (Ks : Finset HashOutput) (L : ℕ) (hρ : L ≤ ρ)
    (s : HashCache C) (hs : CacheOK Ks L s) :
    Pr[fun z => z.1 = none | (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag ρ v) (LocalSpec C))).run s] ≤
      Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries := by
  rw [simulateQ_localAnswer_liftComp]
  exact probEvent_challenge_none prims K (by rintro ⟨_, h, _⟩; cases h) (fun k i h => by cases h)
    (coinKey_fresh hρ hs tag _) Ks (fun k i h => (hs _ h).1 k i rfl)

/-- After a challenge, the cache holds expansions of one more key. -/
theorem challengeQuery_cache (tag ρ : ℕ) (v : List E) (Ks : Finset HashOutput) (L : ℕ) (hρ : L ≤ ρ)
    (s : HashCache C) (hs : CacheOK Ks L s) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (liftComp (challengeQuery K tag ρ v) (LocalSpec C))).run s)) :
    ∃ k, CacheOK (insert k Ks) (ρ + 1) z.2 := by
  rw [simulateQ_localAnswer_liftComp, challengeQuery, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨key, s₁⟩, h₁, hz⟩ := hz
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  have hs₁ := support_hashQuery_entries prims hq s _ h₁
  have hs₂ := support_findChallenge_entries prims K key _ _ _ _ hz
  refine ⟨key, fun q hq' => ?_⟩
  rcases hs₂ q hq' with h | ⟨i, rfl⟩
  · rcases hs₁ q h with h | rfl
    · obtain ⟨h1, h2⟩ := hs q h
      exact ⟨fun k idx hk => Finset.mem_insert_of_mem (h1 k idx hk), fun tag' ρ' v' hk => by
        have := h2 tag' ρ' v' hk; omega⟩
    · exact ⟨fun k idx hk => (by cases hk), fun tag' ρ' v' hk => by cases hk; omega⟩
  · exact ⟨fun k idx hk => by cases hk; exact Finset.mem_insert_self _ _, fun tag' ρ' v' hk => by cases hk⟩

/-- The coins `τ` of a fresh key start with `m` nonzero values, except with probability `m / |E|`. -/
theorem tauQuery_zero_le (tag ρ : ℕ) (v : List E) (count m : ℕ) (hm : m ≤ count) (L : ℕ) (hρ : L ≤ ρ)
    (s : HashCache C) (hs : CacheOK ∅ L s) :
    Pr[fun z => ¬ ∀ b < m, z.1.getD b 0 ≠ 0 |
      (simulateQ (localAnswer prims) (liftComp (tauQuery K tag ρ v count) (LocalSpec C))).run s] ≤
      m / Fintype.card E := by
  rw [simulateQ_localAnswer_liftComp, tauQuery, simulateQ_bind, StateT.run_bind]
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  refine probEvent_bind_le_of_forall_le fun z hz => ?_
  rw [List.range_eq_range']
  refine probEvent_expand_zero prims K z.1 count 0 m z.2 hm fun i _ => ?_
  by_contra hne
  rcases support_hashQuery_entries prims hq s z hz _ hne with h | h
  · exact Finset.notMem_empty _ ((hs _ h).1 _ i rfl)
  · cases h

/-- After the coins `τ`, the cache holds expansions of one key. -/
theorem tauQuery_cache (tag ρ : ℕ) (v : List E) (count L : ℕ) (hρ : L ≤ ρ) (s : HashCache C)
    (hs : CacheOK ∅ L s) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (liftComp (tauQuery K tag ρ v count) (LocalSpec C))).run s)) :
    ∃ k, CacheOK {k} (ρ + 1) z.2 := by
  rw [simulateQ_localAnswer_liftComp, tauQuery, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨key, s₁⟩, h₁, hz⟩ := hz
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  have hs₁ := support_hashQuery_entries prims hq s _ h₁
  have hs₂ := support_expand_entries prims K key _ _ _ hz
  refine ⟨key, fun q hq' => ?_⟩
  rcases hs₂ q hq' with h | ⟨i, rfl⟩
  · rcases hs₁ q h with h | rfl
    · obtain ⟨h1, h2⟩ := hs q h
      exact ⟨fun k idx hk => absurd (h1 k idx hk) (Finset.notMem_empty _), fun tag' ρ' v' hk => by
        have := h2 tag' ρ' v' hk; omega⟩
    · exact ⟨fun k idx hk => (by cases hk), fun tag' ρ' v' hk => by cases hk; omega⟩
  · exact ⟨fun k idx hk => by cases hk; exact Finset.mem_singleton_self _, fun tag' ρ' v' hk => by cases hk⟩

end CoinSteps

end

end ThresholdLeanXmssSecurity

/-! ## The digests and the opening of the check as steps -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

section DigestSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (i : C.Party)

/-- The salted digests of the held terms. -/
def digestQuery (salts : Shares C Bit) (h : C.Term → List Bit) : OracleComp (RoSpec C) (List HashOutput) :=
  C.terms.mapM fun T => if i ∈ C.holders T then do
    hashQuery (.digest (vector 256 (salts T)) (← hashQuery (.history (h T)))) else pure 0

def digestOutbox (ds : List HashOutput) : Mail C E := fun j => if j = i then none else some (.hashes ds)

/-- The test of `compareDigests`. -/
def DigestsAgree (ds : List HashOutput) (inbox : Mail C E) : Prop :=
  ∀ T : C.Term, ∀ j ∈ C.holders T, ∀ j' ∈ C.holders T,
    ((if j = i then ds else Msg.hashesOf (inbox j)))[C.terms.idxOf T]? =
      ((if j' = i then ds else Msg.hashesOf (inbox j')))[C.terms.idxOf T]? ∧
    ((if j = i then ds else Msg.hashesOf (inbox j)))[C.terms.idxOf T]?.isSome

theorem compareDigests_run' {α : Type} (salts : Shares C Bit) (f : Unit → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    (compareDigests (localContext i) salts >>= f).run' st =
      oracleStep (digestQuery i salts st.history) >>= fun ds =>
        exchange (digestOutbox (E := E) i ds) >>= fun inbox =>
          require (DigestsAgree (E := E) i ds inbox) >>= fun _ => (f ()).run' st := by
  simp only [compareDigests, bind_assoc]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc, pure_bind, map_bind]
  rfl

def openOutbox (v : ℕ → E) : Mail C E := fun j => if j = i then none else some (.elements (vector 3 v))

def OpenAgrees (v : ℕ → E) (inbox : Mail C E) : Prop :=
  ∀ j : C.Party, ∀ g < 3, openShare i v inbox j g =
    ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K (K.point j) l * openShare i v inbox l g

def openValue (v : ℕ → E) (inbox : Mail C E) : ℕ → E := fun g =>
  ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * openShare i v inbox l g

theorem openSh_run' {α : Type} (v : ℕ → E) (f : (ℕ → E) → RunM C E (CheckSpec C E) α) (st : RunState C) :
    (StateT.lift (openSh K (localContext i) v 3) >>= f).run' st =
      exchange (openOutbox (E := E) i v) >>= fun inbox =>
        require (OpenAgrees K i v inbox) >>= fun _ => (f (openValue K i v inbox)).run' st := by
  simp only [openSh, bind_assoc]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
  rfl

theorem require_run' (c : Prop) (st : RunState C) :
    (StateT.lift (require c) : RunM C E (CheckSpec C E) Unit).run' st = require c := by
  simp [StateT.run'_eq, StateT.run_lift]

end DigestSteps

section DigestSupport

variable {C : Committee} (prims : Primitives) {σ α : Type}

/-- The steps of a sequence that keep an invariant and a monotone property give them to the whole
sequence. -/
theorem support_sequenceFin_inv [Preorder σ] (Q : σ → Prop) :
    ∀ {n : ℕ} (f : Fin n → StateT σ ProbComp α) (P : Fin n → α → σ → Prop)
      (hf : ∀ i s, Q s → ∀ z ∈ support ((f i).run s), s ≤ z.2 ∧ Q z.2 ∧ P i z.1 z.2)
      (hP : ∀ i a s s', P i a s → s ≤ s' → P i a s') (s : σ), Q s →
      ∀ z ∈ support ((Concrete.sequenceFin f).run s), s ≤ z.2 ∧ Q z.2 ∧ ∀ i, P i (z.1 i) z.2
  | 0, f, P, hf, hP, s, hs => by
    intro z hz
    simp [Concrete.sequenceFin] at hz
    subst hz
    exact ⟨le_rfl, hs, fun i => i.elim0⟩
  | n + 1, f, P, hf, hP, s, hs => by
    intro z hz
    simp only [Concrete.sequenceFin, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨a, s₁⟩, h₁, hz⟩ := hz
    obtain ⟨⟨as, s₂⟩, h₂, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨hs₁, hQ₁, hP₁⟩ := hf 0 s hs _ h₁
    obtain ⟨hs₂, hQ₂, hP₂⟩ := support_sequenceFin_inv Q (fun i : Fin n => f i.succ) (fun i => P i.succ)
      (fun i => hf i.succ) (fun i => hP i.succ) s₁ hQ₁ _ h₂
    refine ⟨hs₁.trans hs₂, hQ₂, fun i => ?_⟩
    cases i using Fin.cases with
    | zero => exact hP 0 a s₁ s₂ hP₁ hs₂
    | succ i => exact hP₂ i

theorem support_hashQuery {q : Query C} (hq : ¬ IsFixed q) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q)).run s)) :
    s ≤ z.2 ∧ z.2 q = some z.1 ∧ ∀ q', z.2 q' ≠ none → s q' ≠ none ∨ q' = q := by
  have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q) = hashAnswer prims q :=
    (simulateQ_query _ _).trans (id_map _)
  refine ⟨?_, ?_, support_hashQuery_entries prims hq s z hz⟩
  · rw [h1] at hz; exact grows_hashAnswer prims q s z hz
  · rw [h1] at hz; exact hashAnswer_cached prims hq s z hz

theorem cacheOK_of_entries {Ks : Finset HashOutput} {L : ℕ} {s s' : HashCache C} (hs : CacheOK Ks L s)
    (q : Query C) (hq : ∀ k idx, q ≠ .expand k idx) (hq' : ∀ tag ρ v, q ≠ .coinKey tag ρ v)
    (h : ∀ q', s' q' ≠ none → s q' ≠ none ∨ q' = q) : CacheOK Ks L s' := by
  intro q' hne
  rcases h q' hne with h | rfl
  · exact hs q' h
  · exact ⟨fun k idx h => absurd h (hq k idx), fun tag ρ v h => absurd h (hq' tag ρ v)⟩

variable {E : Type} [Field E] [Algebra Bit E] (i : C.Party)

theorem support_digestQuery_list (salts : Shares C Bit) (h : C.Term → List Bit) (Ks : Finset HashOutput) (L : ℕ) :
    ∀ (Ts : List C.Term) (s : HashCache C), CacheOK Ks L s → ∀ z,
      z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (Ts.mapM fun T => if i ∈ C.holders T then do
          hashQuery (.digest (vector 256 (salts T)) (← hashQuery (.history (h T)))) else pure 0)).run s) →
      s ≤ z.2 ∧ CacheOK Ks L z.2 ∧ ∃ hlen : z.1.length = Ts.length, ∀ m (hm : m < Ts.length),
        i ∈ C.holders Ts[m] → ∃ hh, z.2 (.history (h Ts[m])) = some hh ∧
          z.2 (.digest (vector 256 (salts Ts[m])) hh) = some (z.1[m]'(hlen ▸ hm)) := by
  intro Ts
  induction Ts with
  | nil =>
    intro s hs z hz
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, hs, rfl, fun m hm => absurd hm (by simp)⟩
  | cons T Ts ih =>
    intro s hs z hz
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨d, s₁⟩, h₁, hz⟩ := hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨ds, s₂⟩, h₂, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    have hT : s ≤ s₁ ∧ CacheOK Ks L s₁ ∧ (i ∈ C.holders T → ∃ hh, s₁ (.history (h T)) = some hh ∧
        s₁ (.digest (vector 256 (salts T)) hh) = some d) := by
      split_ifs at h₁ with hiT
      · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h₁
        obtain ⟨⟨hh, s₀⟩, h₀, h₁⟩ := h₁
        have hq₀ : ¬ IsFixed (C := C) (.history (h T)) := by rintro ⟨_, h, _⟩; cases h
        have hq₁ : ¬ IsFixed (C := C) (.digest (vector 256 (salts T)) hh) := by rintro ⟨_, h, _⟩; cases h
        obtain ⟨hle₀, hc₀, he₀⟩ := support_hashQuery prims hq₀ s _ h₀
        obtain ⟨hle₁, hc₁, he₁⟩ := support_hashQuery prims hq₁ s₀ _ h₁
        have hok₀ := cacheOK_of_entries hs _ (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) he₀
        refine ⟨hle₀.trans hle₁, cacheOK_of_entries hok₀ _ (fun _ _ h => by cases h)
          (fun _ _ _ h => by cases h) he₁, fun _ => ⟨hh, hle₁ hc₀, hc₁⟩⟩
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
        cases h₁
        exact ⟨le_rfl, hs, fun h => absurd h hiT⟩
    obtain ⟨hle₁, hok₁, hd₁⟩ := hT
    obtain ⟨hle₂, hok₂, hlen, hds⟩ := ih s₁ hok₁ _ h₂
    refine ⟨hle₁.trans hle₂, hok₂, by simp [hlen], fun m hm hiT => ?_⟩
    cases m with
    | zero =>
      obtain ⟨hh, h1, h2⟩ := hd₁ hiT
      exact ⟨hh, hle₂ h1, hle₂ h2⟩
    | succ m => exact hds m (by simpa using hm) hiT

theorem idxOf_terms_lt (T : C.Term) : C.terms.idxOf T < C.terms.length :=
  List.idxOf_lt_length_of_mem (Finset.mem_toList.2 (Finset.mem_univ T))

/-- The digests of all operators. Each honest holder of a term has the same digest of it, and the
cache keeps its expansions and coin keys. -/
theorem digests_agree (salts : C.Party → Shares C Bit) (S : Shares C Bit)
    (hS : ∀ i T, i ∈ C.holders T → salts i T = S T) (h : C.Party → C.Term → List Bit) (hh : HistAgree h)
    (Ks : Finset HashOutput) (L : ℕ) (s : HashCache C) (hs : CacheOK Ks L s) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (Concrete.sequenceFin fun i =>
      liftComp (digestQuery i (salts i) (h i)) (LocalSpec C))).run s)) :
    CacheOK Ks L z.2 ∧ (∀ i, (z.1 i).length = C.terms.length) ∧
      ∀ T, ∀ j ∈ C.holders T, ∀ j' ∈ C.holders T, (z.1 j)[C.terms.idxOf T]? = (z.1 j')[C.terms.idxOf T]? := by
  rw [simulateQ_sequenceFin] at hz
  obtain ⟨-, hok, hP⟩ := support_sequenceFin_inv (CacheOK Ks L) _
    (fun i (ds : List HashOutput) (σ : HashCache C) => ∃ hlen : ds.length = C.terms.length,
      ∀ m (hm : m < C.terms.length), i ∈ C.holders C.terms[m] → ∃ hh, σ (.history (h i C.terms[m])) = some hh ∧
        σ (.digest (vector 256 (salts i C.terms[m])) hh) = some (ds[m]'(hlen ▸ hm)))
    (fun i σ hσ y hy => by
      rw [simulateQ_localAnswer_liftComp] at hy
      obtain ⟨hle, hok, hlen, hds⟩ := support_digestQuery_list prims i (salts i) (h i) Ks L C.terms σ hσ y hy
      exact ⟨hle, hok, hlen, hds⟩)
    (fun i ds σ σ' hP hle => by
      obtain ⟨hlen, hds⟩ := hP
      exact ⟨hlen, fun m hm hi => by
        obtain ⟨hh, h1, h2⟩ := hds m hm hi
        exact ⟨hh, hle h1, hle h2⟩⟩) s hs z hz
  refine ⟨hok, fun i => (hP i).1, fun T j hj j' hj' => ?_⟩
  obtain ⟨hlen, hds⟩ := hP j
  obtain ⟨hlen', hds'⟩ := hP j'
  have hT : C.terms[C.terms.idxOf T]'(idxOf_terms_lt T) = T := List.getElem_idxOf _
  obtain ⟨a, ha1, ha2⟩ := hds _ (idxOf_terms_lt T) (by rw [hT]; exact hj)
  obtain ⟨b, hb1, hb2⟩ := hds' _ (idxOf_terms_lt T) (by rw [hT]; exact hj')
  rw [hT] at ha1 ha2 hb1 hb2
  rw [hh T j hj j' hj', hb1, Option.some.injEq] at ha1
  subst ha1
  rw [hS j T hj] at ha2
  rw [hS j' T hj'] at hb2
  have := Option.some.inj (ha2.symm.trans hb2)
  rw [List.getElem?_eq_getElem (by rw [hlen]; exact idxOf_terms_lt T),
    List.getElem?_eq_getElem (by rw [hlen']; exact idxOf_terms_lt T), this]

end DigestSupport

end

end ThresholdLeanXmssSecurity

/-! ## Value facts of an honest check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss Finset Polynomial

noncomputable section

attribute [local instance] Classical.propDecidable

section HonestValues

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

theorem histAgree_record (h : C.Party → C.Term → List Bit) (hh : HistAgree h) (zv : C.Party → Shares C E)
    (Z : Shares C E) (n : ℕ) (hz : ∀ i T g, i ∈ C.holders T → g < n → zv i T g = Z T g) :
    HistAgree (fun i => recordHistory K i (h i) (zv i) n) := by
  intro T i hi j hj
  simp only [recordHistory, if_pos hi, if_pos hj, hh T i hi j hj]
  congr 1
  refine List.flatMap_congr fun g hg => ?_
  have hg' : g < n := List.mem_range.1 (List.mem_filter.1 hg).1
  simp only [Function.comp_apply, hz i T g hi hg', hz j T g hj hg']

theorem digestsAgree_honest (ds : C.Party → List HashOutput) (hlen : ∀ i, (ds i).length = C.terms.length)
    (hag : ∀ T, ∀ j ∈ C.holders T, ∀ j' ∈ C.holders T, (ds j)[C.terms.idxOf T]? = (ds j')[C.terms.idxOf T]?)
    (i : C.Party) : DigestsAgree (E := E) i (ds i) (fun k => digestOutbox (E := E) k (ds k) i) := by
  have hof : ∀ j, (if j = i then ds i else Msg.hashesOf (digestOutbox (E := E) j (ds j) i)) = ds j := fun j => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, digestOutbox, Ne.symm hj, Msg.hashesOf]
  intro T j hj j' hj'
  rw [hof j, hof j']
  refine ⟨hag T j hj j' hj', ?_⟩
  rw [List.getElem?_eq_getElem (by rw [hlen]; exact idxOf_terms_lt T)]
  rfl

theorem openShare_honest (v : C.Party → ℕ → E) (i j : C.Party) (g : ℕ) (hg : g < 3) :
    openShare i (v i) (fun k => openOutbox (E := E) k (v k) i) j g = v j g := by
  unfold openShare
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, openOutbox, Ne.symm hj, Msg.elementAt, vector, hg]

theorem openSh_honest (v : C.Party → ℕ → E) (vals : ℕ → E) (hv : ∀ g < 3, IsShamir K (fun i => v i g) (vals g))
    (i : C.Party) :
    OpenAgrees K i (v i) (fun k => openOutbox (E := E) k (v k) i) ∧
      ∀ g < 3, openValue K i (v i) (fun k => openOutbox (E := E) k (v k) i) g = vals g := by
  constructor
  · intro j g hg
    obtain ⟨P, hP, -, hPi⟩ := hv g hg
    simp only [openShare_honest v i _ g hg, hPi]
    exact (sum_lagrangeFirst_mul_eval K P hP _).symm
  · intro g hg
    obtain ⟨P, hP, hP0, hPi⟩ := hv g hg
    simp only [openValue, openShare_honest v i _ g hg, hPi]
    rw [sum_lagrangeFirst_mul_eval K P hP, hP0]

theorem sum_lagrangeAll_shamir [CharP E 2] {f g : C.Party → E} {a b : E} (hf : IsShamir K f a)
    (hg : IsShamir K g b) : ∑ i, lagrangeAll K i * (f i * g i) = a * b := by
  obtain ⟨P, hP, hP0, hPi⟩ := hf
  obtain ⟨Q, hQ, hQ0, hQi⟩ := hg
  have hdeg : (P * Q).natDegree ≤ C.n - 1 :=
    natDegree_mul_le.trans (by simp only [Committee.n]; omega)
  have := sum_lagrangeAll_mul_eval K (P * Q) hdeg
  simp only [eval_mul] at this
  rw [← hP0, ← hQ0, ← this]
  exact Finset.sum_congr rfl fun i _ => by rw [hPi, hQi]

end HonestValues

end

end ThresholdLeanXmssSecurity

/-! ## The final phase of an honest check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

section FinalPhase

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
  (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
variable {K} in
theorem IsShamir.mul_right {f : C.Party → E} {a : E} (hf : IsShamir K f a) (c : E) :
    IsShamir K (fun i => f i * c) (a * c) :=
  (hf.mul_left c).congr (fun i => by ring) (by ring)

theorem require_of {ι : Type} {G : OracleSpec ι} {c : Prop} (hc : c) :
    (require c : PartyM C E G Unit) = pure () := by
  simp [require, hc]

theorem final_identity [CharP E 2] (α β a b r : E) :
    (α + r * (α + a)) * (β + r * (β + b)) =
      α * β + (a * b + α * β + (α + a) * (β + b)) * r + (α + a) * (β + b) * r ^ 2 := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (-(a * b * r)) * two

/-- The opening of an honest check, whose test holds. -/
theorem open_step_zero [Nonempty C.Party] (v : C.Party → ℕ → E) (vals : ℕ → E)
    (hv : ∀ g < 3, IsShamir K (fun i => v i g) (vals g)) (hfinal : vals 0 * vals 1 = vals 2)
    (st : C.Party → RunState C) (fuel : ℕ) (s : HashCache C) :
    Pr[(· ≠ fun _ => some ()) | (simulateQ (localAnswer prims)
      (honestStart (fun j => (StateT.lift (openSh K (localContext j) (v j) 3) >>= fun opened =>
        (StateT.lift (require (opened 0 * opened 1 = opened 2)) : RunM C E (CheckSpec C E) Unit)).run' (st j)) >>=
        honestRounds (checkFunctionalities K) checkReply (fuel + 1))).run' s] = 0 := by
  simp only [openSh_run']
  rw [honestRounds_exchange]
  swap
  · intro k j; unfold openOutbox; split_ifs <;> rfl
  have hc : ∀ j, openValue K j (v j) (fun k => openOutbox (E := E) k (v k) j) 0 *
      openValue K j (v j) (fun k => openOutbox (E := E) k (v k) j) 1 =
      openValue K j (v j) (fun k => openOutbox (E := E) k (v k) j) 2 := fun j => by
    obtain ⟨-, hval⟩ := openSh_honest K v vals hv j
    rw [hval 0 (by norm_num), hval 1 (by norm_num), hval 2 (by norm_num), hfinal]
  simp only [require_bind_of (openSh_honest K v vals hv _).1, require_of (hc _), StateT.run'_eq,
    StateT.run_lift, pure_bind, map_pure]
  rw [honestRounds_pure]
  simp

theorem final_bound [Nonempty C.Party] (A B : C.Party → ℕ → E) (D : C.Party → E) (a b : E)
    (hA : IsShamir K (fun i => A i 0) a) (hB : IsShamir K (fun i => B i 0) b) (hD : IsShamir K D (a * b))
    (h : C.Party → C.Term → List Bit) (hh : HistAgree h) (L : ℕ) (Ks : Finset HashOutput) (s : HashCache C)
    (hs : CacheOK Ks L s) (fuel : ℕ) :
    Pr[(· ≠ fun _ => some ()) | (simulateQ (localAnswer prims)
      (honestStart (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (A i, B i, D i)).run'
        ⟨h i, L, 0⟩) >>= honestRounds (checkFunctionalities K) checkReply (fuel + 6))).run' s] ≤
      Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries := by
  simp only [finalStep, randElements_run']
  refine probEvent_honest_call prims _ _ (fuel + 5) (fun _ => Sum.inr (Sum.inl 2)) _ _ s _ ?_
  intro z₁ hz₁
  obtain ⟨hs₁, r₁, Zp₁, hz₁⟩ := check_rand_elements_support prims K 2 s z₁ hz₁
  simp only [hz₁, hs₁, extendMult_run']
  refine probEvent_honest_call prims _ _ (fuel + 4) _ _ _ s _ ?_
  intro z₂ hz₂
  obtain ⟨hs₂, Z₂, hZ₂, hz₂⟩ := check_extendMult_support prims K _ 2 (fun i => rfl) s z₂ hz₂
  simp only [hz₂, hs₂, randBits_run']
  refine probEvent_honest_call prims _ _ (fuel + 3) (fun _ => Sum.inr (Sum.inr 256)) _ _ s _ ?_
  intro z₃ hz₃
  obtain ⟨hs₃, r₃, Zp₃, hz₃⟩ := check_rand_bits_support prims K 256 s z₃ hz₃
  simp only [hz₃, hs₃, compareDigests_run']
  refine probEvent_honest_local prims _ _ (fuel + 3) _ _ _ s _ ?_
  intro z₄ hz₄
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hz₄ ⊢
  have hh₄ := histAgree_record K h hh (fun i T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) Z₂ 2
    (fun i T g hi hg => by simp [hi, hg])
  obtain ⟨hok₄, hlen₄, hag₄⟩ := digests_agree prims _ r₃ (fun i T hi => by simp [hi]) _ hh₄ Ks L s hs z₄ hz₄
  rw [show fuel + 3 = (fuel + 2) + 1 from rfl, honestRounds_exchange]
  swap
  · intro k j; unfold digestOutbox; split_ifs <;> rfl
  simp only [require_bind_of (digestsAgree_honest z₄.1 hlen₄ hag₄ _), challenge_run']
  refine probEvent_honest_call prims _ _ (fuel + 1) (fun _ => Sum.inl (Sum.inl 1)) _ _ z₄.2 _ ?_
  intro z₅ hz₅
  obtain ⟨hs₅, v₅, hz₅⟩ := check_coin_support prims K 1 z₄.2 z₅ hz₅
  simp only [hz₅, hs₅]
  have hbound := challengeQuery_none_le prims K 0 (L + 1 + 1 + 1) v₅ Ks L (by omega) z₄.2 hok₄
  refine (probEvent_honest_common prims _ _ (fuel + 1) (challengeQuery K 0 (L + 1 + 1 + 1) v₅) _ _
    (fun z => z.1 = none) z₄.2 0 ?_).trans (by rw [add_zero]; exact hbound)
  intro z₆ hz₆ hbad
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hbad
  simp only [hr]
  haveI := charP_two (E := E)
  refine le_of_eq (open_step_zero prims K _ (fun k => match k with
    | 0 => (∑ T, r₁ T 0) + r * ((∑ T, r₁ T 0) + a)
    | 1 => (∑ T, r₁ T 1) + r * ((∑ T, r₁ T 1) + b)
    | _ => (∑ T, r₁ T 0) * (∑ T, r₁ T 1) +
        (a * b + (∑ T, r₁ T 0) * (∑ T, r₁ T 1) + ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b)) * r +
        ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) * r ^ 2) ?_ ?_ _ fuel _)
  · intro g hg
    have hwa : IsShamir K (fun i => conv K (localContext i) (fun T => if i ∈ C.holders T then r₁ T else fun _ => 0) 0)
        (∑ T, r₁ T 0) := (isShamir_conv r₁ 0).congr (fun i => (conv_congr i _ _ 0 fun T hT => by simp [hT]).symm) rfl
    have hwb : IsShamir K (fun i => conv K (localContext i) (fun T => if i ∈ C.holders T then r₁ T else fun _ => 0) 1)
        (∑ T, r₁ T 1) := (isShamir_conv r₁ 1).congr (fun i => (conv_congr i _ _ 1 fun T hT => by simp [hT]).symm) rfl
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) k) (∑ T, Z₂ T k) := fun k hk =>
      (isShamir_conv Z₂ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₂ T 0 = (∑ T, r₁ T 0) * (∑ T, r₁ T 1) := by
      rw [hZ₂ 0 (by norm_num)]
      simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext,
        Finset.sum_range_one]
      exact sum_lagrangeAll_shamir K hwa hwb
    have hq1 : ∑ T, Z₂ T 1 = ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) := by
      rw [hZ₂ 1 (by norm_num)]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
        localContext, Finset.sum_range_one]
      exact sum_lagrangeAll_shamir K (hwa.add hA) (hwb.add hB)
    interval_cases g
    · exact (hwa.add ((hwa.add hA).mul_left r)).congr (fun i => rfl) rfl
    · exact (hwb.add ((hwb.add hB).mul_left r)).congr (fun i => rfl) rfl
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine ((h0.add (((hD.add h0).add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
      rw [hq0, hq1]
      rfl
  · exact final_identity _ _ _ _ _

end FinalPhase

end

end ThresholdLeanXmssSecurity

/-! ## The halving phase of an honest check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section HalvingPhase

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
  (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

/-- The bound on the failed challenges of `r` coins, when the cache holds expansions of `c` keys. -/
def chalErr (E : Type) [Fintype E] (c r : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range r, (((c + j : ℕ) : ℝ≥0∞) / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries)

omit [Field E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem chalErr_succ (c r : ℕ) :
    chalErr E c (r + 1) = ((c : ℝ≥0∞) / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) + chalErr E (c + 1) r := by
  unfold chalErr
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 3
    omega

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem sum_lagrangeAll_shamir_sum [CharP E 2] {f g : C.Party → ℕ → E} {a b : ℕ → E}
    (hf : ∀ k, IsShamir K (fun i => f i k) (a k)) (hg : ∀ k, IsShamir K (fun i => g i k) (b k)) (n : ℕ) :
    ∑ i, lagrangeAll K i * ∑ k ∈ range n, f i k * g i k = ∑ k ∈ range n, a k * b k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => sum_lagrangeAll_shamir K (hf k) (hg k)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem IsShamir.ite {f : C.Party → E} {a : E} (hf : IsShamir K f a) (c : Prop) [Decidable c] :
    IsShamir K (fun i => if c then f i else 0) (if c then a else 0) := by
  split_ifs
  · exact hf
  · exact IsShamir.const 0

theorem iterate_halvingSteps : ∀ (w : ℕ), 1 ≤ w → halvedLength^[halvingSteps w] w = 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rw [halvingSteps]
    split_ifs with h
    · rw [Function.iterate_succ_apply]
      obtain ⟨h1, h2⟩ := halvedLength_le w
      refine ih _ ?_ (by omega)
      unfold halvedLength; split_ifs <;> omega
    · simp; omega

theorem halving_bound [Nonempty C.Party] (width : ℕ) (hwidth : 1 ≤ width) :
    ∀ (n j₀ : ℕ), j₀ + n = halvingSteps width → ∀ (A B : C.Party → ℕ → E) (D : C.Party → E) (Av Bv : ℕ → E),
      (∀ k, IsShamir K (fun i => A i k) (Av k)) → (∀ k, IsShamir K (fun i => B i k) (Bv k)) →
      IsShamir K D (∑ k ∈ range (halvedLength^[j₀] width), Av k * Bv k) →
      ∀ (h : C.Party → C.Term → List Bit), HistAgree h → ∀ (L c : ℕ) (Ks : Finset HashOutput), Ks.card ≤ c →
      ∀ (s : HashCache C), CacheOK Ks L s → ∀ fuel : ℕ,
      Pr[(· ≠ fun _ => some ()) | (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (halvingStep K (localContext i) (hybridCheckGadgets K i) width)
          (A i, B i, D i) >>= finalStep K (localContext i) (hybridCheckGadgets K i)).run' ⟨h i, L, 0⟩) >>=
          honestRounds (checkFunctionalities K) checkReply (fuel + 2 * n + 6))).run' s] ≤ chalErr E c (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro j₀ hj A B D Av Bv hA hB hD h hh L c Ks hKs s hs fuel
    simp only [List.range'_zero, List.foldlM_nil, pure_bind, Nat.mul_zero, Nat.add_zero]
    rw [Nat.add_zero] at hj
    subst hj
    rw [iterate_halvingSteps width hwidth, Finset.sum_range_one] at hD
    refine (final_bound prims K A B D (Av 0) (Bv 0) (hA 0) (hB 0) hD h hh L Ks s hs fuel).trans ?_
    simp only [chalErr, zero_add, Finset.sum_range_one, Nat.add_zero]
    gcongr
  | succ n ih =>
    intro j₀ hj A B D Av Bv hA hB hD h hh L c Ks hKs s hs fuel
    haveI := charP_two (E := E)
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 6 = (fuel + 2 * n + 7) + 1 by ring]
    simp only [List.foldlM_cons, halvingStep, bind_assoc, pure_bind, extendMult_run']
    refine probEvent_honest_call prims _ _ (fuel + 2 * n + 7) _ _ _ s _ ?_
    intro z₁ hz₁
    obtain ⟨hs₁, Z₁, hZ₁, hz₁⟩ := check_extendMult_support prims K _ 2 (fun i => rfl) s z₁ hz₁
    simp only [hz₁, hs₁, challenge_run', List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    rw [show fuel + 2 * n + 7 = (fuel + 2 * n + 6) + 1 by ring]
    refine probEvent_honest_call prims _ _ (fuel + 2 * n + 6) (fun _ => Sum.inl (Sum.inl 1)) _ _ s _ ?_
    intro z₂ hz₂
    obtain ⟨hs₂, v₂, hz₂⟩ := check_coin_support prims K 1 s z₂ hz₂
    simp only [hz₂, hs₂]
    rw [chalErr_succ]
    refine (probEvent_honest_common prims _ _ _ (challengeQuery K 0 (L + 1) v₂) _ _
      (fun z => z.1 = none) s _ ?_).trans (add_le_add ((challengeQuery_none_le prims K 0 (L + 1) v₂ Ks L
        (by omega) s hs).trans (by gcongr)) le_rfl)
    intro z₃ hz₃ hbad
    obtain ⟨k₃, hok₃⟩ := challengeQuery_cache prims K 0 (L + 1) v₂ Ks L (by omega) s hs z₃ hz₃
    rcases z₃ with ⟨_ | r, s₃⟩
    · exact absurd rfl hbad
    dsimp only at hok₃ ⊢
    set ℓ := halvedLength^[j₀] width with hℓ
    set half := halvedLength ℓ with hhalf
    let hiv := fun (v : ℕ → E) k => if k + half < ℓ then v (k + half) else 0
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
      rw [hZ₁ 0 (by norm_num)]
      simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext]
      exact sum_lagrangeAll_shamir_sum K hA hB half
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, (Av k + hiv Av k) * (Bv k + hiv Bv k) := by
      rw [hZ₁ 1 (by norm_num)]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
        localContext]
      exact sum_lagrangeAll_shamir_sum K (hsum A Av hA) (hsum B Bv hB) half
    refine ih (j₀ + 1) (by omega) _ _ _ (fun k => Av k + r * (Av k + hiv Av k))
      (fun k => Bv k + r * (Bv k + hiv Bv k)) (hfold A Av hA) (hfold B Bv hB) ?_ _
      (histAgree_record K h hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (L + 1 + 1) (c + 1) (insert k₃ Ks)
      ((Finset.card_insert_le _ _).trans (by omega)) s₃ hok₃ fuel
    have h0 := hq 0 (by norm_num)
    have h1 := hq 1 (by norm_num)
    refine ((h0.add ((hD.add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
    rw [hq0, hq1, Function.iterate_succ_apply', ← hℓ, ← hhalf, sum_range_halving_fold, sum_range_padded Av Bv ℓ]

end HalvingPhase

end

end ThresholdLeanXmssSecurity

/-! ## The slice phase of an honest check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section SliceAlgebra

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

theorem coinProduct_succ_low (τ : List E) (w a : ℕ) (ha : a < 2 ^ w) :
    coinProduct τ 0 (w + 1) a = coinProduct τ 0 w a := by
  unfold coinProduct
  rw [Finset.prod_range_succ, Nat.testBit_lt_two_pow ha]
  simp

theorem coinProduct_succ_high (τ : List E) (w a : ℕ) (ha : a < 2 ^ w) :
    coinProduct τ 0 (w + 1) (2 ^ w + a) = coinProduct τ 0 w a * τ.getD w 0 := by
  unfold coinProduct
  rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha]
  simp only [Bool.not_false, if_true, zero_add]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.1 hb)]

theorem coinProduct_zero_width (τ : List E) (a : ℕ) : coinProduct τ 0 0 a = 1 := by
  simp [coinProduct]

/-- The claim of a slice step splits at the top bit of the slice. -/
theorem slice_sum_split (τ : List E) (width w : ℕ) (hw : 0 < width) (X Y : ℕ → E) :
    ∑ k ∈ range (width * 2 ^ (w + 1)), coinProduct τ 0 (w + 1) (k / width) * X k * Y k =
      ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) * X k * Y k +
        τ.getD w 0 * ∑ k ∈ range (width * 2 ^ w),
          coinProduct τ 0 w (k / width) * X (k + width * 2 ^ w) * Y (k + width * 2 ^ w) := by
  rw [show width * 2 ^ (w + 1) = width * 2 ^ w + width * 2 ^ w by ring, Finset.sum_range_add]
  have hlt : ∀ k ∈ range (width * 2 ^ w), k / width < 2 ^ w := fun k hk =>
    (Nat.div_lt_iff_lt_mul hw).2 (by rw [mul_comm]; exact Finset.mem_range.1 hk)
  congr 1
  · exact Finset.sum_congr rfl fun k hk => by rw [coinProduct_succ_low τ w _ (hlt k hk)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.mul_add_div hw, coinProduct_succ_high τ w _ (hlt k hk), add_comm k]
    ring

variable (K : Constants C E)

theorem sum_productShare_replicated (xv yv : C.Party → Shares C E) (X Y : Shares C E) (n : ℕ)
    (hx : ∀ i T, i ∈ C.holders T → xv i T = X T) (hy : ∀ i T, i ∈ C.holders T → yv i T = Y T) :
    ∑ i, productShare K (localContext i) (.replicated (xv i) (yv i) n) =
      ∑ g ∈ range n, (∑ T, X T g) * ∑ T, Y T g := by
  simp only [productShare]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h : ∀ i, mulRep K (localContext i) (xv i) (yv i) g = ∑ AB ∈ K.pairs i, X AB.1 g * Y AB.2 g := by
    intro i
    refine Finset.sum_congr rfl fun AB hAB => ?_
    obtain ⟨h1, h2⟩ := K.pairs_held i AB hAB
    rw [hx i AB.1 h1, hy i AB.2 h2]
  simp_rw [h]
  rw [sum_sum_pairs K (fun AB => X AB.1 g * Y AB.2 g), Finset.sum_mul_sum, ← Finset.sum_product',
    Finset.univ_product_univ]

end SliceAlgebra

end

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section SlicePhase

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
  (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

theorem slice_bound [Nonempty C.Party] (τ : List E) (count : ℕ) (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0)
    (hwidth : 0 < sliceWidth count) :
    ∀ (n j₀ : ℕ), j₀ + n = sliceBits → ∀ (xs ys : C.Party → Shares C E) (D : C.Party → E) (XS YS : Shares C E),
      (∀ i T, i ∈ C.holders T → xs i T = XS T ∧ ys i T = YS T) →
      IsShamir K D (∑ k ∈ range (sliceWidth count * 2 ^ (sliceBits - j₀)),
        coinProduct τ 0 (sliceBits - j₀) (k / sliceWidth count) * (∑ T, XS T k) * ∑ T, YS T k) →
      ∀ (h : C.Party → C.Term → List Bit), HistAgree h → ∀ (L c : ℕ) (Ks : Finset HashOutput), Ks.card ≤ c →
      ∀ (s : HashCache C), CacheOK Ks L s → ∀ fuel : ℕ,
      Pr[(· ≠ fun _ => some ()) | (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (sliceStep K (localContext i) (hybridCheckGadgets K i) τ count)
          (xs i, ys i, D i) >>= fun p =>
            (List.range (halvingSteps (sliceWidth count))).foldlM
              (halvingStep K (localContext i) (hybridCheckGadgets K i) (sliceWidth count))
              (conv K (localContext i) p.1, conv K (localContext i) p.2.1, p.2.2) >>=
            finalStep K (localContext i) (hybridCheckGadgets K i)).run' ⟨h i, L, 0⟩) >>=
          honestRounds (checkFunctionalities K) checkReply
            (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 6))).run' s] ≤
        chalErr E c (n + halvingSteps (sliceWidth count) + 1) := by
  haveI := charP_two (E := E)
  intro n
  induction n with
  | zero =>
    intro j₀ hj xs ys D XS YS hxy hD h hh L c Ks hKs s hs fuel
    simp only [List.range'_zero, List.foldlM_nil, pure_bind, Nat.mul_zero, Nat.add_zero, zero_add]
    rw [Nat.add_zero] at hj
    subst hj
    rw [List.range_eq_range']
    refine halving_bound prims K (sliceWidth count) hwidth _ 0 (by omega) _ _ D (fun k => ∑ T, XS T k)
      (fun k => ∑ T, YS T k) (fun k => (isShamir_conv XS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).1]).symm) rfl)
      (fun k => (isShamir_conv YS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).2]).symm) rfl) ?_ h hh L c Ks hKs s hs fuel
    refine hD.congr (fun i => rfl) ?_
    simp only [Nat.sub_self, pow_zero, mul_one, Function.iterate_zero, id, coinProduct_zero_width, one_mul]
  | succ n ih =>
    intro j₀ hj xs ys D XS YS hxy hD h hh L c Ks hKs s hs fuel
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 2 * halvingSteps (sliceWidth count) + 6 =
      (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 7) + 1 by ring]
    simp only [List.foldlM_cons, sliceStep, bind_assoc, pure_bind, extendMult_run']
    refine probEvent_honest_call prims _ _ _ _ _ _ s _ ?_
    intro z₁ hz₁
    obtain ⟨hs₁, Z₁, hZ₁, hz₁⟩ := check_extendMult_support prims K _ 2 (fun i => rfl) s z₁ hz₁
    simp only [hz₁, hs₁, challenge_run', List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    rw [show fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 7 =
      (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 6) + 1 by ring]
    refine probEvent_honest_call prims _ _ _ (fun _ => Sum.inl (Sum.inl 1)) _ _ s _ ?_
    intro z₂ hz₂
    obtain ⟨hs₂, v₂, hz₂⟩ := check_coin_support prims K 1 s z₂ hz₂
    simp only [hz₂, hs₂]
    rw [show n + 1 + halvingSteps (sliceWidth count) + 1 = (n + halvingSteps (sliceWidth count) + 1) + 1 by ring,
      chalErr_succ]
    refine (probEvent_honest_common prims _ _ _ (challengeQuery K 0 (L + 1) v₂) _ _
      (fun z => z.1 = none) s _ ?_).trans (add_le_add ((challengeQuery_none_le prims K 0 (L + 1) v₂ Ks L
        (by omega) s hs).trans (by gcongr)) le_rfl)
    intro z₃ hz₃ hbad
    obtain ⟨k₃, hok₃⟩ := challengeQuery_cache prims K 0 (L + 1) v₂ Ks L (by omega) s hs z₃ hz₃
    rcases z₃ with ⟨_ | r, s₃⟩
    · exact absurd rfl hbad
    dsimp only at hok₃ ⊢
    have hw : sliceBits - 1 - j₀ = n := by omega
    set width := sliceWidth count with hwidth_def
    set half := width * 2 ^ (sliceBits - 1 - j₀) with hhalf
    set rest := fun k => coinProduct τ 0 (sliceBits - 1 - j₀) (k / width) with hrest
    set cc := τ.getD (sliceBits - 1 - j₀) 0 with hcc
    have hc : cc ≠ 0 := hτ _ (by omega)
    let Xv := fun k => ∑ T, XS T k
    let Yv := fun k => ∑ T, YS T k
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₁ T g else 0) k) (∑ T, Z₁ T k) := fun k hk =>
      (isShamir_conv Z₁ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₁ T 0 = ∑ k ∈ range half, rest k * Xv k * Yv k := by
      rw [hZ₁ 0 (by norm_num)]
      simp only [extendMultShare, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * XS T k) YS half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => (hxy i T hT).2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum]
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, rest k * (Xv k + Xv (k + half)) * (Yv k + Yv (k + half)) := by
      rw [hZ₁ 1 (by norm_num)]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * (XS T k + XS T (k + half)))
        (fun T k => YS T k + YS T (k + half)) half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => by funext k; rw [(hxy i T hT).2])]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsplit := slice_sum_split τ width (sliceBits - 1 - j₀) hwidth Xv Yv
    rw [show sliceBits - 1 - j₀ + 1 = sliceBits - j₀ by omega] at hsplit
    have hDv := hsplit
    refine ih (j₀ + 1) (by omega) _ _ _ (fun T k => XS T k + r * (XS T k + XS T (k + half)))
      (fun T k => YS T k + r * (YS T k + YS T (k + half)))
      (fun i T hT => ⟨by funext k; rw [(hxy i T hT).1], by funext k; rw [(hxy i T hT).2]⟩) ?_ _
      (histAgree_record K h hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (L + 1 + 1) (c + 1) (insert k₃ Ks)
      ((Finset.card_insert_le _ _).trans (by omega)) s₃ hok₃ fuel
    have h0 := hq 0 (by norm_num)
    have h1 := hq 1 (by norm_num)
    refine (((h0.mul_left (1 + r)).add (((hD.add h0).div cc).mul_left r)).add (h1.mul_left (r * (1 + r)))).congr
      (fun i => rfl) ?_
    rw [hq0, hq1, show sliceBits - (j₀ + 1) = sliceBits - 1 - j₀ by omega]
    rw [sum_range_slice_fold rest Xv Yv half r cc _ hc hDv]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Xv, Yv, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl

end SlicePhase

end

end ThresholdLeanXmssSecurity

/-! ## The start of an honest check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section StartPhase

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (i : C.Party)

theorem coinKey_expand_run' {α : Type} (count : ℕ) (f : List E → RunM C E (CheckSpec C E) α) (st : RunState C) :
    (coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key count >>= f).run' st =
      call (Sum.inl (Sum.inl 1)) >>= fun o => match o with
        | some (.inl (.inl v)) => oracleStep (tauQuery K st.tag st.label v count) >>= fun τ =>
            (f τ).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [coinKey, expand, bind_assoc, hybridCheckGadgets, freshLabel, tauQuery, oracleStep_bind]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, StateT.run_get]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift]

omit [Field E] [Algebra Bit E] in
theorem sliceWidth_pos {count : ℕ} (h : count ≠ 0) : 0 < sliceWidth count := by
  simp only [sliceWidth, sliceLength, wordBits, sliceBits]
  have : 0 < count := Nat.pos_of_ne_zero h
  omega

omit [Field E] [Algebra Bit E] in
theorem sliceBits_le_coins {count : ℕ} (h : count ≠ 0) : sliceBits ≤ coins count := by
  have hw := sliceWidth_pos h
  simp only [sliceWidth, wordBits] at hw
  unfold coins
  have h7 : sliceBits = 6 + 1 := rfl
  rw [h7, Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]
  norm_num at hw ⊢
  omega

end StartPhase

end

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section TupleFacts

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The tuple and the position in it of entry `k` of the concatenated vectors of the counts `cs`. -/
def flatPos : List ℕ → ℕ → Option (ℕ × ℕ)
  | [], _ => none
  | c :: cs, k => if k < c then some (0, k) else (flatPos cs (k - c)).map fun p => (p.1 + 1, p.2)

theorem flatPos_spec : ∀ (cs : List ℕ) (k m g : ℕ), flatPos cs k = some (m, g) → m < cs.length ∧ g < cs.getD m 0
  | [], k, m, g, h => by simp [flatPos] at h
  | c :: cs, k, m, g, h => by
    unfold flatPos at h
    split_ifs at h with hk
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using hk
    · rcases hp : flatPos cs (k - c) with _ | ⟨m', g'⟩
      · simp [hp] at h
      · simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := flatPos_spec cs (k - c) m' g' hp
        exact ⟨by simpa using h1, by simpa using h2⟩

theorem getD_flatMap_vector_pos {R : Type} [Zero R] (F : Tuple C → ℕ → R) :
    ∀ (L : List (Tuple C)) (k : ℕ), (L.flatMap fun τ => vector τ.count (F τ)).getD k 0 =
      match flatPos (L.map (·.count)) k with
      | some (m, g) => (L[m]?.map fun τ => F τ g).getD 0
      | none => 0
  | [], k => by simp [flatPos]
  | τ :: L, k => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD]
    simp only [List.map_cons, flatPos]
    by_cases hk : k < τ.count
    · rw [List.getElem?_append_left (by simpa [vector] using hk), if_pos hk]
      simp [vector, hk]
    · rw [List.getElem?_append_right (by simp [vector]; omega), if_neg hk]
      have ih := getD_flatMap_vector_pos F L (k - τ.count)
      rw [List.getD_eq_getElem?_getD] at ih
      simp only [vector, List.length_map, List.length_range] at ih ⊢
      rw [ih]
      rcases flatPos (L.map (·.count)) (k - τ.count) with _ | ⟨m, g⟩ <;> simp

theorem liftedPart_eq (tuples : List (Tuple C)) (part : Tuple C → Shares C Bit) (T : C.Term) (k : ℕ) :
    liftedPart tuples part T k =
      ((tuples.map fun τ => vector τ.count (part τ T)).flatMap (List.map (algebraMap Bit E))).getD k 0 := by
  unfold liftedPart
  rw [List.flatMap_map]
  congr 2
  funext τ
  simp [vector, List.map_map, Function.comp_def]

variable {K}

theorem tupleInputs_count {counts : List ℕ} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts noCoalition x) (i : C.Party) : (x i).map (·.count) = counts :=
  hx.1 i (by simp)

theorem tupleInputs_vectors {counts : List ℕ} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts noCoalition x) (T : C.Term) (i j : C.Party) (hi : i ∈ C.holders T)
    (hj : j ∈ C.holders T) :
    (x i).map (fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) =
      (x j).map (fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) := by
  refine hx.2.2 T ?_ i hi j hj (by simp) (by simp)
  intro i _ j _ _ _
  have h0 : ∀ i, (x i).map (fun τ => vector τ.count fun g =>
      if ∃ j ∈ (noCoalition (C := C)).1, filler K τ.mode T g = some j then τ.z T g else 0) =
        counts.map (fun c => vector c fun _ => (0 : Bit)) := fun i => by
    rw [← tupleInputs_count hx i, List.map_map]
    simp [noCoalition, Function.comp_def]
  exact (h0 i).trans (h0 j).symm

theorem tupleInputs_part {counts : List ℕ} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts noCoalition x) (T : C.Term) (i j : C.Party) (hi : i ∈ C.holders T)
    (hj : j ∈ C.holders T) (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    (x i).map (fun τ => vector τ.count (part τ T)) = (x j).map (fun τ => vector τ.count (part τ T)) := by
  have h := tupleInputs_vectors hx T i j hi hj
  rcases hpart with rfl | rfl | rfl
  · have := congrArg (List.map Prod.fst) h; simpa [List.map_map, Function.comp_def] using this
  · have := congrArg (List.map fun p => p.2.1) h; simpa [List.map_map, Function.comp_def] using this
  · have := congrArg (List.map fun p => p.2.2) h; simpa [List.map_map, Function.comp_def] using this

theorem liftedPart_agree {counts : List ℕ} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts noCoalition x) (T : C.Term) (i j : C.Party) (hi : i ∈ C.holders T)
    (hj : j ∈ C.holders T) (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    liftedPart (E := E) (x i) part T = liftedPart (x j) part T := by
  funext k
  rw [liftedPart_eq, liftedPart_eq, tupleInputs_part hx T i j hi hj part hpart]

theorem histAgree_filled {counts : List ℕ} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts noCoalition x) : HistAgree (fun i => filledHistory K i (x i)) := by
  intro T i hi j hj
  simp only [filledHistory, if_pos hi, if_pos hj]
  let F : ReshareMode × List Bit → List Bit := fun p =>
    ((List.range p.2.length).filter fun g => (filler K p.1 T g).isSome).map fun g => p.2.getD g 0
  have hF : ∀ τ : Tuple C, ((List.range τ.count).filter fun g => (filler K τ.mode T g).isSome).map (τ.z T) =
      F (τ.mode, vector τ.count (τ.z T)) := fun τ => by
    simp only [F, vector, List.length_map, List.length_range]
    refine List.map_congr_left fun g hg => ?_
    have hg' : g < τ.count := List.mem_range.1 (List.mem_filter.1 hg).1
    simp [List.getD_eq_getElem?_getD, hg']
  have hmap : ∀ l : List (Tuple C), l.flatMap (fun τ =>
      ((List.range τ.count).filter fun g => (filler K τ.mode T g).isSome).map (τ.z T)) =
      (l.map fun τ => (τ.mode, vector τ.count (τ.z T))).flatMap F := fun l => by
    rw [List.flatMap_map]
    exact List.flatMap_congr fun τ _ => hF τ
  rw [hmap, hmap]
  congr 1
  rw [← List.zip_map', ← List.zip_map', hx.2.1 i j (by simp) (by simp),
    tupleInputs_part hx T i j hi hj (·.z) (Or.inr (Or.inr rfl))]

theorem reconstruct_eq_view {α : Type} [Inhabited α] (views : C.Party → Option (C.Term → α)) (T : C.Term)
    (h : ∀ i, (views i).isSome) : ∃ i ∈ C.holders T, ∃ f, views i = some f ∧ reconstruct views T = f T := by
  obtain ⟨i₀, hi₀⟩ := exists_holder T
  unfold reconstruct
  rcases hl : (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) with _ | ⟨f, rest⟩
  · exfalso
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (h i₀)
    have : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) :=
      List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [hi₀, hf]⟩
    rw [hl] at this
    simp at this
  · have hmem : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) := by
      rw [hl]; exact List.mem_cons_self
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hmem
    split_ifs at hi with hiT
    exact ⟨i, hiT, f, hi, by simp⟩

theorem vector_point {R : Type} {c c' : ℕ} {f f' : ℕ → R} (h : vector c f = vector c' f') {g : ℕ} (hg : g < c) :
    f g = f' g := by
  have hc : c = c' := by simpa [vector] using congrArg List.length h
  subst hc
  have := congrArg (·[g]?) h
  simp only [vector, List.getElem?_map, List.getElem?_range hg, Option.map_some, Option.some.injEq] at this
  exact this

/-- On correct tuples, the lifted vectors of the owners of the terms multiply at every position. -/
theorem lifted_product [Nonempty C.Party] {counts : List ℕ} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts noCoalition x ∧ CorrectTuples x) (k : ℕ) :
    ∑ T, liftedPart (E := E) (x (K.owner T)) (·.z) T k =
      (∑ T, liftedPart (E := E) (x (K.owner T)) (·.x) T k) * ∑ T, liftedPart (E := E) (x (K.owner T)) (·.y) T k := by
  obtain ⟨hx, hcorrect⟩ := hx
  have hpos : ∀ (part : Tuple C → Shares C Bit) T, liftedPart (E := E) (x (K.owner T)) part T k =
      match flatPos counts k with
      | some (m, g) => (((x (K.owner T))[m]?).map fun τ => algebraMap Bit E (part τ T g)).getD 0
      | none => 0 := fun part T => by
    unfold liftedPart
    rw [getD_flatMap_vector_pos, tupleInputs_count hx]
  simp only [hpos]
  rcases hk : flatPos counts k with _ | ⟨m, g⟩
  · simp
  obtain ⟨hm, hg⟩ := flatPos_spec counts k m g hk
  have hlen : ∀ i, m < (x i).length := fun i => by
    rw [← List.length_map (f := (·.count)), tupleInputs_count hx i]; exact hm
  have hcount : ∀ i, ((x i)[m]'(hlen i)).count = counts.getD m 0 := fun i => by
    have := congrArg (·.getD m 0) (tupleInputs_count hx i)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen i)] using this
  simp only [List.getElem?_eq_getElem (hlen _), Option.map_some, Option.getD_some]
  obtain ⟨p, hp⟩ := firstInput_some_of_nonempty (C := C) (I := List (Tuple C)) (fun i => x i)
  have hfl : m < (firstInput fun i => some (x i)).length := by rw [hp]; exact hlen p
  have hτc : (tupleAt (fun i => some (x i)) m).count = counts.getD m 0 := by
    simp only [tupleAt, hp, List.getElem?_eq_getElem (hlen p), Option.map_some, Option.getD_some, hcount]
  have hrec : ∀ (part : Tuple C → Shares C Bit), (part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) → ∀ T,
      reconstruct (fun i => ((some (x i)).bind (·[m]?)).map part) T g = part ((x (K.owner T))[m]'(hlen _)) T g := by
    intro part hpart T
    obtain ⟨i, hi, f, hf, hrf⟩ := reconstruct_eq_view (fun i => ((some (x i)).bind (·[m]?)).map part) T
      (fun i => by simp [List.getElem?_eq_getElem (hlen i)])
    simp only [Option.bind_some, List.getElem?_eq_getElem (hlen i), Option.map_some, Option.some.injEq] at hf
    rw [hrf, ← hf]
    have h := congrArg (·[m]?) (tupleInputs_part hx T i (K.owner T) hi (K.owner_held T) part hpart)
    simp only [List.getElem?_map, List.getElem?_eq_getElem (hlen _), Option.map_some, Option.some.injEq] at h
    exact vector_point h (by rw [hcount]; exact hg)
  have hc := hcorrect m hfl g (by rw [hτc]; exact hg)
  simp only [shareValue, tupleAt] at hc
  simp only [hrec (·.x) (Or.inl rfl), hrec (·.y) (Or.inr (Or.inl rfl)), hrec (·.z) (Or.inr (Or.inr rfl))] at hc
  rw [← map_sum, hc, map_mul, map_sum, map_sum]

end TupleFacts

end

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section HonestCheck

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
  (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

theorem check_honest_bound [Nonempty C.Party] (counts : List ℕ) (x : C.Party → List (Tuple C))
    (hx : TupleInputs K counts noCoalition x ∧ CorrectTuples x) (hpos : counts.sum ≠ 0) :
    Pr[(· ≠ fun _ => some ()) | (simulateQ (localAnswer prims)
      (honestStart (fun i => checkProtocol K i (x i)) >>=
        honestRounds (checkFunctionalities K) checkReply (checkRounds counts.sum))).run' ∅] ≤
      sliceBits / Fintype.card E + chalErr E 1 (halvings counts.sum + 1) := by
  haveI := charP_two (E := E)
  have hcnt : ∀ i, ((x i).map (·.count)).sum = counts.sum := fun i => by rw [tupleInputs_count hx.1 i]
  have hne : ∀ i, ((x i).map (·.count)).sum ≠ 0 := fun i => by rw [hcnt i]; exact hpos
  simp only [checkProtocol, check_eq _ _ _ _ (hne _)]
  simp only [hcnt, coinKey_expand_run']
  rw [show checkRounds counts.sum = (2 * halvings counts.sum + 7) + 1 by unfold checkRounds; ring]
  refine probEvent_honest_call prims _ _ _ (fun _ => Sum.inl (Sum.inl 1)) _ _ ∅ _ ?_
  intro z₁ hz₁
  obtain ⟨hs₁, v₁, hz₁⟩ := check_coin_support prims K 1 ∅ z₁ hz₁
  simp only [hz₁, hs₁]
  have hok₀ : CacheOK (C := C) ∅ 0 ∅ := fun q h => absurd rfl h
  refine (probEvent_honest_common prims _ _ _ (tauQuery K 0 0 v₁ (coins counts.sum)) _ _
    (fun z => ¬ ∀ b < sliceBits, z.1.getD b 0 ≠ 0) ∅ _ ?_).trans (add_le_add
      (tauQuery_zero_le prims K 0 0 v₁ (coins counts.sum) sliceBits (sliceBits_le_coins hpos) 0 le_rfl ∅ hok₀)
      le_rfl)
  intro z₂ hz₂ hτ
  rw [not_not] at hτ
  obtain ⟨k₂, hok₂⟩ := tauQuery_cache prims K 0 0 v₁ (coins counts.sum) 0 le_rfl ∅ hok₀ z₂ hz₂
  simp only [run'_lift_bind, require_bind_of hτ]
  have hR : halvings counts.sum = sliceBits + halvingSteps (sliceWidth counts.sum) := rfl
  rw [show List.range sliceBits = List.range' 0 sliceBits from List.range_eq_range',
    show halvings counts.sum - sliceBits = halvingSteps (sliceWidth counts.sum) by omega,
    show 2 * halvings counts.sum + 7 = 1 + 2 * sliceBits + 2 * halvingSteps (sliceWidth counts.sum) + 6 by omega,
    show halvings counts.sum + 1 = sliceBits + halvingSteps (sliceWidth counts.sum) + 1 by omega]
  let LX : Shares C E := fun T => liftedPart (x (K.owner T)) (·.x) T
  let LY : Shares C E := fun T => liftedPart (x (K.owner T)) (·.y) T
  let LZ : Shares C E := fun T => liftedPart (x (K.owner T)) (·.z) T
  have hag : ∀ i T, i ∈ C.holders T → ∀ (part : Tuple C → Shares C Bit),
      (part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) → liftedPart (E := E) (x i) part T = liftedPart (x (K.owner T)) part T :=
    fun i T hT part hpart => liftedPart_agree hx.1 T i (K.owner T) hT (K.owner_held T) part hpart
  refine slice_bound prims K z₂.1 counts.sum hτ (sliceWidth_pos hpos) sliceBits 0 (by simp) _ _ _
    (fun T k => wordWeightOf K z₂.1 counts.sum k * LX T k) LY
    (fun i T hT => ⟨by funext k; simp only [LX, hag i T hT (·.x) (Or.inl rfl)],
      hag i T hT (·.y) (Or.inr (Or.inl rfl))⟩) ?_ _ (histAgree_filled hx.1) 1 1 {k₂} (by simp) z₂.2 hok₂ 1
  refine (isShamir_conv (claimOf K z₂.1 counts.sum LZ) 0).congr (fun i => (conv_congr i _ _ 0 fun T hT => by
    simp only [claimOf, LZ, hag i T hT (·.z) (Or.inr (Or.inr rfl))]).symm) ?_
  simp only [claimOf, Nat.sub_zero]
  rw [Finset.sum_comm, mul_comm (sliceWidth counts.sum)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, lifted_product hx k, ← Finset.mul_sum]
  simp only [sliceOf, LX, LY]
  ring

end HonestCheck

end

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section Completeness

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

theorem two_mul_sum_range_succ : ∀ n : ℕ, 2 * ∑ j ∈ range n, (1 + j) = n * (n + 1)
  | 0 => by simp
  | n + 1 => by rw [Finset.sum_range_succ, mul_add, two_mul_sum_range_succ n]; ring

omit [DecidableEq E] [Algebra Bit E] in
theorem chalErr_toReal_le (R : ℕ) :
    ((sliceBits : ℝ≥0∞) / Fintype.card E + chalErr E 1 (R + 1)).toReal ≤ abortErrorOf (E := E) R := by
  have hE : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos_iff.2 ⟨0⟩
  have hE' : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fintype.card_pos_iff.2 ⟨(0 : E)⟩).ne'
  have hfin : ∀ j : ℕ, (((1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) ≠ ⊤ := fun j =>
    ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (by simp) (by simp),
      ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) hE')⟩
  unfold chalErr abortErrorOf coinFailure coinKeyCollision
  rw [ENNReal.toReal_add (ENNReal.div_ne_top (by simp) hE') (ENNReal.sum_ne_top.2 fun j _ => hfin j),
    ENNReal.toReal_sum fun j _ => hfin j]
  have hterm : ∀ j : ℕ, (((1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries).toReal =
      ((1 + j : ℕ) : ℝ) / 2 ^ 256 + (2 / (Fintype.card E : ℝ)) ^ challengeTries := fun j => by
    rw [ENNReal.toReal_add (ENNReal.div_ne_top (by simp) (by simp))
      (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) hE'))]
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_natCast]
    norm_num
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_div]
  have hsum : (∑ j ∈ range (R + 1), ((1 + j : ℕ) : ℝ)) ≤ ((R + 2) ^ 2 : ℕ) / 2 := by
    have h := two_mul_sum_range_succ (R + 1)
    have h' : (2 : ℝ) * ∑ j ∈ range (R + 1), ((1 + j : ℕ) : ℝ) = ((R + 1) * (R + 1 + 1) : ℕ) := by
      rw [← h]; push_cast; rfl
    rw [le_div_iff₀ (by norm_num), mul_comm, h']
    push_cast
    nlinarith
  have h256 : (0 : ℝ) < 2 ^ 256 := by positivity
  have : (∑ j ∈ range (R + 1), ((1 + j : ℕ) : ℝ)) / 2 ^ 256 ≤ (((R + 2) ^ 2 : ℕ) : ℝ) / 2 ^ 257 :=
    calc (∑ j ∈ range (R + 1), ((1 + j : ℕ) : ℝ)) / 2 ^ 256
        ≤ ((((R + 2) ^ 2 : ℕ) : ℝ) / 2) / 2 ^ 256 := by gcongr
      _ = (((R + 2) ^ 2 : ℕ) : ℝ) / 2 ^ 257 := by rw [div_div, show (2 : ℝ) * 2 ^ 256 = 2 ^ 257 from (pow_succ' 2 256).symm]
  push_cast at this ⊢
  linarith

/-- An honest check accepts correct tuples, except when it aborts on a coin. -/
theorem multVerifyCompleteness [SampleableType E] (prims : Primitives) (K : Constants C E) :
    MultVerifyCompletenessStatement prims K := by
  refine multVerifyCompleteness_of_abort_bound prims K fun counts x hx => ?_
  haveI : Nonempty C.Party := ⟨⟨0, by have := C.one_le_t; unfold Committee.n; omega⟩⟩
  by_cases hpos : counts.sum = 0
  · have hcnt : ∀ i, ((x i).map (·.count)).sum = 0 := fun i => by rw [tupleInputs_count hx.1 i, hpos]
    have hprog : ∀ i, checkProtocol K i (x i) = pure () := fun i => by
      simp [checkProtocol, check, hcnt i, StateT.run'_eq]
    simp only [hprog, honestRounds_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
      probEvent_pure, ne_eq, not_true_eq_false, if_false, ENNReal.toReal_zero]
    unfold abortErrorOf coinFailure coinKeyCollision
    positivity
  · refine (ENNReal.toReal_mono ?_ (check_honest_bound prims K counts x hx hpos)).trans (chalErr_toReal_le _)
    refine ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (by simp) ?_, ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (by simp) (by simp), ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) ?_)⟩⟩
    all_goals exact_mod_cast (Fintype.card_pos_iff.2 ⟨(0 : E)⟩).ne'

end Completeness

end

end ThresholdLeanXmssSecurity

/-! ## The soundness of one challenge -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section ChallengeSoundness

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] (prims : Primitives)

/-- A bind meets `q` with the probability of `p₁` plus `B` times the probability of `p₂`, when each
continuation meets `q` with probability at most `1` on `p₁` and at most `B` on `p₂`. -/
theorem probEvent_bind_le_split {α β : Type} {mx : ProbComp α} {my : α → ProbComp β} {q : β → Prop}
    (p₁ p₂ : α → Prop) [DecidablePred p₁] [DecidablePred p₂] (B : ℝ≥0∞)
    (h : ∀ x ∈ support mx, Pr[q | my x] ≤ (if p₁ x then 1 else 0) + (if p₂ x then B else 0)) :
    Pr[q | mx >>= my] ≤ Pr[p₁ | mx] + Pr[p₂ | mx] * B := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · refine (mul_le_mul' le_rfl (h x hx)).trans (le_of_eq ?_)
    split_ifs <;> simp [mul_add]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

theorem card_add_ratio (a M : ℕ) (hM : M ≠ 0) :
    (a : ℝ≥0∞) / (M + 2 : ℕ) + 2 / (M + 2 : ℕ) * (a / M) = a / M := by
  have hM' : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM
  have hM2 : ((M + 2 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : M + 2 ≠ 0)
  have h1 : (a : ℝ≥0∞) / (M + 2 : ℕ) = (a / M) * ((M : ℝ≥0∞) / (M + 2 : ℕ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc (M : ℝ≥0∞)⁻¹,
      ENNReal.inv_mul_cancel hM' (by simp), one_mul]
  rw [h1, mul_comm (2 / _), ← mul_add, ENNReal.div_add_div_same]
  rw [show ((M : ℝ≥0∞) + 2) = ((M + 2 : ℕ) : ℝ≥0∞) by push_cast; rfl, ENNReal.div_self hM2 (by simp), mul_one]

/-- A challenge search on a key with no cached expansion returns a value of `S` with probability at
most `|S| / (|E| - 2)`. -/
theorem probEvent_findChallenge_mem (K : Constants C E) (key : HashOutput) (S : Finset E) :
    ∀ (tries index : ℕ) (s : HashCache C), (∀ i ≥ index, s (.expand key i) = none) →
      Pr[fun z => ∃ e ∈ S, z.1 = some e | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key tries index)).run s] ≤ S.card / (Fintype.card E - 2 : ℕ) := by
  have hcard : 2 < Fintype.card E := by rw [card_field K]; simp [elementBits]
  intro tries
  induction tries with
  | zero => intro index s _; simp [findChallenge]
  | succ tries ih =>
    intro index s hs
    have hq : ¬ IsFixed (C := C) (.expand key index) := by rintro ⟨_, h, _⟩; cases h
    rw [findChallenge, simulateQ_bind, StateT.run_bind, simulateQ_hashQuery_run_fresh prims hq (hs index le_rfl),
      bind_map_left]
    refine (probEvent_bind_le_split (fun u => elementOfHash K u ∈ S) (fun u => ¬ (elementOfHash K u ≠ 0 ∧
      elementOfHash K u ≠ 1)) (S.card / (Fintype.card E - 2 : ℕ)) fun u _ => ?_).trans ?_
    · dsimp only
      split
      · rename_i hne _
        simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, Option.some.injEq, exists_eq_right']
        exact le_self_add
      · rename_i h01 _
        refine (ih (index + 1) _ fun i hi => ?_).trans ?_
        swap
        · rw [if_pos (show ¬(elementOfHash K u ≠ 0 ∧ elementOfHash K u ≠ 1) from h01)]
          exact le_add_self
        rw [QueryCache.cacheQuery, Function.update_of_ne (by simp; omega)]
        exact hs i (by omega)
    · have hS := probEvent_elementOfHash K (· ∈ S)
      have h01 := probEvent_elementOfHash K (fun e => ¬ (e ≠ 0 ∧ e ≠ 1))
      rw [probEvent_map] at hS h01
      rw [show (fun u => elementOfHash K u ∈ S) = (· ∈ S) ∘ elementOfHash K from rfl, hS,
        show (fun u => ¬ (elementOfHash K u ≠ 0 ∧ elementOfHash K u ≠ 1)) =
          (fun e => ¬ (e ≠ 0 ∧ e ≠ 1)) ∘ elementOfHash K from rfl, h01, card_zero_one,
        show (Finset.univ.filter (· ∈ S)) = S by ext; simp]
      obtain ⟨M, hM⟩ : ∃ M, Fintype.card E = M + 2 := ⟨Fintype.card E - 2, by omega⟩
      rw [hM, Nat.add_sub_cancel]
      simpa using (card_add_ratio S.card M (by omega)).le

/-- A challenge on a fresh coin key lands in `S` with probability at most
`|Ks| / 2^256 + |S| / (|E| - 2)`, when the cache holds expansions only of the keys `Ks`. The first term
is a key that collides with an earlier key. -/
theorem challengeQuery_mem_le (K : Constants C E) (tag ρ : ℕ) (v : List E) (Ks : Finset HashOutput) (L : ℕ)
    (hρ : L ≤ ρ) (s : HashCache C) (hs : CacheOK Ks L s) (S : Finset E) :
    Pr[fun z => ∃ e ∈ S, z.1 = some e |
      (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag ρ v) (LocalSpec C))).run s] ≤
      Ks.card / 2 ^ 256 + S.card / (Fintype.card E - 2 : ℕ) := by
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  have hfresh := coinKey_fresh hρ hs tag (v.flatMap fun v => List.ofFn (K.encode v))
  rw [simulateQ_localAnswer_liftComp, challengeQuery, simulateQ_bind, StateT.run_bind]
  have hev : ∀ mx : ProbComp (Option E × HashCache C),
      Pr[fun z => ∃ e ∈ S, z.1 = some e | mx] = Pr[fun z => ¬ ¬ ∃ e ∈ S, z.1 = some e | mx] := fun mx => by simp
  rw [hev]
  refine probEvent_bind_le_add (p := fun z : HashOutput × HashCache C => z.1 ∉ Ks) ?_ fun z hz hkey => ?_
  · simp only [not_not]
    exact probEvent_hash_fresh_mem prims hq hfresh Ks
  · rw [← hev]
    refine probEvent_findChallenge_mem prims K z.1 S challengeTries 0 z.2 fun i _ => ?_
    by_contra hne
    rcases support_hashQuery_entries prims hq s z hz _ hne with h | h
    · exact hkey ((hs _ h).1 _ i rfl)
    · cases h

end ChallengeSoundness

end

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

attribute [local instance] inhabitedField

/-- The dummy inputs of the honest operators. They keep the leaked views of the known terms, and the
first lacked term carries the leaked difference of each tuple. -/
def dummyTuples (D : C.Coalition) (known : C.Party → Option (List (Tuple C))) (differences : List (ℕ → Bit))
    (i : C.Party) : List (Tuple C) :=
  ((known i).getD []).zipIdx.map fun (τ, k) =>
    match lackedTerm D.1 with
    | some T₀ => ⟨τ.x, τ.y, fun T g => if T = T₀ then
        (differences.getD k fun _ => 0) g + shareValue τ.x g * shareValue τ.y g - ∑ T' ∈ univ.erase T₀, τ.z T' g
        else τ.z T g, τ.count, τ.mode⟩
    | none => τ

/-- The simulator of the check. It runs the adversary against the honest operators on the dummy inputs,
and the honest operators that accept receive the output of `F_multVerify`. -/
def checkSimulator (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : Adversary C E (List (Tuple C)) ((List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit))
      ((Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
        ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit))))) :
    Simulator (C := C) (LocalSpec C) (List (Tuple C))
      ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (Finset C.Party) A.State where
  State := A.State
  start x z := A.start x z
  answer st leak := do
    let r ← executePhase localRoles D A (checkFunctionalities K) fuel st
      fun i => checkProtocol K i (dummyTuples D leak.1 leak.2.1 i)
    pure (r.1, univ.filter fun i => r.2 i = some ())
  output st := pure st

end ThresholdLeanXmssSecurity

end
end

/-! ## Query -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- Every path through the challenge search uses at most its number of tries. -/
theorem findChallenge_queryBound (K : Constants C E) (key : HashOutput) :
    ∀ tries index, IsQueryBoundP (findChallenge K key tries index) (fun _ => True) tries := by
  intro tries
  induction tries with
  | zero => intro index; simp [findChallenge]
  | succ tries ih =>
    intro index
    unfold findChallenge
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl (.expand key index))) >>= _) _ _
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · simp
    · intro u
      simp only [if_pos trivial, Nat.add_sub_cancel]
      split
      · simp
      · simpa using ih (index + 1)

/-- Mapping a list costs at most its length times the per-entry bound. -/
theorem queryBound_mapM {ι α β : Type} {S : OracleSpec ι} (p : ι → Prop) [DecidablePred p]
    (f : α → OracleComp S β) (n : ℕ) : ∀ xs : List α,
    (∀ x ∈ xs, IsQueryBoundP (f x) p n) → IsQueryBoundP (xs.mapM f) p (xs.length * n)
  | [], _ => by simp
  | a :: xs, h => by
    rw [List.mapM_cons]
    have htail := queryBound_mapM p f n xs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hb := isQueryBoundP_bind (h a (List.mem_cons_self ..)) (fun y _ =>
      isQueryBoundP_bind htail (fun ys _ => isQueryBoundP_pure p (y :: ys) 0))
    simpa [Nat.succ_mul, Nat.add_comm] using hb

/-- The key query plus at most `challengeTries` expansion queries. -/
theorem challengeQuery_queryBound (K : Constants C E) (tag label : ℕ) (v : List E) :
    IsQueryBoundP (challengeQuery K tag label v) (fun _ => True) (1 + challengeTries) := by
  unfold challengeQuery
  apply isQueryBoundP_bind
  · change IsQueryBoundP (liftM (OracleSpec.query (spec := RoSpec C) (.inl _))) _ 1
    exact (isQueryBoundP_query_iff _ _ _).2 (by omega)
  · intro key _
    exact findChallenge_queryBound K key _ _

/-- A single random-oracle input consumes one query. -/
theorem hashQuery_queryBound (q : Query C) :
    IsQueryBoundP (hashQuery q) (fun _ => True) 1 := by
  change IsQueryBoundP (liftM (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 1
  exact (isQueryBoundP_query_iff _ _ _).2 (by omega)

/-- The de-linearization expansion uses one key query and `count` expansions. -/
theorem tauQuery_queryBound (K : Constants C E) (tag label : ℕ) (v : List E) (count : ℕ) :
    IsQueryBoundP (tauQuery K tag label v count) (fun _ => True) (1 + count) := by
  unfold tauQuery
  apply isQueryBoundP_bind (hashQuery_queryBound _)
  intro key _
  simpa using queryBound_mapM (fun _ => True)
    (fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)) 1 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff ..).2 (hashQuery_queryBound _))

/-- Two hashes for each term suffice for the salted digest list. -/
theorem digestQuery_queryBound (i : C.Party) (salts : Shares C Bit) (h : C.Term → List Bit) :
    IsQueryBoundP (digestQuery i salts h) (fun _ => True) (2 * C.terms.length) := by
  unfold digestQuery
  rw [Nat.mul_comm]
  apply queryBound_mapM
  intro T _
  split_ifs
  · exact isQueryBoundP_bind (hashQuery_queryBound _) (fun u _ => hashQuery_queryBound _)
  · exact isQueryBoundP_pure _ _ _

/-- Count the local oracle calls in a party program; rounds and hybrid calls are free. -/
def PartyCounted {ι : Type} {G : OracleSpec ι} : (PartySpec C E G).Domain → Prop
  | .inl (.inl (.inr _)) => True
  | _ => False

/-- A bound on every path through a party program. -/
def PartyBound {ι α : Type} {G : OracleSpec ι} (p : PartyM C E G α) (n : ℕ) : Prop :=
  IsQueryBoundP p.run (PartyCounted (G := G)) n

/-- A bound independent of the history and round label. -/
def RunBound {ι α : Type} {G : OracleSpec ι} (p : RunM C E G α) (n : ℕ) : Prop :=
  ∀ st, PartyBound (p.run st) n

section PartyBounds
variable {ι α β : Type} {G : OracleSpec ι}

lemma PartyBound.mono {p : PartyM C E G α} {n m : ℕ} (h : PartyBound p n) (hnm : n ≤ m) :
    PartyBound p m := IsQueryBoundP.mono h hnm

lemma PartyBound.pure (a : α) : PartyBound (pure a : PartyM C E G α) 0 := by
  exact isQueryBoundP_pure _ _ _

lemma PartyBound.failure : PartyBound (failure : PartyM C E G α) 0 := by
  exact isQueryBoundP_pure _ _ _

lemma PartyBound.bind {p : PartyM C E G α} {f : α → PartyM C E G β} {n m : ℕ}
    (h : PartyBound p n) (hf : ∀ a, PartyBound (f a) m) : PartyBound (p >>= f) (n + m) := by
  unfold PartyBound
  simp only [OptionT.run_bind]
  apply isQueryBoundP_bind h
  intro a _
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some a => exact hf a

lemma PartyBound.liftQuery (t : (PartySpec C E G).Domain) (ht : ¬ PartyCounted (G := G) t) :
    PartyBound (OptionT.lift (OracleComp.lift (OracleSpec.query t)) : PartyM C E G _) 0 := by
  unfold PartyBound
  change IsQueryBoundP (some <$> (liftM (OracleSpec.query t) : OracleComp (PartySpec C E G) _)) _ 0
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  exact fun h => False.elim (ht h)

lemma PartyBound.require (p : Prop) : PartyBound (require p : PartyM C E G Unit) 0 := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact PartyBound.pure ()
  · exact PartyBound.failure

lemma PartyBound.call (input : ι) : PartyBound (call input : PartyM C E G _) 0 :=
  PartyBound.liftQuery _ (by simp [PartyCounted])

lemma PartyBound.exchange (outbox : Mail C E) : PartyBound (exchange outbox : PartyM C E G _) 0 := by
  unfold ThresholdLeanXmss.exchange
  apply (PartyBound.bind (m := 0) (PartyBound.liftQuery _ (by simp [PartyCounted])) (fun inbox => ?_)).mono (by omega)
  split_ifs
  · exact PartyBound.failure
  · exact PartyBound.pure _

lemma RunBound.pure (a : α) : RunBound (pure a : RunM C E G α) 0 :=
  fun _ => PartyBound.pure _

lemma RunBound.bind {p : RunM C E G α} {f : α → RunM C E G β} {n m : ℕ}
    (h : RunBound p n) (hf : ∀ a, RunBound (f a) m) : RunBound (p >>= f) (n + m) := by
  intro st
  exact PartyBound.bind (h st) (fun a => hf a.1 a.2)

lemma RunBound.mono {p : RunM C E G α} {n m : ℕ} (h : RunBound p n) (hnm : n ≤ m) :
    RunBound p m := fun st => (h st).mono hnm

lemma RunBound.lift {p : PartyM C E G α} {n : ℕ} (h : PartyBound p n) :
    RunBound (StateT.lift p : RunM C E G α) n := by
  intro st
  change PartyBound (p >>= fun a => Pure.pure (a, st)) n
  simpa using PartyBound.bind h (fun a => PartyBound.pure (a, st))

lemma RunBound.get : RunBound (get : RunM C E G (RunState C)) 0 :=
  fun _ => PartyBound.pure _

lemma RunBound.modifyGet (f : RunState C → α × RunState C) :
    RunBound (modifyGet f : RunM C E G α) 0 := fun _ => PartyBound.pure _

lemma RunBound.modify (f : RunState C → RunState C) :
    RunBound (modify f : RunM C E G Unit) 0 := fun _ => PartyBound.pure _

lemma RunBound.foldlM {γ : Type} (f : α → γ → RunM C E G α) (n : ℕ)
    (hf : ∀ a g, RunBound (f a g) n) : ∀ (xs : List γ) (a : α),
    RunBound (xs.foldlM f a) (xs.length * n)
  | [], a => by simpa using RunBound.pure a
  | g :: xs, a => by
    rw [List.foldlM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using (hf a g).bind (fun a' => RunBound.foldlM f n hf xs a')

lemma oracleStep_queryBound {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun _ => True) n) : PartyBound (oracleStep oa : PartyM C E G α) n := by
  unfold PartyBound oracleStep localStep
  change IsQueryBoundP (some <$> liftComp (liftComp oa (LocalSpec C)) (PartySpec C E G)) _ n
  rw [isQueryBoundP_map_iff]
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [liftComp_bind]
    have e : liftComp (liftComp (liftM (OracleSpec.query (spec := RoSpec C) t) : OracleComp (RoSpec C) _) (LocalSpec C)) (PartySpec C E G) =
        (liftM (OracleSpec.query (spec := PartySpec C E G) (.inl (.inl (.inr t)))) : OracleComp (PartySpec C E G) _) := by
      rcases t with q | p <;> rfl
    rw [e]
    erw [isQueryBoundP_query_bind_iff]
    simpa [PartyCounted] using And.intro (h.1) (fun u => ih u (h.2 u))

lemma RunBound.run' {p : RunM C E G α} {n : ℕ} (h : RunBound p n) (st : RunState C) :
    PartyBound (p.run' st) n := by
  unfold StateT.run'
  exact (PartyBound.bind (h st) (fun a => PartyBound.pure a.1)).mono (by omega)

lemma RunBound.openSh (K : Constants C E) (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    PartyBound (openSh K ctx v count : PartyM C E G _) 0 := by
  unfold ThresholdLeanXmss.openSh
  exact ((PartyBound.exchange _).bind (fun inbox =>
    (PartyBound.require _).bind (fun _ => PartyBound.pure _))).mono (by omega)

lemma RunBound.freshLabel : RunBound (freshLabel : RunM C E G ℕ) 0 :=
  RunBound.modifyGet _

lemma RunBound.record {R : Type} (K : Constants C E) (ctx : Context C)
    (codec : Codec C E R) (mode : ReshareMode) (z : Shares C R) (count : ℕ) :
    RunBound (record K ctx codec mode z count : RunM C E G Unit) 0 := RunBound.modify _

end PartyBounds

section CheckBounds
variable (K : Constants C E) (i : C.Party)

lemma hybrid_coin_queryBound (count : ℕ) :
    RunBound ((hybridCheckGadgets K i).coin count) 0 := by
  unfold hybridCheckGadgets
  apply (RunBound.bind (m := 0) RunBound.freshLabel (fun _ => ?_)).mono (by omega)
  apply (RunBound.bind (m := 0) (RunBound.lift (PartyBound.call _)) (fun out => ?_)).mono (by omega)
  split
  · exact RunBound.pure _
  · exact RunBound.lift PartyBound.failure

lemma hybrid_extendMult_queryBound (products : List (Product C E)) :
    RunBound ((hybridCheckGadgets K i).extendMult products) 0 := by
  unfold hybridCheckGadgets
  apply (RunBound.bind (m := 0) RunBound.freshLabel (fun _ => ?_)).mono (by omega)
  apply (RunBound.bind (m := 0) (RunBound.lift (PartyBound.call _)) (fun out => ?_)).mono (by omega)
  split
  · exact ((RunBound.record _ _ _ _ _ _).bind (fun _ => RunBound.pure _)).mono (by omega)
  · exact RunBound.lift PartyBound.failure

lemma hybrid_randElements_queryBound (count : ℕ) :
    RunBound ((hybridCheckGadgets K i).randElements count) 0 := by
  unfold hybridCheckGadgets
  apply (RunBound.bind (m := 0) RunBound.freshLabel (fun _ => ?_)).mono (by omega)
  apply (RunBound.bind (m := 0) (RunBound.lift (PartyBound.call _)) (fun out => ?_)).mono (by omega)
  split
  · exact RunBound.pure _
  · exact RunBound.lift PartyBound.failure

lemma hybrid_randBits_queryBound (count : ℕ) :
    RunBound ((hybridCheckGadgets K i).randBits count) 0 := by
  unfold hybridCheckGadgets
  apply (RunBound.bind (m := 0) RunBound.freshLabel (fun _ => ?_)).mono (by omega)
  apply (RunBound.bind (m := 0) (RunBound.lift (PartyBound.call _)) (fun out => ?_)).mono (by omega)
  split
  · exact RunBound.pure _
  · exact RunBound.lift PartyBound.failure

lemma hybrid_coinKey_queryBound :
    RunBound (coinKey K (hybridCheckGadgets K i)) 1 := by
  unfold coinKey
  exact ((RunBound.get).bind (fun st =>
    (hybrid_coin_queryBound K i 1).bind (fun values =>
      RunBound.lift (oracleStep_queryBound (hashQuery_queryBound _))))).mono (by omega)

lemma expand_queryBound {ι : Type} {G : OracleSpec ι} (key : HashOutput) (count : ℕ) :
    RunBound (expand K key count : RunM C E G (List E)) count := by
  unfold expand
  apply RunBound.lift
  apply oracleStep_queryBound
  simpa using queryBound_mapM (fun _ => True)
    (fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)) 1 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff ..).2 (hashQuery_queryBound _))

lemma hybrid_challenge_queryBound :
    RunBound (challenge K (hybridCheckGadgets K i)) (1 + challengeTries) := by
  unfold challenge
  refine ((hybrid_coinKey_queryBound K i).bind (fun key =>
    (RunBound.lift (oracleStep_queryBound (findChallenge_queryBound K key challengeTries 0))).bind
      (m := 0) (fun out => ?_))).mono (by omega)
  split
  · exact RunBound.pure _
  · exact RunBound.lift PartyBound.failure

lemma compareDigests_queryBound {ι : Type} {G : OracleSpec ι} (salts : Shares C Bit) :
    RunBound (compareDigests (localContext i) salts : RunM C E G Unit) (2 * C.terms.length) := by
  unfold compareDigests
  refine ((RunBound.get).bind (fun st =>
    (RunBound.lift (oracleStep_queryBound (digestQuery_queryBound i salts st.history))).bind (fun ds =>
      (RunBound.lift (PartyBound.exchange _)).bind (fun inbox =>
        RunBound.lift (PartyBound.require _))))).mono (by omega)

lemma sliceStep_queryBound (τ : List E) (count : ℕ) (v : Shares C E × Shares C E × E) (j : ℕ) :
    RunBound (sliceStep K (localContext i) (hybridCheckGadgets K i) τ count v j) (1 + challengeTries) := by
  rcases v with ⟨xs, ys, D⟩
  unfold sliceStep
  exact ((hybrid_extendMult_queryBound K i _).bind (fun t =>
    (hybrid_challenge_queryBound K i).bind (fun r => RunBound.pure _))).mono (by omega)

lemma halvingStep_queryBound (width : ℕ) (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    RunBound (halvingStep K (localContext i) (hybridCheckGadgets K i) width v j) (1 + challengeTries) := by
  rcases v with ⟨A, B, D⟩
  unfold halvingStep
  exact ((hybrid_extendMult_queryBound K i _).bind (fun t =>
    (hybrid_challenge_queryBound K i).bind (fun r => RunBound.pure _))).mono (by omega)

lemma finalStep_queryBound (v : (ℕ → E) × (ℕ → E) × E) :
    RunBound (finalStep K (localContext i) (hybridCheckGadgets K i) v)
      (2 * C.terms.length + (1 + challengeTries)) := by
  rcases v with ⟨A, B, D⟩
  unfold finalStep
  exact ((hybrid_randElements_queryBound K i 2).bind (fun w =>
    (hybrid_extendMult_queryBound K i _).bind (fun q =>
      (hybrid_randBits_queryBound K i 256).bind (fun salts =>
        (compareDigests_queryBound i salts.1).bind (fun _ =>
          (hybrid_challenge_queryBound K i).bind (fun r =>
            (RunBound.lift (RunBound.openSh K _ _ _)).bind (fun opened =>
              RunBound.lift (PartyBound.require _)))))))).mono (by omega)

/-- The query budget of one operator, including all branches that abort early. -/
theorem check_queryBound (tuples : List (Tuple C)) :
    RunBound (check K (localContext i) (hybridCheckGadgets K i) tuples)
      (halvings (tuples.map (·.count)).sum + 2 + coins (tuples.map (·.count)).sum +
        (halvings (tuples.map (·.count)).sum + 1) * challengeTries + 2 * C.terms.length) := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact (RunBound.pure ()).mono (Nat.zero_le _)
  · rw [check_eq _ _ _ _ hz]
    refine ((hybrid_coinKey_queryBound K i).bind (fun key =>
      (expand_queryBound K key _).bind (fun τ =>
        (RunBound.lift (PartyBound.require _)).bind (fun _ =>
          (RunBound.foldlM _ _ (sliceStep_queryBound K i τ _) _ _).bind (fun v =>
            (RunBound.foldlM _ _ (halvingStep_queryBound K i _) _ _).bind (fun v' =>
              finalStep_queryBound K i v')))))).mono ?_
    simp only [List.length_range]
    have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by unfold halvings; omega
    have he : sliceBits + (halvings (tuples.map (·.count)).sum - sliceBits) =
        halvings (tuples.map (·.count)).sum := by omega
    nlinarith [congrArg (fun n => n * (1 + challengeTries)) he]

/-- The protocol wrapper only initializes the local history and round label. -/
theorem checkProtocol_queryBound (tuples : List (Tuple C)) :
    PartyBound (checkProtocol K i tuples)
      (halvings (tuples.map (·.count)).sum + 2 + coins (tuples.map (·.count)).sum +
        (halvings (tuples.map (·.count)).sum + 1) * challengeTries + 2 * C.terms.length) :=
  (check_queryBound K i tuples).run' _

end CheckBounds

end ThresholdLeanXmssSecurity
end

/-! ## Network -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β : Type}

/-- The local budget remaining after the next round or hybrid call. -/
def StepBound (st : Step C E G α) (n : ℕ) : Prop :=
  match st with
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyCounted (E := E) (G := G)) n
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyCounted (E := E) (G := G)) n

/-- Advancing a party spends only its local budget, leaving the residual budget for its continuation. -/
theorem advance_bind_queryBound (oa : OracleComp (PartySpec C E G) (Option α))
    (k : Step C E G α → OracleComp (LocalSpec C) β) (extra : ℕ) :
    ∀ n, IsQueryBoundP oa (PartyCounted (E := E) (G := G)) n →
      (∀ st b, b ≤ n → StepBound st b → IsQueryBoundP (k st) Counted (extra + b)) →
      IsQueryBoundP (advance oa >>= k) Counted (extra + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ hk
    rw [advance_pure, pure_bind]
    exact hk (.done a) n le_rfl trivial
  | query_bind t f ih =>
    intro n h hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · rw [advance_query_bind, bind_assoc, isQueryBoundP_query_bind_iff]
      have hcp : Counted q → PartyCounted (E := E) (G := G) (.inl (.inl q)) := by
        rcases q with u | v <;> simp [Counted, PartyCounted]
      constructor
      · by_cases hc : Counted q
        · right
          have hn := h.1.resolve_left (not_not.mpr (hcp hc))
          omega
        · exact Or.inl hc
      · intro u
        have hb : (if PartyCounted (E := E) (G := G) (.inl (.inl q)) then n - 1 else n) ≤ n := by
          split_ifs <;> omega
        have hi := ih u _ (h.2 u) (fun st b hb' hs => hk st b (hb'.trans hb) hs)
        apply hi.mono
        by_cases hp : PartyCounted (E := E) (G := G) (.inl (.inl q))
        · by_cases hc : Counted q
          · simp only [if_pos hp, if_pos hc]
            have hn := h.1.resolve_left (not_not.mpr hp)
            omega
          · simp only [if_pos hp, if_neg hc]
            omega
        · have hc : ¬ Counted q := fun hc => hp (hcp hc)
          simp only [if_neg hp, if_neg hc]
          exact le_rfl
    · change IsQueryBoundP (k (.wait outbox f)) Counted (extra + n)
      apply hk _ n le_rfl
      simpa [StepBound, PartyCounted] using h.2
    · change IsQueryBoundP (k (.call input f)) Counted (extra + n)
      apply hk _ n le_rfl
      simpa [StepBound, PartyCounted] using h.2

/-- Advance the parties sequentially while accounting for each residual budget. -/
theorem sequenceFin_advance_bind_queryBound : ∀ {N : ℕ}
    (oa : Fin N → OracleComp (PartySpec C E G) (Option α)) (budget : Fin N → ℕ)
    (h : ∀ i, IsQueryBoundP (oa i) (PartyCounted (E := E) (G := G)) (budget i))
    (k : (Fin N → Step C E G α) → OracleComp (LocalSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ), (∀ i, b i ≤ budget i) → (∀ i, StepBound (st i) (b i)) →
      IsQueryBoundP (k st) Counted (extra + ∑ i, b i)) →
    IsQueryBoundP ((Concrete.sequenceFin fun i => advance (oa i)) >>= k) Counted
      (extra + ∑ i, budget i)
  | 0, oa, budget, h, k, extra, hk => by
    simp only [Concrete.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, h, k, extra, hk => by
    simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
    rw [Fin.sum_univ_succ]
    have he : extra + (budget 0 + ∑ i : Fin N, budget i.succ) =
        (extra + ∑ i : Fin N, budget i.succ) + budget 0 := by omega
    rw [he]
    refine advance_bind_queryBound (oa 0) _ _ (budget 0) (h 0) (fun st0 b0 hb0 hs0 => ?_)
    have he' : (extra + ∑ i : Fin N, budget i.succ) + b0 =
        (extra + b0) + ∑ i : Fin N, budget i.succ := by omega
    rw [he']
    refine sequenceFin_advance_bind_queryBound (fun i : Fin N => oa i.succ) (fun i => budget i.succ)
      (fun i => h i.succ) (fun st => k (Fin.cases st0 st)) (extra + b0) (fun st b hb hs => ?_)
    have hp := hk (Fin.cases st0 st) (Fin.cases b0 b)
      (fun i => Fin.cases hb0 hb i) (fun i => Fin.cases hs0 hs i)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hp

section NetworkBound
variable {I O Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R)

def roundResume (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E (CallSpec I O) α) (j : C.Party) :
    OracleComp (PartySpec C E (CallSpec I O)) (Option α) :=
  match steps j with
  | .done out => pure out
  | .wait _ resume => if j ∈ D.1 then pure none else
      resume fun k => if k ∈ D.1 then sent k j else (steps k).delivered j
  | .call _ _ => pure none

def callResume (outputs : C.Party → Option O)
    (steps : C.Party → Step C E (CallSpec I O) α) (j : C.Party) :
    OracleComp (PartySpec C E (CallSpec I O)) (Option α) :=
  match steps j with
  | .call _ resume => if j ∈ D.1 then pure none else resume (outputs j)
  | .done out => pure out
  | .wait outbox resume => OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E (CallSpec I O)) (.inl (.inr outbox))) >>= resume

lemma roundResume_bound (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBound (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (roundResume D sent steps j) (PartyCounted (E := E) (G := CallSpec I O)) (budget j) := by
  have hj := h j
  unfold roundResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k => exact isQueryBoundP_pure _ _ _
  | wait out k =>
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [StepBound, hs] at hj
      exact hj _

lemma callResume_bound (out : C.Party → Option O)
    (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBound (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (callResume D out steps j) (PartyCounted (E := E) (G := CallSpec I O)) (budget j) := by
  have hj := h j
  unfold callResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k =>
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [StepBound, hs] at hj
      exact hj _
  | wait out k =>
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · exact Or.inl (by simp [PartyCounted])
    · simpa [StepBound, hs, PartyCounted] using hj

lemma stepRound_bind_queryBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) Counted step)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBound (steps j) (budget j))
    (k : (A.State × (C.Party → Step C E (CallSpec I O) α) × (C.Party → C.Party → Option (Msg E))) →
      OracleComp (LocalSpec C) β) (extra : ℕ)
    (hk : ∀ st (b : C.Party → ℕ), (∀ j, b j ≤ budget j) → (∀ j, StepBound (st.2.1 j) (b j)) →
      IsQueryBoundP (k st) Counted (extra + ∑ j, b j)) :
    IsQueryBoundP (stepRound localRoles D A F state steps >>= k) Counted (step + extra + ∑ j, budget j) := by
  unfold stepRound
  split_ifs
  · simp only [bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j) (hF _ _) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .call _ resume => if j ∈ D.1 then pure (Step.done none) else advance (resume (result.2 j))
        | st => pure st) = fun j => advance (callResume D result.2 steps j) := by
      funext j
      cases hs : steps j with
      | done out => simp only [callResume, hs]; rfl
      | wait out k => simp only [callResume, hs]; rfl
      | call input k => simp only [callResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_advance_bind_queryBound
      (fun j => callResume D result.2 steps j) budget (callResume_bound D result.2 steps budget h)
      (fun st => k (result.1, st, fun _ _ => none)) extra
      (fun st b hb hs => hk (result.1, st, fun _ _ => none) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) =>
      IsQueryBoundP (Concrete.sequenceFin f >>= fun st => k (result.1, st, fun _ _ => none))
        Counted (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl
  · simp only [localRoles, bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j) (hr _ _) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .done out => pure (Step.done out)
        | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
            advance (resume fun k => if k ∈ D.1 then result.2 k j else (steps k).delivered j)
        | .call _ _ => pure (Step.done none)) = fun j => advance (roundResume D result.2 steps j) := by
      funext j
      cases hs : steps j with
      | done out => simp only [roundResume, hs]; rfl
      | call input k => simp only [roundResume, hs]; rfl
      | wait out k => simp only [roundResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_advance_bind_queryBound
      (fun j => roundResume D result.2 steps j) budget (roundResume_bound D result.2 steps budget h)
      (fun st => k (result.1, st, result.2)) extra
      (fun st b hb hs => hk (result.1, st, result.2) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) =>
      IsQueryBoundP (Concrete.sequenceFin f >>= fun st => k (result.1, st, result.2))
        Counted (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl

lemma executeRounds_queryBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) Counted step) :
    ∀ fuel state (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ),
      (∀ j, StepBound (steps j) (budget j)) →
      IsQueryBoundP (executeRounds localRoles D A F fuel state steps) Counted (fuel * step + ∑ j, budget j)
  | 0, state, steps, budget, h => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, budget, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine (stepRound_bind_queryBound D A F step hr hF state steps budget h _ (fuel * step) ?_).mono ?_
      · intro st b hb hs
        exact executeRounds_queryBound step hr hF fuel st.1 st.2.1 b hs
      · simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma executePhase_queryBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) Counted step)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec I O) α)
    (budget : C.Party → ℕ) (hp : ∀ j, j ∉ D.1 → PartyBound (program j) (budget j)) :
    IsQueryBoundP (executePhase localRoles D A F fuel state program) Counted (fuel * step + ∑ j, budget j) := by
  unfold executePhase startSteps
  simp only [localRoles]
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else advance (program i).run) =
      fun i => advance (if i ∈ D.1 then pure none else (program i).run) := by
    funext i
    split_ifs <;> rfl
  change IsQueryBoundP ((Concrete.sequenceFin _) >>= _) _ _
  rw [he]
  apply sequenceFin_advance_bind_queryBound _ budget
  · intro j
    split_ifs with hj
    · exact isQueryBoundP_pure _ _ _
    · exact hp j hj
  · intro st b hb hs
    exact executeRounds_queryBound D A F step hr hF fuel state st b hs

end NetworkBound

end ThresholdLeanXmssSecurity
end

/-! ## Functionality -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}

/-- A structural query budget with natural-number weights. -/
def WeightedBound {ι α : Type} {S : OracleSpec ι} (oa : OracleComp S α) (w : ι → ℕ) (n : ℕ) : Prop :=
  IsQueryBound oa n (fun t b => w t ≤ b) (fun t b => b - w t)

section Weighted
variable {ι α β : Type} {S : OracleSpec ι} {w : ι → ℕ}
lemma WeightedBound.pure (a : α) (n : ℕ) : WeightedBound (pure a : OracleComp S α) w n := trivial
lemma WeightedBound.mono {oa : OracleComp S α} {n m : ℕ} (h : WeightedBound oa w n) (hnm : n ≤ m) :
    WeightedBound oa w m := by
  induction oa using OracleComp.inductionOn generalizing n m with
  | pure a => exact WeightedBound.pure _ _
  | query_bind t k ih =>
    change w t ≤ n ∧ ∀ u, WeightedBound (k u) w (n - w t) at h
    change w t ≤ m ∧ ∀ u, WeightedBound (k u) w (m - w t)
    exact ⟨h.1.trans hnm, fun u => ih u (h.2 u) (by omega)⟩
lemma WeightedBound.bind {oa : OracleComp S α} {k : α → OracleComp S β} {n m : ℕ}
    (h : WeightedBound oa w n) (hk : ∀ a, WeightedBound (k a) w m) :
    WeightedBound (oa >>= k) w (n + m) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simpa using (hk a).mono (Nat.le_add_left _ _)
  | query_bind t f ih =>
    change w t ≤ n ∧ ∀ u, WeightedBound (f u) w (n - w t) at h
    rw [bind_assoc]
    change w t ≤ n + m ∧ ∀ u, WeightedBound (f u >>= k) w (n + m - w t)
    refine ⟨by omega, fun u => (ih u (h.2 u)).mono ?_⟩
    omega
lemma WeightedBound.map {oa : OracleComp S α} {n : ℕ} (h : WeightedBound oa w n) (f : α → β) :
    WeightedBound (f <$> oa) w n := by
  unfold WeightedBound at *
  exact (isQueryBound_map_iff ..).2 h
lemma WeightedBound.query (t : ι) :
    WeightedBound (liftM (OracleSpec.query (spec := S) t) : OracleComp S _) w (w t) := by
  unfold WeightedBound
  rw [isQueryBound_query_iff]
lemma WeightedBound.simulateQ {κ : Type} {T : OracleSpec κ} {v : κ → ℕ}
    (impl : QueryImpl S (OracleComp T)) (hi : ∀ t, WeightedBound (impl t) v (w t))
    {oa : OracleComp S α} {n : ℕ} (h : WeightedBound oa w n) :
    WeightedBound (_root_.simulateQ impl oa) v n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact WeightedBound.pure _ _
  | query_bind t k ih =>
    change w t ≤ n ∧ ∀ u, WeightedBound (k u) w (n - w t) at h
    rw [simulateQ_query_bind]
    exact ((hi t).bind (fun u => ih u (h.2 u))).mono (by omega)
lemma WeightedBound.simulateQ_state {κ σ : Type} {T : OracleSpec κ} {p : κ → Prop} [DecidablePred p]
    (impl : QueryImpl S (StateT σ (OracleComp T)))
    (hi : ∀ t s, IsQueryBoundP ((impl t).run s) p (w t))
    {oa : OracleComp S α} {n : ℕ} (h : WeightedBound oa w n) (s : σ) :
    IsQueryBoundP ((_root_.simulateQ impl oa).run s) p n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    change w t ≤ n ∧ ∀ u, WeightedBound (k u) w (n - w t) at h
    rw [simulateQ_query_bind, StateT.run_bind]
    exact (isQueryBoundP_bind (hi t s) (fun u _ => ih u.1 (h.2 u.1) u.2)).mono (by omega)
end Weighted

/-- Local samples cost zero; a leak costs the adversary's per-step budget. -/
def hybridWeight {L : Type} (step : ℕ) : (LocalSpec C).Domain ⊕ L → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => step

section HybridBounds
variable {I O L R α : Type}
lemma hybrid_sample_queryBound (p : ProbComp α) (step : ℕ) :
    WeightedBound (liftComp p (LocalSpec C + (L →ₒ R))) (hybridWeight step) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure]; exact WeightedBound.pure _ _
  | query_bind t k ih =>
    rw [liftComp_bind]
    have ht : WeightedBound
        (liftComp (liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) (LocalSpec C + (L →ₒ R)))
        (hybridWeight step) 0 := by
      change WeightedBound (liftM (OracleSpec.query (spec := LocalSpec C + (L →ₒ R)) (.inl (.inl t))) : OracleComp _ _) _ 0
      exact WeightedBound.query _
    exact ht.bind ih

lemma hybrid_leak_queryBound (l : L) (step : ℕ) :
    WeightedBound (leak (C := C) (R := R) l) (hybridWeight step) step :=
  WeightedBound.query _

lemma Fcoin_queryBound [SampleableType E] (D : C.Coalition) (inputs : C.Party → Option ℕ) (step : ℕ) :
    WeightedBound ((Fcoin (C := C) (E := E)).run D inputs) (hybridWeight step) step := by
  unfold Fcoin sample
  exact ((hybrid_sample_queryBound _ step).bind (fun values =>
    (hybrid_leak_queryBound _ step).bind (fun receivers => WeightedBound.pure _ 0))).mono (by omega)

lemma Frand_queryBound {R : Type} [AddCommGroup R] [SampleableType R]
    (D : C.Coalition) (inputs : C.Party → Option ℕ) (step : ℕ) :
    WeightedBound ((Frand R (C := C)).run D inputs) (hybridWeight step) step := by
  unfold Frand sample
  exact ((hybrid_leak_queryBound _ step).bind (fun known =>
    (hybrid_sample_queryBound _ step).bind (fun fresh =>
      (hybrid_sample_queryBound _ step).bind (fun pair => WeightedBound.pure _ 0)))).mono (by omega)

lemma Fmult_queryBound {In Lk R : Type} [Inhabited In] [Field R] [SampleableType R]
    (count : In → ℕ) (filled : In → C.Term → ℕ → Option C.Party)
    (share : C.Party → In → ℕ → R) (view : Finset C.Party → (C.Party → Option In) → Lk)
    (D : C.Coalition) (inputs : C.Party → Option In) (step : ℕ) :
    WeightedBound ((Fmult count filled share view).run D inputs) (hybridWeight step) step := by
  unfold Fmult sample
  exact ((hybrid_leak_queryBound _ step).bind (fun known =>
    (hybrid_sample_queryBound _ step).bind (fun fresh => WeightedBound.pure _ 0))).mono (by omega)

lemma functionality_sum_queryBound {I₁ O₁ L₁ R₁ I₂ O₂ L₂ R₂ : Type} [Inhabited R₁] [Inhabited R₂]
    (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂)
    (h₁ : ∀ D inputs step, WeightedBound (F₁.run D inputs) (hybridWeight step) step)
    (h₂ : ∀ D inputs step, WeightedBound (F₂.run D inputs) (hybridWeight step) step)
    (D : C.Coalition) (inputs : C.Party → Option (I₁ ⊕ I₂)) (step : ℕ) :
    WeightedBound ((F₁.sum F₂).run D inputs) (hybridWeight step) step := by
  unfold Functionality.sum
  dsimp only
  split_ifs
  · refine (WeightedBound.simulateQ _ (fun t => ?_) (h₁ D _ step)).map _
    rcases t with t | l
    · rcases t with u | (q | x) <;> exact WeightedBound.query _
    · exact ((hybrid_leak_queryBound _ step).bind (fun r => by
        cases r <;> exact WeightedBound.pure _ 0)).mono (by simp [hybridWeight])
  · refine (WeightedBound.simulateQ _ (fun t => ?_) (h₂ D _ step)).map _
    rcases t with t | l
    · rcases t with u | (q | x) <;> exact WeightedBound.query _
    · exact ((hybrid_leak_queryBound _ step).bind (fun r => by
        cases r <;> exact WeightedBound.pure _ 0)).mono (by simp [hybridWeight])
  · exact WeightedBound.pure _ _

lemma checkFunctionalities_queryBound [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
    (K : Constants C E) (D : C.Coalition) (inputs : C.Party → Option ((ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ)))
    (step : ℕ) :
    WeightedBound ((checkFunctionalities K).run D inputs) (hybridWeight step) step := by
  unfold checkFunctionalities
  apply functionality_sum_queryBound
  · intro D inputs step
    apply functionality_sum_queryBound
    · exact Fcoin_queryBound
    · intro D inputs step
      unfold FextendMult
      exact Fmult_queryBound _ _ _ _ _ _ _
  · intro D inputs step
    apply functionality_sum_queryBound
    · exact Frand_queryBound
    · exact Frand_queryBound

lemma runFunctionality_queryBound {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (step : ℕ)
    (hF : ∀ inputs, WeightedBound (F.run D inputs) (hybridWeight step) step)
    (hA : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (inputs : C.Party → Option I) :
    IsQueryBoundP (runFunctionality localRoles D A F st inputs) Counted step := by
  let impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT A.State (OracleComp (LocalSpec C))) :=
    (fun (t : (LocalSpec C).Domain) =>
      (StateT.lift (OracleComp.lift (OracleSpec.query t)) : StateT A.State (OracleComp (LocalSpec C)) _)) +
    (fun l => StateT.mk fun s => do
      let a ← A.answer s l
      pure (a.2, a.1))
  have hi : ∀ t s, IsQueryBoundP ((impl t).run s) Counted (hybridWeight step t) := by
    intro t s
    rcases t with t | l
    · change IsQueryBoundP ((fun a => (a, s)) <$> (liftM (OracleSpec.query (spec := LocalSpec C) t) : OracleComp _ _))
        Counted (hybridWeight (L := L) step (.inl t))
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      rcases t with u | v
      · simp [hybridWeight, Counted]
      · simp [hybridWeight]
    · change IsQueryBoundP (A.answer s l >>= fun a => pure (a.2, a.1)) Counted step
      exact (isQueryBoundP_bind (hA s l) (fun a _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  have hrun := WeightedBound.simulateQ_state impl hi (hF inputs) st
  have hswap := isQueryBoundP_bind hrun (fun out _ => isQueryBoundP_pure Counted (out.2, out.1) 0)
  unfold runFunctionality
  split_ifs <;> dsimp only <;> try simp only [pure_bind]
  all_goals first
    | exact isQueryBoundP_pure Counted _ step
    | simpa only [Nat.add_zero, impl, localRoles] using hswap

end HybridBounds
end ThresholdLeanXmssSecurity
end

/-! ## Simulation -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- Fill the hidden term from the reconstructed known tuple, independently of unheld local entries. -/
def canonicalDummyTuples (D : C.Coalition) (known : C.Party → Option (List (Tuple C)))
    (differences : List (ℕ → Bit)) (i : C.Party) : List (Tuple C) :=
  ((known i).getD []).zipIdx.map fun (τ, k) =>
    let σ := tupleAt known k
    match lackedTerm D.1 with
    | some T₀ => ⟨τ.x, τ.y, fun T g => if T = T₀ then
        (differences.getD k fun _ => 0) g + shareValue σ.x g * shareValue σ.y g -
          ∑ T' ∈ univ.erase T₀, σ.z T' g
        else τ.z T g, τ.count, τ.mode⟩
    | none => τ

lemma canonicalDummyTuples_counts (D : C.Coalition) (known : C.Party → Option (List (Tuple C)))
    (differences : List (ℕ → Bit)) (i : C.Party) :
    (canonicalDummyTuples D known differences i).map (·.count) = ((known i).getD []).map (·.count) := by
  unfold canonicalDummyTuples
  rw [List.map_map]
  calc
    _ = ((known i).getD []).zipIdx.map (fun p => p.1.count) := by
      apply congrArg (fun f => List.map f (((known i).getD []).zipIdx))
      funext ⟨τ, k⟩
      dsimp only [Function.comp_apply]
      split <;> rfl
    _ = _ := by
      change List.map ((fun τ : Tuple C => τ.count) ∘ Prod.fst) _ = _
      rw [← List.map_map]
      simp

/-- Replacing one term sets the prescribed difference of a reconstructed tuple. -/
lemma replace_hidden_difference (τ : Tuple C) (T₀ : C.Term) (d : ℕ → Bit) (g : ℕ) :
    shareValue (fun T k => if T = T₀ then
      d k + shareValue τ.x k * shareValue τ.y k - ∑ T' ∈ univ.erase T₀, τ.z T' k
      else τ.z T k) g - shareValue τ.x g * shareValue τ.y g = d g := by
  let z : C.Term → Bit := fun T => if T = T₀ then
    d g + shareValue τ.x g * shareValue τ.y g - ∑ T' ∈ univ.erase T₀, τ.z T' g else τ.z T g
  change (∑ T, z T) - shareValue τ.x g * shareValue τ.y g = d g
  rw [← Finset.sum_erase_add _ z (Finset.mem_univ T₀)]
  have hz : ∑ T ∈ univ.erase T₀, z T = ∑ T ∈ univ.erase T₀, τ.z T g := by
    apply Finset.sum_congr rfl
    intro T hT
    exact if_neg (Finset.mem_erase.mp hT).1
  rw [hz]
  simp only [z, if_pos rfl]
  ring

/-- The pointwise shift required when the final challenge is fixed. -/
lemma final_mask_shift (w a a' r : E) (hr : 1 + r ≠ 0) :
    (w + r / (1 + r) * (a - a')) + r * ((w + r / (1 + r) * (a - a')) + a') =
      w + r * (w + a) := by
  field_simp
  ring

/-- Each fixed-challenge shift is a bijection of the mask space. -/
def finalMaskEquiv {ι : Type} (r : E) (Δ : ι → E) : (ι → E) ≃ (ι → E) :=
  Equiv.addRight (fun T => r / (1 + r) * Δ T)

lemma finalMaskEquiv_apply {ι : Type} (r : E) (Δ w : ι → E) (T : ι) :
    finalMaskEquiv r Δ w T = w T + r / (1 + r) * Δ T := rfl

/-- The fixed-challenge bijection preserves a uniform table of mask terms. -/
theorem finalMaskEquiv_uniform {ι : Type} [Fintype ι] (r : E) (Δ : ι → E) :
    𝒟[finalMaskEquiv r Δ <$> ($ᵗ (ι → E))] = 𝒟[$ᵗ (ι → E)] := by
  apply evalDist_ext
  intro w
  exact probOutput_map_bijective_uniformSample _ (finalMaskEquiv r Δ).bijective w

def canonicalCheckSimulator (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : Adversary C E (List (Tuple C)) ((List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit))
      ((Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
        ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit))))) :
    Simulator (C := C) (LocalSpec C) (List (Tuple C))
      ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (Finset C.Party) A.State where
  State := A.State
  start x z := A.start x z
  answer st leak := do
    let r ← executePhase localRoles D A (checkFunctionalities K) fuel st
      fun i => checkProtocol K i (canonicalDummyTuples D leak.1 leak.2.1 i)
    pure (r.1, univ.filter fun i => r.2 i = some ())
  output st := pure st

end ThresholdLeanXmssSecurity
end

/-! ## Bounds -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- Cardinality of the term enumeration, as used by `checkOverhead`. -/
lemma check_terms_length : C.terms.length = C.n.choose (C.t - 1) := by
  rw [Committee.terms, Finset.length_toList, Finset.card_univ]
  convert Fintype.card_finset_len (α := C.Party) (C.t - 1) using 1
  simp

/-- The deterministic leak of the check functionality. -/
def multVerifyLeak (D : C.Coalition) (inputs : C.Party → Option (List (Tuple C))) :
    (C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool :=
  let count := (firstInput inputs).length
  let tuples := (List.range count).map (tupleAt inputs)
  let differences := tuples.map fun τ g =>
    if g < τ.count then shareValue τ.z g - shareValue τ.x g * shareValue τ.y g else 0
  let agree := ∀ k < count, ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 →
    ∀ g < (tuples.getD k ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count,
      ((inputs i).bind (·[k]?)).map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) =
        ((inputs j).bind (·[k]?)).map fun τ => (τ.x T g, τ.y T g, τ.z T g)
  let accept := decide (agree ∧ ∀ τ ∈ tuples, ∀ g < τ.count, shareValue τ.z g = shareValue τ.x g * shareValue τ.y g)
  let known := fun i => if i ∈ D.1 then none else (inputs i).map fun views =>
    views.map fun τ => (⟨knownView D.1 τ.count τ.x, knownView D.1 τ.count τ.y, knownView D.1 τ.count τ.z,
      τ.count, τ.mode⟩ : Tuple C)
  (known, (if agree then differences else []), accept)

lemma FmultVerify_run_eq (D : C.Coalition) (inputs : C.Party → Option (List (Tuple C))) :
    FmultVerify.run D inputs = (do
      let receivers ← leak (multVerifyLeak D inputs)
      pure fun i => if i ∉ D.1 ∧ (multVerifyLeak D inputs).2.2 ∧ i ∈ receivers then some () else none) := rfl

lemma canonicalDummyTuples_leak_counts (K : Constants C E) (counts : List ℕ) (D : C.Coalition)
    (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x) (i : C.Party) (hi : i ∉ D.1) :
    let l := multVerifyLeak D (fun j => if j ∈ D.1 then none else some (x j))
    (canonicalDummyTuples D l.1 l.2.1 i).map (·.count) = counts := by
  dsimp only
  rw [canonicalDummyTuples_counts]
  simpa [multVerifyLeak, hi, List.map_map, Function.comp_def] using hx.1 i hi

lemma canonicalCheckSimulator_answer_queryBound (K : Constants C E) (fuel step : ℕ) (D : C.Coalition)
    (A : Adversary C E (List (Tuple C)) ((List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit))
      ((Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
        ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))))
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (counts : List ℕ) (l : (C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool)
    (hc : ∀ i, i ∉ D.1 → ((l.1 i).getD []).map (·.count) = counts) (state : A.State) :
    IsQueryBoundP ((canonicalCheckSimulator K fuel D A).answer state l) Counted
      (fuel * step + checkOverhead C counts.sum) := by
  let H := halvings counts.sum + 2 + coins counts.sum + (halvings counts.sum + 1) * challengeTries +
    2 * C.terms.length
  have hp : ∀ i, i ∉ D.1 → PartyBound (checkProtocol K i (canonicalDummyTuples D l.1 l.2.1 i)) H := by
    intro i hi
    have hcount : (canonicalDummyTuples D l.1 l.2.1 i).map (·.count) = counts :=
      (canonicalDummyTuples_counts ..).trans (hc i hi)
    simpa only [hcount] using checkProtocol_queryBound K i (canonicalDummyTuples D l.1 l.2.1 i)
  have he := executePhase_queryBound D A (checkFunctionalities K) step hr
    (fun st inputs => runFunctionality_queryBound D A (checkFunctionalities K) step
      (fun inputs => checkFunctionalities_queryBound K D inputs step) ha st inputs)
    fuel state (fun i => checkProtocol K i (canonicalDummyTuples D l.1 l.2.1 i)) (fun _ => H) hp
  unfold canonicalCheckSimulator
  refine (isQueryBoundP_bind he (fun out _ => isQueryBoundP_pure _ _ 0)).mono ?_
  simp [H, checkOverhead, check_terms_length, termCount]

lemma hasHashQueryBound_adversary (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (n : ℕ) (h : IsQueryBoundP oa Counted n) :
    HasHashQueryBound (runWorld prims (worldRoles.adversary oa)) n := by
  intro r hr
  unfold runWorld at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact cost_counted prims oa n h ∅ r' hr'

lemma adversary_bind {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (k : α → OracleComp (LocalSpec C) β) :
    worldRoles.adversary (oa >>= k) = worldRoles.adversary oa >>= fun a => worldRoles.adversary (k a) := by
  change counted (liftComp (oa >>= k) (SimulatorSpec C)) = _
  rw [liftComp_bind, counted_bind]
  rfl

lemma adversary_pure {α : Type} (a : α) :
    worldRoles.adversary (pure a : OracleComp (LocalSpec C) α) = pure a := by
  rfl

def idealMultVerifyLocal {σ : Type} (D : C.Coalition)
    (S : Simulator (C := C) (LocalSpec C) (List (Tuple C))
      ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (Finset C.Party) σ)
    (x : C.Party → List (Tuple C)) (z : Aux) : OracleComp (LocalSpec C) (σ × (C.Party → Option Unit)) := do
  let st ← S.start (corruptInputs D x) z
  let l := multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))
  let result ← S.answer st l
  let out ← S.output result.1
  pure (out, fun i => if i ∉ D.1 ∧ l.2.2 ∧ i ∈ result.2 then some () else none)

lemma simulateQ_leak_bind_run {L R α σ : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (l : L) (f : R → α) (st : σ) :
    (simulateQ impl (leak l >>= fun r => pure (f r))).run st = (do
      let out ← (impl (.inr l)).run st
      pure (f out.1, out.2)) := by
  rw [simulateQ_bind, StateT.run_bind]
  simp [leak, simulateQ_spec_query]

def checkIdealImpl {σ : Type}
    (S : Simulator (C := C) (LocalSpec C) (List (Tuple C))
      ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (Finset C.Party) σ) :
    QueryImpl (LocalSpec C + (((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) →ₒ Finset C.Party))
      (StateT S.State (OracleComp (WorldSpec C))) :=
  (fun (t : (LocalSpec C).Domain) =>
    (StateT.lift (free (OracleComp.lift (OracleSpec.query t))) : StateT S.State (OracleComp (WorldSpec C)) _)) +
  (fun l => StateT.mk fun st => do
    let (st, r) ← worldRoles.adversary (S.answer st l)
    pure (r, st))

lemma checkIdealImpl_leak_run {σ : Type}
    (S : Simulator (C := C) (LocalSpec C) (List (Tuple C))
      ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (Finset C.Party) σ)
    (l : (C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (st : S.State) :
    ((checkIdealImpl S) (.inr l)).run st =
      (worldRoles.adversary (S.answer st l) >>= fun r => pure (r.2, r.1)) := rfl

lemma idealExecution_multVerify_local {σ : Type} (D : C.Coalition)
    (S : Simulator (C := C) (LocalSpec C) (List (Tuple C))
      ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (Finset C.Party) σ)
    (x : C.Party → List (Tuple C)) (z : Aux) :
    idealExecution worldRoles.adversary D FmultVerify S x z =
      worldRoles.adversary (idealMultVerifyLocal D S x z) := by
  change (do
    let st ← worldRoles.adversary (S.start (corruptInputs D x) z)
    let r ← (simulateQ (checkIdealImpl S) (FmultVerify.run D (fun i => if i ∈ D.1 then none else some (x i)))).run st
    let out ← worldRoles.adversary (S.output r.2)
    pure (out, r.1)) = _
  rw [FmultVerify_run_eq]
  simp only [simulateQ_leak_bind_run, checkIdealImpl_leak_run, bind_assoc, pure_bind]
  change (do
    let st ← worldRoles.adversary (S.start (corruptInputs D x) z)
    let r ← (do let ans ← worldRoles.adversary (S.answer st (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i)))); pure (ans.2, ans.1))
    let out ← worldRoles.adversary (S.output r.2)
    pure (out, fun i => if i ∉ D.1 ∧ (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 ∧ i ∈ r.1 then some () else none)) = _
  simp only [idealMultVerifyLocal, adversary_bind, adversary_pure, bind_assoc, pure_bind]

lemma distinguish_adversary {σ O : Type} (oa : OracleComp (LocalSpec C) (σ × (C.Party → Option O)))
    (Z : Distinguisher C σ O) :
    distinguish (worldRoles.adversary oa) Z = worldRoles.adversary (oa >>= Z) := by
  rw [adversary_bind]
  rfl

theorem canonicalCheckSimulator_queryBound (prims : Primitives) (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition)
    (A : Adversary C E (List (Tuple C)) ((List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit))
      ((Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
        ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) (q : ℕ)
    (hx : TupleInputs K counts D x) (hq : IsQueryBounded A Z (2 * halvings counts.sum + 8) q) :
    HasHashQueryBound (runWorld prims (distinguish
      (idealExecution worldRoles.adversary D FmultVerify
        (canonicalCheckSimulator K (2 * halvings counts.sum + 8) D A) x z) Z))
      (q + checkOverhead C counts.sum) := by
  obtain ⟨start, step, final, hbudget, hstart, hround, hanswer, hfinal⟩ := hq
  rw [idealExecution_multVerify_local, distinguish_adversary]
  apply hasHashQueryBound_adversary
  let l := multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))
  have hc : ∀ i, i ∉ D.1 → ((l.1 i).getD []).map (·.count) = counts := by
    intro i hi
    simpa [l, multVerifyLeak, hi, List.map_map, Function.comp_def] using hx.1 i hi
  have he := fun st => canonicalCheckSimulator_answer_queryBound K (2 * halvings counts.sum + 8)
    step D A hround hanswer counts l hc st
  unfold idealMultVerifyLocal
  simp only [bind_assoc]
  refine (isQueryBoundP_bind (hstart _ _) (fun st _ =>
    isQueryBoundP_bind (m := final) (he st) (fun result _ => ?_))).mono ?_
  · change IsQueryBoundP ((pure result.1 : OracleComp (LocalSpec C) _) >>= _) Counted final
    simp only [pure_bind]
    exact hfinal _
  · omega

end ThresholdLeanXmssSecurity
end

/-! ## Hybrid -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- An independent challenge may be sampled after the masks even when it selects their bijection. -/
theorem finalMaskEquiv_late_uniform {ι β : Type} [Fintype ι]
    (challenge : ProbComp E) (Δ : E → ι → E) (f : E → (ι → E) → ProbComp β) :
    𝒟[do let w ← $ᵗ (ι → E); let r ← challenge; f r (finalMaskEquiv r (Δ r) w)] =
      𝒟[do let w ← $ᵗ (ι → E); let r ← challenge; f r w] := by
  calc
    _ = 𝒟[do let r ← challenge; let w ← $ᵗ (ι → E); f r (finalMaskEquiv r (Δ r) w)] :=
      DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do let r ← challenge; let w ← $ᵗ (ι → E); f r w] := by
      apply evalDist_bind_congr'
      intro r
      have he : (($ᵗ (ι → E)) >>= fun w => f r (finalMaskEquiv r (Δ r) w)) =
          (finalMaskEquiv r (Δ r) <$> ($ᵗ (ι → E))) >>= f r := by simp
      rw [he, evalDist_bind, finalMaskEquiv_uniform, ← evalDist_bind]
    _ = _ := (DeferredSampling.evalDist_bind_comm _ _ _).symm

/-- The coordinate shift fixes every known mask coordinate. -/
lemma finalMaskEquiv_known {ι : Type} (r : E) (Δ w : ι → E) (T : ι) (hT : Δ T = 0) :
    finalMaskEquiv r Δ w T = w T := by
  simp [finalMaskEquiv_apply, hT]

/-- `Conv` respects the coefficientwise mask shift. No spanning argument is required. -/
lemma conv_maskShift (K : Constants C E) (i : C.Party) (w A A' : Shares C E) (r : E) (g : ℕ) :
    conv K (localContext i) (fun T k => w T k + r / (1 + r) * (A T k - A' T k)) g =
      conv K (localContext i) w g + r / (1 + r) *
        (conv K (localContext i) A g - conv K (localContext i) A' g) := by
  simp only [conv, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro T hT <;> ring

lemma final_opening_shift (K : Constants C E) (i : C.Party) (w A A' : Shares C E) (r : E)
    (hr : 1 + r ≠ 0) (g : ℕ) :
    let w' := fun T k => w T k + r / (1 + r) * (A T k - A' T k)
    conv K (localContext i) w' g + r * (conv K (localContext i) w' g + conv K (localContext i) A' g) =
      conv K (localContext i) w g + r * (conv K (localContext i) w g + conv K (localContext i) A g) := by
  dsimp only
  rw [conv_maskShift]
  exact final_mask_shift _ _ _ _ hr

end ThresholdLeanXmssSecurity
end

/-! ## Soundness -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The cached-oracle challenge bound for any set of at most `m` bad values. -/
theorem challengeQuery_pred_card_le (prims : Primitives) (K : Constants C E)
    (tag label : ℕ) (v : List E) (Ks : Finset HashOutput) (L m : ℕ)
    (hL : L ≤ label) (s : HashCache C) (hs : CacheOK Ks L s) (P : E → Prop) [DecidablePred P]
    (hP : (univ.filter P).card ≤ m) :
    Pr[fun z => ∃ r, P r ∧ z.1 = some r |
      (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag label v) (LocalSpec C))).run s] ≤
        Ks.card / 2 ^ 256 + m / (Fintype.card E - 2 : ℕ) := by
  have h := challengeQuery_mem_le prims K tag label v Ks L hL s hs (univ.filter P)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  refine h.trans ?_
  gcongr

/-- GS20 Lemma 10, with the model's actual cached challenge expansion. -/
theorem finalChallenge_soundness (prims : Primitives) (K : Constants C E)
    (tag label : ℕ) (v : List E) (Ks : Finset HashOutput) (L : ℕ)
    (hL : L ≤ label) (s : HashCache C) (hs : CacheOK Ks L s)
    (a b a0 b0 D e0 e2 : E) (hwrong : D ≠ a * b) :
    Pr[fun z => ∃ r,
      ((a0 + r * (a0 + a)) * (b0 + r * (b0 + b)) =
        (a0 * b0 + e0) + (D + (a0 * b0 + e0) + ((a0 + a) * (b0 + b) + e2)) * r +
          ((a0 + a) * (b0 + b) + e2) * r ^ 2) ∧ z.1 = some r |
      (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag label v) (LocalSpec C))).run s] ≤
        Ks.card / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ) := by
  letI : CharP E 2 := charP_two
  exact challengeQuery_pred_card_le prims K tag label v Ks L 2 hL s hs _
    (by simpa using gs20_lemma10_final_step a b a0 b0 D e0 e2 hwrong)

/-- Gruen's slice step, with the same actual challenge distribution. -/
theorem sliceChallenge_soundness (prims : Primitives) (K : Constants C E)
    (tag label : ℕ) (v : List E) (Ks : Finset HashOutput) (L : ℕ)
    (hL : L ≤ label) (s : HashCache C) (hs : CacheOK Ks L s)
    (c D t0 t1 t2 e0 eInf : E) (hc : c ≠ 0) (hwrong : D ≠ t0 + c * (t0 + t1 + t2)) :
    Pr[fun z => ∃ r,
      ((1 + r) * (t0 + e0) + r * ((D + (t0 + e0)) / c) + r * (1 + r) * (t2 + eInf) =
        t0 + t1 * r + t2 * r ^ 2) ∧ z.1 = some r |
      (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag label v) (LocalSpec C))).run s] ≤
        Ks.card / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ) := by
  letI : CharP E 2 := charP_two
  exact challengeQuery_pred_card_le prims K tag label v Ks L 2 hL s hs _
    (by simpa using gruen_slice_step c D t0 t1 t2 e0 eInf hc hwrong)

/-- GS20 Lemma 9, with the same actual challenge distribution. -/
theorem halvingChallenge_soundness (prims : Primitives) (K : Constants C E)
    (tag label : ℕ) (v : List E) (Ks : Finset HashOutput) (L : ℕ)
    (hL : L ≤ label) (s : HashCache C) (hs : CacheOK Ks L s)
    (lo hi lo' hi' : List E) (claim e0 e2 : E)
    (hwrong : claim ≠ (List.zipWith (· * ·) lo lo').sum + (List.zipWith (· * ·) hi hi').sum)
    (hlen : lo.length = hi.length ∧ lo'.length = hi'.length ∧ lo.length = lo'.length) :
    Pr[fun z => ∃ r,
      ((List.zipWith (· * ·) lo lo').sum + e0 +
          (claim + (List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum + e2) * r +
          ((List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum + e2) * r ^ 2 =
        (List.zipWith (· * ·) (List.zipWith (fun a b => a + r * (a + b)) lo hi)
          (List.zipWith (fun a b => a + r * (a + b)) lo' hi')).sum) ∧ z.1 = some r |
      (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag label v) (LocalSpec C))).run s] ≤
        Ks.card / 2 ^ 256 + 2 / (Fintype.card E - 2 : ℕ) := by
  letI : CharP E 2 := charP_two
  exact challengeQuery_pred_card_le prims K tag label v Ks L 2 hL s hs _
    (by simpa using gs20_lemma9_halving_step lo hi lo' hi' claim e0 e2 hwrong hlen)

end ThresholdLeanXmssSecurity
end

/-! ## Delinearization -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- GS20 Lemma 8 is at most the de-linearization summand of `checkErrorOf`. -/
theorem delinearization_card_bound (K : Constants C E) (s d : ℕ) (hs : s ≤ d)
    (δ : ℕ → E) (hδ : ∃ a < 2 ^ d, δ a ≠ 0) :
    ((univ.filter fun τ : (Fin s → {c : E // c ≠ 0}) × (Fin (d - s) → E) =>
        ∑ a ∈ range (2 ^ d), coinProduct (List.ofFn (fun b => (τ.1 b).1) ++ List.ofFn τ.2) 0 d a * δ a = 0).card : ℝ) /
      ((Fintype.card E - 1 : ℝ) ^ s * (Fintype.card E : ℝ) ^ (d - s)) ≤
      d / (Fintype.card E - 2 : ℝ) := by
  have h := gs20_lemma8_delinearization s d hs δ hδ
  have hc : (2 : ℝ) < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  refine h.trans ?_
  have h1 : (s : ℝ) / (Fintype.card E - 1 : ℝ) ≤ s / (Fintype.card E - 2 : ℝ) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg s) <;> linarith
  have h2 : ((d-s : ℕ) : ℝ) / (Fintype.card E : ℝ) ≤ (d-s : ℕ) / (Fintype.card E - 2 : ℝ) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg (d-s)) <;> linarith
  calc
    _ ≤ (s : ℝ) / (Fintype.card E - 2 : ℝ) + (d-s : ℕ) / (Fintype.card E - 2 : ℝ) := add_le_add h1 h2
    _ = _ := by rw [← add_div, ← Nat.cast_add, Nat.add_sub_of_le hs]

end ThresholdLeanXmssSecurity
end

/-! ## Freshness -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- Only the coin input being used needs to be fresh; other labels may have been queried. -/
theorem challengeQuery_mem_le_of_fresh (prims : Primitives) (K : Constants C E)
    (tag label : ℕ) (v : List E) (Ks : Finset HashOutput) (s : HashCache C)
    (hfresh : s (.coinKey tag label (v.flatMap fun v => List.ofFn (K.encode v))) = none)
    (hexp : ∀ k idx, s (.expand k idx) ≠ none → k ∈ Ks) (S : Finset E) :
    Pr[fun z => ∃ e ∈ S, z.1 = some e |
      (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag label v) (LocalSpec C))).run s] ≤
      Ks.card / 2 ^ 256 + S.card / (Fintype.card E - 2 : ℕ) := by
  have hq : ¬ IsFixed (C := C) (.coinKey tag label (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  rw [simulateQ_localAnswer_liftComp, challengeQuery, simulateQ_bind, StateT.run_bind]
  have hev : ∀ mx : ProbComp (Option E × HashCache C),
      Pr[fun z => ∃ e ∈ S, z.1 = some e | mx] = Pr[fun z => ¬ ¬ ∃ e ∈ S, z.1 = some e | mx] := fun mx => by simp
  rw [hev]
  refine probEvent_bind_le_add (p := fun z : HashOutput × HashCache C => z.1 ∉ Ks) ?_ fun z hz hkey => ?_
  · simp only [not_not]
    exact probEvent_hash_fresh_mem prims hq hfresh Ks
  · rw [← hev]
    refine probEvent_findChallenge_mem prims K z.1 S challengeTries 0 z.2 fun i _ => ?_
    by_contra hne
    rcases support_hashQuery_entries prims hq s z hz _ hne with h | h
    · exact hkey (hexp _ i h)
    · cases h

/-- An injectively encoded fresh sample hits at most one value per earlier query. -/
theorem probEvent_uniform_injective_mem {α β : Type} [Fintype α] [Nonempty α] [SampleableType α]
    (f : α → β) (hf : Function.Injective f) (Q : Finset β) :
    Pr[fun a => f a ∈ Q | $ᵗ α] ≤ Q.card / (Fintype.card α : ℕ) := by
  rw [probEvent_uniformSample]
  have hc : (univ.filter fun a => f a ∈ Q).card ≤ Q.card := by
    exact Finset.card_le_card_of_injOn f (fun a ha => (Finset.mem_filter.mp ha).2) (fun a _ b _ h => hf h)
  gcongr

lemma coin_input_injective (K : Constants C E) (tag label : ℕ) :
    Function.Injective (fun r : E => Query.coinKey (C := C) tag label (List.ofFn (K.encode r))) := by
  intro a b hab
  have h := Query.coinKey.inj hab
  exact K.encode.injective (List.ofFn_injective h.2.2)

theorem coin_input_guess_bound (K : Constants C E) (tag label : ℕ) (Q : Finset (Query C)) :
    Pr[fun r : E => Query.coinKey tag label (List.ofFn (K.encode r)) ∈ Q | $ᵗ E] ≤
      Q.card / (Fintype.card E : ℕ) :=
  probEvent_uniform_injective_mem _ (coin_input_injective K tag label) Q

lemma digest_input_injective (history : (Fin 256 → Bit) → HashOutput) :
    Function.Injective (fun salt : Fin 256 → Bit => Query.digest (C := C) (List.ofFn salt) (history salt)) := by
  intro a b hab
  exact List.ofFn_injective (Query.digest.inj hab).1

/-- This event involves salted digest inputs, never history inputs. -/
theorem digest_input_guess_bound (history : (Fin 256 → Bit) → HashOutput) (Q : Finset (Query C)) :
    Pr[fun salt : Fin 256 → Bit => Query.digest (List.ofFn salt) (history salt) ∈ Q | $ᵗ (Fin 256 → Bit)] ≤
      Q.card / 2 ^ 256 := by
  have h := probEvent_uniform_injective_mem _ (digest_input_injective (C := C) history) Q
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using h

end ThresholdLeanXmssSecurity
end

/-! ## Digest -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

lemma relabelHashCache_apply (e : Query C ≃ Query C) (s : HashCache C) (q : Query C) :
    relabelHashCache e s (e q) = s q := by
  unfold relabelHashCache
  change Query C → Option HashOutput at s
  exact congrArg s (e.symm_apply_apply q)

lemma relabelHashCache_insert (e : Query C ≃ Query C) (s : HashCache C)
    (q : Query C) (u : HashOutput) :
    relabelHashCache e (s.cacheQuery q u) = (relabelHashCache e s).cacheQuery (e q) u := by
  funext q'
  by_cases h : q' = e q
  · subst q'
    exact (relabelHashCache_apply e (s.cacheQuery q u) q).trans
      ((QueryCache.cacheQuery_self s q u).trans (QueryCache.cacheQuery_self (relabelHashCache e s) (e q) u).symm)
  · have h' : e.symm q' ≠ q := by intro he; apply h; simpa using congrArg e he
    simp [relabelHashCache, QueryCache.cacheQuery, Function.update_of_ne h, Function.update_of_ne h']

/-- Lazy random-oracle answers commute with an input bijection at random-oracle inputs. -/
theorem hashAnswer_reindex (prims : Primitives) (e : Query C ≃ Query C) (s : HashCache C)
    (q : Query C) (hq : ¬ IsFixed q) (heq : ¬ IsFixed (e q)) :
    (hashAnswer prims (e q)).run (relabelHashCache e s) =
      (fun p => (p.1, relabelHashCache e p.2)) <$> (hashAnswer prims q).run s := by
  rw [hashAnswer_of_not_isFixed prims hq, hashAnswer_of_not_isFixed prims heq]
  cases hs : s q with
  | none =>
    have hs' : relabelHashCache e s (e q) = none := (relabelHashCache_apply e s q).trans hs
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs,
      QueryImpl.withCaching_run_none _ hs', Functor.map_map]
    congr 1
    funext u
    simp only [Function.comp_apply, relabelHashCache_insert]
  | some u =>
    have hs' : relabelHashCache e s (e q) = some u := (relabelHashCache_apply e s q).trans hs
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs,
      QueryImpl.withCaching_run_some _ hs', map_pure]

/-- One salted digest pair can be exchanged while every other query is fixed. -/
def digestSwap (salt : List Bit) (h h' : HashOutput) : Query C ≃ Query C :=
  Equiv.swap (.digest salt h) (.digest salt h')

lemma digestSwap_history (salt values : List Bit) (h h' : HashOutput) :
    digestSwap (C := C) salt h h' (.history values) = .history values := by
  simp [digestSwap, Equiv.swap_apply_def]

lemma digestSwap_coinKey (salt values : List Bit) (h h' : HashOutput) (tag label : ℕ) :
    digestSwap (C := C) salt h h' (.coinKey tag label values) = .coinKey tag label values := by
  simp [digestSwap, Equiv.swap_apply_def]

lemma digestSwap_other_salt (salt salt' : List Bit) (h h' u : HashOutput) (hne : salt' ≠ salt) :
    digestSwap (C := C) salt h h' (.digest salt' u) = .digest salt' u := by
  simp [digestSwap, Equiv.swap_apply_def, hne]

def hashAnswerFlat (prims : Primitives) (q : Query C) : StateT (HashCache C) ProbComp HashOutput :=
  hashAnswer prims q

/-- The single-digest coupling is exact after transporting the cache. -/
theorem hashAnswer_digestSwap (prims : Primitives) (salt : List Bit) (h h' : HashOutput) (s : HashCache C) :
    (hashAnswer prims (.digest salt h')).run (relabelHashCache (digestSwap salt h h') s) =
      (fun p => (p.1, relabelHashCache (digestSwap salt h h') p.2)) <$>
        (hashAnswer prims (.digest salt h)).run s := by
  have h1 : ¬ IsFixed (C := C) (.digest salt h) := by rintro ⟨_, hh, _⟩; cases hh
  have h2 : ¬ IsFixed (digestSwap (C := C) salt h h' (.digest salt h)) := by
    simp only [digestSwap, Equiv.swap_apply_left]
    rintro ⟨_, hh, _⟩; cases hh
  have hh : digestSwap (C := C) salt h h' (.digest salt h) = .digest salt h' := Equiv.swap_apply_left _ _
  have hh' : (hashAnswer prims (digestSwap salt h h' (.digest salt h))).run
      (relabelHashCache (digestSwap salt h h') s) =
      (hashAnswer prims (.digest salt h')).run (relabelHashCache (digestSwap salt h h') s) := by
    exact congrArg (fun q => (hashAnswerFlat prims q).run
      (relabelHashCache (digestSwap salt h h') s)) hh
  exact hh'.symm.trans (hashAnswer_reindex prims (digestSwap salt h h') s (.digest salt h) h1 h2)

end ThresholdLeanXmssSecurity
end

/-! ## Digest program -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

lemma digestSwap_isFixed_iff (salt : List Bit) (h h' : HashOutput) (q : Query C) :
    IsFixed (digestSwap salt h h' q) ↔ IsFixed q := by
  cases q <;> simp [IsFixed, digestSwap, Equiv.swap_apply_def]
  intro x hx
  split_ifs at hx <;> cases hx

lemma hashAnswer_digestSwap_all (prims : Primitives) (salt : List Bit) (h h' : HashOutput)
    (s : HashCache C) (q : Query C) :
    (hashAnswer prims (digestSwap salt h h' q)).run (relabelHashCache (digestSwap salt h h') s) =
      (fun p => (p.1, relabelHashCache (digestSwap salt h h') p.2)) <$> (hashAnswer prims q).run s := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hq
    have he : digestSwap (C := C) salt h h' (.hash input) = .hash input := by
      simp [digestSwap, Equiv.swap_apply_def]
    change (hashAnswerFlat prims _).run _ = _
    rw [he]
    change (hashAnswer prims (.hash input)).run _ = _
    rw [hashAnswer_of_isFixed prims hi]
    simp
  · exact hashAnswer_reindex prims _ s q hq (fun hx => hq ((digestSwap_isFixed_iff salt h h' q).mp hx))

/-- Transport the cache along a digest swap throughout an arbitrary hash-oracle program. -/
theorem hashProgram_digestSwap (prims : Primitives) (salt : List Bit) (h h' : HashOutput)
    {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) (s : HashCache C) :
    (simulateQ (fun q => hashAnswer prims (digestSwap salt h h' q)) oa).run
        (relabelHashCache (digestSwap salt h h') s) =
      (fun p => (p.1, relabelHashCache (digestSwap salt h h') p.2)) <$>
        (simulateQ (hashAnswer prims) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hstep : (hashAnswerFlat prims (digestSwap salt h h' q)).run
        (relabelHashCache (digestSwap salt h h') s) =
        (fun p : HashOutput × HashCache C => (p.1, relabelHashCache (digestSwap salt h h') p.2)) <$>
          (hashAnswerFlat prims q).run s := hashAnswer_digestSwap_all prims salt h h' s q
    change ((hashAnswerFlat prims (digestSwap salt h h' q)).run
      (relabelHashCache (digestSwap salt h h') s) >>= fun p : HashOutput × HashCache C =>
        (simulateQ (fun q => hashAnswer prims (digestSwap salt h h' q)) (k p.1)).run p.2) =
      (fun p => (p.1, relabelHashCache (digestSwap salt h h') p.2)) <$>
        ((hashAnswerFlat prims q).run s >>= fun p : HashOutput × HashCache C =>
          (simulateQ (hashAnswer prims) (k p.1)).run p.2)
    rw [hstep, bind_map_left, map_bind]
    congr 1
    funext p
    exact ih p.1 p.2

end ThresholdLeanXmssSecurity
end

/-! ## Assembly -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- Exactly the distance obligation for the explicit candidate simulator. -/
def MultVerifyDistance (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ)
    (D : C.Coalition)
    (A : Adversary C E (List (Tuple C)) ((List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit))
      ((Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
        ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) (q : ℕ),
    TupleInputs K counts D x → IsQueryBounded A Z (checkRounds counts.sum) q →
    |accepts prims (distinguish (realExecution D A (checkFunctionalities K)
        (checkRounds counts.sum) (checkProtocol K) x z) Z) -
      accepts prims (distinguish (idealExecution worldRoles.adversary D FmultVerify
        (canonicalCheckSimulator K (checkRounds counts.sum) D A) x z) Z)| ≤
      checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q + checkHashError C counts.sum q

/-- Assembly without changing either bound or any quantifier of `MultVerifyStatement`. -/
theorem multVerifyStatement_of_distance (prims : Primitives) (K : Constants C E)
    (h : MultVerifyDistance prims K) : MultVerifyStatement prims K := by
  intro counts D A
  refine ⟨canonicalCheckSimulator K (2 * halvings counts.sum + 8) D A, ?_⟩
  intro x z Z q hx hq
  exact ⟨canonicalCheckSimulator_queryBound prims K counts D A x z Z q hx hq,
    h counts D A x z Z q hx hq⟩

end ThresholdLeanXmssSecurity
end

/-! ## Relations -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The interpolation set used by the actual functionality. -/
def firstHonest (D : C.Coalition) : Finset C.Party :=
  ((C.parties.filter (· ∉ D.1)).take C.t).toFinset

lemma firstHonest_not_corrupt (D : C.Coalition) {i : C.Party} (hi : i ∈ firstHonest D) : i ∉ D.1 := by
  have hi' := List.mem_of_mem_take (List.mem_toFinset.mp hi)
  simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hi').2

lemma firstHonest_card (D : C.Coalition) : (firstHonest D).card = C.t := by
  have hnd : C.parties.Nodup := List.nodup_finRange C.n
  have hn : (C.parties.filter (· ∉ D.1)).Nodup := hnd.filter _
  have he : (C.parties.filter (· ∉ D.1)).toFinset = D.1ᶜ := by
    ext i
    simp [Committee.parties]
  have hl : (C.parties.filter (· ∉ D.1)).length = C.n - D.1.card := by
    rw [← List.toFinset_card_of_nodup hn, he, Finset.card_compl, Fintype.card_fin]
  rw [firstHonest, List.toFinset_card_of_nodup hn.take, List.length_take, hl]
  have := D.2
  have := C.one_le_t
  simp only [Committee.n]
  omega

/-- Interpolation through the honest set reproduces a polynomial of degree at most `t-1`. -/
theorem interpolate_honest_polynomial (K : Constants C E) (D : C.Coalition) (P : Polynomial E)
    (hP : P.natDegree ≤ C.t - 1) (a : C.Party → E)
    (ha : ∀ i, i ∉ D.1 → a i = P.eval (K.point i)) (x : E) :
    interpolate K D.1 a x = P.eval x := by
  have ht := C.one_le_t
  have hd : P.degree < (firstHonest D).card := by
    rw [firstHonest_card]
    exact (degree_le_of_natDegree_le hP).trans_lt (by exact_mod_cast (by omega : C.t - 1 < C.t))
  have hpoly := Lagrange.eq_interpolate K.point.injective.injOn hd
  conv_rhs => rw [hpoly]
  simp only [interpolate, firstHonest, Lagrange.interpolate_apply, eval_finsetSum,
    eval_mul, eval_C, Lagrange.eval_basis_eq_prod, lagrangeAt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i (firstHonest_not_corrupt D hi), mul_comm]

lemma interpolate_sub (K : Constants C E) (D : Finset C.Party) (a b : C.Party → E) (x : E) :
    interpolate K D (fun i => a i - b i) x = interpolate K D a x - interpolate K D b x := by
  simp only [interpolate, mul_sub, Finset.sum_sub_distrib]

/-- A difference may be polynomial even when each individual view is inconsistent. -/
def ShamirDifference (K : Constants C E) (D : C.Coalition) (a b : C.Party → E) : Prop :=
  ∃ P : Polynomial E, P.natDegree ≤ C.t - 1 ∧
    (∀ i, i ∉ D.1 → a i - b i = P.eval (K.point i)) ∧
    (∀ i, i ∈ D.1 → P.eval (K.point i) = 0)

lemma ShamirDifference.refl (K : Constants C E) (D : C.Coalition) (a : C.Party → E) :
    ShamirDifference K D a a := by
  refine ⟨0, by simp, ?_, ?_⟩ <;> simp

lemma ShamirDifference.lin (K : Constants C E) (D : C.Coalition)
    {a b c d : C.Party → E} (hab : ShamirDifference K D a b) (hcd : ShamirDifference K D c d)
    (u v : E) : ShamirDifference K D (fun i => u*a i+v*c i) (fun i => u*b i+v*d i) := by
  obtain ⟨P,hP,hPi,hPD⟩ := hab
  obtain ⟨Q,hQ,hQi,hQD⟩ := hcd
  refine ⟨Polynomial.C u * P + Polynomial.C v * Q, ?_, ?_, ?_⟩
  · exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans hP) ((natDegree_C_mul_le _ _).trans hQ))
  · intro i hi
    simp only [eval_add, eval_mul, eval_C, ← hPi i hi, ← hQi i hi]
    ring
  · intro i hi
    simp [hPD i hi,hQD i hi]

/-- The functionality gives identical Shamir views to every corrupt operator. -/
theorem ShamirDifference.interpolate_eq (K : Constants C E) (D : C.Coalition)
    {a b : C.Party → E} (h : ShamirDifference K D a b) (c : C.Party) (hc : c ∈ D.1) :
    interpolate K D.1 a (K.point c) = interpolate K D.1 b (K.point c) := by
  obtain ⟨P,hP,hPi,hPD⟩ := h
  have he := interpolate_honest_polynomial K D P hP (fun i => a i-b i) hPi (K.point c)
  rw [interpolate_sub,hPD c hc] at he
  exact sub_eq_zero.mp he

/-- A change only in unheld terms has zero value at a corrupt point. -/
lemma conv_hidden_zero (K : Constants C E) (D : C.Coalition) (delta : Shares C E)
    (hknown : ∀ T, KnownTo D.1 T → ∀ g, delta T g = 0) (c : C.Party) (hc : c ∈ D.1) (g : ℕ) :
    conv K (localContext c) delta g = 0 := by
  unfold conv
  apply Finset.sum_eq_zero
  intro T hT
  have hhold : c ∈ C.holders T := by simpa [localContext] using (Finset.mem_filter.mp hT).2
  rw [hknown T ⟨c,hc,hhold⟩ g, mul_zero]

/-- A common hidden coefficient difference gives the invariant used through the check. -/
theorem ShamirDifference.of_conv (K : Constants C E) (D : C.Coalition)
    (a b : C.Party → E) (delta : Shares C E) (g : ℕ)
    (hknown : ∀ T, KnownTo D.1 T → ∀ g, delta T g = 0)
    (hdiff : ∀ i, i ∉ D.1 → a i-b i = conv K (localContext i) delta g) :
    ShamirDifference K D a b := by
  letI : CharP E 2 := charP_two
  obtain ⟨P,hP,hP0,hPi⟩ := cdi05_conv_correct K (fun T => delta T g)
  refine ⟨P,hP,?_,?_⟩
  · intro i hi
    exact (hdiff i hi).trans (hPi i)
  · intro c hc
    rw [← hPi c]
    exact conv_hidden_zero K D delta hknown c hc g

end ThresholdLeanXmssSecurity
end

/-! ## Extend views -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma reconstruct_congr_at {α : Type} [Inhabited α]
    (a b : C.Party → Option (C.Term → α)) (T : C.Term)
    (h : ∀ i, i ∈ C.holders T → (a i).map (· T) = (b i).map (· T)) :
    reconstruct a T = reconstruct b T := by
  unfold reconstruct
  congr 1
  rw [← List.head?_map, ← List.head?_map, List.map_filterMap, List.map_filterMap]
  congr 2
  funext i
  by_cases hi : i ∈ C.holders T
  · simp [hi,h i hi]
  · simp [hi]

def extendEntry (K : Constants C E) (D : Finset C.Party)
    (inputs : C.Party → Option (List (Product C E))) (c : C.Party) (shape : Bool × ℕ) (g : ℕ) : Product C E :=
  let entry := fun i => (inputs i).bind (·[g]?)
  if shape.1 then
    .replicated (knownView D shape.2 (reconstruct fun i => (entry i).map (·.replicatedParts.1)))
      (knownView D shape.2 (reconstruct fun i => (entry i).map (·.replicatedParts.2))) shape.2
  else
    .shamir (fun k => if k < shape.2 then
        interpolate K D (fun i => (((entry i).map (·.shamirParts.1)).getD fun _ => 0) k) (K.point c) else 0)
      (fun k => if k < shape.2 then
        interpolate K D (fun i => (((entry i).map (·.shamirParts.2)).getD fun _ => 0) k) (K.point c) else 0) shape.2

lemma extendView_shapes (K : Constants C E) (D : Finset C.Party)
    (inputs : C.Party → Option (List (Product C E))) (c : C.Party) :
    extendView K D inputs c = if c ∉ D then [] else
      ((firstInput inputs).map Product.shape).zipIdx.map fun (shape,g) => extendEntry K D inputs c shape g := by
  unfold extendView
  by_cases hc : c ∈ D
  · simp only [hc,not_true_eq_false,if_false]
    rw [List.zipIdx_map, List.map_map]
    apply List.map_congr_left
    intro p hp
    rcases p with ⟨p,g⟩
    cases p <;> rfl
  · simp [hc]

/-- The two kinds of data that the multiplication functionality exposes. -/
def ExtendViewRelation (K : Constants C E) (D : C.Coalition)
    (a b : C.Party → Option (List (Product C E))) : Prop :=
  (firstInput a).map Product.shape = (firstInput b).map Product.shape ∧
  (∀ (g : ℕ) (T : C.Term), KnownTo D.1 T → ∀ (i : C.Party), i ∈ C.holders T →
    (((a i).bind (·[g]?)).map fun (p : Product C E) => p.replicatedParts.1 T) =
      (((b i).bind (·[g]?)).map fun (p : Product C E) => p.replicatedParts.1 T)) ∧
  (∀ (g : ℕ) (T : C.Term), KnownTo D.1 T → ∀ (i : C.Party), i ∈ C.holders T →
    (((a i).bind (·[g]?)).map fun (p : Product C E) => p.replicatedParts.2 T) =
      (((b i).bind (·[g]?)).map fun (p : Product C E) => p.replicatedParts.2 T)) ∧
  (∀ (g k : ℕ), ShamirDifference K D
    (fun i => ((((a i).bind (·[g]?)).map (·.shamirParts.1)).getD fun _ => 0) k)
    (fun i => ((((b i).bind (·[g]?)).map (·.shamirParts.1)).getD fun _ => 0) k)) ∧
  (∀ (g k : ℕ), ShamirDifference K D
    (fun i => ((((a i).bind (·[g]?)).map (·.shamirParts.2)).getD fun _ => 0) k)
    (fun i => ((((b i).bind (·[g]?)).map (·.shamirParts.2)).getD fun _ => 0) k))

/-- The actual leak of `F_extendMult` agrees, including interpolation of inconsistent views. -/
theorem extendView_eq_of_relation (K : Constants C E) (D : C.Coalition)
    (a b : C.Party → Option (List (Product C E))) (h : ExtendViewRelation K D a b) :
    extendView K D.1 a = extendView K D.1 b := by
  obtain ⟨hshape,hx,hy,hA,hB⟩ := h
  funext c
  rw [extendView_shapes,extendView_shapes,hshape]
  by_cases hc : c ∈ D.1
  · simp only [hc,not_true_eq_false,if_false]
    apply List.map_congr_left
    rintro ⟨⟨kind,count⟩,g⟩ _
    simp only [extendEntry]
    split_ifs
    · congr 1
      · funext T k
        unfold knownView
        split_ifs with hT
        · have he := reconstruct_congr_at
            (fun i => ((a i).bind (·[g]?)).map (·.replicatedParts.1))
            (fun i => ((b i).bind (·[g]?)).map (·.replicatedParts.1)) T
            (by intro i hi; simpa only [Option.map_map,Function.comp_def] using hx g T hT.1 i hi)
          exact congrFun he k
        · rfl
      · funext T k
        unfold knownView
        split_ifs with hT
        · have he := reconstruct_congr_at
            (fun i => ((a i).bind (·[g]?)).map (·.replicatedParts.2))
            (fun i => ((b i).bind (·[g]?)).map (·.replicatedParts.2)) T
            (by intro i hi; simpa only [Option.map_map,Function.comp_def] using hy g T hT.1 i hi)
          exact congrFun he k
        · rfl
    · congr 1
      · funext k
        split_ifs
        · exact ShamirDifference.interpolate_eq K D (hA g k) c hc
        · rfl
      · funext k
        split_ifs
        · exact ShamirDifference.interpolate_eq K D (hB g k) c hc
        · rfl

  · simp [hc]

end ThresholdLeanXmssSecurity
end

/-! ## Mult shift -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma lackedTerm_unknown (D : C.Coalition) (T : C.Term) (h : lackedTerm D.1 = some T) :
    ¬ KnownTo D.1 T := by
  have ht := List.find?_some h
  simpa only [decide_eq_true_eq] using ht

def multFinish (D : C.Coalition) (width : ℕ) (filled : C.Term → ℕ → Option C.Party)
    (result : ℕ → E) (known : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (fresh : C.Term → Fin width → E) : C.Party → Option (Shares C E) :=
  let base : Shares C E := fun T g =>
    if KnownTo D.1 T then known T g else if h : g < width then fresh T ⟨g,h⟩ else 0
  let z : Shares C E := fun T g => if lackedTerm D.1 = some T then
    result g - ∑ T' ∈ univ.erase T, base T' g else base T g
  fun i => if i ∈ D.1 ∨ i ∉ receivers then none else
    some fun T g => if i ∈ C.holders T ∧ g < width then
      z T g + (if ∃ j ∈ D.1, filled T g = some j then offset i T g else 0) else 0

def addHiddenOutput (D : C.Coalition) (width : ℕ) (delta : ℕ → E)
    (out : C.Party → Option (Shares C E)) : C.Party → Option (Shares C E) :=
  fun i => (out i).map fun z T g => z T g +
    if i ∈ C.holders T ∧ g < width ∧ lackedTerm D.1 = some T then delta g else 0

lemma multFinish_shift (D : C.Coalition) (width : ℕ) (filled : C.Term → ℕ → Option C.Party)
    (result result' : ℕ → E) (known : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (fresh : C.Term → Fin width → E) :
    multFinish D width filled result known offset receivers fresh =
      addHiddenOutput D width (fun g => result g-result' g)
        (multFinish D width filled result' known offset receivers fresh) := by
  funext i
  dsimp only [multFinish,addHiddenOutput]
  by_cases hi : i ∈ D.1 ∨ i ∉ receivers
  · simp only [if_pos hi,Option.map_none]
  · simp only [if_neg hi,Option.map_some]
    congr 1
    funext T g
    by_cases hh : i ∈ C.holders T <;> by_cases hg : g < width <;>
      by_cases ht : lackedTerm D.1 = some T <;>
      simp only [hh,hg,ht,true_and,false_and,and_true,and_false,if_true,if_false,add_zero] <;> ring

def extendTotal (K : Constants C E) (D : C.Coalition)
    (inputs : C.Party → Option (List (Product C E))) (g : ℕ) : E :=
  ∑ i ∈ univ.filter (· ∉ D.1),
    ((inputs i).map fun products => match products[g]? with
      | some p => productShare K (localContext i) p
      | none => 0).getD 0

lemma FextendMult_run_finish (K : Constants C E) (D : C.Coalition)
    (inputs : C.Party → Option (List (Product C E))) :
    (FextendMult K).run D inputs = (do
      let (d,known,offset,receivers) ← leak (extendView K D.1 inputs)
      let fresh ← sample (C.Term → Fin (firstInput inputs).length → E)
      pure (multFinish D (firstInput inputs).length (filler K .peer)
        (fun g => extendTotal K D inputs g+d g) known offset receivers fresh)) := rfl

def multLeak (view : C.Party → List (Product C E)) :
    OracleComp (LocalSpec C + ((C.Party → List (Product C E)) →ₒ
      ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)))
      ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) := leak view

def multRun (D : C.Coalition) (width : ℕ) (filled : C.Term → ℕ → Option C.Party)
    (total : ℕ → E) (view : C.Party → List (Product C E)) :
    OracleComp (LocalSpec C + ((C.Party → List (Product C E)) →ₒ
      ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)))
      (C.Party → Option (Shares C E)) := do
  let (d,known,offset,receivers) ← multLeak view
  let fresh ← sample (C.Term → Fin width → E)
  pure (multFinish D width filled (fun g => total g+d g) known offset receivers fresh)

lemma multRun_shift (D : C.Coalition) (width : ℕ) (filled : C.Term → ℕ → Option C.Party)
    (total total' : ℕ → E) (view : C.Party → List (Product C E)) :
    multRun D width filled total view =
      addHiddenOutput D width (fun g => total g-total' g) <$> multRun D width filled total' view := by
  unfold multRun
  simp only [map_bind]
  apply bind_congr
  intro reply
  rcases reply with ⟨d,known,offset,receivers⟩
  simp only [map_bind]
  apply bind_congr
  intro fresh
  simp only [map_pure]
  have hdelta : (fun g => total g+d g-(total' g+d g)) = (fun g => total g-total' g) := by
    funext g; ring
  have hout := multFinish_shift D width filled (fun g => total g+d g)
    (fun g => total' g+d g) known offset receivers fresh
  rw [hdelta] at hout
  exact congrArg Pure.pure hout

/-- One complete ideal multiplication call couples exactly, including the adversary's adaptive reply. -/
theorem FextendMult_run_shift (K : Constants C E) (D : C.Coalition)
    (a b : C.Party → Option (List (Product C E))) (h : ExtendViewRelation K D a b) :
    (FextendMult K).run D a =
      addHiddenOutput D (firstInput b).length (fun g => extendTotal K D a g-extendTotal K D b g) <$>
        (FextendMult K).run D b := by
  have hview := extendView_eq_of_relation K D a b h
  have hlen : (firstInput a).length = (firstInput b).length := by
    simpa only [List.length_map] using congrArg List.length h.1
  change multRun D (firstInput a).length (filler K .peer) (extendTotal K D a) (extendView K D.1 a) =
    addHiddenOutput D (firstInput b).length (fun g => extendTotal K D a g-extendTotal K D b g) <$>
      multRun D (firstInput b).length (filler K .peer) (extendTotal K D b) (extendView K D.1 b)
  rw [hview,hlen]
  exact multRun_shift D _ _ _ _ _

/-- Known output terms are unchanged by the coupled multiplication. -/
lemma addHiddenOutput_known (D : C.Coalition) (width : ℕ) (delta : ℕ → E)
    (out : C.Party → Option (Shares C E)) (i : C.Party) (T : C.Term)
    (hT : KnownTo D.1 T) :
    ((addHiddenOutput D width delta out i).map fun z => z T) = ((out i).map fun z => z T) := by
  have hnot : lackedTerm D.1 ≠ some T := fun hh => lackedTerm_unknown D T hh hT
  simp only [addHiddenOutput,Option.map_map]
  congr 1
  funext z
  funext g
  simp [hnot]

end ThresholdLeanXmssSecurity
end

/-! ## Network shift -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}

/-- Equality of functionality programs lifts through an adaptive adversary's entire callback. -/
theorem runFunctionality_map_output {m : Type → Type} [Monad m] [LawfulMonad m]
    {I O L R Ia : Type} (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (st : A.State) (a b : C.Party → Option I)
    (f : (C.Party → Option O) → (C.Party → Option O))
    (hinput : ∀ i, i ∉ D.1 → (a i).isSome = (b i).isSome)
    (hcall : F.run D a = f <$> F.run D b) (hzero : f (fun _ => none) = fun _ => none) :
    runFunctionality Ro D A F st a =
      (fun r => (r.1,f r.2)) <$> runFunctionality Ro D A F st b := by
  have hi : (∀ i, i ∉ D.1 → (a i).isSome) ↔ (∀ i, i ∉ D.1 → (b i).isSome) := by
    constructor <;> intro h i hD
    · rw [← hinput i hD]; exact h i hD
    · rw [hinput i hD]; exact h i hD
  unfold runFunctionality
  simp only [hi]
  split_ifs
  · simp only [hcall,simulateQ_map,StateT.run_map,bind_map_left,map_bind,map_pure]
  · simp [hzero]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The network callback itself has the hidden-output translation, with identical adversary state. -/
theorem runFunctionality_extend_shift {m : Type → Type} [Monad m] [LawfulMonad m]
    {Ia : Type} (Ro : Roles C m) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E Ia (C.Party → List (Product C E))
      ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party))
    (st : A.State) (a b : C.Party → Option (List (Product C E)))
    (hinput : ∀ i, i ∉ D.1 → (a i).isSome = (b i).isSome)
    (h : ExtendViewRelation K D a b) :
    runFunctionality Ro D A (FextendMult K) st a =
      (fun r => (r.1,addHiddenOutput D (firstInput b).length
        (fun g => extendTotal K D a g-extendTotal K D b g) r.2)) <$>
      runFunctionality Ro D A (FextendMult K) st b := by
  apply runFunctionality_map_output Ro D A (FextendMult K) st a b _ hinput
  · exact FextendMult_run_shift K D a b h
  · funext i
    rfl

end ThresholdLeanXmssSecurity
end

/-! ## Inputs -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

lemma filler_held (K : Constants C E) (mode : ReshareMode) (T : C.Term) (g : ℕ)
    (i : C.Party) (h : filler K mode T g = some i) : i ∈ C.holders T := by
  cases mode with
  | peer =>
    have hf := List.find?_some h
    have he : K.filled i = T := by simpa only [decide_eq_true_eq] using hf
    rw [← he]
    exact K.filled_held i
  | collector =>
    dsimp only [filler] at h
    split_ifs at h with ht
    · have hi := Option.some.inj h
      rw [← hi,← ht]
      exact K.collector_held g

lemma unknown_no_corrupt_filler (K : Constants C E) (D : C.Coalition) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (mode : ReshareMode) (g : ℕ) :
    ¬ ∃ j ∈ D.1, filler K mode T g = some j := by
  rintro ⟨j,hj,hf⟩
  exact hT ⟨j,hj,filler_held K mode T g j hf⟩

/-- The full input assumption gives consistency of every term hidden from the coalition. -/
theorem tupleInputs_unknown_vectors (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) : ConsistentAt D
      (fun i T => (x i).map fun τ =>
        (vector τ.count (τ.x T),vector τ.count (τ.y T),vector τ.count (τ.z T))) T := by
  apply hx.2.2 T
  intro i _ j _ hi hj
  have hzero : ∀ i, i ∉ D.1 →
      (x i).map (fun τ => vector τ.count fun g =>
        if ∃ j ∈ D.1, filler K τ.mode T g = some j then τ.z T g else 0) =
        counts.map (fun n => vector n fun _ => (0 : Bit)) := by
    intro i hi
    rw [← hx.1 i hi,List.map_map]
    simp only [Function.comp_def,if_neg (unknown_no_corrupt_filler K D T hT _ _)]
  exact (hzero i hi).trans (hzero j hj).symm

theorem tupleInputs_unknown_part (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (part : Tuple C → Shares C Bit)
    (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    ConsistentAt D (fun i T => (x i).map fun τ => vector τ.count (part τ T)) T := by
  intro i hi j hj hiD hjD
  have h := tupleInputs_unknown_vectors K hx T hT i hi j hj hiD hjD
  rcases hpart with rfl | rfl | rfl
  · simpa only [List.map_map,Function.comp_def] using congrArg (List.map Prod.fst) h
  · simpa only [List.map_map,Function.comp_def] using congrArg (List.map fun p => p.2.1) h
  · simpa only [List.map_map,Function.comp_def] using congrArg (List.map fun p => p.2.2) h

theorem tupleInputs_unknown_lifted (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (part : Tuple C → Shares C Bit)
    (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    ConsistentAt D (fun i T => liftedPart (E := E) (x i) part T) T := by
  intro i hi j hj hiD hjD
  funext k
  dsimp only
  have h := tupleInputs_unknown_part K hx T hT part hpart i hi j hj hiD hjD
  dsimp only at h
  rw [liftedPart_eq,liftedPart_eq,h]

/-- Common differences on unknown terms, with zero difference on every known term. -/
def HiddenDifference (D : C.Coalition) (a b : C.Party → Shares C E) : Prop :=
  ∃ delta : Shares C E, (∀ T, KnownTo D.1 T → ∀ g, delta T g = 0) ∧
    ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g, a i T g-b i T g = delta T g

lemma HiddenDifference.of_consistent (K : Constants C E) (D : C.Coalition)
    (a b : C.Party → Shares C E)
    (hknown : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → a i T = b i T)
    (ha : ∀ T, ¬ KnownTo D.1 T → ConsistentAt D a T)
    (hb : ∀ T, ¬ KnownTo D.1 T → ConsistentAt D b T) : HiddenDifference D a b := by
  have hh := exists_honest_holder (C := C) D
  let j := fun T => Classical.choose (hh T)
  have hj := fun T => Classical.choose_spec (hh T)
  refine ⟨fun T g => if KnownTo D.1 T then 0 else a (j T) T g-b (j T) T g,?_,?_⟩
  · intro T hT g; simp only [if_pos hT]
  · intro i hi T hiT g
    by_cases hT : KnownTo D.1 T
    · simp only [if_pos hT,hknown T hT i hi hiT,sub_self]
    · dsimp only
      rw [if_neg hT,ha T hT i hiT (j T) (hj T).1 hi (hj T).2,
        hb T hT i hiT (j T) (hj T).1 hi (hj T).2]

lemma HiddenDifference.conv (K : Constants C E) (D : C.Coalition)
    {a b : C.Party → Shares C E} (h : HiddenDifference D a b) (g : ℕ) :
    ShamirDifference K D (fun i => ThresholdLeanXmss.conv K (localContext i) (a i) g)
      (fun i => ThresholdLeanXmss.conv K (localContext i) (b i) g) := by
  obtain ⟨delta,hknown,hdiff⟩ := h
  apply ShamirDifference.of_conv K D _ _ delta g hknown
  intro i hi
  change ThresholdLeanXmss.conv K (localContext i) (a i) g-ThresholdLeanXmss.conv K (localContext i) (b i) g =
    ThresholdLeanXmss.conv K (localContext i) delta g
  unfold ThresholdLeanXmss.conv
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  apply Finset.sum_congr rfl
  intro T hT
  rw [hdiff i hi T (by simpa [localContext] using (Finset.mem_filter.mp hT).2)]

lemma HiddenDifference.lin (D : C.Coalition) {a b c d : C.Party → Shares C E}
    (h₁ : HiddenDifference D a b) (h₂ : HiddenDifference D c d) (u v : ℕ → E) :
    HiddenDifference D (fun i T g => u g*a i T g+v g*c i T g)
      (fun i T g => u g*b i T g+v g*d i T g) := by
  obtain ⟨delta₁,h₁known,h₁diff⟩ := h₁
  obtain ⟨delta₂,h₂known,h₂diff⟩ := h₂
  refine ⟨fun T g => u g*delta₁ T g+v g*delta₂ T g,?_,?_⟩
  · intro T hT g; simp [h₁known T hT,h₂known T hT]
  · intro i hi T hT g
    dsimp only
    rw [← h₁diff i hi T hT g,← h₂diff i hi T hT g]
    ring

lemma HiddenDifference.reindex (D : C.Coalition) {a b : C.Party → Shares C E}
    (h : HiddenDifference D a b) (f : ℕ → ℕ) :
    HiddenDifference D (fun i T g => a i T (f g)) (fun i T g => b i T (f g)) := by
  obtain ⟨delta,hknown,hdiff⟩ := h
  exact ⟨fun T g => delta T (f g),fun T hT g => hknown T hT (f g),
    fun i hi T hT g => hdiff i hi T hT (f g)⟩

end ThresholdLeanXmssSecurity
end

/-! ## Dummy relation -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

def checkKnownTuples (D : C.Coalition) (x : C.Party → List (Tuple C)) :
    C.Party → Option (List (Tuple C)) :=
  (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).1

lemma checkKnownTuples_honest (D : C.Coalition) (x : C.Party → List (Tuple C))
    (i : C.Party) (hi : i ∉ D.1) :
    checkKnownTuples D x i = some ((x i).map fun τ =>
      (⟨knownView D.1 τ.count τ.x,knownView D.1 τ.count τ.y,knownView D.1 τ.count τ.z,
        τ.count,τ.mode⟩ : Tuple C)) := by
  simp [checkKnownTuples,multVerifyLeak,hi]

lemma knownView_vector (D : Finset C.Party) (n : ℕ) (v : Shares C Bit) (T : C.Term)
    (hT : KnownTo D T) : vector n (knownView D n v T) = vector n (v T) := by
  unfold vector
  apply List.map_congr_left
  intro g hg
  simp [knownView,hT,List.mem_range.mp hg]

lemma knownView_vector_zero (D : Finset C.Party) (n : ℕ) (v : Shares C Bit) (T : C.Term)
    (hT : ¬ KnownTo D T) : knownView D n v T = fun _ => 0 := by
  funext g
  simp [knownView,hT]

/-- All corrupt-known input vectors are reproduced exactly by the dummy input. -/
theorem canonicalDummyTuples_known_vectors (D : C.Coalition) (x : C.Party → List (Tuple C))
    (differences : List (ℕ → Bit)) (i : C.Party) (hi : i ∉ D.1) (T : C.Term)
    (hT : KnownTo D.1 T) :
    (canonicalDummyTuples D (checkKnownTuples D x) differences i).map
      (fun τ => (vector τ.count (τ.x T),vector τ.count (τ.y T),vector τ.count (τ.z T))) =
    (x i).map (fun τ => (vector τ.count (τ.x T),vector τ.count (τ.y T),vector τ.count (τ.z T))) := by
  unfold canonicalDummyTuples
  rw [checkKnownTuples_honest D x i hi]
  simp only [Option.getD_some,List.zipIdx_map,List.map_map]
  cases ht : lackedTerm D.1 with
  | none =>
    simp only [Function.comp_def,Prod.map,id_eq,knownView_vector D.1 _ _ T hT]
    change List.map ((fun τ : Tuple C =>
      (vector τ.count (τ.x T),vector τ.count (τ.y T),vector τ.count (τ.z T))) ∘ Prod.fst) _ = _
    rw [← List.map_map]
    simp
  | some T₀ =>
    have hne : T ≠ T₀ := by intro he; subst T₀; exact lackedTerm_unknown D T ht hT
    simp only [Function.comp_def,Prod.map,id_eq,if_neg hne,knownView_vector D.1 _ _ T hT]
    change List.map ((fun τ : Tuple C =>
      (vector τ.count (τ.x T),vector τ.count (τ.y T),vector τ.count (τ.z T))) ∘ Prod.fst) _ = _
    rw [← List.map_map]
    simp

lemma map_zipIdx_count_eq {α β : Type} (a b : List α) (n : α → ℕ) (F : ℕ → ℕ → β)
    (h : a.map n = b.map n) :
    a.zipIdx.map (fun p => F (n p.1) p.2) = b.zipIdx.map (fun p => F (n p.1) p.2) := by
  have hh := congrArg (fun l : List ℕ => l.zipIdx.map fun p => F p.1 p.2) h
  simpa only [List.zipIdx_map,List.map_map,Function.comp_def,Prod.map,id_eq] using hh

/-- Unknown dummy terms are common across honest holders, even when known terms are split. -/
theorem canonicalDummyTuples_unknown_vectors (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (differences : List (ℕ → Bit)) (T : C.Term) (hT : ¬ KnownTo D.1 T) :
    ConsistentAt D (fun i T => (canonicalDummyTuples D (checkKnownTuples D x) differences i).map
      (fun τ => (vector τ.count (τ.x T),vector τ.count (τ.y T),vector τ.count (τ.z T)))) T := by
  intro i _ j _ hi hj
  dsimp only
  unfold canonicalDummyTuples
  rw [checkKnownTuples_honest D x i hi,checkKnownTuples_honest D x j hj]
  simp only [Option.getD_some,List.zipIdx_map,List.map_map]
  cases ht : lackedTerm D.1 with
  | none =>
    simp only [Function.comp_def,Prod.map,id_eq,knownView_vector_zero D.1 _ _ T hT]
    exact map_zipIdx_count_eq (x i) (x j) (·.count)
      (fun n _ => (vector n (fun _ => (0 : Bit)),vector n (fun _ => (0 : Bit)),
        vector n (fun _ => (0 : Bit)))) ((hx.1 i hi).trans (hx.1 j hj).symm)
  | some T₀ =>
    simp only [Function.comp_def,Prod.map,id_eq,knownView_vector_zero D.1 _ _ T hT]
    by_cases he : T = T₀
    · simp only [if_pos he]
      exact map_zipIdx_count_eq (x i) (x j) (·.count)
        (fun n k => (vector n (fun _ => (0 : Bit)),vector n (fun _ => (0 : Bit)),
          vector n (fun g => (differences.getD k (fun _ => 0)) g +
            shareValue (tupleAt (checkKnownTuples D x) k).x g *
              shareValue (tupleAt (checkKnownTuples D x) k).y g -
            ∑ T' ∈ univ.erase T₀,(tupleAt (checkKnownTuples D x) k).z T' g)))
        ((hx.1 i hi).trans (hx.1 j hj).symm)
    · simp only [if_neg he,knownView_vector_zero D.1 _ _ T hT]
      exact map_zipIdx_count_eq (x i) (x j) (·.count)
        (fun n _ => (vector n (fun _ => (0 : Bit)),vector n (fun _ => (0 : Bit)),
          vector n (fun _ => (0 : Bit)))) ((hx.1 i hi).trans (hx.1 j hj).symm)

/-- The simulator's input and the real input begin with a common hidden-term difference. -/
theorem canonicalDummyTuples_hiddenDifference (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (differences : List (ℕ → Bit)) (part : Tuple C → Shares C Bit)
    (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    HiddenDifference D (fun i => liftedPart (E := E) (x i) part)
      (fun i => liftedPart (canonicalDummyTuples D (checkKnownTuples D x) differences i) part) := by
  apply HiddenDifference.of_consistent K D
  · intro T hT i hi _
    have hv := canonicalDummyTuples_known_vectors D x differences i hi T hT
    have hp : (canonicalDummyTuples D (checkKnownTuples D x) differences i).map
        (fun τ => vector τ.count (part τ T)) = (x i).map (fun τ => vector τ.count (part τ T)) := by
      rcases hpart with rfl | rfl | rfl
      · simpa only [List.map_map,Function.comp_def,Prod.map,id_eq] using congrArg (List.map Prod.fst) hv
      · simpa only [List.map_map,Function.comp_def,Prod.map,id_eq] using congrArg (List.map fun p => p.2.1) hv
      · simpa only [List.map_map,Function.comp_def,Prod.map,id_eq] using congrArg (List.map fun p => p.2.2) hv
    funext g
    try dsimp only
    rw [liftedPart_eq,liftedPart_eq,hp]
  · intro T hT
    exact tupleInputs_unknown_lifted K hx T hT part hpart
  · intro T hT i hi j hj hiD hjD
    have hv := canonicalDummyTuples_unknown_vectors K counts D x hx differences T hT i hi j hj hiD hjD
    dsimp only at hv
    have hp : (canonicalDummyTuples D (checkKnownTuples D x) differences i).map
        (fun τ => vector τ.count (part τ T)) =
      (canonicalDummyTuples D (checkKnownTuples D x) differences j).map
        (fun τ => vector τ.count (part τ T)) := by
      rcases hpart with rfl | rfl | rfl
      · simpa only [List.map_map,Function.comp_def,Prod.map,id_eq] using congrArg (List.map Prod.fst) hv
      · simpa only [List.map_map,Function.comp_def,Prod.map,id_eq] using congrArg (List.map fun p => p.2.1) hv
      · simpa only [List.map_map,Function.comp_def,Prod.map,id_eq] using congrArg (List.map fun p => p.2.2) hv
    funext g
    try dsimp only
    rw [liftedPart_eq,liftedPart_eq,hp]

end ThresholdLeanXmssSecurity
end

/-! ## Final shares -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The final third opening is the product of the first two plus this error polynomial. -/
lemma final_residual_identity (a b wa wb d e0 e2 r : E) :
    ((wa*wb+e0)+(d+(wa*wb+e0)+((wa+a)*(wb+b)+e2))*r+((wa+a)*(wb+b)+e2)*r^2) -
      (wa+r*(wa+a))*(wb+r*(wb+b)) =
        r*(d-a*b)+(1+r)*e0+r*(1+r)*e2 := by
  letI : CharP E 2 := charP_two
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (norm := ring_nf) (a*b*r)*two

/-- Matching the residual and the first two openings matches the third one too. -/
theorem final_three_openings (a b a' b' wa wb wa' wb' d d' e0 e2 r : E)
    (herror : d-a*b = d'-a'*b')
    (ha : wa+r*(wa+a) = wa'+r*(wa'+a'))
    (hb : wb+r*(wb+b) = wb'+r*(wb'+b')) :
    ((wa*wb+e0)+(d+(wa*wb+e0)+((wa+a)*(wb+b)+e2))*r+((wa+a)*(wb+b)+e2)*r^2) =
      ((wa'*wb'+e0)+(d'+(wa'*wb'+e0)+((wa'+a')*(wb'+b')+e2))*r+
        ((wa'+a')*(wb'+b')+e2)*r^2) := by
  have h := final_residual_identity a b wa wb d e0 e2 r
  have h' := final_residual_identity a' b' wa' wb' d' e0 e2 r
  rw [herror,ha,hb] at h
  linear_combination h-h'

/-- The mask translation preserves all three public openings when the error is fixed. -/
theorem final_three_openings_shift (a b a' b' wa wb d d' e0 e2 r : E)
    (hr : 1+r ≠ 0) (herror : d-a*b = d'-a'*b') :
    let wa' := wa+r/(1+r)*(a-a')
    let wb' := wb+r/(1+r)*(b-b')
    (wa+r*(wa+a),wb+r*(wb+b),
      (wa*wb+e0)+(d+(wa*wb+e0)+((wa+a)*(wb+b)+e2))*r+((wa+a)*(wb+b)+e2)*r^2) =
    (wa'+r*(wa'+a'),wb'+r*(wb'+b'),
      (wa'*wb'+e0)+(d'+(wa'*wb'+e0)+((wa'+a')*(wb'+b')+e2))*r+
        ((wa'+a')*(wb'+b')+e2)*r^2) := by
  dsimp only
  have ha := (final_mask_shift wa a a' r hr).symm
  have hb := (final_mask_shift wb b b' r hr).symm
  exact Prod.ext ha (Prod.ext hb (final_three_openings _ _ _ _ _ _ _ _ _ _ _ _ _ herror ha hb))

end ThresholdLeanXmssSecurity
end

/-! ## Errors -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Equal corrupt additive shares cancel from the difference of honest contributions. -/
lemma honest_sum_sub (D : C.Coalition) (f g : C.Party → E)
    (hD : ∀ i ∈ D.1, f i = g i) :
    (∑ i ∈ univ.filter (· ∉ D.1),f i) - (∑ i ∈ univ.filter (· ∉ D.1),g i) =
      (∑ i,f i) - ∑ i,g i := by
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hiD : i ∈ D.1 := by simpa using hi
  rw [hD i hiD,sub_self]

/-- The honest `MulSh` contributions change by exactly the change of the actual product. -/
theorem honest_mulSh_difference (K : Constants C E) (D : C.Coalition)
    (A B A' B' : C.Party → ℕ → E) (a b a' b' : ℕ → E) (n : ℕ)
    (hA : ∀ g < n,IsShamir K (fun i => A i g) (a g))
    (hB : ∀ g < n,IsShamir K (fun i => B i g) (b g))
    (hA' : ∀ g < n,IsShamir K (fun i => A' i g) (a' g))
    (hB' : ∀ g < n,IsShamir K (fun i => B' i g) (b' g))
    (hAD : ∀ i ∈ D.1,∀ g < n,A i g = A' i g)
    (hBD : ∀ i ∈ D.1,∀ g < n,B i g = B' i g) :
    (∑ i ∈ univ.filter (· ∉ D.1),mulSh K (localContext i) (A i) (B i) n) -
      (∑ i ∈ univ.filter (· ∉ D.1),mulSh K (localContext i) (A' i) (B' i) n) =
        (∑ g ∈ range n,a g*b g) - ∑ g ∈ range n,a' g*b' g := by
  letI : CharP E 2 := charP_two
  rw [honest_sum_sub D _ _ (by
    intro i hi
    unfold mulSh
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [hAD i hi g (mem_range.mp hg),hBD i hi g (mem_range.mp hg)])]
  have hs : ∀ (U V : C.Party → ℕ → E) (u v : ℕ → E),
      (∀ g < n,IsShamir K (fun i => U i g) (u g)) →
      (∀ g < n,IsShamir K (fun i => V i g) (v g)) →
      (∑ i,mulSh K (localContext i) (U i) (V i) n) = ∑ g ∈ range n,u g*v g := by
    intro U V u v hU hV
    simp only [mulSh,localContext,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hg
    exact sum_lagrangeAll_shamir K (hU g (mem_range.mp hg)) (hV g (mem_range.mp hg))
  rw [hs A B a b hA hB,hs A' B' a' b' hA' hB']

/-- In particular the attack added by `F_extendMult` induces the same product error. -/
theorem honest_mulSh_error_eq (K : Constants C E) (D : C.Coalition)
    (A B A' B' : C.Party → ℕ → E) (a b a' b' : ℕ → E) (n : ℕ) (attack : E)
    (hA : ∀ g < n,IsShamir K (fun i => A i g) (a g))
    (hB : ∀ g < n,IsShamir K (fun i => B i g) (b g))
    (hA' : ∀ g < n,IsShamir K (fun i => A' i g) (a' g))
    (hB' : ∀ g < n,IsShamir K (fun i => B' i g) (b' g))
    (hAD : ∀ i ∈ D.1,∀ g < n,A i g = A' i g)
    (hBD : ∀ i ∈ D.1,∀ g < n,B i g = B' i g) :
    (∑ i ∈ univ.filter (· ∉ D.1),mulSh K (localContext i) (A i) (B i) n) + attack -
      (∑ g ∈ range n,a g*b g) =
    (∑ i ∈ univ.filter (· ∉ D.1),mulSh K (localContext i) (A' i) (B' i) n) + attack -
      (∑ g ∈ range n,a' g*b' g) := by
  have h := honest_mulSh_difference K D A B A' B' a b a' b' n hA hB hA' hB' hAD hBD
  linear_combination h

/-- Error recurrence for Gruen's weighted slice fold. -/
lemma slice_residual_identity (c d t0 t1 t2 e0 eInf r : E) (hc : c ≠ 0) :
    ((1+r)*(t0+e0)+r*((d+(t0+e0))/c)+r*(1+r)*(t2+eInf)) -
      (t0+t1*r+t2*r^2) =
    (1+r)*e0+r/c*((d-(t0+c*(t0+t1+t2)))+e0)+r*(1+r)*eInf := by
  letI : CharP E 2 := charP_two
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  field_simp
  linear_combination (norm := ring_nf) (r*t0+r*t0*c+r*c*t2)*two

/-- Error recurrence for the quadratic dimension-reduction step. -/
lemma halving_residual_identity (d lo hi cross e0 e2 r : E) :
    (lo+e0+(d+(lo+hi+cross)+e2)*r+(lo+hi+cross+e2)*r^2) -
      (lo+cross*r+(lo+hi+cross)*r^2) =
    e0+r*(d-(lo+hi))+r*(1+r)*e2 := by
  letI : CharP E 2 := charP_two
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (norm := ring_nf) (lo*r+hi*r)*two

end ThresholdLeanXmssSecurity
end

/-! ## Digest local -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

/-- Digest renaming leaves every PRG key unchanged. -/
lemma digestSwap_streamKey (salt : List Bit) (h h' : HashOutput) (key : HashOutput) :
    digestSwap (C := C) salt h h' (.streamKey key) = .streamKey key := by
  simp [digestSwap,Equiv.swap_apply_def]

lemma prgAnswer_digestSwap (prims : Primitives) (salt : List Bit) (h h' : HashOutput)
    (s : HashCache C) (x : PrgInput C) :
    (prgAnswer prims x).run (relabelHashCache (digestSwap salt h h') s) =
      (fun p => (p.1,relabelHashCache (digestSwap salt h h') p.2)) <$>
        (prgAnswer prims x).run s := by
  have hq := hashAnswer_digestSwap_all prims salt h h' s (.streamKey x.2.1)
  rw [digestSwap_streamKey] at hq
  unfold prgAnswer
  simp only [StateT.run_bind,StateT.run_pure,map_bind,map_pure]
  rw [hq,bind_map_left]

def localDigestAnswer (prims : Primitives) (salt : List Bit) (h h' : HashOutput) :
    QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp) :=
  unifFwdImpl (Query C →ₒ HashOutput) +
    (((fun (q : Query C) => (hashAnswer prims (digestSwap salt h h' q) :
      StateT (HashCache C) ProbComp HashOutput)) :
      QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp)) + prgAnswer (C := C) prims)

/-- The cache transport works for private draws, hashes, and PRG calls together. -/
theorem localAnswer_digestSwap (prims : Primitives) (salt : List Bit) (h h' : HashOutput)
    (s : HashCache C) (t : (LocalSpec C).Domain) :
    (localDigestAnswer prims salt h h' t).run (relabelHashCache (digestSwap salt h h') s) =
      (fun p => (p.1,relabelHashCache (digestSwap salt h h') p.2)) <$>
        (localAnswer prims t).run s := by
  rcases t with n | q | x
  · simp [localDigestAnswer,localAnswer,unifFwdImpl,Functor.map_map]
  · exact hashAnswer_digestSwap_all prims salt h h' s q
  · exact prgAnswer_digestSwap prims salt h h' s x

/-- Digest coupling for a whole local computation, including an adaptive adversary. -/
theorem localProgram_digestSwap (prims : Primitives) (salt : List Bit) (h h' : HashOutput)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (s : HashCache C) :
    (simulateQ (localDigestAnswer prims salt h h') oa).run
        (relabelHashCache (digestSwap salt h h') s) =
      (fun p => (p.1,relabelHashCache (digestSwap salt h h') p.2)) <$>
        (simulateQ (localAnswer prims) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [localAnswer_digestSwap,bind_map_left,map_bind]
    apply bind_congr
    intro p
    exact ih p.1 p.2

end ThresholdLeanXmssSecurity
end

/-! ## Late local -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

lemma sameRun_liftComp_of_evalDist (prims : Primitives) {α : Type} (p q : ProbComp α)
    (h : 𝒟[p] = 𝒟[q]) :
    SameRun (C := C) prims (liftComp p (LocalSpec C)) (liftComp q (LocalSpec C)) := by
  intro s
  rw [run_liftComp_prob,run_liftComp_prob,evalDist_map,evalDist_map,h]

theorem sameRun_uniform_equiv (prims : Primitives) {α : Type} [Fintype α] [SampleableType α]
    (e : α ≃ α) :
    SameRun (C := C) prims (e <$> liftComp ($ᵗ α) (LocalSpec C)) (liftComp ($ᵗ α) (LocalSpec C)) := by
  have he : 𝒟[e <$> ($ᵗ α)] = 𝒟[$ᵗ α] := by
    apply evalDist_ext
    intro a
    exact probOutput_map_bijective_uniformSample _ e.bijective a
  simpa only [liftComp_map] using sameRun_liftComp_of_evalDist (C := C) prims _ _ he

/-- A later transcript may choose the mask bijection; arbitrary hash and PRG queries are retained. -/
theorem sameRun_late_uniform_equiv (prims : Primitives) {α β γ : Type}
    [Fintype α] [SampleableType α] (transcript : OracleComp (LocalSpec C) β)
    (e : β → α ≃ α) (k : β → α → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (do let w ← liftComp ($ᵗ α) (LocalSpec C); let t ← transcript; k t (e t w))
      (do let w ← liftComp ($ᵗ α) (LocalSpec C); let t ← transcript; k t w) := by
  have h : ∀ t, SameRun prims
      (liftComp ($ᵗ α) (LocalSpec C) >>= fun w => k t (e t w))
      (liftComp ($ᵗ α) (LocalSpec C) >>= k t) := by
    intro t
    simpa only [bind_map_left] using
      (sameRun_uniform_equiv (C := C) prims (e t)).bind (fun w => SameRun.refl prims (k t w))
  exact (sameRun_swap prims (liftComp ($ᵗ α) (LocalSpec C)) transcript (fun w t => k t (e t w))).trans
    ((SameRun.bind_right transcript h).trans
      (sameRun_swap prims (liftComp ($ᵗ α) (LocalSpec C)) transcript (fun w t => k t w)).symm)

end ThresholdLeanXmssSecurity
end

/-! ## Output terms -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma correctedTerms_translate (T₀ : C.Term) (u v delta : C.Term → E) (result result' : E)
    (hsum : ∑ T,delta T = result-result')
    (hbase : ∀ T,T ≠ T₀ → u T = v T+delta T) (T : C.Term) :
    (if T = T₀ then result-∑ T' ∈ univ.erase T₀,u T' else u T) =
    (if T = T₀ then result'-∑ T' ∈ univ.erase T₀,v T' else v T)+delta T := by
  by_cases hT : T = T₀
  · subst T
    simp only [ite_true]
    have he : (∑ T ∈ univ.erase T₀,u T) =
        (∑ T ∈ univ.erase T₀,v T)+(∑ T ∈ univ.erase T₀,delta T) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T hT => hbase T (mem_erase.mp hT).1
    have hd : (∑ T ∈ univ.erase T₀,delta T)+delta T₀ = result-result' :=
      (sum_erase_add _ _ (mem_univ T₀)).trans hsum
    rw [he]
    linear_combination -hd
  · simp only [if_neg hT,hbase T hT]

def multBase (D : C.Coalition) (width : ℕ) (known : Shares C E)
    (fresh : C.Term → Fin width → E) : Shares C E :=
  fun T g => if KnownTo D.1 T then known T g else if h : g < width then fresh T ⟨g,h⟩ else 0

def multTerms (D : C.Coalition) (width : ℕ) (result : ℕ → E) (known : Shares C E)
    (fresh : C.Term → Fin width → E) : Shares C E :=
  fun T g => if lackedTerm D.1 = some T then
    result g-∑ T' ∈ univ.erase T,multBase D width known fresh T' g else multBase D width known fresh T g

/-- Translating all unobserved fresh terms translates the corrected sharing by `delta`. -/
theorem multTerms_translate (D : C.Coalition) (width : ℕ) (result result' : ℕ → E)
    (known delta : Shares C E) (fresh : C.Term → Fin width → E)
    (hknown : ∀ T,KnownTo D.1 T → ∀ g,delta T g = 0)
    (hsum : ∀ g < width,∑ T,delta T g = result g-result' g) (T : C.Term) (g : ℕ) (hg : g < width) :
    multTerms D width result known fresh T g =
      multTerms D width result' known (fun T k => fresh T k-delta T k) T g+delta T g := by
  obtain ⟨T₀,hT₀,-⟩ := lackedTerm_spec D
  have hb : ∀ T,multBase D width known fresh T g =
      multBase D width known (fun T k => fresh T k-delta T k) T g+delta T g := by
    intro T
    by_cases hT : KnownTo D.1 T
    · simp [multBase,hT,hknown T hT]
    · simp [multBase,hT,hg]
  have hh := correctedTerms_translate T₀ (fun T => multBase D width known fresh T g)
    (fun T => multBase D width known (fun T k => fresh T k-delta T k) T g)
    (fun T => delta T g) (result g) (result' g) (hsum g hg) (fun T _ => hb T) T
  unfold multTerms
  rw [hT₀]
  by_cases hT : T = T₀
  · subst T
    simpa only [if_pos rfl] using hh
  · have hne : some T₀ ≠ some T := by simpa using Ne.symm hT
    simpa only [if_neg hne,if_neg hT] using hh

def addSharedOutput (D : C.Coalition) (width : ℕ) (delta : Shares C E)
    (out : C.Party → Option (Shares C E)) : C.Party → Option (Shares C E) :=
  fun i => (out i).map fun z T g => z T g+if i ∈ C.holders T ∧ g < width then delta T g else 0

/-- A translation of output shares is realized by a bijection of `F_mult`'s sampled table. -/
theorem multFinish_translate (D : C.Coalition) (width : ℕ) (filled : C.Term → ℕ → Option C.Party)
    (result result' : ℕ → E) (known delta : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (fresh : C.Term → Fin width → E)
    (hknown : ∀ T,KnownTo D.1 T → ∀ g,delta T g = 0)
    (hsum : ∀ g < width,∑ T,delta T g = result g-result' g) :
    multFinish D width filled result known offset receivers fresh =
      addSharedOutput D width delta
        (multFinish D width filled result' known offset receivers (fun T k => fresh T k-delta T k)) := by
  funext i
  change (if i ∈ D.1 ∨ i ∉ receivers then none else some fun T g =>
    if i ∈ C.holders T ∧ g < width then multTerms D width result known fresh T g+
      (if ∃ j ∈ D.1,filled T g = some j then offset i T g else 0) else 0) = _
  by_cases hi : i ∈ D.1 ∨ i ∉ receivers
  · simp [multFinish,addSharedOutput,hi]
  · simp only [addSharedOutput,multFinish,if_neg hi,Option.map_some]
    change (some fun T g => if i ∈ C.holders T ∧ g < width then
      multTerms D width result known fresh T g+(if ∃ j ∈ D.1,filled T g = some j then offset i T g else 0)
      else 0) = some (fun T g =>
        (if i ∈ C.holders T ∧ g < width then
          multTerms D width result' known (fun T k => fresh T k-delta T k) T g+
            (if ∃ j ∈ D.1,filled T g = some j then offset i T g else 0) else 0)+
          if i ∈ C.holders T ∧ g < width then delta T g else 0)
    congr 1
    funext T g
    by_cases hT : i ∈ C.holders T ∧ g < width
    · simp only [if_pos hT]
      rw [multTerms_translate D width result result' known delta fresh hknown hsum T g hT.2]
      ring
    · simp only [if_neg hT,add_zero]

/-- The fresh-table translation is measure preserving. -/
theorem multFresh_translate_uniform (width : ℕ) (delta : Shares C E) :
    𝒟[(fun fresh : C.Term → Fin width → E => fun T k => fresh T k-delta T k) <$>
      ($ᵗ (C.Term → Fin width → E))] = 𝒟[$ᵗ (C.Term → Fin width → E)] := by
  let e : (C.Term → Fin width → E) ≃ (C.Term → Fin width → E) :=
    Equiv.addRight (fun T k => -delta T k)
  have he : (fun fresh : C.Term → Fin width → E => fun T k => fresh T k-delta T k) = e := by
    funext fresh T k
    simp [e,sub_eq_add_neg]
  rw [he]
  apply evalDist_ext
  intro fresh
  exact probOutput_map_bijective_uniformSample _ e.bijective fresh

end ThresholdLeanXmssSecurity
end

/-! ## Final terms -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def balanceTerm (T₀ : C.Term) (total : E) (base : C.Term → E) : C.Term → E :=
  fun T => if T = T₀ then total-∑ T' ∈ univ.erase T₀,base T' else base T

lemma balanceTerm_sum (T₀ : C.Term) (total : E) (base : C.Term → E) :
    ∑ T,balanceTerm T₀ total base T = total := by
  rw [← sum_erase_add _ _ (mem_univ T₀)]
  have he : (∑ T ∈ univ.erase T₀,balanceTerm T₀ total base T) = ∑ T ∈ univ.erase T₀,base T := by
    apply Finset.sum_congr rfl
    intro T hT
    exact if_neg (mem_erase.mp hT).1
  rw [he]
  simp [balanceTerm]

lemma balanceTerm_known (D : C.Coalition) (T₀ : C.Term) (hT₀ : ¬ KnownTo D.1 T₀)
    (total : E) (base : C.Term → E) (hbase : ∀ T,KnownTo D.1 T → base T = 0)
    (T : C.Term) (hT : KnownTo D.1 T) : balanceTerm T₀ total base T = 0 := by
  have hne : T ≠ T₀ := by intro he; subst T; exact hT₀ hT
  simp [balanceTerm,hne,hbase T hT]

/-- The necessary changes to the two final multiplication outputs, at the term level. -/
def finalOutputDelta (T₀ : C.Term) (r q0 q2 : E) (d : C.Term → E) : Shares C E :=
  fun T g => if g = 0 then balanceTerm T₀ q0 (fun T => -(r/(1+r))*d T) T
    else if g = 1 then balanceTerm T₀ q2 (fun _ => 0) T else 0

lemma finalOutputDelta_sum (T₀ : C.Term) (r q0 q2 : E) (d : C.Term → E) :
    (∑ T,finalOutputDelta T₀ r q0 q2 d T 0) = q0 ∧
      (∑ T,finalOutputDelta T₀ r q0 q2 d T 1) = q2 := by
  simp only [finalOutputDelta,ite_true,one_ne_zero,if_false]
  exact ⟨balanceTerm_sum T₀ q0 _,balanceTerm_sum T₀ q2 _⟩

lemma finalOutputDelta_known (D : C.Coalition) (T₀ : C.Term) (hT₀ : ¬ KnownTo D.1 T₀)
    (r q0 q2 : E) (d : C.Term → E) (hd : ∀ T,KnownTo D.1 T → d T = 0)
    (T : C.Term) (hT : KnownTo D.1 T) (g : ℕ) : finalOutputDelta T₀ r q0 q2 d T g = 0 := by
  unfold finalOutputDelta
  split_ifs
  · exact balanceTerm_known D T₀ hT₀ q0 _ (fun T hT => by rw [hd T hT,mul_zero]) T hT
  · exact balanceTerm_known D T₀ hT₀ q2 _ (fun _ _ => rfl) T hT
  · rfl

/-- Scalar compatibility suffices to cancel the third opening at every replicated term. -/
theorem finalOutputDelta_cancel (T₀ : C.Term) (r q0 q2 : E) (d : C.Term → E) (hr : 1+r ≠ 0)
    (htotal : (1+r)*q0+r*(∑ T,d T)+r*(1+r)*q2 = 0) (T : C.Term) :
    (1+r)*finalOutputDelta T₀ r q0 q2 d T 0+r*d T+
      r*(1+r)*finalOutputDelta T₀ r q0 q2 d T 1 = 0 := by
  let residual : C.Term → E := fun T => (1+r)*finalOutputDelta T₀ r q0 q2 d T 0+r*d T+
    r*(1+r)*finalOutputDelta T₀ r q0 q2 d T 1
  have hnot : ∀ T,T ≠ T₀ → residual T = 0 := by
    intro T hT
    dsimp only [residual,finalOutputDelta]
    simp only [ite_true,one_ne_zero,if_false,balanceTerm,if_neg hT,mul_zero,add_zero]
    field_simp
    ring
  have hsum : ∑ T,residual T = 0 := by
    dsimp only [residual]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      ← Finset.mul_sum,← Finset.mul_sum,
      (finalOutputDelta_sum T₀ r q0 q2 d).1,(finalOutputDelta_sum T₀ r q0 q2 d).2]
    exact htotal
  change residual T = 0
  by_cases hT : T = T₀
  · subst T
    rw [← sum_erase_add _ residual (mem_univ T₀),Finset.sum_eq_zero (fun T hT => hnot T (mem_erase.mp hT).1),
      zero_add] at hsum
    exact hsum
  · exact hnot T hT

/-- The corresponding shifts preserve each operator's third opened Shamir share. -/
theorem finalOutputDelta_conv_cancel (K : Constants C E) (T₀ : C.Term) (r q0 q2 : E)
    (d : C.Term → E) (hr : 1+r ≠ 0)
    (htotal : (1+r)*q0+r*(∑ T,d T)+r*(1+r)*q2 = 0) (i : C.Party) :
    (1+r)*conv K (localContext i) (finalOutputDelta T₀ r q0 q2 d) 0+
      r*conv K (localContext i) (fun T _ => d T) 0+
      r*(1+r)*conv K (localContext i) (finalOutputDelta T₀ r q0 q2 d) 1 = 0 := by
  simp only [conv,localContext,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro T _
  have h := finalOutputDelta_cancel T₀ r q0 q2 d hr htotal T
  linear_combination psi K T i*h

/-- The scalar condition needed by the term translation follows from the three-opening identity. -/
theorem finalOutputDelta_compatible (a b a' b' wa wb d d' e0 e2 r : E)
    (hr : 1+r ≠ 0) (herror : d-a*b = d'-a'*b') :
    let wa' := wa+r/(1+r)*(a-a')
    let wb' := wb+r/(1+r)*(b-b')
    let q0 := (wa*wb+e0)-(wa'*wb'+e0)
    let q2 := ((wa+a)*(wb+b)+e2)-((wa'+a')*(wb'+b')+e2)
    (1+r)*q0+r*(d-d')+r*(1+r)*q2 = 0 := by
  dsimp only
  have ha := (final_mask_shift wa a a' r hr).symm
  have hb := (final_mask_shift wb b b' r hr).symm
  have h := final_three_openings a b a' b' wa wb _ _ d d' e0 e2 r herror ha hb
  linear_combination h

/-- Two consecutive fresh tables allow a triangular bijection: the second shift may depend on the first. -/
theorem sameRun_uniform_two_equivs (prims : Primitives) {α β γ : Type}
    [Fintype α] [SampleableType α] [Fintype β] [SampleableType β]
    (e : α ≃ α) (f : α → β ≃ β) (k : α → β → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (do let a ← liftComp ($ᵗ α) (LocalSpec C); let b ← liftComp ($ᵗ β) (LocalSpec C); k (e a) (f a b))
      (do let a ← liftComp ($ᵗ α) (LocalSpec C); let b ← liftComp ($ᵗ β) (LocalSpec C); k a b) := by
  refine (SameRun.bind_right (g := fun a => liftComp ($ᵗ β) (LocalSpec C) >>= k (e a))
    (liftComp ($ᵗ α) (LocalSpec C)) fun a => ?_).trans ?_
  · simpa only [bind_map_left] using
      (sameRun_uniform_equiv (C := C) prims (f a)).bind (fun b => SameRun.refl prims (k (e a) b))
  · simpa only [bind_map_left] using
      (sameRun_uniform_equiv (C := C) prims e).bind
        (fun a => SameRun.refl prims (liftComp ($ᵗ β) (LocalSpec C) >>= k a))

end ThresholdLeanXmssSecurity
end

/-! ## Digest commit -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

/-- One actual two-level salted digest, before it is inserted in the message vector. -/
def saltedDigestAnswer (prims : Primitives) (salt history : List Bit) :
    StateT (HashCache C) ProbComp HashOutput := do
  let h ← hashAnswer prims (.history history)
  hashAnswer prims (.digest salt h)

lemma relabelHashCache_digest_history (salt history : List Bit) (h h' : HashOutput) (s : HashCache C) :
    relabelHashCache (digestSwap salt h h') s (.history history) = s (.history history) := by
  have he := relabelHashCache_apply (digestSwap (C := C) salt h h') s (.history history)
  rw [digestSwap_history] at he
  exact he

/-- The real and dummy inner histories may both be publicly queried. Only their outer digest names move. -/
theorem saltedDigestAnswer_couple (prims : Primitives) (salt history history' : List Bit)
    (h h' : HashOutput) (s : HashCache C)
    (hh : s (.history history) = some h) (hh' : s (.history history') = some h') :
    (saltedDigestAnswer prims salt history').run (relabelHashCache (digestSwap salt h h') s) =
      (fun p => (p.1,relabelHashCache (digestSwap salt h h') p.2)) <$>
        (saltedDigestAnswer prims salt history).run s := by
  have hf : ∀ history : List Bit,¬ IsFixed (C := C) (.history history) := by
    intro history
    rintro ⟨_,he,_⟩
    cases he
  have hh'' : relabelHashCache (digestSwap salt h h') s (.history history') = some h' :=
    (relabelHashCache_digest_history salt history' h h' s).trans hh'
  unfold saltedDigestAnswer
  simp only [StateT.run_bind]
  rw [hashAnswer_run_cached prims (hf _) hh'',hashAnswer_run_cached prims (hf _) hh,pure_bind,pure_bind]
  exact hashAnswer_digestSwap prims salt h h' s

/-- The coupling extends through the entire adaptive local continuation after the digest is sent. -/
theorem saltedDigestAnswer_bind_couple (prims : Primitives) (salt history history' : List Bit)
    (h h' : HashOutput) (s : HashCache C)
    (hh : s (.history history) = some h) (hh' : s (.history history') = some h')
    {α : Type} (k : HashOutput → OracleComp (LocalSpec C) α) :
    ((saltedDigestAnswer prims salt history' >>= fun d => simulateQ (localDigestAnswer prims salt h h') (k d)).run
      (relabelHashCache (digestSwap salt h h') s)) =
    (fun p => (p.1,relabelHashCache (digestSwap salt h h') p.2)) <$>
      ((saltedDigestAnswer prims salt history >>= fun d => simulateQ (localAnswer prims) (k d)).run s) := by
  simp only [StateT.run_bind]
  rw [saltedDigestAnswer_couple prims salt history history' h h' s hh hh',bind_map_left,map_bind]
  apply bind_congr
  intro p
  exact localProgram_digestSwap prims salt h h' (k p.1) p.2

end ThresholdLeanXmssSecurity
end

/-! ## Lockstep -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O L R Ia α : Type}

lemma coalition_has_honest (D : C.Coalition) : ∃ i : C.Party,i ∉ D.1 := by
  have hc : D.1.card < (univ : Finset C.Party).card := by
    have := D.2
    have := C.one_le_t
    simp only [Finset.card_univ,Fintype.card_fin,Committee.n]
    omega
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨i,hi⟩

def callSteps (D : C.Coalition) (input : C.Party → I)
    (f : C.Party → Option O → PartyM C E (CallSpec I O) α) : C.Party → Step C E (CallSpec I O) α :=
  fun i => if i ∈ D.1 then .done none else .call (input i) (fun r => (f i r).run)

lemma startSteps_call (D : C.Coalition) (input : C.Party → I)
    (f : C.Party → Option O → PartyM C E (CallSpec I O) α) :
    startSteps localRoles D (fun i => call (input i) >>= f i) = pure (callSteps D input f) := by
  unfold startSteps
  simp only [localRoles,advance_call_bind]
  calc
    _ = Concrete.sequenceFin (fun i => pure (callSteps D input f i)) := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1 <;> simp only [hi,if_true,if_false,callSteps]
    _ = _ := sequenceFin_pure _

/-- A synchronous functionality call, for an arbitrary coalition and adaptive adversary. -/
theorem executePhase_call (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (input : C.Party → I)
    (f : C.Party → Option O → PartyM C E (CallSpec I O) α) :
    executePhase localRoles D A F (fuel+1) st (fun i => call (input i) >>= f i) = (do
      let (st',out) ← runFunctionality localRoles D A F st (fun i => if i ∈ D.1 then none else some (input i))
      executePhase localRoles D A F fuel st' (fun i => f i (out i))) := by
  have hn : ¬ ∀ i,i ∉ D.1 → (callSteps D input f i).isDone := by
    obtain ⟨i,hi⟩ := coalition_has_honest D
    intro h
    simpa [callSteps,hi,Step.isDone] using h i hi
  have hc : (∃ i,i ∉ D.1 ∧ (callSteps D input f i).callInput.isSome) ∧
      ∀ i,i ∉ D.1 → (callSteps D input f i).callInput.isSome ∨ (callSteps D input f i).isDone := by
    constructor
    · obtain ⟨i,hi⟩ := coalition_has_honest D
      exact ⟨i,hi,by simp [callSteps,hi,Step.callInput]⟩
    · intro i hi
      left
      simp [callSteps,hi,Step.callInput]
  have hin : (fun i => if i ∈ D.1 then none else (callSteps D input f i).callInput) =
      (fun i => if i ∈ D.1 then none else some (input i)) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp [callSteps,hi,Step.callInput]
  unfold executePhase
  rw [startSteps_call,pure_bind,executeRounds,if_neg hn]
  simp only [stepRound,if_pos hc,hin,bind_assoc,pure_bind]
  apply bind_congr
  intro p
  apply congrArg (fun start => start >>= executeRounds localRoles D A F fuel p.1)
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1 <;> simp [callSteps,hi,localRoles]

end ThresholdLeanXmssSecurity
end

/-! ## The halving input and callback -/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma ShamirDifference.congr (K : Constants C E) (D : C.Coalition)
    {a b a' b' : C.Party → E} (h : ShamirDifference K D a b)
    (ha : ∀ i,i ∉ D.1 → a' i = a i) (hb : ∀ i,i ∉ D.1 → b' i = b i) :
    ShamirDifference K D a' b' := by
  obtain ⟨P,hP,he,hD⟩ := h
  exact ⟨P,hP,fun i hi => by rw [ha i hi,hb i hi];exact he i hi,hD⟩

lemma ShamirDifference.ite (K : Constants C E) (D : C.Coalition)
    {a b : C.Party → E} (h : ShamirDifference K D a b) (p : Prop) [Decidable p] :
    ShamirDifference K D (fun i => if p then a i else 0) (fun i => if p then b i else 0) := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using ShamirDifference.refl K D (fun _ => 0)

def shamirPairInputs (D : C.Coalition) (A B U V : C.Party → ℕ → E) (n m : ℕ) :
    C.Party → Option (List (Product C E)) :=
  fun i => if i ∈ D.1 then none else some [.shamir (A i) (B i) n,.shamir (U i) (V i) m]

/-- The exact two-product input shape used by every halving step and by randomization. -/
theorem shamirPair_viewRelation (K : Constants C E) (D : C.Coalition)
    (A B U V A' B' U' V' : C.Party → ℕ → E) (n m : ℕ)
    (hA : ∀ k,ShamirDifference K D (fun i => A i k) (fun i => A' i k))
    (hB : ∀ k,ShamirDifference K D (fun i => B i k) (fun i => B' i k))
    (hU : ∀ k,ShamirDifference K D (fun i => U i k) (fun i => U' i k))
    (hV : ∀ k,ShamirDifference K D (fun i => V i k) (fun i => V' i k)) :
    ExtendViewRelation K D (shamirPairInputs D A B U V n m) (shamirPairInputs D A' B' U' V' n m) := by
  constructor
  · obtain ⟨i,hi,he⟩ := firstInput_honest (I := List (Product C E)) D (fun i => [.shamir (A i) (B i) n,.shamir (U i) (V i) m])
    obtain ⟨j,hj,he'⟩ := firstInput_honest (I := List (Product C E)) D (fun i => [.shamir (A' i) (B' i) n,.shamir (U' i) (V' i) m])
    change (firstInput (fun i => if i ∈ D.1 then none else some
      [Product.shamir (A i) (B i) n,Product.shamir (U i) (V i) m])).map Product.shape =
      (firstInput (fun i => if i ∈ D.1 then none else some
      [Product.shamir (A' i) (B' i) n,Product.shamir (U' i) (V' i) m])).map Product.shape
    rw [he,he']
    rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro g T _ i _
    by_cases hi : i ∈ D.1 <;> cases g with
    | zero => simp [shamirPairInputs,hi,Product.replicatedParts]
    | succ g => cases g <;> simp [shamirPairInputs,hi,Product.replicatedParts]
  · intro g T _ i _
    by_cases hi : i ∈ D.1 <;> cases g with
    | zero => simp [shamirPairInputs,hi,Product.replicatedParts]
    | succ g => cases g <;> simp [shamirPairInputs,hi,Product.replicatedParts]
  · intro g k
    cases g with
    | zero =>
      apply ShamirDifference.congr K D (hA k) <;> intro i hi <;> simp [shamirPairInputs,hi,Product.shamirParts]
    | succ g => cases g with
      | zero =>
        apply ShamirDifference.congr K D (hU k) <;> intro i hi <;> simp [shamirPairInputs,hi,Product.shamirParts]
      | succ g =>
        apply ShamirDifference.congr K D (ShamirDifference.refl K D (fun _ => (0 : E))) <;>
          intro i hi <;> simp [shamirPairInputs,hi]
  · intro g k
    cases g with
    | zero =>
      apply ShamirDifference.congr K D (hB k) <;> intro i hi <;> simp [shamirPairInputs,hi,Product.shamirParts]
    | succ g => cases g with
      | zero =>
        apply ShamirDifference.congr K D (hV k) <;> intro i hi <;> simp [shamirPairInputs,hi,Product.shamirParts]
      | succ g =>
        apply ShamirDifference.congr K D (ShamirDifference.refl K D (fun _ => (0 : E))) <;>
          intro i hi <;> simp [shamirPairInputs,hi]

/-- The complete adaptive callback on the two Shamir products preserves the adversary's state. -/
theorem shamirPair_call_shift {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (Adv : Adversary C E Ia (C.Party → List (Product C E))
      ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) (st : Adv.State)
    (A B U V A' B' U' V' : C.Party → ℕ → E) (n m : ℕ)
    (hA : ∀ k,ShamirDifference K D (fun i => A i k) (fun i => A' i k))
    (hB : ∀ k,ShamirDifference K D (fun i => B i k) (fun i => B' i k))
    (hU : ∀ k,ShamirDifference K D (fun i => U i k) (fun i => U' i k))
    (hV : ∀ k,ShamirDifference K D (fun i => V i k) (fun i => V' i k)) :
    let a := shamirPairInputs D A B U V n m
    let b := shamirPairInputs D A' B' U' V' n m
    runFunctionality localRoles D Adv (FextendMult K) st a =
      (fun out => (out.1,addHiddenOutput D 2
        (fun g => extendTotal K D a g-extendTotal K D b g) out.2)) <$>
        runFunctionality localRoles D Adv (FextendMult K) st b := by
  dsimp only
  have hlen : (firstInput (shamirPairInputs D A' B' U' V' n m)).length = 2 := by
    obtain ⟨j,hj,he⟩ := firstInput_honest (I := List (Product C E)) D
      (fun i => [.shamir (A' i) (B' i) n,.shamir (U' i) (V' i) m])
    change (firstInput (fun i => if i ∈ D.1 then none else some
      [Product.shamir (A' i) (B' i) n,Product.shamir (U' i) (V' i) m])).length = 2
    rw [he]
    rfl
  have h := runFunctionality_extend_shift localRoles K D Adv st
    (shamirPairInputs D A B U V n m) (shamirPairInputs D A' B' U' V' n m)
    (by intro i hi; simp [shamirPairInputs,hi])
    (shamirPair_viewRelation K D A B U V A' B' U' V' n m hA hB hU hV)
  simpa only [hlen] using h

/-- The input to the actual halving functionality has the same adversarial view in both runs. -/
theorem halving_view_eq (K : Constants C E) (D : C.Coalition)
    (A B A' B' : C.Party → ℕ → E) (length half : ℕ)
    (hA : ∀ k,ShamirDifference K D (fun i => A i k) (fun i => A' i k))
    (hB : ∀ k,ShamirDifference K D (fun i => B i k) (fun i => B' i k)) :
    let sum := fun (A : C.Party → ℕ → E) i k => A i k+if k+half < length then A i (k+half) else 0
    extendView K D.1 (shamirPairInputs D A B (sum A) (sum B) half half) =
      extendView K D.1 (shamirPairInputs D A' B' (sum A') (sum B') half half) := by
  dsimp only
  apply extendView_eq_of_relation K D
  apply shamirPair_viewRelation K D _ _ _ _ _ _ _ _ half half hA hB
  · intro k
    simpa only [one_mul] using ShamirDifference.lin K D (hA k)
      (ShamirDifference.ite K D (hA (k+half)) (k+half < length)) 1 1
  · intro k
    simpa only [one_mul] using ShamirDifference.lin K D (hB k)
      (ShamirDifference.ite K D (hB (k+half)) (k+half < length)) 1 1

end ThresholdLeanXmssSecurity
end

/-! ## Sum calls -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia I₁ O₁ L₁ R₁ I₂ O₂ L₂ R₂ : Type}

@[reducible] def leftAdversary [Inhabited R₁] (A : Adversary C E Ia (L₁ ⊕ L₂) (R₁ ⊕ R₂)) :
    Adversary C E Ia L₁ R₁ where
  State := A.State
  start := A.start
  round := A.round
  answer st l := do
    let p ← A.answer st (.inl l)
    pure (p.1, match p.2 with | .inl r => r | .inr _ => default)

@[reducible] def rightAdversary [Inhabited R₂] (A : Adversary C E Ia (L₁ ⊕ L₂) (R₁ ⊕ R₂)) :
    Adversary C E Ia L₂ R₂ where
  State := A.State
  start := A.start
  round := A.round
  answer st l := do
    let p ← A.answer st (.inr l)
    pure (p.1, match p.2 with | .inr r => r | .inl _ => default)

lemma runFunctionality_sum_inl [Inhabited R₁] [Inhabited R₂]
    (D : C.Coalition) (A : Adversary C E Ia (L₁ ⊕ L₂) (R₁ ⊕ R₂))
    (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂)
    (st : A.State) (inputs : C.Party → I₁) :
    runFunctionality localRoles D A (F₁.sum F₂) st
      (fun i => if i ∈ D.1 then none else some (.inl (inputs i))) =
    (fun p => (p.1,fun i => (p.2 i).map Sum.inl)) <$>
      runFunctionality localRoles D (leftAdversary A) F₁ st
        (fun i => if i ∈ D.1 then none else some (inputs i)) := by
  have hfull {T : Type} (v : C.Party → T) :
      ∀ i,i ∉ D.1 → ((if i ∈ D.1 then none else some (v i)) : Option T).isSome := by
    intro i hi
    simp [hi]
  have hl : ∀ i,∀ x ∈ (if i ∈ D.1 then none else some (Sum.inl (inputs i) : I₁ ⊕ I₂)),x.isLeft := by
    intro i
    by_cases hi : i ∈ D.1 <;> simp [hi]
  have hin : (fun i => (if i ∈ D.1 then none else some (Sum.inl (inputs i) : I₁ ⊕ I₂)).bind Sum.getLeft?) =
      (fun i => if i ∈ D.1 then none else some (inputs i)) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi]
  unfold runFunctionality
  rw [if_neg (not_not.mpr (hfull (fun i => (Sum.inl (inputs i) : I₁ ⊕ I₂)))),
    if_neg (not_not.mpr (hfull inputs))]
  simp only [Functionality.sum]
  rw [if_pos hl]
  simp only [hin, simulateQ_map, StateT.run_map, bind_map_left, map_bind, map_pure,pure_bind]
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  congr 1
  funext t
  rcases t with t | l
  · rfl
  · simp only [QueryImpl.apply_compose]
    erw [QueryImpl.add_apply_inr]
    simp only [leak]
    erw [QueryImpl.add_apply_inr]
    apply StateT.ext
    intro s
    simp [StateT.run_bind,localRoles,leftAdversary]
    erw [QueryImpl.add_apply_inr]
    simp only [StateT.run_mk,map_eq_bind_pure_comp,bind_assoc,Function.comp_def,pure_bind]
    apply bind_congr
    intro p
    rcases p with ⟨s,r|r⟩ <;> simp

lemma runFunctionality_sum_inr [Inhabited R₁] [Inhabited R₂]
    (D : C.Coalition) (A : Adversary C E Ia (L₁ ⊕ L₂) (R₁ ⊕ R₂))
    (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂)
    (st : A.State) (inputs : C.Party → I₂) :
    runFunctionality localRoles D A (F₁.sum F₂) st
      (fun i => if i ∈ D.1 then none else some (.inr (inputs i))) =
    (fun p => (p.1,fun i => (p.2 i).map Sum.inr)) <$>
      runFunctionality localRoles D (rightAdversary A) F₂ st
        (fun i => if i ∈ D.1 then none else some (inputs i)) := by
  have hfull {T : Type} (v : C.Party → T) :
      ∀ i,i ∉ D.1 → ((if i ∈ D.1 then none else some (v i)) : Option T).isSome := by
    intro i hi
    simp [hi]
  have hl : ∀ i,∀ x ∈ (if i ∈ D.1 then none else some (Sum.inr (inputs i) : I₁ ⊕ I₂)),x.isRight := by
    intro i
    by_cases hi : i ∈ D.1 <;> simp [hi]
  have hn : ¬ ∀ i,∀ x ∈ (if i ∈ D.1 then none else some (Sum.inr (inputs i) : I₁ ⊕ I₂)),x.isLeft := by
    obtain ⟨i,hi⟩ := coalition_has_honest D
    intro h
    simpa [hi] using h i (Sum.inr (inputs i)) (by simp [hi])
  have hin : (fun i => (if i ∈ D.1 then none else some (Sum.inr (inputs i) : I₁ ⊕ I₂)).bind Sum.getRight?) =
      (fun i => if i ∈ D.1 then none else some (inputs i)) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi]
  unfold runFunctionality
  rw [if_neg (not_not.mpr (hfull (fun i => (Sum.inr (inputs i) : I₁ ⊕ I₂)))),
    if_neg (not_not.mpr (hfull inputs))]
  simp only [Functionality.sum]
  rw [if_neg hn,if_pos hl]
  simp only [hin, simulateQ_map, StateT.run_map, bind_map_left, map_bind, map_pure,pure_bind]
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  congr 1
  funext t
  rcases t with t | l
  · rfl
  · simp only [QueryImpl.apply_compose]
    erw [QueryImpl.add_apply_inr]
    simp only [leak]
    erw [QueryImpl.add_apply_inr]
    apply StateT.ext
    intro s
    simp [StateT.run_bind,localRoles,rightAdversary]
    erw [QueryImpl.add_apply_inr]
    simp only [StateT.run_mk,map_eq_bind_pure_comp,bind_assoc,Function.comp_def,pure_bind]
    apply bind_congr
    intro p
    rcases p with ⟨s,r|r⟩ <;> simp

end ThresholdLeanXmssSecurity
end

/-! ## Scheduler -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O L R Ia α : Type}

lemma startSteps_congr_honest (D : C.Coalition)
    (a b : C.Party → PartyM C E (CallSpec I O) α) (h : ∀ i,i ∉ D.1 → a i = b i) :
    startSteps localRoles D a = startSteps localRoles D b := by
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1 <;> simp [hi,h]

lemma executePhase_congr_honest (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (a b : C.Party → PartyM C E (CallSpec I O) α) (h : ∀ i,i ∉ D.1 → a i = b i) :
    executePhase localRoles D A F fuel st a = executePhase localRoles D A F fuel st b := by
  unfold executePhase
  rw [startSteps_congr_honest D a b h]

lemma startSteps_failure (D : C.Coalition) :
    startSteps localRoles D (fun _ => (failure : PartyM C E (CallSpec I O) α)) =
      pure (fun _ => Step.done none) := by
  unfold startSteps
  simp only [localRoles,advance_run_failure]
  simpa using sequenceFin_pure (fun _ : C.Party => (Step.done none : Step C E (CallSpec I O) α))

lemma executePhase_failure (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) :
    executePhase localRoles D A F fuel st (fun _ => (failure : PartyM C E (CallSpec I O) α)) =
      pure (st,fun _ => none) := by
  unfold executePhase
  rw [startSteps_failure,pure_bind]
  cases fuel <;> simp [executeRounds,Step.isDone,Step.output]

def optionalCall (input : Option I) (f : Option O → PartyM C E (CallSpec I O) α) :
    PartyM C E (CallSpec I O) α :=
  match input with
  | some v => call v >>= f
  | none => failure

def optionalCallSteps (D : C.Coalition) (input : C.Party → Option I)
    (f : C.Party → Option O → PartyM C E (CallSpec I O) α) : C.Party → Step C E (CallSpec I O) α :=
  fun i => if i ∈ D.1 then .done none else match input i with
    | some v => .call v (fun r => (f i r).run)
    | none => .done none

lemma startSteps_optionalCall (D : C.Coalition) (input : C.Party → Option I)
    (f : C.Party → Option O → PartyM C E (CallSpec I O) α) :
    startSteps localRoles D (fun i => optionalCall (input i) (f i)) = pure (optionalCallSteps D input f) := by
  unfold startSteps
  calc
    _ = Concrete.sequenceFin (fun i => pure (optionalCallSteps D input f i)) := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [hi,optionalCallSteps]
      · cases hv : input i <;>
          simp only [hi,if_false,hv,optionalCall,optionalCallSteps,localRoles,advance_run_failure,advance_call_bind]
    _ = _ := sequenceFin_pure _

/-- A partial functionality call has the scheduler's exact global-abort behavior. -/
theorem executePhase_optionalCall (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (input : C.Party → Option I)
    (f : C.Party → Option O → PartyM C E (CallSpec I O) α)
    (hf : ∀ i,i ∉ D.1 → f i none = failure) :
    executePhase localRoles D A F (fuel+1) st (fun i => optionalCall (input i) (f i)) = (do
      let (st',out) ← runFunctionality localRoles D A F st (fun i => if i ∈ D.1 then none else input i)
      executePhase localRoles D A F fuel st' (fun i => f i (out i))) := by
  by_cases ha : ∃ i,i ∉ D.1 ∧ (input i).isSome
  · have hn : ¬ ∀ i,i ∉ D.1 → (optionalCallSteps D input f i).isDone := by
      obtain ⟨i,hi,hv⟩ := ha
      intro h
      cases he : input i with
      | none => simp [he] at hv
      | some v => simpa [optionalCallSteps,hi,he,Step.isDone] using h i hi
    have hc : (∃ i,i ∉ D.1 ∧ (optionalCallSteps D input f i).callInput.isSome) ∧
        ∀ i,i ∉ D.1 → (optionalCallSteps D input f i).callInput.isSome ∨ (optionalCallSteps D input f i).isDone := by
      constructor
      · obtain ⟨i,hi,hv⟩ := ha
        refine ⟨i,hi,?_⟩
        cases he : input i <;> simp_all [optionalCallSteps,Step.callInput]
      · intro i hi
        cases he : input i <;> simp [optionalCallSteps,hi,he,Step.callInput,Step.isDone]
    have hin : (fun i => if i ∈ D.1 then none else (optionalCallSteps D input f i).callInput) =
        (fun i => if i ∈ D.1 then none else input i) := by
      funext i
      by_cases hi : i ∈ D.1 <;> cases he : input i <;> simp [optionalCallSteps,hi,he,Step.callInput]
    unfold executePhase
    rw [startSteps_optionalCall,pure_bind,executeRounds,if_neg hn]
    simp only [stepRound,if_pos hc,hin,bind_assoc,pure_bind]
    by_cases hall : ∀ i,i ∉ D.1 → (input i).isSome
    · have hv : ∀ i,i ∉ D.1 → ∃ v,input i = some v := by
        intro i hi
        exact Option.isSome_iff_exists.mp (hall i hi)
      apply bind_congr
      intro p
      apply congrArg (fun start => start >>= executeRounds localRoles D A F fuel p.1)
      unfold startSteps
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [optionalCallSteps,hi]
      · obtain ⟨v,hv⟩ := hv i hi
        simp [optionalCallSteps,hi,hv,localRoles]
    · have hnfull : ¬ ∀ i,i ∉ D.1 → ((if i ∈ D.1 then none else input i) : Option I).isSome := by
        intro h
        apply hall
        intro i hi
        simpa [hi] using h i hi
      simp only [runFunctionality,if_pos hnfull,pure_bind]
      apply congrArg (fun start => start >>= executeRounds localRoles D A F fuel st)
      unfold startSteps
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [optionalCallSteps,hi]
      · cases he : input i <;>
          simp only [optionalCallSteps,hi,if_false,he,localRoles,hf i hi,advance_run_failure]
  · have hi : ∀ i,i ∉ D.1 → input i = none := by
      intro i hi
      cases he : input i
      · rfl
      · exact False.elim (ha ⟨i,hi,by simp [he]⟩)
    rw [executePhase_congr_honest D A F (fuel+1) st _ (fun _ => failure)
      (fun i h => by simp [optionalCall,hi i h]),executePhase_failure]
    have hnfull : ¬ ∀ i,i ∉ D.1 → ((if i ∈ D.1 then none else input i) : Option I).isSome := by
      obtain ⟨i,hD⟩ := coalition_has_honest D
      intro h
      simpa [hD,hi i hD] using h i hD
    simp only [runFunctionality,if_pos hnfull,pure_bind]
    rw [executePhase_congr_honest D A F fuel st _ (fun _ => failure) hf,executePhase_failure]

end ThresholdLeanXmssSecurity
end

/-! ## Check calls -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

abbrev CheckAdversary (C : Committee) (E Ia : Type) :=
  Adversary C E Ia ((List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit))
    ((Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
      ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit))))

lemma runCheck_coin (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (st : A.State) (input : C.Party → ℕ) :
    runFunctionality localRoles D A (checkFunctionalities K) st
      (fun i => if i ∈ D.1 then none else some (.inl (.inl (input i)))) =
      (fun p => (p.1,fun i => (p.2 i).map (Sum.inl ∘ Sum.inl))) <$>
        runFunctionality localRoles D (leftAdversary (leftAdversary A)) (Fcoin (E := E)) st
          (fun i => if i ∈ D.1 then none else some (input i)) := by
  rw [checkFunctionalities,runFunctionality_sum_inl,runFunctionality_sum_inl]
  simp only [Functor.map_map,Function.comp_def,Option.map_map]

lemma runCheck_extend (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (st : A.State) (input : C.Party → List (Product C E)) :
    runFunctionality localRoles D A (checkFunctionalities K) st
      (fun i => if i ∈ D.1 then none else some (.inl (.inr (input i)))) =
      (fun p => (p.1,fun i => (p.2 i).map (Sum.inl ∘ Sum.inr))) <$>
        runFunctionality localRoles D (rightAdversary (leftAdversary A)) (FextendMult K) st
          (fun i => if i ∈ D.1 then none else some (input i)) := by
  rw [checkFunctionalities,runFunctionality_sum_inl,runFunctionality_sum_inr]
  simp only [Functor.map_map,Function.comp_def,Option.map_map]

lemma runCheck_randElements (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (st : A.State) (input : C.Party → ℕ) :
    runFunctionality localRoles D A (checkFunctionalities K) st
      (fun i => if i ∈ D.1 then none else some (.inr (.inl (input i)))) =
      (fun p => (p.1,fun i => (p.2 i).map (Sum.inr ∘ Sum.inl))) <$>
        runFunctionality localRoles D (leftAdversary (rightAdversary A)) (Frand E) st
          (fun i => if i ∈ D.1 then none else some (input i)) := by
  rw [checkFunctionalities,runFunctionality_sum_inr,runFunctionality_sum_inl]
  simp only [Functor.map_map,Function.comp_def,Option.map_map]

lemma runCheck_randBits (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (st : A.State) (input : C.Party → ℕ) :
    runFunctionality localRoles D A (checkFunctionalities K) st
      (fun i => if i ∈ D.1 then none else some (.inr (.inr (input i)))) =
      (fun p => (p.1,fun i => (p.2 i).map (Sum.inr ∘ Sum.inr))) <$>
        runFunctionality localRoles D (rightAdversary (rightAdversary A)) (Frand Bit) st
          (fun i => if i ∈ D.1 then none else some (input i)) := by
  rw [checkFunctionalities,runFunctionality_sum_inr,runFunctionality_sum_inr]
  simp only [Functor.map_map,Function.comp_def,Option.map_map]

/-- The actual check-interface multiplication call has the same hidden-output coupling. -/
theorem runCheck_extend_shift (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (st : A.State) (a b : C.Party → List (Product C E))
    (h : ExtendViewRelation K D (fun i => if i ∈ D.1 then none else some (a i))
      (fun i => if i ∈ D.1 then none else some (b i))) :
    runFunctionality localRoles D A (checkFunctionalities K) st
      (fun i => if i ∈ D.1 then none else some (.inl (.inr (a i)))) =
      (fun p => (p.1,fun i =>
        ((addHiddenOutput D (firstInput (fun j => if j ∈ D.1 then none else some (b j))).length
          (fun g => extendTotal K D (fun j => if j ∈ D.1 then none else some (a j)) g -
            extendTotal K D (fun j => if j ∈ D.1 then none else some (b j)) g) p.2) i).map
          (Sum.inl ∘ Sum.inr))) <$>
        runFunctionality localRoles D (rightAdversary (leftAdversary A)) (FextendMult K) st
          (fun i => if i ∈ D.1 then none else some (b i)) := by
  rw [runCheck_extend,runFunctionality_extend_shift localRoles K D (rightAdversary (leftAdversary A)) st _ _ (by
    intro i hi
    simp [hi]) h]
  simp only [Functor.map_map,Function.comp_def]

end ThresholdLeanXmssSecurity
end

/-! ## Check phases -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def afterExtend (K : Constants C E) (i : C.Party) (width : ℕ) (hs : RunState C)
    (f : Shares C E → RunM C E (CheckSpec C E) α) (out : Option (Shares C E)) :
    PartyM C E (CheckSpec C E) α :=
  match out with
  | some z => (f z).run' ⟨recordHistory K i hs.history z width,hs.label+1,hs.tag⟩
  | none => failure

/-- An actual check multiplication phase, with arbitrary continuation and local history. -/
theorem executePhase_extend (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (products : C.Party → List (Product C E)) (hs : C.Party → RunState C)
    (f : C.Party → Shares C E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => ((hybridCheckGadgets K i).extendMult (products i) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (rightAdversary (leftAdversary A)) (FextendMult K) st
        (fun i => if i ∈ D.1 then none else some (products i))
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterExtend K i (products i).length (hs i) (f i) (p.2 i))) := by
  simp_rw [extendMult_run']
  rw [executePhase_call,runCheck_extend,bind_map_left]
  apply bind_congr
  intro p
  dsimp only
  congr 1
  funext i
  cases he : p.2 i <;> rfl

/-- The hidden-input translation is preserved through the real scheduler and the recorded history. -/
theorem executePhase_extend_shift (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (a b : C.Party → List (Product C E)) (hs : C.Party → RunState C)
    (f : C.Party → Shares C E → RunM C E (CheckSpec C E) α)
    (h : ExtendViewRelation K D (fun i => if i ∈ D.1 then none else some (a i))
      (fun i => if i ∈ D.1 then none else some (b i))) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => ((hybridCheckGadgets K i).extendMult (a i) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (rightAdversary (leftAdversary A)) (FextendMult K) st
        (fun i => if i ∈ D.1 then none else some (b i))
      let out := addHiddenOutput D (firstInput (fun j => if j ∈ D.1 then none else some (b j))).length
        (fun g => extendTotal K D (fun j => if j ∈ D.1 then none else some (a j)) g -
          extendTotal K D (fun j => if j ∈ D.1 then none else some (b j)) g) p.2
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterExtend K i (a i).length (hs i) (f i) (out i))) := by
  rw [executePhase_extend,runFunctionality_extend_shift localRoles K D (rightAdversary (leftAdversary A)) st _ _ (by
    intro i hi
    simp [hi]) h,bind_map_left]

def afterChallenge (K : Constants C E) (hs : RunState C)
    (f : E → RunM C E (CheckSpec C E) α) (out : Option (List E)) :
    PartyM C E (CheckSpec C E) α :=
  match out with
  | some v => oracleStep (challengeQuery K hs.tag hs.label v) >>= fun r => match r with
      | some r => (f r).run' ⟨hs.history,hs.label+1,hs.tag⟩
      | none => failure
  | none => failure

theorem executePhase_challenge (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (hs : C.Party → RunState C)
    (f : C.Party → E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => (challenge K (hybridCheckGadgets K i) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (leftAdversary (leftAdversary A)) (Fcoin (E := E)) st
        (fun i => if i ∈ D.1 then none else some 1)
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterChallenge K (hs i) (f i) (p.2 i))) := by
  simp_rw [challenge_run']
  rw [executePhase_call,runCheck_coin,bind_map_left]
  apply bind_congr
  intro p
  dsimp only
  congr 1
  funext i
  cases he : p.2 i <;> rfl

end ThresholdLeanXmssSecurity
end

/-! ## Exchange -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O L R Ia α : Type}

def optionalExchange (outbox : Option (Mail C E)) (f : Mail C E → PartyM C E (CallSpec I O) α) :
    PartyM C E (CallSpec I O) α := match outbox with
  | some out => exchange out >>= f
  | none => failure

def optionalExchangeSteps (D : C.Coalition) (outbox : C.Party → Option (Mail C E))
    (f : C.Party → Mail C E → PartyM C E (CallSpec I O) α) : C.Party → Step C E (CallSpec I O) α :=
  fun i => if i ∈ D.1 then .done none else match outbox i with
    | some out => .wait out (exchangeResume (f i))
    | none => .done none

lemma startSteps_optionalExchange (D : C.Coalition) (outbox : C.Party → Option (Mail C E))
    (f : C.Party → Mail C E → PartyM C E (CallSpec I O) α) :
    startSteps localRoles D (fun i => optionalExchange (outbox i) (f i)) =
      pure (optionalExchangeSteps D outbox f) := by
  unfold startSteps
  calc
    _ = Concrete.sequenceFin (fun i => pure (optionalExchangeSteps D outbox f i)) := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [hi,optionalExchangeSteps]
      · cases hv : outbox i <;>
          simp only [hi,if_false,hv,optionalExchange,optionalExchangeSteps,localRoles,
            advance_run_failure,advance_exchange_bind]
    _ = _ := sequenceFin_pure _

def afterExchange (D : C.Coalition) (outbox : C.Party → Option (Mail C E))
    (sent : C.Party → Mail C E) (i : C.Party)
    (f : Mail C E → PartyM C E (CallSpec I O) α) : PartyM C E (CallSpec I O) α :=
  match outbox i with
  | none => failure
  | some _ =>
      let inbox := fun k => if k ∈ D.1 then sent k i else
        ((outbox k).getD (fun _ => some .abort)) i
      if C.parties.any (fun j => Msg.isAbort (inbox j)) then failure else f inbox

/-- A network round includes every abort frame and the rushing adversary's full callback. -/
theorem executePhase_optionalExchange (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (outbox : C.Party → Option (Mail C E)) (f : C.Party → Mail C E → PartyM C E (CallSpec I O) α)
    (ha : ∃ i,i ∉ D.1 ∧ (outbox i).isSome) :
    executePhase localRoles D A F (fuel+1) st (fun i => optionalExchange (outbox i) (f i)) = (do
      let p ← A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
        ((outbox i).getD (fun _ => none)) c else none)
      executePhase localRoles D A F fuel p.1 (fun i => afterExchange D outbox p.2 i (f i))) := by
  have hn : ¬ ∀ i,i ∉ D.1 → (optionalExchangeSteps D outbox f i).isDone := by
    obtain ⟨i,hi,hv⟩ := ha
    intro h
    cases he : outbox i with
    | none => simp [he] at hv
    | some v => simpa [optionalExchangeSteps,hi,he,Step.isDone] using h i hi
  have hc : ¬ ((∃ i,i ∉ D.1 ∧ (optionalExchangeSteps D outbox f i).callInput.isSome) ∧
      ∀ i,i ∉ D.1 → (optionalExchangeSteps D outbox f i).callInput.isSome ∨
        (optionalExchangeSteps D outbox f i).isDone) := by
    rintro ⟨⟨i,hi,hv⟩,_⟩
    cases he : outbox i <;> simp [optionalExchangeSteps,hi,he,Step.callInput] at hv
  have hout : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (optionalExchangeSteps D outbox f i).outbox c else none) =
      (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then ((outbox i).getD (fun _ => none)) c else none) := by
    funext c i
    by_cases hi : i ∈ D.1 <;> cases he : outbox i <;> simp [hi,he,optionalExchangeSteps,Step.outbox]
  have hin (sent : C.Party → Mail C E) (j : C.Party) :
      (fun k => if k ∈ D.1 then sent k j else (optionalExchangeSteps D outbox f k).delivered j) =
      (fun k => if k ∈ D.1 then sent k j else ((outbox k).getD (fun _ => some .abort)) j) := by
    funext k
    by_cases hk : k ∈ D.1 <;> cases he : outbox k <;> simp [hk,he,optionalExchangeSteps,Step.delivered]
  unfold executePhase
  rw [startSteps_optionalExchange,pure_bind,executeRounds,if_neg hn]
  simp only [stepRound,if_neg hc,hout,localRoles,bind_assoc,pure_bind]
  apply bind_congr
  intro p
  apply congrArg (fun start => start >>= executeRounds localRoles D A F fuel p.1)
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [optionalExchangeSteps,hi]
  · cases he : outbox i with
    | none => simp only [optionalExchangeSteps,hi,if_false,he,afterExchange,localRoles,advance_run_failure]
    | some v =>
        simp only [optionalExchangeSteps,hi,if_false,he,localRoles]
        change advance (exchangeResume (f i) (fun k => if k ∈ D.1 then p.2 k i else
          (optionalExchangeSteps D outbox f k).delivered i)) = _
        rw [hin]
        simp only [afterExchange,he,exchangeResume]
        split_ifs <;> rfl

end ThresholdLeanXmssSecurity
end

/-! ## Prefetch -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

/-- An unobserved local computation can be prefetched, even when it changes the oracle cache. -/
theorem local_prefetch_output (prims : Primitives) {α β : Type}
    (probe : OracleComp (LocalSpec C) β) (oa : OracleComp (LocalSpec C) α) (s : HashCache C) :
    𝒟[(simulateQ (localAnswer prims) (probe >>= fun _ => oa)).run' s] =
      𝒟[(simulateQ (localAnswer prims) oa).run' s] := by
  have h := sameRun_swap prims probe oa (fun _ a => pure a) s
  simp only [bind_pure] at h
  have hp := congrArg (fun d => Prod.fst <$> d) h
  simp only [← evalDist_map] at hp
  rw [StateT.run'_eq]
  refine hp.trans ?_
  simp only [simulateQ_bind,simulateQ_pure,StateT.run_bind,StateT.run_pure,map_bind,map_pure]
  rw [StateT.run'_eq,map_eq_bind_pure_comp]
  simp only [evalDist_bind,Function.comp_def]
  congr 1
  funext p
  rw [← evalDist_bind]
  apply evalDist_ext
  intro a
  rw [probOutput_bind_const,probFailure_eq_zero,tsub_zero,one_mul]

end ThresholdLeanXmssSecurity
end

/-! ## Local calls -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O L R Ia α : Type}

/-- The functionality's local oracle and adaptive reply interpreted in the local world. -/
def localHybridImpl (A : Adversary C E Ia L R) :
    QueryImpl (LocalSpec C + (L →ₒ R)) (StateT A.State (OracleComp (LocalSpec C))) :=
  (fun (t : (LocalSpec C).Domain) => (StateT.lift (OracleComp.lift (OracleSpec.query t)) : StateT A.State (OracleComp (LocalSpec C)) _)) +
    (fun l => StateT.mk fun st => do
      let p ← A.answer st l
      pure (p.2,p.1))

lemma localHybridImpl_sample (A : Adversary C E Ia L R) (p : ProbComp α) :
    simulateQ (localHybridImpl A) (liftComp p (LocalSpec C + (L →ₒ R))) =
      StateT.lift (liftComp p (LocalSpec C)) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp; rfl
  | query_bind t k ih =>
      rw [liftComp_bind,simulateQ_bind,liftComp_bind]
      simp only [ih]
      have hl {β γ : Type} (oa : OracleComp (LocalSpec C) β) (f : β → OracleComp (LocalSpec C) γ) :
          (StateT.lift (oa >>= f) : StateT A.State _ γ) = StateT.lift oa >>= fun a => StateT.lift (f a) := by
        ext s
        simp [StateT.lift]
      rw [hl]
      congr 1

lemma localHybridImpl_leak (A : Adversary C E Ia L R) (l : L) :
    simulateQ (localHybridImpl A) (leak (C := C) l) =
      StateT.mk (fun st => (fun p => (p.2,p.1)) <$> A.answer st l) := by
  unfold leak
  erw [simulateQ_query]
  change (fun r : R => r) <$> localHybridImpl A (.inr l) = _
  rw [id_map']
  rfl

lemma runFunctionality_local (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (st : A.State) (inputs : C.Party → Option I)
    (h : ∀ i,i ∉ D.1 → (inputs i).isSome) :
    runFunctionality localRoles D A F st inputs =
      (fun p => (p.2,p.1)) <$> ((simulateQ (localHybridImpl A) (F.run D inputs)).run st) := by
  unfold runFunctionality
  rw [if_neg (not_not.mpr h)]
  simp only [pure_bind]
  rfl

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

theorem runFunctionality_coin_local (D : C.Coalition)
    (A : Adversary C E Ia (List E) (Finset C.Party)) (st : A.State)
    (inputs : C.Party → Option ℕ) (h : ∀ i,i ∉ D.1 → (inputs i).isSome) :
    runFunctionality localRoles D A (Fcoin (E := E)) st inputs = (do
      let v ← liftComp ($ᵗ (Fin (firstInput inputs) → E)) (LocalSpec C)
      let p ← A.answer st (List.ofFn v)
      pure (p.1,fun i => if i ∉ D.1 ∧ i ∈ p.2 then some (List.ofFn v) else none)) := by
  rw [runFunctionality_local D A _ st inputs h]
  simp only [Fcoin,sample,simulateQ_bind,localHybridImpl_sample,localHybridImpl_leak,simulateQ_pure,
    StateT.run_bind,StateT.run_lift,StateT.run_pure,StateT.run_mk,map_bind,map_pure,bind_map_left,bind_assoc,pure_bind]

/-- An adaptive multiplication reply precedes the fresh output table. -/
theorem runFunctionality_extend_local (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E Ia (C.Party → List (Product C E))
      ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) (st : A.State)
    (inputs : C.Party → Option (List (Product C E))) (h : ∀ i,i ∉ D.1 → (inputs i).isSome) :
    runFunctionality localRoles D A (FextendMult K) st inputs = (do
      let p ← A.answer st (extendView K D.1 inputs)
      let fresh ← liftComp ($ᵗ (C.Term → Fin (firstInput inputs).length → E)) (LocalSpec C)
      pure (p.1,multFinish D (firstInput inputs).length (filler K .peer)
        (fun g => extendTotal K D inputs g+p.2.1 g) p.2.2.1 p.2.2.2.1 p.2.2.2.2 fresh)) := by
  rw [runFunctionality_local D A _ st inputs h,FextendMult_run_finish]
  simp only [sample,simulateQ_bind,localHybridImpl_sample,localHybridImpl_leak,simulateQ_pure,
    StateT.run_bind,StateT.run_lift,StateT.run_pure,StateT.run_mk,map_bind,map_pure,bind_map_left,
    bind_assoc,pure_bind]

def randFinish {R : Type} [Zero R] (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin count → R)
    (freshPair : C.Pair → Fin count → R) : C.Party → Option (PrssOutput C R) := fun i =>
  if i ∈ D.1 then none else some
    (fun T => if i ∈ C.holders T then
      (if KnownTo D.1 T then known T else fun g => if h : g < count then fresh T ⟨g,h⟩ else 0)
      else fun _ => 0,
    fun j => if h : i = j then fun _ => 0 else if j ∈ D.1 then knownPairs j i
      else fun g => if h' : g < count then freshPair (C.pairOf i j h) ⟨g,h'⟩ else 0)

theorem runFunctionality_rand_local {R : Type} [AddCommGroup R] [SampleableType R] (D : C.Coalition)
    (A : Adversary C E Ia Unit (Shares C R × (C.Party → C.Party → ℕ → R))) (st : A.State)
    (inputs : C.Party → Option ℕ) (h : ∀ i,i ∉ D.1 → (inputs i).isSome) :
    runFunctionality localRoles D A (Frand R) st inputs = (do
      let p ← A.answer st ()
      let fresh ← liftComp ($ᵗ (C.Term → Fin (firstInput inputs) → R)) (LocalSpec C)
      let pairs ← liftComp ($ᵗ (C.Pair → Fin (firstInput inputs) → R)) (LocalSpec C)
      pure (p.1,randFinish D (firstInput inputs) p.2.1 p.2.2 fresh pairs)) := by
  rw [runFunctionality_local D A _ st inputs h]
  simp only [Frand,sample,simulateQ_bind,localHybridImpl_sample,localHybridImpl_leak,simulateQ_pure,
    StateT.run_bind,StateT.run_lift,StateT.run_pure,StateT.run_mk,map_bind,map_pure,bind_map_left,
    bind_assoc,pure_bind]
  rfl

end ThresholdLeanXmssSecurity
end

/-! ## Mask leak -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def randShares (D : C.Coalition) (count : ℕ) (known : Shares C E)
    (fresh : C.Term → Fin count → E) (i : C.Party) : Shares C E := fun T g =>
  if i ∈ C.holders T then
    if KnownTo D.1 T then known T g else if h : g < count then fresh T ⟨g,h⟩ else 0
  else 0

lemma randFinish_shares (D : C.Coalition) (count : ℕ) (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (fresh : C.Term → Fin count → E)
    (pairs : C.Pair → Fin count → E) (i : C.Party) (hi : i ∉ D.1) :
    ((randFinish D count known knownPairs fresh pairs i).map Prod.fst) =
      some (randShares D count known fresh i) := by
  simp only [randFinish,if_neg hi,Option.map_some]
  congr 1
  funext T g
  by_cases ht : i ∈ C.holders T <;> by_cases hk : KnownTo D.1 T <;> simp [randShares,ht,hk]

lemma randShares_hiddenDifference (D : C.Coalition) (count : ℕ) (known : Shares C E)
    (a b : C.Term → Fin count → E) :
    HiddenDifference D (randShares D count known a) (randShares D count known b) := by
  refine ⟨fun T g => if KnownTo D.1 T then 0 else
    if h : g < count then a T ⟨g,h⟩-b T ⟨g,h⟩ else 0,?_,?_⟩
  · intro T hT g
    simp [hT]
  · intro i hi T hT g
    unfold randShares
    simp only [if_pos hT]
    by_cases hk : KnownTo D.1 T <;> by_cases hg : g < count <;> simp [hk,hg]

/-- The masked multiplication leak is independent of every hidden entry of the mask table. -/
theorem final_mask_leak_independent (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (a b : C.Term → Fin 2 → E) (A B : C.Party → E) :
    extendView K D.1 (shamirPairInputs D
      (fun i _ => conv K (localContext i) (randShares D 2 known a i) 0)
      (fun i _ => conv K (localContext i) (randShares D 2 known a i) 1)
      (fun i _ => conv K (localContext i) (randShares D 2 known a i) 0+A i)
      (fun i _ => conv K (localContext i) (randShares D 2 known a i) 1+B i) 1 1) =
    extendView K D.1 (shamirPairInputs D
      (fun i _ => conv K (localContext i) (randShares D 2 known b i) 0)
      (fun i _ => conv K (localContext i) (randShares D 2 known b i) 1)
      (fun i _ => conv K (localContext i) (randShares D 2 known b i) 0+A i)
      (fun i _ => conv K (localContext i) (randShares D 2 known b i) 1+B i) 1 1) := by
  have h := randShares_hiddenDifference D 2 known a b
  have ha := h.conv K D 0
  have hb := h.conv K D 1
  apply extendView_eq_of_relation
  apply shamirPair_viewRelation
  · intro k
    exact ha
  · intro k
    exact hb
  · intro k
    simpa only [one_mul] using ShamirDifference.lin K D ha (ShamirDifference.refl K D A) 1 1
  · intro k
    simpa only [one_mul] using ShamirDifference.lin K D hb (ShamirDifference.refl K D B) 1 1

end ThresholdLeanXmssSecurity
end

/-! ## Mask defer -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E σ τ γ : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

abbrev MaskTable (C : Committee) (E : Type) := C.Term → Fin 2 → E

def maskedView (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (A B : C.Party → E) : C.Party → List (Product C E) :=
  extendView K D.1 (shamirPairInputs D
    (fun i _ => conv K (localContext i) (randShares D 2 known w i) 0)
    (fun i _ => conv K (localContext i) (randShares D 2 known w i) 1)
    (fun i _ => conv K (localContext i) (randShares D 2 known w i) 0+A i)
    (fun i _ => conv K (localContext i) (randShares D 2 known w i) 1+B i) 1 1)

lemma maskedView_eq (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (a b : MaskTable C E) (A B : C.Party → E) :
    maskedView K D known a A B = maskedView K D known b A B :=
  final_mask_leak_independent K D known a b A B

/-- The actual masked leak allows both secret tables to be sampled after any intervening
transcript whose only input from this call is the adversary's reply. -/
theorem maskedTables_defer (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (known : Shares C E) (A B : C.Party → E)
    (reply : (C.Party → List (Product C E)) → OracleComp (LocalSpec C) σ)
    (transcript : σ → OracleComp (LocalSpec C) τ)
    (k : σ → τ → MaskTable C E → MaskTable C E → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let p ← reply (maskedView K D known w A B)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let t ← transcript p
        k p t w q)
      (do
        let p ← reply (maskedView K D known 0 A B)
        let t ← transcript p
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        k p t w q) := by
  have hv : ∀ w,maskedView K D known w A B = maskedView K D known 0 A B :=
    fun w => maskedView_eq K D known w 0 A B
  simp_rw [hv]
  refine (sameRun_swap prims (liftComp ($ᵗ (MaskTable C E)) (LocalSpec C))
    (reply (maskedView K D known 0 A B)) _).trans ?_
  refine SameRun.bind_right _ fun p => ?_
  refine (SameRun.bind_right (g := fun w => transcript p >>= fun t =>
    liftComp ($ᵗ (MaskTable C E)) (LocalSpec C) >>= fun q => k p t w q)
    (liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)) fun w => ?_).trans ?_
  · exact sameRun_swap prims _ (transcript p) _
  · exact sameRun_swap prims _ (transcript p) _

/-- The late transcript may choose the triangular, measure-preserving table translation. -/
theorem maskedTables_late_bijection (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (known : Shares C E) (A B : C.Party → E)
    (reply : (C.Party → List (Product C E)) → OracleComp (LocalSpec C) σ)
    (transcript : σ → OracleComp (LocalSpec C) τ)
    (e : σ → τ → MaskTable C E ≃ MaskTable C E)
    (f : σ → τ → MaskTable C E → MaskTable C E ≃ MaskTable C E)
    (k : σ → τ → MaskTable C E → MaskTable C E → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let p ← reply (maskedView K D known w A B)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let t ← transcript p
        k p t (e p t w) (f p t w q))
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let p ← reply (maskedView K D known w A B)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let t ← transcript p
        k p t w q) := by
  refine (maskedTables_defer prims K D known A B reply transcript
    (fun p t w q => k p t (e p t w) (f p t w q))).trans ?_
  refine SameRun.trans ?_ (maskedTables_defer prims K D known A B reply transcript k).symm
  refine SameRun.bind_right _ fun p => SameRun.bind_right _ fun t => ?_
  exact sameRun_uniform_two_equivs prims (e p t) (f p t) (k p t)

end ThresholdLeanXmssSecurity
end

/-! ## Digest fresh -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

lemma relabelHashCache_digestSwap_fresh (salt : List Bit) (h h' : HashOutput) (s : HashCache C)
    (hf : s (.digest salt h) = none) (hf' : s (.digest salt h') = none) :
    relabelHashCache (digestSwap salt h h') s = s := by
  funext q
  change Query C → Option HashOutput at s
  change Query C at q
  change s ((Equiv.swap (Query.digest salt h) (Query.digest salt h')) q) = s q
  by_cases hq : q = .digest salt h
  · subst q
    simp [Equiv.swap_apply_def,hf,hf']
  · by_cases hq' : q = .digest salt h'
    · subst q
      simp [Equiv.swap_apply_def,hf,hf']
    · simp [Equiv.swap_apply_def,hq,hq']

/-- From a cache with fresh outer names, changing the committed history exactly renames only those names. -/
theorem saltedDigest_fresh_couple (prims : Primitives) (salt history history' : List Bit)
    (h h' : HashOutput) (s : HashCache C)
    (hh : s (.history history) = some h) (hh' : s (.history history') = some h')
    (hf : s (.digest salt h) = none) (hf' : s (.digest salt h') = none)
    {α : Type} (k : HashOutput → OracleComp (LocalSpec C) α) :
    (saltedDigestAnswer prims salt history' >>= fun d =>
      simulateQ (localDigestAnswer prims salt h h') (k d)).run' s =
    (saltedDigestAnswer prims salt history >>= fun d =>
      simulateQ (localAnswer prims) (k d)).run' s := by
  have hc := saltedDigestAnswer_bind_couple prims salt history history' h h' s hh hh' k
  rw [relabelHashCache_digestSwap_fresh salt h h' s hf hf'] at hc
  simp only [StateT.run'_eq]
  rw [hc,Functor.map_map]

end ThresholdLeanXmssSecurity
end

/-! ## Trace guess -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

/-- A query budget bounds every projected trace, including traces chosen adaptively from answers. -/
theorem projected_log_length_le {ι β α : Type} {S : OracleSpec ι}
    [S.DecidableEq] [IsUniformSpec S] (charged : ι → Prop) [DecidablePred charged]
    (project : ι → Option β) (hproject : ∀ t,(project t).isSome → charged t)
    {oa : OracleComp S α} {q : ℕ} (hq : IsQueryBoundP oa charged q)
    {z : α × QueryLog S} (hz : z ∈ support ((simulateQ loggingOracle oa).run)) :
    (z.2.filterMap (fun entry => project entry.1)).length ≤ q := by
  induction oa using OracleComp.inductionOn generalizing q z with
  | pure x =>
      simp only [simulateQ_pure] at hz
      subst hz
      simp
  | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hpos,hrest⟩ := hq
      rw [run_simulateQ_loggingOracle_query_bind,support_bind] at hz
      simp only [Set.mem_iUnion,support_map] at hz
      obtain ⟨u,_,z',hz',rfl⟩ := hz
      have hb := ih u (hrest u) hz'
      cases hp : project t with
      | none =>
          simp only [List.filterMap_cons,hp] 
          by_cases hc : charged t <;> simp only [hc,if_true,if_false] at hb <;> omega
      | some b =>
          have hc := hproject t (by simp [hp])
          simp only [hc,if_true] at hb
          simp only [List.filterMap_cons,hp,List.length_cons]
          rcases hpos with hn | hn
          · exact False.elim (hn hc)
          · omega

/-- A uniform secret hits an arbitrary independent query trace with probability at most q/card. -/
theorem independent_trace_guess_bound {α β : Type} [Fintype α] [Nonempty α] [SampleableType α]
    (encode : α → β) (hinj : Function.Injective encode) (trace : ProbComp (List β)) (q : ℕ)
    (htrace : ∀ l ∈ support trace,l.length ≤ q) :
    Pr[fun p : List β × α => encode p.2 ∈ p.1 | (do
      let l ← trace
      let a ← $ᵗ α
      pure (l,a))] ≤ (q : ℝ≥0∞) / Fintype.card α := by
  classical
  letI : DecidableEq β := Classical.typeDecidableEq β
  refine probEvent_bind_le_of_forall_le fun l hl => ?_
  have he : (do let a ← $ᵗ α; pure (l,a)) = (fun a => (l,a)) <$> ($ᵗ α) :=
    (map_eq_bind_pure_comp (m := ProbComp) _ _).symm
  rw [he,probEvent_map]
  have h := probEvent_uniform_injective_mem encode hinj l.toFinset
  simp only [List.mem_toFinset] at h
  refine h.trans ?_
  gcongr
  exact (List.toFinset_card_le _).trans (htrace l hl)

/-- Fresh 256-bit salts are protected against every digest input in the independent trace;
there is no restriction at all on history inputs. -/
theorem independent_salt_trace_bound (trace : ProbComp (List (List Bit))) (q : ℕ)
    (htrace : ∀ l ∈ support trace,l.length ≤ q) :
    Pr[fun p : List (List Bit) × (Fin 256 → Bit) => List.ofFn p.2 ∈ p.1 | (do
      let l ← trace
      let salt ← $ᵗ (Fin 256 → Bit)
      pure (l,salt))] ≤ (q : ℝ≥0∞) / 2^256 := by
  have h := independent_trace_guess_bound (fun s : Fin 256 → Bit => List.ofFn s)
    List.ofFn_injective trace q htrace
  simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat] using h

end ThresholdLeanXmssSecurity
end

/-! ## Known history -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- A known output term is fixed by the adversary's reply, independently of the product or fresh table. -/
theorem multFinish_known_independent (D : C.Coalition) (width : ℕ)
    (filled : C.Term → ℕ → Option C.Party) (result result' : ℕ → E) (known : Shares C E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (a b : C.Term → Fin width → E) (i : C.Party) (T : C.Term) (hT : KnownTo D.1 T) :
    ((multFinish D width filled result known offset receivers a i).map (fun z => z T)) =
      ((multFinish D width filled result' known offset receivers b i).map (fun z => z T)) := by
  have hn : lackedTerm D.1 ≠ some T := fun h => lackedTerm_unknown D T h hT
  unfold multFinish
  by_cases hi : i ∈ D.1 ∨ i ∉ receivers
  · simp only [if_pos hi,Option.map_none]
  · simp only [if_neg hi,Option.map_some]
    congr 1
    funext g
    simp only [if_neg hn,if_pos hT]

/-- Every recorded known history is likewise independent of the hidden product and output coins. -/
theorem recordHistory_multFinish_known (K : Constants C E) (D : C.Coalition) (width : ℕ)
    (result result' : ℕ → E) (known : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (a b : C.Term → Fin width → E)
    (history : C.Term → List Bit) (i : C.Party) (T : C.Term) (hT : KnownTo D.1 T) :
    ((multFinish D width (filler K .peer) result known offset receivers a i).map
      (fun z => recordHistory K i history z width T)) =
    ((multFinish D width (filler K .peer) result' known offset receivers b i).map
      (fun z => recordHistory K i history z width T)) := by
  have h := multFinish_known_independent D width (filler K .peer) result result' known offset receivers a b i T hT
  have hp := congrArg (Option.map (fun z : ℕ → E => if i ∈ C.holders T then
    history T ++ ((List.range width).filter fun g => (filler K .peer T g).isSome).flatMap ((elementCodec K).toBits ∘ z)
    else history T)) h
  simpa only [Option.map_map,Function.comp_def,recordHistory] using hp

end ThresholdLeanXmssSecurity
end

/-! ## Final network -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def finalOpenVector (wa wb a b d q0 q2 r : E) : ℕ → E := fun k => match k with
  | 0 => wa+r*(wa+a)
  | 1 => wb+r*(wb+b)
  | _ => q0+(d+q0+q2)*r+q2*r^2

/-- The term-level translation preserves the exact three shares each honest party sends. -/
theorem finalOpenVector_shift (K : Constants C E) (T₀ : C.Term) (i : C.Party)
    (r d0 d2 : E) (deltaD : C.Term → E) (hr : 1+r ≠ 0)
    (hcompat : (1+r)*d0+r*(∑ T,deltaD T)+r*(1+r)*d2=0)
    (wa wb a b d q0 q2 a' b' d' q0' q2' : E)
    (hd : d-d'=conv K (localContext i) (fun T _ => deltaD T) 0)
    (hq0 : q0-q0'=conv K (localContext i) (finalOutputDelta T₀ r d0 d2 deltaD) 0)
    (hq2 : q2-q2'=conv K (localContext i) (finalOutputDelta T₀ r d0 d2 deltaD) 1) :
    finalOpenVector wa wb a b d q0 q2 r =
      finalOpenVector (wa+r/(1+r)*(a-a')) (wb+r/(1+r)*(b-b')) a' b' d' q0' q2' r := by
  funext k
  cases k with
  | zero => exact (final_mask_shift wa a a' r hr).symm
  | succ k =>
      cases k with
      | zero => exact (final_mask_shift wb b b' r hr).symm
      | succ k =>
          change q0+(d+q0+q2)*r+q2*r^2 = q0'+(d'+q0'+q2')*r+q2'*r^2
          have hc := finalOutputDelta_conv_cancel K T₀ r d0 d2 deltaD hr hcompat i
          rw [← hd,← hq0,← hq2] at hc
          linear_combination hc

def finalOpenProgram (K : Constants C E) (i : C.Party) (v : ℕ → E) :
    PartyM C E (CheckSpec C E) Unit := do
  let opened ← openSh K (localContext i) v 3
  require (opened 0*opened 1=opened 2)

/-- The last network phase agrees with any rushing adversary, including partial aborts. -/
theorem finalOpen_network_congr (K : Constants C E) (D : C.Coalition)
    {L R : Type} (A : Adversary C E Ia L R)
    (F : Functionality C ((ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ))
      ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) L R)
    (fuel : ℕ) (st : A.State) (live : C.Party → Prop) (v v' : C.Party → ℕ → E)
    (hv : ∀ i,i ∉ D.1 → live i → v i=v' i) :
    executePhase localRoles D A F fuel st
      (fun i => if live i then finalOpenProgram K i (v i) else failure) =
    executePhase localRoles D A F fuel st
      (fun i => if live i then finalOpenProgram K i (v' i) else failure) := by
  apply executePhase_congr_honest
  intro i hi
  by_cases hl : live i <;> simp only [hl,if_true,if_false]
  rw [hv i hi hl]

/-- The source-level final opening is the same program, with no remaining use of its history. -/
lemma finalOpen_run' (K : Constants C E) (i : C.Party) (v : ℕ → E) (hs : RunState C) :
    ((do
      let opened ← StateT.lift (openSh K (localContext i) v 3)
      StateT.lift (require (opened 0*opened 1=opened 2))) : RunM C E (CheckSpec C E) Unit).run' hs =
      finalOpenProgram K i v := by
  simp only [StateT.run'_eq,StateT.run_bind,StateT.run_lift,map_bind,map_pure,bind_assoc,pure_bind,bind_pure,finalOpenProgram]

end ThresholdLeanXmssSecurity
end

/-! ## Final soundness -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The honest shares alone fix an accepted opening, whatever the corrupt parties sent. -/
theorem openValue_robust (K : Constants C E) (D : C.Coalition) (v : C.Party → ℕ → E)
    (vals : ℕ → E)
    (hv : ∀ g < 3,∃ P : Polynomial E,P.natDegree ≤ C.t-1 ∧ P.eval 0=vals g ∧
      ∀ j,j ∉ D.1 → v j g=P.eval (K.point j))
    (i : C.Party) (hi : i ∉ D.1) (inbox : Mail C E)
    (hin : ∀ j,j ∉ D.1 → j ≠ i → inbox j=openOutbox j (v j) i)
    (hag : OpenAgrees K i (v i) inbox) :
    ∀ g < 3,openValue K i (v i) inbox g=vals g := by
  intro g hg
  obtain ⟨P,hP,hP0,hPj⟩ := hv g hg
  rw [← hP0]
  apply gs20_openSh_robust K D P hP
  · intro j hj
    rw [← hPj j hj]
    unfold openShare
    by_cases he : j=i
    · subst j
      simp
    · rw [if_neg he,hin j hj he]
      simp [openOutbox,Ne.symm he,Msg.elementAt,vector,hg]
  · exact fun j => hag j g hg

/-- If an honest party accepts the final opening, the GS20 final error polynomial vanishes. -/
theorem final_accept_implies_root (K : Constants C E) (D : C.Coalition)
    (v : C.Party → ℕ → E) (a b wa wb d e0 e2 r : E)
    (hv : ∀ g < 3,∃ P : Polynomial E,P.natDegree ≤ C.t-1 ∧
      P.eval 0=finalOpenVector wa wb a b d (wa*wb+e0) ((wa+a)*(wb+b)+e2) r g ∧
      ∀ j,j ∉ D.1 → v j g=P.eval (K.point j))
    (i : C.Party) (hi : i ∉ D.1) (inbox : Mail C E)
    (hin : ∀ j,j ∉ D.1 → j ≠ i → inbox j=openOutbox j (v j) i)
    (hag : OpenAgrees K i (v i) inbox)
    (haccept : openValue K i (v i) inbox 0*openValue K i (v i) inbox 1=
      openValue K i (v i) inbox 2) :
    r*(d-a*b)+(1+r)*e0+r*(1+r)*e2=0 := by
  have ho := openValue_robust K D v _ hv i hi inbox hin hag
  rw [ho 0 (by omega),ho 1 (by omega),ho 2 (by omega)] at haccept
  change (wa+r*(wa+a))*(wb+r*(wb+b)) =
    (wa*wb+e0)+(d+(wa*wb+e0)+((wa+a)*(wb+b)+e2))*r+((wa+a)*(wb+b)+e2)*r^2 at haccept
  rw [← final_residual_identity a b wa wb d e0 e2 r,← haccept,sub_self]

lemma final_residual_card_le_two (a b d e0 e2 : E) (hwrong : d ≠ a*b) :
    (univ.filter fun r : E => r*(d-a*b)+(1+r)*e0+r*(1+r)*e2=0).card ≤ 2 := by
  apply card_filter_le_two_of_quadratic e0 (d-a*b+e0+e2) e2
  · by_contra! h
    obtain ⟨h0,h1,h2⟩ := h
    apply hwrong
    linear_combination h1-h0-h2
  · intro r hr
    linear_combination hr

/-- The actual cached challenge bounds acceptance of any later adaptive continuation,
provided acceptance implies the final error root. -/
theorem finalChallenge_adaptive_soundness {β : Type} (prims : Primitives) (K : Constants C E)
    (tag label : ℕ) (coin : List E) (Ks : Finset HashOutput) (cache : HashCache C)
    (hfresh : cache (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v)))=none)
    (hexpand : ∀ key idx,cache (.expand key idx) ≠ none → key ∈ Ks)
    (a b d e0 e2 : E) (hwrong : d ≠ a*b)
    (cont : Option E × HashCache C → ProbComp β) (accept : β → Prop)
    (hroot : ∀ p x,x ∈ support (cont p) → accept x →
      ∃ r,p.1=some r ∧ r*(d-a*b)+(1+r)*e0+r*(1+r)*e2=0) :
    Pr[accept | (simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache >>= cont] ≤
        Ks.card / 2^256 + 2/(Fintype.card E-2 : ℕ) := by
  let roots := univ.filter fun r : E => r*(d-a*b)+(1+r)*e0+r*(1+r)*e2=0
  have hp : Pr[accept | (simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache >>= cont] ≤
    Pr[fun p => ∃ r ∈ roots,p.1=some r | (simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag label coin) (LocalSpec C))).run cache] := by
    apply probEvent_bind_le_probEvent
    intro p hp hn
    apply probEvent_eq_zero
    intro x hx ha
    obtain ⟨r,hr,he⟩ := hroot p x hx ha
    exact hn ⟨r,by simp [roots,he],hr⟩
  refine hp.trans ((challengeQuery_mem_le_of_fresh prims K tag label coin Ks cache hfresh hexpand roots).trans ?_)
  gcongr
  exact_mod_cast final_residual_card_le_two a b d e0 e2 hwrong

end ThresholdLeanXmssSecurity
end

/-! ## Terminal -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O L R Ia α : Type}

def terminalProgram (out : Option α) : PartyM C E (CallSpec I O) α :=
  match out with | none => failure | some a => pure a

lemma executePhase_terminal (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (out : C.Party → Option α) :
    executePhase localRoles D A F fuel st (fun i => terminalProgram (out i)) =
      pure (st,fun i => if i ∈ D.1 then none else out i) := by
  have hs : startSteps localRoles D (fun i => (terminalProgram (out i) : PartyM C E (CallSpec I O) α)) =
      pure (fun i => Step.done (if i ∈ D.1 then none else out i)) := by
    unfold startSteps
    calc
      _ = Concrete.sequenceFin (fun i => pure (Step.done (if i ∈ D.1 then none else out i))) := by
        congr 1
        funext i
        by_cases hi : i ∈ D.1
        · simp [hi]
        · cases ho : out i <;>
            simp only [hi,if_false,ho,terminalProgram,localRoles,advance_run_failure,advance_run_pure]
      _ = _ := sequenceFin_pure _
  unfold executePhase
  rw [hs,pure_bind]
  cases fuel <;> simp [executeRounds,Step.isDone,Step.output]

lemma require_require_terminal (p q : Prop) :
    (require p >>= fun _ => require q : PartyM C E (CallSpec I O) Unit) =
      terminalProgram (if p ∧ q then some () else none) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [require,hp,hq,terminalProgram]

end ThresholdLeanXmssSecurity
end

/-! ## Final round -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma finalOpenProgram_exchange (K : Constants C E) (i : C.Party) (v : ℕ → E) :
    finalOpenProgram K i v = (do
      let inbox ← exchange (openOutbox i v)
      require (OpenAgrees K i v inbox)
      require (openValue K i v inbox 0*openValue K i v inbox 1=openValue K i v inbox 2)) := by
  simp only [finalOpenProgram,openSh,bind_assoc]
  rfl

def finalInbox (D : C.Coalition) (live : C.Party → Prop) (v : C.Party → ℕ → E)
    (sent : C.Party → Mail C E) (i : C.Party) : Mail C E := fun k =>
  if k ∈ D.1 then sent k i else if live k then openOutbox k (v k) i else some .abort

def finalRoundAccept (K : Constants C E) (D : C.Coalition) (live : C.Party → Prop)
    (v : C.Party → ℕ → E) (sent : C.Party → Mail C E) (i : C.Party) : Prop :=
  let inbox := finalInbox D live v sent i
  C.parties.any (fun j => Msg.isAbort (inbox j)) = false ∧
    OpenAgrees K i (v i) inbox ∧
      openValue K i (v i) inbox 0*openValue K i (v i) inbox 1=openValue K i (v i) inbox 2

def finalRoundOutputs (K : Constants C E) (D : C.Coalition) (live : C.Party → Prop)
    (v : C.Party → ℕ → E) (sent : C.Party → Mail C E) : C.Party → Option Unit := fun i =>
  if i ∉ D.1 ∧ live i ∧ finalRoundAccept K D live v sent i then some () else none

/-- Exact distribution of the final network round, including the rushing reply and all abort cases. -/
theorem finalOpen_round (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (live : C.Party → Prop) (v : C.Party → ℕ → E)
    (hlive : ∃ i,i ∉ D.1 ∧ live i) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => if live i then finalOpenProgram K i (v i) else failure) = (do
      let p ← A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ live i then openOutbox i (v i) c else none)
      pure (p.1,finalRoundOutputs K D live v p.2)) := by
  let out := fun i => if live i then some (openOutbox i (v i)) else none
  let f := fun i inbox => (require (OpenAgrees K i (v i) inbox) >>= fun _ =>
    require (openValue K i (v i) inbox 0*openValue K i (v i) inbox 1=openValue K i (v i) inbox 2) :
      PartyM C E (CheckSpec C E) Unit)
  have hp : (fun i => if live i then finalOpenProgram K i (v i) else failure) =
      (fun i => optionalExchange (out i) (f i)) := by
    funext i
    by_cases hi : live i <;> simp only [out,f,hi,if_true,if_false,optionalExchange,finalOpenProgram_exchange]
  rw [hp,executePhase_optionalExchange D A _ fuel st out f (by
    obtain ⟨i,hi,hl⟩ := hlive
    exact ⟨i,hi,by simp [out,hl]⟩)]
  have hs : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (out i).getD (fun _ => none) c else none) =
      (fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ live i then openOutbox i (v i) c else none) := by
    funext c i
    by_cases hc : c ∈ D.1 <;> by_cases hi : i ∈ D.1 <;> by_cases hl : live i <;> simp [out,hc,hi,hl]
  rw [hs]
  apply bind_congr
  intro p
  have hp' : (fun i => afterExchange D out p.2 i (f i)) =
      (fun i => terminalProgram (if live i ∧ finalRoundAccept K D live v p.2 i then some () else none)) := by
    funext i
    have hin : (fun k => if k ∈ D.1 then p.2 k i else (out k).getD (fun _ => some .abort) i) =
        finalInbox D live v p.2 i := by
      funext k
      by_cases hk : k ∈ D.1 <;> by_cases hl : live k <;> simp [out,hk,hl,finalInbox]
    by_cases hi : live i
    · have hoi : out i = some (openOutbox i (v i)) := by simp [out,hi]
      unfold afterExchange
      rw [hoi]
      change (if C.parties.any (fun j => Msg.isAbort
        ((fun k => if k ∈ D.1 then p.2 k i else (out k).getD (fun _ => some .abort) i) j))
        then failure else f i (fun k => if k ∈ D.1 then p.2 k i else (out k).getD (fun _ => some .abort) i)) = _
      rw [hin]
      by_cases hb : C.parties.any (fun j => Msg.isAbort (finalInbox D live v p.2 i j)) = true
      · simp [hb,finalRoundAccept,hi,terminalProgram]
      · have hb' : C.parties.any (fun j => Msg.isAbort (finalInbox D live v p.2 i j)) = false := by
          cases he : C.parties.any (fun j => Msg.isAbort (finalInbox D live v p.2 i j)) <;> simp_all
        simp only [hb',Bool.false_eq_true,if_false,f,require_require_terminal,finalRoundAccept,
          hi,true_and,hb']
        split_ifs <;> rfl
    · simp [afterExchange,out,hi,terminalProgram]
  rw [hp',executePhase_terminal]
  congr 2
  funext i
  by_cases hi : i ∈ D.1 <;> simp [hi,finalRoundOutputs]

/-- A missing honest opener forces every live honest party to reject. -/
theorem finalRoundAccept_all_live (K : Constants C E) (D : C.Coalition) (live : C.Party → Prop)
    (v : C.Party → ℕ → E) (sent : C.Party → Mail C E) (i : C.Party)
    (h : finalRoundAccept K D live v sent i) : ∀ j,j ∉ D.1 → live j := by
  intro j hj
  by_contra hl
  have habort : C.parties.any (fun k => Msg.isAbort (finalInbox D live v sent i k)) = true :=
    List.any_eq_true.mpr ⟨j,List.mem_finRange j,by simp [finalInbox,hj,hl,Msg.isAbort]⟩
  exact Bool.false_ne_true (h.1.symm.trans habort)

/-- Acceptance in the actual final round implies the final polynomial root. -/
theorem finalRoundOutputs_implies_root (K : Constants C E) (D : C.Coalition)
    (live : C.Party → Prop) (v : C.Party → ℕ → E) (sent : C.Party → Mail C E)
    (a b wa wb d e0 e2 r : E)
    (hv : ∀ g < 3,∃ P : Polynomial E,P.natDegree ≤ C.t-1 ∧
      P.eval 0=finalOpenVector wa wb a b d (wa*wb+e0) ((wa+a)*(wb+b)+e2) r g ∧
      ∀ j,j ∉ D.1 → v j g=P.eval (K.point j))
    (i : C.Party) (hi : finalRoundOutputs K D live v sent i=some ()) :
    r*(d-a*b)+(1+r)*e0+r*(1+r)*e2=0 := by
  have ha : i ∉ D.1 ∧ live i ∧ finalRoundAccept K D live v sent i := by
    by_contra hn
    simp [finalRoundOutputs,hn] at hi
  have hl := finalRoundAccept_all_live K D live v sent i ha.2.2
  exact final_accept_implies_root K D v a b wa wb d e0 e2 r hv i ha.1
    (finalInbox D live v sent i)
    (fun j hj _ => by simp [finalInbox,hj,hl j hj]) ha.2.2.2.1 ha.2.2.2.2

end ThresholdLeanXmssSecurity
end

/-! ## Challenge order -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α β γ : Type}

def SameLocalOutput (prims : Primitives) (a b : OracleComp (LocalSpec C) α) : Prop :=
  ∀ s : HashCache C,𝒟[(simulateQ (localAnswer prims) a).run' s] =
    𝒟[(simulateQ (localAnswer prims) b).run' s]

lemma SameLocalOutput.of_sameRun (prims : Primitives) {a b : OracleComp (LocalSpec C) α}
    (h : SameRun prims a b) : SameLocalOutput prims a b := by
  intro s
  simp only [StateT.run'_eq,evalDist_map,h s]

lemma SameLocalOutput.bind_right (prims : Primitives) (oa : OracleComp (LocalSpec C) α)
    {f g : α → OracleComp (LocalSpec C) β} (h : ∀ a,SameLocalOutput prims (f a) (g a)) :
    SameLocalOutput prims (oa >>= f) (oa >>= g) := by
  intro s
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind,evalDist_bind]
  apply congrArg
  funext p
  exact h p.1 p.2

/-- A challenge query can be made before a selective-abort decision. The result is ignored
on aborted branches, and its cache effects remain indistinguishable in the full continuation. -/
theorem challenge_before_selective_reply (prims : Primitives)
    (reply : OracleComp (LocalSpec C) α) (challenge : OracleComp (LocalSpec C) β)
    (go : α → Prop) (next : α → β → OracleComp (LocalSpec C) γ)
    (abort : α → OracleComp (LocalSpec C) γ) :
    SameLocalOutput prims
      (do let p ← reply; if go p then challenge >>= next p else abort p)
      (do let r ← challenge; let p ← reply; if go p then next p r else abort p) := by
  have h : SameLocalOutput prims
      (do let p ← reply; if go p then challenge >>= next p else abort p)
      (do let p ← reply; let r ← challenge; if go p then next p r else abort p) := by
    apply SameLocalOutput.bind_right
    intro p s
    by_cases hg : go p
    · simp only [if_pos hg]
    · simp only [if_neg hg]
      exact (local_prefetch_output prims challenge (abort p) s).symm
  intro s
  refine (h s).trans ?_
  exact SameLocalOutput.of_sameRun prims
    (sameRun_swap prims reply challenge (fun p r => if go p then next p r else abort p)) s

end ThresholdLeanXmssSecurity
end

/-! ## Until digest -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {ι σ α : Type} {S : OracleSpec ι}

def flagQueries (impl : QueryImpl S (StateT σ ProbComp)) (bad : ι → Bool) :
    QueryImpl S (StateT (σ × Bool) ProbComp) := fun t p =>
  (fun z => (z.1,(z.2,p.2 || bad t))) <$> (impl t).run p.1

@[simp] lemma flagQueries_run (impl : QueryImpl S (StateT σ ProbComp)) (bad : ι → Bool)
    (t : ι) (p : σ × Bool) : (flagQueries impl bad t).run p =
      (fun z => (z.1,(z.2,p.2 || bad t))) <$> (impl t).run p.1 := rfl

lemma flagQueries_forget (impl : QueryImpl S (StateT σ ProbComp)) (bad : ι → Bool)
    (oa : OracleComp S α) (s : σ) (b : Bool) :
    (fun z : α × σ × Bool => (z.1,z.2.1)) <$> (simulateQ (flagQueries impl bad) oa).run (s,b) =
      (simulateQ impl oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s b with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,flagQueries_run,
      bind_map_left,map_bind]
    apply bind_congr
    intro p
    exact ih p.1 p.2 (b || bad t)

lemma flagQueries_mono (impl : QueryImpl S (StateT σ ProbComp)) (bad : ι → Bool)
    (t : ι) (p : σ × Bool) (hp : p.2=true) :
    ∀ z ∈ support ((flagQueries impl bad t).run p),z.2.2=true := by
  intro z hz
  simp only [flagQueries_run,support_map,Set.mem_image] at hz
  obtain ⟨x,_,rfl⟩ := hz
  simp [hp]

/-- A change confined to selected query inputs is invisible until one of those inputs occurs. -/
theorem localHandler_until_query
    (impl₁ impl₂ : QueryImpl S (StateT σ ProbComp)) (bad : ι → Bool)
    (heq : ∀ t s,bad t=false → (impl₁ t).run s=(impl₂ t).run s)
    (oa : OracleComp S α) (s : σ) :
    tvDist ((simulateQ impl₁ oa).run s) ((simulateQ impl₂ oa).run s) ≤
      Pr[fun z : α × σ × Bool => z.2.2=true |
        (simulateQ (flagQueries impl₁ bad) oa).run (s,false)].toReal := by
  have hag : ∀ t s u s',
      Pr[= (u,(s',false)) | (flagQueries impl₁ bad t).run (s,false)] =
      Pr[= (u,(s',false)) | (flagQueries impl₂ bad t).run (s,false)] := by
    intro t s u s'
    cases hb : bad t with
    | false => simp only [flagQueries_run,heq t s hb]
    | true =>
      have hz : ∀ (impl : QueryImpl S (StateT σ ProbComp)),
          Pr[= (u,(s',false)) | (flagQueries impl bad t).run (s,false)] = 0 := by
        intro impl
        apply probOutput_eq_zero_of_not_mem_support
        simp [flagQueries_run,hb]
      rw [hz impl₁,hz impl₂]
  have hzero (impl : QueryImpl S (StateT σ ProbComp)) (oa : OracleComp S α)
      (s s' : σ) (a : α) :
      Pr[= (a,(s',false)) | (simulateQ (flagQueries impl bad) oa).run (s,true)] = 0 :=
    probOutput_simulateQ_run_eq_zero_of_bad (flagQueries impl bad) (fun p => p.2=true)
      (flagQueries_mono impl bad) oa (s,true) rfl a (s',false) Bool.false_ne_true
  have hgood : ∀ (oa : OracleComp S α) s a s',
      Pr[= (a,(s',false)) | (simulateQ (flagQueries impl₁ bad) oa).run (s,false)] =
      Pr[= (a,(s',false)) | (simulateQ (flagQueries impl₂ bad) oa).run (s,false)] := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a => intros; rfl
    | query_bind t k ih =>
      intro s a s'
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
      rw [probOutput_bind_eq_tsum,probOutput_bind_eq_tsum]
      apply tsum_congr
      rintro ⟨u,s'',b⟩
      cases b with
      | false => rw [hag t s u s'',ih u s'' a s']
      | true => rw [hzero impl₁,hzero impl₂,mul_zero,mul_zero]
  let sim₁ := (simulateQ (flagQueries impl₁ bad) oa).run (s,false)
  let sim₂ := (simulateQ (flagQueries impl₂ bad) oa).run (s,false)
  have hnot : Pr[fun z : α × σ × Bool => ¬z.2.2=true | sim₁] =
      Pr[fun z : α × σ × Bool => ¬z.2.2=true | sim₂] := by
    rw [probEvent_eq_tsum_ite,probEvent_eq_tsum_ite]
    apply tsum_congr
    rintro ⟨a,s',b⟩
    cases b <;> simp only [Bool.false_eq_true,not_false_eq_true,ite_true,not_true_eq_false,ite_false]
    exact hgood oa s a s'
  have hbad : Pr[fun z : α × σ × Bool => z.2.2=true | sim₁] =
      Pr[fun z : α × σ × Bool => z.2.2=true | sim₂] := by
    have h₁ := probEvent_compl sim₁ (fun z : α × σ × Bool => z.2.2=true)
    have h₂ := probEvent_compl sim₂ (fun z : α × σ × Bool => z.2.2=true)
    simp only [probFailure_eq_zero,tsub_zero] at h₁ h₂
    rw [hnot] at h₁
    exact (ENNReal.add_left_inj probEvent_ne_top).mp (h₁.trans h₂.symm)
  have h : tvDist sim₁ sim₂ ≤ Pr[fun z : α × σ × Bool => z.2.2=true | sim₁].toReal := by
    apply tvDist_le_probEvent_of_probOutput_eq_of_not _ _ hbad
    rintro ⟨a,s',b⟩ hb
    cases b with
    | false => exact hgood oa s a s'
    | true => exact False.elim (hb rfl)
  have hp := tvDist_map_le (fun z : α × σ × Bool => (z.1,z.2.1))
    ((simulateQ (flagQueries impl₁ bad) oa).run (s,false))
    ((simulateQ (flagQueries impl₂ bad) oa).run (s,false))
  rw [flagQueries_forget,flagQueries_forget] at hp
  exact hp.trans h

variable {C : Committee}

/-- Only outer digests at this salt are protected; histories are unrestricted. -/
def digestSaltHit (salt : List Bit) : (LocalSpec C).Domain → Bool
  | .inr (.inl (.digest s _)) => decide (s=salt)
  | _ => false

lemma localDigestAnswer_eq_of_no_salt (prims : Primitives) (salt : List Bit)
    (h h' : HashOutput) (t : (LocalSpec C).Domain) (s : HashCache C)
    (ht : digestSaltHit salt t=false) :
    (localAnswer prims t).run s=(localDigestAnswer prims salt h h' t).run s := by
  rcases t with n | q | x
  · rfl
  · have hq : digestSwap salt h h' q=q := by
      cases q <;> simp_all [digestSaltHit,digestSwap,Equiv.swap_apply_def]
    change (hashAnswerFlat prims q).run s=(hashAnswerFlat prims (digestSwap salt h h' q)).run s
    rw [hq]
  · rfl

/-- Digest renaming is coupled against the actual local oracle until a query at the hidden salt. -/
theorem digestSwap_until_salt (prims : Primitives) (salt : List Bit) (h h' : HashOutput)
    (oa : OracleComp (LocalSpec C) α) (s : HashCache C) :
    tvDist ((simulateQ (localAnswer prims) oa).run s)
      ((simulateQ (localDigestAnswer prims salt h h') oa).run s) ≤
        Pr[fun z : α × HashCache C × Bool => z.2.2=true |
          (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) oa).run (s,false)].toReal := by
  exact localHandler_until_query (localAnswer prims) (localDigestAnswer prims salt h h')
    (digestSaltHit salt) (fun t s ht => localDigestAnswer_eq_of_no_salt prims salt h h' t s ht) oa s

end ThresholdLeanXmssSecurity
end

/-! ## Salt trace -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {ι σ α β : Type} {S : OracleSpec ι}

def projectQueries (impl : QueryImpl S (StateT σ ProbComp)) (project : ι → Option β) :
    QueryImpl S (StateT (σ × List β) ProbComp) := fun t p =>
  (fun z => (z.1,(z.2,(project t).toList ++ p.2))) <$> (impl t).run p.1

@[simp] lemma projectQueries_run (impl : QueryImpl S (StateT σ ProbComp)) (project : ι → Option β)
    (t : ι) (p : σ × List β) : (projectQueries impl project t).run p =
      (fun z => (z.1,(z.2,(project t).toList ++ p.2))) <$> (impl t).run p.1 := rfl

/-- Projected query bounds hold for arbitrary stateful handlers, including the actual cached oracle. -/
theorem projectQueries_length (impl : QueryImpl S (StateT σ ProbComp))
    (charged : ι → Prop) [DecidablePred charged] (project : ι → Option β)
    (hproject : ∀ t,(project t).isSome → charged t)
    {oa : OracleComp S α} {q : ℕ} (hq : IsQueryBoundP oa charged q)
    (s : σ) (l : List β) {z : α × σ × List β}
    (hz : z ∈ support ((simulateQ (projectQueries impl project) oa).run (s,l))) :
    z.2.2.length ≤ l.length+q := by
  induction oa using OracleComp.inductionOn generalizing q s l z with
  | pure a =>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at hz
    subst z
    change l.length ≤ l.length+q
    omega
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    obtain ⟨hpos,hrest⟩ := hq
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,projectQueries_run,
      bind_map_left,support_bind,Set.mem_iUnion,exists_prop] at hz
    obtain ⟨p,_,hz⟩ := hz
    have hb := ih p.1 (hrest p.1) p.2 ((project t).toList ++ l) hz
    cases hp : project t with
    | none =>
      simp only [hp,Option.toList_none,List.nil_append] at hb
      by_cases hc : charged t <;> simp only [hc,if_true,if_false] at hb <;> omega
    | some b =>
      have hc := hproject t (by simp [hp])
      simp only [hp,Option.toList_some,List.singleton_append,List.length_cons,hc,if_true] at hb
      rcases hpos with hn | hn
      · exact False.elim (hn hc)
      · omega

lemma projectQueries_flag (impl : QueryImpl S (StateT σ ProbComp)) (project : ι → Option β)
    (a : β) (oa : OracleComp S α) (s : σ) (l : List β) :
    (fun z : α × σ × List β => (z.1,(z.2.1,decide (a ∈ z.2.2)))) <$>
      (simulateQ (projectQueries impl project) oa).run (s,l) =
    (simulateQ (flagQueries impl (fun t => decide (project t=some a))) oa).run (s,decide (a ∈ l)) := by
  letI : DecidableEq β := Classical.typeDecidableEq β
  induction oa using OracleComp.inductionOn generalizing s l with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,projectQueries_run,
      flagQueries_run,bind_map_left,map_bind]
    apply bind_congr
    intro p
    rw [ih]
    congr 1
    cases hp : project t <;> simp [List.mem_cons,eq_comm,Bool.or_comm]
    congr 1

variable {C : Committee}

def digestSaltProjection : (LocalSpec C).Domain → Option (List Bit)
  | .inr (.inl (.digest salt _)) => some salt
  | _ => none

lemma digestSaltProjection_counted (t : (LocalSpec C).Domain)
    (ht : (digestSaltProjection t).isSome) : Counted t := by
  rcases t with n | q | x
  · simp [digestSaltProjection] at ht
  · cases q <;> simp_all [digestSaltProjection,Counted]
  · simp [digestSaltProjection] at ht

lemma digestSaltHit_projection (salt : List Bit) : digestSaltHit (C := C) salt =
    (fun t => decide (digestSaltProjection t=some salt)) := by
  funext t
  rcases t with n | q | x
  · rfl
  · cases q <;> simp [digestSaltHit,digestSaltProjection]
  · rfl

/-- The adaptive query trace is independent of a freshly chosen hidden salt. -/
theorem digestSaltFlag_bound (prims : Primitives) (oa : OracleComp (LocalSpec C) α)
    (s : HashCache C) (q : ℕ) (hq : IsQueryBoundP oa Counted q) :
    Pr[fun z : α × HashCache C × Bool => z.2.2=true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false))] ≤
      (q : ℝ≥0∞)/2^256 := by
  let raw := (simulateQ (projectQueries (localAnswer prims) digestSaltProjection) oa).run (s,[])
  let trace := (fun z : α × HashCache C × List (List Bit) => z.2.2) <$> raw
  have ht : ∀ l ∈ support trace,l.length ≤ q := by
    intro l hl
    simp only [trace,support_map,Set.mem_image] at hl
    obtain ⟨z,hz,rfl⟩ := hl
    simpa using projectQueries_length (localAnswer prims) Counted digestSaltProjection
      digestSaltProjection_counted hq s [] hz
  have hb := independent_salt_trace_bound trace q ht
  have hp : ∀ salt : Fin 256 → Bit,
      Pr[fun z : α × HashCache C × Bool => z.2.2=true |
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false)] =
      Pr[fun l => List.ofFn salt ∈ l | trace] := by
    intro salt
    rw [digestSaltHit_projection]
    have he := projectQueries_flag (localAnswer prims) digestSaltProjection (List.ofFn salt) oa s []
    simp only [List.not_mem_nil,decide_false] at he
    have he' : (simulateQ (flagQueries (localAnswer prims)
        (fun t => decide (digestSaltProjection t=some (List.ofFn salt)))) oa).run (s,false) =
        (fun z : α × HashCache C × List (List Bit) => (z.1,(z.2.1,decide (List.ofFn salt ∈ z.2.2)))) <$> raw := by
      convert he.symm using 1 <;> congr
      · funext t
        by_cases h : digestSaltProjection t=some (List.ofFn salt) <;> simp only [h,decide_true,decide_false]
      · funext z
        by_cases h : List.ofFn salt ∈ z.2.2 <;> simp only [h,decide_true,decide_false]
    rw [he',probEvent_map]
    simp only [trace,probEvent_map,Function.comp_def,decide_eq_true_eq]
  have he : Pr[fun z : α × HashCache C × Bool => z.2.2=true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false))] =
      Pr[fun p : List (List Bit) × (Fin 256 → Bit) => List.ofFn p.2 ∈ p.1 | (do
        let l ← trace; let salt ← $ᵗ (Fin 256 → Bit); pure (l,salt))] := by
    simp only [probEvent_bind_eq_tsum,hp,probEvent_pure]
    simp only [probEvent_eq_tsum_ite]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro l
    apply tsum_congr
    intro salt
    split_ifs <;> simp [mul_comm]

  rw [he]
  exact hb

end ThresholdLeanXmssSecurity
end

/-! ## Digest programmed -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

lemma hashAnswer_cacheQuery_other (prims : Primitives) (s : HashCache C)
    (target q : Query C) (d : HashOutput) (hne : q ≠ target) :
    (hashAnswer prims q).run (s.cacheQuery target d) =
      (fun p => (p.1,p.2.cacheQuery target d)) <$> (hashAnswer prims q).run s := by
  by_cases hq : IsFixed q
  · obtain ⟨input,rfl,hi⟩ := hq
    rw [hashAnswer_of_isFixed prims hi]
    simp
  · rw [hashAnswer_of_not_isFixed prims hq]
    have ht : (s.cacheQuery target d) q=s q := QueryCache.cacheQuery_of_ne _ _ hne
    cases hs : s q with
    | none =>
      rw [OracleSpec.randomOracle,QueryImpl.withCaching_run_none _ hs,
        QueryImpl.withCaching_run_none _ (ht.trans hs)]
      simp only [Functor.map_map]
      congr 1
      funext u
      congr 1
      exact Function.update_comm (Ne.symm hne) _ _ _
    | some u =>
      rw [OracleSpec.randomOracle,QueryImpl.withCaching_run_some _ hs,
        QueryImpl.withCaching_run_some _ (ht.trans hs)]
      simp

def patchedDigestHash (prims : Primitives) (salt : List Bit) (h d : HashOutput) :
    QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp) := fun q =>
  if q = .digest salt h then pure d else hashAnswer prims q

def patchedDigestLocal (prims : Primitives) (salt : List Bit) (h d : HashOutput) :
    QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp) :=
  unifFwdImpl (Query C →ₒ HashOutput) + (patchedDigestHash (C := C) prims salt h d + prgAnswer (C := C) prims)

lemma hashAnswer_digest_programmed (prims : Primitives) (s : HashCache C)
    (salt : List Bit) (h d : HashOutput) (q : Query C) :
    (hashAnswer prims q).run (s.cacheQuery (.digest salt h) d) =
      (fun p => (p.1,p.2.cacheQuery (.digest salt h) d)) <$>
        (patchedDigestHash prims salt h d q).run s := by
  by_cases hq : q=.digest salt h
  · subst q
    have hf : ¬ IsFixed (Query.digest (C := C) salt h) := by rintro ⟨_,he,_⟩; cases he
    rw [hashAnswer_run_cached prims hf (QueryCache.cacheQuery_self _ _ _)]
    simp [patchedDigestHash]
  · simp only [patchedDigestHash,if_neg hq]
    exact hashAnswer_cacheQuery_other prims s _ q d hq

lemma localAnswer_digest_programmed (prims : Primitives) (s : HashCache C)
    (salt : List Bit) (h d : HashOutput) (t : (LocalSpec C).Domain) :
    (localAnswer prims t).run (s.cacheQuery (.digest salt h) d) =
      (fun p => (p.1,p.2.cacheQuery (.digest salt h) d)) <$>
        (patchedDigestLocal prims salt h d t).run s := by
  rcases t with n | q | x
  · simp [localAnswer,patchedDigestLocal,unifFwdImpl,Functor.map_map]
  · exact hashAnswer_digest_programmed prims s salt h d q
  · have hh := hashAnswer_cacheQuery_other prims s (.digest salt h) (.streamKey x.2.1) d (by simp)
    change (prgAnswer prims x).run _ = (fun p => (p.1,p.2.cacheQuery (.digest salt h) d)) <$> (prgAnswer prims x).run s
    unfold prgAnswer
    simp only [StateT.run_bind,StateT.run_pure,map_bind,map_pure]
    rw [hh,bind_map_left]

/-- A planted digest is exactly an overridden local oracle, including arbitrary later adaptive calls. -/
theorem localProgram_digest_programmed (prims : Primitives) (s : HashCache C)
    (salt : List Bit) (h d : HashOutput) (oa : OracleComp (LocalSpec C) α) :
    (simulateQ (localAnswer prims) oa).run (s.cacheQuery (.digest salt h) d) =
      (fun p => (p.1,p.2.cacheQuery (.digest salt h) d)) <$>
        (simulateQ (patchedDigestLocal prims salt h d) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [localAnswer_digest_programmed,bind_map_left,map_bind]
    apply bind_congr
    intro p
    exact ih p.1 p.2

/-- Programming one hidden digest changes observable behavior only if its salt is queried. -/
theorem digest_programming_until_salt (prims : Primitives) (s : HashCache C)
    (salt : List Bit) (h d : HashOutput) (oa : OracleComp (LocalSpec C) α) :
    tvDist ((simulateQ (localAnswer prims) oa).run' s)
      ((simulateQ (localAnswer prims) oa).run' (s.cacheQuery (.digest salt h) d)) ≤
      Pr[fun z : α × HashCache C × Bool => z.2.2=true |
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) oa).run (s,false)].toReal := by
  have he : ∀ (t : (LocalSpec C).Domain) (s : HashCache C),digestSaltHit salt t=false →
      (localAnswer prims t).run s=(patchedDigestLocal prims salt h d t).run s := by
    intro t s ht
    rcases t with n | q | x
    · rfl
    · have hq : q ≠ .digest salt h := by intro hq; subst q; simp [digestSaltHit] at ht
      change (hashAnswer prims q).run s=(patchedDigestHash prims salt h d q).run s
      simp [patchedDigestHash,hq]
    · rfl
  have hb := localHandler_until_query (localAnswer prims) (patchedDigestLocal prims salt h d)
    (digestSaltHit salt) he oa s
  simp only [StateT.run'_eq,localProgram_digest_programmed,Functor.map_map]
  exact (tvDist_map_le Prod.fst _ _).trans hb

end ThresholdLeanXmssSecurity
end

/-! ## Digest bound -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

/-- Programming a digest at an independent hidden salt costs at most q/2^256,
even if its inner hash and programmed value depend on that salt. -/
theorem hidden_digest_programming_bound (prims : Primitives) (cache : HashCache C)
    (h d : (Fin 256 → Bit) → HashOutput) (oa : OracleComp (LocalSpec C) α)
    (q : ℕ) (hq : IsQueryBoundP oa Counted q) :
    tvDist (do
        let _salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (localAnswer prims) oa).run' cache)
      (do
        let salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (localAnswer prims) oa).run'
          (cache.cacheQuery (.digest (List.ofFn salt) (h salt)) (d salt))) ≤
      (q : ℝ)/2^256 := by
  let prob := fun salt : Fin 256 → Bit =>
    Pr[fun z : α × HashCache C × Bool => z.2.2=true |
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (cache,false)]
  have hb := tvDist_bind_left_le ($ᵗ (Fin 256 → Bit))
    (fun _ => (simulateQ (localAnswer prims) oa).run' cache)
    (fun salt => (simulateQ (localAnswer prims) oa).run'
      (cache.cacheQuery (.digest (List.ofFn salt) (h salt)) (d salt)))
  simp only [tsum_fintype] at hb
  have hsum : (∑ salt : Fin 256 → Bit,Pr[= salt | $ᵗ (Fin 256 → Bit)].toReal * (prob salt).toReal) =
      Pr[fun z : α × HashCache C × Bool => z.2.2=true | (do
        let salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (cache,false))].toReal := by
    rw [probEvent_bind_eq_tsum,tsum_fintype,ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul,prob]
    · intro salt _
      exact ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top
  calc
    _ ≤ ∑ salt : Fin 256 → Bit,Pr[= salt | $ᵗ (Fin 256 → Bit)].toReal * (prob salt).toReal := by
      refine hb.trans (Finset.sum_le_sum fun salt _ => ?_)
      exact mul_le_mul_of_nonneg_left
        (digest_programming_until_salt prims cache (List.ofFn salt) (h salt) (d salt) oa)
        ENNReal.toReal_nonneg
    _ = _ := hsum
    _ ≤ (q : ℝ)/2^256 := by
      have hp := ENNReal.toReal_mono (by finiteness)
        (digestSaltFlag_bound prims oa cache q hq)
      simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,
        ENNReal.toReal_ofNat] using hp

end ThresholdLeanXmssSecurity
end

/-! ## Digest hide -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

lemma saltedDigestAnswer_fresh (prims : Primitives) (cache : HashCache C)
    (salt history : List Bit) (h : HashOutput)
    (hh : cache (.history history)=some h) (hf : cache (.digest salt h)=none) :
    (saltedDigestAnswer prims salt history).run cache =
      (fun d => (d,cache.cacheQuery (.digest salt h) d)) <$> ($ᵗ HashOutput) := by
  have hhistory : ¬ IsFixed (Query.history (C := C) history) := by rintro ⟨_,he,_⟩; cases he
  have hdigest : ¬ IsFixed (Query.digest (C := C) salt h) := by rintro ⟨_,he,_⟩; cases he
  simp only [saltedDigestAnswer,StateT.run_bind]
  rw [hashAnswer_run_cached prims hhistory hh,pure_bind,
    hashAnswer_of_not_isFixed prims hdigest,OracleSpec.randomOracle,QueryImpl.withCaching_run_none _ hf]
  rfl

/-- A real two-level salted commitment hides any already cached inner history from an arbitrary
q-query continuation. The continuation may contain the distinguisher and all subsequent rounds. -/
theorem saltedDigest_hide_fresh (prims : Primitives) (cache : HashCache C)
    (history : List Bit) (h : HashOutput) (hh : cache (.history history)=some h)
    (hf : ∀ salt : Fin 256 → Bit,cache (.digest (List.ofFn salt) h)=none)
    (k : HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ d,IsQueryBoundP (k d) Counted q) :
    tvDist
      (do let salt ← $ᵗ (Fin 256 → Bit)
          (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
            simulateQ (localAnswer prims) (k d)).run' cache)
      (do let d ← $ᵗ HashOutput
          (simulateQ (localAnswer prims) (k d)).run' cache) ≤ (q : ℝ)/2^256 := by
  let real : ProbComp α := do
    let salt ← $ᵗ (Fin 256 → Bit)
    (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
      simulateQ (localAnswer prims) (k d)).run' cache
  let programmed : ProbComp α := do
    let d ← $ᵗ HashOutput
    let salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run'
      (cache.cacheQuery (.digest (List.ofFn salt) h) d)
  let ghost : ProbComp α := do
    let d ← $ᵗ HashOutput
    let _salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run' cache
  have hr : 𝒟[real]=𝒟[programmed] := by
    have he : real = (do
        let salt ← $ᵗ (Fin 256 → Bit)
        let d ← $ᵗ HashOutput
        (simulateQ (localAnswer prims) (k d)).run'
          (cache.cacheQuery (.digest (List.ofFn salt) h) d)) := by
      unfold real
      apply bind_congr
      intro salt
      simp only [StateT.run'_eq,StateT.run_bind]
      rw [saltedDigestAnswer_fresh prims cache (List.ofFn salt) history h hh (hf salt)]
      simp only [bind_map_left,map_bind]
    rw [he]
    exact DeferredSampling.evalDist_bind_comm _ _ _
  have hg : 𝒟[ghost]=𝒟[(do
      let d ← $ᵗ HashOutput
      (simulateQ (localAnswer prims) (k d)).run' cache)] := by
    unfold ghost
    simp only [evalDist_bind]
    congr 1
    funext d
    simpa only [evalDist_bind] using DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ (Fin 256 → Bit)) (by simp) ((simulateQ (localAnswer prims) (k d)).run' cache)
  have hb : tvDist ghost programmed ≤ (q : ℝ)/2^256 := by
    apply tvDist_bind_left_le_const'
    intro d
    exact hidden_digest_programming_bound prims cache (fun _ => h) (fun _ => d) (k d) q (hq d)
  change tvDist real _ ≤ _
  simpa only [tvDist,hr,← hg,SPMF.tvDist_comm] using hb

end ThresholdLeanXmssSecurity
end

/-! ## Digest hide cache -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

def digestProgrammedGame (prims : Primitives) (cache : HashCache C) (h : HashOutput)
    (k : HashOutput → OracleComp (LocalSpec C) α) : ProbComp α := do
  let salt ← $ᵗ (Fin 256 → Bit)
  let d ← $ᵗ HashOutput
  (simulateQ (localAnswer prims) (k d)).run' (cache.cacheQuery (.digest (List.ofFn salt) h) d)

def digestGhostGame (prims : Primitives) (cache : HashCache C)
    (k : HashOutput → OracleComp (LocalSpec C) α) : ProbComp α := do
  let d ← $ᵗ HashOutput
  (simulateQ (localAnswer prims) (k d)).run' cache

lemma digestProgrammedGame_bound (prims : Primitives) (cache : HashCache C) (h : HashOutput)
    (k : HashOutput → OracleComp (LocalSpec C) α) (q : ℕ) (hq : ∀ d,IsQueryBoundP (k d) Counted q) :
    tvDist (digestProgrammedGame prims cache h k) (digestGhostGame prims cache k) ≤ (q : ℝ)/2^256 := by
  let programmed : ProbComp α := do
    let d ← $ᵗ HashOutput
    let salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run' (cache.cacheQuery (.digest (List.ofFn salt) h) d)
  let ghost : ProbComp α := do
    let d ← $ᵗ HashOutput
    let _salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run' cache
  have hr : 𝒟[digestProgrammedGame prims cache h k]=𝒟[programmed] :=
    DeferredSampling.evalDist_bind_comm _ _ _
  have hg : 𝒟[ghost]=𝒟[digestGhostGame prims cache k] := by
    unfold ghost digestGhostGame
    simp only [evalDist_bind]
    congr 1
    funext d
    simpa only [evalDist_bind] using DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ (Fin 256 → Bit)) (by simp) ((simulateQ (localAnswer prims) (k d)).run' cache)
  have hb : tvDist ghost programmed ≤ (q : ℝ)/2^256 := by
    apply tvDist_bind_left_le_const'
    intro d
    exact hidden_digest_programming_bound prims cache (fun _ => h) (fun _ => d) (k d) q (hq d)
  simpa only [tvDist,hr,← hg,SPMF.tvDist_comm] using hb

/-- A two-level commitment hides its history even after earlier oracle queries. Only their
outer digest salts are charged; the inner history may already be completely known. -/
theorem saltedDigest_hide (prims : Primitives) (cache : HashCache C)
    (history : List Bit) (h : HashOutput) (hh : cache (.history history)=some h)
    (seen : Finset (List Bit))
    (hf : ∀ salt : Fin 256 → Bit,List.ofFn salt ∉ seen → cache (.digest (List.ofFn salt) h)=none)
    (k : HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ d,IsQueryBoundP (k d) Counted q) :
    tvDist
      (do let salt ← $ᵗ (Fin 256 → Bit)
          (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
            simulateQ (localAnswer prims) (k d)).run' cache)
      (digestGhostGame prims cache k) ≤ ((seen.card+q : ℕ) : ℝ)/2^256 := by
  let actual : (Fin 256 → Bit) → ProbComp α := fun salt =>
    (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
      simulateQ (localAnswer prims) (k d)).run' cache
  let overwrite : (Fin 256 → Bit) → ProbComp α := fun salt => do
    let d ← $ᵗ HashOutput
    (simulateQ (localAnswer prims) (k d)).run' (cache.cacheQuery (.digest (List.ofFn salt) h) d)
  have hstep : ∀ salt,List.ofFn salt ∉ seen → 𝒟[actual salt]=𝒟[overwrite salt] := by
    intro salt hs
    have he : actual salt=overwrite salt := by
      simp only [actual,overwrite,StateT.run'_eq,StateT.run_bind]
      rw [saltedDigestAnswer_fresh prims cache (List.ofFn salt) history h hh (hf salt hs)]
      simp only [bind_map_left,map_bind]
    rw [he]
  have hb := tvDist_bind_left_event_le ($ᵗ (Fin 256 → Bit)) actual overwrite
    (fun salt => List.ofFn salt ∈ seen) hstep
  have hguess : Pr[fun salt : Fin 256 → Bit => List.ofFn salt ∈ seen | $ᵗ (Fin 256 → Bit)].toReal ≤
      (seen.card : ℝ)/2^256 := by
    have hg := probEvent_uniform_injective_mem (fun salt : Fin 256 → Bit => List.ofFn salt)
      List.ofFn_injective seen
    have hgr := ENNReal.toReal_mono (by finiteness) hg
    simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat,
      ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using hgr
  have hc := digestProgrammedGame_bound prims cache h k q hq
  have ht := tvDist_triangle (($ᵗ (Fin 256 → Bit)) >>= actual)
    (digestProgrammedGame prims cache h k) (digestGhostGame prims cache k)
  refine ht.trans ?_
  calc
    _ ≤ (seen.card : ℝ)/2^256 + (q : ℝ)/2^256 := add_le_add (hb.trans hguess) hc
    _ = _ := by push_cast; ring

end ThresholdLeanXmssSecurity
end

/-! ## Salt projected -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

/-- The adaptive query trace is independent of a freshly chosen hidden salt. -/
theorem digestSaltFlag_boundP (prims : Primitives) (oa : OracleComp (LocalSpec C) α)
    (s : HashCache C) (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : IsQueryBoundP oa charged q) :
    Pr[fun z : α × HashCache C × Bool => z.2.2=true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false))] ≤
      (q : ℝ≥0∞)/2^256 := by
  let raw := (simulateQ (projectQueries (localAnswer prims) digestSaltProjection) oa).run (s,[])
  let trace := (fun z : α × HashCache C × List (List Bit) => z.2.2) <$> raw
  have ht : ∀ l ∈ support trace,l.length ≤ q := by
    intro l hl
    simp only [trace,support_map,Set.mem_image] at hl
    obtain ⟨z,hz,rfl⟩ := hl
    simpa using projectQueries_length (localAnswer prims) charged digestSaltProjection
      hproject hq s [] hz
  have hb := independent_salt_trace_bound trace q ht
  have hp : ∀ salt : Fin 256 → Bit,
      Pr[fun z : α × HashCache C × Bool => z.2.2=true |
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false)] =
      Pr[fun l => List.ofFn salt ∈ l | trace] := by
    intro salt
    rw [digestSaltHit_projection]
    have he := projectQueries_flag (localAnswer prims) digestSaltProjection (List.ofFn salt) oa s []
    simp only [List.not_mem_nil,decide_false] at he
    have he' : (simulateQ (flagQueries (localAnswer prims)
        (fun t => decide (digestSaltProjection t=some (List.ofFn salt)))) oa).run (s,false) =
        (fun z : α × HashCache C × List (List Bit) => (z.1,(z.2.1,decide (List.ofFn salt ∈ z.2.2)))) <$> raw := by
      convert he.symm using 1 <;> congr
      · funext t
        by_cases h : digestSaltProjection t=some (List.ofFn salt) <;> simp only [h,decide_true,decide_false]
      · funext z
        by_cases h : List.ofFn salt ∈ z.2.2 <;> simp only [h,decide_true,decide_false]
    rw [he',probEvent_map]
    simp only [trace,probEvent_map,Function.comp_def,decide_eq_true_eq]
  have he : Pr[fun z : α × HashCache C × Bool => z.2.2=true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false))] =
      Pr[fun p : List (List Bit) × (Fin 256 → Bit) => List.ofFn p.2 ∈ p.1 | (do
        let l ← trace; let salt ← $ᵗ (Fin 256 → Bit); pure (l,salt))] := by
    simp only [probEvent_bind_eq_tsum,hp,probEvent_pure]
    simp only [probEvent_eq_tsum_ite]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro l
    apply tsum_congr
    intro salt
    split_ifs <;> simp [mul_comm]

  rw [he]
  exact hb

end ThresholdLeanXmssSecurity
end

/-! ## Digest projected -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

/-- Programming a digest at an independent hidden salt costs at most q/2^256,
even if its inner hash and programmed value depend on that salt. -/
theorem hidden_digest_programming_boundP (prims : Primitives) (cache : HashCache C)
    (h d : (Fin 256 → Bit) → HashOutput) (oa : OracleComp (LocalSpec C) α)
    (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : IsQueryBoundP oa charged q) :
    tvDist (do
        let _salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (localAnswer prims) oa).run' cache)
      (do
        let salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (localAnswer prims) oa).run'
          (cache.cacheQuery (.digest (List.ofFn salt) (h salt)) (d salt))) ≤
      (q : ℝ)/2^256 := by
  let prob := fun salt : Fin 256 → Bit =>
    Pr[fun z : α × HashCache C × Bool => z.2.2=true |
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (cache,false)]
  have hb := tvDist_bind_left_le ($ᵗ (Fin 256 → Bit))
    (fun _ => (simulateQ (localAnswer prims) oa).run' cache)
    (fun salt => (simulateQ (localAnswer prims) oa).run'
      (cache.cacheQuery (.digest (List.ofFn salt) (h salt)) (d salt)))
  simp only [tsum_fintype] at hb
  have hsum : (∑ salt : Fin 256 → Bit,Pr[= salt | $ᵗ (Fin 256 → Bit)].toReal * (prob salt).toReal) =
      Pr[fun z : α × HashCache C × Bool => z.2.2=true | (do
        let salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (cache,false))].toReal := by
    rw [probEvent_bind_eq_tsum,tsum_fintype,ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul,prob]
    · intro salt _
      exact ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top
  calc
    _ ≤ ∑ salt : Fin 256 → Bit,Pr[= salt | $ᵗ (Fin 256 → Bit)].toReal * (prob salt).toReal := by
      refine hb.trans (Finset.sum_le_sum fun salt _ => ?_)
      exact mul_le_mul_of_nonneg_left
        (digest_programming_until_salt prims cache (List.ofFn salt) (h salt) (d salt) oa)
        ENNReal.toReal_nonneg
    _ = _ := hsum
    _ ≤ (q : ℝ)/2^256 := by
      have hp := ENNReal.toReal_mono (by finiteness)
        (digestSaltFlag_boundP prims oa cache charged hproject q hq)
      simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,
        ENNReal.toReal_ofNat] using hp

lemma digestProgrammedGame_boundP (prims : Primitives) (cache : HashCache C) (h : HashOutput)
    (k : HashOutput → OracleComp (LocalSpec C) α) (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : ∀ d,IsQueryBoundP (k d) charged q) :
    tvDist (digestProgrammedGame prims cache h k) (digestGhostGame prims cache k) ≤ (q : ℝ)/2^256 := by
  let programmed : ProbComp α := do
    let d ← $ᵗ HashOutput
    let salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run' (cache.cacheQuery (.digest (List.ofFn salt) h) d)
  let ghost : ProbComp α := do
    let d ← $ᵗ HashOutput
    let _salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run' cache
  have hr : 𝒟[digestProgrammedGame prims cache h k]=𝒟[programmed] :=
    DeferredSampling.evalDist_bind_comm _ _ _
  have hg : 𝒟[ghost]=𝒟[digestGhostGame prims cache k] := by
    unfold ghost digestGhostGame
    simp only [evalDist_bind]
    congr 1
    funext d
    simpa only [evalDist_bind] using DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ (Fin 256 → Bit)) (by simp) ((simulateQ (localAnswer prims) (k d)).run' cache)
  have hb : tvDist ghost programmed ≤ (q : ℝ)/2^256 := by
    apply tvDist_bind_left_le_const'
    intro d
    exact hidden_digest_programming_boundP prims cache (fun _ => h) (fun _ => d) (k d) charged hproject q (hq d)
  simpa only [tvDist,hr,← hg,SPMF.tvDist_comm] using hb

/-- A two-level commitment hides its history even after earlier oracle queries. Only their
outer digest salts are charged; the inner history may already be completely known. -/
theorem saltedDigest_hideP (prims : Primitives) (cache : HashCache C)
    (history : List Bit) (h : HashOutput) (hh : cache (.history history)=some h)
    (seen : Finset (List Bit))
    (hf : ∀ salt : Fin 256 → Bit,List.ofFn salt ∉ seen → cache (.digest (List.ofFn salt) h)=none)
    (k : HashOutput → OracleComp (LocalSpec C) α)
    (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : ∀ d,IsQueryBoundP (k d) charged q) :
    tvDist
      (do let salt ← $ᵗ (Fin 256 → Bit)
          (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
            simulateQ (localAnswer prims) (k d)).run' cache)
      (digestGhostGame prims cache k) ≤ ((seen.card+q : ℕ) : ℝ)/2^256 := by
  let actual : (Fin 256 → Bit) → ProbComp α := fun salt =>
    (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
      simulateQ (localAnswer prims) (k d)).run' cache
  let overwrite : (Fin 256 → Bit) → ProbComp α := fun salt => do
    let d ← $ᵗ HashOutput
    (simulateQ (localAnswer prims) (k d)).run' (cache.cacheQuery (.digest (List.ofFn salt) h) d)
  have hstep : ∀ salt,List.ofFn salt ∉ seen → 𝒟[actual salt]=𝒟[overwrite salt] := by
    intro salt hs
    have he : actual salt=overwrite salt := by
      simp only [actual,overwrite,StateT.run'_eq,StateT.run_bind]
      rw [saltedDigestAnswer_fresh prims cache (List.ofFn salt) history h hh (hf salt hs)]
      simp only [bind_map_left,map_bind]
    rw [he]
  have hb := tvDist_bind_left_event_le ($ᵗ (Fin 256 → Bit)) actual overwrite
    (fun salt => List.ofFn salt ∈ seen) hstep
  have hguess : Pr[fun salt : Fin 256 → Bit => List.ofFn salt ∈ seen | $ᵗ (Fin 256 → Bit)].toReal ≤
      (seen.card : ℝ)/2^256 := by
    have hg := probEvent_uniform_injective_mem (fun salt : Fin 256 → Bit => List.ofFn salt)
      List.ofFn_injective seen
    have hgr := ENNReal.toReal_mono (by finiteness) hg
    simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat,
      ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using hgr
  have hc := digestProgrammedGame_boundP prims cache h k charged hproject q hq
  have ht := tvDist_triangle (($ᵗ (Fin 256 → Bit)) >>= actual)
    (digestProgrammedGame prims cache h k) (digestGhostGame prims cache k)
  refine ht.trans ?_
  calc
    _ ≤ (seen.card : ℝ)/2^256 + (q : ℝ)/2^256 := add_le_add (hb.trans hguess) hc
    _ = _ := by push_cast; ring

end ThresholdLeanXmssSecurity
end

/-! ## Rand phases -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α R : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def afterRandom (hs : RunState C) (f : PrssOutput C R → RunM C E (CheckSpec C E) α)
    (out : Option (PrssOutput C R)) : PartyM C E (CheckSpec C E) α :=
  match out with
  | some w => (f w).run' ⟨hs.history,hs.label+1,hs.tag⟩
  | none => failure

/-- The actual mask-sampling phase, including the adversary's chosen known terms. -/
theorem executePhase_randElements (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (count : C.Party → ℕ) (hs : C.Party → RunState C)
    (f : C.Party → PrssOutput C E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => ((hybridCheckGadgets K i).randElements (count i) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (leftAdversary (rightAdversary A)) (Frand E) st
        (fun i => if i ∈ D.1 then none else some (count i))
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterRandom (hs i) (f i) (p.2 i))) := by
  simp_rw [randElements_run']
  rw [executePhase_call,runCheck_randElements,bind_map_left]
  apply bind_congr
  intro p
  dsimp only
  congr 1
  funext i
  cases he : p.2 i <;> rfl

/-- The actual salt-sampling phase, with the same arbitrary-adversary normalization. -/
theorem executePhase_randBits (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (count : C.Party → ℕ) (hs : C.Party → RunState C)
    (f : C.Party → PrssOutput C Bit → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => ((hybridCheckGadgets K i).randBits (count i) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (rightAdversary (rightAdversary A)) (Frand Bit) st
        (fun i => if i ∈ D.1 then none else some (count i))
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterRandom (hs i) (f i) (p.2 i))) := by
  simp_rw [randBits_run']
  rw [executePhase_call,runCheck_randBits,bind_map_left]
  apply bind_congr
  intro p
  dsimp only
  congr 1
  funext i
  cases he : p.2 i <;> rfl

/-- The fresh PRSS pair table is irrelevant whenever the continuation uses only replicated terms. -/
theorem randFinish_first (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin count → R)
    (pairs pairs' : C.Pair → Fin count → R) [Zero R] (i : C.Party) :
    (randFinish D count known knownPairs fresh pairs i).map Prod.fst =
      (randFinish D count known knownPairs fresh pairs' i).map Prod.fst := by
  unfold randFinish
  by_cases hi : i ∈ D.1 <;> simp [hi]

end ThresholdLeanXmssSecurity
end

/-! ## Mask phase -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma sameRun_discard_sample (prims : Primitives) {β γ : Type} [SampleableType β]
    (oa : OracleComp (LocalSpec C) γ) :
    SameRun prims (liftComp ($ᵗ β) (LocalSpec C) >>= fun _ => oa) oa := by
  intro s
  simp only [simulateQ_bind,StateT.run_bind,run_liftComp_prob,bind_map_left]
  change 𝒟[(do let b ← $ᵗ β; (simulateQ (localAnswer prims) oa).run s)] = _
  exact DeferredSampling.evalDist_bind_const_neverFails ($ᵗ β) (by simp) _

/-- The actual final mask phase reduces to the chosen known terms and one fresh hidden table;
the unused PRSS pair table has no effect on the entire adaptive continuation. -/
theorem executePhase_randElements_first (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (count : ℕ)
    (hs : C.Party → RunState C) (f : C.Party → Shares C E → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
        (fun i => ((hybridCheckGadgets K i).randElements count >>= fun w => f i w.1).run' (hs i)))
      (do
        let p ← (leftAdversary (rightAdversary A)).answer st ()
        let fresh ← liftComp ($ᵗ (C.Term → Fin count → E)) (LocalSpec C)
        executePhase localRoles D A (checkFunctionalities K) fuel p.1
          (fun i => (f i (randShares D count p.2.1 fresh i)).run'
            ⟨(hs i).history,(hs i).label+1,(hs i).tag⟩)) := by
  rw [executePhase_randElements,runFunctionality_rand_local D (leftAdversary (rightAdversary A)) st _
    (by intro i hi; simp [hi]),firstInput_honest_const]
  simp only [bind_assoc,pure_bind]
  apply SameRun.bind_right
  intro p
  apply SameRun.bind_right
  intro fresh
  refine SameRun.trans (SameRun.bind_right _ fun pairs => ?_) (sameRun_discard_sample prims _)
  apply SameRun.of_eq
  apply executePhase_congr_honest
  intro i hi
  simp only [afterRandom,randFinish,if_neg hi]
  congr 2
  funext T g
  by_cases ht : i ∈ C.holders T <;> by_cases hk : KnownTo D.1 T <;> simp [randShares,ht,hk]

end ThresholdLeanXmssSecurity
end

/-! ## Masked extend -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def maskedProducts (K : Constants C E) (A B : C.Party → E) (i : C.Party) (w : Shares C E) :
    List (Product C E) :=
  let wa := conv K (localContext i) w 0
  let wb := conv K (localContext i) w 1
  [.shamir (fun _ => wa) (fun _ => wb) 1,
   .shamir (fun _ => wa+A i) (fun _ => wb+B i) 1]

def maskedInputs (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (A B : C.Party → E) : C.Party → Option (List (Product C E)) := fun i =>
  if i ∈ D.1 then none else some (maskedProducts K A B i (randShares D 2 known w i))

lemma maskedInputs_view (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (A B : C.Party → E) :
    extendView K D.1 (maskedInputs K D known w A B)=maskedView K D known w A B := rfl

lemma maskedInputs_width (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (A B : C.Party → E) :
    (firstInput (maskedInputs K D known w A B)).length=2 := by
  obtain ⟨j,_,hj⟩ := firstInput_honest D (fun i => maskedProducts K A B i (randShares D 2 known w i))
  change (firstInput (fun i => if i ∈ D.1 then none else
    some (maskedProducts K A B i (randShares D 2 known w i)))).length=2
  rw [hj]
  rfl

/-- The actual final masked multiplication, after the PRSS table is fixed. Its adaptive leak
is independent of the hidden table, while its output retains the exact additive attack. -/
theorem executePhase_maskedExtend (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (known : Shares C E) (w : MaskTable C E) (A B : C.Party → E)
    (hs : C.Party → RunState C) (f : C.Party → Shares C E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel+1) st
      (fun i => ((hybridCheckGadgets K i).extendMult
        (maskedProducts K A B i (randShares D 2 known w i)) >>= f i).run' (hs i)) = (do
      let p ← (rightAdversary (leftAdversary Ad)).answer st (maskedView K D known 0 A B)
      let fresh ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
      executePhase localRoles D Ad (checkFunctionalities K) fuel p.1
        (fun i => afterExtend K i 2 (hs i) (f i)
          (multFinish D 2 (filler K .peer)
            (fun g => extendTotal K D (maskedInputs K D known w A B) g+p.2.1 g)
            p.2.2.1 p.2.2.2.1 p.2.2.2.2 fresh i))) := by
  rw [executePhase_extend]
  change (runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st
    (maskedInputs K D known w A B) >>= _) = _
  rw [runFunctionality_extend_local K D (rightAdversary (leftAdversary Ad)) st _
    (by intro i hi; simp [maskedInputs,hi])]
  rw [maskedInputs_width,maskedInputs_view,maskedView_eq K D known w 0 A B]
  simp only [bind_assoc,pure_bind]
  rfl

end ThresholdLeanXmssSecurity
end

/-! ## Masked phase -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- Both actual adaptive replies in final randomization precede its hidden tables in distribution.
The rest is the original scheduler, with its exact histories and all selective-abort cases. -/
theorem executePhase_finalMasks (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (fuel : ℕ) (st : Ad.State)
    (A B : C.Party → E) (hs : C.Party → RunState C)
    (f : C.Party → Shares C E → Shares C E → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) (fuel+2) st
        (fun i => (do
          let w ← (hybridCheckGadgets K i).randElements 2
          let q ← (hybridCheckGadgets K i).extendMult (maskedProducts K A B i w.1)
          f i w.1 q).run' (hs i)))
      (do
        let p ← (leftAdversary (rightAdversary Ad)).answer st ()
        let p' ← (rightAdversary (leftAdversary Ad)).answer p.1 (maskedView K D p.2.1 0 A B)
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel p'.1
          (fun i => afterExtend K i 2 ⟨(hs i).history,(hs i).label+1,(hs i).tag⟩
            (f i (randShares D 2 p.2.1 w i))
            (multFinish D 2 (filler K .peer)
              (fun g => extendTotal K D (maskedInputs K D p.2.1 w A B) g+p'.2.1 g)
              p'.2.2.1 p'.2.2.2.1 p'.2.2.2.2 q i))) := by
  refine (executePhase_randElements_first prims K D Ad (fuel+1) st 2 hs
    (fun i w => (hybridCheckGadgets K i).extendMult (maskedProducts K A B i w) >>= f i w)).trans ?_
  refine SameRun.bind_right ((leftAdversary (rightAdversary Ad)).answer st ()) ?_
  intro p
  simp_rw [executePhase_maskedExtend]
  exact sameRun_swap prims (liftComp ($ᵗ (MaskTable C E)) (LocalSpec C))
    ((rightAdversary (leftAdversary Ad)).answer p.1 (maskedView K D p.2.1 0 A B)) _

end ThresholdLeanXmssSecurity
end

/-! ## Partial abort -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O Ia L R α : Type}

/-- A single absent honest functionality caller makes this phase abort without another adversary callback. -/
theorem executePhase_partialCall_abort (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (input : C.Party → Option I)
    (f : C.Party → Option O → PartyM C E (CallSpec I O) α)
    (hf : ∀ i,i ∉ D.1 → f i none=failure)
    (hmissing : ∃ i,i ∉ D.1 ∧ input i=none) :
    executePhase localRoles D A F (fuel+1) st (fun i => optionalCall (input i) (f i)) =
      pure (st,fun _ => none) := by
  rw [executePhase_optionalCall D A F fuel st input f hf]
  have hnone : ¬ ∀ i,i ∉ D.1 → ((if i ∈ D.1 then none else input i) : Option I).isSome := by
    obtain ⟨i,hi,he⟩ := hmissing
    intro h
    simpa [hi,he] using h i hi
  rw [runFunctionality,if_pos hnone,pure_bind]
  dsimp only
  rw [executePhase_congr_honest D A F fuel st _ (fun _ => failure) hf,executePhase_failure]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- An abort of the final masked multiplication stops salt generation before its leak. -/
theorem executePhase_randBits_missing (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (count : ℕ)
    (hs : C.Party → RunState C) (live : C.Party → Prop)
    (f : C.Party → PrssOutput C Bit → RunM C E (CheckSpec C E) α)
    (hmissing : ∃ i,i ∉ D.1 ∧ ¬live i) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => if live i then ((hybridCheckGadgets K i).randBits count >>= f i).run' (hs i) else failure) =
      pure (st,fun _ => none) := by
  let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) α := fun i o => match o with
    | some (.inr (.inr w)) => (f i w).run' ⟨(hs i).history,(hs i).label+1,(hs i).tag⟩
    | _ => failure
  have hp : (fun i => if live i then ((hybridCheckGadgets K i).randBits count >>= f i).run' (hs i) else failure) =
      (fun i => optionalCall (if live i then some (.inr (.inr count)) else none) (next i)) := by
    funext i
    by_cases hi : live i <;> simp only [hi,if_true,if_false,optionalCall,randBits_run',next]
    apply bind_congr
    intro o
    rcases o with _ | ((a | b) | (c | d)) <;> rfl
  rw [hp]
  apply executePhase_partialCall_abort
  · intro i hi; rfl
  · obtain ⟨i,hi,hl⟩ := hmissing
    exact ⟨i,hi,if_neg hl⟩

end ThresholdLeanXmssSecurity
end

/-! ## Local phase -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O Ia L R α β : Type} [Inhabited β]

/-- The honest local oracle computations can precede every honest continuation, with the
same final oracle cache. Corrupt programs are not run. -/
theorem startSteps_local (prims : Primitives) (D : C.Coalition)
    (oa : C.Party → OracleComp (LocalSpec C) β)
    (f : C.Party → β → PartyM C E (CallSpec I O) α) :
    SameRun prims (startSteps localRoles D (fun i => localStep (oa i) >>= f i))
      (do
        let v ← Concrete.sequenceFin (fun i => if i ∈ D.1 then pure default else oa i)
        startSteps localRoles D (fun i => f i (v i))) := by
  let queries : C.Party → OracleComp (LocalSpec C) β := fun i => if i ∈ D.1 then pure default else oa i
  let next : C.Party → β → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) :=
    fun i b => if i ∈ D.1 then pure (.done none) else advance (f i b).run
  have hn : startSteps localRoles D (fun i => localStep (oa i) >>= f i) =
      Concrete.sequenceFin (fun i => do let b ← queries i; let v ← next i b; pure v) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;>
      simp only [queries,next,hi,if_true,if_false,pure_bind,bind_pure,localRoles,advance_localStep_bind]
  rw [hn]
  have hh := sameRun_sequenceFin_dep prims queries next (fun _ _ v => v)
  refine hh.trans (SameRun.of_eq ?_)
  apply bind_congr
  intro v
  change (Concrete.sequenceFin (fun i => next i (v i)) >>= pure) = _
  rw [bind_pure]
  rfl

/-- The scheduler preserves that reordering through the complete adaptive network continuation. -/
theorem executePhase_local (prims : Primitives) (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (oa : C.Party → OracleComp (LocalSpec C) β)
    (f : C.Party → β → PartyM C E (CallSpec I O) α) :
    SameRun prims (executePhase localRoles D A F fuel st (fun i => localStep (oa i) >>= f i))
      (do
        let v ← Concrete.sequenceFin (fun i => if i ∈ D.1 then pure default else oa i)
        executePhase localRoles D A F fuel st (fun i => f i (v i))) := by
  unfold executePhase
  have h := (startSteps_local prims D oa f).bind (fun steps =>
    SameRun.refl prims (executeRounds localRoles D A F fuel st steps))
  simpa only [bind_assoc] using h

end ThresholdLeanXmssSecurity
end

/-! ## Ro selected -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {β : Type}

lemma sequenceFin_select_none {n : ℕ} (oa : OracleComp (LocalSpec C) β) (pick : Fin n → Prop)
    (fallback : β) (hn : ¬∃ i,pick i) :
    Concrete.sequenceFin (fun i => if pick i then oa else pure fallback) = pure (fun _ => fallback) := by
  have hp : (fun i => if pick i then oa else pure fallback) = fun _ => pure fallback := by
    funext i
    exact if_neg (fun hi => hn ⟨i,hi⟩)
  rw [hp,sequenceFin_pure]

/-- A shared deterministic oracle computation is performed once for its honest holders.
This also covers nonholders and corrupt slots, whose entries are fixed fallbacks. -/
theorem sameRun_sequenceFin_selected (prims : Primitives) (oa : OracleComp (RoSpec C) β)
    (fallback : β) : ∀ {n : ℕ} (pick : Fin n → Prop), (∃ i,pick i) →
    SameRun prims (Concrete.sequenceFin (fun i => if pick i then liftComp oa (LocalSpec C) else pure fallback))
      (do let v ← liftComp oa (LocalSpec C); pure (fun i => if pick i then v else fallback))
  | 0,pick,h => by obtain ⟨i,_⟩ := h; exact i.elim0
  | n+1,pick,h => by
    rw [Concrete.sequenceFin]
    by_cases hrest : ∃ i : Fin n,pick i.succ
    · have hi := sameRun_sequenceFin_selected prims oa fallback (fun i : Fin n => pick i.succ) hrest
      refine (SameRun.bind_right _ fun v => hi.bind (fun rest => SameRun.refl prims (pure (Fin.cases (motive := fun _ => β) v rest)))).trans ?_
      simp only [bind_assoc,pure_bind]
      by_cases hzero : pick 0
      · simp only [if_pos hzero]
        refine (sameRun_ro_dup prims oa (fun a b => pure (Fin.cases (motive := fun _ => β) a (fun i => if pick i.succ then b else fallback)))).trans ?_
        apply SameRun.of_eq
        apply bind_congr
        intro v
        congr 1
        funext i
        cases i using Fin.cases <;> simp [hzero]
      · simp only [if_neg hzero,pure_bind]
        apply SameRun.of_eq
        apply bind_congr
        intro v
        congr 1
        funext i
        cases i using Fin.cases <;> simp [hzero]
    · have hzero : pick 0 := by
        obtain ⟨i,hi⟩ := h
        cases i using Fin.cases with
        | zero => exact hi
        | succ i => exact False.elim (hrest ⟨i,hi⟩)
      rw [if_pos hzero,sequenceFin_select_none _ (fun i : Fin n => pick i.succ) fallback hrest]
      simp only [pure_bind]
      apply SameRun.of_eq
      apply bind_congr
      intro v
      congr 1
      funext i
      cases i using Fin.cases with
      | zero => simp [hzero]
      | succ i => simp [show ¬pick i.succ from fun hi => hrest ⟨i,hi⟩]

end ThresholdLeanXmssSecurity
end

/-! ## Digest columns -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α β : Type} {n : ℕ}

def queryColumns (f : Fin n → α → OracleComp (LocalSpec C) β) :
    List α → OracleComp (LocalSpec C) (Fin n → List β)
  | [] => pure (fun _ => [])
  | a::as => do
    let head ← Concrete.sequenceFin (fun i => f i a)
    let tail ← queryColumns f as
    pure (fun i => head i::tail i)

/-- Independent local query rows can be evaluated by columns without changing their answers or cache. -/
theorem sameRun_queryColumns (prims : Primitives)
    (f : Fin n → α → OracleComp (LocalSpec C) β) (as : List α) :
    SameRun prims (Concrete.sequenceFin (fun i => as.mapM (f i))) (queryColumns f as) := by
  induction as with
  | nil => simp only [List.mapM_nil,sequenceFin_pure,queryColumns]; exact SameRun.refl prims _
  | cons a as ih =>
    simp only [List.mapM_cons,queryColumns]
    have h := sameRun_sequenceFin_dep prims (fun i => f i a) (fun i _ => as.mapM (f i))
      (fun _ x xs => x::xs)
    refine h.trans ?_
    apply SameRun.bind_right
    intro head
    exact ih.bind (fun tail => SameRun.refl prims (pure (fun i => head i::tail i)))

variable (D : C.Coalition)

def oneDigestQuery (salt history : List Bit) : OracleComp (RoSpec C) HashOutput := do
  let h ← hashQuery (.history history)
  hashQuery (.digest salt h)

def honestDigestColumn (T : C.Term) (salts : C.Party → Shares C Bit)
    (history : C.Party → C.Term → List Bit) (i : C.Party) : OracleComp (LocalSpec C) HashOutput :=
  if i ∉ D.1 ∧ i ∈ C.holders T then
    liftComp (oneDigestQuery (C := C) (vector 256 (salts i T)) (history i T)) (LocalSpec C)
  else pure 0

/-- All honest holders of an agreeing term use one two-level digest, even though each sends a copy. -/
theorem honestDigestColumn_common (prims : Primitives) (T : C.Term)
    (salts : C.Party → Shares C Bit) (history : C.Party → C.Term → List Bit)
    (salt hist : List Bit)
    (hs : ∀ i,i ∉ D.1 → i ∈ C.holders T → vector 256 (salts i T)=salt)
    (hh : ∀ i,i ∉ D.1 → i ∈ C.holders T → history i T=hist) :
    SameRun prims (Concrete.sequenceFin (honestDigestColumn D T salts history))
      (do
        let d ← liftComp (oneDigestQuery (C := C) salt hist) (LocalSpec C)
        pure (fun i => if i ∉ D.1 ∧ i ∈ C.holders T then d else 0)) := by
  have hc : honestDigestColumn D T salts history =
      (fun i => if i ∉ D.1 ∧ i ∈ C.holders T then
        liftComp (oneDigestQuery (C := C) salt hist) (LocalSpec C) else pure 0) := by
    funext i
    unfold honestDigestColumn
    by_cases hi : i ∉ D.1 ∧ i ∈ C.holders T
    · simp only [if_pos hi,hs i hi.1 hi.2,hh i hi.1 hi.2]
    · simp only [if_neg hi]
  rw [hc]
  have ha : ∃ i,i ∉ D.1 ∧ i ∈ C.holders T := by
    obtain ⟨i,hi,ht⟩ := exists_honest_holder D T
    exact ⟨i,ht,hi⟩
  convert sameRun_sequenceFin_selected prims (oneDigestQuery (C := C) salt hist) 0
    (fun i => i ∉ D.1 ∧ i ∈ C.holders T) ha using 1 <;> congr
  · funext i
    split_ifs <;> rfl
  · funext d
    congr 1
    funext i
    split_ifs <;> rfl

end ThresholdLeanXmssSecurity
end

/-! ## Local fallback -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E I O Ia L R α β : Type} 

/-- The honest local oracle computations can precede every honest continuation, with the
same final oracle cache. Corrupt programs are not run. -/
theorem startSteps_local_fallback (prims : Primitives) (D : C.Coalition)
    (oa : C.Party → OracleComp (LocalSpec C) β) (fallback : C.Party → β)
    (f : C.Party → β → PartyM C E (CallSpec I O) α) :
    SameRun prims (startSteps localRoles D (fun i => localStep (oa i) >>= f i))
      (do
        let v ← Concrete.sequenceFin (fun i => if i ∈ D.1 then pure (fallback i) else oa i)
        startSteps localRoles D (fun i => f i (v i))) := by
  let queries : C.Party → OracleComp (LocalSpec C) β := fun i => if i ∈ D.1 then pure (fallback i) else oa i
  let next : C.Party → β → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) :=
    fun i b => if i ∈ D.1 then pure (.done none) else advance (f i b).run
  have hn : startSteps localRoles D (fun i => localStep (oa i) >>= f i) =
      Concrete.sequenceFin (fun i => do let b ← queries i; let v ← next i b; pure v) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;>
      simp only [queries,next,hi,if_true,if_false,pure_bind,bind_pure,localRoles,advance_localStep_bind]
  rw [hn]
  have hh := sameRun_sequenceFin_dep prims queries next (fun _ _ v => v)
  refine hh.trans (SameRun.of_eq ?_)
  apply bind_congr
  intro v
  change (Concrete.sequenceFin (fun i => next i (v i)) >>= pure) = _
  rw [bind_pure]
  rfl

/-- The scheduler preserves that reordering through the complete adaptive network continuation. -/
theorem executePhase_local_fallback (prims : Primitives) (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (oa : C.Party → OracleComp (LocalSpec C) β) (fallback : C.Party → β)
    (f : C.Party → β → PartyM C E (CallSpec I O) α) :
    SameRun prims (executePhase localRoles D A F fuel st (fun i => localStep (oa i) >>= f i))
      (do
        let v ← Concrete.sequenceFin (fun i => if i ∈ D.1 then pure (fallback i) else oa i)
        executePhase localRoles D A F fuel st (fun i => f i (v i))) := by
  unfold executePhase
  have h := (startSteps_local_fallback prims D oa fallback f).bind (fun steps =>
    SameRun.refl prims (executeRounds localRoles D A F fuel st steps))
  simpa only [bind_assoc] using h

end ThresholdLeanXmssSecurity
end

/-! ## Digest phase -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}

def afterDigests (i : C.Party) (ds : List HashOutput) (k : PartyM C E (CheckSpec C E) α) :
    PartyM C E (CheckSpec C E) α := do
  let inbox ← exchange (digestOutbox i ds)
  require (DigestsAgree i ds inbox)
  k

lemma lift_digest_row (D : C.Coalition) (i : C.Party) (hi : i ∉ D.1)
    (salts : C.Party → Shares C Bit) (history : C.Party → C.Term → List Bit) (ts : List C.Term) :
    liftComp (ts.mapM (fun T => if i ∈ C.holders T then
      oneDigestQuery (C := C) (vector 256 (salts i T)) (history i T) else pure 0)) (LocalSpec C) =
      ts.mapM (fun T => honestDigestColumn D T salts history i) := by
  induction ts with
  | nil => simp
  | cons T ts ih =>
    simp only [List.mapM_cons,liftComp_bind,liftComp_pure,ih]
    have hh : (liftComp (if i ∈ C.holders T then
        oneDigestQuery (C := C) (vector 256 (salts i T)) (history i T) else pure 0) (LocalSpec C)) =
        honestDigestColumn D T salts history i := by
      by_cases ht : i ∈ C.holders T <;> simp [honestDigestColumn,hi,ht]
    rw [hh]

lemma digest_rows_honest (D : C.Coalition) (salts : C.Party → Shares C Bit)
    (history : C.Party → C.Term → List Bit) :
    (fun i => if i ∈ D.1 then pure (C.terms.map (fun _ => (0 : HashOutput))) else
      liftComp (digestQuery i (salts i) (history i)) (LocalSpec C)) =
    (fun i => C.terms.mapM (fun T => honestDigestColumn D T salts history i)) := by
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
    have hc : (fun T => honestDigestColumn D T salts history i) = fun _ => pure (0 : HashOutput) := by
      funext T
      simp [honestDigestColumn,hi]
    rw [hc,List.mapM_pure]
  · simp only [if_neg hi]
    exact lift_digest_row D i hi salts history C.terms

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The actual digest phase can be evaluated one term at a time, then execute its unchanged
rushing network round and entire continuation. This exposes one common digest per honest term. -/
theorem executePhase_digestColumns (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (salts : C.Party → Shares C Bit)
    (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) fuel st
        (fun i => (compareDigests (localContext i) (salts i) >>= f i).run' (hs i)))
      (do
        let ds ← queryColumns (fun i T => honestDigestColumn D T salts (fun j => (hs j).history) i) C.terms
        executePhase localRoles D A (checkFunctionalities K) fuel st
          (fun i => afterDigests i (ds i) ((f i ()).run' (hs i)))) := by
  simp_rw [compareDigests_run']
  change SameRun prims (executePhase localRoles D A (checkFunctionalities K) fuel st
    (fun i => localStep (liftComp (digestQuery i (salts i) (hs i).history) (LocalSpec C)) >>=
      fun ds => afterDigests i ds ((f i ()).run' (hs i)))) _
  refine (executePhase_local_fallback prims D A (checkFunctionalities K) fuel st
    (fun i => liftComp (digestQuery i (salts i) (hs i).history) (LocalSpec C))
    (fun _ => C.terms.map (fun _ => (0 : HashOutput)))
    (fun i ds => afterDigests i ds ((f i ()).run' (hs i)))).trans ?_
  rw [digest_rows_honest]
  exact (sameRun_queryColumns prims
    (fun i T => honestDigestColumn D T salts (fun j => (hs j).history) i) C.terms).bind
      (fun ds => SameRun.refl prims _)

end ThresholdLeanXmssSecurity
end

/-! ## Digest common -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}

def digestColumnValues (D : C.Coalition) (T : C.Term) (d : HashOutput) : C.Party → HashOutput := fun i =>
  if i ∉ D.1 ∧ i ∈ C.holders T then d else 0

def commonDigestColumn (D : C.Coalition) (salts : C.Party → Shares C Bit)
    (history : C.Party → C.Term → List Bit) (salt hist : C.Term → List Bit) (T : C.Term) :
    OracleComp (LocalSpec C) (C.Party → HashOutput) :=
  if KnownTo D.1 T then Concrete.sequenceFin (honestDigestColumn D T salts history) else do
    let d ← liftComp (oneDigestQuery (C := C) (salt T) (hist T)) (LocalSpec C)
    pure (digestColumnValues D T d)

def digestColumnsRun (column : C.Term → OracleComp (LocalSpec C) (C.Party → HashOutput)) :
    List C.Term → OracleComp (LocalSpec C) (C.Party → List HashOutput)
  | [] => pure (fun _ => [])
  | T::Ts => do
    let head ← column T
    let tail ← digestColumnsRun column Ts
    pure (fun i => head i::tail i)

/-- Unknown terms with agreeing honest copies require only one real hash pair per term. -/
theorem digestColumns_common (prims : Primitives) (D : C.Coalition)
    (salts : C.Party → Shares C Bit) (history : C.Party → C.Term → List Bit)
    (salt hist : C.Term → List Bit)
    (hs : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → vector 256 (salts i T)=salt T)
    (hh : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → history i T=hist T)
    (ts : List C.Term) :
    SameRun prims (queryColumns (fun i T => honestDigestColumn D T salts history i) ts)
      (digestColumnsRun (commonDigestColumn D salts history salt hist) ts) := by
  induction ts with
  | nil => exact SameRun.refl prims _
  | cons T ts ih =>
    simp only [queryColumns,digestColumnsRun]
    have hc : SameRun prims (Concrete.sequenceFin (honestDigestColumn D T salts history))
        (commonDigestColumn D salts history salt hist T) := by
      unfold commonDigestColumn
      by_cases ht : KnownTo D.1 T
      · rw [if_pos ht]; exact SameRun.refl prims _
      · rw [if_neg ht]
        exact honestDigestColumn_common D prims T salts history (salt T) (hist T) (hs T ht) (hh T ht)
    exact hc.bind (fun head => ih.bind (fun tail => SameRun.refl prims (pure (fun i => head i::tail i))))

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The complete actual digest phase exposes exactly one common unknown digest per term;
its recipient messages, rushing reply, and adaptive continuation are preserved. -/
theorem executePhase_digestCommon (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (salts : C.Party → Shares C Bit)
    (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (salt hist : C.Term → List Bit)
    (hsalt : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → vector 256 (salts i T)=salt T)
    (hhist : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → (hs i).history T=hist T) :
    SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) fuel st
        (fun i => (compareDigests (localContext i) (salts i) >>= f i).run' (hs i)))
      (do
        let ds ← digestColumnsRun (commonDigestColumn D salts (fun j => (hs j).history) salt hist) C.terms
        executePhase localRoles D A (checkFunctionalities K) fuel st
          (fun i => afterDigests i (ds i) ((f i ()).run' (hs i)))) := by
  refine (executePhase_digestColumns prims K D A fuel st salts hs f).trans ?_
  exact (digestColumns_common prims D salts (fun j => (hs j).history) salt hist hsalt hhist C.terms).bind
    (fun ds => SameRun.refl prims _)

end ThresholdLeanXmssSecurity
end

/-! ## Coordinate -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {I R α : Type} [Fintype I] [DecidableEq I] [Fintype R] [Nonempty R]
  [SampleableType R] [SampleableType (I → R)]

/-- A single coordinate of a uniform table can be resampled independently of its other entries. -/
theorem sameRun_uniform_coordinate (prims : Primitives) (i : I)
    (k : (I → R) → OracleComp (LocalSpec C) α) :
    SameRun prims
      (do
        let table ← liftComp ($ᵗ (I → R)) (LocalSpec C)
        let value ← liftComp ($ᵗ R) (LocalSpec C)
        k (Function.update table i value))
      (do
        let table ← liftComp ($ᵗ (I → R)) (LocalSpec C)
        k table) := by
  refine (sameRun_swap prims (liftComp ($ᵗ (I → R)) (LocalSpec C))
    (liftComp ($ᵗ R) (LocalSpec C)) (fun table value => k (Function.update table i value))).trans ?_
  have h : SameRun (C := C) prims
      (do
        let value ← liftComp ($ᵗ R) (LocalSpec C)
        let table ← liftComp ($ᵗ (I → R)) (LocalSpec C)
        pure (Function.update table i value))
      (liftComp ($ᵗ (I → R)) (LocalSpec C)) := by
    simpa only [liftComp_bind,liftComp_pure] using sameRun_liftComp_of_evalDist (C := C) prims _ _
      (evalDist_uniformSample_bind_update (R := R) i)
  have hb := h.bind (fun table => SameRun.refl prims (k table))
  simpa only [bind_assoc,pure_bind] using hb

end ThresholdLeanXmssSecurity
end

/-! ## Salt coordinate -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee}

lemma vector_extend_ofFn {R : Type} [Zero R] (n : ℕ) (v : Fin n → R) :
    vector n (fun g => if h : g < n then v ⟨g,h⟩ else 0)=List.ofFn v := by
  apply List.ext_getElem
  · simp [vector]
  · intro k h₁ h₂
    have hk : k < n := by simpa [vector] using h₁
    simp [vector,hk]

/-- Every honest holder of an unknown term receives the same independent 256-bit salt. -/
theorem randFinish_unknown_salt (D : C.Coalition) (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin 256 → Bit)
    (pairs : C.Pair → Fin 256 → Bit) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (ht : i ∈ C.holders T) (hu : ¬KnownTo D.1 T) :
    (randFinish D 256 known knownPairs fresh pairs i).map (fun w => vector 256 (w.1 T)) =
      some (List.ofFn (fresh T)) := by
  simp only [randFinish,if_neg hi,Option.map_some,if_pos ht,if_neg hu]
  rw [vector_extend_ofFn]

/-- Resampling one unknown salt changes no known salt, and changes no other honest term. -/
theorem randFinish_update_salt (D : C.Coalition) (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin 256 → Bit)
    (pairs : C.Pair → Fin 256 → Bit) (T U : C.Term) (u : Fin 256 → Bit)
    (hU : U ≠ T ∨ KnownTo D.1 U) (i : C.Party) :
    (randFinish D 256 known knownPairs (Function.update fresh T u) pairs i).map (fun w => w.1 U) =
      (randFinish D 256 known knownPairs fresh pairs i).map (fun w => w.1 U) := by
  unfold randFinish
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi,Option.map_none]
  · simp only [if_neg hi,Option.map_some]
    by_cases hu : i ∈ C.holders U
    · simp only [if_pos hu]
      rcases hU with hne | hknown
      · simp only [Function.update_of_ne hne]
      · simp only [if_pos hknown]
    · simp only [if_neg hu]

end ThresholdLeanXmssSecurity
end

/-! ## Mask translation -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma randShares_conv (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (i : C.Party) (g : ℕ) :
    conv K (localContext i) (randShares D 2 known w i) g =
      conv K (localContext i) (multBase D 2 known w) g := by
  apply conv_congr
  intro T ht
  simp [randShares,multBase,ht]

lemma randShares_isShamir (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (g : ℕ) :
    IsShamir K (fun i => conv K (localContext i) (randShares D 2 known w i) g)
      (∑ T,multBase D 2 known w T g) := by
  letI : CharP E 2 := charP_two
  exact (isShamir_conv (K := K) (multBase D 2 known w) g).congr
    (fun i => (randShares_conv K D known w i g).symm) rfl

def maskTableEquiv (r : E) (delta : MaskTable C E) : MaskTable C E ≃ MaskTable C E :=
  Equiv.addRight (fun T g => r/(1+r)*delta T g)

lemma maskTableEquiv_apply (r : E) (delta w : MaskTable C E) (T : C.Term) (g : Fin 2) :
    maskTableEquiv r delta w T g=w T g+r/(1+r)*delta T g := rfl

lemma multBase_maskTableEquiv (D : C.Coalition) (known : Shares C E) (w delta : MaskTable C E)
    (r : E) (hd : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0) (T : C.Term) (g : Fin 2) :
    multBase D 2 known (maskTableEquiv r delta w) T g =
      multBase D 2 known w T g+r/(1+r)*delta T g := by
  by_cases ht : KnownTo D.1 T
  · simp [multBase,ht,hd T ht]
  · simp [multBase,ht,g.isLt,maskTableEquiv_apply]

/-- The concrete raw-mask bijection shifts every honest Shamir share by its hidden coefficient difference. -/
theorem randShares_maskTableEquiv (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w delta : MaskTable C E) (r : E) (hd : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0)
    (i : C.Party) (g : Fin 2) :
    conv K (localContext i) (randShares D 2 known (maskTableEquiv r delta w) i) g =
      conv K (localContext i) (randShares D 2 known w i) g+
        r/(1+r)*conv K (localContext i) (fun T _ => delta T g) 0 := by
  rw [randShares_conv,randShares_conv]
  simp only [conv,multBase_maskTableEquiv D known w delta r hd,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  ring

lemma maskValue_maskTableEquiv (D : C.Coalition) (known : Shares C E)
    (w delta : MaskTable C E) (r : E) (hd : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0) (g : Fin 2) :
    (∑ T,multBase D 2 known (maskTableEquiv r delta w) T g) =
      (∑ T,multBase D 2 known w T g)+r/(1+r)*(∑ T,delta T g) := by
  simp only [multBase_maskTableEquiv D known w delta r hd,Finset.sum_add_distrib,Finset.mul_sum]

/-- The same concrete bijection leaves every corrupt evaluation unchanged. -/
theorem randShares_maskTableEquiv_corrupt (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w delta : MaskTable C E) (r : E) (hd : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0)
    (i : C.Party) (hi : i ∈ D.1) (g : Fin 2) :
    conv K (localContext i) (randShares D 2 known (maskTableEquiv r delta w) i) g =
      conv K (localContext i) (randShares D 2 known w i) g := by
  rw [randShares_maskTableEquiv K D known w delta r hd]
  rw [conv_hidden_zero K D (fun T _ => delta T g) (fun T ht _ => hd T ht g) i hi 0,mul_zero,add_zero]

end ThresholdLeanXmssSecurity
end

/-! ## Mask totals -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset Polynomial
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def maskValue (D : C.Coalition) (known : Shares C E) (w : MaskTable C E) (g : ℕ) : E :=
  ∑ T,multBase D 2 known w T g

def maskShare (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (g : ℕ) (i : C.Party) : E :=
  conv K (localContext i) (randShares D 2 known w i) g

lemma maskedTotal_zero (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (A B : C.Party → E) :
    extendTotal K D (maskedInputs K D known w A B) 0 =
      ∑ i ∈ univ.filter (· ∉ D.1),lagrangeAll K i*(maskShare K D known w 0 i*maskShare K D known w 1 i) := by
  unfold extendTotal
  apply Finset.sum_congr rfl
  intro i hi
  have hiD := (mem_filter.mp hi).2
  simp [maskedInputs,hiD,maskedProducts,productShare,mulSh,localContext,maskShare]

lemma maskedTotal_one (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (A B : C.Party → E) :
    extendTotal K D (maskedInputs K D known w A B) 1 =
      ∑ i ∈ univ.filter (· ∉ D.1),lagrangeAll K i*
        ((maskShare K D known w 0 i+A i)*(maskShare K D known w 1 i+B i)) := by
  unfold extendTotal
  apply Finset.sum_congr rfl
  intro i hi
  have hiD := (mem_filter.mp hi).2
  simp [maskedInputs,hiD,maskedProducts,productShare,mulSh,localContext,maskShare]

lemma honest_shamir_product_difference (K : Constants C E) (D : C.Coalition)
    {U V U' V' : C.Party → E} {u v u' v' : E}
    (hU : IsShamir K U u) (hV : IsShamir K V v)
    (hU' : IsShamir K U' u') (hV' : IsShamir K V' v')
    (hcU : ∀ i ∈ D.1,U i=U' i) (hcV : ∀ i ∈ D.1,V i=V' i) :
    (∑ i ∈ univ.filter (· ∉ D.1),lagrangeAll K i*(U i*V i))-
      (∑ i ∈ univ.filter (· ∉ D.1),lagrangeAll K i*(U' i*V' i))=u*v-u'*v' := by
  letI : CharP E 2 := charP_two
  rw [honest_sum_sub D _ _ (by intro i hi; rw [hcU i hi,hcV i hi])]
  rw [sum_lagrangeAll_shamir K hU hV,sum_lagrangeAll_shamir K hU' hV']

/-- The two actual masked multiplication totals change by the corresponding true products.
This keeps the corrupt additive attack identical in the two coupled runs. -/
theorem maskedTotal_difference (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w w' : MaskTable C E) (A B A' B' : C.Party → E) (a b a' b' : E)
    (hA : IsShamir K A a) (hB : IsShamir K B b)
    (hA' : IsShamir K A' a') (hB' : IsShamir K B' b')
    (hWA : ∀ i ∈ D.1,maskShare K D known w 0 i=maskShare K D known w' 0 i)
    (hWB : ∀ i ∈ D.1,maskShare K D known w 1 i=maskShare K D known w' 1 i)
    (hCA : ∀ i ∈ D.1,A i=A' i) (hCB : ∀ i ∈ D.1,B i=B' i) :
    (extendTotal K D (maskedInputs K D known w A B) 0-
      extendTotal K D (maskedInputs K D known w' A' B') 0=
        maskValue D known w 0*maskValue D known w 1-maskValue D known w' 0*maskValue D known w' 1) ∧
    (extendTotal K D (maskedInputs K D known w A B) 1-
      extendTotal K D (maskedInputs K D known w' A' B') 1=
        (maskValue D known w 0+a)*(maskValue D known w 1+b)-
          (maskValue D known w' 0+a')*(maskValue D known w' 1+b')) := by
  have hW0 := randShares_isShamir K D known w 0
  have hW1 := randShares_isShamir K D known w 1
  have hW0' := randShares_isShamir K D known w' 0
  have hW1' := randShares_isShamir K D known w' 1
  constructor
  · rw [maskedTotal_zero,maskedTotal_zero]
    exact honest_shamir_product_difference K D hW0 hW1 hW0' hW1' hWA hWB
  · rw [maskedTotal_one,maskedTotal_one]
    exact honest_shamir_product_difference K D (hW0.add hA) (hW1.add hB) (hW0'.add hA') (hW1'.add hB')
      (by intro i hi; rw [hWA i hi,hCA i hi]) (by intro i hi; rw [hWB i hi,hCB i hi])

end ThresholdLeanXmssSecurity
end

/-! ## Output conv -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- A translated actual multiplication table produces the prescribed difference in every
received Shamir conversion, including adversarially chosen known terms and offsets. -/
theorem multFinish_conv_translate (K : Constants C E) (D : C.Coalition) (width : ℕ)
    (result result' : ℕ → E) (known delta : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (fresh : C.Term → Fin width → E)
    (hknown : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0)
    (hsum : ∀ g < width,∑ T,delta T g=result g-result' g)
    (i : C.Party) (hi : i ∉ D.1) (hr : i ∈ receivers) (g : ℕ) (hg : g < width) :
    conv K (localContext i)
        ((multFinish D width (filler K .peer) result known offset receivers fresh i).getD (fun _ _ => 0)) g -
      conv K (localContext i)
        ((multFinish D width (filler K .peer) result' known offset receivers
          (fun T k => fresh T k-delta T k) i).getD (fun _ _ => 0)) g =
      conv K (localContext i) delta g := by
  rw [multFinish_translate D width (filler K .peer) result result' known delta offset receivers fresh hknown hsum]
  have hrec : ¬(i ∈ D.1 ∨ i ∉ receivers) := by simp [hi,hr]
  simp only [addSharedOutput,multFinish,if_neg hrec,Option.map_some,Option.getD_some]
  simp only [conv,localContext,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have ht : i ∈ C.holders T := (mem_filter.mp hT).2
  simp only [ht,hg,and_self,if_true]
  ring

end ThresholdLeanXmssSecurity
end

/-! ## Final bijection -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def maskedResult (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (attack : ℕ → E) (w : MaskTable C E) (A B : C.Party → E) (g : ℕ) : E :=
  extendTotal K D (maskedInputs K D known w A B) g+attack g

def maskedResultDelta (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (attack : ℕ → E) (r : E) (delta w : MaskTable C E) (A B A' B' : C.Party → E) : ℕ → E :=
  fun g => maskedResult K D known attack w A B g-
    maskedResult K D known attack (maskTableEquiv r delta w) A' B' g

/-- The actual functionality totals satisfy precisely the scalar constraint required for the
last opening. The adversary's additive attack cancels without any restriction on it. -/
theorem maskedResultDelta_compatible (K : Constants C E) (D : C.Coalition)
    (known : Shares C E) (attack : ℕ → E) (r : E) (delta w : MaskTable C E)
    (A B A' B' : C.Party → E) (a b a' b' d d' : E) (deltaD : C.Term → E)
    (hr : 1+r ≠ 0) (hknown : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0)
    (hA : IsShamir K A a) (hB : IsShamir K B b)
    (hA' : IsShamir K A' a') (hB' : IsShamir K B' b')
    (hCA : ∀ i ∈ D.1,A i=A' i) (hCB : ∀ i ∈ D.1,B i=B' i)
    (hda : ∑ T,delta T 0=a-a') (hdb : ∑ T,delta T 1=b-b')
    (hdd : ∑ T,deltaD T=d-d') (herr : d-a*b=d'-a'*b') :
    (1+r)*maskedResultDelta K D known attack r delta w A B A' B' 0+
      r*(∑ T,deltaD T)+r*(1+r)*maskedResultDelta K D known attack r delta w A B A' B' 1=0 := by
  have ht := maskedTotal_difference K D known w (maskTableEquiv r delta w) A B A' B' a b a' b'
    hA hB hA' hB'
    (fun i hi => (randShares_maskTableEquiv_corrupt K D known w delta r hknown i hi 0).symm)
    (fun i hi => (randShares_maskTableEquiv_corrupt K D known w delta r hknown i hi 1).symm)
    hCA hCB
  have hw0 : maskValue D known (maskTableEquiv r delta w) 0=
      maskValue D known w 0+r/(1+r)*(a-a') := by
    simpa [maskValue,hda] using maskValue_maskTableEquiv D known w delta r hknown 0
  have hw1 : maskValue D known (maskTableEquiv r delta w) 1=
      maskValue D known w 1+r/(1+r)*(b-b') := by
    simpa [maskValue,hdb] using maskValue_maskTableEquiv D known w delta r hknown 1
  have hc := finalOutputDelta_compatible a b a' b' (maskValue D known w 0)
    (maskValue D known w 1) d d' 0 0 r hr herr
  dsimp only at hc
  simp only [add_zero] at hc
  simp only [maskedResultDelta,maskedResult,add_sub_add_right_eq_sub]
  rw [ht.1,ht.2,hw0,hw1,hdd]
  exact hc

def finalTableEquiv (T₀ : C.Term) (r : E) (deltaResult : ℕ → E)
    (deltaD : C.Term → E) : MaskTable C E ≃ MaskTable C E :=
  Equiv.addRight (fun T g => -finalOutputDelta T₀ r (deltaResult 0) (deltaResult 1) deltaD T g)

lemma finalTableEquiv_apply (T₀ : C.Term) (r : E) (deltaResult : ℕ → E)
    (deltaD : C.Term → E) (q : MaskTable C E) :
    finalTableEquiv T₀ r deltaResult deltaD q=
      fun T g => q T g-finalOutputDelta T₀ r (deltaResult 0) (deltaResult 1) deltaD T g := by
  funext T g
  simp [finalTableEquiv,sub_eq_add_neg]

/-- Both fresh output columns have exactly the change in total required by `F_mult`. -/
lemma finalTableEquiv_sum (T₀ : C.Term) (r : E) (result result' : ℕ → E)
    (deltaD : C.Term → E) (g : ℕ) (hg : g < 2) :
    ∑ T,finalOutputDelta T₀ r (result 0-result' 0) (result 1-result' 1) deltaD T g=
      result g-result' g := by
  have h := finalOutputDelta_sum T₀ r (result 0-result' 0) (result 1-result' 1) deltaD
  rcases (by omega : g=0 ∨ g=1) with rfl|rfl
  · exact h.1
  · exact h.2

end ThresholdLeanXmssSecurity
end

/-! ## Final vector -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def finalMaskVector (K : Constants C E) (D : C.Coalition) (known knownQ : Shares C E)
    (attack : ℕ → E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (r : E) (A B V : C.Party → E) (w q : MaskTable C E) (i : C.Party) : ℕ → E :=
  let output := (multFinish D 2 (filler K .peer) (maskedResult K D known attack w A B)
    knownQ offset receivers q i).getD (fun _ _ => 0)
  finalOpenVector (maskShare K D known w 0 i) (maskShare K D known w 1 i)
    (A i) (B i) (V i) (conv K (localContext i) output 0) (conv K (localContext i) output 1) r

/-- The concrete mask and output table bijections preserve the exact final vector sent by
an honest recipient. This also permits split known shares chosen by the adversary. -/
theorem finalMaskVector_bijection (K : Constants C E) (D : C.Coalition)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (T₀ : C.Term) (hT₀ : ¬ KnownTo D.1 T₀)
    (r : E) (delta : MaskTable C E) (deltaD : C.Term → E)
    (A B V A' B' V' : C.Party → E) (w q : MaskTable C E)
    (hr : 1+r ≠ 0) (hknown : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0)
    (hknownD : ∀ T,KnownTo D.1 T → deltaD T=0)
    (hcompat : (1+r)*maskedResultDelta K D known attack r delta w A B A' B' 0+
      r*(∑ T,deltaD T)+r*(1+r)*maskedResultDelta K D known attack r delta w A B A' B' 1=0)
    (i : C.Party) (hi : i ∉ D.1) (hrec : i ∈ receivers)
    (hlocalA : A i-A' i=conv K (localContext i) (fun T _ => delta T 0) 0)
    (hlocalB : B i-B' i=conv K (localContext i) (fun T _ => delta T 1) 0)
    (hlocalD : V i-V' i=conv K (localContext i) (fun T _ => deltaD T) 0) :
    finalMaskVector K D known knownQ attack offset receivers r A B V w q i=
      finalMaskVector K D known knownQ attack offset receivers r A' B' V'
        (maskTableEquiv r delta w)
        (finalTableEquiv T₀ r (maskedResultDelta K D known attack r delta w A B A' B') deltaD q) i := by
  let result := maskedResult K D known attack w A B
  let result' := maskedResult K D known attack (maskTableEquiv r delta w) A' B'
  let deltaQ := finalOutputDelta T₀ r (result 0-result' 0) (result 1-result' 1) deltaD
  have hdq : ∀ T,KnownTo D.1 T → ∀ g,deltaQ T g=0 :=
    finalOutputDelta_known D T₀ hT₀ r _ _ deltaD hknownD
  have hs : ∀ g < 2,∑ T,deltaQ T g=result g-result' g :=
    finalTableEquiv_sum T₀ r result result' deltaD
  have hq0 := multFinish_conv_translate K D 2 result result' knownQ deltaQ offset receivers q hdq hs i hi hrec 0 (by omega)
  have hq1 := multFinish_conv_translate K D 2 result result' knownQ deltaQ offset receivers q hdq hs i hi hrec 1 (by omega)
  have hwa : maskShare K D known (maskTableEquiv r delta w) 0 i=
      maskShare K D known w 0 i+r/(1+r)*(A i-A' i) := by
    simpa [maskShare,← hlocalA] using randShares_maskTableEquiv K D known w delta r hknown i 0
  have hwb : maskShare K D known (maskTableEquiv r delta w) 1 i=
      maskShare K D known w 1 i+r/(1+r)*(B i-B' i) := by
    simpa [maskShare,← hlocalB] using randShares_maskTableEquiv K D known w delta r hknown i 1
  dsimp only [finalMaskVector]
  rw [finalTableEquiv_apply,hwa,hwb]
  exact finalOpenVector_shift K T₀ i r (result 0-result' 0) (result 1-result' 1) deltaD hr hcompat
    _ _ _ _ _ _ _ _ _ _ _ _ hlocalD hq0 hq1

end ThresholdLeanXmssSecurity
end

/-! ## Final distribution -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia L R : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def finalMaskNetwork (K : Constants C E) (D : C.Coalition) (Adv : Adversary C E Ia L R)
    (F : Functionality C ((ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ))
      ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) L R)
    (fuel : ℕ) (st : Adv.State) (live : C.Party → Prop)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (r : E) (A B V : C.Party → E) (w q : MaskTable C E) :=
  executePhase localRoles D Adv F fuel st (fun i => if live i then
    finalOpenProgram K i (finalMaskVector K D known knownQ attack offset receivers r A B V w q i)
    else failure)

/-- After a common challenge, the triangular translation couples the complete last network
round pointwise, with the same adversary state and any pattern of honest aborts. -/
theorem finalMaskNetwork_bijection (K : Constants C E) (D : C.Coalition)
    (Adv : Adversary C E Ia L R)
    (F : Functionality C ((ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ))
      ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) L R)
    (fuel : ℕ) (st : Adv.State) (live : C.Party → Prop)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (T₀ : C.Term) (hT₀ : ¬ KnownTo D.1 T₀)
    (r : E) (delta : MaskTable C E) (deltaD : C.Term → E)
    (A B V A' B' V' : C.Party → E) (w q : MaskTable C E)
    (hr : 1+r ≠ 0) (hknown : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0)
    (hknownD : ∀ T,KnownTo D.1 T → deltaD T=0)
    (hcompat : (1+r)*maskedResultDelta K D known attack r delta w A B A' B' 0+
      r*(∑ T,deltaD T)+r*(1+r)*maskedResultDelta K D known attack r delta w A B A' B' 1=0)
    (hrec : ∀ i,i ∉ D.1 → live i → i ∈ receivers)
    (hlocalA : ∀ i,i ∉ D.1 → live i → A i-A' i=conv K (localContext i) (fun T _ => delta T 0) 0)
    (hlocalB : ∀ i,i ∉ D.1 → live i → B i-B' i=conv K (localContext i) (fun T _ => delta T 1) 0)
    (hlocalD : ∀ i,i ∉ D.1 → live i → V i-V' i=conv K (localContext i) (fun T _ => deltaD T) 0) :
    finalMaskNetwork K D Adv F fuel st live known knownQ attack offset receivers r A B V w q=
      finalMaskNetwork K D Adv F fuel st live known knownQ attack offset receivers r A' B' V'
        (maskTableEquiv r delta w)
        (finalTableEquiv T₀ r (maskedResultDelta K D known attack r delta w A B A' B') deltaD q) := by
  apply finalOpen_network_congr
  intro i hi hl
  exact finalMaskVector_bijection K D known knownQ attack offset receivers T₀ hT₀ r delta deltaD
    A B V A' B' V' w q hr hknown hknownD hcompat i hi (hrec i hi hl)
    (hlocalA i hi hl) (hlocalB i hi hl) (hlocalD i hi hl)

/-- The actual last-round distribution agrees for equal residuals once the challenge and
public transcript are fixed independently of the two hidden tables. -/
theorem finalMaskNetwork_sameRun (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (Adv : Adversary C E Ia L R)
    (F : Functionality C ((ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ))
      ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) L R)
    (fuel : ℕ) (st : Adv.State) (live : C.Party → Prop)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (T₀ : C.Term) (hT₀ : ¬ KnownTo D.1 T₀)
    (r : E) (delta : MaskTable C E) (deltaD : C.Term → E)
    (A B V A' B' V' : C.Party → E) (a b a' b' d d' : E)
    (hr : 1+r ≠ 0) (hknown : ∀ T,KnownTo D.1 T → ∀ g,delta T g=0)
    (hknownD : ∀ T,KnownTo D.1 T → deltaD T=0)
    (hA : IsShamir K A a) (hB : IsShamir K B b)
    (hA' : IsShamir K A' a') (hB' : IsShamir K B' b')
    (hCA : ∀ i ∈ D.1,A i=A' i) (hCB : ∀ i ∈ D.1,B i=B' i)
    (hda : ∑ T,delta T 0=a-a') (hdb : ∑ T,delta T 1=b-b')
    (hdd : ∑ T,deltaD T=d-d') (herr : d-a*b=d'-a'*b')
    (hrec : ∀ i,i ∉ D.1 → live i → i ∈ receivers)
    (hlocalA : ∀ i,i ∉ D.1 → live i → A i-A' i=conv K (localContext i) (fun T _ => delta T 0) 0)
    (hlocalB : ∀ i,i ∉ D.1 → live i → B i-B' i=conv K (localContext i) (fun T _ => delta T 1) 0)
    (hlocalD : ∀ i,i ∉ D.1 → live i → V i-V' i=conv K (localContext i) (fun T _ => deltaD T) 0) :
    SameRun prims
      (do let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          finalMaskNetwork K D Adv F fuel st live known knownQ attack offset receivers r A B V w q)
      (do let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          finalMaskNetwork K D Adv F fuel st live known knownQ attack offset receivers r A' B' V' w q) := by
  let e := maskTableEquiv r delta
  let f := fun w => finalTableEquiv T₀ r (maskedResultDelta K D known attack r delta w A B A' B') deltaD
  let k := finalMaskNetwork K D Adv F fuel st live known knownQ attack offset receivers r A' B' V'
  refine SameRun.trans (ob := (do
    let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
    let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
    k (e w) (f w q))) ?_ (sameRun_uniform_two_equivs prims e f k)
  apply SameRun.bind_right
  intro w
  apply SameRun.bind_right
  intro q
  apply SameRun.of_eq
  exact finalMaskNetwork_bijection K D Adv F fuel st live known knownQ attack offset receivers T₀ hT₀
    r delta deltaD A B V A' B' V' w q hr hknown hknownD
    (maskedResultDelta_compatible K D known attack r delta w A B A' B' a b a' b' d d' deltaD
      hr hknown hA hB hA' hB' hCA hCB hda hdb hdd herr) hrec hlocalA hlocalB hlocalD

end ThresholdLeanXmssSecurity
end

/-! ## Digest uncached -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

def DigestSaltsCovered (cache : HashCache C) (seen : Finset (List Bit)) : Prop :=
  ∀ salt h,cache (.digest salt h) ≠ none → salt ∈ seen

lemma history_preserves_digestSalts (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hs : DigestSaltsCovered cache seen)
    (history : List Bit) (p : HashOutput × HashCache C)
    (hp : p ∈ support ((hashAnswer prims (.history history)).run cache)) :
    DigestSaltsCovered p.2 seen := by
  intro salt h hd
  have hn : ¬ IsFixed (Query.history (C := C) history) := by rintro ⟨_,he,_⟩; cases he
  have he := support_hashQuery_entries prims hn cache p (by
    have he : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (hashQuery (.history history))=hashAnswer prims (.history history) :=
      (simulateQ_query _ _).trans (id_map _)
    rwa [he])
  rcases he (.digest salt h) hd with hc|he
  · exact hs salt h hc
  · cases he

def saltedDigestProgram (history : List Bit) (k : HashOutput → OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) α := do
  let salt ← liftComp ($ᵗ (Fin 256 → Bit)) (LocalSpec C)
  let d ← liftComp (oneDigestQuery (C := C) (List.ofFn salt) history) (LocalSpec C)
  k d

lemma simulate_oneDigestQuery (prims : Primitives) (salt history : List Bit) :
    simulateQ (localAnswer prims) (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C))=
      saltedDigestAnswer prims salt history := by
  simp only [oneDigestQuery,liftComp_bind,simulateQ_bind,simulateQ_localAnswer_hash,saltedDigestAnswer]

lemma saltedDigestProgram_run' (prims : Primitives) (cache : HashCache C)
    (history : List Bit) (k : HashOutput → OracleComp (LocalSpec C) α) :
    (simulateQ (localAnswer prims) (saltedDigestProgram history k)).run' cache=
      (do let salt ← $ᵗ (Fin 256 → Bit)
          (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
            simulateQ (localAnswer prims) (k d)).run' cache) := by
  simp only [saltedDigestProgram,simulateQ_bind,StateT.run'_eq,StateT.run_bind,
    run_liftComp_prob,bind_map_left,map_bind,simulate_oneDigestQuery]

lemma digestGhostGame_run' (prims : Primitives) (cache : HashCache C)
    (k : HashOutput → OracleComp (LocalSpec C) α) :
    (simulateQ (localAnswer prims) (liftComp ($ᵗ HashOutput) (LocalSpec C) >>= k)).run' cache=
      digestGhostGame prims cache k := by
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,run_liftComp_prob,bind_map_left,map_bind,digestGhostGame]

/-- The history need not be cached in advance. Unobserved prefetching removes that condition
without charging any history query or exposing its answer to the continuation. -/
theorem saltedDigestProgram_hide (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hs : DigestSaltsCovered cache seen)
    (history : List Bit) (k : HashOutput → OracleComp (LocalSpec C) α)
    (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : ∀ d,IsQueryBoundP (k d) charged q) :
    tvDist ((simulateQ (localAnswer prims) (saltedDigestProgram history k)).run' cache)
      ((simulateQ (localAnswer prims) (liftComp ($ᵗ HashOutput) (LocalSpec C) >>= k)).run' cache) ≤
      ((seen.card+q : ℕ) : ℝ)/2^256 := by
  let probe : OracleComp (LocalSpec C) HashOutput := liftComp (hashQuery (Query.history (C := C) history)) (LocalSpec C)
  let real := saltedDigestProgram history k
  let ghost := liftComp ($ᵗ HashOutput) (LocalSpec C) >>= k
  have hr := local_prefetch_output prims probe real cache
  have hg := local_prefetch_output prims probe ghost cache
  change tvDist ((simulateQ (localAnswer prims) real).run' cache)
    ((simulateQ (localAnswer prims) ghost).run' cache) ≤ _
  rw [tvDist,← hr,← hg]
  change tvDist ((simulateQ (localAnswer prims) (probe >>= fun _ => real)).run' cache)
    ((simulateQ (localAnswer prims) (probe >>= fun _ => ghost)).run' cache) ≤ _
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
  dsimp only [probe]
  rw [simulateQ_localAnswer_hash]
  change tvDist (((hashAnswer prims (.history history)).run cache) >>= fun p =>
      (simulateQ (localAnswer prims) real).run' p.2)
    (((hashAnswer prims (.history history)).run cache) >>= fun p =>
      (simulateQ (localAnswer prims) ghost).run' p.2) ≤ _
  apply tvDist_bind_left_le_const
  intro p hp
  have hn : ¬ IsFixed (Query.history (C := C) history) := by rintro ⟨_,he,_⟩; cases he
  have hh := hashAnswer_cached prims hn cache p hp
  have hc := history_preserves_digestSalts prims cache seen hs history p hp
  change tvDist ((simulateQ (localAnswer prims) (saltedDigestProgram history k)).run' p.2)
    ((simulateQ (localAnswer prims) (liftComp ($ᵗ HashOutput) (LocalSpec C) >>= k)).run' p.2) ≤ _
  rw [saltedDigestProgram_run',digestGhostGame_run']
  apply saltedDigest_hideP prims p.2 history p.1 hh seen _ k charged hproject q hq
  intro salt hnot
  by_contra hne
  exact hnot (hc (List.ofFn salt) p.1 hne)

end ThresholdLeanXmssSecurity
end

/-! ## Digest coverage -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

lemma hashAnswer_digest_entries (prims : Primitives) (q : Query C) (cache : HashCache C)
    (p : HashOutput × HashCache C) (hp : p ∈ support ((hashAnswer prims q).run cache))
    (salt : List Bit) (h : HashOutput) (hd : p.2 (.digest salt h) ≠ none) :
    cache (.digest salt h) ≠ none ∨ q=.digest salt h := by
  by_cases hq : IsFixed q
  · obtain ⟨input,rfl,hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm,StateT.run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst p
    exact Or.inl hd
  · have he : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q)=
        hashAnswer prims q := (simulateQ_query _ _).trans (id_map _)
    have hs := support_hashQuery_entries prims hq cache p (by rwa [he]) (.digest salt h) hd
    exact hs.imp_right Eq.symm

lemma localAnswer_digest_covered (prims : Primitives) (cache : HashCache C)
    (l : List (List Bit)) (hc : ∀ salt h,cache (.digest salt h) ≠ none → salt ∈ l)
    (t : (LocalSpec C).Domain) (p : (LocalSpec C).Range t × HashCache C)
    (hp : p ∈ support ((localAnswer prims t).run cache)) :
    ∀ salt h,p.2 (.digest salt h) ≠ none → salt ∈ (digestSaltProjection t).toList ++ l := by
  rcases t with n|q|x
  · simp [localAnswer,unifFwdImpl] at hp
    obtain ⟨_,rfl⟩ := hp
    simpa only [digestSaltProjection,Option.toList_none,List.nil_append] using hc
  · intro salt h hd
    rcases hashAnswer_digest_entries prims q cache p hp salt h hd with hs|he
    · exact List.mem_append_right _ (hc salt h hs)
    · subst q
      simp [digestSaltProjection]
  · simp [localAnswer,prgAnswer] at hp
    obtain ⟨p,hp,rfl⟩ := hp
    intro salt h hd
    rcases hashAnswer_digest_entries prims (.streamKey x.2.1) cache p hp salt h hd with hs|he
    · exact List.mem_append_right _ (hc salt h hs)
    · cases he

/-- The salt trace covers every cached outer digest, including those introduced through
arbitrary adaptive local calls. Queries of other domains never enlarge this cover. -/
theorem projectQueries_digest_covered (prims : Primitives) (oa : OracleComp (LocalSpec C) α)
    (cache : HashCache C) (l : List (List Bit))
    (hc : ∀ salt h,cache (.digest salt h) ≠ none → salt ∈ l)
    (z : α × HashCache C × List (List Bit))
    (hz : z ∈ support ((simulateQ (projectQueries (localAnswer prims) digestSaltProjection) oa).run (cache,l))) :
    ∀ salt h,z.2.1 (.digest salt h) ≠ none → salt ∈ z.2.2 := by
  induction oa using OracleComp.inductionOn generalizing cache l z with
  | pure a =>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at hz
    subst z
    exact hc
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,projectQueries_run,
      bind_map_left,support_bind,Set.mem_iUnion,exists_prop] at hz
    obtain ⟨p,hp,hz⟩ := hz
    exact ih p.1 p.2 ((digestSaltProjection t).toList ++ l)
      (localAnswer_digest_covered prims cache l hc t p hp) z hz

lemma projectQueries_forget {ι σ β : Type} {S : OracleSpec ι}
    (impl : QueryImpl S (StateT σ ProbComp)) (project : ι → Option β)
    (oa : OracleComp S α) (s : σ) (l : List β) :
    (fun z : α × σ × List β => (z.1,z.2.1)) <$>
      (simulateQ (projectQueries impl project) oa).run (s,l)=
      (simulateQ impl oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s l with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,projectQueries_run,bind_map_left,map_bind]
    apply bind_congr
    intro p
    exact ih p.1 p.2 ((project t).toList ++ l)

/-- A charged query bound supplies a finite cover for all digest salts in the resulting cache. -/
theorem localProgram_digest_covered (prims : Primitives) (oa : OracleComp (LocalSpec C) α)
    (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : IsQueryBoundP oa charged q) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (p : α × HashCache C) (hp : p ∈ support ((simulateQ (localAnswer prims) oa).run cache)) :
    ∃ seen',DigestSaltsCovered p.2 seen' ∧ seen'.card ≤ seen.card+q := by
  rw [← projectQueries_forget (localAnswer prims) digestSaltProjection oa cache seen.toList,support_map] at hp
  obtain ⟨z,hz,rfl⟩ := hp
  refine ⟨z.2.2.toFinset,?_,?_⟩
  · intro salt h hd
    exact List.mem_toFinset.mpr (projectQueries_digest_covered prims oa cache seen.toList
      (fun salt h hh => Finset.mem_toList.mpr (hc salt h hh)) z hz salt h hd)
  · have hb := projectQueries_length (localAnswer prims) charged digestSaltProjection hproject hq cache seen.toList hz
    exact (List.toFinset_card_le z.2.2).trans (by simpa using hb)

end ThresholdLeanXmssSecurity
end

/-! ## Digest prefix -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α β : Type}

/-- The hiding bound includes every earlier adaptive query in the same execution. -/
theorem saltedDigestProgram_hide_after (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hs : DigestSaltsCovered cache seen)
    (before : OracleComp (LocalSpec C) β) (history : β → List Bit)
    (k : β → HashOutput → OracleComp (LocalSpec C) α)
    (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (p q : ℕ) (hp : IsQueryBoundP before charged p) (hq : ∀ b d,IsQueryBoundP (k b d) charged q) :
    tvDist ((simulateQ (localAnswer prims) (before >>= fun b => saltedDigestProgram (history b) (k b))).run' cache)
      ((simulateQ (localAnswer prims) (before >>= fun b =>
        liftComp ($ᵗ HashOutput) (LocalSpec C) >>= k b)).run' cache) ≤
      ((seen.card+p+q : ℕ) : ℝ)/2^256 := by
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
  apply tvDist_bind_left_le_const
  intro z hz
  obtain ⟨seen',hc,hcard⟩ := localProgram_digest_covered prims before charged hproject p hp cache seen hs z hz
  have hb := saltedDigestProgram_hide prims z.2 seen' hc (history z.1) (k z.1) charged hproject q (hq z.1)
  refine hb.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.add_le_add_right hcard q

end ThresholdLeanXmssSecurity
end

/-! ## Digest list -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

def DigestQuery (t : (LocalSpec C).Domain) : Prop := (digestSaltProjection t).isSome

lemma prob_lift_no_digest (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) DigestQuery 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind,liftComp_query]
    simp only [OracleQuery.input_query,OracleQuery.cont_query,id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inl t)) >>= fun u =>
      liftComp (k u) (LocalSpec C)) DigestQuery 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [DigestQuery,digestSaltProjection]),fun u => by
      simpa [DigestQuery,digestSaltProjection] using ih u⟩

lemma oneDigestQuery_digestBound (salt history : List Bit) :
    IsQueryBoundP (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)) DigestQuery 1 := by
  unfold oneDigestQuery
  rw [liftComp_bind]
  apply isQueryBoundP_bind (n := 0) (m := 1)
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inr (.inl (.history history))))) DigestQuery 0
    rw [isQueryBoundP_query_iff]
    simp [DigestQuery,digestSaltProjection]
  · intro h _
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inr (.inl (.digest salt h))))) DigestQuery 1
    rw [isQueryBoundP_query_iff]
    simp

set_option maxRecDepth 4096 in
lemma saltedDigestProgram_digestBound (history : List Bit)
    (k : HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ d,IsQueryBoundP (k d) DigestQuery q) :
    IsQueryBoundP (saltedDigestProgram history k) DigestQuery (1+q) := by
  unfold saltedDigestProgram
  simpa only [Nat.zero_add] using isQueryBoundP_bind (prob_lift_no_digest ($ᵗ (Fin 256 → Bit))) (fun salt _ =>
    isQueryBoundP_bind (oneDigestQuery_digestBound (List.ofFn salt) history) fun d _ => hq d)

def saltedDigestList : List (List Bit) → (List HashOutput → OracleComp (LocalSpec C) α) → OracleComp (LocalSpec C) α
  | [], k => k []
  | h::hs, k => saltedDigestProgram h fun d => saltedDigestList hs fun ds => k (d::ds)

def ghostDigestList : List (List Bit) → (List HashOutput → OracleComp (LocalSpec C) α) → OracleComp (LocalSpec C) α
  | [], k => k []
  | _::hs, k => liftComp ($ᵗ HashOutput) (LocalSpec C) >>= fun d => ghostDigestList hs fun ds => k (d::ds)

set_option maxRecDepth 4096 in
lemma saltedDigestList_digestBound (histories : List (List Bit))
    (k : List HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ ds,IsQueryBoundP (k ds) DigestQuery q) :
    IsQueryBoundP (saltedDigestList histories k) DigestQuery (histories.length+q) := by
  induction histories generalizing k with
  | nil => simpa only [saltedDigestList,List.length_nil,Nat.zero_add] using hq []
  | cons h hs ih =>
    simpa only [saltedDigestList,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      saltedDigestProgram_digestBound h (fun d => saltedDigestList hs fun ds => k (d::ds)) (hs.length+q)
        (fun d => ih (fun ds => k (d::ds)) (fun ds => hq (d::ds)))

/-- All independently salted commitments can be replaced by fresh digest tokens. The whole
remaining protocol and distinguisher may be in `k`; only its outer digest calls are charged. -/
theorem saltedDigestList_hide (prims : Primitives) (histories : List (List Bit))
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : List HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ ds,IsQueryBoundP (k ds) DigestQuery q) :
    tvDist ((simulateQ (localAnswer prims) (saltedDigestList histories k)).run' cache)
      ((simulateQ (localAnswer prims) (ghostDigestList histories k)).run' cache) ≤
      ((histories.length*(seen.card+q+histories.length) : ℕ) : ℝ)/2^256 := by
  induction histories generalizing k with
  | nil => simp [saltedDigestList,ghostDigestList]
  | cons h hs ih =>
    let next := fun d => saltedDigestList hs fun ds => k (d::ds)
    let ghost := liftComp ($ᵗ HashOutput) (LocalSpec C) >>= next
    have hb := saltedDigestProgram_hide prims cache seen hc h next DigestQuery
      (fun _ ht => ht) (hs.length+q)
      (fun d => saltedDigestList_digestBound hs (fun ds => k (d::ds)) q (fun ds => hq (d::ds)))
    have ht : tvDist ((simulateQ (localAnswer prims) ghost).run' cache)
        ((simulateQ (localAnswer prims) (ghostDigestList (h::hs) k)).run' cache) ≤
        ((hs.length*(seen.card+q+hs.length) : ℕ) : ℝ)/2^256 := by
      simp only [ghost,ghostDigestList,simulateQ_bind,StateT.run'_eq,StateT.run_bind,
        run_liftComp_prob,bind_map_left,map_bind]
      apply tvDist_bind_left_le_const'
      intro d
      exact ih (fun ds => k (d::ds)) (fun ds => hq (d::ds))
    have htri := tvDist_triangle
      ((simulateQ (localAnswer prims) (saltedDigestProgram h next)).run' cache)
      ((simulateQ (localAnswer prims) ghost).run' cache)
      ((simulateQ (localAnswer prims) (ghostDigestList (h::hs) k)).run' cache)
    refine htri.trans ((add_le_add hb ht).trans ?_)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simp only [List.length_cons]
    push_cast
    nlinarith [show (0 : ℝ) ≤ hs.length by positivity]

end ThresholdLeanXmssSecurity
end

/-! ## Digest table -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

def tableDigests (hist : C.Term → List Bit) (table : C.Term → Fin 256 → Bit) :
    List C.Term → (List HashOutput → OracleComp (LocalSpec C) α) → OracleComp (LocalSpec C) α
  | [], k => k []
  | T::Ts, k => do
    let d ← liftComp (oneDigestQuery (C := C) (List.ofFn (table T)) (hist T)) (LocalSpec C)
    tableDigests hist table Ts fun ds => k (d::ds)

lemma tableDigests_congr (hist : C.Term → List Bit) (table table' : C.Term → Fin 256 → Bit)
    (Ts : List C.Term) (ht : ∀ T ∈ Ts,table T=table' T)
    (k : List HashOutput → OracleComp (LocalSpec C) α) :
    tableDigests hist table Ts k=tableDigests hist table' Ts k := by
  induction Ts generalizing k with
  | nil => rfl
  | cons T Ts ih =>
    simp only [tableDigests,ht T (by simp)]
    apply bind_congr
    intro d
    exact ih (fun U hU => ht U (by simp [hU])) _

/-- A uniform salt table gives independent fresh salts along any list of distinct terms.
The proof resamples coordinates, so no enumeration or size assumption on the committee is needed. -/
theorem tableDigests_fresh (prims : Primitives) (hist : C.Term → List Bit)
    (Ts : List C.Term) (hTs : Ts.Nodup)
    (k : List HashOutput → OracleComp (LocalSpec C) α) :
    SameRun prims
      (do let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
          tableDigests hist table Ts k)
      (saltedDigestList (Ts.map hist) k) := by
  induction Ts generalizing k with
  | nil =>
    simp only [tableDigests,List.map_nil,saltedDigestList]
    exact sameRun_discard_sample prims _
  | cons T Ts ih =>
    have hn := List.nodup_cons.mp hTs
    let draw := saltedDigestProgram (C := C) (hist T) (fun d => pure d)
    let rest := fun table d => tableDigests hist table Ts fun ds => k (d::ds)
    refine (sameRun_uniform_coordinate prims T (fun table => tableDigests hist table (T::Ts) k)).symm.trans ?_
    have hupdate : ∀ table : C.Term → Fin 256 → Bit,∀ salt,
        tableDigests hist (Function.update table T salt) (T::Ts) k=
          (do let d ← liftComp (oneDigestQuery (C := C) (List.ofFn salt) (hist T)) (LocalSpec C)
              rest table d) := by
      intro table salt
      simp only [tableDigests,Function.update_self]
      apply bind_congr
      intro d
      apply tableDigests_congr
      intro U hU
      have hne : U ≠ T := by intro he; subst U; exact hn.1 hU
      exact Function.update_of_ne hne _ _
    refine SameRun.trans (ob := (do
      let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
      draw >>= rest table)) (SameRun.of_eq ?_) ?_
    · simp only [draw,saltedDigestProgram,bind_assoc,pure_bind]
      simp_rw [hupdate]
    have hswap := sameRun_swap prims (liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)) draw rest
    refine hswap.trans ?_
    simp only [draw,rest,List.map_cons,saltedDigestList,saltedDigestProgram,bind_assoc,pure_bind]
    apply SameRun.bind_right
    intro salt
    apply SameRun.bind_right
    intro d
    exact ih hn.2 (fun ds => k (d::ds))

/-- The hiding theorem applies directly to the uniform table used by the actual salt gadget. -/
theorem tableDigests_hide (prims : Primitives) (hist : C.Term → List Bit)
    (Ts : List C.Term) (hTs : Ts.Nodup) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : List HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ ds,IsQueryBoundP (k ds) DigestQuery q) :
    tvDist ((simulateQ (localAnswer prims) (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        tableDigests hist table Ts k)).run' cache)
      ((simulateQ (localAnswer prims) (ghostDigestList (Ts.map hist) k)).run' cache) ≤
      ((Ts.length*(seen.card+q+Ts.length) : ℕ) : ℝ)/2^256 := by
  have he := tableDigests_fresh prims hist Ts hTs k cache
  have he' := congrArg (fun d => Prod.fst <$> d) he
  simp only [← evalDist_map,← StateT.run'_eq] at he'
  rw [tvDist,he']
  simpa only [tvDist,List.length_map] using saltedDigestList_hide prims (Ts.map hist) cache seen hc k q hq

end ThresholdLeanXmssSecurity
end

/-! ## Digest mixed -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

abbrev DigestColumn (C : Committee) := C.Party → HashOutput

def mixedDigests (D : C.Coalition) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hist : C.Term → List Bit) :
    List C.Term → (List (DigestColumn C) → OracleComp (LocalSpec C) α) → OracleComp (LocalSpec C) α
  | [], k => k []
  | T::Ts, k => if KnownTo D.1 T then known T >>= fun col => mixedDigests D known hist Ts fun cs => k (col::cs)
    else saltedDigestProgram (hist T) fun d => mixedDigests D known hist Ts fun cs => k (digestColumnValues D T d::cs)

def mixedGhostDigests (D : C.Coalition) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) :
    List C.Term → (List (DigestColumn C) → OracleComp (LocalSpec C) α) → OracleComp (LocalSpec C) α
  | [], k => k []
  | T::Ts, k => if KnownTo D.1 T then known T >>= fun col => mixedGhostDigests D known Ts fun cs => k (col::cs)
    else liftComp ($ᵗ HashOutput) (LocalSpec C) >>= fun d => mixedGhostDigests D known Ts fun cs => k (digestColumnValues D T d::cs)

set_option maxRecDepth 4096 in
lemma mixedDigests_digestBound (D : C.Coalition) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hist : C.Term → List Bit) (p : ℕ) (hknown : ∀ T,KnownTo D.1 T → IsQueryBoundP (known T) DigestQuery p)
    (Ts : List C.Term) (k : List (DigestColumn C) → OracleComp (LocalSpec C) α)
    (q : ℕ) (hq : ∀ cs,IsQueryBoundP (k cs) DigestQuery q) :
    IsQueryBoundP (mixedDigests D known hist Ts k) DigestQuery ((p+1)*Ts.length+q) := by
  induction Ts generalizing k with
  | nil => simpa only [mixedDigests,List.length_nil,Nat.mul_zero,Nat.zero_add] using hq []
  | cons T Ts ih =>
    simp only [mixedDigests]
    by_cases hT : KnownTo D.1 T
    · rw [if_pos hT]
      apply (isQueryBoundP_bind (hknown T hT) (fun col _ => ih (fun cs => k (col::cs)) (fun cs => hq (col::cs)))).mono
      simp only [List.length_cons,Nat.mul_succ]
      omega
    · rw [if_neg hT]
      apply (saltedDigestProgram_digestBound (hist T) _ ((p+1)*Ts.length+q)
        (fun d => ih (fun cs => k (digestColumnValues D T d::cs)) (fun cs => hq _))).mono
      simp only [List.length_cons,Nat.mul_succ]
      omega

/-- Known-term digest columns remain actual oracle calls. All hidden-term columns are
replaced by common fresh tokens, even with arbitrary adaptive known-column programs. -/
theorem mixedDigests_hide (prims : Primitives) (D : C.Coalition)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) (hist : C.Term → List Bit)
    (p : ℕ) (hknown : ∀ T,KnownTo D.1 T → IsQueryBoundP (known T) DigestQuery p)
    (Ts : List C.Term) (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : List (DigestColumn C) → OracleComp (LocalSpec C) α)
    (q : ℕ) (hq : ∀ cs,IsQueryBoundP (k cs) DigestQuery q) :
    tvDist ((simulateQ (localAnswer prims) (mixedDigests D known hist Ts k)).run' cache)
      ((simulateQ (localAnswer prims) (mixedGhostDigests D known Ts k)).run' cache) ≤
      ((Ts.length*(seen.card+q+(p+1)*Ts.length) : ℕ) : ℝ)/2^256 := by
  induction Ts generalizing cache seen k with
  | nil => simp [mixedDigests,mixedGhostDigests]
  | cons T Ts ih =>
    simp only [mixedDigests,mixedGhostDigests]
    by_cases hT : KnownTo D.1 T
    · rw [if_pos hT,if_pos hT]
      simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
      apply tvDist_bind_left_le_const
      intro z hz
      obtain ⟨seen',hc',hcard⟩ := localProgram_digest_covered prims (known T) DigestQuery
        (fun _ ht => ht) p (hknown T hT) cache seen hc z hz
      refine (ih z.2 seen' hc' (fun cs => k (z.1::cs)) (fun cs => hq _)).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (show Ts.length*(seen'.card+q+(p+1)*Ts.length) ≤
        (T::Ts).length*(seen.card+q+(p+1)*(T::Ts).length) from calc
        _ ≤ Ts.length*(seen.card+p+q+(p+1)*Ts.length) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ _ := by simp only [List.length_cons]; nlinarith)
    · rw [if_neg hT,if_neg hT]
      let next := fun d => mixedDigests D known hist Ts fun cs => k (digestColumnValues D T d::cs)
      let ghost := liftComp ($ᵗ HashOutput) (LocalSpec C) >>= next
      have hb := saltedDigestProgram_hide prims cache seen hc (hist T) next DigestQuery
        (fun _ ht => ht) ((p+1)*Ts.length+q)
        (fun d => mixedDigests_digestBound D known hist p hknown Ts _ q (fun cs => hq _))
      have ht : tvDist ((simulateQ (localAnswer prims) ghost).run' cache)
          ((simulateQ (localAnswer prims) (liftComp ($ᵗ HashOutput) (LocalSpec C) >>= fun d =>
            mixedGhostDigests D known Ts fun cs => k (digestColumnValues D T d::cs))).run' cache) ≤
          ((Ts.length*(seen.card+q+(p+1)*Ts.length) : ℕ) : ℝ)/2^256 := by
        simp only [ghost,simulateQ_bind,StateT.run'_eq,StateT.run_bind,run_liftComp_prob,bind_map_left,map_bind]
        apply tvDist_bind_left_le_const'
        intro d
        exact ih cache seen hc _ (fun cs => hq _)
      have htri := tvDist_triangle
        ((simulateQ (localAnswer prims) (saltedDigestProgram (hist T) next)).run' cache)
        ((simulateQ (localAnswer prims) ghost).run' cache)
        ((simulateQ (localAnswer prims) (liftComp ($ᵗ HashOutput) (LocalSpec C) >>= fun d =>
          mixedGhostDigests D known Ts fun cs => k (digestColumnValues D T d::cs))).run' cache)
      refine htri.trans ((add_le_add hb ht).trans ?_)
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simp only [List.length_cons]
      push_cast
      nlinarith [show (0 : ℝ) ≤ Ts.length by positivity,show (0 : ℝ) ≤ p by positivity]

end ThresholdLeanXmssSecurity
end

/-! ## Digest mixed table -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

def mixedTableDigests (D : C.Coalition) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hist : C.Term → List Bit) (table : C.Term → Fin 256 → Bit) :
    List C.Term → (List (DigestColumn C) → OracleComp (LocalSpec C) α) → OracleComp (LocalSpec C) α
  | [], k => k []
  | T::Ts, k => if KnownTo D.1 T then known T >>= fun col => mixedTableDigests D known hist table Ts fun cs => k (col::cs)
    else do
      let d ← liftComp (oneDigestQuery (C := C) (List.ofFn (table T)) (hist T)) (LocalSpec C)
      mixedTableDigests D known hist table Ts fun cs => k (digestColumnValues D T d::cs)

lemma mixedTableDigests_congr (D : C.Coalition) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hist : C.Term → List Bit) (table table' : C.Term → Fin 256 → Bit)
    (Ts : List C.Term) (ht : ∀ T ∈ Ts,table T=table' T)
    (k : List (DigestColumn C) → OracleComp (LocalSpec C) α) :
    mixedTableDigests D known hist table Ts k=mixedTableDigests D known hist table' Ts k := by
  induction Ts generalizing k with
  | nil => rfl
  | cons T Ts ih =>
    simp only [mixedTableDigests,ht T (by simp)]
    by_cases hT : KnownTo D.1 T <;> simp only [hT,if_true,if_false]
    all_goals
      apply bind_congr
      intro v
      exact ih (fun U hU => ht U (by simp [hU])) _

/-- The actual salt table can be sampled coordinate by coordinate while preserving every
known-column oracle call and the entire continuation. -/
theorem mixedTableDigests_fresh (prims : Primitives) (D : C.Coalition)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) (hist : C.Term → List Bit)
    (Ts : List C.Term) (hTs : Ts.Nodup)
    (k : List (DigestColumn C) → OracleComp (LocalSpec C) α) :
    SameRun prims
      (do let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
          mixedTableDigests D known hist table Ts k)
      (mixedDigests D known hist Ts k) := by
  induction Ts generalizing k with
  | nil =>
    simp only [mixedTableDigests,mixedDigests]
    exact sameRun_discard_sample prims _
  | cons T Ts ih =>
    have hn := List.nodup_cons.mp hTs
    by_cases hT : KnownTo D.1 T
    · simp only [mixedTableDigests,mixedDigests,if_pos hT]
      refine (sameRun_swap prims (liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)) (known T) _).trans ?_
      apply SameRun.bind_right
      intro col
      exact ih hn.2 (fun cs => k (col::cs))
    · let draw := saltedDigestProgram (C := C) (hist T) (fun d => pure d)
      let rest := fun table d => mixedTableDigests D known hist table Ts fun cs => k (digestColumnValues D T d::cs)
      refine (sameRun_uniform_coordinate prims T (fun table => mixedTableDigests D known hist table (T::Ts) k)).symm.trans ?_
      have hupdate : ∀ table : C.Term → Fin 256 → Bit,∀ salt,
          mixedTableDigests D known hist (Function.update table T salt) (T::Ts) k=
            (do let d ← liftComp (oneDigestQuery (C := C) (List.ofFn salt) (hist T)) (LocalSpec C)
                rest table d) := by
        intro table salt
        simp only [mixedTableDigests,if_neg hT,Function.update_self]
        apply bind_congr
        intro d
        apply mixedTableDigests_congr
        intro U hU
        have hne : U ≠ T := by intro he; subst U; exact hn.1 hU
        exact Function.update_of_ne hne _ _
      refine SameRun.trans (ob := (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        draw >>= rest table)) (SameRun.of_eq ?_) ?_
      · simp only [draw,saltedDigestProgram,bind_assoc,pure_bind]
        simp_rw [hupdate]
      refine (sameRun_swap prims (liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)) draw rest).trans ?_
      simp only [draw,rest,mixedDigests,if_neg hT,saltedDigestProgram,bind_assoc,pure_bind]
      apply SameRun.bind_right
      intro salt
      apply SameRun.bind_right
      intro d
      exact ih hn.2 (fun cs => k (digestColumnValues D T d::cs))

/-- Known columns stay real, whereas all hidden columns lose their history dependence,
with a bound on actual outer-digest calls. -/
theorem mixedTableDigests_hide (prims : Primitives) (D : C.Coalition)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) (hist : C.Term → List Bit)
    (p : ℕ) (hknown : ∀ T,KnownTo D.1 T → IsQueryBoundP (known T) DigestQuery p)
    (Ts : List C.Term) (hTs : Ts.Nodup) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : List (DigestColumn C) → OracleComp (LocalSpec C) α)
    (q : ℕ) (hq : ∀ cs,IsQueryBoundP (k cs) DigestQuery q) :
    tvDist ((simulateQ (localAnswer prims) (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        mixedTableDigests D known hist table Ts k)).run' cache)
      ((simulateQ (localAnswer prims) (mixedGhostDigests D known Ts k)).run' cache) ≤
      ((Ts.length*(seen.card+q+(p+1)*Ts.length) : ℕ) : ℝ)/2^256 := by
  have he := mixedTableDigests_fresh prims D known hist Ts hTs k cache
  have he' := congrArg (fun d => Prod.fst <$> d) he
  simp only [← evalDist_map,← StateT.run'_eq] at he'
  rw [tvDist,he']
  exact mixedDigests_hide prims D known hist p hknown Ts cache seen hc k q hq

end ThresholdLeanXmssSecurity
end

/-! ## Digest protocol -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

def digestRows (cols : List (DigestColumn C)) : C.Party → List HashOutput :=
  fun i => cols.map (fun col => col i)

lemma digestColumnsRun_mixedTable (D : C.Coalition)
    (salts : C.Party → Shares C Bit) (history : C.Party → C.Term → List Bit)
    (hist : C.Term → List Bit) (table : C.Term → Fin 256 → Bit)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hknown : ∀ T,KnownTo D.1 T → Concrete.sequenceFin (honestDigestColumn D T salts history)=known T)
    (Ts : List C.Term) (k : (C.Party → List HashOutput) → OracleComp (LocalSpec C) α) :
    (digestColumnsRun (commonDigestColumn D salts history (fun T => List.ofFn (table T)) hist) Ts >>= k)=
      mixedTableDigests D known hist table Ts (fun cols => k (digestRows cols)) := by
  induction Ts generalizing k with
  | nil => simp only [digestColumnsRun,mixedTableDigests,pure_bind]; rfl
  | cons T Ts ih =>
    simp only [digestColumnsRun,bind_assoc,pure_bind,commonDigestColumn,mixedTableDigests]
    by_cases hT : KnownTo D.1 T
    · simp only [if_pos hT,hknown T hT]
      apply bind_congr
      intro col
      rw [ih]
      rfl
    · simp only [if_neg hT,bind_assoc,pure_bind]
      apply bind_congr
      intro d
      rw [ih]
      rfl

lemma mixedTableDigests_bind {β : Type} (D : C.Coalition)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hist : C.Term → List Bit) (table : C.Term → Fin 256 → Bit)
    (Ts : List C.Term) (k : List (DigestColumn C) → OracleComp (LocalSpec C) α)
    (tail : α → OracleComp (LocalSpec C) β) :
    (mixedTableDigests D known hist table Ts k >>= tail)=
      mixedTableDigests D known hist table Ts (fun cs => k cs >>= tail) := by
  induction Ts generalizing k with
  | nil => rfl
  | cons T Ts ih =>
    simp only [mixedTableDigests]
    by_cases hT : KnownTo D.1 T <;> simp only [hT,if_true,if_false,bind_assoc]
    all_goals
      apply bind_congr
      intro col
      exact ih _

variable {E Ia : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The real compare-digests phase, including its network round and arbitrary tail, has the
mixed-table form used by the hiding theorem. -/
theorem executePhase_digestTables (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State)
    (salts : (C.Term → Fin 256 → Bit) → C.Party → Shares C Bit)
    (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (hist : C.Term → List Bit) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hsalt : ∀ table T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T →
      vector 256 (salts table i T)=List.ofFn (table T))
    (hhist : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → (hs i).history T=hist T)
    (hknown : ∀ table T,KnownTo D.1 T →
      Concrete.sequenceFin (honestDigestColumn D T (salts table) (fun j => (hs j).history))=known T) :
    SameRun prims
      (do let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
          executePhase localRoles D A (checkFunctionalities K) fuel st
            (fun i => (compareDigests (localContext i) (salts table i) >>= f i).run' (hs i)))
      (do let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
          mixedTableDigests D known hist table C.terms fun cols =>
            executePhase localRoles D A (checkFunctionalities K) fuel st
              (fun i => afterDigests i (digestRows cols i) ((f i ()).run' (hs i)))) := by
  apply SameRun.bind_right
  intro table
  refine (executePhase_digestCommon prims K D A fuel st (salts table) hs f
    (fun T => List.ofFn (table T)) hist (hsalt table) hhist).trans ?_
  apply SameRun.of_eq
  exact digestColumnsRun_mixedTable D (salts table) (fun j => (hs j).history) hist table known (hknown table) C.terms _

/-- The actual network digest phase can replace all hidden digests by independent tokens.
The bound concerns the full continuation, so it includes adaptive challenge calls and Z. -/
theorem executePhase_digestHide (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State)
    (salts : (C.Term → Fin 256 → Bit) → C.Party → Shares C Bit)
    (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (hist : C.Term → List Bit) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hsalt : ∀ table T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T →
      vector 256 (salts table i T)=List.ofFn (table T))
    (hhist : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → (hs i).history T=hist T)
    (hknown : ∀ table T,KnownTo D.1 T →
      Concrete.sequenceFin (honestDigestColumn D T (salts table) (fun j => (hs j).history))=known T)
    (p : ℕ) (hbound : ∀ T,KnownTo D.1 T → IsQueryBoundP (known T) DigestQuery p)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    {β : Type} (tail : (A.State × (C.Party → Option α)) → OracleComp (LocalSpec C) β)
    (q : ℕ) (hq : ∀ cols,IsQueryBoundP
      (executePhase localRoles D A (checkFunctionalities K) fuel st
        (fun i => afterDigests i (digestRows cols i) ((f i ()).run' (hs i))) >>= tail) DigestQuery q) :
    tvDist ((simulateQ (localAnswer prims) (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        let out ← executePhase localRoles D A (checkFunctionalities K) fuel st
          (fun i => (compareDigests (localContext i) (salts table i) >>= f i).run' (hs i))
        tail out)).run' cache)
      ((simulateQ (localAnswer prims) (mixedGhostDigests D known C.terms fun cols =>
        executePhase localRoles D A (checkFunctionalities K) fuel st
          (fun i => afterDigests i (digestRows cols i) ((f i ()).run' (hs i))) >>= tail)).run' cache) ≤
      ((C.terms.length*(seen.card+q+(p+1)*C.terms.length) : ℕ) : ℝ)/2^256 := by
  have he := (executePhase_digestTables prims K D A fuel st salts hs f hist known hsalt hhist hknown).bind
    (fun out => SameRun.refl prims (tail out)) cache
  simp only [bind_assoc,mixedTableDigests_bind] at he
  have he' := congrArg (fun d => Prod.fst <$> d) he
  simp only [← evalDist_map,← StateT.run'_eq] at he'
  rw [tvDist,he']
  have hnodup : C.terms.Nodup := Finset.nodup_toList _
  exact mixedTableDigests_hide prims D known hist p hbound C.terms hnodup cache seen hc _ q hq

end ThresholdLeanXmssSecurity
end

/-! ## Projected network -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β : Type}

def PartyDigest : (PartySpec C E G).Domain → Prop
  | .inl (.inl q) => DigestQuery q
  | _ => False

def DigestPartyBound (p : PartyM C E G α) (n : ℕ) : Prop :=
  IsQueryBoundP p.run (PartyDigest (E := E) (G := G)) n

/-- The local budget remaining after the next round or hybrid call. -/
def DigestStepBound (st : Step C E G α) (n : ℕ) : Prop :=
  match st with
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyDigest (E := E) (G := G)) n
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyDigest (E := E) (G := G)) n

/-- Advancing a party spends only its local budget, leaving the residual budget for its continuation. -/
theorem advance_bind_digestBound (oa : OracleComp (PartySpec C E G) (Option α))
    (k : Step C E G α → OracleComp (LocalSpec C) β) (extra : ℕ) :
    ∀ n, IsQueryBoundP oa (PartyDigest (E := E) (G := G)) n →
      (∀ st b, b ≤ n → DigestStepBound st b → IsQueryBoundP (k st) DigestQuery (extra + b)) →
      IsQueryBoundP (advance oa >>= k) DigestQuery (extra + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ hk
    rw [advance_pure, pure_bind]
    exact hk (.done a) n le_rfl trivial
  | query_bind t f ih =>
    intro n h hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · rw [advance_query_bind, bind_assoc, isQueryBoundP_query_bind_iff]
      have hcp : DigestQuery q → PartyDigest (E := E) (G := G) (.inl (.inl q)) := by
        exact id
      constructor
      · by_cases hc : DigestQuery q
        · right
          have hn := h.1.resolve_left (not_not.mpr (hcp hc))
          omega
        · exact Or.inl hc
      · intro u
        have hb : (if PartyDigest (E := E) (G := G) (.inl (.inl q)) then n - 1 else n) ≤ n := by
          split_ifs <;> omega
        have hi := ih u _ (h.2 u) (fun st b hb' hs => hk st b (hb'.trans hb) hs)
        apply hi.mono
        by_cases hp : PartyDigest (E := E) (G := G) (.inl (.inl q))
        · by_cases hc : DigestQuery q
          · simp only [if_pos hp, if_pos hc]
            have hn := h.1.resolve_left (not_not.mpr hp)
            omega
          · simp only [if_pos hp, if_neg hc]
            omega
        · have hc : ¬ DigestQuery q := fun hc => hp (hcp hc)
          simp only [if_neg hp, if_neg hc]
          exact le_rfl
    · change IsQueryBoundP (k (.wait outbox f)) DigestQuery (extra + n)
      apply hk _ n le_rfl
      simpa [DigestStepBound, PartyDigest] using h.2
    · change IsQueryBoundP (k (.call input f)) DigestQuery (extra + n)
      apply hk _ n le_rfl
      simpa [DigestStepBound, PartyDigest] using h.2

/-- Advance the parties sequentially while accounting for each residual budget. -/
theorem sequenceFin_advance_bind_digestBound : ∀ {N : ℕ}
    (oa : Fin N → OracleComp (PartySpec C E G) (Option α)) (budget : Fin N → ℕ)
    (h : ∀ i, IsQueryBoundP (oa i) (PartyDigest (E := E) (G := G)) (budget i))
    (k : (Fin N → Step C E G α) → OracleComp (LocalSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ), (∀ i, b i ≤ budget i) → (∀ i, DigestStepBound (st i) (b i)) →
      IsQueryBoundP (k st) DigestQuery (extra + ∑ i, b i)) →
    IsQueryBoundP ((Concrete.sequenceFin fun i => advance (oa i)) >>= k) DigestQuery
      (extra + ∑ i, budget i)
  | 0, oa, budget, h, k, extra, hk => by
    simp only [Concrete.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, h, k, extra, hk => by
    simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
    rw [Fin.sum_univ_succ]
    have he : extra + (budget 0 + ∑ i : Fin N, budget i.succ) =
        (extra + ∑ i : Fin N, budget i.succ) + budget 0 := by omega
    rw [he]
    refine advance_bind_digestBound (oa 0) _ _ (budget 0) (h 0) (fun st0 b0 hb0 hs0 => ?_)
    have he' : (extra + ∑ i : Fin N, budget i.succ) + b0 =
        (extra + b0) + ∑ i : Fin N, budget i.succ := by omega
    rw [he']
    refine sequenceFin_advance_bind_digestBound (fun i : Fin N => oa i.succ) (fun i => budget i.succ)
      (fun i => h i.succ) (fun st => k (Fin.cases st0 st)) (extra + b0) (fun st b hb hs => ?_)
    have hp := hk (Fin.cases st0 st) (Fin.cases b0 b)
      (fun i => Fin.cases hb0 hb i) (fun i => Fin.cases hs0 hs i)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hp

section NetworkBound
variable {I O Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R)

lemma roundResume_digestBound (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, DigestStepBound (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (roundResume D sent steps j) (PartyDigest (E := E) (G := CallSpec I O)) (budget j) := by
  have hj := h j
  unfold roundResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k => exact isQueryBoundP_pure _ _ _
  | wait out k =>
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [DigestStepBound, hs] at hj
      exact hj _

lemma callResume_digestBound (out : C.Party → Option O)
    (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, DigestStepBound (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (callResume D out steps j) (PartyDigest (E := E) (G := CallSpec I O)) (budget j) := by
  have hj := h j
  unfold callResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k =>
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [DigestStepBound, hs] at hj
      exact hj _
  | wait out k =>
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · exact Or.inl (by simp [PartyDigest])
    · simpa [DigestStepBound, hs, PartyDigest] using hj

lemma stepRound_bind_digestBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) DigestQuery step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) DigestQuery step)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, DigestStepBound (steps j) (budget j))
    (k : (A.State × (C.Party → Step C E (CallSpec I O) α) × (C.Party → C.Party → Option (Msg E))) →
      OracleComp (LocalSpec C) β) (extra : ℕ)
    (hk : ∀ st (b : C.Party → ℕ), (∀ j, b j ≤ budget j) → (∀ j, DigestStepBound (st.2.1 j) (b j)) →
      IsQueryBoundP (k st) DigestQuery (extra + ∑ j, b j)) :
    IsQueryBoundP (stepRound localRoles D A F state steps >>= k) DigestQuery (step + extra + ∑ j, budget j) := by
  unfold stepRound
  split_ifs
  · simp only [bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j) (hF _ _) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .call _ resume => if j ∈ D.1 then pure (Step.done none) else advance (resume (result.2 j))
        | st => pure st) = fun j => advance (callResume D result.2 steps j) := by
      funext j
      cases hs : steps j with
      | done out => simp only [callResume, hs]; rfl
      | wait out k => simp only [callResume, hs]; rfl
      | call input k => simp only [callResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_advance_bind_digestBound
      (fun j => callResume D result.2 steps j) budget (callResume_digestBound D result.2 steps budget h)
      (fun st => k (result.1, st, fun _ _ => none)) extra
      (fun st b hb hs => hk (result.1, st, fun _ _ => none) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) =>
      IsQueryBoundP (Concrete.sequenceFin f >>= fun st => k (result.1, st, fun _ _ => none))
        DigestQuery (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl
  · simp only [localRoles, bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j) (hr _ _) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .done out => pure (Step.done out)
        | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
            advance (resume fun k => if k ∈ D.1 then result.2 k j else (steps k).delivered j)
        | .call _ _ => pure (Step.done none)) = fun j => advance (roundResume D result.2 steps j) := by
      funext j
      cases hs : steps j with
      | done out => simp only [roundResume, hs]; rfl
      | call input k => simp only [roundResume, hs]; rfl
      | wait out k => simp only [roundResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_advance_bind_digestBound
      (fun j => roundResume D result.2 steps j) budget (roundResume_digestBound D result.2 steps budget h)
      (fun st => k (result.1, st, result.2)) extra
      (fun st b hb hs => hk (result.1, st, result.2) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) =>
      IsQueryBoundP (Concrete.sequenceFin f >>= fun st => k (result.1, st, result.2))
        DigestQuery (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl

lemma executeRounds_digestBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) DigestQuery step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) DigestQuery step) :
    ∀ fuel state (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ),
      (∀ j, DigestStepBound (steps j) (budget j)) →
      IsQueryBoundP (executeRounds localRoles D A F fuel state steps) DigestQuery (fuel * step + ∑ j, budget j)
  | 0, state, steps, budget, h => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, budget, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine (stepRound_bind_digestBound D A F step hr hF state steps budget h _ (fuel * step) ?_).mono ?_
      · intro st b hb hs
        exact executeRounds_digestBound step hr hF fuel st.1 st.2.1 b hs
      · simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma executePhase_digestBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) DigestQuery step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) DigestQuery step)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec I O) α)
    (budget : C.Party → ℕ) (hp : ∀ j, j ∉ D.1 → DigestPartyBound (program j) (budget j)) :
    IsQueryBoundP (executePhase localRoles D A F fuel state program) DigestQuery (fuel * step + ∑ j, budget j) := by
  unfold executePhase startSteps
  simp only [localRoles]
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else advance (program i).run) =
      fun i => advance (if i ∈ D.1 then pure none else (program i).run) := by
    funext i
    split_ifs <;> rfl
  change IsQueryBoundP ((Concrete.sequenceFin _) >>= _) _ _
  rw [he]
  apply sequenceFin_advance_bind_digestBound _ budget
  · intro j
    split_ifs with hj
    · exact isQueryBoundP_pure _ _ _
    · exact hp j hj
  · intro st b hb hs
    exact executeRounds_digestBound D A F step hr hF fuel state st b hs

end NetworkBound

end ThresholdLeanXmssSecurity
end

/-! ## Salt phase -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The actual salt phase reduces to the chosen known terms and one fresh hidden table;
the unused PRSS pair table has no effect on the entire adaptive continuation. -/
theorem executePhase_randBits_first (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (count : ℕ)
    (hs : C.Party → RunState C) (f : C.Party → Shares C Bit → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
        (fun i => ((hybridCheckGadgets K i).randBits count >>= fun w => f i w.1).run' (hs i)))
      (do
        let p ← (rightAdversary (rightAdversary A)).answer st ()
        let fresh ← liftComp ($ᵗ (C.Term → Fin count → Bit)) (LocalSpec C)
        executePhase localRoles D A (checkFunctionalities K) fuel p.1
          (fun i => (f i (randShares D count p.2.1 fresh i)).run'
            ⟨(hs i).history,(hs i).label+1,(hs i).tag⟩)) := by
  rw [executePhase_randBits,runFunctionality_rand_local D (rightAdversary (rightAdversary A)) st _
    (by intro i hi; simp [hi]),firstInput_honest_const]
  simp only [bind_assoc,pure_bind]
  apply SameRun.bind_right
  intro p
  apply SameRun.bind_right
  intro fresh
  refine SameRun.trans (SameRun.bind_right _ fun pairs => ?_) (sameRun_discard_sample prims _)
  apply SameRun.of_eq
  apply executePhase_congr_honest
  intro i hi
  simp only [afterRandom,randFinish,if_neg hi]
  congr 2
  funext T g
  by_cases ht : i ∈ C.holders T <;> by_cases hk : KnownTo D.1 T <;> simp [randShares,ht,hk]

end ThresholdLeanXmssSecurity
end

/-! ## Digest known -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {α : Type}

lemma sequenceFin_digestBound : ∀ {n : ℕ} (oa : Fin n → OracleComp (LocalSpec C) α) (p : ℕ),
    (∀ i,IsQueryBoundP (oa i) DigestQuery p) →
      IsQueryBoundP (Concrete.sequenceFin oa) DigestQuery (n*p)
  | 0,oa,p,h => isQueryBoundP_pure _ _ _
  | n+1,oa,p,h => by
    simp only [Concrete.sequenceFin]
    have hb := isQueryBoundP_bind (h 0) (fun a _ =>
      isQueryBoundP_bind (sequenceFin_digestBound (fun i : Fin n => oa i.succ) p (fun i => h i.succ))
        (fun b _ => isQueryBoundP_pure DigestQuery (Fin.cases (motive := fun _ => α) a b) 0))
    simpa [Nat.succ_mul,Nat.add_comm] using hb

lemma honestDigestColumn_digestBound (D : C.Coalition) (T : C.Term)
    (salts : C.Party → Shares C Bit) (history : C.Party → C.Term → List Bit) :
    IsQueryBoundP (Concrete.sequenceFin (honestDigestColumn D T salts history)) DigestQuery C.n := by
  simpa only [Nat.mul_one] using sequenceFin_digestBound (honestDigestColumn D T salts history) 1 (by
    intro i
    unfold honestDigestColumn
    split_ifs
    · exact oneDigestQuery_digestBound _ _
    · exact isQueryBoundP_pure _ _ _)

lemma randShares_salt_vector (D : C.Coalition) (known : Shares C Bit)
    (table : C.Term → Fin 256 → Bit) (T : C.Term) (hT : ¬ KnownTo D.1 T)
    (i : C.Party) (hi : i ∈ C.holders T) :
    vector 256 (randShares D 256 known table i T)=List.ofFn (table T) := by
  have he : randShares D 256 known table i T=(fun g => if h : g < 256 then table T ⟨g,h⟩ else 0) := by
    funext g
    simp [randShares,hi,hT]
  rw [he]
  exact vector_extend_ofFn 256 (table T)

lemma honestDigestColumn_randShares_known (D : C.Coalition) (T : C.Term) (hT : KnownTo D.1 T)
    (known : Shares C Bit) (table table' : C.Term → Fin 256 → Bit)
    (history : C.Party → C.Term → List Bit) :
    honestDigestColumn D T (randShares D 256 known table) history=
      honestDigestColumn D T (randShares D 256 known table') history := by
  funext i
  simp only [honestDigestColumn]
  by_cases hi : i ∉ D.1 ∧ i ∈ C.holders T
  · simp only [if_pos hi]
    have he : ∀ tab : C.Term → Fin 256 → Bit,randShares D 256 known tab i T=known T := by
      intro tab
      funext g
      simp [randShares,hi.2,hT]
    rw [he,he]
  · simp only [if_neg hi]

variable {E Ia : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- For the actual salt gadget, known columns consume at most one outer digest per party;
all hypotheses about salt independence are discharged by its sampled-table definition. -/
theorem executePhase_digestHide_randShares (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (knownSalt : Shares C Bit)
    (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (hist : C.Term → List Bit)
    (hhist : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → (hs i).history T=hist T)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    {β : Type} (tail : (A.State × (C.Party → Option α)) → OracleComp (LocalSpec C) β)
    (q : ℕ) (hq : ∀ cols,IsQueryBoundP
      (executePhase localRoles D A (checkFunctionalities K) fuel st
        (fun i => afterDigests i (digestRows cols i) ((f i ()).run' (hs i))) >>= tail) DigestQuery q) :
    tvDist ((simulateQ (localAnswer prims) (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        let out ← executePhase localRoles D A (checkFunctionalities K) fuel st
          (fun i => (compareDigests (localContext i) (randShares D 256 knownSalt table i) >>= f i).run' (hs i))
        tail out)).run' cache)
      ((simulateQ (localAnswer prims) (mixedGhostDigests D
        (fun T => Concrete.sequenceFin (honestDigestColumn D T (randShares D 256 knownSalt 0) (fun j => (hs j).history)))
        C.terms fun cols => executePhase localRoles D A (checkFunctionalities K) fuel st
          (fun i => afterDigests i (digestRows cols i) ((f i ()).run' (hs i))) >>= tail)).run' cache) ≤
      ((C.terms.length*(seen.card+q+(C.n+1)*C.terms.length) : ℕ) : ℝ)/2^256 := by
  apply executePhase_digestHide prims K D A fuel st (fun table => randShares D 256 knownSalt table) hs f hist _
    (fun table T hT i _ hi => randShares_salt_vector D knownSalt table T hT i hi) hhist
    (fun table T hT => congrArg Concrete.sequenceFin (honestDigestColumn_randShares_known D T hT knownSalt table 0 _))
    C.n (fun T _ => honestDigestColumn_digestBound D T _ _) cache seen hc tail q hq

end ThresholdLeanXmssSecurity
end

/-! ## Digest tail -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β ι : Type} {G : OracleSpec ι}

lemma counted_digestBound {oa : OracleComp (LocalSpec C) α} {q : ℕ}
    (h : IsQueryBoundP oa Counted q) : IsQueryBoundP oa DigestQuery q :=
  IsQueryBoundP.of_imp digestSaltProjection_counted h

lemma PartyBound.to_digest {p : PartyM C E G α} {n : ℕ} (h : PartyBound p n) : DigestPartyBound p n := by
  apply IsQueryBoundP.of_imp _ h
  rintro ((q|out)|input) ht
  · rcases q with n|q|x
    · simp [PartyDigest,DigestQuery,digestSaltProjection] at ht
    · trivial
    · trivial
  · exact False.elim ht
  · exact False.elim ht

lemma DigestPartyBound.pure (a : α) : DigestPartyBound (pure a : PartyM C E G α) 0 :=
  isQueryBoundP_pure _ _ _

lemma DigestPartyBound.bind {p : PartyM C E G α} {f : α → PartyM C E G β} {n m : ℕ}
    (h : DigestPartyBound p n) (hf : ∀ a,DigestPartyBound (f a) m) : DigestPartyBound (p >>= f) (n+m) := by
  unfold DigestPartyBound
  simp only [OptionT.run_bind]
  apply isQueryBoundP_bind h
  intro a _
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some a => exact hf a

def DigestRunBound (p : RunM C E G α) : Prop := ∀ hs,DigestPartyBound (p.run hs) 0

lemma DigestRunBound.of_zero {p : RunM C E G α} (h : RunBound p 0) : DigestRunBound p :=
  fun hs => (h hs).to_digest

lemma DigestRunBound.bind {p : RunM C E G α} {f : α → RunM C E G β}
    (h : DigestRunBound p) (hf : ∀ a,DigestRunBound (f a)) : DigestRunBound (p >>= f) := by
  intro hs
  exact DigestPartyBound.bind (h hs) (fun a => hf a.1 a.2)

lemma DigestRunBound.lift {p : PartyM C E G α} (h : DigestPartyBound p 0) :
    DigestRunBound (StateT.lift p : RunM C E G α) := by
  intro hs
  change DigestPartyBound (p >>= fun a => Pure.pure (a,hs)) 0
  exact DigestPartyBound.bind h (fun _ => DigestPartyBound.pure _)

lemma DigestRunBound.run' {p : RunM C E G α} (h : DigestRunBound p) (hs : RunState C) :
    DigestPartyBound (p.run' hs) 0 :=
  DigestPartyBound.bind (h hs) (fun _ => DigestPartyBound.pure _)

lemma localStep_digestBound {oa : OracleComp (LocalSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa DigestQuery n) : DigestPartyBound (localStep oa : PartyM C E G α) n := by
  unfold DigestPartyBound localStep
  change IsQueryBoundP (some <$> liftComp oa (PartySpec C E G)) _ n
  rw [isQueryBoundP_map_iff]
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftComp_bind]
    have he : liftComp (OracleComp.lift (OracleSpec.query t)) (PartySpec C E G)=
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (.inl (.inl t))) := by
      rcases t with n | q | x <;> rfl
    rw [he]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1,fun u => ih u (h.2 u)⟩

lemma hashQuery_no_digest (q : Query C) (hq : ¬ DigestQuery (.inr (.inl q))) :
    IsQueryBoundP (liftComp (hashQuery q) (LocalSpec C)) DigestQuery 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inr (.inl q)))) DigestQuery 0
  exact (isQueryBoundP_query_iff ..).2 (fun h => False.elim (hq h))

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

lemma findChallenge_no_digest (K : Constants C E) (key : HashOutput) : ∀ tries index,
    IsQueryBoundP (liftComp (findChallenge K key tries index) (LocalSpec C)) DigestQuery 0
  | 0,index => by simp [findChallenge]
  | tries+1,index => by
    simp only [findChallenge,liftComp_bind]
    apply isQueryBoundP_bind (n := 0) (m := 0) (hashQuery_no_digest _ (by simp [DigestQuery,digestSaltProjection]))
    intro h _
    split
    · simp
    · exact findChallenge_no_digest K key tries (index+1)

lemma hybrid_challenge_no_digest (K : Constants C E) (i : C.Party) :
    DigestRunBound (challenge K (hybridCheckGadgets K i)) := by
  have hc : DigestRunBound (coinKey K (hybridCheckGadgets K i)) := by
    unfold coinKey
    apply (DigestRunBound.of_zero RunBound.get).bind
    intro hs
    apply (DigestRunBound.of_zero (hybrid_coin_queryBound K i 1)).bind
    intro values
    apply DigestRunBound.lift
    exact localStep_digestBound (hashQuery_no_digest _ (by simp [DigestQuery,digestSaltProjection]))
  unfold challenge
  apply hc.bind
  intro key
  apply (DigestRunBound.lift (localStep_digestBound (findChallenge_no_digest K key challengeTries 0))).bind
  intro out
  split
  · exact DigestRunBound.of_zero (RunBound.pure _)
  · exact DigestRunBound.of_zero (RunBound.lift PartyBound.failure)

lemma finalOpenProgram_no_digest (K : Constants C E) (i : C.Party) (v : ℕ → E) :
    DigestPartyBound (finalOpenProgram K i v) 0 := by
  unfold finalOpenProgram
  exact (PartyBound.bind (RunBound.openSh K _ _ _) (fun _ => PartyBound.require _)).to_digest

lemma afterDigests_no_digest (i : C.Party) (ds : List HashOutput)
    (next : PartyM C E (CheckSpec C E) α) (hn : DigestPartyBound next 0) :
    DigestPartyBound (afterDigests i ds next) 0 := by
  unfold afterDigests
  exact DigestPartyBound.bind (PartyBound.exchange _).to_digest fun _ =>
    DigestPartyBound.bind (PartyBound.require _).to_digest fun _ => hn

/-- The actual post-digest network consumes only the adversary's outer-digest budget.
Honest challenge expansion, however long it runs, contributes zero to this bound. -/
theorem executePhase_afterDigests_digestBound {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel step : ℕ) (st : A.State)
    (hr : ∀ st sent,IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l,IsQueryBoundP (A.answer st l) Counted step)
    (ds : C.Party → List HashOutput) (next : C.Party → PartyM C E (CheckSpec C E) α)
    (hn : ∀ i,i ∉ D.1 → DigestPartyBound (next i) 0)
    (tail : A.State × (C.Party → Option α) → OracleComp (LocalSpec C) β)
    (q : ℕ) (hq : ∀ out,IsQueryBoundP (tail out) Counted q) :
    IsQueryBoundP (executePhase localRoles D A (checkFunctionalities K) fuel st
      (fun i => afterDigests i (ds i) (next i)) >>= tail) DigestQuery (fuel*step+q) := by
  have hb := executePhase_digestBound D A (checkFunctionalities K) step
    (fun st sent => counted_digestBound (hr st sent))
    (fun st inputs => counted_digestBound (runFunctionality_queryBound D A (checkFunctionalities K) step
      (fun inputs => checkFunctionalities_queryBound K D inputs step) ha st inputs))
    fuel st (fun i => afterDigests i (ds i) (next i)) (fun _ => 0)
    (fun i hi => afterDigests_no_digest i (ds i) (next i) (hn i hi))
  simpa only [Finset.sum_const_zero,Nat.add_zero] using
    isQueryBoundP_bind hb (fun out _ => counted_digestBound (hq out))

end ThresholdLeanXmssSecurity
end

/-! ## Final digest -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α β : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

def finalAfterDigests (K : Constants C E) (i : C.Party) (wa wb a b d q0 q2 : E) :
    RunM C E (CheckSpec C E) Unit := do
  let r ← challenge K (hybridCheckGadgets K i)
  StateT.lift (finalOpenProgram K i (finalOpenVector wa wb a b d q0 q2 r))

/-- The remaining source program after the digest comparison has no honest outer-digest calls. -/
theorem finalAfterDigests_no_digest (K : Constants C E) (i : C.Party) (wa wb a b d q0 q2 : E) :
    DigestRunBound (finalAfterDigests K i wa wb a b d q0 q2) := by
  apply (hybrid_challenge_no_digest K i).bind
  intro r
  exact DigestRunBound.lift (finalOpenProgram_no_digest K i _)

def afterSalt (hs : RunState C) : RunState C := ⟨hs.history,hs.label+1,hs.tag⟩

abbrev SaltReply (A : CheckAdversary C E Ia) := A.State × Shares C Bit × (C.Party → C.Party → ℕ → Bit)

def saltActualContinuation (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (tail : A.State × (C.Party → Option α) → OracleComp (LocalSpec C) β)
    (p : SaltReply A) : OracleComp (LocalSpec C) β := do
  let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
  let out ← executePhase localRoles D A (checkFunctionalities K) fuel p.1
    (fun i => (compareDigests (localContext i) (randShares D 256 p.2.1 table i) >>= f i).run' (afterSalt (hs i)))
  tail out

def saltGhostContinuation (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (tail : A.State × (C.Party → Option α) → OracleComp (LocalSpec C) β)
    (p : SaltReply A) : OracleComp (LocalSpec C) β :=
  mixedGhostDigests D
    (fun T => Concrete.sequenceFin (honestDigestColumn D T (randShares D 256 p.2.1 0) (fun j => (hs j).history)))
    C.terms fun cols => executePhase localRoles D A (checkFunctionalities K) fuel p.1
      (fun i => afterDigests i (digestRows cols i) ((f i ()).run' (afterSalt (hs i)))) >>= tail

def saltGhostPhase (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (hs : C.Party → RunState C)
    (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (tail : A.State × (C.Party → Option α) → OracleComp (LocalSpec C) β) : OracleComp (LocalSpec C) β :=
  (rightAdversary (rightAdversary A)).answer st () >>= saltGhostContinuation K D A fuel hs f tail

/-- Both projected replies preserve the caller's query bound. -/
lemma saltReply_queryBound (A : CheckAdversary C E Ia) (st : A.State) (step : ℕ)
    (ha : ∀ st l,IsQueryBoundP (A.answer st l) Counted step) :
    IsQueryBoundP ((rightAdversary (rightAdversary A)).answer st ()) Counted step := by
  dsimp only [rightAdversary]
  simp only [bind_assoc,pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st (.inr (.inr ())))
    (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

/-- The complete salt-generation and digest phase can use independent hidden tokens.
The callback, digest network round, challenge phase, final opening, and distinguisher are
all included; only actual outer-digest queries enter the hiding bound. -/
theorem saltDigestPhase_hide (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel step : ℕ) (st : A.State)
    (hr : ∀ st sent,IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l,IsQueryBoundP (A.answer st l) Counted step)
    (hs : C.Party → RunState C) (f : C.Party → Unit → RunM C E (CheckSpec C E) α)
    (hf : ∀ i,i ∉ D.1 → DigestRunBound (f i ()))
    (hist : C.Term → List Bit)
    (hhist : ∀ T,¬KnownTo D.1 T → ∀ i,i ∉ D.1 → i ∈ C.holders T → (hs i).history T=hist T)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (tail : A.State × (C.Party → Option α) → OracleComp (LocalSpec C) β)
    (final : ℕ) (hq : ∀ out,IsQueryBoundP (tail out) Counted final) :
    tvDist ((simulateQ (localAnswer prims)
      (executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
        (fun i => ((hybridCheckGadgets K i).randBits 256 >>= fun salts =>
          compareDigests (localContext i) salts.1 >>= f i).run' (hs i)) >>= tail)).run' cache)
      ((simulateQ (localAnswer prims) (saltGhostPhase K D A fuel st hs f tail)).run' cache) ≤
      ((C.terms.length*(seen.card+(fuel+1)*step+final+(C.n+1)*C.terms.length) : ℕ) : ℝ)/2^256 := by
  have hsame : SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
        (fun i => ((hybridCheckGadgets K i).randBits 256 >>= fun salts =>
          compareDigests (localContext i) salts.1 >>= f i).run' (hs i)) >>= tail)
      ((rightAdversary (rightAdversary A)).answer st () >>= saltActualContinuation K D A fuel hs f tail) := by
    have hh := (executePhase_randBits_first prims K D A fuel st 256 hs
      (fun i salts => compareDigests (localContext i) salts >>= f i)).bind
        (fun out => SameRun.refl prims (tail out))
    simpa only [saltActualContinuation,afterSalt,bind_assoc,pure_bind] using hh
  have he := hsame cache
  have he' := congrArg (fun d => Prod.fst <$> d) he
  simp only [← evalDist_map,← StateT.run'_eq] at he'
  rw [tvDist,he']
  change tvDist ((simulateQ (localAnswer prims)
      ((rightAdversary (rightAdversary A)).answer st () >>= saltActualContinuation K D A fuel hs f tail)).run' cache)
    ((simulateQ (localAnswer prims)
      ((rightAdversary (rightAdversary A)).answer st () >>= saltGhostContinuation K D A fuel hs f tail)).run' cache) ≤ _
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
  apply tvDist_bind_left_le_const
  intro z hz
  have hz' : z ∈ support ((simulateQ (localAnswer prims)
      ((rightAdversary (rightAdversary A)).answer st ())).run cache) := by
    simpa only [rightAdversary,simulateQ_bind,StateT.run_bind] using hz
  obtain ⟨seen',hc',hcard⟩ := localProgram_digest_covered prims
    ((rightAdversary (rightAdversary A)).answer st ()) DigestQuery (fun _ ht => ht)
    step (counted_digestBound (saltReply_queryBound A st step ha)) cache seen hc z hz'
  have htail : ∀ cols,IsQueryBoundP
      (executePhase localRoles D A (checkFunctionalities K) fuel z.1.1
        (fun i => afterDigests i (digestRows cols i) ((f i ()).run' (afterSalt (hs i)))) >>= tail)
      DigestQuery (fuel*step+final) := fun cols => executePhase_afterDigests_digestBound K D A fuel step z.1.1 hr ha
        (digestRows cols) (fun i => (f i ()).run' (afterSalt (hs i)))
        (fun i hi => (hf i hi).run' _) tail final hq
  have hb := executePhase_digestHide_randShares prims K D A fuel z.1.1 z.1.2.1
    (fun i => afterSalt (hs i)) f hist hhist z.2 seen' hc' tail (fuel*step+final) htail
  refine hb.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.mul_le_mul_left C.terms.length (show
    seen'.card+(fuel*step+final)+(C.n+1)*C.terms.length ≤
      seen.card+(fuel+1)*step+final+(C.n+1)*C.terms.length by nlinarith)

end ThresholdLeanXmssSecurity
end

/-! ## Digest round -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E Ia α : Type}

def digestInbox (D : C.Coalition) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) : Mail C E :=
  fun j => if j ∈ D.1 then sent j i else digestOutbox j (ds j) i

def digestLive (D : C.Coalition) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) : Prop :=
  ¬ C.parties.any (fun j => Msg.isAbort (digestInbox D ds sent i j)) ∧ DigestsAgree i (ds i) (digestInbox D ds sent i)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The transcript of the digest round is independent of every later opening vector.
Selective abort is recorded explicitly as the predicate `digestLive`. -/
theorem executePhase_afterDigests_round (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (ds : C.Party → List HashOutput)
    (next : C.Party → PartyM C E (CheckSpec C E) α) :
    executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
      (fun i => afterDigests i (ds i) (next i)) = (do
      let p ← A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then digestOutbox i (ds i) c else none)
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => if digestLive D ds p.2 i then next i else failure)) := by
  have he : (fun i => afterDigests i (ds i) (next i)) =
      (fun i => optionalExchange (some (digestOutbox i (ds i)))
        (fun inbox => require (DigestsAgree i (ds i) inbox) >>= fun _ => next i)) := rfl
  rw [he,executePhase_optionalExchange D A (checkFunctionalities K) fuel st _ _ (by
    obtain ⟨i,hi⟩ := coalition_has_honest D
    exact ⟨i,hi,by simp⟩)]
  dsimp only [Option.getD_some]
  apply bind_congr
  intro p
  apply executePhase_congr_honest
  intro i hi
  simp only [afterExchange,Option.getD_some]
  change (if C.parties.any (fun j => Msg.isAbort (digestInbox D ds p.2 i j)) then failure
    else require (DigestsAgree i (ds i) (digestInbox D ds p.2 i)) >>= fun _ => next i)=_
  by_cases ha : C.parties.any (fun j => Msg.isAbort (digestInbox D ds p.2 i j))
  · simp only [ha,if_true,digestLive,not_true_eq_false,false_and,if_false]
  · simp only [ha,if_false,digestLive,not_false_eq_true,true_and]
    by_cases hg : DigestsAgree i (ds i) (digestInbox D ds p.2 i)
    · simp [require,hg]
    · simp [require,hg]

end ThresholdLeanXmssSecurity
end


namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

end ThresholdLeanXmssSecurity
