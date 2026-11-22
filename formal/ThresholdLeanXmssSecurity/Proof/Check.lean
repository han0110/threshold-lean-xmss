import ThresholdLeanXmssSecurity.Proof.BuildingBlocks
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.CharP.Algebra

/-!
# The check

The honest run of the check, step by step, through its coins, its slices, its halvings and its
final phase. The later lemmas bound the queries of a run, the soundness of one challenge and the
digests, the masks and the phases of a check on the network with a coalition.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

/-! ## Lockstep steps of the honest network -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} {I O L R α : Type}

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
  right_inv x := by fin_cases x <;> rfl

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E]

/-- A hash output splits into the element of its first bits and its other bits. -/
def hashSplit (K : Constants C E) : HashOutput ≃ E × (Fin 128 → Bool) :=
  (bitsEquiv 256).trans <| ((finSumFinEquiv (m := elementBits) (n := 128)).symm.arrowCongr (Equiv.refl Bool)).trans <|
    (Equiv.sumArrowEquivProdArrow _ _ _).trans <|
      Equiv.prodCongr ((Equiv.arrowCongr (Equiv.refl _) boolBit).trans K.encode.symm) (Equiv.refl _)

omit [Fintype E] in
theorem hashSplit_fst (K : Constants C E) (h : HashOutput) : (hashSplit K h).1 = elementOfHash K h := by
  rfl

theorem card_field (K : Constants C E) : Fintype.card E = 2 ^ elementBits := by
  rw [Fintype.card_congr K.encode]; simp [ZMod.card]

/-- The element of a uniform hash output is uniform. -/
theorem probEvent_elementOfHash (K : Constants C E) (p : E → Prop) [DecidablePred p] :
    Pr{let z ← elementOfHash K <$> ($ᵗ HashOutput)}[p z] = (Finset.univ.filter p).card / Fintype.card E := by
  classical
  rw [prEvent_map, SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter fun h => p (elementOfHash K h)).card = (Finset.univ.filter p).card * 2 ^ 128 := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype,
      Fintype.card_congr ((hashSplit K).subtypeEquiv (p := fun h => p (elementOfHash K h))
        (q := fun z => p z.1) fun h => by simp [hashSplit_fst]),
      Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := p))]
    simp
  have hH : Fintype.card HashOutput = Fintype.card E * 2 ^ 128 := by
    rw [card_field K, Fintype.card_congr (bitsEquiv 256), Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; norm_num [elementBits]
  rw [hcard, hH]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

variable (prims : Primitives)

omit [Algebra Bit E] in
theorem card_zero_one [DecidableEq E] :
    (Finset.univ.filter fun e : E => ¬ (e ≠ 0 ∧ e ≠ 1)).card = 2 := by
  have : (Finset.univ.filter fun e : E => ¬ (e ≠ 0 ∧ e ≠ 1)) = {0, 1} := by
    ext e; simp [or_iff_not_imp_left]
  rw [this, Finset.card_pair zero_ne_one]

/-- A challenge search on a key with no cached expansion fails with probability `(2 / |E|) ^ tries`. -/
theorem probEvent_findChallenge_none [DecidableEq E] (K : Constants C E) (key : HashOutput) :
    ∀ (tries index : ℕ) (s : HashCache C), (∀ i ≥ index, s (.expand key i) = none) →
      Pr{let z ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key tries index)).run s}[z.1 = none] ≤ (2 / Fintype.card E) ^ tries := by
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
    have h2 : (2 : ℝ≥0∞) / Fintype.card E = Pr{let e ← elementOfHash K <$> ($ᵗ HashOutput)}[¬ (e ≠ 0 ∧ e ≠ 1)] := by
      rw [probEvent_elementOfHash, card_zero_one]; norm_cast
    rw [findChallenge, simulateQ_bind, StateT.run_bind, hrun, bind_map_left, pow_succ']
    nth_rewrite 1 [h2]
    rw [prEvent_map]
    refine probEvent_bind_le_mul fun u _ => ?_
    dsimp only
    split
    · simp
    · rename_i h _
      rw [ite_eq_left (by simpa using h)]
      refine ih (index + 1) _ fun i hi => ?_
      rw [QueryCache.cacheQuery_of_ne _ _ (by simp; omega)]
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
      Pr{let z ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        ((List.range' index count).mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run s}[¬ ∀ b < m, z.1.getD b 0 ≠ 0] ≤
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
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun u => ¬ elementOfHash K u ≠ 0) _ fun u _ hu => ?_).trans
      (add_le_add ?_ le_rfl)
    rotate_left
    · have := probEvent_elementOfHash K (fun e => e = 0)
      rw [prEvent_map] at this
      simp only [not_not]
      convert this.le using 2
      · have : (Finset.univ.filter fun e : E => e = 0) = {0} := by ext; simp
        rw [this]; simp
    · simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, prEvent_map]
      refine le_trans (prEvent_mono_of_support _ _ _ fun z _ hz => ?_) (ih (index + 1) (m - 1) _ (by omega) fun i hi => ?_)
      · refine fun hall => hz fun b hb => ?_
        rcases b with _ | b
        · simpa using hu
        · simpa using hall b (by omega)
      · rw [QueryCache.cacheQuery_of_ne _ _ (by simp; omega)]
        exact hs i (by omega)

/-- A fresh query of `H` lands in a set of `S` hash outputs with probability `|S| / 2 ^ 256`. -/
theorem probEvent_hash_fresh_mem {q : Query C} (hq : ¬ IsFixed q) {s : HashCache C} (hs : s q = none)
    (S : Finset HashOutput) :
    Pr{let z ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q)).run s}[z.1 ∈ S] ≤
      S.card / 2 ^ 256 := by
  classical
  rw [simulateQ_hashQuery_run_fresh prims hq hs, prEvent_map, SampleableType.prEvent_uniformSample]
  have hH : Fintype.card HashOutput = 2 ^ 256 := by
    rw [Fintype.card_congr (bitsEquiv 256), Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
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
    ∀ n : ℕ, SameRun prims (OverPermutation.sequenceFin fun _ : Fin (n + 1) => liftComp oa (LocalSpec C))
      (liftComp oa (LocalSpec C) >>= fun b => pure fun _ => b)
  | 0 => by
    simp only [OverPermutation.sequenceFin, pure_bind]
    refine SameRun.bind_right _ fun b => SameRun.of_eq ?_
    congr 1; funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => exact i.elim0
  | n + 1 => by
    rw [OverPermutation.sequenceFin]
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
    SameRun prims (OverPermutation.sequenceFin fun j => liftComp oa (LocalSpec C) >>= B j)
      (liftComp oa (LocalSpec C) >>= fun b => OverPermutation.sequenceFin fun j => B j b) := by
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
    Pr{let z ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (hashQuery q >>= fun key => findChallenge K key challengeTries 0)).run s}[z.1 = none] ≤
      Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries := by
  rw [simulateQ_bind, StateT.run_bind]
  have hev : ∀ mx : ProbComp (Option E × HashCache C),
      Pr{let z ← mx}[z.1 = none] = Pr{let z ← mx}[¬ (z.1 ≠ none)] := fun mx => by simp
  rw [hev]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z : HashOutput × HashCache C => ¬ z.1 ∉ Ks) _
    fun z hz hkey => ?_).trans (add_le_add ?_ le_rfl)
  rotate_left
  · simp only [not_not]
    exact probEvent_hash_fresh_mem prims hq hs Ks
  · rw [not_not] at hkey
    rw [← hev]
    refine probEvent_findChallenge_none prims K z.1 challengeTries 0 z.2 fun i _ => ?_
    by_contra hne
    have hz' := simulateQ_hashQuery_run_fresh prims hq hs ▸ hz
    rw [support_map] at hz'
    obtain ⟨u, -, rfl⟩ := hz'
    by_cases hqi : (Query.expand u i : Query C) = q
    · exact (hq' u i hqi.symm).elim
    · dsimp only at hne hkey
      rw [QueryCache.cacheQuery_of_ne _ _ hqi] at hne
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
    SameRun prims (OverPermutation.sequenceFin fun j => liftComp oa (LocalSpec C) >>= B j)
      (liftComp oa (LocalSpec C) >>= fun b => OverPermutation.sequenceFin fun j => B j b)
  | _ + 1, _, oa, B => sameRun_sequenceFin_common prims oa B

/-- The honest network after a computation `oa` of `H` and `PRG` that every operator runs. A bad
result of `oa` costs its probability, and each other result costs at most `ε`. -/
theorem probEvent_honest_common [Nonempty C.Party] {β : Type} (F : Functionality C I O L R) (reply : L → R)
    (fuel : ℕ) (oa : OracleComp (RoSpec C) β) (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (bad : β × HashCache C → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support ((simulateQ (localAnswer prims) (liftComp oa (LocalSpec C))).run s), ¬ bad z →
      Pr{let y ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i z.1) >>= honestRounds F reply fuel)).run' z.2}[event y] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] ≤
      Pr{let z ← (simulateQ (localAnswer prims) (liftComp oa (LocalSpec C))).run s}[bad z] + ε := by
  have hsame : SameRun prims (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)
      (liftComp oa (LocalSpec C) >>= fun b => honestStart (fun i => g i b) >>= honestRounds F reply fuel) := by
    have hstart : SameRun prims (honestStart fun i => oracleStep oa >>= g i)
        (liftComp oa (LocalSpec C) >>= fun b => honestStart fun i => g i b) := by
      unfold honestStart
      simp only [advance_oracleStep_bind]
      exact sameRun_sequenceFin_common_pos prims (Fin.pos (Classical.arbitrary C.Party)) oa _
    refine (hstart.bind fun _ => SameRun.refl _ _).trans (SameRun.of_eq ?_)
    rw [bind_assoc]
  have hrun : Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] =
      Pr{let z ← (simulateQ (localAnswer prims) (liftComp oa (LocalSpec C) >>= fun b =>
        honestStart (fun i => g i b) >>= honestRounds F reply fuel)).run' s}[event z] := by
    simp only [StateT.run'_eq]
    exact ((hsame s).map _).prEvent_eq _
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prEvent_bind_le_prEvent_add_of_support _ _ _ _ fun z hz hbad => ?_
  have := h z hz hbad
  rwa [StateT.run'_eq] at this

end

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss Finset

noncomputable section

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

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

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

attribute [local instance] inhabitedField

/-- The additive share of operator `i` of product `g` in `F_extendMult`. -/
def extendMultShare (K : Constants C E) (i : C.Party) (products : List (Product C E)) (g : ℕ) : E :=
  match products[g]? with
  | some p => productShare K (localContext i) p
  | none => 0

end

end ThresholdLeanXmssSecurity

/-! ## The program of one operator in the check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

attribute [local instance] Classical.propDecidable

section CheckProgram

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C) (buildingBlocks : CheckBuildingBlocks C E G)

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
    let t ← buildingBlocks.extendMult [.replicated (fun T k => rest k * xs T k) ys half,
      .replicated (fun T k => rest k * (xs T k + xs T (k + half))) (fun T k => ys T k + ys T (k + half)) half]
    let r ← challenge K buildingBlocks
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
    let p ← buildingBlocks.extendMult [.shamir A B half, .shamir (sum A) (sum B) half]
    let r ← challenge K buildingBlocks
    let fold := fun (v : ℕ → E) k => v k + r * (v k + hi v k)
    pure (fold A, fold B, conv K ctx p 0 + (D + conv K ctx p 1) * r + conv K ctx p 1 * r ^ 2)

/-- The randomization of `check` and its final test. -/
def finalStep : (ℕ → E) × (ℕ → E) × E → RunM C E G Unit := fun (A, B, D) => do
  let w ← buildingBlocks.randElements 2
  let wa := conv K ctx w.1 0
  let wb := conv K ctx w.1 1
  let q ← buildingBlocks.extendMult [.shamir (fun _ => wa) (fun _ => wb) 1,
    .shamir (fun _ => wa + A 0) (fun _ => wb + B 0) 1]
  let q₀ := conv K ctx q 0
  let q₂ := conv K ctx q 1
  let salts ← buildingBlocks.randBits 256
  compareDigests ctx salts.1
  let r ← challenge K buildingBlocks
  let opened ← StateT.lift (openSh K ctx (fun k => match k with
    | 0 => wa + r * (wa + A 0)
    | 1 => wb + r * (wb + B 0)
    | _ => q₀ + (D + q₀ + q₂) * r + q₂ * r ^ 2) 3)
  StateT.lift (require (opened 0 * opened 1 = opened 2))

theorem check_eq (tuples : List (Tuple C)) (h : (tuples.map (·.count)).sum ≠ 0) :
    check K ctx buildingBlocks tuples = (do
      let count := (tuples.map (·.count)).sum
      let τ ← expand K (← coinKey K buildingBlocks) (coins count)
      StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
      let p ← (List.range sliceBits).foldlM (sliceStep K ctx buildingBlocks τ count)
        ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k : Shares C E), liftedPart tuples (·.y),
          conv K ctx (claimOf K τ count (liftedPart tuples (·.z))) 0)
      let p' ← (List.range (halvings count - sliceBits)).foldlM
          (halvingStep K ctx buildingBlocks (sliceWidth count))
        (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
      finalStep K ctx buildingBlocks p') := by
  simp only [check, ite_eq_right h]
  rfl

end CheckProgram

end

end ThresholdLeanXmssSecurity

/-! ## The building blocks of the check as steps -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss

noncomputable section

attribute [local instance] Classical.propDecidable

section BuildingBlockSteps

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

omit [Field E] [Algebra Bit E] in
theorem oracleStep_bind {ι : Type} {G : OracleSpec ι} {α β : Type} (oa : OracleComp (RoSpec C) α)
    (ob : α → OracleComp (RoSpec C) β) :
    (oracleStep (C := C) (E := E) (G := G) (oa >>= ob)) = oracleStep oa >>= fun a => oracleStep (ob a) := by
  simp only [oracleStep, localStep, liftComp_bind]
  apply OptionT.ext
  simp [OptionT.run_bind, OptionT.run_lift]

theorem extendMult_run' {α : Type} (products : List (Product C E)) (f : Shares C E → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((hybridCheckBuildingBlocks K i).extendMult products >>= f).run' st =
      call (Sum.inl (Sum.inr products)) >>= fun o => match o with
        | some (.inl (.inr z)) => (f z).run' ⟨recordHistory K i st.history z products.length, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [hybridCheckBuildingBlocks, freshLabel, record, bind_assoc]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift, localContext]
  rfl

theorem randElements_run' {α : Type} (count : ℕ) (f : PrssOutput C E → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((hybridCheckBuildingBlocks K i).randElements count >>= f).run' st =
      call (Sum.inr (Sum.inl count)) >>= fun o => match o with
        | some (.inr (.inl w)) => (f w).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [hybridCheckBuildingBlocks, freshLabel, bind_assoc]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | (w | w)) <;> simp [StateT.run_lift]

theorem randBits_run' {α : Type} (count : ℕ) (f : PrssOutput C Bit → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((hybridCheckBuildingBlocks K i).randBits count >>= f).run' st =
      call (Sum.inr (Sum.inr count)) >>= fun o => match o with
        | some (.inr (.inr w)) => (f w).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [hybridCheckBuildingBlocks, freshLabel, bind_assoc]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | (w | w)) <;> simp [StateT.run_lift]

theorem challenge_run' {α : Type} (f : E → RunM C E (CheckSpec C E) α) (st : RunState C) :
    (challenge K (hybridCheckBuildingBlocks K i) >>= f).run' st =
      call (Sum.inl (Sum.inl 2)) >>= fun o => match o with
        | some (.inl (.inl v)) => oracleStep (challengeQuery K st.tag st.label v) >>= fun r => match r with
          | some r => (f r).run' ⟨st.history, st.label + 1, st.tag⟩
          | none => failure
        | _ => failure := by
  simp only [challenge, coinKey, bind_assoc, hybridCheckBuildingBlocks, freshLabel, challengeQuery,
      oracleStep_bind]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, StateT.run_get]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift]
  refine bind_congr fun key => bind_congr fun r => ?_
  rcases r with _ | r <;> simp [StateT.run_lift]

end BuildingBlockSteps

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
        (OverPermutation.sequenceFin fun i => liftComp (oa i) (LocalSpec C))).run s),
      Pr{let y ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (z.1 i)) >>= honestRounds F reply fuel)).run' z.2}[event y] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε := by
  have hsame : SameRun prims (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)
      ((OverPermutation.sequenceFin fun i => liftComp (oa i) (LocalSpec C)) >>= fun b =>
        honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel) := by
    have hstart : SameRun prims (honestStart fun i => oracleStep (oa i) >>= g i)
        ((OverPermutation.sequenceFin fun i => liftComp (oa i) (LocalSpec C)) >>= fun b => honestStart fun i => g i (b i)) := by
      unfold honestStart
      simp only [advance_oracleStep_bind]
      have h := sameRun_sequenceFin_dep prims (fun i => liftComp (oa i) (LocalSpec C))
        (fun i u => advance (g i u).run) (fun _ _ v => v)
      refine (SameRun.of_eq ?_).trans (h.trans (SameRun.of_eq (bind_congr fun x => bind_pure _)))
      simp only [bind_pure]
    refine (hstart.bind fun _ => SameRun.refl _ _).trans (SameRun.of_eq ?_)
    rw [bind_assoc]
  have hrun : Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] =
      Pr{let z ← (simulateQ (localAnswer prims) ((OverPermutation.sequenceFin fun i => liftComp (oa i) (LocalSpec C)) >>= fun b =>
        honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel)).run' s}[event z] := by
    simp only [StateT.run'_eq]
    exact ((hsame s).map _).prEvent_eq _
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  have := h z hz
  rwa [StateT.run'_eq] at this

theorem require_bind_of {ι : Type} {G : OracleSpec ι} {c : Prop} (hc : c) (f : Unit → PartyM C E G α) :
    require c >>= f = f () := by
  simp [require, hc]

/-- A computation in the local oracles that only samples. -/
def IsLocalProb {β : Type} (oa : OracleComp (LocalSpec C) β) : Prop := ∃ p : ProbComp β, oa = liftComp p _

theorem IsLocalProb.liftComp {β : Type} (p : ProbComp β) : IsLocalProb (C := C) (liftComp p _) := ⟨p, rfl⟩

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

theorem conv_congr (i : C.Party) (xv X : Shares C E) (k : ℕ) (h : ∀ T, i ∈ C.holders T → xv T k = X T k) :
    conv K (localContext i) xv k = conv K (localContext i) X k := by
  unfold conv
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [h T (Finset.mem_filter.mp hT).2]

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
      simpa [QueryCache.cacheQuery_of_ne _ _ h] using hq'
  · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q) = hashAnswer prims q :=
      (simulateQ_query _ _).trans (id_map _)
    rw [h1, hashAnswer_run_cached prims hq hs, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hq'

omit [Fintype E] [DecidableEq E] in
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

omit [Fintype E] [DecidableEq E] in
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
    Pr{let z ← (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag ρ v) (LocalSpec C))).run s}[z.1 = none] ≤
      Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries := by
  rw [simulateQ_localAnswer_liftComp]
  exact probEvent_challenge_none prims K (by rintro ⟨_, h, _⟩; cases h) (fun k i h => by cases h)
    (coinKey_fresh hρ hs tag _) Ks (fun k i h => (hs _ h).1 k i rfl)

omit [Fintype E] [DecidableEq E] in
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

omit [Field E] [Algebra Bit E] in
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

end DigestSteps

section DigestSupport

variable {C : Committee} (prims : Primitives) {σ α : Type}

/-- The steps of a sequence that keep an invariant and a monotone property give them to the whole
sequence. -/
theorem support_sequenceFin_inv [Preorder σ] (Q : σ → Prop) :
    ∀ {n : ℕ} (f : Fin n → StateT σ ProbComp α) (P : Fin n → α → σ → Prop)
      (_hf : ∀ i s, Q s → ∀ z ∈ support ((f i).run s), s ≤ z.2 ∧ Q z.2 ∧ P i z.1 z.2)
      (_hP : ∀ i a s s', P i a s → s ≤ s' → P i a s') (s : σ), Q s →
      ∀ z ∈ support ((OverPermutation.sequenceFin f).run s), s ≤ z.2 ∧ Q z.2 ∧ ∀ i, P i (z.1 i) z.2
  | 0, f, P, hf, hP, s, hs => by
    intro z hz
    simp [OverPermutation.sequenceFin] at hz
    subst hz
    exact ⟨le_rfl, hs, fun i => i.elim0⟩
  | n + 1, f, P, hf, hP, s, hs => by
    intro z hz
    simp only [OverPermutation.sequenceFin, StateT.run_bind, mem_support_bind_iff] at hz
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
    (hz : z ∈ support ((simulateQ (localAnswer prims) (OverPermutation.sequenceFin fun i =>
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
  simp only [recordHistory, ite_eq_left hi, ite_eq_left hj, hh T i hi j hj]
  congr 1
  refine List.flatMap_congr fun g hg => ?_
  have hg' : g < n := List.mem_range.1 (List.mem_filter.1 hg).1
  simp only [Function.comp_apply, hz i T g hi hg', hz j T g hj hg']

omit [Field E] [Algebra Bit E] in
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

omit [Algebra Bit E] in
theorem coinProduct_succ_low (τ : List E) (w a : ℕ) (ha : a < 2 ^ w) :
    coinProduct τ 0 (w + 1) a = coinProduct τ 0 w a := by
  unfold coinProduct
  rw [Finset.prod_range_succ, Nat.testBit_lt_two_pow ha]
  simp

omit [Algebra Bit E] in
theorem coinProduct_succ_high (τ : List E) (w a : ℕ) (ha : a < 2 ^ w) :
    coinProduct τ 0 (w + 1) (2 ^ w + a) = coinProduct τ 0 w a * τ.getD w 0 := by
  unfold coinProduct
  rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha]
  simp only [Bool.not_false, ite_true, zero_add]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.1 hb)]

omit [Algebra Bit E] in
theorem coinProduct_zero_width (τ : List E) (a : ℕ) : coinProduct τ 0 0 a = 1 := by
  simp [coinProduct]

omit [Algebra Bit E] in
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

/-! ## The start of an honest check -/

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss ENNReal Finset

noncomputable section

attribute [local instance] Classical.propDecidable

section StartPhase

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (i : C.Party)

theorem coinKey_expand_run' {α : Type} (count : ℕ) (f : List E → RunM C E (CheckSpec C E) α) (st : RunState C) :
    (coinKey K (hybridCheckBuildingBlocks K i) >>= fun key => expand K key count >>= f).run' st =
      call (Sum.inl (Sum.inl 2)) >>= fun o => match o with
        | some (.inl (.inl v)) => oracleStep (tauQuery K st.tag st.label v count) >>= fun τ =>
            (f τ).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [coinKey, expand, bind_assoc, hybridCheckBuildingBlocks, freshLabel, tauQuery, oracleStep_bind]
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
    · rw [List.getElem?_append_left (by simpa [vector] using hk), ite_eq_left hk]
      simp [vector, hk]
    · rw [List.getElem?_append_right (by simp [vector]; omega), ite_eq_right hk]
      have ih := getD_flatMap_vector_pos F L (k - τ.count)
      rw [List.getD_eq_getElem?_getD] at ih
      simp only [vector, List.length_map, List.length_range] at ih ⊢
      rw [ih]
      rcases flatPos (L.map (·.count)) (k - τ.count) with _ | ⟨m, g⟩ <;> simp

variable {K}

theorem vector_point {R : Type} {c c' : ℕ} {f f' : ℕ → R} (h : vector c f = vector c' f') {g : ℕ} (hg : g < c) :
    f g = f' g := by
  have hc : c = c' := by simpa [vector] using congrArg List.length h
  subst hc
  have := congrArg (·[g]?) h
  simp only [vector, List.getElem?_map, List.getElem?_range hg, Option.map_some, Option.some.injEq] at this
  exact this

end TupleFacts

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
    (h : ∀ x ∈ support mx, Pr{let z ← my x}[q z] ≤ (if p₁ x then 1 else 0) + (if p₂ x then B else 0)) :
    Pr{let z ← mx >>= my}[q z] ≤ Pr{let z ← mx}[p₁ z] + Pr{let z ← mx}[p₂ z] * B := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · refine (mul_le_mul' le_rfl (h x hx)).trans (le_of_eq ?_)
    split_ifs <;> simp [mul_add]
  · simp [prEvent_eq_zero_of_not_mem_support _ hx]

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
      Pr{let z ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key tries index)).run s}[∃ e ∈ S, z.1 = some e] ≤ S.card / (Fintype.card E - 2 : ℕ) := by
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
        simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, Option.some.injEq, exists_eq_right']
        exact le_self_add
      · rename_i h01 _
        refine (ih (index + 1) _ fun i hi => ?_).trans ?_
        swap
        · rw [ite_eq_left (show ¬(elementOfHash K u ≠ 0 ∧ elementOfHash K u ≠ 1) from h01)]
          exact le_add_self
        rw [QueryCache.cacheQuery_of_ne _ _ (by simp; omega)]
        exact hs i (by omega)
    · have hS := probEvent_elementOfHash K (· ∈ S)
      have h01 := probEvent_elementOfHash K (fun e => ¬ (e ≠ 0 ∧ e ≠ 1))
      rw [prEvent_map] at hS h01
      rw [hS, h01, card_zero_one, show (Finset.univ.filter (· ∈ S)) = S by ext; simp]
      obtain ⟨M, hM⟩ : ∃ M, Fintype.card E = M + 2 := ⟨Fintype.card E - 2, by omega⟩
      rw [hM, Nat.add_sub_cancel]
      simpa using (card_add_ratio S.card M (by omega)).le

end ChallengeSoundness

end

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec ThresholdLeanXmss Finset

end

/-! ## Query -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

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

/-- A single random-oracle input consumes one query. -/
theorem hashQuery_queryBound (q : Query C) :
    IsQueryBoundP (hashQuery q) (fun _ => True) 1 := by
  change IsQueryBoundP (liftM (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 1
  exact (isQueryBoundP_query_iff _ _ _).2 (by omega)

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
  change IsQueryBoundP (liftComp (liftComp oa (LocalSpec C)) (PartySpec C E G) >>= pure ∘ some) (PartyCounted (G := G)) n
  rw [← map_eq_bind_pure_comp, isQueryBoundP_map_iff]
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
    RunBound ((hybridCheckBuildingBlocks K i).coin count) 0 := by
  unfold hybridCheckBuildingBlocks
  apply (RunBound.bind (m := 0) RunBound.freshLabel (fun _ => ?_)).mono (by omega)
  apply (RunBound.bind (m := 0) (RunBound.lift (PartyBound.call _)) (fun out => ?_)).mono (by omega)
  split
  · exact RunBound.pure _
  · exact RunBound.lift PartyBound.failure

lemma hybrid_extendMult_queryBound (products : List (Product C E)) :
    RunBound ((hybridCheckBuildingBlocks K i).extendMult products) 0 := by
  unfold hybridCheckBuildingBlocks
  apply (RunBound.bind (m := 0) RunBound.freshLabel (fun _ => ?_)).mono (by omega)
  apply (RunBound.bind (m := 0) (RunBound.lift (PartyBound.call _)) (fun out => ?_)).mono (by omega)
  split
  · exact ((RunBound.record _ _ _ _ _ _).bind (fun _ => RunBound.pure _)).mono (by omega)
  · exact RunBound.lift PartyBound.failure

lemma hybrid_randElements_queryBound (count : ℕ) :
    RunBound ((hybridCheckBuildingBlocks K i).randElements count) 0 := by
  unfold hybridCheckBuildingBlocks
  apply (RunBound.bind (m := 0) RunBound.freshLabel (fun _ => ?_)).mono (by omega)
  apply (RunBound.bind (m := 0) (RunBound.lift (PartyBound.call _)) (fun out => ?_)).mono (by omega)
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

end CheckBounds

end ThresholdLeanXmssSecurity
end

/-! ## Network -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β : Type}

/-- The local budget remaining after the next round or hybrid call. -/
def StepBound (st : Step C E G α) (n : ℕ) : Prop :=
  match st with
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyCounted (E := E) (G := G)) n
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyCounted (E := E) (G := G)) n

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

end NetworkBound

end ThresholdLeanXmssSecurity
end

/-! ## Functionality -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
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

end HybridBounds
end ThresholdLeanXmssSecurity
end

/-! ## Bounds -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The number of terms. -/
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

lemma adversary_bind {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (k : α → OracleComp (LocalSpec C) β) :
    worldRoles.adversary (oa >>= k) = worldRoles.adversary oa >>= fun a => worldRoles.adversary (k a) := by
  change counted (liftComp (oa >>= k) (SimulatorSpec C)) = _
  rw [liftComp_bind, counted_bind]
  rfl

lemma adversary_pure {α : Type} (a : α) :
    worldRoles.adversary (pure a : OracleComp (LocalSpec C) α) = pure a := by
  rfl

end ThresholdLeanXmssSecurity
end

/-! ## Delinearization -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
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
    Pr{let z ←
      (simulateQ (localAnswer prims) (liftComp (challengeQuery K tag label v) (LocalSpec C))).run s}[∃ e ∈ S, z.1 = some e] ≤
      Ks.card / 2 ^ 256 + S.card / (Fintype.card E - 2 : ℕ) := by
  have hq : ¬ IsFixed (C := C) (.coinKey tag label (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  rw [simulateQ_localAnswer_liftComp, challengeQuery, simulateQ_bind, StateT.run_bind]
  have hev : ∀ mx : ProbComp (Option E × HashCache C),
      Pr{let z ← mx}[∃ e ∈ S, z.1 = some e] = Pr{let z ← mx}[¬ ¬ ∃ e ∈ S, z.1 = some e] := fun mx => by simp
  rw [hev]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z : HashOutput × HashCache C => ¬ z.1 ∉ Ks) _
    fun z hz hkey => ?_).trans (add_le_add ?_ le_rfl)
  rotate_left
  · simp only [not_not]
    exact probEvent_hash_fresh_mem prims hq hfresh Ks
  · rw [not_not] at hkey
    rw [← hev]
    refine probEvent_findChallenge_mem prims K z.1 S challengeTries 0 z.2 fun i _ => ?_
    by_contra hne
    rcases support_hashQuery_entries prims hq s z hz _ hne with h | h
    · exact hkey (hexp _ i h)
    · cases h

/-- An injectively encoded fresh sample hits at most one value per earlier query. -/
theorem probEvent_uniform_injective_mem {α β : Type} [Fintype α] [Nonempty α] [SampleableType α]
    (f : α → β) (hf : Function.Injective f) (Q : Finset β) :
    Pr{let a ← $ᵗ α}[f a ∈ Q] ≤ Q.card / (Fintype.card α : ℕ) := by
  rw [SampleableType.prEvent_uniformSample]
  have hc : (univ.filter fun a => f a ∈ Q).card ≤ Q.card := by
    exact Finset.card_le_card_of_injOn f (fun a ha => (Finset.mem_filter.mp ha).2) (fun a _ b _ h => hf h)
  gcongr

lemma coin_input_injective (K : Constants C E) (tag label : ℕ) :
    Function.Injective (fun v : Fin 2 → E => Query.coinKey (C := C) tag label
      ((List.ofFn v).flatMap fun v => List.ofFn (K.encode v))) := by
  intro a b hab
  have h := (Query.coinKey.inj hab).2.2
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at h
  obtain ⟨h0, h1⟩ := List.append_inj h (by simp only [List.length_ofFn])
  funext i
  fin_cases i
  · exact K.encode.injective (List.ofFn_injective h0)
  · exact K.encode.injective (List.ofFn_injective h1)

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
  let : CharP E 2 := charP_two
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
  · simp only [hc,not_true_eq_false,ite_false]
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
  · simp only [hc,not_true_eq_false,ite_false]
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
    simp only [Function.comp_def,ite_eq_right (unknown_no_corrupt_filler K D T hT _ _)]
  exact (hzero i hi).trans (hzero j hj).symm

/-- Common differences on unknown terms, with zero difference on every known term. -/
def HiddenDifference (D : C.Coalition) (a b : C.Party → Shares C E) : Prop :=
  ∃ delta : Shares C E, (∀ T, KnownTo D.1 T → ∀ g, delta T g = 0) ∧
    ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g, a i T g-b i T g = delta T g

lemma HiddenDifference.conv (K : Constants C E) (D : C.Coalition)
    {a b : C.Party → Shares C E} (h : HiddenDifference D a b) (g : ℕ) :
    ShamirDifference K D (fun i => ThresholdLeanXmss.conv K (localContext i) (a i) g)
      (fun i => ThresholdLeanXmss.conv K (localContext i) (b i) g) := by
  obtain ⟨delta,hknown,hdiff⟩ := h
  apply ShamirDifference.of_conv K D _ _ delta g hknown
  intro i hi
  unfold ThresholdLeanXmss.conv
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  apply Finset.sum_congr rfl
  intro T hT
  rw [hdiff i hi T (by simpa [localContext] using (Finset.mem_filter.mp hT).2)]

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
  let : CharP E 2 := charP_two
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (norm := ring_nf) (a*b*r)*two

end ThresholdLeanXmssSecurity
end

/-! ## Late local -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

lemma sameRun_liftComp_of_evalDist (prims : Primitives) {α : Type} (p q : ProbComp α)
    (h : p =ᵈ q) :
    SameRun (C := C) prims (liftComp p (LocalSpec C)) (liftComp q (LocalSpec C)) := by
  intro s
  rw [run_liftComp_prob,run_liftComp_prob]
  exact h.map _

end ThresholdLeanXmssSecurity
end

/-! ## Digest commit -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- One actual two-level salted digest, before it is inserted in the message vector. -/
def saltedDigestAnswer (prims : Primitives) (salt history : List Bit) :
    StateT (HashCache C) ProbComp HashOutput := do
  let h ← hashAnswer prims (.history history)
  hashAnswer prims (.digest salt h)

end ThresholdLeanXmssSecurity
end

/-! ## Lockstep -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
    _ = OverPermutation.sequenceFin (fun i => pure (callSteps D input f i)) := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1 <;> simp only [hi,ite_true,ite_false,callSteps]
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
  rw [startSteps_call,pure_bind,executeRounds,ite_eq_right hn]
  simp only [stepRound,ite_eq_left hc,hin,bind_assoc,pure_bind]
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

end ThresholdLeanXmssSecurity
end

/-! ## Sum calls -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
  rw [ite_eq_right (not_not.mpr (hfull (fun i => (Sum.inl (inputs i) : I₁ ⊕ I₂)))),
    ite_eq_right (not_not.mpr (hfull inputs))]
  simp only [Functionality.sum]
  rw [ite_eq_left hl]
  simp only [hin, simulateQ_map, StateT.run_map, bind_map_left, map_bind, map_pure]
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
    simp [StateT.run_bind,localRoles]
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
  rw [ite_eq_right (not_not.mpr (hfull (fun i => (Sum.inr (inputs i) : I₁ ⊕ I₂)))),
    ite_eq_right (not_not.mpr (hfull inputs))]
  simp only [Functionality.sum]
  rw [ite_eq_right hn,ite_eq_left hl]
  simp only [hin, simulateQ_map, StateT.run_map, bind_map_left, map_bind, map_pure]
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
    simp [StateT.run_bind,localRoles]
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
    _ = OverPermutation.sequenceFin (fun i => pure (optionalCallSteps D input f i)) := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [hi,optionalCallSteps]
      · cases hv : input i <;>
          simp only [hi,ite_false,hv,optionalCall,optionalCallSteps,localRoles,advance_run_failure,advance_call_bind]
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
    rw [startSteps_optionalCall,pure_bind,executeRounds,ite_eq_right hn]
    simp only [stepRound,ite_eq_left hc,hin,bind_assoc,pure_bind]
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
      simp only [runFunctionality,ite_eq_left hnfull,pure_bind]
      apply congrArg (fun start => start >>= executeRounds localRoles D A F fuel st)
      unfold startSteps
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [optionalCallSteps,hi]
      · cases he : input i <;>
          simp only [optionalCallSteps,hi,ite_false,he,localRoles,hf i hi,advance_run_failure]
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
    simp only [runFunctionality,ite_eq_left hnfull,pure_bind]
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

end ThresholdLeanXmssSecurity
end

/-! ## Check phases -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
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
      (fun i => ((hybridCheckBuildingBlocks K i).extendMult (products i) >>= f i).run' (hs i)) = (do
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
      (fun i => (challenge K (hybridCheckBuildingBlocks K i) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (leftAdversary (leftAdversary A)) (Fcoin (E := E)) st
        (fun i => if i ∈ D.1 then none else some 2)
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
    _ = OverPermutation.sequenceFin (fun i => pure (optionalExchangeSteps D outbox f i)) := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [hi,optionalExchangeSteps]
      · cases hv : outbox i <;>
          simp only [hi,ite_false,hv,optionalExchange,optionalExchangeSteps,localRoles,
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
  rw [startSteps_optionalExchange,pure_bind,executeRounds,ite_eq_right hn]
  simp only [stepRound,ite_eq_right hc,hout,localRoles,bind_assoc,pure_bind]
  apply bind_congr
  intro p
  apply congrArg (fun start => start >>= executeRounds localRoles D A F fuel p.1)
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [optionalExchangeSteps,hi]
  · cases he : outbox i with
    | none => simp only [optionalExchangeSteps,hi,ite_false,he,afterExchange,advance_run_failure]
    | some v =>
        simp only [optionalExchangeSteps,hi,ite_false,he]
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
variable {C : Committee}

/-- An unobserved local computation can be prefetched, even when it changes the oracle cache. -/
theorem local_prefetch_output (prims : Primitives) {α β : Type}
    (probe : OracleComp (LocalSpec C) β) (oa : OracleComp (LocalSpec C) α) (s : HashCache C) :
    (simulateQ (localAnswer prims) (probe >>= fun _ => oa)).run' s =ᵈ
      (simulateQ (localAnswer prims) oa).run' s := by
  have h := sameRun_swap prims probe oa (fun _ a => pure a) s
  simp only [bind_pure] at h
  have hp := h.map Prod.fst
  rw [StateT.run'_eq]
  refine hp.trans ?_
  simp only [simulateQ_bind,simulateQ_pure,StateT.run_bind,StateT.run_pure,map_bind,map_pure]
  rw [StateT.run'_eq,map_eq_bind_pure_comp]
  simp only [Function.comp_def]
  refine EvalDistEq.bind_right _ fun p => ?_
  exact OracleComp.EvalDistEq.bind_const _ _

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
        simp
      rw [hl]
      congr 1

lemma localHybridImpl_leak (A : Adversary C E Ia L R) (l : L) :
    simulateQ (localHybridImpl A) (leak (C := C) l) =
      StateT.mk (fun st => (fun p => (p.2,p.1)) <$> A.answer st l) := by
  unfold leak
  erw [simulateQ_query]
  change (fun r : R => r) <$> localHybridImpl A (.inr l) = _
  rw [id_map']
  refine congrArg StateT.mk (funext fun st => ?_)
  exact (map_eq_bind_pure_comp (OracleComp (LocalSpec C)) _ _).symm

lemma runFunctionality_local (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (st : A.State) (inputs : C.Party → Option I)
    (h : ∀ i,i ∉ D.1 → (inputs i).isSome) :
    runFunctionality localRoles D A F st inputs =
      (fun p => (p.2,p.1)) <$> ((simulateQ (localHybridImpl A) (F.run D inputs)).run st) := by
  unfold runFunctionality
  rw [ite_eq_right (not_not.mpr h)]
  simp only
  exact (map_eq_bind_pure_comp _ _ _).symm

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

lemma randShares_hiddenDifference (D : C.Coalition) (count : ℕ) (known : Shares C E)
    (a b : C.Term → Fin count → E) :
    HiddenDifference D (randShares D count known a) (randShares D count known b) := by
  refine ⟨fun T g => if KnownTo D.1 T then 0 else
    if h : g < count then a T ⟨g,h⟩-b T ⟨g,h⟩ else 0,?_,?_⟩
  · intro T hT g
    simp [hT]
  · intro i hi T hT g
    unfold randShares
    simp only [ite_eq_left hT]
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

end ThresholdLeanXmssSecurity
end

/-! ## Trace guess -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- A uniform secret hits an arbitrary independent query trace with probability at most q/card. -/
theorem independent_trace_guess_bound {α β : Type} [Fintype α] [Nonempty α] [SampleableType α]
    (encode : α → β) (hinj : Function.Injective encode) (trace : ProbComp (List β)) (q : ℕ)
    (htrace : ∀ l ∈ support trace,l.length ≤ q) :
    Pr{let p : List β × α ← (do
      let l ← trace
      let a ← $ᵗ α
      pure (l,a))}[encode p.2 ∈ p.1] ≤ (q : ℝ≥0∞) / Fintype.card α := by
  classical
  let : DecidableEq β := Classical.typeDecidableEq β
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun l hl => ?_
  have he : (do let a ← $ᵗ α; pure (l,a)) = (fun a => (l,a)) <$> ($ᵗ α) :=
    (map_eq_bind_pure_comp (m := ProbComp) _ _).symm
  rw [he,prEvent_map]
  have h := probEvent_uniform_injective_mem encode hinj l.toFinset
  simp only [List.mem_toFinset] at h
  refine h.trans ?_
  gcongr
  exact (List.toFinset_card_le _).trans (htrace l hl)

/-- Fresh 256-bit salts are protected against every digest input in the independent trace;
there is no restriction at all on history inputs. -/
theorem independent_salt_trace_bound (trace : ProbComp (List (List Bit))) (q : ℕ)
    (htrace : ∀ l ∈ support trace,l.length ≤ q) :
    Pr{let p : List (List Bit) × (Fin 256 → Bit) ← (do
      let l ← trace
      let salt ← $ᵗ (Fin 256 → Bit)
      pure (l,salt))}[List.ofFn p.2 ∈ p.1] ≤ (q : ℝ≥0∞) / 2^256 := by
  have h := independent_trace_guess_bound (fun s : Fin 256 → Bit => List.ofFn s)
    List.ofFn_injective trace q htrace
  simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat] using h

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

def finalOpenProgram (K : Constants C E) (i : C.Party) (v : ℕ → E) :
    PartyM C E (CheckSpec C E) Unit := do
  let opened ← openSh K (localContext i) v 3
  require (opened 0*opened 1=opened 2)

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

lemma final_residual_card_le_two (a b d e0 e2 : E) (hwrong : d ≠ a*b) :
    (univ.filter fun r : E => r*(d-a*b)+(1+r)*e0+r*(1+r)*e2=0).card ≤ 2 := by
  apply card_filter_le_two_of_quadratic e0 (d-a*b+e0+e2) e2
  · by_contra! h
    obtain ⟨h0,h1,h2⟩ := h
    apply hwrong
    linear_combination h1-h0-h2
  · intro r hr
    linear_combination hr

end ThresholdLeanXmssSecurity
end

/-! ## Terminal -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
      _ = OverPermutation.sequenceFin (fun i => pure (Step.done (if i ∈ D.1 then none else out i))) := by
        congr 1
        funext i
        by_cases hi : i ∈ D.1
        · simp [hi]
        · cases ho : out i <;>
            simp only [hi,ite_false,ho,terminalProgram,localRoles,advance_run_failure,advance_run_pure]
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
    by_cases hi : live i <;> simp only [out,f,hi,ite_true,ite_false,optionalExchange,finalOpenProgram_exchange]
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
        simp only [Bool.false_eq_true,ite_false,f,require_require_terminal,finalRoundAccept,
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

end ThresholdLeanXmssSecurity
end

/-! ## Challenge order -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {α β γ : Type}

def SameLocalOutput (prims : Primitives) (a b : OracleComp (LocalSpec C) α) : Prop :=
  ∀ s : HashCache C,(simulateQ (localAnswer prims) a).run' s =ᵈ
    (simulateQ (localAnswer prims) b).run' s

lemma SameLocalOutput.of_sameRun (prims : Primitives) {a b : OracleComp (LocalSpec C) α}
    (h : SameRun prims a b) : SameLocalOutput prims a b := by
  intro s
  simp only [StateT.run'_eq]
  exact (h s).map _

lemma SameLocalOutput.bind_right (prims : Primitives) (oa : OracleComp (LocalSpec C) α)
    {f g : α → OracleComp (LocalSpec C) β} (h : ∀ a,SameLocalOutput prims (f a) (g a)) :
    SameLocalOutput prims (oa >>= f) (oa >>= g) := by
  intro s
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
  refine EvalDistEq.bind_right _ fun p => ?_
  exact h p.1 p.2

end ThresholdLeanXmssSecurity
end

/-! ## Until digest -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
    letI : MeasurableSpace (α × σ) := ⊤
    measureTVDist ((simulateQ impl₁ oa).run s) ((simulateQ impl₂ oa).run s) ≤
      Pr{let z : α × σ × Bool ←
        (simulateQ (flagQueries impl₁ bad) oa).run (s,false)}[z.2.2=true].toReal := by
  let : MeasurableSpace (α × σ) := ⊤
  have hag : ∀ t (p : σ × Bool),¬ p.2=true → ∀ q : S.Range t × σ × Bool → Prop,
      Pr{let z ← (flagQueries impl₁ bad t).run p}[q z ∧ ¬ z.2.2=true] =
      Pr{let z ← (flagQueries impl₂ bad t).run p}[q z ∧ ¬ z.2.2=true] := by
    intro t p _ q
    cases hb : bad t with
    | false => simp only [flagQueries_run,heq t p.1 hb]
    | true =>
      have hz : ∀ (impl : QueryImpl S (StateT σ ProbComp)),
          Pr{let z ← (flagQueries impl bad t).run p}[q z ∧ ¬ z.2.2=true] = 0 := by
        intro impl
        refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hq => ?_
        simp only [flagQueries_run,support_map,Set.mem_image] at hz
        obtain ⟨x,_,rfl⟩ := hz
        simp [hb] at hq
      rw [hz impl₁,hz impl₂]
  have hgood := ProgramLogic.Relational.prEvent_simulateQ_run_and_not_bad_eq (flagQueries impl₁ bad)
    (flagQueries impl₂ bad) (fun p => p.2=true) hag (flagQueries_mono impl₁ bad) (flagQueries_mono impl₂ bad)
    oa (s,false)
  have hbad := ProgramLogic.Relational.prEvent_simulateQ_run_bad_eq (flagQueries impl₁ bad)
    (flagQueries impl₂ bad) (fun p => p.2=true) hag (flagQueries_mono impl₁ bad) (flagQueries_mono impl₂ bad)
    oa (s,false)
  have h := measureETVDist_map_le_prEvent_of_agree
    ((simulateQ (flagQueries impl₁ bad) oa).run (s,false))
    ((simulateQ (flagQueries impl₂ bad) oa).run (s,false))
    (fun z : α × σ × Bool => (z.1,z.2.1)) (fun z => z.2.2=true) hgood hbad.ge
  rw [flagQueries_forget,flagQueries_forget] at h
  rw [measureTVDist_eq_toReal_measureETVDist]
  exact ENNReal.toReal_mono (prEvent_ne_top _) h

variable {C : Committee}

/-- Only outer digests at this salt are protected; histories are unrestricted. -/
def digestSaltHit (salt : List Bit) : (LocalSpec C).Domain → Bool
  | .inr (.inl (.digest s _)) => decide (s=salt)
  | _ => false

end ThresholdLeanXmssSecurity
end

/-! ## Salt trace -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
      by_cases hc : charged t <;> simp only [hc,ite_true,ite_false] at hb <;> omega
    | some b =>
      have hc := hproject t (by simp [hp])
      simp only [hp,Option.toList_some,List.singleton_append,List.length_cons,hc,ite_true] at hb
      rcases hpos with hn | hn
      · exact False.elim (hn hc)
      · omega

lemma projectQueries_flag (impl : QueryImpl S (StateT σ ProbComp)) (project : ι → Option β)
    (a : β) (oa : OracleComp S α) (s : σ) (l : List β) :
    (fun z : α × σ × List β => (z.1,(z.2.1,decide (a ∈ z.2.2)))) <$>
      (simulateQ (projectQueries impl project) oa).run (s,l) =
    (simulateQ (flagQueries impl (fun t => decide (project t=some a))) oa).run (s,decide (a ∈ l)) := by
  let : DecidableEq β := Classical.typeDecidableEq β
  induction oa using OracleComp.inductionOn generalizing s l with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,projectQueries_run,
      flagQueries_run,bind_map_left,map_bind]
    apply bind_congr
    intro p
    rw [ih]
    congr 1
    cases hp : project t <;> simp [List.mem_cons,eq_comm,Bool.or_comm] <;> rfl

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

end ThresholdLeanXmssSecurity
end

/-! ## Digest programmed -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
      exact QueryCache.cacheQuery_comm s (Ne.symm hne) _ _
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
  · simp only [patchedDigestHash,ite_eq_right hq]
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
    letI : MeasurableSpace α := ⊤
    measureTVDist ((simulateQ (localAnswer prims) oa).run' s)
      ((simulateQ (localAnswer prims) oa).run' (s.cacheQuery (.digest salt h) d)) ≤
      Pr{let z : α × HashCache C × Bool ←
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) oa).run (s,false)}[z.2.2=true].toReal := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace (α × HashCache C) := ⊤
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
  exact (measureTVDist_map_le _ _ Prod.fst measurable_from_top).trans hb

end ThresholdLeanXmssSecurity
end

/-! ## Digest hide -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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

end ThresholdLeanXmssSecurity
end

/-! ## Digest hide cache -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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

end ThresholdLeanXmssSecurity
end

/-! ## Salt projected -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {α : Type}

/-- The adaptive query trace is independent of a freshly chosen hidden salt. -/
theorem digestSaltFlag_boundP (prims : Primitives) (oa : OracleComp (LocalSpec C) α)
    (s : HashCache C) (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : IsQueryBoundP oa charged q) :
    Pr{let z : α × HashCache C × Bool ← (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false))}[z.2.2=true] ≤
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
      Pr{let z : α × HashCache C × Bool ←
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false)}[z.2.2=true] =
      Pr{let l ← trace}[List.ofFn salt ∈ l] := by
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
    rw [he',prEvent_map]
    simp only [trace,prEvent_map,decide_eq_true_eq]
  have he : Pr{let z : α × HashCache C × Bool ← (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (s,false))}[z.2.2=true] =
      Pr{let p : List (List Bit) × (Fin 256 → Bit) ← (do
        let l ← trace; let salt ← $ᵗ (Fin 256 → Bit); pure (l,salt))}[List.ofFn p.2 ∈ p.1] := by
    have hswap : (do let l ← trace; let salt ← $ᵗ (Fin 256 → Bit); pure (l,salt) :
        ProbComp (List (List Bit) × (Fin 256 → Bit))) =ᵈ
        (do let salt ← $ᵗ (Fin 256 → Bit); let l ← trace; pure (l,salt)) :=
      OracleComp.EvalDistEq.bind_bind_swap _ _ _
    rw [hswap.prEvent_eq]
    refine prEvent_bind_congr _ _ _ _ _ fun salt => ?_
    have hm : (do let l ← trace; pure (l,salt) : ProbComp (List (List Bit) × (Fin 256 → Bit))) =
        (fun l => (l,salt)) <$> trace := (map_eq_bind_pure_comp ProbComp _ _).symm
    rw [hp salt]
    exact ((congrArg (fun m : ProbComp (List (List Bit) × (Fin 256 → Bit)) =>
      Pr{let p ← m}[List.ofFn p.2 ∈ p.1]) hm).trans (prEvent_map _ _ _)).symm

  rw [he]
  exact hb

end ThresholdLeanXmssSecurity
end

/-! ## Digest projected -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {α : Type}

/-- Programming a digest at an independent hidden salt costs at most q/2^256,
even if its inner hash and programmed value depend on that salt. -/
theorem hidden_digest_programming_boundP (prims : Primitives) (cache : HashCache C)
    (h d : (Fin 256 → Bit) → HashOutput) (oa : OracleComp (LocalSpec C) α)
    (charged : (LocalSpec C).Domain → Prop) [DecidablePred charged]
    (hproject : ∀ t,(digestSaltProjection t).isSome → charged t)
    (q : ℕ) (hq : IsQueryBoundP oa charged q) :
    letI : MeasurableSpace α := ⊤
    measureTVDist (do
        let _salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (localAnswer prims) oa).run' cache)
      (do
        let salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (localAnswer prims) oa).run'
          (cache.cacheQuery (.digest (List.ofFn salt) (h salt)) (d salt))) ≤
      (q : ℝ)/2^256 := by
  let : MeasurableSpace α := ⊤
  let prob := fun salt : Fin 256 → Bit =>
    Pr{let z : α × HashCache C × Bool ←
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (cache,false)}[z.2.2=true]
  have hb := measureTVDist_bind_left_le_tsum ($ᵗ (Fin 256 → Bit))
    (fun _ => (simulateQ (localAnswer prims) oa).run' cache)
    (fun salt => (simulateQ (localAnswer prims) oa).run'
      (cache.cacheQuery (.digest (List.ofFn salt) (h salt)) (d salt)))
  simp only [tsum_fintype] at hb
  have hsum : (∑ salt : Fin 256 → Bit,Pr{let z ← $ᵗ (Fin 256 → Bit)}[z = salt].toReal * (prob salt).toReal) =
      Pr{let z : α × HashCache C × Bool ← (do
        let salt ← $ᵗ (Fin 256 → Bit)
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) oa).run (cache,false))}[z.2.2=true].toReal := by
    rw [OracleComp.prEvent_bind_eq_tsum,tsum_fintype,ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul,prob]
    · intro salt _
      exact ENNReal.mul_ne_top (prEvent_ne_top _) (prEvent_ne_top _)
  calc
    _ ≤ ∑ salt : Fin 256 → Bit,Pr{let z ← $ᵗ (Fin 256 → Bit)}[z = salt].toReal * (prob salt).toReal := by
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
    letI : MeasurableSpace α := ⊤
    measureTVDist (digestProgrammedGame prims cache h k) (digestGhostGame prims cache k) ≤ (q : ℝ)/2^256 := by
  let : MeasurableSpace α := ⊤
  let programmed : ProbComp α := do
    let d ← $ᵗ HashOutput
    let salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run' (cache.cacheQuery (.digest (List.ofFn salt) h) d)
  let ghost : ProbComp α := do
    let d ← $ᵗ HashOutput
    let _salt ← $ᵗ (Fin 256 → Bit)
    (simulateQ (localAnswer prims) (k d)).run' cache
  have hr : digestProgrammedGame prims cache h k =ᵈ programmed :=
    OracleComp.EvalDistEq.bind_bind_swap _ _ _
  have hg : ghost =ᵈ digestGhostGame prims cache k :=
    EvalDistEq.bind_right _ fun d => OracleComp.EvalDistEq.bind_const _ _
  have hb : measureTVDist ghost programmed ≤ (q : ℝ)/2^256 := by
    refine measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity) fun d => ?_
    exact hidden_digest_programming_boundP prims cache (fun _ => h) (fun _ => d) (k d) charged hproject q (hq d)
  change measureTVDist (digestProgrammedGame prims cache h k) (digestGhostGame prims cache k) ≤ _
  rw [measureTVDist_comm] at hb
  unfold measureTVDist at hb ⊢
  rw [hr.evalDist_eq,← hg.evalDist_eq]
  exact hb

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
    letI : MeasurableSpace α := ⊤
    measureTVDist
      (do let salt ← $ᵗ (Fin 256 → Bit)
          (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
            simulateQ (localAnswer prims) (k d)).run' cache)
      (digestGhostGame prims cache k) ≤ ((seen.card+q : ℕ) : ℝ)/2^256 := by
  let : MeasurableSpace α := ⊤
  let actual : (Fin 256 → Bit) → ProbComp α := fun salt =>
    (saltedDigestAnswer prims (List.ofFn salt) history >>= fun d =>
      simulateQ (localAnswer prims) (k d)).run' cache
  let overwrite : (Fin 256 → Bit) → ProbComp α := fun salt => do
    let d ← $ᵗ HashOutput
    (simulateQ (localAnswer prims) (k d)).run' (cache.cacheQuery (.digest (List.ofFn salt) h) d)
  have hstep : ∀ salt,List.ofFn salt ∉ seen → actual salt =ᵈ overwrite salt := by
    intro salt hs
    have he : actual salt=overwrite salt := by
      simp only [actual,overwrite,StateT.run'_eq,StateT.run_bind]
      rw [saltedDigestAnswer_fresh prims cache (List.ofFn salt) history h hh (hf salt hs)]
      simp only [bind_map_left,map_bind]
    rw [he]
  have hb := measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ (Fin 256 → Bit)) actual overwrite
    (fun salt => List.ofFn salt ∈ seen) hstep
  have hguess : Pr{let salt : Fin 256 → Bit ← $ᵗ (Fin 256 → Bit)}[List.ofFn salt ∈ seen].toReal ≤
      (seen.card : ℝ)/2^256 := by
    have hg := probEvent_uniform_injective_mem (fun salt : Fin 256 → Bit => List.ofFn salt)
      List.ofFn_injective seen
    have hgr := ENNReal.toReal_mono (by finiteness) hg
    simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat,
      ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using hgr
  have hc := digestProgrammedGame_boundP prims cache h k charged hproject q hq
  have ht := measureTVDist_triangle (($ᵗ (Fin 256 → Bit)) >>= actual)
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
      (fun i => ((hybridCheckBuildingBlocks K i).randElements (count i) >>= f i).run' (hs i)) = (do
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
      (fun i => ((hybridCheckBuildingBlocks K i).randBits (count i) >>= f i).run' (hs i)) = (do
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

end ThresholdLeanXmssSecurity
end

/-! ## Mask phase -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable inhabitedField
variable {C : Committee} {E Ia α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

lemma sameRun_discard_sample (prims : Primitives) {β γ : Type} [SampleableType β]
    (oa : OracleComp (LocalSpec C) γ) :
    SameRun prims (liftComp ($ᵗ β) (LocalSpec C) >>= fun _ => oa) oa := by
  intro s
  simp only [simulateQ_bind,StateT.run_bind,run_liftComp_prob,bind_map_left]
  exact OracleComp.EvalDistEq.bind_const ($ᵗ β) _

/-- The actual final mask phase reduces to the chosen known terms and one fresh hidden table;
the unused PRSS pair table has no effect on the entire adaptive continuation. -/
theorem executePhase_randElements_first (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (count : ℕ)
    (hs : C.Party → RunState C) (f : C.Party → Shares C E → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
        (fun i => ((hybridCheckBuildingBlocks K i).randElements count >>= fun w => f i w.1).run' (hs i)))
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
  simp only [afterRandom,randFinish,ite_eq_right hi]
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
      (fun i => ((hybridCheckBuildingBlocks K i).extendMult
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
          let w ← (hybridCheckBuildingBlocks K i).randElements 2
          let q ← (hybridCheckBuildingBlocks K i).extendMult (maskedProducts K A B i w.1)
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
    (fun i w => (hybridCheckBuildingBlocks K i).extendMult (maskedProducts K A B i w) >>= f i w)).trans ?_
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
  rw [runFunctionality,ite_eq_left hnone,pure_bind]
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
      (fun i => if live i then ((hybridCheckBuildingBlocks K i).randBits count >>= f i).run' (hs i) else
          failure) =
      pure (st,fun _ => none) := by
  let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) α := fun i o => match o with
    | some (.inr (.inr w)) => (f i w).run' ⟨(hs i).history,(hs i).label+1,(hs i).tag⟩
    | _ => failure
  have hp : (fun i => if live i then ((hybridCheckBuildingBlocks K i).randBits count >>= f i).run' (hs i) else failure) =
      (fun i => optionalCall (if live i then some (.inr (.inr count)) else none) (next i)) := by
    funext i
    by_cases hi : live i <;> simp only [hi,ite_true,ite_false,optionalCall,randBits_run',next]
    apply bind_congr
    intro o
    rcases o with _ | ((a | b) | (c | d)) <;> rfl
  rw [hp]
  apply executePhase_partialCall_abort
  · intro i hi; rfl
  · obtain ⟨i,hi,hl⟩ := hmissing
    exact ⟨i,hi,ite_eq_right hl⟩

end ThresholdLeanXmssSecurity
end

/-! ## Ro selected -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {β : Type}

lemma sequenceFin_select_none {n : ℕ} (oa : OracleComp (LocalSpec C) β) (pick : Fin n → Prop)
    (fallback : β) (hn : ¬∃ i,pick i) :
    OverPermutation.sequenceFin (fun i => if pick i then oa else pure fallback) = pure (fun _ => fallback) := by
  have hp : (fun i => if pick i then oa else pure fallback) = fun _ => pure fallback := by
    funext i
    exact ite_eq_right (fun hi => hn ⟨i,hi⟩)
  rw [hp,sequenceFin_pure]

/-- A shared deterministic oracle computation is performed once for its honest holders.
This also covers nonholders and corrupt slots, whose entries are fixed fallbacks. -/
theorem sameRun_sequenceFin_selected (prims : Primitives) (oa : OracleComp (RoSpec C) β)
    (fallback : β) : ∀ {n : ℕ} (pick : Fin n → Prop), (∃ i,pick i) →
    SameRun prims (OverPermutation.sequenceFin (fun i => if pick i then liftComp oa (LocalSpec C) else pure fallback))
      (do let v ← liftComp oa (LocalSpec C); pure (fun i => if pick i then v else fallback))
  | 0,pick,h => by obtain ⟨i,_⟩ := h; exact i.elim0
  | n+1,pick,h => by
    rw [OverPermutation.sequenceFin]
    by_cases hrest : ∃ i : Fin n,pick i.succ
    · have hi := sameRun_sequenceFin_selected prims oa fallback (fun i : Fin n => pick i.succ) hrest
      refine (SameRun.bind_right _ fun v => hi.bind (fun rest => SameRun.refl prims (pure (Fin.cases (motive := fun _ => β) v rest)))).trans ?_
      simp only [bind_assoc,pure_bind]
      by_cases hzero : pick 0
      · simp only [ite_eq_left hzero]
        refine (sameRun_ro_dup prims oa (fun a b => pure (Fin.cases (motive := fun _ => β) a (fun i => if pick i.succ then b else fallback)))).trans ?_
        apply SameRun.of_eq
        apply bind_congr
        intro v
        congr 1
        funext i
        cases i using Fin.cases <;> simp [hzero]
      · simp only [ite_eq_right hzero,pure_bind]
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
      rw [ite_eq_left hzero,sequenceFin_select_none _ (fun i : Fin n => pick i.succ) fallback hrest]
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
variable {C : Committee} {α β : Type} {n : ℕ}

def queryColumns (f : Fin n → α → OracleComp (LocalSpec C) β) :
    List α → OracleComp (LocalSpec C) (Fin n → List β)
  | [] => pure (fun _ => [])
  | a::as => do
    let head ← OverPermutation.sequenceFin (fun i => f i a)
    let tail ← queryColumns f as
    pure (fun i => head i::tail i)

/-- Independent local query rows can be evaluated by columns without changing their answers or cache. -/
theorem sameRun_queryColumns (prims : Primitives)
    (f : Fin n → α → OracleComp (LocalSpec C) β) (as : List α) :
    SameRun prims (OverPermutation.sequenceFin (fun i => as.mapM (f i))) (queryColumns f as) := by
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

end ThresholdLeanXmssSecurity
end

/-! ## Local fallback -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E I O Ia L R α β : Type} 

/-- The honest local oracle computations can precede every honest continuation, with the
same final oracle cache. Corrupt programs are not run. -/
theorem startSteps_local_fallback (prims : Primitives) (D : C.Coalition)
    (oa : C.Party → OracleComp (LocalSpec C) β) (fallback : C.Party → β)
    (f : C.Party → β → PartyM C E (CallSpec I O) α) :
    SameRun prims (startSteps localRoles D (fun i => localStep (oa i) >>= f i))
      (do
        let v ← OverPermutation.sequenceFin (fun i => if i ∈ D.1 then pure (fallback i) else oa i)
        startSteps localRoles D (fun i => f i (v i))) := by
  let queries : C.Party → OracleComp (LocalSpec C) β := fun i => if i ∈ D.1 then pure (fallback i) else oa i
  let next : C.Party → β → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) :=
    fun i b => if i ∈ D.1 then pure (.done none) else advance (f i b).run
  have hn : startSteps localRoles D (fun i => localStep (oa i) >>= f i) =
      OverPermutation.sequenceFin (fun i => queries i >>= fun b => next i b >>= fun v => pure v) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;>
      simp only [queries,next,hi,ite_true,ite_false,pure_bind,bind_pure,localRoles,advance_localStep_bind]
  rw [hn]
  have hh := sameRun_sequenceFin_dep prims queries next (fun _ _ v => v)
  refine hh.trans (SameRun.of_eq ?_)
  apply bind_congr
  intro v
  change (OverPermutation.sequenceFin (fun i => next i (v i)) >>= pure) = _
  rw [bind_pure]
  rfl

/-- The scheduler preserves that reordering through the complete adaptive network continuation. -/
theorem executePhase_local_fallback (prims : Primitives) (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (oa : C.Party → OracleComp (LocalSpec C) β) (fallback : C.Party → β)
    (f : C.Party → β → PartyM C E (CallSpec I O) α) :
    SameRun prims (executePhase localRoles D A F fuel st (fun i => localStep (oa i) >>= f i))
      (do
        let v ← OverPermutation.sequenceFin (fun i => if i ∈ D.1 then pure (fallback i) else oa i)
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
  · simp only [ite_eq_left hi]
    have hc : (fun T => honestDigestColumn D T salts history i) = fun _ => pure (0 : HashOutput) := by
      funext T
      simp [honestDigestColumn,hi]
    rw [hc,List.mapM_pure]
  · simp only [ite_eq_right hi]
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
variable {C : Committee} {E Ia α : Type}

def digestColumnValues (D : C.Coalition) (T : C.Term) (d : HashOutput) : C.Party → HashOutput := fun i =>
  if i ∉ D.1 ∧ i ∈ C.holders T then d else 0

end ThresholdLeanXmssSecurity
end

/-! ## Coordinate -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
    have hu : (do let value ← $ᵗ R; let table ← $ᵗ (I → R); pure (Function.update table i value) :
        ProbComp (I → R)) =ᵈ $ᵗ (I → R) := by
      let : MeasurableSpace R := ⊤
      have hu := EvalDistEq.of_evalDist_eq (evalDist_bind_bind_update ($ᵗ R) ($ᵗ (I → R))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample i pure)
      rwa [bind_pure] at hu
    simpa only [liftComp_bind,liftComp_pure] using sameRun_liftComp_of_evalDist (C := C) prims _ _ hu
  have hb := h.bind (fun table => SameRun.refl prims (k table))
  simpa only [bind_assoc,pure_bind] using hb

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

def maskShare (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    (w : MaskTable C E) (g : ℕ) (i : C.Party) : E :=
  conv K (localContext i) (randShares D 2 known w i) g

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

end ThresholdLeanXmssSecurity
end

/-! ## Digest uncached -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
    letI : MeasurableSpace α := ⊤
    measureTVDist ((simulateQ (localAnswer prims) (saltedDigestProgram history k)).run' cache)
      ((simulateQ (localAnswer prims) (liftComp ($ᵗ HashOutput) (LocalSpec C) >>= k)).run' cache) ≤
      ((seen.card+q : ℕ) : ℝ)/2^256 := by
  let : MeasurableSpace α := ⊤
  let probe : OracleComp (LocalSpec C) HashOutput := liftComp (hashQuery (Query.history (C := C) history)) (LocalSpec C)
  let real := saltedDigestProgram history k
  let ghost := liftComp ($ᵗ HashOutput) (LocalSpec C) >>= k
  have hr := local_prefetch_output prims probe real cache
  have hg := local_prefetch_output prims probe ghost cache
  change measureTVDist ((simulateQ (localAnswer prims) real).run' cache)
    ((simulateQ (localAnswer prims) ghost).run' cache) ≤ _
  rw [measureTVDist,← hr.evalDist_eq,← hg.evalDist_eq]
  change measureTVDist ((simulateQ (localAnswer prims) (probe >>= fun _ => real)).run' cache)
    ((simulateQ (localAnswer prims) (probe >>= fun _ => ghost)).run' cache) ≤ _
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
  dsimp only [probe]
  rw [simulateQ_localAnswer_hash]
  change measureTVDist (((hashAnswer prims (.history history)).run cache) >>= fun p =>
      (simulateQ (localAnswer prims) real).run' p.2)
    (((hashAnswer prims (.history history)).run cache) >>= fun p =>
      (simulateQ (localAnswer prims) ghost).run' p.2) ≤ _
  refine le_of_eq_of_le (congrArg₂ measureTVDist (bind_eq_attach_bind _ _) (bind_eq_attach_bind _ _))
    (measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity) fun p => ?_)
  obtain ⟨p,hp⟩ := p
  replace hp := MonadAttach.mem_support.2 hp
  have hn : ¬ IsFixed (Query.history (C := C) history) := by rintro ⟨_,he,_⟩; cases he
  have hh := hashAnswer_cached prims hn cache p hp
  have hc := history_preserves_digestSalts prims cache seen hs history p hp
  change measureTVDist ((simulateQ (localAnswer prims) (saltedDigestProgram history k)).run' p.2)
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
    obtain ⟨p,c,hp,rfl⟩ := hp
    intro salt h hd
    rcases hashAnswer_digest_entries prims (.streamKey x.2.1) cache (p,c) hp salt h hd with hs|he
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

/-! ## Digest list -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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

end ThresholdLeanXmssSecurity
end

/-! ## Digest mixed -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
    · rw [ite_eq_left hT]
      apply (isQueryBoundP_bind (hknown T hT) (fun col _ => ih (fun cs => k (col::cs)) (fun cs => hq (col::cs)))).mono
      simp only [List.length_cons,Nat.mul_succ]
      omega
    · rw [ite_eq_right hT]
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
    letI : MeasurableSpace α := ⊤
    measureTVDist ((simulateQ (localAnswer prims) (mixedDigests D known hist Ts k)).run' cache)
      ((simulateQ (localAnswer prims) (mixedGhostDigests D known Ts k)).run' cache) ≤
      ((Ts.length*(seen.card+q+(p+1)*Ts.length) : ℕ) : ℝ)/2^256 := by
  let : MeasurableSpace α := ⊤
  induction Ts generalizing cache seen k with
  | nil => simp [mixedDigests,mixedGhostDigests]
  | cons T Ts ih =>
    simp only [mixedDigests,mixedGhostDigests]
    by_cases hT : KnownTo D.1 T
    · rw [ite_eq_left hT,ite_eq_left hT]
      simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
      refine le_of_eq_of_le (congrArg₂ measureTVDist (bind_eq_attach_bind _ _) (bind_eq_attach_bind _ _))
        (measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity) fun z => ?_)
      obtain ⟨z,hz⟩ := z
      replace hz := MonadAttach.mem_support.2 hz
      obtain ⟨seen',hc',hcard⟩ := localProgram_digest_covered prims (known T) DigestQuery
        (fun _ ht => ht) p (hknown T hT) cache seen hc z hz
      refine (ih z.2 seen' hc' (fun cs => k (z.1::cs)) (fun cs => hq _)).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (show Ts.length*(seen'.card+q+(p+1)*Ts.length) ≤
        (T::Ts).length*(seen.card+q+(p+1)*(T::Ts).length) from calc
        _ ≤ Ts.length*(seen.card+p+q+(p+1)*Ts.length) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ _ := by simp only [List.length_cons]; nlinarith)
    · rw [ite_eq_right hT,ite_eq_right hT]
      let next := fun d => mixedDigests D known hist Ts fun cs => k (digestColumnValues D T d::cs)
      let ghost := liftComp ($ᵗ HashOutput) (LocalSpec C) >>= next
      have hb := saltedDigestProgram_hide prims cache seen hc (hist T) next DigestQuery
        (fun _ ht => ht) ((p+1)*Ts.length+q)
        (fun d => mixedDigests_digestBound D known hist p hknown Ts _ q (fun cs => hq _))
      have ht : measureTVDist ((simulateQ (localAnswer prims) ghost).run' cache)
          ((simulateQ (localAnswer prims) (liftComp ($ᵗ HashOutput) (LocalSpec C) >>= fun d =>
            mixedGhostDigests D known Ts fun cs => k (digestColumnValues D T d::cs))).run' cache) ≤
          ((Ts.length*(seen.card+q+(p+1)*Ts.length) : ℕ) : ℝ)/2^256 := by
        simp only [ghost,simulateQ_bind,StateT.run'_eq,StateT.run_bind,run_liftComp_prob,bind_map_left,map_bind]
        refine measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity) fun d => ?_
        exact ih cache seen hc _ (fun cs => hq _)
      have htri := measureTVDist_triangle
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
    by_cases hT : KnownTo D.1 T <;> simp only [hT,ite_true,ite_false]
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
    · simp only [mixedTableDigests,mixedDigests,ite_eq_left hT]
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
        simp only [mixedTableDigests,ite_eq_right hT,Function.update_self]
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
      simp only [draw,rest,mixedDigests,ite_eq_right hT,saltedDigestProgram,bind_assoc,pure_bind]
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
    letI : MeasurableSpace α := ⊤
    measureTVDist ((simulateQ (localAnswer prims) (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        mixedTableDigests D known hist table Ts k)).run' cache)
      ((simulateQ (localAnswer prims) (mixedGhostDigests D known Ts k)).run' cache) ≤
      ((Ts.length*(seen.card+q+(p+1)*Ts.length) : ℕ) : ℝ)/2^256 := by
  let : MeasurableSpace α := ⊤
  have he := mixedTableDigests_fresh prims D known hist Ts hTs k cache
  have he' := he.map Prod.fst
  simp only [← StateT.run'_eq] at he'
  rw [measureTVDist,he'.evalDist_eq]
  exact mixedDigests_hide prims D known hist p hknown Ts cache seen hc k q hq

end ThresholdLeanXmssSecurity
end

/-! ## Digest protocol -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {α : Type}

def digestRows (cols : List (DigestColumn C)) : C.Party → List HashOutput :=
  fun i => cols.map (fun col => col i)

end ThresholdLeanXmssSecurity
end

/-! ## Projected network -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
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
          · simp only [ite_eq_left hp, ite_eq_left hc]
            have hn := h.1.resolve_left (not_not.mpr hp)
            omega
          · simp only [ite_eq_left hp, ite_eq_right hc]
            omega
        · have hc : ¬ DigestQuery q := fun hc => hp (hcp hc)
          simp only [ite_eq_right hp, ite_eq_right hc]
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
    (_h : ∀ i, IsQueryBoundP (oa i) (PartyDigest (E := E) (G := G)) (budget i))
    (k : (Fin N → Step C E G α) → OracleComp (LocalSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ), (∀ i, b i ≤ budget i) → (∀ i, DigestStepBound (st i) (b i)) →
      IsQueryBoundP (k st) DigestQuery (extra + ∑ i, b i)) →
    IsQueryBoundP ((OverPermutation.sequenceFin fun i => advance (oa i)) >>= k) DigestQuery
      (extra + ∑ i, budget i)
  | 0, oa, budget, h, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, h, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
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
      IsQueryBoundP (OverPermutation.sequenceFin f >>= fun st => k (result.1, st, fun _ _ => none))
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
      IsQueryBoundP (OverPermutation.sequenceFin f >>= fun st => k (result.1, st, result.2))
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
      · simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

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
  change IsQueryBoundP ((OverPermutation.sequenceFin _) >>= _) _ _
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
variable {C : Committee} {E Ia α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The actual salt phase reduces to the chosen known terms and one fresh hidden table;
the unused PRSS pair table has no effect on the entire adaptive continuation. -/
theorem executePhase_randBits_first (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (count : ℕ)
    (hs : C.Party → RunState C) (f : C.Party → Shares C Bit → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) (fuel+1) st
        (fun i => ((hybridCheckBuildingBlocks K i).randBits count >>= fun w => f i w.1).run' (hs i)))
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
  simp only [afterRandom,randFinish,ite_eq_right hi]
  congr 2
  funext T g
  by_cases ht : i ∈ C.holders T <;> by_cases hk : KnownTo D.1 T <;> simp [randShares,ht,hk]

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

lemma localStep_digestBound {oa : OracleComp (LocalSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa DigestQuery n) : DigestPartyBound (localStep oa : PartyM C E G α) n := by
  unfold DigestPartyBound localStep
  change IsQueryBoundP (liftComp oa (PartySpec C E G) >>= pure ∘ some) (PartyDigest (E := E) (G := G)) n
  rw [← map_eq_bind_pure_comp,isQueryBoundP_map_iff]
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
    DigestRunBound (challenge K (hybridCheckBuildingBlocks K i)) := by
  have hc : DigestRunBound (coinKey K (hybridCheckBuildingBlocks K i)) := by
    unfold coinKey
    apply (DigestRunBound.of_zero RunBound.get).bind
    intro hs
    apply (DigestRunBound.of_zero (hybrid_coin_queryBound K i 2)).bind
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
  let r ← challenge K (hybridCheckBuildingBlocks K i)
  StateT.lift (finalOpenProgram K i (finalOpenVector wa wb a b d q0 q2 r))

/-- Both projected replies preserve the caller's query bound. -/
lemma saltReply_queryBound (A : CheckAdversary C E Ia) (st : A.State) (step : ℕ)
    (ha : ∀ st l,IsQueryBoundP (A.answer st l) Counted step) :
    IsQueryBoundP ((rightAdversary (rightAdversary A)).answer st ()) Counted step := by
  dsimp only [rightAdversary]
  simp only [bind_assoc,pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st (.inr (.inr ())))
    (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

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
  · simp only [ha,ite_true,digestLive,not_true_eq_false,false_and,ite_false]
  · simp only [ha,digestLive]
    by_cases hg : DigestsAgree i (ds i) (digestInbox D ds p.2 i)
    · simp [require,hg]
    · simp [require,hg]

end ThresholdLeanXmssSecurity
end
