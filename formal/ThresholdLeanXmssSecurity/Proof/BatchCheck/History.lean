import ThresholdLeanXmssSecurity.Proof.BatchCheck.CoinBlock
import ThresholdLeanXmssSecurity.Proof.BatchCheck.Tails

/-!
# The invariants of the outputs of the head, and the step of one check

`headHist` proves `HeadHistStatement` from the four blocks of the histories. `firstCoinBlock` proves
`FirstCoinBlockStatement`. `c1b` and `c1a` give the two halves of the step, and `c1Named` proves the
step of one check with the named witness `c1Wrapper`.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1w

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1t RealNetworkC1u

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- A point of the support of a run is in the support of each equal run. -/
theorem SameRun.mem_support_run (prims : Primitives) {α : Type} {oa ob : OracleComp (LocalSpec C) α}
    (h : SameRun prims oa ob) (cache : HashCache C) (z : α × HashCache C)
    (hz : z ∈ support ((simulateQ (localAnswer prims) oa).run cache)) :
    z ∈ support ((simulateQ (localAnswer prims) ob).run cache) := by
  rwa [← support_eq_of_evalDistEq (h cache)]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

theorem histMaskBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    HistMaskBlockStatement prims K D := by
  intro Ia W knownE knownB names hN count L tg hist st mem p hs hRel hK hH cache z hz
  let A : C.Party → ℕ → E := fun i => match p i with
    | .mask a _ _ => a
    | .step _ _ => fun _ => 0
  let B : C.Party → ℕ → E := fun i => match p i with
    | .mask _ b _ => b
    | .step _ _ => fun _ => 0
  let V : C.Party → E := fun i => match p i with
    | .mask _ _ v => v
    | .step _ _ => 0
  have hp : ∀ i, i ∉ D.1 → p i = .mask (A i) (B i) (V i) := by
    intro i hi
    have h := hRel i hi
    simp only [A, B, V]
    cases hpi : p i with
    | mask a b v => rfl
    | step ps nx =>
      rw [hpi] at h
      obtain ⟨-, d', hd, -⟩ := h
      omega
  let w : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → C.Party → PrssOutput C E := fun a b i =>
    frandShare D 2 (knownE (2 * halvings count + 1)).1 (knownE (2 * halvings count + 1)).2 a b i
  let hs' : C.Party → RunState C := fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
  let prods : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → C.Party → List (Product C E) := fun a b i =>
    maskProducts K i (A i) (B i) (w a b i)
  have eprog : executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (2 * 0 + 2) ((st, mem), 2 * halvings count + 1)
      (fun i => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (p i)).run (hs i)) =
    executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (1 + 1) ((st, mem), 2 * halvings count + 1)
      (fun i => call (Sum.inr (Sum.inl 2)) >>= hybridMaskAfter K i (A i) (B i) (V i) (hs i)) := by
    refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
    rw [hp i hi, hybridMask_eq]
  rw [eprog, executePhase_call, runCheck_randElements, bind_map_left, runFunctionality_rand_local D _ _ _
    (by intro i hi; simp [hi]), firstInput_honest_const,
    frandElements_answer K D W knownE knownB count hist names hN _ _ _, pure_bind] at hz
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨a, c1⟩, -, ⟨b, c2⟩, -, hz⟩ := hz
  dsimp only at hz
  rw [executePhase_congr_honest D _ _ 1 _ _ (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inr (prods a b i)))
    (fun o => (extendOutput o).map fun z => (z, extendState K i (hs' i) z)) >>= fun q =>
      pure (((A i 0, B i 0, V i, (w a b i).1, q.1), q.2) : HeadOut C E × RunState C)) fun i hi => ?_] at hz
  swap
  · simp only [randFinish, hi, ite_false, Option.map_some, Function.comp_apply, hybridMaskAfter,
      RealNetworkGP.callProg, bind_assoc]
    refine bind_congr fun r => ?_
    rcases r with _ | ((_ | y) | _) <;> rfl
  have hz' := SameRun.mem_support_run prims (executePhase_bind_pure prims D _ _ 1 _ _ _ fun i _ =>
    timed_callProg _ _) c2 z hz
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  have hm := extendMemoryHead prims K D W knownE knownB count L tg hist names 0 (2 * halvings count + 1 + 1)
    (st, mem) (prods a b) hs' c2 (fun i hi => rfl) y hy
  have hh := RealNetworkC1v.extendHidden prims K D W knownE knownB count L tg hist names 0
    (2 * halvings count + 1 + 1) (st, mem) (prods a b) hs' c2 (fun i hi => rfl)
    (fun T hT i j hi hj hiT hjT => hH T hT i j hi hj hiT hjT _ _ rfl rfl) y hy
  refine ⟨fun i hi zz hzz T hT => ?_, fun T hT i j hi hj hiT hjT zi zj hzi hzj => ?_⟩
  · simp only [hi, ite_false, Option.map_eq_some_iff] at hzz
    obtain ⟨q, hq, rfl⟩ := hzz
    exact hm.2.2 i q hi hq (fun T hT => hK i hi _ rfl T hT) T hT
  · simp only [hi, hj, ite_false, Option.map_eq_some_iff] at hzi hzj
    obtain ⟨qi, hqi, rfl⟩ := hzi
    obtain ⟨qj, hqj, rfl⟩ := hzj
    exact hh T hT i j hi hj hiT hjT qi qj hqi hqj

end ThresholdLeanXmssSecurity.RealNetworkC1w

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1w

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1t RealNetworkC1u

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The plan after the search of a challenge from the values `v` of the coin, at the state `hs` before the
coin. With no challenge the operator aborts. -/
def coinNext (K : Constants C E) (i : C.Party) (next : E → Plan C E) (hs : RunState C) :
    Option E → PartyM C E (CheckSpec C E) (HeadOut C E × RunState C)
  | some r => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next r)).run
      ⟨hs.history, hs.label + 1, hs.tag⟩
  | none => failure

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The coin block in the hybrid model is the call of `F_coin`, the search of the challenge and then the
plan of the next step. -/
theorem hybridCoin_run (K : Constants C E) (i : C.Party) (next : E → Plan C E) (hs : RunState C) :
    (hybridCoin K i next).run hs =
      RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= fun v =>
        oracleStep (challengeQuery K hs.tag hs.label v) >>= coinNext K i next hs := by
  rw [RealNetworkC1v.run_eq_run']
  simp only [hybridCoin, bind_assoc]
  rw [challenge_run']
  simp only [RealNetworkGP.callProg, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | _) | _) <;>
    simp only [Option.bind_some, Option.bind_none, coinOutput, RealNetworkGP.ofOption, failure_bind, pure_bind]
  refine bind_congr fun r => ?_
  cases r with
  | none => simp only [coinNext]
  | some r =>
    simp only [coinNext]
    exact (RealNetworkC1v.run_eq_run' _ _).symm

theorem histCoinBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    HistCoinBlockStatement prims K D := by
  intro Ia W knownE knownB names hN count L tg hist j d hjd hIH st mem next hs hRel hK hH cache z hz
  have eprog : executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (2 * d + 3) ((st, mem), 2 * j + 2)
      (fun i => (hybridCoin K i (next i)).run (hs i)) =
    executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (1 + (2 * d + 2)) ((st, mem), 2 * j + 2)
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= fun v =>
        oracleStep (challengeQuery K (hs i).tag (hs i).label v) >>= coinNext K i (next i) (hs i)) := by
    rw [show 2 * d + 3 = 1 + (2 * d + 2) by omega]
    simp only [hybridCoin_run]
  rw [eprog] at hz
  have hz1 := SameRun.mem_support_run prims (executePhase_bind prims D _ _ 1 (2 * d + 2) _ _ _ fun i _ =>
    timed_callProg _ _) cache z hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz1
  obtain ⟨y, hy, hz2⟩ := hz1
  have hm := coinMemoryHead prims K D W knownE knownB count L tg hist names 0 (2 * j + 2) (st, mem) cache y hy
  obtain ⟨⟨⟨s1, k⟩, o⟩, c⟩ := y
  obtain ⟨hk, hhist, -⟩ := hm
  dsimp only at hk hhist hz2
  subst hk
  have hprog : (fun i => (o i).elim failure fun v =>
      oracleStep (challengeQuery K (hs i).tag (hs i).label v) >>= coinNext K i (next i) (hs i)) =
    fun i => localStep ((o i).elim (pure none) fun v =>
        liftComp (challengeQuery K (hs i).tag (hs i).label v) (LocalSpec C)) >>= fun r =>
      (o i).elim failure fun _ => coinNext K i (next i) (hs i) r := by
    funext i
    cases o i with
    | none => simp only [Option.elim_none, localStep_pure', pure_bind]
    | some v => rfl
  rw [hprog] at hz2
  have hz3 := SameRun.mem_support_run prims (executePhase_local_fallback prims D _ _ (2 * d + 2) _ _
    (fun _ => none) _) c z hz2
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz3
  obtain ⟨⟨vv, c'⟩, -, hz4⟩ := hz3
  dsimp only at hz4
  let o' : C.Party → Option (Plan C E × RunState C) := fun i => match o i, vv i with
    | some _, some r => some (next i r, ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩)
    | _, _ => none
  have hprog2 : (fun i => (o i).elim failure fun _ => coinNext K i (next i) (hs i) (vv i)) =
      fun i => (o' i).elim failure fun q => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) q.1).run q.2 := by
    funext i
    simp only [o']
    cases o i <;> cases vv i <;> rfl
  rw [hprog2] at hz4
  have ho' : ∀ i q, o' i = some q → (∃ r, q.1 = next i r) ∧ q.2.history = (hs i).history := by
    intro i q hq
    simp only [o'] at hq
    split at hq
    · cases hq
      exact ⟨⟨_, rfl⟩, rfl⟩
    · cases hq
  by_cases hfull : ∀ i, i ∉ D.1 → (o' i).isSome
  · let zf : C.Party → Plan C E × RunState C := fun i => (o' i).getD (next i 0, hs i)
    have hz : ∀ i, i ∉ D.1 → o' i = some (zf i) := fun i hi => by
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      simp only [zf, hq, Option.getD_some]
    refine hIH s1.1 s1.2 (fun i => (zf i).1) (fun i => (zf i).2) (fun i hi => ?_)
      (fun i hi q hq T hT => ?_) (fun T hT i j hi hj hiT hjT zi zj hzi hzj => ?_) c' z ?_
    · obtain ⟨⟨r, hr⟩, -⟩ := ho' i _ (hz i hi)
      show PlanOK (zf i).1 d
      rw [hr]
      exact hRel i hi r
    · cases hq
      rw [hhist, (ho' i _ (hz i hi)).2]
      exact hK i hi _ rfl T hT
    · cases hzi
      cases hzj
      rw [(ho' i _ (hz i hi)).2, (ho' j _ (hz j hj)).2]
      exact hH T hT i j hi hj hiT hjT _ _ rfl rfl
    · rw [executePhase_congr_honest D _ _ _ _ _ _ fun i hi => by rw [hz i hi, Option.elim_some],
        show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by omega] at hz4
      exact hz4
  · push Not at hfull
    obtain ⟨i0, hi0, h0⟩ := hfull
    rw [RealNetworkC1v.planDead K D _ _ _ _ ⟨i0, hi0, Option.not_isSome_iff_eq_none.1 h0⟩] at hz4
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz4
    rw [hz4]
    exact inv_none D _

end ThresholdLeanXmssSecurity.RealNetworkC1w

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1w

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1t RealNetworkC1u

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

theorem histExtendBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    HistExtendBlockStatement prims K D := by
  intro Ia W knownE knownB names hN count L tg hist j d hjd hIH st mem p hs hRel hK hH cache z hz
  let products : C.Party → List (Product C E) := fun i => match p i with
    | .step ps _ => ps
    | .mask _ _ _ => []
  let next : C.Party → Shares C E → E → Plan C E := fun i => match p i with
    | .step _ nx => nx
    | .mask _ _ _ => fun _ _ => p i
  have hp : ∀ i, i ∉ D.1 → p i = .step (products i) (next i) ∧ (products i).length = 2 ∧
      ∀ z r, PlanOK (next i z r) d := by
    intro i hi
    have h := hRel i hi
    simp only [products, next]
    cases hpi : p i with
    | mask A B V =>
      rw [hpi] at h
      simp only [PlanOK] at h
      omega
    | step ps nx =>
      rw [hpi] at h
      obtain ⟨hl, d', hd, hnx⟩ := h
      obtain rfl : d' = d := by omega
      exact ⟨rfl, hl, hnx⟩
  have eprog : executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (2 * (d + 1) + 2) ((st, mem), 2 * j + 1)
      (fun i => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (p i)).run (hs i)) =
    executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (1 + (2 * d + 3)) ((st, mem), 2 * j + 1)
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inr (products i)))
        (fun o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)) >>= fun q =>
          (hybridCoin K i (next i q.1)).run q.2) := by
    rw [show 2 * (d + 1) + 2 = 1 + (2 * d + 3) by omega]
    refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
    rw [(hp i hi).1, hybridStep_eq K i (hs i) (products i) (hp i hi).2.1 (next i)]
    simp only [RealNetworkGP.callProg, bind_assoc]
    refine bind_congr fun r => ?_
    rcases r with _ | ((_ | y) | _) <;> rfl
  rw [eprog] at hz
  have hz1 := SameRun.mem_support_run prims (executePhase_bind prims D _ _ 1 (2 * d + 3) _ _ _ fun i _ =>
    timed_callProg _ _) cache z hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz1
  obtain ⟨y, hy, hz2⟩ := hz1
  have hm := extendMemoryHead prims K D W knownE knownB count L tg hist names 0 (2 * j + 1) (st, mem) products hs
    cache (fun i hi => (hp i hi).2.1) y hy
  have hh := RealNetworkC1v.extendHidden prims K D W knownE knownB count L tg hist names 0 (2 * j + 1) (st, mem)
    products hs cache (fun i hi => (hp i hi).2.1)
    (fun T hT i j hi hj hiT hjT => hH T hT i j hi hj hiT hjT _ _ rfl rfl) y hy
  obtain ⟨⟨⟨s1, k⟩, o⟩, c⟩ := y
  obtain ⟨hk, -, hmem⟩ := hm
  dsimp only at hk hmem hh hz2
  subst hk
  by_cases hfull : ∀ i, i ∉ D.1 → (o i).isSome
  · let zf : C.Party → Shares C E × RunState C := fun i => (o i).getD (fun _ _ => 0, hs i)
    have hz : ∀ i, i ∉ D.1 → o i = some (zf i) := fun i hi => by
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      simp only [zf, hq, Option.getD_some]
    refine hIH s1.1 s1.2 (fun i => next i (zf i).1) (fun i => (zf i).2) (fun i hi r => (hp i hi).2.2 _ r)
      (fun i hi q hq T hT => ?_) (fun T hT i j hi hj hiT hjT zi zj hzi hzj => ?_) c z ?_
    · cases hq
      exact hmem i (zf i) hi (hz i hi) (fun T hT => hK i hi _ rfl T hT) T hT
    · cases hzi
      cases hzj
      exact hh T hT i j hi hj hiT hjT (zf i) (zf j) (hz i hi) (hz j hj)
    · rw [executePhase_congr_honest D _ _ _ _ _ _ fun i hi => by rw [hz i hi, Option.elim_some]] at hz2
      exact hz2
  · push Not at hfull
    obtain ⟨i0, hi0, h0⟩ := hfull
    rw [show (fun i => (o i).elim failure fun q => (hybridCoin K i (next i q.1)).run q.2) =
        fun i => ((o i).map fun q => (next i q.1, q.2)).elim failure fun pr => (hybridCoin K i pr.1).run pr.2 by
          funext i
          cases o i <;> rfl,
      RealNetworkC1v.coinDead K D _ _ _ _ ⟨i0, hi0, by simp [Option.not_isSome_iff_eq_none.1 h0]⟩] at hz2
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz2
    rw [hz2]
    exact inv_none D _

end ThresholdLeanXmssSecurity.RealNetworkC1w

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1w

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1t RealNetworkC1u

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The plan of the head after the coins `τ` of the first coin, at the state `hs` before the coin. With
coins that fail the test the operator aborts. -/
def startNext (K : Constants C E) (i : C.Party) (next : List E → Plan C E) (hs : RunState C) (τ : List E) :
    PartyM C E (CheckSpec C E) (HeadOut C E × RunState C) :=
  if ∀ b < sliceBits, τ.getD b 0 ≠ 0 then
    (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next τ)).run ⟨hs.history, hs.label + 1, hs.tag⟩
  else failure

omit [Fintype E] [SampleableType E] in
/-- The first coin block in the hybrid model is the call of `F_coin`, the coins from `H` and then
`startNext`. -/
theorem hybridStart_run (K : Constants C E) (count : ℕ) (i : C.Party) (next : List E → Plan C E)
    (hs : RunState C) :
    (hybridStart K count i next).run hs =
      RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= fun v =>
        oracleStep (tauQuery K hs.tag hs.label v (coins count)) >>= startNext K i next hs := by
  rw [RealNetworkC1v.run_eq_run']
  simp only [hybridStart, bind_assoc]
  rw [coinKey_expand_run']
  simp only [RealNetworkGP.callProg, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | _) | _) <;>
    simp only [Option.bind_some, Option.bind_none, coinOutput, RealNetworkGP.ofOption, failure_bind, pure_bind]
  refine bind_congr fun τ => ?_
  unfold startNext
  rw [RealNetworkC1v.run_eq_run' (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next τ))]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, bind_assoc, map_bind]
  unfold require
  split_ifs with h
  · simp only [pure_bind]
  · simp only [failure_bind]

theorem histFirstBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    HistFirstBlockStatement prims K D := by
  intro Ia W knownE knownB names hN count L tg hist hIH st mem next hs hRel hK hH cache z hz
  have eprog : executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (2 * halvings count + 3) ((st, mem), 0)
      (fun i => (hybridStart K count i (next i)).run (hs i)) =
    executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
      (checkFunctionalities K) (1 + (2 * halvings count + 2)) ((st, mem), 0)
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= fun v =>
        oracleStep (tauQuery K (hs i).tag (hs i).label v (coins count)) >>= startNext K i (next i) (hs i)) := by
    rw [show 2 * halvings count + 3 = 1 + (2 * halvings count + 2) by omega]
    simp only [hybridStart_run]
  rw [eprog] at hz
  have hz1 := SameRun.mem_support_run prims (executePhase_bind prims D _ _ 1 (2 * halvings count + 2) _ _ _ fun i _ =>
    timed_callProg _ _) cache z hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz1
  obtain ⟨y, hy, hz2⟩ := hz1
  have hm := coinMemoryHead prims K D W knownE knownB count L tg hist names 0 0 (st, mem) cache y hy
  obtain ⟨⟨⟨s1, k⟩, o⟩, c⟩ := y
  obtain ⟨hk, hhist, -⟩ := hm
  dsimp only at hk hhist hz2
  subst hk
  have hprog : (fun i => (o i).elim failure fun v =>
      oracleStep (tauQuery K (hs i).tag (hs i).label v (coins count)) >>= startNext K i (next i) (hs i)) =
    fun i => localStep ((o i).elim (pure none) fun v =>
        some <$> liftComp (tauQuery K (hs i).tag (hs i).label v (coins count)) (LocalSpec C)) >>= fun r =>
      (o i).elim failure fun _ => r.elim failure (startNext K i (next i) (hs i)) := by
    funext i
    cases o i with
    | none => simp only [Option.elim_none, localStep_pure', pure_bind]
    | some v =>
      simp only [Option.elim_some, oracleStep, localStep, liftComp_map]
      apply OptionT.ext
      simp [OptionT.run_bind, OptionT.run_lift]
  rw [hprog] at hz2
  have hz3 := SameRun.mem_support_run prims (executePhase_local_fallback prims D _ _ (2 * halvings count + 2) _ _
    (fun _ => none) _) c z hz2
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz3
  obtain ⟨⟨vv, c'⟩, -, hz4⟩ := hz3
  dsimp only at hz4
  let o' : C.Party → Option (Plan C E × RunState C) := fun i => match o i, vv i with
    | some _, some τ => if ∀ b < sliceBits, τ.getD b 0 ≠ 0 then
        some (next i τ, ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) else none
    | _, _ => none
  have hprog2 : (fun i => (o i).elim failure fun _ => (vv i).elim failure (startNext K i (next i) (hs i))) =
      fun i => (o' i).elim failure fun q => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) q.1).run q.2 := by
    funext i
    simp only [o']
    cases o i with
    | none => rfl
    | some v =>
      cases vv i with
      | none => rfl
      | some τ =>
        simp only [Option.elim_some, startNext]
        split_ifs <;> rfl
  rw [hprog2] at hz4
  have ho' : ∀ i q, o' i = some q → (∃ τ, q.1 = next i τ) ∧ q.2.history = (hs i).history := by
    intro i q hq
    simp only [o'] at hq
    split at hq
    · split_ifs at hq
      cases hq
      exact ⟨⟨_, rfl⟩, rfl⟩
    · cases hq
  by_cases hfull : ∀ i, i ∉ D.1 → (o' i).isSome
  · let zf : C.Party → Plan C E × RunState C := fun i => (o' i).getD (next i [], hs i)
    have hz : ∀ i, i ∉ D.1 → o' i = some (zf i) := fun i hi => by
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      simp only [zf, hq, Option.getD_some]
    refine hIH s1.1 s1.2 (fun i => (zf i).1) (fun i => (zf i).2) (fun i hi => ?_)
      (fun i hi q hq T hT => ?_) (fun T hT i j hi hj hiT hjT zi zj hzi hzj => ?_) c' z ?_
    · obtain ⟨⟨r, hr⟩, -⟩ := ho' i _ (hz i hi)
      show PlanOK (zf i).1 (halvings count)
      rw [hr]
      exact hRel i hi r
    · cases hq
      rw [hhist, (ho' i _ (hz i hi)).2]
      exact hK i hi _ rfl T hT
    · cases hzi
      cases hzj
      rw [(ho' i _ (hz i hi)).2, (ho' j _ (hz j hj)).2]
      exact hH T hT i j hi hj hiT hjT _ _ rfl rfl
    · rw [executePhase_congr_honest D _ _ _ _ _ _ fun i hi => by rw [hz i hi, Option.elim_some],
        show 0 + 1 = 2 * 0 + 1 by omega] at hz4
      exact hz4
  · push Not at hfull
    obtain ⟨i0, hi0, h0⟩ := hfull
    rw [RealNetworkC1v.planDead K D _ _ _ _ ⟨i0, hi0, Option.not_isSome_iff_eq_none.1 h0⟩] at hz4
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz4
    rw [hz4]
    exact inv_none D _

end ThresholdLeanXmssSecurity.RealNetworkC1w

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1w

open RealNetworkC1r

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

theorem headHist (prims : Primitives) (K : Constants C E) (D : C.Coalition) : HeadHistStatement prims K D :=
  headHist_of_steps prims K D (histMaskBlock prims K D) (histExtendBlock prims K D) (histCoinBlock prims K D)
    (histFirstBlock prims K D)

end ThresholdLeanXmssSecurity.RealNetworkC1w

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1c

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1y

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The test of the slice coins, as a decoder of the coins `τ`. -/
def firstDec (τ : List E) : Option (List E) :=
  if ∀ b < sliceBits, τ.getD b 0 ≠ 0 then some τ else none

omit [Fintype E] [SampleableType E] in
/-- The real program of the first block is the coin and `genNext`. -/
theorem first_hR (K : Constants C E) (D : C.Coalition) (L tg count : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    {m : ℕ} (hnR : 0 < m) (T : DrawTables C E m) (i : C.Party) (b : List E → Plan C E) (hs : RunState C)
    (hl : hs.label = L + 0) (ht : hs.tag = tg) :
    (do
      let τ ← expand K (← coinKey K (drawnCheckBuildingBlocks K D L knownE knownB T i)) (coins count)
      StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
      runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (b τ)).run hs =
      openSh K (localContext i) (conv K (localContext i) (frandShare D 2 (knownE 0).1
        (knownE 0).2 (T.freshE ⟨0, hnR⟩) (T.freshPairE ⟨0, hnR⟩) i).1) 2 >>= fun w =>
          genNext K (fun vals => startQuery K tg L vals (coins count)) firstDec
            (drawnCheckBuildingBlocks K D L knownE knownB T i) i hs b (vector 2 w) := by
  have hn : hs.label - L = 0 := by
    rw [hl]
    omega
  simp only [coinKey, expand, bind_assoc, drawnCheckBuildingBlocks, freshLabel, coinWith, genNext, startQuery,
    oracleStep_bind, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, StateT.run_get, pure_bind, hn]
  simp only [drawnE, hnR, ↓reduceDIte, ht, hl, Nat.add_zero]
  refine bind_congr fun w => bind_congr fun key => bind_congr fun τ => ?_
  unfold firstDec require
  split_ifs <;> simp only [pure_bind, failure_bind, Option.elim_some, Option.elim_none]

omit [Fintype E] [SampleableType E] in
/-- The hybrid program of the first block is the call of `F_coin` and `genNext`. -/
theorem first_hH (K : Constants C E) (L tg count : ℕ) (i : C.Party) (b : List E → Plan C E) (hs : RunState C)
    (hl : hs.label = L + 0) (ht : hs.tag = tg) :
    (do
      let τ ← expand K (← coinKey K (hybridCheckBuildingBlocks K i)) (coins count)
      StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
      runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (b τ)).run hs =
      RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>=
        genNext K (fun vals => startQuery K tg L vals (coins count)) firstDec (hybridCheckBuildingBlocks K i) i hs b := by
  refine (RealNetworkC1w.hybridStart_run K count i b hs).trans (bind_congr fun v => ?_)
  rw [ht, hl, Nat.add_zero]
  refine bind_congr fun τ => ?_
  unfold RealNetworkC1w.startNext firstDec
  split_ifs <;> simp only [Option.elim_some, Option.elim_none]

omit [Fintype E] in
/-- The tail of the wrapper after the first coin. -/
theorem firstTail_eq (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (count L tg : ℕ) (live : Finset C.Party) (st : W.State) (mem : C1Memory C E) :
    c1HeadTails K D W knownE knownB count L tg 0 live (st, mem) =
      liftComp (startQuery K tg L mem.values (coins count)) (LocalSpec C) >>= fun τ => if (firstDec τ).isSome then
        (fun st' => (st', mem)) <$> reshareTail K D (elementCodec K) W (knownE (0 + 1)).1 (knownE (0 + 1)).2 2 live st
      else pure (st, mem) := by
  have hR : 0 < halvings count := by
    unfold halvings sliceBits
    omega
  simp only [c1HeadTails, c1Tails, nextMult, show (0 : ℕ) ≠ 2 * halvings count + 2 by omega,
    show 0 < 2 * halvings count by omega, ↓reduceIte]
  refine bind_congr fun τ => ?_
  unfold firstDec
  by_cases h : ∀ b < sliceBits, τ.getD b 0 ≠ 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    simp only [Option.isSome_some, ↓reduceIte]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

theorem firstCoinBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    FirstCoinBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist hIH
  have hR : 0 < halvings count := by
    unfold halvings sliceBits
    omega
  have h0 : 0 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  have h1 : 0 + 1 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  unfold PlanSuffix at hIH
  rw [show 2 * 0 + 1 = 0 + 1 by rfl] at hIH
  exact genBlock_of prims K D W knownE knownB names hn count L tg hist
    (fun vals => startQuery K tg L vals (coins count)) firstDec 0 (halvings count) h0 hIH _ _
    (fun T i b hs hl ht => first_hR K D L tg count knownE knownB h0 T i b hs hl ht)
    (fun i b hs hl ht => first_hH K L tg count i b hs hl ht)
    fun T0 st mem o hs next hnext hlab hO hp =>
      (partialReal prims K D W knownE knownB count L (fun vals => startQuery K tg L vals (coins count)) firstDec 0 (halvings count) (0 + 1) T0 st mem o hs next
        hO hp (stepSome_real prims K D W knownE knownB count L (0 + 1) h1 (halvings count) hR T0 st o hs next
          hnext (fun i hi => by rw [(hlab i hi).1]) hp)).trans
        (partialHybrid prims K D W knownE knownB names count L tg hist
          (fun vals => startQuery K tg L vals (coins count)) firstDec 0 (halvings count) (0 + 1) st
          mem o hs next hO hp (firstTail_eq K D W knownE knownB count L tg _ st mem)
          (stepAbort K D _ (halvings count) hR o hs next hnext hp)).symm

end ThresholdLeanXmssSecurity.RealNetworkC1c

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkC1z
open RealNetworkV3 RealNetworkC1s RealNetworkC1r
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
omit [Fintype E] in
private theorem partial_bound (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist0 : C.Party → C.Term → List Bit)
    (r : (c1WrapperWith K D W knownE knownB count hist0 names
      (c1HeadTails K D W knownE knownB count L tg)).State ×
      (C.Party → Option (HeadOut C E × RunState C)))
    (hk : KnownInv D r.1.1.2 r.2) (hh' : HiddenInv D r.2) (hp : PartialOut D r.2)
    (step q : ℕ) (hW : ∀ s m, IsQueryBoundP (W.round s m) Counted step)
    (Z : W.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) Bool)
    (hZ : ∀ out, IsQueryBoundP (Z out) DigestQuery q)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    letI : MeasurableSpace Bool := ⊤
    measureTVDist
      ((simulateQ (localAnswer prims) (midRest K D W knownE knownB names count L tg hist0 r >>= Z)).run' cache)
      ((simulateQ (localAnswer prims) (midTailRest K D W knownE knownB names count L tg hist0 r >>= Z)).run' cache) ≤
      ((C.terms.length * (seen.card + (step + q) + (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256 := by
  obtain ⟨hist, hhist'⟩ := hiddenInv_common D r.2 hh'
  have hp' : RealNetworkRC.PartialOut D (fun i => (r.2 i).map Prod.snd) := by
    simpa only [RealNetworkRC.PartialOut, PartialOut, Option.map_eq_none_iff,
      Option.isSome_map] using hp
  have hlive : RealNetworkRC.liveSet D (fun i => (r.2 i).map Prod.snd) = liveSet D r.2 := by
    simp only [RealNetworkRC.liveSet, liveSet, Option.isSome_map]
  have hh'' : ∀ T, ¬ KnownTo D.1 T → ∀ i ∉ D.1, ∀ hs, i ∈ C.holders T →
      (r.2 i).map Prod.snd = some hs → hs.history T = hist T := by
    intro T hT i hi hs hiT ho
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 ho
    exact hhist' T hT i hi hiT v hv
  have hb := RealNetworkRC.realDigestPhase_partial_hide prims D W noFunctionality 0 r.1.1.1
    (digestSalts D knownB) (fun i => (r.2 i).map Prod.snd) hp'
    (fun _ _ => (pure () : RunM C E RealSpec Unit)) hist
    (knownColumns (liveSet D r.2) knownB.1 r.1.1.2.hist)
    (RealNetworkC1v.digestSalts_hidden D knownB) hh''
    (RealNetworkC1v.knownColumns D knownB r.1.1.2 r.2 hk) C.n
    (fun T _ => knownColumnsBound _ _ _ T) step (fun s m => counted_digestBound (hW s m))
    Z q (fun s => hZ (s, fun _ => none)) cache seen hc
  simp only [hlive] at hb
  simp only [midRest, midTailRest, hp, ↓reduceIte, bind_assoc, bind_map_left,
    simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] 
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] at hb
  exact hb

theorem digestJoin_of_headHist (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    HeadHistStatement prims K D → DigestJoinStatement prims K D := by
  intro hhist Ia W knownE knownB names hn step hW counts L tg x st hpos hx hh cache seen hc Z q hZ
  let : MeasurableSpace Bool := ⊤
  unfold c1Mid c1MidTail
  rw [bind_assoc, bind_assoc]
  change measureTVDist
    ((simulateQ (localAnswer prims) (headPhase K D W knownE knownB names L tg counts x st >>=
      fun r => midRest K D W knownE knownB names counts.sum L tg (knownHist K D x) r >>= Z)).run' cache)
    ((simulateQ (localAnswer prims) (headPhase K D W knownE knownB names L tg counts x st >>=
      fun r => midTailRest K D W knownE knownB names counts.sum L tg (knownHist K D x) r >>= Z)).run' cache) ≤ _
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine le_of_eq_of_le (congrArg₂ measureTVDist (bind_eq_attach_bind _ _) (bind_eq_attach_bind _ _))
    (measureTVDist_bind_left_le_of_forall_le _ _ _ (by unfold c1Error; positivity) fun z => ?_)
  obtain ⟨z, hz⟩ := z
  replace hz := MonadAttach.mem_support.2 hz
  obtain ⟨seen', hc', hcard⟩ := headCover prims K D W knownE knownB names step hW counts L tg x st cache seen hc z hz
  obtain ⟨hk, hh'⟩ := hhist W knownE knownB names hn counts L tg x st hpos hx hh cache z hz
  by_cases hp : PartialOut D z.1.2
  · have hb := partial_bound prims K D W knownE knownB names counts.sum L tg (knownHist K D x)
      z.1 hk hh' hp step q hW Z hZ z.2 seen' hc'
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] at hb
    refine hb.trans ?_
    unfold c1Error
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hs := head_slack (2 * (2 * halvings counts.sum + 3) * step) step counts.sum (le_refl _)
    exact_mod_cast Nat.mul_le_mul_left C.terms.length (by omega :
      seen'.card + (step + q) + (C.n + 1) * C.terms.length ≤
        seen.card + 4 * checkRounds counts.sum * step + q + (C.n + 1) * C.terms.length)
  · simp only [midRest, midTailRest, hp, ↓reduceIte, measureTVDist_self]
    unfold c1Error
    positivity
-- The zero-count input is excluded by the positive-count premise.
end ThresholdLeanXmssSecurity.RealNetworkC1z

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkC1z
open RealNetworkC1r
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
theorem hybridTail (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    HybridTailStatement prims K D := by
  exact hybridTail_of_steps prims K D (RealNetworkC1x.headTails prims K D)
    (RealNetworkC1v.restAbort K D)
end ThresholdLeanXmssSecurity.RealNetworkC1z

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkC1z
open RealNetworkC1r RealNetworkC1s
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
theorem c1b_of_headHist (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    HeadHistStatement prims K D → C1bStatement prims K D := by
  intro h
  exact c1b_of_steps prims K D (digestJoin_of_headHist prims K D h) (hybridTail prims K D)
theorem c1b (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    C1bStatement prims K D := by
  exact c1b_of_headHist prims K D (RealNetworkC1w.headHist prims K D)
end ThresholdLeanXmssSecurity.RealNetworkC1z

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1c

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

theorem c1a (prims : Primitives) (K : Constants C E) (D : C.Coalition) : C1aStatement prims K D :=
  c1a_of_steps prims K D (RealNetworkC1w.maskBlock prims K D) (RealNetworkC1t.extendBlock prims K D)
    (coinBlock prims K D) (lastCoinBlock prims K D) (firstCoinBlock prims K D)
    (RealNetworkC1u.randBitsBlock prims K D) (RealNetworkC1t.digestBlock prims K D)
    (RealNetworkC1t.finalCoinBlock prims K D) (RealNetworkC1t.openRound prims K D)
    (RealNetworkC1t.restPartial prims K D)

end ThresholdLeanXmssSecurity.RealNetworkC1c

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1g

open RealNetworkE1r

attribute [local instance] Classical.propDecidable inhabitedField
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP

/-! ## The step of one check with the named wrapper -/

section C1

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The step of one check with `c1Wrapper` as the wrapper. The right side is the check under `c1Wrapper`.
-/
def C1NamedStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (step : ℕ),
    (∀ st sent, IsQueryBoundP (W.round st sent) Counted step) →
    ∀ (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State),
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      (∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
        filledHistory K i (x i) T = filledHistory K j (x j) T) →
      ∀ (cache : HashCache C) (seen : Finset (List Bit)), DigestSaltsCovered cache seen →
      ∀ (Z : W.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) Bool) (q : ℕ),
        (∀ out, IsQueryBoundP (Z out) DigestQuery q) →
        measureTVDist
          ((simulateQ (localAnswer prims)
            (RealNetworkC1s.c1Real K D W knownE knownB counts L tg x st >>= Z)).run' cache)
          ((simulateQ (localAnswer prims) (executePhase localRoles D
            (RealNetworkC1s.c1Wrapper K D W knownE knownB counts.sum L tg (RealNetworkV3.knownHist K D x))
            (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨RealNetworkV3.knownHist K D x, []⟩), 0)
            (RealNetworkV3.checkAt K L tg x) >>= fun r => Z (r.1.1.1, r.2))).run' cache) ≤
          RealNetworkV3.c1Error C step q seen.card counts.sum

end C1

end ThresholdLeanXmssSecurity.RealNetworkE1g

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1i

open RealNetworkV3 RealNetworkC1s RealNetworkE1g

attribute [local instance] Classical.propDecidable inhabitedField
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

theorem c1Named (prims : Primitives) (K : Constants C E) (D : C.Coalition) : C1NamedStatement prims K D := by
  intro Ia W knownE knownB step hW counts L tg x st hx hh cache seen hc Z q hZ
  by_cases hpos : counts.sum = 0
  · have h1 := (RealNetworkC1p.c1Zero prims K D W knownE knownB counts L tg x st hpos hx).bind
      fun r => SameRun.refl prims (Z r)
    unfold c1Hybrid at h1
    rw [bind_map_left] at h1
    have he := (h1 cache).map Prod.fst
    simp only [← StateT.run'_eq] at he
    refine le_of_eq_of_le (b := 0) ?_ (by unfold c1Error; positivity)
    rw [measureTVDist, he.evalDist_eq]
    exact measureTVDist_self _
  · have h1 := (RealNetworkC1c.c1a prims K D W knownE knownB c1Names (c1Names_receivers D) counts L tg x st
      hpos hx).bind fun r => SameRun.refl prims (Z r)
    have he := (h1 cache).map Prod.fst
    simp only [← StateT.run'_eq] at he
    rw [measureTVDist, he.evalDist_eq]
    exact RealNetworkC1z.c1b prims K D W knownE knownB c1Names (c1Names_receivers D) step hW counts L tg x st
      hpos hx hh cache seen hc Z q hZ

end ThresholdLeanXmssSecurity.RealNetworkE1i

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1w.histMaskBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1w.histMaskBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1w.histCoinBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1w.histCoinBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1w.histExtendBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1w.histExtendBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1w.histFirstBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1w.histFirstBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1w.headHist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1w.headHist

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1c.firstCoinBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1c.firstCoinBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1z.digestJoin_of_headHist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1z.digestJoin_of_headHist

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1z.hybridTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1z.hybridTail

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1z.c1b_of_headHist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1z.c1b_of_headHist

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1z.c1b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1z.c1b

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1c.c1a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1c.c1a

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkE1i.c1Named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkE1i.c1Named
