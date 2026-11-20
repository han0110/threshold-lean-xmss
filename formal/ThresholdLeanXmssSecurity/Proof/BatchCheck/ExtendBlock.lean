import ThresholdLeanXmssSecurity.Proof.BatchCheck.Plan

/-!
# The blocks of `extendMult`, of the last coin, of the opening and of the digest round

`extendBlock` proves `ExtendBlockStatement`, `finalCoinBlock` proves `FinalCoinBlockStatement`,
`openRound` proves `OpenRoundStatement`, and `digestBlock` proves `DigestBlockStatement`.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1t

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

section Steps

variable (K : Constants C E) (D : C.Coalition) (L : ℕ) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))

/-- The rest of a real step after its `extendMult` with the output `z`. -/
def realAfter {m : ℕ} (T : DrawTables C E m) (i : C.Party) (hs : RunState C)
    (next : Shares C E → E → Plan C E) (z : Shares C E) : PartyM C E RealSpec (HeadOut C E × RunState C) :=
  (challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
    runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (next z r)).run
      (extendState K i hs z)

/-- The rest of a step in the hybrid model after its `extendMult` with the output `z`. -/
def hybridAfter (i : C.Party) (hs : RunState C) (next : Shares C E → E → Plan C E) (z : Shares C E) :
    PartyM C E (CheckSpec C E) (HeadOut C E × RunState C) :=
  (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
    runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next z r)).run (extendState K i hs z)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A real step is the real `extendMult` on the drawn row of its label and then `realAfter`. -/
theorem realStep_eq {m : ℕ} (T : DrawTables C E m) (i : C.Party) (hs : RunState C) (n : ℕ) (hn : n < m)
    (hl : hs.label = L + n) (products : List (Product C E)) (hlen : products.length = 2)
    (next : Shares C E → E → Plan C E) :
    (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (.step products next)).run hs =
      realExtendProg K (frandShare D 2 (knownE n).1 (knownE n).2 (T.freshE ⟨n, hn⟩) (T.freshPairE ⟨n, hn⟩)) i
          (products, hs) >>= fun q => realAfter K D L knownE knownB T i hs next q.1 := by
  have hext : ((drawnCheckBuildingBlocks K D L knownE knownB T i).extendMult products).run hs =
      realExtendProg K (frandShare D 2 (knownE n).1 (knownE n).2 (T.freshE ⟨n, hn⟩) (T.freshPairE ⟨n, hn⟩)) i
        (products, hs) := by
    unfold realExtendProg drawnCheckBuildingBlocks
    simp only [freshLabel, StateT.run_bind, StateT.run_modifyGet, pure_bind, hl, Nat.add_sub_cancel_left, drawnE,
      hn, ↓reduceDIte]
    rfl
  simp only [runPlan, StateT.run_bind]
  rw [hext, RealNetworkC1q.realExtendProg_eq]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun inbox => ?_
  simp only [hlen]
  rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A step in the hybrid model is the call of `F_extendMult` and then `hybridAfter`. -/
theorem hybridStep_eq (i : C.Party) (hs : RunState C) (products : List (Product C E)) (hlen : products.length = 2)
    (next : Shares C E → E → Plan C E) :
    (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (.step products next)).run hs =
      RealNetworkGP.callProg (Sum.inl (Sum.inr products)) (fun o => (extendOutput o).map fun z =>
          (z, extendState K i hs z)) >>= fun q => hybridAfter K i hs next q.1 := by
  have hext : ((hybridCheckBuildingBlocks K i).extendMult products).run hs =
      RealNetworkGP.callProg (Sum.inl (Sum.inr products)) (fun o => (extendOutput o).map fun z =>
        (z, extendState K i hs z)) := by
    simp only [hybridCheckBuildingBlocks, freshLabel, StateT.run_bind, StateT.run_modifyGet, pure_bind,
      RealNetworkGP.callProg, StateT.run_lift, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with _ | ((_ | z) | _) <;> first | rfl | (simp only [hlen]; rfl)
  simp only [runPlan, StateT.run_bind]
  rw [hext]
  simp only [RealNetworkGP.callProg, bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with _ | ((_ | z) | _) <;> rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem timed_realExtendProg (rnd : C.Party → PrssOutput C E) (i : C.Party) (p : List (Product C E) × RunState C) :
    Timed 1 (realExtendProg K rnd i p).run := by
  rw [RealNetworkC1q.realExtendProg_eq]
  exact Timed.exchange_bind 0 _ _ fun _ => timed_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem timed_callProg {I O α : Type} (x : I) (extract : O → Option α) :
    Timed 1 (RealNetworkGP.callProg (C := C) (E := E) x extract).run :=
  Timed.call_bind 0 x _ fun r => by
    cases r.bind extract with
    | none => exact timed_failure 0
    | some a => exact timed_pure a

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The rest of a real step starts with the round of the coin of its challenge, on the drawn row of the
label after the step. -/
theorem realAfter_exchange {m : ℕ} (T : DrawTables C E m) (i : C.Party) (hs : RunState C)
    (next : Shares C E → E → Plan C E) (z : Shares C E) :
    ∃ f, realAfter K D L knownE knownB T i hs next z =
      exchange (openOut i (conv K (localContext i) (drawnE D knownE T (hs.label + 1 - L) i).1) 2) >>= f := by
  simp only [realAfter, challenge, coinKey, drawnCheckBuildingBlocks, coinWith, openSh, freshLabel, extendState,
    StateT.run_bind, StateT.run_get, StateT.run_modifyGet, StateT.run_lift, bind_assoc, pure_bind]
  exact ⟨_, rfl⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The rest of a step in the hybrid model starts with the call of `F_coin` of its challenge. With no reply
it aborts. -/
theorem hybridAfter_call (i : C.Party) (hs : RunState C) (next : Shares C E → E → Plan C E) (z : Shares C E) :
    ∃ f, f none = failure ∧ hybridAfter K i hs next z = call (Sum.inl (Sum.inl 2)) >>= f := by
  simp only [hybridAfter, challenge, coinKey, hybridCheckBuildingBlocks, freshLabel, extendState,
    StateT.run_bind, StateT.run_get, StateT.run_modifyGet, StateT.run_lift, bind_assoc, pure_bind]
  exact ⟨_, rfl, rfl⟩

end Steps

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A computation that sets the counter to `c` keeps it. The types of the states unify only up to the
unfolding of the state of the wrapper, so the goals close with `exact` on this form. -/
theorem bind_map_counter {α β ξ γ S : Type} (y : OracleComp (LocalSpec C) α) (s : α → S) (r : α → β) (c : ℕ)
    (samp : β → OracleComp (LocalSpec C) ξ) (out : β → ξ → γ) :
    (((fun a => ((s a, c), r a)) <$> y) >>= fun a => samp a.2 >>= fun x => pure (a.1, out a.2 x)) =
      (fun q => ((q.1.1, c), q.2)) <$>
        (((fun a => ((s a, c), r a)) <$> y) >>= fun a => samp a.2 >>= fun x => pure (a.1, out a.2 x)) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Two maps and a continuation. The goals close with `exact` on this form, for the same reason as
`bind_map_counter`. -/
theorem map_map_bind {α β γ δ : Type} (x : OracleComp (LocalSpec C) α) (f : α → β) (g : β → γ)
    (k : γ → OracleComp (LocalSpec C) δ) (r : α → OracleComp (LocalSpec C) δ) (h : ∀ a, k (g (f a)) = r a) :
    (g <$> (f <$> x)) >>= k = x >>= r := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, h]

omit [Fintype E] [DecidableEq E] in
/-- A call under the wrapper with no tail counts the call. -/
theorem callPhase_counter {Ia I O α P X : Type} (K : Constants C E) (D : C.Coalition)
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ) (hist : C.Party → C.Term → List Bit)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (F : Functionality C I O (CheckLeak C E) (CheckAnswer C E)) (inp : C.Party → I)
    (extract : C.Party → O → Option α) (pre : OracleComp (LocalSpec C) P) (lk : P → CheckLeak C E)
    (samp : P → CheckAnswer C E → OracleComp (LocalSpec C) X) (outF : P → CheckAnswer C E → X → C.Party → Option O)
    (hF : ∀ (A : Adversary C E Ia (CheckLeak C E) (CheckAnswer C E)) st,
      runFunctionality localRoles D A F st (fun i => if i ∈ D.1 then none else some (inp i)) =
        pre >>= fun p => A.answer st (lk p) >>= fun a => samp p a.2 >>= fun x => pure (a.1, outF p a.2 x))
    (fuel : ℕ) (st : (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails).State) :
    RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails) F
        (fuel + 1) st inp extract =
      (fun r => (((r.1.1, st.2 + 1) : (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails).State),
          r.2)) <$>
        RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails) F
          (fuel + 1) st inp extract := by
  rw [RealNetworkGP.callPhase_eq D F inp extract pre lk samp outF _ (hF _)]
  rw [map_bind]
  refine bind_congr fun p => ?_
  rw [RealNetworkC1q.noTails_answer]
  exact bind_map_counter (c1Sims K D W knownE knownB st.2 st.1 (lk p)) Prod.fst Prod.snd (st.2 + 1) (samp p)
    fun b x j => if j ∈ D.1 then none else (outF p b x j).bind (extract j)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An unused drawn table drops. -/
theorem sameRun_drawTables_drop (prims : Primitives) {m : ℕ} {β : Type} (X : OracleComp (LocalSpec C) β) :
    SameRun prims (drawTables (C := C) (E := E) m >>= fun _ => X) X := by
  unfold drawTables
  simp only [bind_assoc, pure_bind]
  refine (SameRun.bind_right _ fun _ => SameRun.bind_right _ fun _ => SameRun.bind_right _ fun _ =>
    sameRun_drop prims _ _).trans ?_
  refine (SameRun.bind_right _ fun _ => SameRun.bind_right _ fun _ => sameRun_drop prims _ _).trans ?_
  exact (SameRun.bind_right _ fun _ => sameRun_drop prims _ _).trans (sameRun_drop prims _ _)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real rest of the check with no honest operator ends at once. -/
theorem realRest_none (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (count L : ℕ) (T : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) :
    realRest K D W knownE knownB count L T (st, fun _ => none) = pure (st, fun _ => none) := by
  unfold realRest
  rw [executePhase_congr_honest D W _ _ st _ (fun _ => failure) (fun i _ => by simp only [Option.elim_none]),
    executePhase_failure]

omit [Fintype E] in
/-- The part of `c1Mid` after the head with no honest operator ends at once. -/
theorem midRest_none (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit)
    (s : (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg)).State) :
    midRest K D W knownE knownB names count L tg hist (s, fun _ => none) = pure (s.1.1, fun _ => none) := by
  have hnp : ¬ PartialOut D (fun _ : C.Party => (none : Option (HeadOut C E × RunState C))) :=
    fun h => by
      obtain ⟨-, i, -, h⟩ := h
      simp only [Option.isSome_none, Bool.false_eq_true] at h
  unfold midRest
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), executePhase_congr_honest D _ _ _ _ _ (fun _ => failure) (fun i _ => by simp only [Option.elim_none]),
    executePhase_failure, map_pure]

/-- A computation that reads only row `n` of a drawn table is a draw of this row. -/
theorem sameRun_drawTables_row (prims : Primitives) {m : ℕ} {β : Type} (n : ℕ) (hn : n < m)
    (G : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → OracleComp (LocalSpec C) β) :
    SameRun prims (drawTables (C := C) (E := E) m >>= fun T => G (T.freshE ⟨n, hn⟩) (T.freshPairE ⟨n, hn⟩))
      (liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a =>
        liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b => G a b) := by
  refine (resample prims n _).trans ?_
  refine SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => ?_
  simp only [setRow, ↓reduceIte]
  exact sameRun_drawTables_drop prims _

section After

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
  (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- The real run after the phase of `extendMult` at position `N`, with the outputs `o`. It draws the table
rows from `N + 1` on. -/
def realRestAfter (N d : ℕ) (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State)
    (o : C.Party → Option (Shares C E × RunState C)) (hs : C.Party → RunState C)
    (next : C.Party → Shares C E → E → Plan C E) : OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
    executePhase localRoles D W noFunctionality (2 * d + 2) st (fun i => (o i).elim failure fun q =>
        realAfter K D L knownE knownB (splice (N + 1) T0 T) i (hs i) (next i) q.1) >>=
      realRest K D W knownE knownB count L (splice (N + 1) T0 T)

/-- The run in the hybrid model after the call of `F_extendMult` at position `N` with no tail, with the
outputs `o`. The tail of the reply runs after a partial output. -/
def hybridRest (N d : ℕ) (st : W.State) (mem : C1Memory C E) (o : C.Party → Option (Shares C E × RunState C))
    (hs : C.Party → RunState C) (next : C.Party → Shares C E → E → Plan C E) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  (if PartialOut D o then
      (fun s' => (((s', N + 1) : (c1WrapperWith K D W knownE knownB count hist names
        (c1HeadTails K D W knownE knownB count L tg)).State), o)) <$>
        c1HeadTails K D W knownE knownB count L tg N (liveSet D o) (st, mem)
    else pure ((((st, mem), N + 1) : (c1WrapperWith K D W knownE knownB count hist names
        (c1HeadTails K D W knownE knownB count L tg)).State), o)) >>= fun r =>
    executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (2 * d + 3) r.1
        (fun i => (r.2 i).elim failure fun q => hybridAfter K i (hs i) (next i) q.1) >>=
      midRest K D W knownE knownB names count L tg hist

/-- The claim after the phase of `extendMult` of step `j`, for each output. -/
theorem afterExtend (j d : ℕ) (hjd : j + d + 1 = halvings count)
    (hIH : CoinSuffix prims K D W knownE knownB names count L tg hist j d)
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E)
    (o : C.Party → Option (Shares C E × RunState C)) (hs : C.Party → RunState C)
    (next : C.Party → Shares C E → E → Plan C E) (hnext : ∀ i, i ∉ D.1 → ∀ z r, PlanOK (next i z r) d)
    (hlab : ∀ i, i ∉ D.1 → (hs i).label = L + (2 * j + 1) ∧ (hs i).tag = tg) :
    SameRun prims (realRestAfter K D W knownE knownB count L (2 * j + 1) d T0 st o hs next)
      (hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d st mem o hs next) := by
  by_cases hnone : ∀ i, i ∉ D.1 → o i = none
  · have hnp : ¬ PartialOut D o := fun h => by
      obtain ⟨-, i, hi, h⟩ := h
      simp only [hnone i hi, Option.isSome_none, Bool.false_eq_true] at h
    unfold realRestAfter hybridRest
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), pure_bind, executePhase_congr_honest D _ _ _ _ _ (fun _ => failure)
      (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure, pure_bind, midRest_none]
    refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) (sameRun_drawTables_drop prims _)
    rw [executePhase_congr_honest D W _ _ st _ (fun _ => failure) (fun i hi => by simp only [hnone i hi,
      Option.elim_none]), executePhase_failure, pure_bind, realRest_none]
  by_cases hfull : ∀ i, i ∉ D.1 → (o i).isSome
  · have hnp : ¬ PartialOut D o := fun h => by
      obtain ⟨⟨i, hi, h⟩, -⟩ := h
      have := hfull i hi
      simp only [h, Option.isSome_none, Bool.false_eq_true] at this
    let zf : C.Party → Shares C E := fun i => match o i with
      | some q => q.1
      | none => fun _ _ => 0
    have hz : ∀ i, i ∉ D.1 → ∃ q, o i = some q ∧ zf i = q.1 := fun i hi => by
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      exact ⟨q, hq, by simp only [zf, hq]⟩
    have hIH' := hIH T0 st mem (fun i => next i (zf i)) (fun i => extendState K i (hs i) (zf i))
      (fun i hi r => hnext i hi (zf i) r)
      (fun i hi => ⟨by simp only [extendState, (hlab i hi).1]; omega, (hlab i hi).2⟩)
    unfold realRestAfter hybridRest
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), pure_bind, show 2 * j + 1 + 1 = 2 * j + 2 by omega]
    refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) (hIH'.trans (SameRun.of_eq ?_))
    · congr 1
      refine executePhase_congr_honest D W _ _ st _ _ fun i hi => ?_
      obtain ⟨q, hq, hzq⟩ := hz i hi
      rw [hq, Option.elim_some, ← hzq]
      rfl
    · congr 1
      refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
      obtain ⟨q, hq, hzq⟩ := hz i hi
      change _ = (o i).elim failure fun q => hybridAfter K i (hs i) (next i) q.1
      rw [hq, Option.elim_some, ← hzq]
      rfl
  have hp : PartialOut D o := by
    refine ⟨?_, ?_⟩
    · push Not at hfull
      obtain ⟨i, hi, h⟩ := hfull
      exact ⟨i, hi, Option.not_isSome_iff_eq_none.1 h⟩
    · push Not at hnone
      obtain ⟨i, hi, h⟩ := hnone
      exact ⟨i, hi, Option.isSome_iff_ne_none.2 h⟩
  have hNm : 2 * j + 1 + 1 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  have hreal : SameRun prims (realRestAfter K D W knownE knownB count L (2 * j + 1) d T0 st o hs next)
      (liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a =>
        liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b =>
          W.round st (fun c i => if c ∈ D.1 ∧ i ∈ liveSet D o then
            openOut i (conv K (localContext i)
              (frandShare D 2 (knownE (2 * j + 1 + 1)).1 (knownE (2 * j + 1 + 1)).2 a b i).1) 2 c else none) >>=
            fun r => pure (r.1, fun _ => none)) := by
    let G : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
      fun a b => W.round st (fun c i => if c ∈ D.1 ∧ i ∈ liveSet D o then
        openOut i (conv K (localContext i)
          (frandShare D 2 (knownE (2 * j + 1 + 1)).1 (knownE (2 * j + 1 + 1)).2 a b i).1) 2 c else none) >>=
        fun r => pure (r.1, fun _ => none)
    have hT : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count),
        executePhase localRoles D W noFunctionality (2 * d + 2) st (fun i => (o i).elim failure fun q =>
            realAfter K D L knownE knownB (splice (2 * j + 1 + 1) T0 T) i (hs i) (next i) q.1) >>=
          realRest K D W knownE knownB count L (splice (2 * j + 1 + 1) T0 T) =
        G (T.freshE ⟨2 * j + 1 + 1, hNm⟩) (T.freshPairE ⟨2 * j + 1 + 1, hNm⟩) := by
      intro T
      have hex := fun i (q : Shares C E × RunState C) =>
        realAfter_exchange K D L knownE knownB (splice (2 * j + 1 + 1) T0 T) i (hs i) (next i) q.1
      choose f hf using hex
      rw [show 2 * d + 2 = 2 * d + 1 + 1 by omega, RealNetworkRC.roundPhase_partial D W noFunctionality
        (fun i (q : Shares C E × RunState C) =>
          realAfter K D L knownE knownB (splice (2 * j + 1 + 1) T0 T) i (hs i) (next i) q.1)
        (fun i _ => openOut i (conv K (localContext i)
          (drawnE D knownE (splice (2 * j + 1 + 1) T0 T) ((hs i).label + 1 - L) i).1) 2)
        f (fun i q => by rw [hf, advance_exchange_bind]) (2 * d + 1) st o hp]
      simp only [bind_assoc, pure_bind, realRest_none, G]
      congr 2
      funext c i
      by_cases h : c ∈ D.1 ∧ i ∈ liveSet D o
      · obtain ⟨hi, hs'⟩ := (Finset.mem_filter.1 h.2).2
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs'
        have hl : (hs i).label + 1 - L = 2 * j + 1 + 1 := by
          rw [(hlab i hi).1]
          omega
        have h' : c ∈ D.1 ∧ i ∈ RealNetworkRC.liveSet D o := h
        simp only [h, h', and_self, ↓reduceIte, hv, Option.elim_some, hl, drawnE, hNm, ↓reduceDIte, splice,
          lt_self_iff_false]
      · have h' : ¬ (c ∈ D.1 ∧ i ∈ RealNetworkRC.liveSet D o) := h
        simp only [h, h', ↓reduceIte]
    unfold realRestAfter
    exact (SameRun.bind_right _ fun T => SameRun.of_eq (hT T)).trans
      (sameRun_drawTables_row prims (2 * j + 1 + 1) hNm G)
  have hhyb : hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d st mem o hs next =
      RealNetworkC1s.coinTail K D W (knownE (2 * j + 1 + 1)).1 (knownE (2 * j + 1 + 1)).2 2 (liveSet D o) st >>= fun st' =>
        pure (st', fun _ => none) := by
    have htail : c1HeadTails K D W knownE knownB count L tg (2 * j + 1) (liveSet D o) (st, mem) =
        (fun st' => (st', mem)) <$> RealNetworkC1s.coinTail K D W (knownE (2 * j + 1 + 1)).1
          (knownE (2 * j + 1 + 1)).2 2 (liveSet D o) st := by
      simp only [c1HeadTails, c1Tails, show 2 * j + 1 ≠ 2 * halvings count + 2 by omega, show 2 * j + 1 ≠ 0 by omega,
        show ¬ 2 * halvings count < 2 * j + 1 by omega, show (2 * j + 1) % 2 = 1 by omega, ↓reduceIte]
    have hg := fun i (q : Shares C E × RunState C) => hybridAfter_call K i (hs i) (next i) q.1
    choose g hgn hgeq using hg
    have habort : ∀ s : (c1WrapperWith K D W knownE knownB count hist names
        (c1HeadTails K D W knownE knownB count L tg)).State,
        executePhase localRoles D
          (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
          (checkFunctionalities K) (2 * d + 3) s
          (fun i => (o i).elim failure fun q => hybridAfter K i (hs i) (next i) q.1) = pure (s, fun _ => none) := by
      intro s
      have hprog : (fun i => (o i).elim failure fun q => hybridAfter K i (hs i) (next i) q.1) =
          fun i => optionalCall ((o i).map fun _ => Sum.inl (Sum.inl 2))
            (fun r => (o i).elim failure fun q => g i q r) := by
        funext i
        cases o i with
        | none => rfl
        | some q => exact hgeq i q
      rw [hprog]
      refine executePhase_partialCall_abort D _ _ (2 * d + 2) s _ _ (fun i _ => ?_) ?_
      · cases o i with
        | none => rfl
        | some q => exact hgn i q
      · obtain ⟨⟨i, hi, h⟩, -⟩ := hp
        exact ⟨i, hi, by simp only [h, Option.map_none]⟩
    unfold hybridRest
    rw [ite_eq_left_of_eq_true _ _ (eq_true hp), htail]
    exact map_map_bind _ (fun st' => (st', mem)) (fun s' => ((s', 2 * j + 1 + 1), o)) _ _ fun st' =>
      (congrArg (· >>= midRest K D W knownE knownB names count L tg hist) (habort _)).trans
        (by rw [pure_bind, midRest_none])
  rw [hhyb]
  refine hreal.trans (SameRun.of_eq ?_)
  simp only [RealNetworkC1s.coinTail, bind_assoc, pure_bind]

end After

theorem extendBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) : ExtendBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist j d hjd hIH T0 st mem p hs hRel hlab
  have hNm : 2 * j + 1 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
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
  let ext : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) →
      OracleComp (LocalSpec C) (W.State × (C.Party → Option (Shares C E × RunState C))) := fun a b =>
    executePhase localRoles D W noFunctionality (0 + 1) st fun i =>
      realExtendProg K (frandShare D 2 (knownE (2 * j + 1)).1 (knownE (2 * j + 1)).2 a b) i (products i, hs i)
  have hreal : SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * (d + 1) + 1) st
            (fun i => (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB
              (splice (2 * j + 1) T0 T) i) (p i)).run (hs i)) >>=
          realRest K D W knownE knownB count L (splice (2 * j + 1) T0 T))
      (liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a =>
        liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b =>
          ext a b >>= fun r =>
            realRestAfter K D W knownE knownB count L (2 * j + 1) d (setRow T0 (2 * j + 1) a b) r.1 r.2 hs next) := by
    refine (resample prims (2 * j + 1) _).trans ?_
    refine SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => ?_
    simp only [splice_setRow]
    have hstep : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count), SameRun prims
        (executePhase localRoles D W noFunctionality (2 * (d + 1) + 1) st
            (fun i => (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB
              (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T) i) (p i)).run (hs i)) >>=
          realRest K D W knownE knownB count L (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T))
        (ext a b >>= fun r => executePhase localRoles D W noFunctionality (2 * d + 2) r.1 (fun i => (r.2 i).elim failure
            fun q => realAfter K D L knownE knownB (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T) i (hs i)
              (next i) q.1) >>=
          realRest K D W knownE knownB count L (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T)) := by
      intro T
      have hE : (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T).freshE ⟨2 * j + 1, hNm⟩ = a := by
        simp only [splice, setRow]
        simp
      have hP : (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T).freshPairE ⟨2 * j + 1, hNm⟩ = b := by
        simp only [splice, setRow]
        simp
      have eT : executePhase localRoles D W noFunctionality (2 * (d + 1) + 1) st
          (fun i => (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB
            (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T) i) (p i)).run (hs i)) =
        executePhase localRoles D W noFunctionality (1 + (2 * d + 2)) st (fun i =>
          realExtendProg K (frandShare D 2 (knownE (2 * j + 1)).1 (knownE (2 * j + 1)).2 a b) i (products i, hs i) >>=
            fun q => realAfter K D L knownE knownB (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T) i (hs i)
              (next i) q.1) := by
        rw [show 2 * (d + 1) + 1 = 1 + (2 * d + 2) by omega]
        refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
        rw [(hp i hi).1, realStep_eq K D L knownE knownB _ i (hs i) (2 * j + 1) hNm (hlab i hi).1 (products i)
          (hp i hi).2.1 (next i), hE, hP]
      rw [eT]
      refine ((executePhase_bind prims D W noFunctionality 1 (2 * d + 2) st _ _
        fun i _ => timed_realExtendProg K _ i _).bind fun _ => SameRun.refl prims _).trans ?_
      exact SameRun.of_eq (bind_assoc _ _ _)
    refine (SameRun.bind_right _ hstep).trans ?_
    exact sameRun_swap prims (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count)) (ext a b)
      fun T r => executePhase localRoles D W noFunctionality (2 * d + 2) r.1 (fun i => (r.2 i).elim failure
          fun q => realAfter K D L knownE knownB (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T) i (hs i)
            (next i) q.1) >>=
        realRest K D W knownE knownB count L (splice (2 * j + 1 + 1) (setRow T0 (2 * j + 1) a b) T)
  have hhyb : SameRun prims
      (executePhase localRoles D
          (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
          (checkFunctionalities K) (2 * (d + 1) + 2) ((st, mem), 2 * j + 1)
          (fun i => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (p i)).run (hs i)) >>=
        midRest K D W knownE knownB names count L tg hist)
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (0 + 1) ((st, mem), 2 * j + 1) (fun i => Sum.inl (Sum.inr (products i)))
          (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)) >>= fun r =>
        hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d r.1.1.1 r.1.1.2 r.2 hs next) := by
    have eprog : executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (2 * (d + 1) + 2) ((st, mem), 2 * j + 1)
        (fun i => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (p i)).run (hs i)) =
      executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (1 + (2 * d + 3)) ((st, mem), 2 * j + 1)
        (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inr (products i))) (fun o => (extendOutput o).map fun z =>
          (z, extendState K i (hs i) z)) >>= fun q => hybridAfter K i (hs i) (next i) q.1) := by
      rw [show 2 * (d + 1) + 2 = 1 + (2 * d + 3) by omega]
      refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
      rw [(hp i hi).1]
      exact hybridStep_eq K i (hs i) (products i) (hp i hi).2.1 (next i)
    rw [eprog]
    refine ((executePhase_bind prims D _ _ 1 (2 * d + 3) _ _ _ fun i _ => timed_callProg _ _).bind
      fun _ => SameRun.refl prims _).trans ?_
    refine (SameRun.of_eq (bind_assoc _ _ _)).trans ?_
    refine ((extendPhase_tail prims K D W knownE knownB count hist names hn
      (c1HeadTails K D W knownE knownB count L tg) products hs 0 (st, mem) (2 * j + 1)).bind
      fun _ => SameRun.refl prims _).trans ?_
    refine SameRun.of_eq ?_
    rw [bind_assoc, callPhase_counter K D W knownE knownB count hist names (checkFunctionalities K)
      (fun i => Sum.inl (Sum.inr (products i))) (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
      (pure () : OracleComp (LocalSpec C) Unit) (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D products r fresh) (fun A st => extendRun_form K D A st products),
      bind_map_left, bind_map_left]
    rfl
  have hhop := RealNetworkC1q.extendHop prims K D W knownE knownB count hist names hn (2 * j + 1) 0 0 (st, mem)
    products hs fun i hi => (hp i hi).2.1
  have hnext : ∀ i, i ∉ D.1 → ∀ z r, PlanOK (next i z r) d := fun i hi => (hp i hi).2.2
  have hmem : ∀ (st' : W.State) (mem' : C1Memory C E) (o : C.Party → Option (Shares C E × RunState C)),
      SameRun prims (hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d st' mem o hs next)
        (hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d st' mem' o hs next) :=
    fun st' mem' o =>
      (afterExtend prims K D W knownE knownB names count L tg hist j d hjd hIH T0 st' mem o hs next hnext hlab).symm.trans
        (afterExtend prims K D W knownE knownB names count L tg hist j d hjd hIH T0 st' mem' o hs next hnext hlab)
  refine hreal.trans ?_
  refine SameRun.trans ?_ hhyb.symm
  have hafter : ∀ a b, SameRun prims (ext a b >>= fun r =>
        realRestAfter K D W knownE knownB count L (2 * j + 1) d (setRow T0 (2 * j + 1) a b) r.1 r.2 hs next)
      (ext a b >>= fun r => hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d r.1 mem r.2 hs next) :=
    fun a b => SameRun.bind_right (ext a b) fun r =>
      afterExtend prims K D W knownE knownB names count L tg hist j d hjd hIH (setRow T0 (2 * j + 1) a b) r.1 mem r.2
        hs next hnext hlab
  refine (SameRun.bind_right (liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)) fun a =>
    SameRun.bind_right (liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C)) fun b => hafter a b).trans ?_
  refine SameRun.trans (SameRun.of_eq ?_) ((hhop.bind (f := fun r =>
      hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d r.1 mem r.2 hs next)
    (g := fun r => hybridRest K D W knownE knownB names count L tg hist (2 * j + 1) d r.1 mem r.2 hs next)
    fun _ => SameRun.refl prims _).trans ?_)
  · simp only [ext, bind_assoc]
  · rw [bind_map_left]
    exact SameRun.bind_right _ fun r => hmem r.1.1.1 r.1.1.2 r.2

end ThresholdLeanXmssSecurity.RealNetworkC1t

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1t

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

section Programs

variable (K : Constants C E)

/-- The search of the challenge from the values `vals` of the coin and the end of the check, from the
run state `st` before the coin. -/
def restC {ι : Type} {G : OracleSpec ι} (i : C.Party) (st : RunState C) (v : HeadOut C E) (vals : List E) :
    PartyM C E G Unit :=
  oracleStep (challengeQuery K st.tag st.label vals) >>= fun r => match r with
    | some r => (openTailOf K (localContext i) v r).run' ⟨st.history, st.label + 1, st.tag⟩
    | none => failure

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real end of the check from its last challenge is the real coin on the drawn row of its label, and
then `restC`. -/
theorem realChallenge_split (D : C.Coalition) (L : ℕ) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) {m : ℕ} (T : DrawTables C E m) (i : C.Party)
    (st : RunState C) (v : HeadOut C E) :
    (challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
        openTailOf K (localContext i) v r).run' st =
      openSh K (localContext i) (conv K (localContext i) (drawnE D knownE T (st.label - L) i).1) 2 >>= fun w =>
        restC K i st v (vector 2 w) := by
  simp only [challenge, coinKey, bind_assoc, drawnCheckBuildingBlocks, freshLabel, coinWith, restC, challengeQuery,
    oracleStep_bind, StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, StateT.run_get,
    pure_bind, map_bind]
  refine bind_congr fun w => bind_congr fun key => bind_congr fun r => ?_
  cases r <;> rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The end of the check in the hybrid model from its last challenge is the call of `F_coin`, and then
`restC`. -/
theorem hybridChallenge_split (i : C.Party) (st : RunState C) (v : HeadOut C E) :
    (challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) v r).run' st =
      RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= restC K i st v := by
  rw [challenge_run']
  simp only [RealNetworkGP.callProg, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with _ | ((vs | z) | w) <;>
    simp only [Option.bind_none, Option.bind_some, coinOutput, RealNetworkGP.ofOption, pure_bind, failure_bind, restC]
  refine bind_congr fun r => ?_
  cases r <;> rfl

end Programs

omit [Fintype E] in
/-- After the coin with the values `vals` at each honest receiver, the search and the round of `OpenSh`
are the same run in both models. -/
theorem afterCoin (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) (hOpen : OpenRound prims K D W knownE knownB names count L tg hist)
    (b : C.Party → HeadOut C E) (hs : C.Party → RunState C)
    (hlab : ∀ i, i ∉ D.1 → (hs i).label = L + (2 * halvings count + 4) ∧ (hs i).tag = tg)
    (st : W.State) (mem : C1Memory C E) (vals : List E) (O : C.Party → Option (List E))
    (hO : ∀ i, i ∉ D.1 → O i = none ∨ O i = some vals) :
    SameRun prims (executePhase localRoles D W noFunctionality 4 st
        (fun i => (O i).elim failure (restC K i (hs i) (b i))))
      ((fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) 2 ((st, mem), 2 * halvings count + 4 + 1)
        (fun i => (O i).elim failure (restC K i (hs i) (b i)))) := by
  let inp : C.Party → Option Unit := fun i => (O i).map fun _ => ()
  let next : ∀ {ι : Type} {G : OracleSpec ι}, C.Party → Option E → Unit → PartyM C E G Unit :=
    fun i c _ => match c with
      | some r => (openTailOf K (localContext i) (b i) r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
      | none => failure
  have hprog : ∀ {ι : Type} {G : OracleSpec ι} (i : C.Party), i ∉ D.1 →
      ((O i).elim failure (restC K i (hs i) (b i)) : PartyM C E G Unit) =
        (inp i).elim failure fun u => oracleStep (challengeQuery K tg (L + (2 * halvings count + 4)) vals) >>=
          fun c => next i c u := by
    intro ι G i hi
    rcases hO i hi with h | h
    · simp only [inp, h, Option.map_none, Option.elim_none]
    · simp only [inp, h, Option.map_some, Option.elim_some, restC]
      rw [← (hlab i hi).1, ← (hlab i hi).2]
  rw [executePhase_congr_honest D W _ _ st _ _ hprog, executePhase_congr_honest D _ _ _ _ _ _ hprog]
  by_cases hlive : ∃ i ∉ D.1, (inp i).isSome
  · refine (RealNetworkC1q.hoist prims D W noFunctionality 4 st _ inp (fun i c u => next i c u) hlive).trans ?_
    refine SameRun.trans ?_ ((RealNetworkC1q.hoist prims D
      (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
      (checkFunctionalities K) 2 ((st, mem), 2 * halvings count + 4 + 1) _ inp (fun i c u => next i c u)
      hlive).map (fun r => (r.1.1.1, r.2))).symm
    rw [map_bind]
    refine SameRun.bind_right _ fun c => ?_
    cases c with
    | none =>
      refine SameRun.of_eq ?_
      rw [executePhase_congr_honest D W _ _ st _ (fun _ => failure) (fun i _ => by cases inp i <;> rfl),
        executePhase_failure, executePhase_congr_honest D _ _ _ _ _ (fun _ => failure)
          (fun i _ => by cases inp i <;> rfl), executePhase_failure, map_pure]
    | some r =>
      let o' : C.Party → Option (HeadOut C E × E × RunState C) := fun i =>
        (inp i).map fun _ => (b i, r, ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩)
      refine (SameRun.of_eq (executePhase_congr_honest D W _ _ st _ _ fun i _ => ?_)).trans
        ((hOpen st mem (2 * halvings count + 4 + 1) o' (by omega)).trans (SameRun.of_eq ?_))
      · simp only [o']
        cases inp i <;> rfl
      · congr 1
        refine executePhase_congr_honest D _ _ _ _ _ _ fun i _ => ?_
        simp only [o']
        cases inp i <;> rfl
  · push Not at hlive
    have hf : ∀ {ι : Type} {G : OracleSpec ι} (i : C.Party), i ∉ D.1 →
        ((inp i).elim failure fun u => oracleStep (challengeQuery K tg (L + (2 * halvings count + 4)) vals) >>=
          fun c => next i c u : PartyM C E G Unit) = failure := by
      intro ι G i hi
      have h := hlive i hi
      cases hx : inp i with
      | none => rfl
      | some u =>
        rw [hx] at h
        exact absurd rfl h
    refine SameRun.of_eq ?_
    rw [executePhase_congr_honest D W _ _ st _ _ hf, executePhase_failure, executePhase_congr_honest D _ _ _ _ _ _ hf,
      executePhase_failure, map_pure]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A tail that is `pure`, and a next phase under a map. The goals close with `exact` on this form. -/
theorem map_bind_tail {α β γ : Type} (x : OracleComp (LocalSpec C) α) (t : α → OracleComp (LocalSpec C) α)
    (k : α → OracleComp (LocalSpec C) β) (f : β → γ) (ht : ∀ r, t r = pure r) :
    f <$> ((x >>= t) >>= k) = x >>= fun r => f <$> k r := by
  rw [show t = pure from funext ht, bind_pure, map_bind]

theorem finalCoinBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    FinalCoinBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist hOpen T0 st mem b hs hlab
  have hNm : 2 * halvings count + 4 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  let K2 : W.State × (C.Party → Option (List E)) → OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
    fun q => executePhase localRoles D W noFunctionality 4 q.1 (fun i => (q.2 i).elim failure (restC K i (hs i) (b i)))
  let G : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
    fun a c => ((fun r => (r.1, fun i => (r.2 i).map (vector 2))) <$> RealNetworkC1s.realCoinPhase K D W noFunctionality
      (frandShare D 2 (knownE (2 * halvings count + 4)).1 (knownE (2 * halvings count + 4)).2 a c) 2 (0 + 1) st
      (fun _ => some ())) >>= K2
  have hT : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count), SameRun prims
      (executePhase localRoles D W noFunctionality 5 st (fun i => (challenge K (drawnCheckBuildingBlocks K D L knownE
        knownB (splice (2 * halvings count + 4) T0 T) i) >>= fun r => openTailOf K (localContext i) (b i) r).run' (hs i)))
      (G (T.freshE ⟨2 * halvings count + 4, hNm⟩) (T.freshPairE ⟨2 * halvings count + 4, hNm⟩)) := by
    intro T
    have e : executePhase localRoles D W noFunctionality 5 st (fun i => (challenge K (drawnCheckBuildingBlocks K D L
        knownE knownB (splice (2 * halvings count + 4) T0 T) i) >>= fun r =>
          openTailOf K (localContext i) (b i) r).run' (hs i)) =
      executePhase localRoles D W noFunctionality (1 + 4) st (fun i =>
        openSh K (localContext i) (conv K (localContext i) (frandShare D 2 (knownE (2 * halvings count + 4)).1
          (knownE (2 * halvings count + 4)).2 (T.freshE ⟨2 * halvings count + 4, hNm⟩)
          (T.freshPairE ⟨2 * halvings count + 4, hNm⟩) i).1) 2 >>= fun w =>
            restC K i (hs i) (b i) (vector 2 w)) := by
      refine executePhase_congr_honest D W _ _ st _ _ fun i hi => ?_
      have hl : (hs i).label - L = 2 * halvings count + 4 := by
        rw [(hlab i hi).1]
        omega
      rw [realChallenge_split, hl]
      simp only [drawnE, hNm, ↓reduceDIte, splice, lt_self_iff_false, ↓reduceIte]
    rw [e]
    refine (executePhase_bind prims D W noFunctionality 1 4 st _ _
      fun i _ => timed_openSh K (localContext i) _ 2).trans (SameRun.of_eq ?_)
    simp only [G, K2, bind_map_left]
    refine bind_congr fun r => ?_
    congr 1
    funext i
    cases r.2 i <;> rfl
  have hhop := RealNetworkC1q.coinHop prims K D W knownE knownB count hist names hn (2 * halvings count + 4) 0 0
    (st, mem)
  have hreal : SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality 5 st (fun i => (challenge K (drawnCheckBuildingBlocks K D L knownE
          knownB (splice (2 * halvings count + 4) T0 T) i) >>= fun r => openTailOf K (localContext i) (b i) r).run' (hs i)))
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (0 + 1) ((st, mem), 2 * halvings count + 4) (fun _ => Sum.inl (Sum.inl 2))
          (fun _ => coinOutput) >>= fun r => K2 (r.1.1.1, r.2)) := by
    refine (SameRun.bind_right _ hT).trans ((sameRun_drawTables_row prims _ hNm G).trans ?_)
    refine (SameRun.of_eq ?_).trans ((hhop.bind (f := K2) (g := K2) fun _ => SameRun.refl prims _).trans
      (SameRun.of_eq ?_))
    · simp only [G, bind_assoc]
    · rw [bind_map_left]
  have hct : ∀ (live : Finset C.Party) (s : W.State × C1Memory C E),
      c1Tails K D W knownE knownB count L tg (2 * halvings count + 4) live s = pure s := fun live s => by
    simp only [c1Tails, show 2 * halvings count + 4 ≠ 0 by omega,
      show 2 * halvings count + 4 ≠ 2 * halvings count + 2 by omega,
      show 2 * halvings count < 2 * halvings count + 4 by omega, ↓reduceIte]
  have hhyb : SameRun prims
      ((fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) 3 ((st, mem), 2 * halvings count + 4)
        (fun i => (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
          openTailOf K (localContext i) (b i) r).run' (hs i)))
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (0 + 1) ((st, mem), 2 * halvings count + 4) (fun _ => Sum.inl (Sum.inl 2))
          (fun _ => coinOutput) >>= fun r => (fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
            (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
            (checkFunctionalities K) 2 r.1 (fun i => (r.2 i).elim failure (restC K i (hs i) (b i)))) := by
    rw [show 3 = 1 + 2 by rfl, executePhase_congr_honest D _ _ _ _ _
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= restC K i (hs i) (b i))
      (fun i _ => hybridChallenge_split K i (hs i) (b i))]
    refine ((executePhase_bind prims D _ _ 1 2 _ _ _ fun i _ => timed_callProg _ _).map _).trans ?_
    refine (((coinPhase_tail prims K D W knownE knownB count L tg hist names hn 0 (st, mem)
      (2 * halvings count + 4)).bind fun _ => SameRun.refl prims _).map _).trans (SameRun.of_eq ?_)
    exact map_bind_tail _ _ _ _ fun r => by
      split_ifs
      · exact (congrArg (fun z => (fun s' => ((s', r.1.2), r.2)) <$> z) (hct (liveSet D r.2) r.1.1)).trans (map_pure _ _)
      · rfl
  refine hreal.trans (SameRun.trans ?_ hhyb.symm)
  rw [callPhase_counter K D W knownE knownB count hist names (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2))
    (fun _ => coinOutput) (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
    (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r)
    (fun A st => coinRun_form K D A st), bind_map_left, bind_map_left,
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st)]
  rw [bind_assoc, bind_assoc]
  refine SameRun.bind_right _ fun v => ?_
  rw [bind_assoc, bind_assoc]
  refine SameRun.bind_right _ fun a => ?_
  simp only [pure_bind]
  refine afterCoin prims K D W knownE knownB names count L tg hist hOpen b hs hlab a.1.1.1 a.1.1.2 (List.ofFn v) _
    fun i hi => ?_
  unfold coinOutputs
  by_cases h : i ∈ coinReply a.2
  · exact Or.inr (by simp [hi, h, coinOutput])
  · exact Or.inl (by simp [hi, h])

end ThresholdLeanXmssSecurity.RealNetworkC1t

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1t

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

section OpenTail

variable [Field E] [Algebra Bit E]

/-- The opened values of `OpenSh` in `openTailOf`. -/
def openTailValues (v : HeadOut C E) (r : E) (K : Constants C E) (ctx : Context C) : ℕ → E :=
  let wa := conv K ctx v.2.2.2.1 0
  let wb := conv K ctx v.2.2.2.1 1
  let q₀ := conv K ctx v.2.2.2.2 0
  let q₂ := conv K ctx v.2.2.2.2 1
  fun k => match k with
    | 0 => wa + r * (wa + v.1)
    | 1 => wb + r * (wb + v.2.1)
    | _ => q₀ + (v.2.2.1 + q₀ + q₂) * r + q₂ * r ^ 2

/-- The message of `openTailOf`. -/
def openTailOut (K : Constants C E) (ctx : Context C) (v : HeadOut C E) (r : E) : Mail C E :=
  fun j => if j = ctx.self then none else some (.elements (vector 3 (openTailValues v r K ctx)))

/-- The output of `openTailOf` from its inbox. -/
def openTailRes (K : Constants C E) (ctx : Context C) (v : HeadOut C E) (r : E) (inbox : Mail C E) : Option Unit :=
  let share : C.Party → ℕ → E := fun j g =>
    if j = ctx.self then openTailValues v r K ctx g else Msg.elementAt (inbox j) g
  let first := Finset.univ.filter fun l : C.Party => l.val < C.t
  let opened : ℕ → E := fun g => ∑ l ∈ first, lagrangeFirst K 0 l * share l g
  if (∀ j : C.Party, ∀ g < 3, share j g = ∑ l ∈ first, lagrangeFirst K (K.point j) l * share l g) ∧
    opened 0 * opened 1 = opened 2 then some () else none

omit [Field E] [Algebra Bit E] in
theorem require_bind_require {ι : Type} {G : OracleSpec ι} (A B : Prop) {h : Decidable (A ∧ B)} :
    (require A >>= fun _ => require B : PartyM C E G Unit) = OptionT.mk (pure (if A ∧ B then some () else none)) := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [require, hA, hB, ite_true, ite_false, pure_bind, and_self,
    and_false, false_and] <;> rfl

theorem openTailOf_run' {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C) (v : HeadOut C E)
    (r : E) (s : RunState C) :
    (openTailOf (G := G) K ctx v r).run' s =
      exchange (openTailOut K ctx v r) >>= fun inbox => OptionT.mk (pure (openTailRes K ctx v r inbox)) := by
  simp only [openTailOf, openSh, StateT.run'_eq, StateT.run_bind, StateT.run_lift, bind_assoc, map_bind]
  refine bind_congr fun inbox => ?_
  simp only [pure_bind, map_pure, bind_pure]
  exact (require_bind_require _ _).trans rfl

end OpenTail

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

omit [Fintype E] [DecidableEq E] in
/-- A round of the wrapper at a position other than the digest round is a round of `W`. -/
theorem c1Wrapper_round {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (count : ℕ) (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (st : W.State) (mem : C1Memory C E) (k : ℕ) (hk : k ≠ 2 * halvings count + 4)
    (m : C.Party → C.Party → Option (Msg E)) :
    (c1WrapperWith K D W knownE knownB count hist names tails).round ((st, mem), k) m =
      (fun r => ((((r.1, mem), k) : (c1WrapperWith K D W knownE knownB count hist names tails).State), r.2)) <$>
        W.round st m := by
  simp only [c1WrapperWith, relabel, withMemory, c1Rtails, hk, ↓reduceIte, map_pure, bind_map_left, ite_self]
  rw [map_eq_bind_pure_comp]
  rfl

omit [Fintype E] in
theorem openRound (prims : Primitives) (K : Constants C E) (D : C.Coalition) : OpenRoundStatement prims K D := by
  intro Ia W knownE knownB names count L tg hist st mem k o hk
  by_cases hnone : ∀ i ∉ D.1, o i = none
  · rw [executePhase_congr_honest D W _ 4 st _ (fun _ => failure) (fun i hi => by simp only [hnone i hi, Option.elim_none]),
      executePhase_failure, executePhase_congr_honest D _ _ 2 _ _ (fun _ => failure)
        (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure, map_pure]
    exact SameRun.refl prims _
  by_cases hfull : ∀ i ∉ D.1, (o i).isSome
  · have hprog {I O : Type} : ∀ i, i ∉ D.1 →
        ((o i).elim failure fun z => (openTailOf (G := CallSpec I O) K (localContext i) z.1 z.2.1).run' z.2.2) =
          exchange ((o i).elim (fun _ => none) fun z => openTailOut K (localContext i) z.1 z.2.1) >>= fun inbox =>
            OptionT.mk (pure ((o i).elim none fun z => openTailRes K (localContext i) z.1 z.2.1 inbox)) := by
      intro i hi
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      simp only [hz, Option.elim_some]
      exact openTailOf_run' K (localContext i) z.1 z.2.1 z.2.2
    refine (SameRun.of_eq (RealNetworkC1q.roundPhase_full D W noFunctionality _ _ _ hprog 3 st)).trans ?_
    refine SameRun.trans ?_ (SameRun.of_eq (congrArg (fun x => (fun r => (r.1.1.1, r.2)) <$> x)
      (RealNetworkC1q.roundPhase_full D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) _ _ _ hprog 1 ((st, mem), k))).symm)
    rw [c1Wrapper_round K D W knownE knownB count hist names _ st mem k hk]
    refine SameRun.of_eq ?_
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  · have hp : RealNetworkRC.PartialOut D o := by
      refine ⟨?_, ?_⟩
      · push Not at hfull
        obtain ⟨i, hi, h⟩ := hfull
        exact ⟨i, hi, Option.not_isSome_iff_eq_none.1 h⟩
      · push Not at hnone
        obtain ⟨i, hi, h⟩ := hnone
        exact ⟨i, hi, Option.isSome_iff_ne_none.2 h⟩
    refine (SameRun.of_eq (RealNetworkRC.roundPhase_partial D W noFunctionality
      (fun i (z : HeadOut C E × E × RunState C) => (openTailOf K (localContext i) z.1 z.2.1).run' z.2.2)
      (fun i z => openTailOut K (localContext i) z.1 z.2.1)
      (fun i z inbox => OptionT.mk (pure (openTailRes K (localContext i) z.1 z.2.1 inbox)))
      (fun i z => by rw [openTailOf_run', advance_exchange_bind]) 3 st o hp)).trans ?_
    refine SameRun.trans ?_ (SameRun.of_eq (congrArg (fun x => (fun r => (r.1.1.1, r.2)) <$> x)
      (RealNetworkRC.roundPhase_partial D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K)
      (fun i (z : HeadOut C E × E × RunState C) => (openTailOf K (localContext i) z.1 z.2.1).run' z.2.2)
      (fun i z => openTailOut K (localContext i) z.1 z.2.1)
      (fun i z inbox => OptionT.mk (pure (openTailRes K (localContext i) z.1 z.2.1 inbox)))
      (fun i z => by rw [openTailOf_run', advance_exchange_bind]) 1 ((st, mem), k) o hp)).symm)
    rw [c1Wrapper_round K D W knownE knownB count hist names _ st mem k hk]
    refine SameRun.of_eq ?_
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

end ThresholdLeanXmssSecurity.RealNetworkC1t

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1t

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

section Surv

variable (D : C.Coalition)

/-- The view of the coalition of the digest round with the digest lists `ds`. -/
def digestView (ds : C.Party → List HashOutput) : C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∉ D.1 then digestOutbox i (ds i) c else none

/-- The outputs of the digest round with the digest lists `ds` and the messages `sent` of the coalition. -/
def digestOuts (ds : C.Party → List HashOutput) (sent : C.Party → C.Party → Option (Msg E)) :
    C.Party → Option Unit := fun i => if i ∈ D.1 then none else
  let inbox : Mail C E := fun k => if k ∈ D.1 then sent k i else digestOutbox k (ds k) i
  if anyAbort inbox then none else if DigestsAgree i (ds i) inbox then some () else none

/-- The wrapper names the survivors of the digest round. The statement is over `digestOuts` and
`digestView`, the form of `roundPhase_full`. -/
theorem digestOuts_surv (ds : C.Party → List HashOutput) (sent : C.Party → C.Party → Option (Msg E))
    (hpart : PartialOut D (digestOuts D ds sent) ∨
      PartialOut D (survivors D (digestSurv D (digestView D ds) sent))) :
    ∀ j ∉ D.1, (digestOuts D ds sent j).isSome = (survivors D (digestSurv D (digestView D ds) sent) j).isSome := by
  intro j hj
  by_cases hD : ∃ c, c ∈ D.1
  · have hc := hD.choose_spec
    have hin : (fun k => if k ∈ D.1 then sent k j else digestOutbox k (ds k) j : Mail C E) =
        RealNetworkC1s.digestInbox D (digestView D ds) sent hD.choose j := by
      funext m
      unfold RealNetworkC1s.digestInbox digestView
      by_cases hm : m ∈ D.1
      · simp only [hm, ↓reduceIte]
      · have hne : hD.choose ≠ m := fun h => hm (h ▸ hc)
        by_cases hmj : m = j
        · subst hmj
          simp only [hm, ↓reduceIte, digestOutbox]
        · simp only [hm, ↓reduceIte, hmj, hc, not_false_eq_true, and_self, digestOutbox, hne, Ne.symm hmj]
    have hds : Msg.hashesOf (digestView D ds hD.choose j : Option (Msg E)) = ds j := by
      have hne : j ≠ hD.choose := fun h => hj (h ▸ hc)
      simp only [digestView, hc, hj, not_false_eq_true, and_self, ↓reduceIte, digestOutbox, Ne.symm hne,
        Msg.hashesOf]
    simp only [digestOuts, survivors, digestSurv, hj, ↓reduceIte, hD, dite_true, not_false_eq_true, true_and]
    rw [hin, hds]
    unfold anyAbort
    split_ifs <;> simp_all
  · exfalso
    have hDe : ∀ c, c ∉ D.1 := fun c hc => hD ⟨c, hc⟩
    let Q : Prop := ∀ T : C.Term, ∀ h ∈ C.holders T, ∀ h' ∈ C.holders T,
      (ds h)[C.terms.idxOf T]? = (ds h')[C.terms.idxOf T]? ∧ (ds h)[C.terms.idxOf T]?.isSome
    have hout : ∀ j', digestOuts D ds sent j' = if Q then some () else none := by
      intro j'
      have hin : (fun k => if k ∈ D.1 then sent k j' else digestOutbox k (ds k) j' : Mail C E) =
          fun m => digestOutbox m (ds m) j' := by
        funext m
        simp only [hDe m, ↓reduceIte]
      have hab : anyAbort (fun m => digestOutbox (E := E) m (ds m) j') = false := by
        unfold anyAbort
        rw [List.any_eq_false]
        intro m _
        by_cases hm : j' = m <;> simp only [digestOutbox, hm, ↓reduceIte, Msg.isAbort, Bool.false_eq_true,
          not_false_eq_true]
      have hsel : ∀ h, (if h = j' then ds j' else Msg.hashesOf (digestOutbox (E := E) h (ds h) j')) = ds h := by
        intro h
        by_cases hh : h = j'
        · subst hh
          simp only [↓reduceIte]
        · simp only [hh, ↓reduceIte, digestOutbox, Ne.symm hh, Msg.hashesOf]
      have hag : DigestsAgree (E := E) j' (ds j') (fun m => digestOutbox m (ds m) j') ↔ Q := by
        unfold DigestsAgree
        simp only [hsel]
        exact Iff.rfl
      simp only [digestOuts, hDe j', ↓reduceIte, hin, hab, Bool.false_eq_true, hag]
    have hsv : ∀ j', survivors D (digestSurv D (digestView D ds) sent) j' = some () := by
      intro j'
      simp only [survivors, digestSurv, hD, dite_false, hDe j', not_false_eq_true, and_self, ↓reduceIte]
    rcases hpart with ⟨⟨i, hi, hn⟩, i', hi', hs⟩ | ⟨⟨i, hi, hn⟩, -⟩
    · rw [hout] at hn hs
      by_cases hQ : Q
      · simp only [hQ, ↓reduceIte, reduceCtorEq] at hn
      · simp only [hQ, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at hs
    · rw [hsv] at hn
      exact Option.some_ne_none _ hn

end Surv

section Programs

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

variable (K : Constants C E) (D : C.Coalition) (L : ℕ) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem require_eq_mk {ι : Type} {G : OracleSpec ι} (P : Prop) :
    (require P : PartyM C E G Unit) = OptionT.mk (pure (if P then some () else none)) := by
  unfold require
  split_ifs <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The digest round of operator `i` with its digest list `ds`. -/
def digestBlk {I O : Type} (i : C.Party) (ds : List HashOutput) : PartyM C E (CallSpec I O) Unit :=
  exchange (digestOutbox i ds) >>= fun inbox => require (DigestsAgree (E := E) i ds inbox)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- `compareDigests` is the local digest rows, then the digest round. -/
theorem compareDigests_blk {I O α : Type} (i : C.Party) (salts : Shares C Bit)
    (f : Unit → RunM C E (CallSpec I O) α) (st : RunState C) :
    (compareDigests (localContext i) salts >>= f).run' st =
      localStep (liftComp (digestQuery i salts st.history) (LocalSpec C)) >>= fun ds =>
        digestBlk i ds >>= fun _ => (f ()).run' st := by
  rw [RealNetworkRC.compareDigests_run'_any]
  simp only [digestBlk, bind_assoc]
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem timed_digestBlk {I O : Type} (i : C.Party) (ds : List HashOutput) :
    Timed 1 (digestBlk (C := C) (E := E) (I := I) (O := O) i ds).run :=
  Timed.exchange_bind 0 _ _ fun inbox => by
    rw [require_eq_mk]
    split_ifs
    · exact Timed.done ()
    · exact Timed.abort 0

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The digest round from a full start is one round and then `digestOuts`. -/
theorem digestPhase_full {I O L' R' Ia : Type} (A : Adversary C E Ia L' R') (F : Functionality C I O L' R')
    (st : A.State) (ds : C.Party → List HashOutput) :
    executePhase localRoles D A F 1 st (fun i => digestBlk i (ds i)) =
      A.round st (digestView D ds) >>= fun b => pure (b.1, digestOuts D ds b.2) :=
  RealNetworkC1q.roundPhase_full D A F _ (fun i => digestOutbox i (ds i))
    (fun i inbox => if DigestsAgree (E := E) i (ds i) inbox then some () else none)
    (fun i _ => by
      unfold digestBlk
      simp only [require_eq_mk]) 0 st

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real end of the check from its last challenge starts with the round of the coin, on the drawn row
of its label. -/
theorem realChallenge_exchange {m : ℕ} (T : DrawTables C E m) (i : C.Party) (hs : RunState C) (v : HeadOut C E) :
    ∃ f, (challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
        openTailOf K (localContext i) v r).run' hs =
      exchange (openOut i (conv K (localContext i) (drawnE D knownE T (hs.label - L) i).1) 2) >>= f := by
  simp only [challenge, coinKey, drawnCheckBuildingBlocks, coinWith, openSh, freshLabel, StateT.run'_eq,
    StateT.run_bind, StateT.run_get, StateT.run_modifyGet, StateT.run_lift, bind_assoc, pure_bind, map_bind]
  exact ⟨_, rfl⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The end of the check in the hybrid model from its last challenge starts with the call of `F_coin`. With
no reply it aborts. -/
theorem hybridChallenge_call (i : C.Party) (hs : RunState C) (v : HeadOut C E) :
    ∃ f, f none = failure ∧ (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
        openTailOf K (localContext i) v r).run' hs = call (Sum.inl (Sum.inl 2)) >>= f := by
  simp only [challenge, coinKey, hybridCheckBuildingBlocks, freshLabel, StateT.run'_eq,
    StateT.run_bind, StateT.run_get, StateT.run_modifyGet, StateT.run_lift, bind_assoc, pure_bind, map_bind]
  exact ⟨_, rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- A round of the wrapper at the digest round is a round of `W`, and then `coinTail` of the last coin on
the survivors after a partial abort. -/
theorem c1Wrapper_round_digest {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (count : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (st : W.State) (mem : C1Memory C E) (m : C.Party → C.Party → Option (Msg E)) :
    (c1WrapperWith K D W knownE knownB count hist names tails).round ((st, mem), 2 * halvings count + 4) m =
      W.round st m >>= fun r => if PartialOut D (survivors D (digestSurv D m r.2)) then
        (fun st' => ((((st', mem), 2 * halvings count + 4) :
          (c1WrapperWith K D W knownE knownB count hist names tails).State), r.2)) <$>
          RealNetworkC1s.coinTail K D W (knownE (2 * halvings count + 4)).1 (knownE (2 * halvings count + 4)).2 2
            (liveSet D (survivors D (digestSurv D m r.2))) r.1
      else pure ((((r.1, mem), 2 * halvings count + 4) :
        (c1WrapperWith K D W knownE knownB count hist names tails).State), r.2) := by
  simp only [c1WrapperWith, relabel, withMemory, c1Rtails, ↓reduceIte, bind_map_left]
  refine bind_congr fun r => ?_
  split_ifs <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rfl

end Programs

/-- A map and a continuation. The goals close with `exact` on this form. -/
theorem map_bind_eq {α β δ : Type} (x : OracleComp (LocalSpec C) α) (f : α → β)
    (k : β → OracleComp (LocalSpec C) δ) (r : α → OracleComp (LocalSpec C) δ) (h : ∀ a, k (f a) = r a) :
    (f <$> x) >>= k = x >>= r := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, h]

/-- A round with a tail, the outputs and the next phase under a map, as one computation. The goals close
with `exact` on this form, for the same reason as `bind_map_counter`. -/
theorem map_bind_round {α β γ δ ε ζ : Type} (x : OracleComp (LocalSpec C) (α × β))
    (t : α × β → OracleComp (LocalSpec C) (γ × β)) (O : β → ζ) (k : γ × ζ → OracleComp (LocalSpec C) δ)
    (f : δ → ε) :
    f <$> (((x >>= t) >>= fun bb => pure (bb.1, O bb.2)) >>= k) =
      x >>= fun r => t r >>= fun bb => f <$> k (bb.1, O bb.2) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

theorem digestBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) : DigestBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist hIH T0 st mem b hs hlab
  let restR : DrawTables C E (RealNetworkV3.checkLabels count) → C.Party → PartyM C E RealSpec Unit := fun T i =>
    (challenge K (drawnCheckBuildingBlocks K D L knownE knownB (splice (2 * halvings count + 4) T0 T) i) >>= fun r =>
      openTailOf K (localContext i) (b i).2 r).run' (hs i)
  let restH : C.Party → PartyM C E (CheckSpec C E) Unit := fun i =>
    (challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (b i).2 r).run' (hs i)
  let oa : C.Party → OracleComp (LocalSpec C) (List HashOutput) := fun i =>
    liftComp (digestQuery i (b i).1.1 (hs i).history) (LocalSpec C)
  let seqv : OracleComp (LocalSpec C) (C.Party → List HashOutput) :=
    OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure [] else oa i
  have hv : ∀ v : C.Party → List HashOutput, SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality 6 st (fun i => digestBlk i (v i) >>= fun _ => restR T i))
      ((fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) 4 ((st, mem), 2 * halvings count + 4)
        (fun i => digestBlk i (v i) >>= fun _ => restH i)) := by
    intro v
    have hr : ∀ r : W.State × (C.Party → C.Party → Option (Msg E)), SameRun prims
        (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
          executePhase localRoles D W noFunctionality 5 r.1
            (fun i => (digestOuts D v r.2 i).elim failure fun _ => restR T i))
        ((if PartialOut D (survivors D (digestSurv D (digestView D v) r.2)) then
          (fun st' => ((((st', mem), 2 * halvings count + 4) : (c1WrapperWith K D W knownE knownB count hist names
            (c1Tails K D W knownE knownB count L tg)).State), r.2)) <$>
            RealNetworkC1s.coinTail K D W (knownE (2 * halvings count + 4)).1 (knownE (2 * halvings count + 4)).2 2
              (liveSet D (survivors D (digestSurv D (digestView D v) r.2))) r.1
        else pure ((((r.1, mem), 2 * halvings count + 4) : (c1WrapperWith K D W knownE knownB count hist names
            (c1Tails K D W knownE knownB count L tg)).State), r.2)) >>= fun bb =>
          (fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
            (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
            (checkFunctionalities K) 3 bb.1 (fun i => (digestOuts D v bb.2 i).elim failure fun _ => restH i)) := by
      intro r
      have hagree := digestOuts_surv D v r.2
      by_cases hnone : ∀ i, i ∉ D.1 → digestOuts D v r.2 i = none
      · have hnp : ¬ PartialOut D (survivors D (digestSurv D (digestView D v) r.2)) := fun h => by
          have := h.2
          obtain ⟨j, hj, hs'⟩ := this
          have := hagree (Or.inr h) j hj
          rw [hnone j hj, hs'] at this
          simp only [Option.isSome_none, Bool.false_eq_true] at this
        have e1 : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count),
            executePhase localRoles D W noFunctionality 5 r.1
              (fun i => (digestOuts D v r.2 i).elim failure fun _ => restR T i) = pure (r.1, fun _ => none) :=
          fun T => by
            rw [executePhase_congr_honest D W _ _ _ _ (fun _ => failure)
              (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure]
        simp only [e1]
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), pure_bind]
        refine (sameRun_drawTables_drop prims _).trans (SameRun.of_eq ?_)
        rw [executePhase_congr_honest D _ _ _ _ _ (fun _ => failure)
          (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure, map_pure]
      by_cases hfull : ∀ i, i ∉ D.1 → (digestOuts D v r.2 i).isSome
      · have hnp : ¬ PartialOut D (survivors D (digestSurv D (digestView D v) r.2)) := fun h => by
          have := h.1
          obtain ⟨j, hj, hs'⟩ := this
          have := hagree (Or.inr h) j hj
          rw [hfull j hj, hs'] at this
          simp only [Option.isSome_none, Bool.true_eq_false] at this
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), pure_bind]
        refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq
          (executePhase_congr_honest D W _ _ _ _ (fun i => restR T i) fun i hi => ?_))
          ((hIH T0 r.1 mem (fun i => (b i).2) hs hlab).trans (SameRun.of_eq ?_))
        · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hfull i hi)
          rw [hu]
          rfl
        · congr 1
          refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
          obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hfull i hi)
          change _ = (digestOuts D v r.2 i).elim failure fun _ => restH i
          rw [hu]
          rfl
      have hpO : PartialOut D (digestOuts D v r.2) := by
        refine ⟨?_, ?_⟩
        · push Not at hfull
          obtain ⟨i, hi, h⟩ := hfull
          exact ⟨i, hi, Option.not_isSome_iff_eq_none.1 h⟩
        · push Not at hnone
          obtain ⟨i, hi, h⟩ := hnone
          exact ⟨i, hi, Option.isSome_iff_ne_none.2 h⟩
      have hag := hagree (Or.inl hpO)
      have hpS : PartialOut D (survivors D (digestSurv D (digestView D v) r.2)) := by
        obtain ⟨⟨i, hi, h⟩, i', hi', h'⟩ := hpO
        refine ⟨⟨i, hi, ?_⟩, i', hi', by rw [← hag i' hi']; exact h'⟩
        have := hag i hi
        rw [h, Option.isSome_none] at this
        exact Option.not_isSome_iff_eq_none.1 (by rw [← this]; decide)
      have hlive : liveSet D (survivors D (digestSurv D (digestView D v) r.2)) = liveSet D (digestOuts D v r.2) := by
        unfold liveSet
        exact Finset.filter_congr fun i _ => by
          constructor
          · rintro ⟨hi, h⟩
            exact ⟨hi, by rw [hag i hi]; exact h⟩
          · rintro ⟨hi, h⟩
            exact ⟨hi, by rw [← hag i hi]; exact h⟩
      have hg := fun i => hybridChallenge_call K i (hs i) (b i).2
      choose g hgn hgeq using hg
      have habort : ∀ s : (c1WrapperWith K D W knownE knownB count hist names
          (c1Tails K D W knownE knownB count L tg)).State,
          executePhase localRoles D
            (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
            (checkFunctionalities K) 3 s (fun i => (digestOuts D v r.2 i).elim failure fun _ => restH i) =
          pure (s, fun _ => none) := by
        intro s
        have hprog : (fun i => (digestOuts D v r.2 i).elim failure fun _ => restH i) =
            fun i => optionalCall ((digestOuts D v r.2 i).map fun _ => Sum.inl (Sum.inl 2))
              (fun o => (digestOuts D v r.2 i).elim failure fun _ => g i o) := by
          funext i
          cases digestOuts D v r.2 i with
          | none => rfl
          | some u => exact hgeq i
        rw [hprog]
        refine executePhase_partialCall_abort D _ _ 2 s _ _ (fun i _ => ?_) ?_
        · cases digestOuts D v r.2 i with
          | none => rfl
          | some u => exact hgn i
        · obtain ⟨⟨i, hi, h⟩, -⟩ := hpO
          exact ⟨i, hi, by simp only [h, Option.map_none]⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hpS), hlive]
      refine SameRun.trans ?_ (SameRun.of_eq (map_bind_eq _ (fun st' => ((((st', mem), 2 * halvings count + 4) :
          (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg)).State), r.2))
        _ (fun st' => pure (st', fun _ => none)) fun st' => by
          change (fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
            (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
            (checkFunctionalities K) 3 ((st', mem), 2 * halvings count + 4)
            (fun i => (digestOuts D v r.2 i).elim failure fun _ => restH i) = _
          rw [habort, map_pure])).symm
      have hnm : 2 * halvings count + 4 < RealNetworkV3.checkLabels count := by
        unfold RealNetworkV3.checkLabels
        omega
      let G : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) →
          OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) := fun a c =>
        W.round r.1 (fun c' i => if c' ∈ D.1 ∧ i ∈ liveSet D (digestOuts D v r.2) then
          openOut i (conv K (localContext i)
            (frandShare D 2 (knownE (2 * halvings count + 4)).1 (knownE (2 * halvings count + 4)).2 a c i).1) 2 c'
          else none) >>= fun x => pure (x.1, fun _ => none)
      have hT : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count),
          executePhase localRoles D W noFunctionality 5 r.1
            (fun i => (digestOuts D v r.2 i).elim failure fun _ => restR T i) =
          G (T.freshE ⟨2 * halvings count + 4, hnm⟩) (T.freshPairE ⟨2 * halvings count + 4, hnm⟩) := by
        intro T
        have hex := fun i => realChallenge_exchange K D L knownE knownB
          (splice (2 * halvings count + 4) T0 T) i (hs i) (b i).2
        choose f hf using hex
        rw [RealNetworkRC.roundPhase_partial D W noFunctionality (fun i (_ : Unit) => restR T i)
          (fun i _ => openOut i (conv K (localContext i)
            (drawnE D knownE (splice (2 * halvings count + 4) T0 T) ((hs i).label - L) i).1) 2)
          (fun i _ => f i) (fun i _ => (congrArg (fun p => advance (OptionT.run p)) (hf i)).trans
            (advance_exchange_bind _ _)) 4 r.1 _ hpO]
        simp only [G]
        congr 2
        funext c i
        by_cases h : c ∈ D.1 ∧ i ∈ liveSet D (digestOuts D v r.2)
        · obtain ⟨hi, hs'⟩ := (Finset.mem_filter.1 h.2).2
          obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hs'
          have hl : (hs i).label - L = 2 * halvings count + 4 := by
            rw [(hlab i hi).1]
            omega
          have h' : c ∈ D.1 ∧ i ∈ RealNetworkRC.liveSet D (digestOuts D v r.2) := h
          simp only [h, h', and_self, ↓reduceIte, hu, Option.elim_some, hl, drawnE, hnm, ↓reduceDIte, splice,
            lt_self_iff_false]
        · have h' : ¬ (c ∈ D.1 ∧ i ∈ RealNetworkRC.liveSet D (digestOuts D v r.2)) := h
          simp only [h, h', ↓reduceIte]
      refine (SameRun.bind_right _ fun T => SameRun.of_eq (hT T)).trans
        ((sameRun_drawTables_row prims (2 * halvings count + 4) hnm G).trans (SameRun.of_eq ?_))
      simp only [G, RealNetworkC1s.coinTail, bind_assoc, pure_bind]
    have hR : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count), SameRun prims
        (executePhase localRoles D W noFunctionality 6 st (fun i => digestBlk i (v i) >>= fun _ => restR T i))
        (W.round st (digestView D v) >>= fun r => executePhase localRoles D W noFunctionality 5 r.1
          (fun i => (digestOuts D v r.2 i).elim failure fun _ => restR T i)) := by
      intro T
      refine (executePhase_bind prims D W noFunctionality 1 5 st _ _ fun i _ => timed_digestBlk i (v i)).trans
        (SameRun.of_eq ?_)
      rw [digestPhase_full, bind_assoc]
      simp only [pure_bind]
    refine (SameRun.bind_right _ hR).trans ((sameRun_swap prims _ (W.round st (digestView D v)) _).trans ?_)
    refine (SameRun.bind_right _ hr).trans ?_
    refine SameRun.trans (SameRun.of_eq ?_) ((executePhase_bind prims D
      (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
      (checkFunctionalities K) 1 3 ((st, mem), 2 * halvings count + 4) _ _
      fun i _ => timed_digestBlk i (v i)).map (fun r => (r.1.1.1, r.2))).symm
    rw [digestPhase_full, c1Wrapper_round_digest]
    exact (map_bind_round (W.round st (digestView D v)) (fun r =>
      if PartialOut D (survivors D (digestSurv D (digestView D v) r.2)) then
        (fun st' => ((((st', mem), 2 * halvings count + 4) : (c1WrapperWith K D W knownE knownB count hist names
          (c1Tails K D W knownE knownB count L tg)).State), r.2)) <$>
          RealNetworkC1s.coinTail K D W (knownE (2 * halvings count + 4)).1 (knownE (2 * halvings count + 4)).2 2
            (liveSet D (survivors D (digestSurv D (digestView D v) r.2))) r.1
      else pure ((((r.1, mem), 2 * halvings count + 4) : (c1WrapperWith K D W knownE knownB count hist names
          (c1Tails K D W knownE knownB count L tg)).State), r.2)) (digestOuts D v)
      (fun r => executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) 3 r.1 (fun i => (r.2 i).elim failure fun _ => restH i))
      (fun r => (r.1.1.1, r.2))).symm
  refine SameRun.trans (SameRun.bind_right _ fun T => (SameRun.of_eq ?_).trans
    (executePhase_local_fallback prims D W noFunctionality 6 st oa (fun _ => [])
      (fun i ds => digestBlk i ds >>= fun _ => restR T i))) ?_
  · congr 1
    funext i
    exact compareDigests_blk (E := E) i (b i).1.1 _ (hs i)
  refine (sameRun_swap prims _ seqv _).trans ?_
  refine SameRun.trans ?_ (((executePhase_local_fallback prims D
    (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
    (checkFunctionalities K) 4
    ((st, mem), 2 * halvings count + 4) oa (fun _ => []) (fun i ds => digestBlk i ds >>= fun _ => restH i)).map
      (fun r => (r.1.1.1, r.2))).symm.trans (SameRun.of_eq ?_))
  · rw [map_bind]
    exact SameRun.bind_right seqv hv
  · congr 2
    funext i
    exact (compareDigests_blk (E := E) i (b i).1.1 (fun _ => challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
      openTailOf K (localContext i) (b i).2 r) (hs i)).symm

end ThresholdLeanXmssSecurity.RealNetworkC1t

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1t.extendBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1t.extendBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1t.finalCoinBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1t.finalCoinBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1t.openRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1t.openRound

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1t.digestBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1t.digestBlock
