import ThresholdLeanXmssSecurity.Proof.BatchCheck.ExtendBlock
import ThresholdLeanXmssSecurity.Proof.BatchCheck.Rand

/-!
# The blocks of the masked multiplication and of the coins

`maskBlock` proves `MaskBlockStatement`, the block of the masked multiplication. `coinBlock` proves
`CoinBlockStatement`, the coin of a challenge in the middle of the check, with the generic coin
block `genBlock_of`. `lastCoinBlock` proves `LastCoinBlockStatement`.
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

/-- A run with no fuel of programs that return a value or fail. -/
theorem executePhase_zero_elim {I O L R Ia α β : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (st : A.State) (o : C.Party → Option α) (g : C.Party → α → β) :
    executePhase localRoles D A F 0 st
        (fun i => (o i).elim failure fun q => (pure (g i q) : PartyM C E (CallSpec I O) β)) =
      pure (st, fun i => if i ∈ D.1 then none else (o i).map (g i)) := by
  have hadv : ∀ i, advance ((o i).elim failure fun q => (pure (g i q) : PartyM C E (CallSpec I O) β)).run =
      pure (Step.done ((o i).map (g i))) := fun i => by cases o i <;> rfl
  have hs : startSteps localRoles D (fun i => (o i).elim failure fun q => (pure (g i q) : PartyM C E (CallSpec I O) β)) =
      pure (fun i => if i ∈ D.1 then Step.done none else Step.done ((o i).map (g i))) := by
    unfold startSteps
    simp only [localRoles, hadv]
    rw [← sequenceFin_pure]
    congr 1
    funext i
    split_ifs <;> rfl
  unfold executePhase
  rw [hs, pure_bind]
  simp only [executeRounds]
  congr 2
  funext i
  split_ifs <;> rfl

/-- A phase of programs with a pure end is the phase and a map of its outputs. -/
theorem executePhase_bind_pure {I O L R Ia α β : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) (a : ℕ) (st : A.State)
    (p : C.Party → PartyM C E (CallSpec I O) α) (g : C.Party → α → β) (hp : ∀ i ∉ D.1, Timed a (p i).run) :
    SameRun prims (executePhase localRoles D A F a st (fun i => p i >>= fun q => pure (g i q)))
      ((fun r => (r.1, fun i => if i ∈ D.1 then none else (r.2 i).map (g i))) <$>
        executePhase localRoles D A F a st p) := by
  refine (executePhase_bind prims D A F a 0 st p (fun i q => pure (g i q)) hp).trans (SameRun.of_eq ?_)
  simp only [executePhase_zero_elim, map_eq_bind_pure_comp, Function.comp_def]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

section Programs

variable (K : Constants C E) (D : C.Coalition) (L : ℕ) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))

/-- The two products of the masked multiplication of operator `i` with the mask `w`. -/
def maskProducts (i : C.Party) (A B : ℕ → E) (w : PrssOutput C E) : List (Product C E) :=
  [.shamir (fun _ => conv K (localContext i) w.1 0) (fun _ => conv K (localContext i) w.1 1) 1,
    .shamir (fun _ => conv K (localContext i) w.1 0 + A 0) (fun _ => conv K (localContext i) w.1 1 + B 0) 1]

/-- The output of the masked multiplication of operator `i` with the mask `w`, the state `hs` after the
draw of the mask, and the output `z` of `extendMult`. -/
def maskOut (i : C.Party) (A B : ℕ → E) (V : E) (w : PrssOutput C E) (hs : RunState C) (z : Shares C E) :
    HeadOut C E × RunState C :=
  ((A 0, B 0, V, w.1, z), extendState K i hs z)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real masked multiplication reads the mask from row `n` and runs `extendMult` on row `n + 1`. -/
theorem realMask_eq {m : ℕ} (T : DrawTables C E m) (i : C.Party) (hs : RunState C) (n : ℕ) (hn : n + 1 < m)
    (hl : hs.label = L + n) (A B : ℕ → E) (V : E) :
    (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (.mask A B V)).run hs =
      realExtendProg K (frandShare D 2 (knownE (n + 1)).1 (knownE (n + 1)).2 (T.freshE ⟨n + 1, hn⟩)
          (T.freshPairE ⟨n + 1, hn⟩)) i
        (maskProducts K i A B (drawnE D knownE T n i), ⟨hs.history, hs.label + 1, hs.tag⟩) >>= fun q =>
        pure (maskOut K i A B V (drawnE D knownE T n i) ⟨hs.history, hs.label + 1, hs.tag⟩ q.1) := by
  have hext : ((drawnCheckBuildingBlocks K D L knownE knownB T i).extendMult
      (maskProducts K i A B (drawnE D knownE T n i))).run ⟨hs.history, L + n + 1, hs.tag⟩ =
      realExtendProg K (frandShare D 2 (knownE (n + 1)).1 (knownE (n + 1)).2 (T.freshE ⟨n + 1, hn⟩)
        (T.freshPairE ⟨n + 1, hn⟩)) i (maskProducts K i A B (drawnE D knownE T n i), ⟨hs.history, L + n + 1, hs.tag⟩) := by
    unfold realExtendProg
    conv_lhs => unfold drawnCheckBuildingBlocks
    simp only [freshLabel, StateT.run_bind, StateT.run_modifyGet, pure_bind, show L + n + 1 - L = n + 1 by omega]
    simp only [drawnE, hn, ↓reduceDIte]
    rfl
  simp only [runPlan, maskHeadOf, StateT.run_bind, drawn_randElements_run, pure_bind, hl, Nat.add_sub_cancel_left]
  rw [show [Product.shamir (fun _ => conv K (localContext i) (drawnE D knownE T n i).1 0)
      (fun _ => conv K (localContext i) (drawnE D knownE T n i).1 1) 1,
    Product.shamir (fun _ => conv K (localContext i) (drawnE D knownE T n i).1 0 + A 0)
      (fun _ => conv K (localContext i) (drawnE D knownE T n i).1 1 + B 0) 1] =
      maskProducts K i A B (drawnE D knownE T n i) from rfl, hext, RealNetworkC1q.realExtendProg_eq]
  simp only [bind_assoc, pure_bind]
  rfl

/-- The masked multiplication in the hybrid model after the reply `o` to `F_rand`. -/
def hybridMaskAfter (i : C.Party) (A B : ℕ → E) (V : E) (hs : RunState C)
    (o : Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit))) :
    PartyM C E (CheckSpec C E) (HeadOut C E × RunState C) :=
  match o with
  | some (.inr (.inl w)) =>
    RealNetworkGP.callProg (Sum.inl (Sum.inr (maskProducts K i A B w))) (fun o => (extendOutput o).map
        fun z => (z, extendState K i ⟨hs.history, hs.label + 1, hs.tag⟩ z)) >>= fun q =>
      pure (maskOut K i A B V w ⟨hs.history, hs.label + 1, hs.tag⟩ q.1)
  | _ => failure

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The masked multiplication in the hybrid model is the call of `F_rand`, the call of `F_extendMult` and
a pure output. -/
theorem hybridMask_eq (i : C.Party) (hs : RunState C) (A B : ℕ → E) (V : E) :
    (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (.mask A B V)).run hs =
      (call (Sum.inr (Sum.inl 2)) : PartyM C E (CheckSpec C E) _) >>= hybridMaskAfter K i A B V hs := by
  have hext : ∀ w : PrssOutput C E, ((hybridCheckBuildingBlocks K i).extendMult (maskProducts K i A B w)).run
      ⟨hs.history, hs.label + 1, hs.tag⟩ =
      RealNetworkGP.callProg (Sum.inl (Sum.inr (maskProducts K i A B w))) (fun o => (extendOutput o).map
        fun z => (z, extendState K i ⟨hs.history, hs.label + 1, hs.tag⟩ z)) := by
    intro w
    simp only [hybridCheckBuildingBlocks, freshLabel, StateT.run_bind, StateT.run_modifyGet, pure_bind,
      RealNetworkGP.callProg, StateT.run_lift, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with _ | ((_ | z) | _) <;> rfl
  simp only [runPlan, maskHeadOf, StateT.run_bind, hybrid_randElements_run, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with _ | ((_ | _) | (w | _)) <;> try rfl
  dsimp only [hybridMaskAfter]
  rw [pure_bind]
  rw [show [Product.shamir (fun _ => conv K (localContext i) w.1 0) (fun _ => conv K (localContext i) w.1 1) 1,
    Product.shamir (fun _ => conv K (localContext i) w.1 0 + A 0) (fun _ => conv K (localContext i) w.1 1 + B 0) 1] =
      maskProducts K i A B w from rfl, hext w]
  simp only [RealNetworkGP.callProg, bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with _ | ((_ | z) | _) <;> rfl

end Programs

section After

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
  (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- The real run after the head with the outputs `o`. It draws the table rows from `2 R + 3` on. -/
def realMaskRest (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State)
    (o : C.Party → Option (HeadOut C E × RunState C)) : OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
    realRest K D W knownE knownB count L (splice (2 * halvings count + 3) T0 T) (st, o)

omit [Fintype E] in
/-- The claim after the head, for each output. -/
theorem afterMask (hFull : RestFull prims K D W knownE knownB names count L tg hist)
    (hPart : RestPartial prims K D W knownE knownB count L)
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E)
    (o : C.Party → Option (HeadOut C E × RunState C))
    (hlab : ∀ i, i ∉ D.1 → ∀ z, o i = some z → z.2.label = L + (2 * halvings count + 3) ∧ z.2.tag = tg) :
    SameRun prims (realMaskRest K D W knownE knownB count L T0 st o)
      (midRest K D W knownE knownB names count L tg hist
        ((((st, mem), 2 * halvings count + 3) : (c1WrapperWith K D W knownE knownB count hist names
          (c1HeadTails K D W knownE knownB count L tg)).State), o)) := by
  by_cases hnone : ∀ i, i ∉ D.1 → o i = none
  · have hnp : ¬ PartialOut D o := fun h => by
      obtain ⟨-, i, hi, h⟩ := h
      simp only [hnone i hi, Option.isSome_none, Bool.false_eq_true] at h
    unfold realMaskRest midRest
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), executePhase_congr_honest D _ _ _ _ _ (fun _ => failure)
      (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure, map_pure]
    refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) (sameRun_drawTables_drop prims _)
    unfold realRest
    rw [executePhase_congr_honest D W _ _ st _ (fun _ => failure) (fun i hi => by simp only [hnone i hi,
      Option.elim_none]), executePhase_failure]
  by_cases hfull : ∀ i, i ∉ D.1 → (o i).isSome
  · have hnp : ¬ PartialOut D o := fun h => by
      obtain ⟨⟨i, hi, h⟩, -⟩ := h
      have := hfull i hi
      simp only [h, Option.isSome_none, Bool.false_eq_true] at this
    let zf : C.Party → HeadOut C E × RunState C := fun i =>
      (o i).getD ((0, 0, 0, fun _ _ => 0, fun _ _ => 0), ⟨fun _ => [], L + (2 * halvings count + 3), tg⟩)
    have hz : ∀ i, i ∉ D.1 → o i = some (zf i) := fun i hi => by
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      simp only [zf, hq, Option.getD_some]
    have h := hFull T0 st mem (fun i => (zf i).1) (fun i => (zf i).2) (fun i hi => hlab i hi _ (hz i hi))
    unfold realMaskRest midRest
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp)]
    refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) (h.trans (SameRun.of_eq ?_))
    · unfold realRest
      refine executePhase_congr_honest D W _ _ st _ _ fun i hi => ?_
      change (o i).elim failure _ = _
      rw [hz i hi, Option.elim_some]
      rfl
    · congr 1
      refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
      change _ = (o i).elim failure (restAt K i)
      rw [hz i hi, Option.elim_some]
      rfl
  have hp : PartialOut D o := by
    refine ⟨?_, ?_⟩
    · push Not at hfull
      obtain ⟨i, hi, h⟩ := hfull
      exact ⟨i, hi, Option.not_isSome_iff_eq_none.1 h⟩
    · push Not at hnone
      obtain ⟨i, hi, h⟩ := hnone
      exact ⟨i, hi, Option.isSome_iff_ne_none.2 h⟩
  unfold realMaskRest midRest
  rw [ite_eq_left_of_eq_true _ _ (eq_true hp)]
  exact hPart T0 st o hp

end After

theorem maskBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) : MaskBlockStatement prims K D := by
  intro Ia W knownE knownB names hN count L tg hist hFull hPart T0 st mem p hs hRel hlab
  have hNm : 2 * halvings count + 1 + 1 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
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
  let out : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → C.Party → Option (Shares C E × RunState C) →
      Option (HeadOut C E × RunState C) := fun a b i o =>
    if i ∈ D.1 then none else o.map fun q => maskOut K i (A i) (B i) (V i) (w a b i) (hs' i) q.1
  have hout : ∀ a b (o : C.Party → Option (Shares C E × RunState C)), ∀ i, i ∉ D.1 → ∀ z, out a b i (o i) = some z →
      z.2.label = L + (2 * halvings count + 3) ∧ z.2.tag = tg := by
    intro a b o i hi z hz
    simp only [out, hi, ite_false, Option.map_eq_some_iff] at hz
    obtain ⟨q, -, rfl⟩ := hz
    simp only [maskOut, extendState, hs', (hlab i hi).1, (hlab i hi).2]
    exact ⟨by omega, trivial⟩
  let ext : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) →
      OracleComp (LocalSpec C) (W.State × (C.Party → Option (Shares C E × RunState C))) := fun a b a' b' =>
    executePhase localRoles D W noFunctionality (0 + 1) st fun i =>
      realExtendProg K (frandShare D 2 (knownE (2 * halvings count + 1 + 1)).1
        (knownE (2 * halvings count + 1 + 1)).2 a' b') i (prods a b i, hs' i)
  have hreal : SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * 0 + 1) st
            (fun i => (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB
              (splice (2 * halvings count + 1) T0 T) i) (p i)).run (hs i)) >>=
          realRest K D W knownE knownB count L (splice (2 * halvings count + 1) T0 T))
      (liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a =>
        liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b =>
          liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a' =>
            liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b' =>
              ext a b a' b' >>= fun r => realMaskRest K D W knownE knownB count L
                (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') r.1
                (fun i => out a b i (r.2 i))) := by
    refine (resample prims (2 * halvings count + 1) _).trans ?_
    refine SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => ?_
    simp only [splice_setRow]
    refine (resample prims (2 * halvings count + 1 + 1) _).trans ?_
    refine SameRun.bind_right _ fun a' => SameRun.bind_right _ fun b' => ?_
    simp only [splice_setRow]
    have hT : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count), SameRun prims
        (executePhase localRoles D W noFunctionality (2 * 0 + 1) st
            (fun i => (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB
              (splice (2 * halvings count + 1 + 1 + 1)
                (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') T) i)
              (p i)).run (hs i)) >>=
          realRest K D W knownE knownB count L (splice (2 * halvings count + 1 + 1 + 1)
            (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') T))
        (ext a b a' b' >>= fun r => realRest K D W knownE knownB count L (splice (2 * halvings count + 1 + 1 + 1)
            (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') T)
          (r.1, fun i => out a b i (r.2 i))) := by
      intro T
      have hE : (splice (2 * halvings count + 1 + 1 + 1) (setRow (setRow T0 (2 * halvings count + 1) a b)
          (2 * halvings count + 1 + 1) a' b') T).freshE ⟨2 * halvings count + 1 + 1, hNm⟩ = a' := by
        simp only [splice, setRow]
        simp
      have hP : (splice (2 * halvings count + 1 + 1 + 1) (setRow (setRow T0 (2 * halvings count + 1) a b)
          (2 * halvings count + 1 + 1) a' b') T).freshPairE ⟨2 * halvings count + 1 + 1, hNm⟩ = b' := by
        simp only [splice, setRow]
        simp
      have hw : ∀ i, drawnE D knownE (splice (2 * halvings count + 1 + 1 + 1) (setRow (setRow T0
          (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') T) (2 * halvings count + 1) i = w a b i := by
        intro i
        have h1 : 2 * halvings count + 1 < RealNetworkV3.checkLabels count := by omega
        simp only [drawnE, h1, ↓reduceDIte, w, splice, setRow]
        simp
      have eT : executePhase localRoles D W noFunctionality (2 * 0 + 1) st
          (fun i => (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB
            (splice (2 * halvings count + 1 + 1 + 1)
              (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') T) i)
            (p i)).run (hs i)) =
        executePhase localRoles D W noFunctionality 1 st (fun i =>
          realExtendProg K (frandShare D 2 (knownE (2 * halvings count + 1 + 1)).1
            (knownE (2 * halvings count + 1 + 1)).2 a' b') i (prods a b i, hs' i) >>= fun q =>
            pure (maskOut K i (A i) (B i) (V i) (w a b i) (hs' i) q.1)) := by
        refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
        rw [hp i hi, realMask_eq K D L knownE knownB _ i (hs i) (2 * halvings count + 1) hNm (hlab i hi).1, hE, hP,
          hw]
      rw [eT]
      refine ((executePhase_bind_pure prims D W noFunctionality 1 st _ _ fun i _ =>
        timed_realExtendProg K _ i _).bind fun _ => SameRun.refl prims _).trans (SameRun.of_eq ?_)
      rw [bind_map_left]
    refine (SameRun.bind_right _ hT).trans ?_
    exact sameRun_swap prims (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count)) (ext a b a' b')
      fun T r => realRest K D W knownE knownB count L (splice (2 * halvings count + 1 + 1 + 1)
        (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') T)
        (r.1, fun i => out a b i (r.2 i))
  have hhyb : SameRun prims
      (executePhase localRoles D
          (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
          (checkFunctionalities K) (2 * 0 + 2) ((st, mem), 2 * halvings count + 1)
          (fun i => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (p i)).run (hs i)) >>=
        midRest K D W knownE knownB names count L tg hist)
      (liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a =>
        liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b =>
          RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
              (checkFunctionalities K) (0 + 1) ((st, mem), 2 * halvings count + 1 + 1)
              (fun i => Sum.inl (Sum.inr (prods a b i)))
              (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs' i) z)) >>= fun r =>
            midRest K D W knownE knownB names count L tg hist
              ((((r.1.1.1, r.1.1.2), 2 * halvings count + 3) : (c1WrapperWith K D W knownE knownB count hist names
                (c1HeadTails K D W knownE knownB count L tg)).State), fun i => out a b i (r.2 i))) := by
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
      frandElements_answer K D W knownE knownB count hist names hN _ _ _, pure_bind]
    simp only [bind_assoc, pure_bind]
    refine SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => ?_
    rw [executePhase_congr_honest D _ _ 1 _ _ (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inr (prods a b i)))
      (fun o => (extendOutput o).map fun z => (z, extendState K i (hs' i) z)) >>= fun q =>
        pure (maskOut K i (A i) (B i) (V i) (w a b i) (hs' i) q.1)) fun i hi => ?_]
    swap
    · simp only [randFinish, hi, ite_false, Option.map_some]
      rfl
    refine ((executePhase_bind_pure prims D _ _ 1 _ _ _ fun i _ => timed_callProg _ _).bind
      fun _ => SameRun.refl prims _).trans ?_
    have htail := extendPhase_tail prims K D W knownE knownB count hist names hN
      (c1HeadTails K D W knownE knownB count L tg) (prods a b) hs' 0 (st, mem) (2 * halvings count + 1 + 1)
    refine ((htail.map _).bind fun _ => SameRun.refl prims _).trans (SameRun.of_eq ?_)
    rw [callPhase_counter K D W knownE knownB count hist names (checkFunctionalities K)
      (fun i => Sum.inl (Sum.inr (prods a b i))) (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs' i) z))
      (pure () : OracleComp (LocalSpec C) Unit)
      (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D (prods a b)))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D (prods a b))).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D (prods a b) r fresh) (fun A st => extendRun_form K D A st (prods a b))]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun r => ?_
    split_ifs
    · simp only [c1HeadTails, show 2 * halvings count + 1 + 1 = 2 * halvings count + 2 by omega, ↓reduceIte]
      erw [map_pure, pure_bind]
      rfl
    · erw [pure_bind]
      rfl
  have hmem : ∀ a b (st' : W.State) (mem' : C1Memory C E) (o : C.Party → Option (Shares C E × RunState C)),
      SameRun prims
        (midRest K D W knownE knownB names count L tg hist
          ((((st', mem), 2 * halvings count + 3) : (c1WrapperWith K D W knownE knownB count hist names
            (c1HeadTails K D W knownE knownB count L tg)).State), fun i => out a b i (o i)))
        (midRest K D W knownE knownB names count L tg hist
          ((((st', mem'), 2 * halvings count + 3) : (c1WrapperWith K D W knownE knownB count hist names
            (c1HeadTails K D W knownE knownB count L tg)).State), fun i => out a b i (o i))) :=
    fun a b st' mem' o =>
      (afterMask prims K D W knownE knownB names count L tg hist hFull hPart T0 st' mem _ (hout a b o)).symm.trans
        (afterMask prims K D W knownE knownB names count L tg hist hFull hPart T0 st' mem' _ (hout a b o))
  refine hreal.trans (SameRun.trans ?_ hhyb.symm)
  refine SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => ?_
  have hhop := RealNetworkC1q.extendHop prims K D W knownE knownB count hist names hN (2 * halvings count + 1 + 1)
    0 0 (st, mem) (prods a b) hs' fun i hi => rfl
  have hstep : ∀ a' b', SameRun prims
      (ext a b a' b' >>= fun r => realMaskRest K D W knownE knownB count L
        (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') r.1
        (fun i => out a b i (r.2 i)))
      (ext a b a' b' >>= fun r => midRest K D W knownE knownB names count L tg hist
        ((((r.1, mem), 2 * halvings count + 3) : (c1WrapperWith K D W knownE knownB count hist names
          (c1HeadTails K D W knownE knownB count L tg)).State), fun i => out a b i (r.2 i))) :=
    fun a' b' => SameRun.bind_right _ fun r =>
      afterMask prims K D W knownE knownB names count L tg hist hFull hPart
        (setRow (setRow T0 (2 * halvings count + 1) a b) (2 * halvings count + 1 + 1) a' b') r.1 mem
        (fun i => out a b i (r.2 i)) (hout a b r.2)
  refine (SameRun.bind_right _ fun a' => SameRun.bind_right _ fun b' => hstep a' b').trans ?_
  let g : W.State × (C.Party → Option (Shares C E × RunState C)) →
      OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) := fun r =>
    midRest K D W knownE knownB names count L tg hist
      ((((r.1, mem), 2 * halvings count + 3) : (c1WrapperWith K D W knownE knownB count hist names
        (c1HeadTails K D W knownE knownB count L tg)).State), fun i => out a b i (r.2 i))
  have hbind := hhop.bind (f := g) (g := g) fun _ => SameRun.refl prims _
  refine SameRun.trans (SameRun.of_eq ?_) (hbind.trans ?_)
  · simp only [ext, g, bind_assoc]
  · rw [bind_map_left]
    exact SameRun.bind_right _ fun r => hmem a b r.1.1.1 r.1.1.2 r.2

end ThresholdLeanXmssSecurity.RealNetworkC1w

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkC1y
open RealNetworkV3 RealNetworkC1s RealNetworkC1r
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The continuation after the coin, including its challenge search. -/
def coinNext {ι : Type} {G : OracleSpec ι} (K : Constants C E) (bb : CheckBuildingBlocks C E G)
    (i : C.Party) (hs : RunState C) (next : E → Plan C E) (vals : List E) :
    PartyM C E G (HeadOut C E × RunState C) :=
  oracleStep (challengeQuery K hs.tag hs.label vals) >>= fun o =>
    o.elim failure fun r =>
      (runPlan K (localContext i) bb (next r)).run ⟨hs.history, hs.label + 1, hs.tag⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem realCoin_split (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    {m : ℕ} (T : DrawTables C E m) (i : C.Party) (hs : RunState C) (next : E → Plan C E) :
    (challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
      runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (next r)).run hs =
    openSh K (localContext i) (conv K (localContext i) (drawnE D knownE T (hs.label - L) i).1) 2 >>= fun w =>
      coinNext K (drawnCheckBuildingBlocks K D L knownE knownB T i) i hs next (vector 2 w) := by
  simp only [challenge, coinKey, bind_assoc, drawnCheckBuildingBlocks, freshLabel, coinWith,
    coinNext, challengeQuery, oracleStep_bind, StateT.run_bind, StateT.run_lift,
    StateT.run_modifyGet, StateT.run_get, pure_bind]
  refine bind_congr fun w => bind_congr fun key => bind_congr fun r => ?_
  cases r <;> rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem hybridCoin_split (K : Constants C E) (i : C.Party) (hs : RunState C) (next : E → Plan C E) :
    (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
      runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next r)).run hs =
    RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>=
      coinNext K (hybridCheckBuildingBlocks K i) i hs next := by
  simp only [challenge, coinKey, bind_assoc, hybridCheckBuildingBlocks, freshLabel,
    StateT.run_bind, StateT.run_lift,
    StateT.run_modifyGet, StateT.run_get, pure_bind, RealNetworkGP.callProg]
  refine bind_congr fun o => ?_
  rcases o with _ | ((vs | z) | w) <;>
    simp only [Option.bind_none, Option.bind_some, coinOutput, RealNetworkGP.ofOption,
      pure_bind, failure_bind, StateT.run_lift, StateT.run_pure]
  simp only [coinNext, challengeQuery, oracleStep_bind, bind_assoc]
  refine bind_congr fun key => bind_congr fun r => ?_
  cases r <;> rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem coinNext_eq {ι : Type} {G : OracleSpec ι} (K : Constants C E)
    (bb : CheckBuildingBlocks C E G) (i : C.Party) (hs : RunState C) (next : E → Plan C E)
    (vals : List E) (L tg : ℕ) (hl : hs.label = L) (ht : hs.tag = tg) :
    coinNext K bb i hs next vals =
      oracleStep (challengeQuery K tg L vals) >>= fun o => o.elim failure fun r =>
        (runPlan K (localContext i) bb (next r)).run ⟨hs.history, hs.label + 1, hs.tag⟩ := by
  subst L tg
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem optionElim_congr {α β : Type} (o : Option α) (b : β) (f g : α → β)
    (h : ∀ a, o = some a → f a = g a) : o.elim b f = o.elim b g := by
  cases o with
  | none => rfl
  | some a => exact h a rfl

end ThresholdLeanXmssSecurity.RealNetworkC1y

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

/-- Runs that agree on each result of a simulated run of a common prefix are the same run. -/
theorem sameRun_bind_sim (prims : Primitives) {α β : Type} (oa : OracleComp (LocalSpec C) α)
    {f g : α → OracleComp (LocalSpec C) β}
    (h : ∀ (cache : HashCache C) (z : α × HashCache C), z ∈ support ((simulateQ (localAnswer prims) oa).run cache) →
      SameRun prims (f z.1) (g z.1)) :
    SameRun prims (oa >>= f) (oa >>= g) := by
  intro s
  simp only [simulateQ_bind, StateT.run_bind]
  exact OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => h s z hz z.2

/-- A prefix `X` with the image `Y`. When the continuations agree on each result of `X` whose image meets
`P`, and each result of `Y` meets `P`, the runs are the same. -/
theorem sameRun_bind_join (prims : Primitives) {α β γ : Type} (X : OracleComp (LocalSpec C) α) (f : α → β)
    (Y : OracleComp (LocalSpec C) β) (hXY : SameRun prims (f <$> X) Y) (P : β → Prop)
    (hY : ∀ (cache : HashCache C) (z : β × HashCache C),
      z ∈ support ((simulateQ (localAnswer prims) Y).run cache) → P z.1)
    (Kx : α → OracleComp (LocalSpec C) γ) (H : β → OracleComp (LocalSpec C) γ)
    (hK : ∀ x, P (f x) → SameRun prims (Kx x) (H (f x))) :
    SameRun prims (X >>= Kx) (Y >>= H) := by
  refine (sameRun_bind_sim prims X (g := fun x => H (f x)) fun cache z hz => hK z.1 (hY cache (f z.1, z.2) ?_)).trans ?_
  · rw [← support_eq_of_evalDistEq (hXY cache)]
    simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image]
    exact ⟨z, hz, rfl⟩
  · exact (SameRun.of_eq (bind_map_left f X H).symm).trans (hXY.bind fun _ => SameRun.refl prims _)

/-- The values of an honest output of `o`. -/
def valsOf (D : C.Coalition) (o : C.Party → Option (List E)) : List E :=
  Classical.epsilon fun v => ∃ i ∉ D.1, o i = some v

/-- When the honest outputs agree with `vals`, they agree with `valsOf`. -/
theorem valsOf_spec (D : C.Coalition) (o : C.Party → Option (List E)) (vals : List E)
    (h : ∀ i, i ∉ D.1 → ∀ v, o i = some v → v = vals) :
    ∀ i, i ∉ D.1 → o i = none ∨ o i = some (valsOf D o) := by
  intro i hi
  cases hx : o i with
  | none => exact Or.inl rfl
  | some v =>
    obtain ⟨i', hi', he⟩ := Classical.epsilon_spec (p := fun v => ∃ i ∉ D.1, o i = some v) ⟨v, i, hi, hx⟩
    refine Or.inr ?_
    rw [h i hi v hx, ← h i' hi' _ he]
    rfl

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- `coinPhase_tail` for each `tails`. -/
theorem coinPhase_tailWith (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (hn : NamesReceivers D names)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (fuel : ℕ) (st : W.State × C1Memory C E) (k : ℕ) :
    SameRun prims
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names tails)
        (checkFunctionalities K) (fuel + 1) (st, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput))
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (fuel + 1) (st, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput) >>=
        fun r => if PartialOut D r.2 then
          (fun s' => ((s', r.1.2), r.2)) <$> tails k (liveSet D r.2) r.1.1
        else pure r) := by
  have h := RealNetworkGP.callPhase_tail D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2))
    (fun _ => coinOutput) (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
    (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
    (fun v r _ => coinOutputs D v r) prims
    (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) names tails
    (fun A st => coinRun_form K D A st) (fun v r _ j hj => coin_hnames D names hn v r j hj) fuel st k
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st),
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st)] at h
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st),
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st)]
  exact h

/-- The program of operator `i` after a coin with the values `vals`, from the run state `hs` before the
coin. It runs the computation `srch vals` of `H`, reads its result with `dec`, and runs the plan `next r`.
For a challenge `srch` is `challengeQuery` and `dec` is `id`. For the first coin `srch` gives the coins
`τ`, and `dec` is the test of the slice coins. -/
def genNext {ι : Type} {G : OracleSpec ι} {γ ρ : Type} (K : Constants C E)
    (srch : List E → OracleComp (RoSpec C) γ) (dec : γ → Option ρ) (bb : CheckBuildingBlocks C E G)
    (i : C.Party) (hs : RunState C) (next : ρ → Plan C E) (vals : List E) :
    PartyM C E G (HeadOut C E × RunState C) :=
  oracleStep (srch vals) >>= fun c => (dec c).elim failure fun r =>
    (runPlan K (localContext i) bb (next r)).run ⟨hs.history, hs.label + 1, hs.tag⟩

/-- The real run after the coin at position `n` with the outputs `o`. It draws the table rows from `n + 1`
on. -/
def realRestGen (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (count L : ℕ) {γ ρ : Type} (srch : List E → OracleComp (RoSpec C) γ) (dec : γ → Option ρ) (n d : ℕ)
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State)
    (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → ρ → Plan C E) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
    executePhase localRoles D W noFunctionality (2 * d + 1) st (fun i => (o i).elim failure fun vals =>
        genNext K srch dec (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i) i (hs i) (next i)
          vals) >>=
      realRest K D W knownE knownB count L (splice (n + 1) T0 T)

/-- The run in the hybrid model after the call of `F_coin` at position `n` with no tail, with the outputs
`o`. The tail of the reply runs after a partial output. -/
def hybridRestGen (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ) (hist : C.Party → C.Term → List Bit)
    {γ ρ : Type} (srch : List E → OracleComp (RoSpec C) γ) (dec : γ → Option ρ) (n d : ℕ) (st : W.State)
    (mem : C1Memory C E) (o : C.Party → Option (List E)) (hs : C.Party → RunState C)
    (next : C.Party → ρ → Plan C E) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  (if PartialOut D o then
      (fun s' => (((s', n + 1) : (c1WrapperWith K D W knownE knownB count hist names
        (c1HeadTails K D W knownE knownB count L tg)).State), o)) <$>
        c1HeadTails K D W knownE knownB count L tg n (liveSet D o) (st, mem)
    else pure ((((st, mem), n + 1) : (c1WrapperWith K D W knownE knownB count hist names
        (c1HeadTails K D W knownE knownB count L tg)).State), o)) >>= fun r =>
    executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (2 * d + 2) r.1
        (fun i => (r.2 i).elim failure fun vals =>
          genNext K srch dec (hybridCheckBuildingBlocks K i) i (hs i) (next i) vals) >>=
      midRest K D W knownE knownB names count L tg hist

omit [Fintype E] in
/-- A full output of a coin at position `n` with the values `vals` continues with the next plan suffix. -/
theorem genFull (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) {γ ρ : Type} (srch : List E → OracleComp (RoSpec C) γ)
    (dec : γ → Option ρ) (n d : ℕ)
    (hIH : HeadSuffix prims K D W knownE knownB names count L tg hist (n + 1) (2 * d + 1) (2 * d + 2)
      (fun p : C.Party → Plan C E => ∀ i, i ∉ D.1 → PlanOK (p i) d)
      (fun T i p => runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) p)
      (fun i p => runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p))
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E)
    (hs : C.Party → RunState C) (next : C.Party → ρ → Plan C E) (vals : List E)
    (hnext : ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d)
    (hlab : ∀ i, i ∉ D.1 → (hs i).label = L + n ∧ (hs i).tag = tg) :
    SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * d + 1) st (fun i =>
          genNext K srch dec (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i) i (hs i) (next i)
            vals) >>=
        realRest K D W knownE knownB count L (splice (n + 1) T0 T))
      (executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (2 * d + 2) ((st, mem), n + 1)
        (fun i => genNext K srch dec (hybridCheckBuildingBlocks K i) i (hs i) (next i) vals) >>=
        midRest K D W knownE knownB names count L tg hist) := by
  let V := c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg)
  have hv : ∃ i ∉ D.1, (some (hs i)).isSome := by
    obtain ⟨i, hi⟩ := exists_honest D
    exact ⟨i, hi, rfl⟩
  have hr (T : DrawTables C E (RealNetworkV3.checkLabels count)) := RealNetworkC1q.hoist prims D W noFunctionality
    (2 * d + 1) st (srch vals) (fun i => some (hs i)) (fun i c hs' => (dec c).elim failure fun r =>
      (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i)
        (next i r)).run ⟨hs'.history, hs'.label + 1, hs'.tag⟩) hv
  have hh := RealNetworkC1q.hoist prims D V (checkFunctionalities K) (2 * d + 2) ((st, mem), n + 1) (srch vals)
    (fun i => some (hs i)) (fun i c hs' => (dec c).elim failure fun r =>
      (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next i r)).run ⟨hs'.history, hs'.label + 1, hs'.tag⟩)
    hv
  simp only [Option.elim_some] at hr hh
  unfold genNext
  refine (SameRun.bind_right _ fun T => (hr T).bind fun _ => SameRun.refl prims _).trans ?_
  simp only [bind_assoc]
  refine (sameRun_swap prims (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count))
    (liftComp (srch vals) (LocalSpec C)) _).trans ?_
  refine SameRun.trans ?_ ((hh.bind fun _ => SameRun.refl prims _).symm)
  simp only [bind_assoc]
  refine SameRun.bind_right _ fun c => ?_
  cases hc : dec c with
  | none =>
    dsimp only [V]
    simp only [Option.elim_none, executePhase_failure, pure_bind, RealNetworkC1t.realRest_none]
    rw [RealNetworkC1t.midRest_none K D W knownE knownB names count L tg hist ((st, mem), n + 1)]
    exact RealNetworkC1t.sameRun_drawTables_drop (C := C) (E := E) prims _
  | some r =>
    simp only [Option.elim_some]
    have h := hIH T0 st mem (fun i => next i r)
      (fun i => (⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ : RunState C))
      (fun i hi => hnext i hi r) (fun i hi => ⟨by dsimp; rw [(hlab i hi).1]; omega, (hlab i hi).2⟩)
    convert h using 1

omit [Fintype E] in
/-- The claim after the coin at position `n`, for each output that agrees with the memory. The partial
case is the premise `hpart`. -/
theorem genAfter (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) {γ ρ : Type} (srch : List E → OracleComp (RoSpec C) γ)
    (dec : γ → Option ρ) (n d : ℕ)
    (hIH : HeadSuffix prims K D W knownE knownB names count L tg hist (n + 1) (2 * d + 1) (2 * d + 2)
      (fun p : C.Party → Plan C E => ∀ i, i ∉ D.1 → PlanOK (p i) d)
      (fun T i p => runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) p)
      (fun i p => runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p))
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E)
    (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → ρ → Plan C E)
    (hnext : ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d)
    (hlab : ∀ i, i ∉ D.1 → (hs i).label = L + n ∧ (hs i).tag = tg)
    (hO : ∀ i, i ∉ D.1 → o i = none ∨ o i = some mem.values)
    (hpart : PartialOut D o → SameRun prims (realRestGen K D W knownE knownB count L srch dec n d T0 st o hs next)
      (hybridRestGen K D W knownE knownB names count L tg hist srch dec n d st mem o hs next)) :
    SameRun prims (realRestGen K D W knownE knownB count L srch dec n d T0 st o hs next)
      (hybridRestGen K D W knownE knownB names count L tg hist srch dec n d st mem o hs next) := by
  by_cases hnone : ∀ i, i ∉ D.1 → o i = none
  · have hnp : ¬ PartialOut D o := fun h => by
      obtain ⟨-, i, hi, h⟩ := h
      simp only [hnone i hi, Option.isSome_none, Bool.false_eq_true] at h
    unfold realRestGen hybridRestGen
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), pure_bind, executePhase_congr_honest D _ _ _ _ _ (fun _ => failure)
      (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure, pure_bind,
      RealNetworkC1t.midRest_none]
    refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) (RealNetworkC1t.sameRun_drawTables_drop prims _)
    rw [executePhase_congr_honest D W _ _ st _ (fun _ => failure) (fun i hi => by simp only [hnone i hi,
      Option.elim_none]), executePhase_failure, pure_bind, RealNetworkC1t.realRest_none]
  by_cases hfull : ∀ i, i ∉ D.1 → (o i).isSome
  · have hnp : ¬ PartialOut D o := fun h => by
      obtain ⟨⟨i, hi, h⟩, -⟩ := h
      have := hfull i hi
      simp only [h, Option.isSome_none, Bool.false_eq_true] at this
    have hv : ∀ i, i ∉ D.1 → o i = some mem.values := fun i hi => by
      rcases hO i hi with h | h
      · have := hfull i hi
        simp only [h, Option.isSome_none, Bool.false_eq_true] at this
      · exact h
    have h := genFull prims K D W knownE knownB names count L tg hist srch dec n d hIH T0 st mem hs next mem.values
      hnext hlab
    unfold realRestGen hybridRestGen
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp), pure_bind]
    refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) (h.trans (SameRun.of_eq ?_))
    · congr 1
      refine executePhase_congr_honest D W _ _ st _ _ fun i hi => ?_
      rw [hv i hi, Option.elim_some]
    · congr 1
      refine executePhase_congr_honest D _ _ _ _ _ _ fun i hi => ?_
      change _ = (o i).elim failure fun vals =>
        genNext K srch dec (hybridCheckBuildingBlocks K i) i (hs i) (next i) vals
      rw [hv i hi, Option.elim_some]
  refine hpart ⟨?_, ?_⟩
  · push Not at hfull
    obtain ⟨i, hi, h⟩ := hfull
    exact ⟨i, hi, Option.not_isSome_iff_eq_none.1 h⟩
  · push Not at hnone
    obtain ⟨i, hi, h⟩ := hnone
    exact ⟨i, hi, Option.isSome_iff_ne_none.2 h⟩

/-- The block of a coin at position `n`, with `d` steps after it. The premises `hR` and `hH` split the
programs of the block into the coin and `genNext`. The partial case is the premise `hpart` of `genAfter`. -/
theorem genBlock_of (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (hn : NamesReceivers D names) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) {γ ρ : Type} (srch : List E → OracleComp (RoSpec C) γ)
    (dec : γ → Option ρ) (n d : ℕ) (hnR : n < RealNetworkV3.checkLabels count)
    (hIH : HeadSuffix prims K D W knownE knownB names count L tg hist (n + 1) (2 * d + 1) (2 * d + 2)
      (fun p : C.Party → Plan C E => ∀ i, i ∉ D.1 → PlanOK (p i) d)
      (fun T i p => runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) p)
      (fun i p => runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p))
    (kR : DrawTables C E (RealNetworkV3.checkLabels count) → C.Party → (ρ → Plan C E) → RunM C E RealSpec (HeadOut C E))
    (kH : C.Party → (ρ → Plan C E) → RunM C E (CheckSpec C E) (HeadOut C E))
    (hR : ∀ (T : DrawTables C E (RealNetworkV3.checkLabels count)) (i : C.Party) (b : ρ → Plan C E)
      (hs : RunState C), hs.label = L + n → hs.tag = tg →
      (kR T i b).run hs = openSh K (localContext i) (conv K (localContext i) (frandShare D 2 (knownE n).1
        (knownE n).2 (T.freshE ⟨n, hnR⟩) (T.freshPairE ⟨n, hnR⟩) i).1) 2 >>= fun w =>
          genNext K srch dec (drawnCheckBuildingBlocks K D L knownE knownB T i) i hs b (vector 2 w))
    (hH : ∀ (i : C.Party) (b : ρ → Plan C E) (hs : RunState C), hs.label = L + n → hs.tag = tg →
      (kH i b).run hs = RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>=
        genNext K srch dec (hybridCheckBuildingBlocks K i) i hs b)
    (hpart : ∀ (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E)
      (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → ρ → Plan C E),
      (∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d) →
      (∀ i, i ∉ D.1 → (hs i).label = L + n ∧ (hs i).tag = tg) →
      (∀ i, i ∉ D.1 → o i = none ∨ o i = some mem.values) → PartialOut D o →
      SameRun prims (realRestGen K D W knownE knownB count L srch dec n d T0 st o hs next)
        (hybridRestGen K D W knownE knownB names count L tg hist srch dec n d st mem o hs next)) :
    HeadSuffix prims K D W knownE knownB names count L tg hist n (2 * d + 2) (2 * d + 3)
      (fun next : C.Party → ρ → Plan C E => ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d) kR kH := by
  intro T0 st mem next hs hnext hlab
  let coinPh : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) →
      OracleComp (LocalSpec C) (W.State × (C.Party → Option (List E))) := fun a b =>
    (fun r => (r.1, fun i => (r.2 i).map (vector 2))) <$> RealNetworkC1s.realCoinPhase K D W noFunctionality
      (frandShare D 2 (knownE n).1 (knownE n).2 a b) 2 (0 + 1) st (fun _ => some ())
  let X := liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a =>
    liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b => (fun r => (a, b, r)) <$> coinPh a b
  let Kx : (C.Term → Fin 2 → E) × (C.Pair → Fin 2 → E) × (W.State × (C.Party → Option (List E))) →
      OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) := fun z =>
    realRestGen K D W knownE knownB count L srch dec n d (setRow T0 n z.1 z.2.1) z.2.2.1 z.2.2.2 hs next
  let H : W.State × (C.Party → Option (List E)) → OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
    fun r => hybridRestGen K D W knownE knownB names count L tg hist srch dec n d r.1 ⟨hist, valsOf D r.2⟩ r.2 hs next
  let CP := RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
    (checkFunctionalities K) (0 + 1) ((st, mem), n) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
  have hhop : SameRun prims ((fun z => z.2.2) <$> X) ((fun r => (r.1.1.1, r.2)) <$> CP) := by
    have h := RealNetworkC1q.coinHop prims K D W knownE knownB count hist names hn n 0 0 (st, mem)
    have e : (fun z => z.2.2) <$> X = liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a =>
        liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b => coinPh a b := by
      simp only [X, map_bind, Functor.map_map, id_map']
    rw [e]
    exact h
  have hreal : SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * d + 2) st (fun i => (kR (splice n T0 T) i (next i)).run (hs i)) >>=
          realRest K D W knownE knownB count L (splice n T0 T))
      (X >>= Kx) := by
    refine (RealNetworkC1t.resample prims n _).trans ?_
    simp only [X, bind_assoc]
    refine SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => ?_
    simp only [splice_setRow]
    have hstep : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count), SameRun prims
        (executePhase localRoles D W noFunctionality (2 * d + 2) st (fun i =>
          (kR (splice (n + 1) (setRow T0 n a b) T) i (next i)).run (hs i)) >>=
          realRest K D W knownE knownB count L (splice (n + 1) (setRow T0 n a b) T))
        (executePhase localRoles D W noFunctionality 1 st (fun i => openSh K (localContext i)
            (conv K (localContext i) (frandShare D 2 (knownE n).1 (knownE n).2 a b i).1) 2) >>=
          fun r => executePhase localRoles D W noFunctionality (2 * d + 1) r.1 (fun i => (r.2 i).elim failure
            fun w => genNext K srch dec (drawnCheckBuildingBlocks K D L knownE knownB
              (splice (n + 1) (setRow T0 n a b) T) i) i (hs i) (next i) (vector 2 w)) >>=
          realRest K D W knownE knownB count L (splice (n + 1) (setRow T0 n a b) T)) := by
      intro T
      have hE : (splice (n + 1) (setRow T0 n a b) T).freshE ⟨n, hnR⟩ = a := by
        simp only [splice, setRow]
        simp
      have hP : (splice (n + 1) (setRow T0 n a b) T).freshPairE ⟨n, hnR⟩ = b := by
        simp only [splice, setRow]
        simp
      have e : executePhase localRoles D W noFunctionality (2 * d + 2) st (fun i =>
          (kR (splice (n + 1) (setRow T0 n a b) T) i (next i)).run (hs i)) =
          executePhase localRoles D W noFunctionality (1 + (2 * d + 1)) st (fun i => openSh K (localContext i)
            (conv K (localContext i) (frandShare D 2 (knownE n).1 (knownE n).2 a b i).1) 2 >>=
            fun w => genNext K srch dec (drawnCheckBuildingBlocks K D L knownE knownB
              (splice (n + 1) (setRow T0 n a b) T) i) i (hs i) (next i) (vector 2 w)) := by
        rw [show 2 * d + 2 = 1 + (2 * d + 1) by omega]
        refine executePhase_congr_honest D W _ _ st _ _ fun i hi => ?_
        rw [hR _ i (next i) (hs i) (hlab i hi).1 (hlab i hi).2, hE, hP]
      rw [e]
      refine ((executePhase_bind prims D W noFunctionality 1 (2 * d + 1) st _ _
        fun i _ => ThresholdLeanXmssSecurity.timed_openSh K _ _ 2).bind fun _ => SameRun.refl prims _).trans ?_
      exact SameRun.of_eq (bind_assoc _ _ _)
    refine (SameRun.bind_right _ hstep).trans ?_
    refine (sameRun_swap prims (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count))
      (executePhase localRoles D W noFunctionality 1 st (fun i => openSh K (localContext i)
        (conv K (localContext i) (frandShare D 2 (knownE n).1 (knownE n).2 a b i).1) 2)) _).trans
      (SameRun.of_eq ?_)
    simp only [coinPh, Kx, realRestGen, bind_map_left]
    refine bind_congr fun r => bind_congr fun T => ?_
    congr 2
    funext i
    cases r.2 i <;> rfl
  have hhyb : SameRun prims
      (executePhase localRoles D
          (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
          (checkFunctionalities K) (2 * d + 3) ((st, mem), n) (fun i => (kH i (next i)).run (hs i)) >>=
        midRest K D W knownE knownB names count L tg hist)
      (CP >>= fun r => hybridRestGen K D W knownE knownB names count L tg hist srch dec n d r.1.1.1 r.1.1.2 r.2 hs
        next) := by
    rw [show 2 * d + 3 = 1 + (2 * d + 2) by omega, executePhase_congr_honest D _ _ _ _ _
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>=
        genNext K srch dec (hybridCheckBuildingBlocks K i) i (hs i) (next i))
      (fun i hi => hH i (next i) (hs i) (hlab i hi).1 (hlab i hi).2)]
    refine ((executePhase_bind prims D _ _ 1 (2 * d + 2) _ _ _ fun i _ => RealNetworkC1t.timed_callProg _ _).bind
      fun _ => SameRun.refl prims _).trans ?_
    refine (SameRun.of_eq (bind_assoc _ _ _)).trans ?_
    refine ((coinPhase_tailWith prims K D W knownE knownB count hist names hn
      (c1HeadTails K D W knownE knownB count L tg) 0 (st, mem) n).bind
      fun _ => SameRun.refl prims _).trans ?_
    refine SameRun.of_eq ?_
    rw [bind_assoc, RealNetworkC1t.callPhase_counter K D W knownE knownB count hist names (checkFunctionalities K)
      (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput) (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
      (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
      (fun v r _ => coinOutputs D v r) (fun A st => coinRun_form K D A st), bind_map_left]
    rfl
  have hmemv : ∀ (cache : HashCache C) z, z ∈ support ((simulateQ (localAnswer prims) CP).run cache) →
      ∀ i, i ∉ D.1 → z.1.2 i = none ∨ z.1.2 i = some z.1.1.1.2.values := by
    intro cache z hz i hi
    have hm := (coinMemoryNoTails prims K D W knownE knownB count hist names 0 n (st, mem) cache z hz).2.2
    cases hx : z.1.2 i with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (by rw [hm i v hx])
  have hagree : ∀ (o : C.Party → Option (List E)) (vals : List E), (∀ i, i ∉ D.1 → o i = none ∨ o i = some vals) →
      ∀ i, i ∉ D.1 → ∀ v, o i = some v → v = vals := fun o vals h i hi v hv => by
    rcases h i hi with h | h
    · rw [h] at hv
      cases hv
    · rw [h] at hv
      exact (Option.some.inj hv).symm
  refine hreal.trans (SameRun.trans ?_ hhyb.symm)
  refine (sameRun_bind_join prims X (fun z => z.2.2) _ hhop
    (fun r => ∀ i, i ∉ D.1 → r.2 i = none ∨ r.2 i = some (valsOf D r.2)) ?_ Kx H ?_).trans ?_
  · intro cache z hz
    simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact valsOf_spec D _ _ (hagree _ _ (hmemv cache y hy))
  · intro x hP
    exact genAfter prims K D W knownE knownB names count L tg hist srch dec n d hIH (setRow T0 n x.1 x.2.1)
      x.2.2.1 ⟨hist, valsOf D x.2.2.2⟩ x.2.2.2 hs next hnext hlab hP (hpart _ _ _ _ hs next hnext hlab hP)
  · refine (SameRun.of_eq (bind_map_left _ _ _)).trans (sameRun_bind_sim prims CP fun cache z hz => ?_)
    have h1 := hmemv cache z hz
    have h2 := valsOf_spec D z.1.2 _ (hagree _ _ h1)
    exact (genAfter prims K D W knownE knownB names count L tg hist srch dec n d hIH T0 z.1.1.1.1
      ⟨hist, valsOf D z.1.2⟩ z.1.2 hs next hnext hlab h2 (hpart _ _ _ _ hs next hnext hlab h2)).symm.trans
      (genAfter prims K D W knownE knownB names count L tg hist srch dec n d hIH T0 z.1.1.1.1 z.1.1.1.2 z.1.2 hs next
        hnext hlab h1 (hpart _ _ _ _ hs next hnext hlab h1))

/-- The common end of both sides after a partial output `o` of a coin. The live operators run the search
`search` and read it with `dec`. With a result the adversary sees the round of the next reshare on the known
stream `knownE k`, and each operator aborts. -/
def partialTail (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (k : ℕ) {γ ρ : Type}
    (search : OracleComp (RoSpec C) γ) (dec : γ → Option ρ) (st : W.State) (o : C.Party → Option (List E)) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  liftComp search (LocalSpec C) >>= fun c =>
    if (dec c).isSome then reshareTail K D (elementCodec K) W (knownE k).1 (knownE k).2 2 (liveSet D o) st >>=
      fun st' => pure (st', fun _ => none)
    else pure (st, fun _ => none)

omit [Fintype E] [DecidableEq E] in
/-- The real half of the partial case. The case of a result `r` of the search is the premise `hsome`. -/
theorem partialReal (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L : ℕ) {γ ρ : Type}
    (srch : List E → OracleComp (RoSpec C) γ) (dec : γ → Option ρ) (n d k : ℕ)
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E)
    (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → ρ → Plan C E)
    (hO : ∀ i, i ∉ D.1 → o i = none ∨ o i = some mem.values) (hp : PartialOut D o)
    (hsome : ∀ r, SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * d + 1) st (fun i => (o i).elim failure fun _ =>
          (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i)
            (next i r)).run ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) >>=
          realRest K D W knownE knownB count L (splice (n + 1) T0 T))
      (reshareTail K D (elementCodec K) W (knownE k).1 (knownE k).2 2 (liveSet D o) st >>= fun st' =>
        pure (st', fun _ => none))) :
    SameRun prims (realRestGen K D W knownE knownB count L srch dec n d T0 st o hs next)
      (partialTail K D W knownE k (srch mem.values) dec st o) := by
  let hs1 : C.Party → RunState C := fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
  have hprog : ∀ (T : DrawTables C E (RealNetworkV3.checkLabels count)) (i : C.Party), i ∉ D.1 →
      ((o i).elim failure fun vals =>
        genNext K srch dec (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i) i (hs i) (next i)
          vals) =
      (o i).elim failure fun _ => oracleStep (srch mem.values) >>= fun c => (dec c).elim failure fun r =>
        (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i)
          (next i r)).run (hs1 i) := by
    intro T i hi
    rcases hO i hi with h | h
    · rw [h, Option.elim_none, Option.elim_none]
    · rw [h, Option.elim_some, Option.elim_some]
      rfl
  unfold realRestGen partialTail
  refine (SameRun.bind_right _ (g := fun T => liftComp (srch mem.values) (LocalSpec C) >>= fun c =>
      executePhase localRoles D W noFunctionality (2 * d + 1) st (fun i => (o i).elim failure fun _ =>
        (dec c).elim failure fun r => (runPlan K (localContext i)
          (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i) (next i r)).run (hs1 i)) >>=
        realRest K D W knownE knownB count L (splice (n + 1) T0 T)) fun T => ?_).trans ?_
  · rw [executePhase_congr_honest D W _ _ st _ _ (hprog T)]
    refine ((RealNetworkC1q.hoist prims D W noFunctionality _ st (srch mem.values) o
      (fun i c _ => (dec c).elim failure fun r => (runPlan K (localContext i)
        (drawnCheckBuildingBlocks K D L knownE knownB (splice (n + 1) T0 T) i) (next i r)).run (hs1 i))
      hp.2).bind fun _ => SameRun.refl prims _).trans (SameRun.of_eq ?_)
    rw [bind_assoc]
  refine (sameRun_swap prims (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count))
    (liftComp (srch mem.values) (LocalSpec C)) _).trans ?_
  refine SameRun.bind_right _ fun c => ?_
  cases hc : dec c with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    refine SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) (RealNetworkC1t.sameRun_drawTables_drop prims _)
    rw [executePhase_congr_honest D W _ _ st _ (fun _ => failure) (fun i _ => by
        cases o i <;> simp only [Option.elim_none, Option.elim_some]),
      executePhase_failure, pure_bind, RealNetworkC1t.realRest_none]
  | some r =>
    simp only [Option.isSome_some, ↓reduceIte, Option.elim_some]
    exact hsome r

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A map after a bind, and a continuation. The goals close with `exact` on this form, because the state
of the wrapper does not unify for `rw`. -/
theorem map_bind_bind {α β γ δ : Type} (x : OracleComp (LocalSpec C) α) (k : α → OracleComp (LocalSpec C) β)
    (f : β → γ) (g : γ → OracleComp (LocalSpec C) δ) :
    (f <$> (x >>= k)) >>= g = x >>= fun a => k a >>= fun b => g (f b) := by
  simp only [map_bind, bind_assoc, bind_map_left]

omit [Fintype E] in
/-- The hybrid half of the partial case. The
tail of the wrapper runs the search and the round of the reshare (`htail`). Then each live operator runs the
search again, and its next call aborts (`habort`). -/
theorem partialHybrid (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) {γ ρ : Type} (srch : List E → OracleComp (RoSpec C) γ)
    (dec : γ → Option ρ) (n d k : ℕ) (st : W.State) (mem : C1Memory C E)
    (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → ρ → Plan C E)
    (hO : ∀ i, i ∉ D.1 → o i = none ∨ o i = some mem.values) (hp : PartialOut D o)
    (htail : c1HeadTails K D W knownE knownB count L tg n (liveSet D o) (st, mem) =
      liftComp (srch mem.values) (LocalSpec C) >>= fun c => if (dec c).isSome then
        (fun st' => (st', mem)) <$> reshareTail K D (elementCodec K) W (knownE k).1 (knownE k).2 2 (liveSet D o) st
      else pure (st, mem))
    (habort : ∀ (s : (c1WrapperWith K D W knownE knownB count hist names
        (c1HeadTails K D W knownE knownB count L tg)).State) (r : ρ),
      executePhase localRoles D (c1WrapperWith K D W knownE knownB count hist names
          (c1HeadTails K D W knownE knownB count L tg)) (checkFunctionalities K) (2 * d + 2) s
        (fun i => (o i).elim failure fun _ => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i)
          (next i r)).run ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) =
      pure (s, fun _ => none)) :
    SameRun prims (hybridRestGen K D W knownE knownB names count L tg hist srch dec n d st mem o hs next)
      (partialTail K D W knownE k (srch mem.values) dec st o) := by
  let hs1 : C.Party → RunState C := fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
  let V := c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg)
  have hprog : ∀ (i : C.Party), i ∉ D.1 →
      ((o i).elim failure fun vals => genNext K srch dec (hybridCheckBuildingBlocks K i) i (hs i) (next i) vals) =
      (o i).elim failure fun _ => oracleStep (srch mem.values) >>= fun c => (dec c).elim failure fun r =>
        (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next i r)).run (hs1 i) := by
    intro i hi
    rcases hO i hi with h | h
    · rw [h, Option.elim_none, Option.elim_none]
    · rw [h, Option.elim_some, Option.elim_some]
      rfl
  have habort' : ∀ (s : V.State) (c : γ),
      executePhase localRoles D V (checkFunctionalities K) (2 * d + 2) s (fun i => (o i).elim failure fun _ =>
        (dec c).elim failure fun r => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next i r)).run
          (hs1 i)) =
      pure (s, fun _ => none) := by
    intro s c
    cases dec c with
    | none =>
      rw [executePhase_congr_honest D V _ _ s _ (fun _ => failure) (fun i _ => by
        cases o i <;> simp only [Option.elim_none, Option.elim_some]), executePhase_failure]
    | some r =>
      simp only [Option.elim_some]
      exact habort s r
  have hrest : ∀ s : V.State, SameRun prims
      (executePhase localRoles D V (checkFunctionalities K) (2 * d + 2) s (fun i => (o i).elim failure fun vals =>
        genNext K srch dec (hybridCheckBuildingBlocks K i) i (hs i) (next i) vals) >>=
        midRest K D W knownE knownB names count L tg hist)
      (liftComp (srch mem.values) (LocalSpec C) >>= fun _ => pure (s.1.1, fun _ => none)) := by
    intro s
    rw [executePhase_congr_honest D V _ _ s _ _ hprog]
    refine ((RealNetworkC1q.hoist prims D V (checkFunctionalities K) _ s (srch mem.values) o
      (fun i c _ => (dec c).elim failure fun r => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i)
        (next i r)).run (hs1 i)) hp.2).bind fun _ => SameRun.refl prims _).trans (SameRun.of_eq ?_)
    simp only [bind_assoc, habort', pure_bind]
    exact bind_congr fun _ => RealNetworkC1t.midRest_none K D W knownE knownB names count L tg hist s
  unfold hybridRestGen partialTail
  rw [ite_eq_left_of_eq_true _ _ (eq_true hp), htail]
  refine (SameRun.of_eq (map_bind_bind _ _ _ _)).trans ?_
  refine (SameRun.bind_right _ fun c => SameRun.bind_right _ fun s' => hrest ((s', n + 1))).trans ?_
  refine (RealNetworkRC.sameRun_repeat prims (srch mem.values) (fun c => if (dec c).isSome then
      (fun st' => (st', mem)) <$> reshareTail K D (elementCodec K) W (knownE k).1 (knownE k).2 2 (liveSet D o) st
    else pure (st, mem)) (fun _ s' => pure (s'.1, fun _ => none))).trans (SameRun.of_eq ?_)
  refine bind_congr fun c => ?_
  cases dec c with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pure_bind]
  | some r => simp only [Option.isSome_some, ↓reduceIte, bind_map_left]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Each plan with `d + 1` steps is a step with two products. -/
theorem plan_step (p : Plan C E) (d : ℕ) (h : PlanOK p (d + 1)) :
    ∃ ps nx, p = .step ps nx ∧ ps.length = 2 := by
  cases p with
  | mask A B V =>
    simp only [PlanOK] at h
    omega
  | step ps nx => exact ⟨ps, nx, rfl, h.1⟩

/-- The case of a result `r` in `partialReal` when a step follows. The real `extendMult` sends the round
of its reshare on row `m`, and the GS20 coupling `sameRun_realMsgs` removes its values. -/
theorem stepSome_real (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L : ℕ) (m : ℕ)
    (hN : m < RealNetworkV3.checkLabels count) (d : ℕ) (hd : 0 < d)
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) {ρ : Type}
    (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → ρ → Plan C E)
    (hnext : ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d)
    (hlab : ∀ i, i ∉ D.1 → (hs i).label + 1 = L + m) (hp : PartialOut D o) (r : ρ) :
    SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * d + 1) st (fun i => (o i).elim failure fun _ =>
          (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB (splice m T0 T) i)
            (next i r)).run ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) >>=
          realRest K D W knownE knownB count L (splice m T0 T))
      (reshareTail K D (elementCodec K) W (knownE m).1 (knownE m).2 2 (liveSet D o) st >>=
        fun st' => pure (st', fun _ => none)) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  let hs1 : C.Party → RunState C := fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
  have hex : ∀ i, ∃ ps : List (Product C E), ∃ nx : Shares C E → E → Plan C E,
      i ∉ D.1 → next i r = .step ps nx ∧ ps.length = 2 := fun i => by
    by_cases hi : i ∈ D.1
    · exact ⟨[], fun _ _ => next i r, fun h => absurd hi h⟩
    · obtain ⟨ps, nx, h1, h2⟩ := plan_step _ _ (hnext i hi r)
      exact ⟨ps, nx, fun _ => ⟨h1, h2⟩⟩
  choose ps nx hpn using hex
  let v : C.Party → ℕ → E := fun i => productValues K i (ps i)
  let G : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
    fun a b => W.round st (fun c i => if i ∈ liveSet D o then
      realMsgs K D (elementCodec K) (knownE m).1 (knownE m).2 a b v c i else none) >>=
        fun q => pure (q.1, fun _ => none)
  have hT : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count),
      executePhase localRoles D W noFunctionality (2 * (d + 1) + 1) st (fun i => (o i).elim failure fun _ =>
        (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB (splice m T0 T) i)
          (next i r)).run (hs1 i)) >>= realRest K D W knownE knownB count L (splice m T0 T) =
      G (T.freshE ⟨m, hN⟩) (T.freshPairE ⟨m, hN⟩) := by
    intro T
    let rnd := frandShare D 2 (knownE m).1 (knownE m).2 (T.freshE ⟨m, hN⟩) (T.freshPairE ⟨m, hN⟩)
    let prog : C.Party → List E → PartyM C E RealSpec (HeadOut C E × RunState C) := fun i _ =>
      realExtendProg K rnd i (ps i, hs1 i) >>= fun q =>
        RealNetworkC1t.realAfter K D L knownE knownB (splice m T0 T) i (hs1 i) (nx i) q.1
    have hE : (splice m T0 T).freshE ⟨m, hN⟩ = T.freshE ⟨m, hN⟩ := by
      simp only [splice, lt_self_iff_false, ↓reduceIte]
    have hP : (splice m T0 T).freshPairE ⟨m, hN⟩ = T.freshPairE ⟨m, hN⟩ := by
      simp only [splice, lt_self_iff_false, ↓reduceIte]
    have hc : ∀ i (w : List E), ∃ f, prog i w = exchange (reshareOut K (localContext i) (elementCodec K)
        (rnd i).1 (rnd i).2 (productValues K i (ps i)) (ps i).length) >>= f := fun i w =>
      ⟨_, by simp only [prog]; rw [RealNetworkC1q.realExtendProg_eq, bind_assoc]⟩
    choose f hf using hc
    rw [executePhase_congr_honest D W _ _ st _ (fun i => (o i).elim failure (prog i)) fun i hi =>
      optionElim_congr _ _ _ _ fun w _ => by
        rw [(hpn i hi).1, RealNetworkC1t.realStep_eq K D L knownE knownB _ i (hs1 i) m hN
          (hlab i hi) (ps i) (hpn i hi).2 (nx i), hE, hP]]
    rw [show 2 * (d + 1) + 1 = 2 * d + 2 + 1 by omega, RealNetworkGP.roundPhase_partial D W noFunctionality prog
      (fun i _ => reshareOut K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2 (productValues K i (ps i))
        (ps i).length) f (fun i w => by rw [hf, advance_exchange_bind]) (2 * d + 2) st o hp]
    simp only [bind_assoc, pure_bind, RealNetworkC1t.realRest_none, G]
    congr 2
    funext c i
    unfold realMsgs RealNetworkGP.liveSet liveSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ D.1
    · simp [hi]
    · cases hx : o i with
      | none => simp [hi]
      | some w => by_cases hc : c ∈ D.1 <;> simp [hc, hi, (hpn i hi).2, v, rnd]
  refine (SameRun.bind_right _ fun T => SameRun.of_eq (hT T)).trans
    ((RealNetworkC1t.sameRun_drawTables_row prims m hN G).trans ?_)
  refine (RealNetworkGP.sameRun_realMsgs prims K D (elementCodec K) 2 (knownE m).1
    (knownE m).2 v (fun msgs => W.round st (fun c i => if i ∈ liveSet D o then msgs c i else none) >>=
      fun q => pure (q.1, fun _ => none))).trans (SameRun.of_eq ?_)
  unfold reshareTail
  simp only [bind_assoc, pure_bind]

omit [Fintype E] [DecidableEq E] in
/-- After a result `r` the call of `F_extendMult` of the next step aborts, because an honest operator has no
input. -/
theorem stepAbort (K : Constants C E) (D : C.Coalition) {Ia : Type} (A : CheckAdversary C E Ia) (d : ℕ)
    (hd : 0 < d) {ρ : Type} (o : C.Party → Option (List E)) (hs : C.Party → RunState C)
    (next : C.Party → ρ → Plan C E)
    (hnext : ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d) (hp : PartialOut D o) (s : A.State) (r : ρ) :
    executePhase localRoles D A (checkFunctionalities K) (2 * d + 2) s
        (fun i => (o i).elim failure fun _ => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i)
          (next i r)).run ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) =
      pure (s, fun _ => none) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  let hs1 : C.Party → RunState C := fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
  have hex : ∀ i, ∃ ps : List (Product C E), ∃ nx : Shares C E → E → Plan C E,
      i ∉ D.1 → next i r = .step ps nx ∧ ps.length = 2 := fun i => by
    by_cases hi : i ∈ D.1
    · exact ⟨[], fun _ _ => next i r, fun h => absurd hi h⟩
    · obtain ⟨ps, nx, h1, h2⟩ := plan_step _ _ (hnext i hi r)
      exact ⟨ps, nx, fun _ => ⟨h1, h2⟩⟩
  choose ps nx hpn using hex
  rw [executePhase_congr_honest D A _ _ s _ (fun i => optionalCall ((o i).map fun _ => Sum.inl (Sum.inr (ps i)))
    (fun r' => RealNetworkGP.ofOption (r'.bind fun o' => (extendOutput o').map fun z =>
      (z, extendState K i (hs1 i) z)) >>= fun q => RealNetworkC1t.hybridAfter K i (hs1 i) (nx i) q.1))
    fun i hi => by
      cases o i with
      | none => simp only [Option.elim_none, Option.map_none]; rfl
      | some w =>
        rw [Option.elim_some, Option.map_some, (hpn i hi).1,
          RealNetworkC1t.hybridStep_eq K i (hs1 i) (ps i) (hpn i hi).2 (nx i)]
        simp only [RealNetworkGP.callProg, bind_assoc]
        rfl]
  refine executePhase_partialCall_abort D A (checkFunctionalities K) (2 * (d + 1) + 1) s _ _ (fun i _ => ?_) ?_
  · simp only [Option.bind_none, RealNetworkGP.ofOption, failure_bind]
  · obtain ⟨⟨i, hi, h⟩, -⟩ := hp
    exact ⟨i, hi, by simp only [h, Option.map_none]⟩

omit [Fintype E] in
/-- The tail of the wrapper after the coin of step `j` when a step follows. -/
theorem stepTail_eq (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (count L tg j d : ℕ) (hjd : j + 1 + (d + 1) = halvings count) (live : Finset C.Party) (st : W.State)
    (mem : C1Memory C E) :
    c1HeadTails K D W knownE knownB count L tg (2 * j + 2) live (st, mem) =
      liftComp (challengeQuery K tg (L + (2 * j + 2)) mem.values) (LocalSpec C) >>= fun c => if (id c).isSome then
        (fun st' => (st', mem)) <$> reshareTail K D (elementCodec K) W (knownE (2 * j + 2 + 1)).1
          (knownE (2 * j + 2 + 1)).2 2 live st
      else pure (st, mem) := by
  simp only [c1HeadTails, c1Tails, nextMult, show 2 * j + 2 ≠ 2 * halvings count + 2 by omega,
    show 2 * j + 2 ≠ 0 by omega, show ¬ 2 * halvings count < 2 * j + 2 by omega,
    show ¬ (2 * j + 2) % 2 = 1 by omega, show 2 * j + 2 < 2 * halvings count by omega, ↓reduceIte]
  rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real program of a challenge at position `n` is the coin and `genNext`. -/
theorem coin_hR (K : Constants C E) (D : C.Coalition) (L tg n : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    {m : ℕ} (hnR : n < m) (T : DrawTables C E m) (i : C.Party) (b : E → Plan C E) (hs : RunState C)
    (hl : hs.label = L + n) (ht : hs.tag = tg) :
    (challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
        runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (b r)).run hs =
      openSh K (localContext i) (conv K (localContext i) (frandShare D 2 (knownE n).1
        (knownE n).2 (T.freshE ⟨n, hnR⟩) (T.freshPairE ⟨n, hnR⟩) i).1) 2 >>= fun w =>
          genNext K (fun vals => challengeQuery K tg (L + n) vals) id
            (drawnCheckBuildingBlocks K D L knownE knownB T i) i hs b (vector 2 w) := by
  have hn : hs.label - L = n := by
    rw [hl]
    omega
  rw [RealNetworkC1y.realCoin_split, hn]
  simp only [drawnE, hnR, ↓reduceDIte]
  refine bind_congr fun w => ?_
  exact coinNext_eq K _ i hs b _ _ _ hl ht

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The hybrid program of a challenge at position `n` is the call of `F_coin` and `genNext`. -/
theorem coin_hH (K : Constants C E) (L tg n : ℕ) (i : C.Party) (b : E → Plan C E) (hs : RunState C)
    (hl : hs.label = L + n) (ht : hs.tag = tg) :
    (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
        runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (b r)).run hs =
      RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>=
        genNext K (fun vals => challengeQuery K tg (L + n) vals) id (hybridCheckBuildingBlocks K i) i hs b := by
  rw [hybridCoin_split]
  refine bind_congr fun v => ?_
  exact coinNext_eq K _ i hs b _ _ _ hl ht

theorem coinBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) : CoinBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist j d hjd hIH
  have hjR : 2 * j + 2 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  have hm : 2 * j + 2 + 1 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  unfold PlanSuffix at hIH
  rw [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by omega] at hIH
  exact genBlock_of prims K D W knownE knownB names hn count L tg hist
    (fun vals => challengeQuery K tg (L + (2 * j + 2)) vals) id (2 * j + 2) (d + 1) hjR hIH _ _
    (fun T i b hs hl ht => coin_hR K D L tg (2 * j + 2) knownE knownB hjR T i b hs hl ht)
    (fun i b hs hl ht => coin_hH K L tg (2 * j + 2) i b hs hl ht)
    fun T0 st mem o hs next hnext hlab hO hp =>
      (partialReal prims K D W knownE knownB count L _ id (2 * j + 2) (d + 1) (2 * j + 2 + 1) T0 st mem o hs next
        hO hp (stepSome_real prims K D W knownE knownB count L (2 * j + 2 + 1) hm (d + 1) (by omega) T0 st o hs next
          hnext (fun i hi => by rw [(hlab i hi).1]; omega) hp)).trans
        (partialHybrid prims K D W knownE knownB names count L tg hist _ id (2 * j + 2) (d + 1) (2 * j + 2 + 1) st
          mem o hs next hO hp (stepTail_eq K D W knownE knownB count L tg j d hjd _ st mem)
          (stepAbort K D _ (d + 1) (by omega) o hs next hnext hp)).symm

end ThresholdLeanXmssSecurity.RealNetworkC1c

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

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Each plan with no step is the masked multiplication. -/
theorem plan_mask (p : Plan C E) (h : PlanOK p 0) : ∃ A B V, p = .mask A B V := by
  cases p with
  | mask A B V => exact ⟨A, B, V, rfl⟩
  | step ps nx =>
    obtain ⟨-, d', hd, -⟩ := h
    omega

/-- The case of a challenge `r` in `partialReal` when the masked multiplication follows. -/
theorem maskSome_real (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ) (j : ℕ)
    (hj : j + 1 = halvings count)
    (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State)
    (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → E → Plan C E)
    (hnext : ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) 0)
    (hlab : ∀ i, i ∉ D.1 → (hs i).label = L + (2 * j + 2) ∧ (hs i).tag = tg) (hp : PartialOut D o) (r : E) :
    SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * 0 + 1) st (fun i => (o i).elim failure fun _ =>
          (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB (splice (2 * j + 3) T0 T) i)
            (next i r)).run ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) >>=
          realRest K D W knownE knownB count L (splice (2 * j + 3) T0 T))
      (reshareTail K D (elementCodec K) W (knownE (2 * j + 3 + 1)).1 (knownE (2 * j + 3 + 1)).2 2 (liveSet D o) st >>=
        fun st' => pure (st', fun _ => none)) := by
  let hs1 : C.Party → RunState C := fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
  have hN3 : 2 * j + 3 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  have hN4 : 2 * j + 3 + 1 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  have hex : ∀ i, ∃ A B : ℕ → E, ∃ V : E, i ∉ D.1 → next i r = .mask A B V := fun i => by
    by_cases hi : i ∈ D.1
    · exact ⟨fun _ => 0, fun _ => 0, 0, fun h => absurd hi h⟩
    · obtain ⟨A, B, V, h⟩ := plan_mask _ (hnext i hi r)
      exact ⟨A, B, V, fun _ => h⟩
  choose A B V hm using hex
  let v : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → C.Party → ℕ → E := fun a1 b1 i =>
    productValues K i (RealNetworkC1w.maskProducts K i (A i) (B i)
      (frandShare D 2 (knownE (2 * j + 3)).1 (knownE (2 * j + 3)).2 a1 b1 i))
  let X : (C.Party → C.Party → Option (Msg E)) → OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
    fun msgs => W.round st (fun c i => if i ∈ liveSet D o then msgs c i else none) >>=
      fun q => pure (q.1, fun _ => none)
  let G : (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) → (C.Term → Fin 2 → E) → (C.Pair → Fin 2 → E) →
      OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) := fun a1 b1 a2 b2 =>
    X (realMsgs K D (elementCodec K) (knownE (2 * j + 3 + 1)).1 (knownE (2 * j + 3 + 1)).2 a2 b2 (v a1 b1))
  have hT : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count),
      executePhase localRoles D W noFunctionality (2 * 0 + 1) st (fun i => (o i).elim failure fun _ =>
        (runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB (splice (2 * j + 3) T0 T) i)
          (next i r)).run (hs1 i)) >>= realRest K D W knownE knownB count L (splice (2 * j + 3) T0 T) =
      G (T.freshE ⟨2 * j + 3, hN3⟩) (T.freshPairE ⟨2 * j + 3, hN3⟩) (T.freshE ⟨2 * j + 3 + 1, hN4⟩)
        (T.freshPairE ⟨2 * j + 3 + 1, hN4⟩) := by
    intro T
    let rnd1 := frandShare D 2 (knownE (2 * j + 3)).1 (knownE (2 * j + 3)).2 (T.freshE ⟨2 * j + 3, hN3⟩)
      (T.freshPairE ⟨2 * j + 3, hN3⟩)
    let rnd2 := frandShare D 2 (knownE (2 * j + 3 + 1)).1 (knownE (2 * j + 3 + 1)).2 (T.freshE ⟨2 * j + 3 + 1, hN4⟩)
      (T.freshPairE ⟨2 * j + 3 + 1, hN4⟩)
    let hs2 : C.Party → RunState C := fun i => ⟨(hs1 i).history, (hs1 i).label + 1, (hs1 i).tag⟩
    let prog : C.Party → List E → PartyM C E RealSpec (HeadOut C E × RunState C) := fun i _ =>
      realExtendProg K rnd2 i (RealNetworkC1w.maskProducts K i (A i) (B i) (rnd1 i), hs2 i) >>= fun q =>
        pure (RealNetworkC1w.maskOut K i (A i) (B i) (V i) (rnd1 i) (hs2 i) q.1)
    have hc : ∀ i (w : List E), ∃ f, prog i w = exchange (reshareOut K (localContext i) (elementCodec K)
        (rnd2 i).1 (rnd2 i).2 (productValues K i (RealNetworkC1w.maskProducts K i (A i) (B i) (rnd1 i)))
        (RealNetworkC1w.maskProducts K i (A i) (B i) (rnd1 i)).length) >>= f := fun i w =>
      ⟨_, by simp only [prog]; rw [RealNetworkC1q.realExtendProg_eq, bind_assoc]⟩
    choose f hf using hc
    have hd : ∀ i, drawnE D knownE (splice (2 * j + 3) T0 T) (2 * j + 3) i = rnd1 i := fun i => by
      simp only [drawnE, hN3, ↓reduceDIte, splice, lt_self_iff_false, ↓reduceIte, rnd1]
    have h4E : (splice (2 * j + 3) T0 T).freshE ⟨2 * j + 3 + 1, hN4⟩ = T.freshE ⟨2 * j + 3 + 1, hN4⟩ := by
      simp only [splice]
      simp
    have h4P : (splice (2 * j + 3) T0 T).freshPairE ⟨2 * j + 3 + 1, hN4⟩ = T.freshPairE ⟨2 * j + 3 + 1, hN4⟩ := by
      simp only [splice]
      simp
    rw [executePhase_congr_honest D W _ _ st _ (fun i => (o i).elim failure (prog i)) fun i hi =>
      optionElim_congr _ _ _ _ fun w _ => by
        rw [hm i hi, RealNetworkC1w.realMask_eq K D L knownE knownB _ i (hs1 i) (2 * j + 3) hN4
          (by simp only [hs1, (hlab i hi).1]; omega) (A i) (B i) (V i), hd, h4E, h4P]]
    rw [show 2 * 0 + 1 = 0 + 1 by rfl, RealNetworkGP.roundPhase_partial D W noFunctionality prog
      (fun i _ => reshareOut K (localContext i) (elementCodec K) (rnd2 i).1 (rnd2 i).2
        (productValues K i (RealNetworkC1w.maskProducts K i (A i) (B i) (rnd1 i)))
        (RealNetworkC1w.maskProducts K i (A i) (B i) (rnd1 i)).length) f
      (fun i w => by rw [hf, advance_exchange_bind]) 0 st o hp]
    simp only [bind_assoc, pure_bind, RealNetworkC1t.realRest_none, G, X]
    congr 2
    funext c i
    unfold realMsgs RealNetworkGP.liveSet liveSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ D.1
    · simp [hi]
    · cases hx : o i with
      | none => simp [hi]
      | some w => by_cases hc : c ∈ D.1 <;> simp [hc, hi, v, rnd1, rnd2, RealNetworkC1w.maskProducts]
  refine (SameRun.bind_right _ fun T => SameRun.of_eq (hT T)).trans ?_
  refine (RealNetworkC1t.resample prims (2 * j + 3) _).trans ?_
  have hrow : ∀ a1 b1, SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        G ((setRow T (2 * j + 3) a1 b1).freshE ⟨2 * j + 3, hN3⟩) ((setRow T (2 * j + 3) a1 b1).freshPairE ⟨2 * j + 3, hN3⟩)
          ((setRow T (2 * j + 3) a1 b1).freshE ⟨2 * j + 3 + 1, hN4⟩)
          ((setRow T (2 * j + 3) a1 b1).freshPairE ⟨2 * j + 3 + 1, hN4⟩))
      (liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C) >>= fun a2 =>
        liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b2 =>
          X (realMsgs K D (elementCodec K) (knownE (2 * j + 3 + 1)).1 (knownE (2 * j + 3 + 1)).2 a2 b2
            fun _ _ => 0)) := by
    intro a1 b1
    have e : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count),
        G ((setRow T (2 * j + 3) a1 b1).freshE ⟨2 * j + 3, hN3⟩) ((setRow T (2 * j + 3) a1 b1).freshPairE ⟨2 * j + 3, hN3⟩)
          ((setRow T (2 * j + 3) a1 b1).freshE ⟨2 * j + 3 + 1, hN4⟩)
          ((setRow T (2 * j + 3) a1 b1).freshPairE ⟨2 * j + 3 + 1, hN4⟩) =
        G a1 b1 (T.freshE ⟨2 * j + 3 + 1, hN4⟩) (T.freshPairE ⟨2 * j + 3 + 1, hN4⟩) := fun T => by
      simp only [setRow, ↓reduceIte, show 2 * j + 3 + 1 ≠ 2 * j + 3 by omega]
    simp only [e]
    exact (RealNetworkC1t.sameRun_drawTables_row prims (2 * j + 3 + 1) hN4 (G a1 b1)).trans
      (RealNetworkGP.sameRun_realMsgs prims K D (elementCodec K) 2 (knownE (2 * j + 3 + 1)).1
        (knownE (2 * j + 3 + 1)).2 (v a1 b1) X)
  refine (SameRun.bind_right _ fun a1 => SameRun.bind_right _ fun b1 => hrow a1 b1).trans ?_
  refine ((SameRun.bind_right _ fun _ => RealNetworkC1t.sameRun_drop prims _ _).trans
    (RealNetworkC1t.sameRun_drop prims _ _)).trans (SameRun.of_eq ?_)
  unfold reshareTail
  simp only [X, bind_assoc, pure_bind]

omit [Fintype E] in
/-- The tail of the wrapper after the coin of the last challenge. -/
theorem maskTail_eq (K : Constants C E) (D : C.Coalition) {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (count L tg j : ℕ) (hj : j + 1 = halvings count) (live : Finset C.Party) (st : W.State)
    (mem : C1Memory C E) :
    c1HeadTails K D W knownE knownB count L tg (2 * j + 2) live (st, mem) =
      liftComp (challengeQuery K tg (L + (2 * j + 2)) mem.values) (LocalSpec C) >>= fun c => if (id c).isSome then
        (fun st' => (st', mem)) <$> reshareTail K D (elementCodec K) W (knownE (2 * j + 3 + 1)).1
          (knownE (2 * j + 3 + 1)).2 2 live st
      else pure (st, mem) := by
  simp only [c1HeadTails, c1Tails, nextMult, show 2 * j + 2 ≠ 2 * halvings count + 2 by omega,
    show 2 * j + 2 ≠ 0 by omega, show ¬ 2 * halvings count < 2 * j + 2 by omega,
    show ¬ (2 * j + 2) % 2 = 1 by omega, show ¬ 2 * j + 2 < 2 * halvings count by omega, ↓reduceIte]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- After a challenge `r` the call of `F_rand` of the mask aborts, because an honest operator has no
input. -/
theorem maskAbort (K : Constants C E) (D : C.Coalition) {Ia : Type} (A : CheckAdversary C E Ia)
    (o : C.Party → Option (List E)) (hs : C.Party → RunState C) (next : C.Party → E → Plan C E)
    (hnext : ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) 0) (hp : PartialOut D o) (s : A.State) (r : E) :
    executePhase localRoles D A (checkFunctionalities K) (2 * 0 + 2) s
        (fun i => (o i).elim failure fun _ => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i)
          (next i r)).run ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) =
      pure (s, fun _ => none) := by
  let hs1 : C.Party → RunState C := fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
  have hex : ∀ i, ∃ A B : ℕ → E, ∃ V : E, i ∉ D.1 → next i r = .mask A B V := fun i => by
    by_cases hi : i ∈ D.1
    · exact ⟨fun _ => 0, fun _ => 0, 0, fun h => absurd hi h⟩
    · obtain ⟨A, B, V, h⟩ := plan_mask _ (hnext i hi r)
      exact ⟨A, B, V, fun _ => h⟩
  choose Am Bm Vm hm using hex
  rw [executePhase_congr_honest D A _ _ s _ (fun i => optionalCall ((o i).map fun _ => Sum.inr (Sum.inl 2))
    (RealNetworkC1w.hybridMaskAfter K i (Am i) (Bm i) (Vm i) (hs1 i)))
    fun i hi => by
      cases o i with
      | none => simp only [Option.elim_none, Option.map_none]; rfl
      | some w =>
        rw [Option.elim_some, Option.map_some, hm i hi, RealNetworkC1w.hybridMask_eq K i (hs1 i)]
        rfl]
  refine executePhase_partialCall_abort D A (checkFunctionalities K) (2 * 0 + 1) s _ _ (fun i _ => rfl) ?_
  obtain ⟨⟨i, hi, h⟩, -⟩ := hp
  exact ⟨i, hi, by simp only [h, Option.map_none]⟩

theorem lastCoinBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    LastCoinBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist j hj hIH
  have hjR : 2 * j + 2 < RealNetworkV3.checkLabels count := by
    unfold RealNetworkV3.checkLabels
    omega
  unfold PlanSuffix at hIH
  rw [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by omega] at hIH
  exact genBlock_of prims K D W knownE knownB names hn count L tg hist
    (fun vals => challengeQuery K tg (L + (2 * j + 2)) vals) id (2 * j + 2) 0 hjR hIH _ _
    (fun T i b hs hl ht => coin_hR K D L tg (2 * j + 2) knownE knownB hjR T i b hs hl ht)
    (fun i b hs hl ht => coin_hH K L tg (2 * j + 2) i b hs hl ht)
    fun T0 st mem o hs next hnext hlab hO hp =>
      (partialReal prims K D W knownE knownB count L _ id (2 * j + 2) 0 (2 * j + 3 + 1) T0 st mem o hs next hO hp
        (maskSome_real prims K D W knownE knownB count L tg j hj T0 st o hs next hnext hlab hp)).trans
        (partialHybrid prims K D W knownE knownB names count L tg hist _ id (2 * j + 2) 0 (2 * j + 3 + 1) st mem o hs
          next hO hp (maskTail_eq K D W knownE knownB count L tg j hj _ st mem)
          (maskAbort K D _ o hs next hnext hp)).symm

end ThresholdLeanXmssSecurity.RealNetworkC1c

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1w.maskBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1w.maskBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1y.realCoin_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1y.realCoin_split

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1y.hybridCoin_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1y.hybridCoin_split

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1c.coinBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1c.coinBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1c.lastCoinBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1c.lastCoinBlock
