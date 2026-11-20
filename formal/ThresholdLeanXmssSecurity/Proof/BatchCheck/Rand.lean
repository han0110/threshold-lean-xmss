import ThresholdLeanXmssSecurity.Proof.BatchCheck.Plan

/-!
# The hops of `F_rand` and the rest of the check after a partial head

The hops of `F_rand` hold because both sides are equal programs. `randBitsBlock` proves the block of the salts, and `restPartial` gives the real rest of the check after
a partial head.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1u

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- `randElements` of the hybrid model as one call of `F_rand`, with its final state. -/
theorem hybrid_randElements_run (K : Constants C E) (i : C.Party) (count : ℕ) (st : RunState C) :
    ((hybridCheckBuildingBlocks K i).randElements count).run st =
      call (Sum.inr (Sum.inl count)) >>= fun o => match o with
        | some (.inr (.inl w)) => pure (w, ⟨st.history, st.label + 1, st.tag⟩)
        | _ => failure := by
  simp only [hybridCheckBuildingBlocks, freshLabel]
  simp [StateT.run_bind, StateT.run_lift, StateT.run_modifyGet]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | (w | w)) <;> simp [StateT.run_lift]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real `randElements` on drawn values reads the row of its label. -/
theorem drawn_randElements_run {m : ℕ} (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (T : DrawTables C E m) (i : C.Party) (count : ℕ)
    (st : RunState C) :
    ((drawnCheckBuildingBlocks K D L knownE knownB T i).randElements count).run st =
      pure (drawnE D knownE T (st.label - L) i, ⟨st.history, st.label + 1, st.tag⟩) := by
  simp [drawnCheckBuildingBlocks, freshLabel, StateT.run_modifyGet]

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Under `NamesReceivers` a reply to `F_rand` is not partial. -/
theorem frand_not_partial_names (D : C.Coalition) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (hN : NamesReceivers D names) (l : Unit ⊕ Unit) (r : CheckAnswer C E) :
    ¬ PartialOut D (receivers D names (Sum.inr l : CheckLeak C E) r) := by
  have he : receivers D names (Sum.inr l : CheckLeak C E) r = receivers D c1Names (Sum.inr l : CheckLeak C E) r := by
    funext i
    unfold receivers
    by_cases hi : i ∈ D.1
    · simp only [hi, not_true_eq_false, false_and, ↓reduceIte]
    · simp only [hi, not_false_eq_true, true_and, hN _ _ i hi]
  rw [he]
  exact frand_not_partial D l r

omit [Fintype E] [DecidableEq E] in
/-- The wrapper answers a call of `F_rand` for elements with the known stream of its counter, runs no
tail and counts the call. The state type is written out, so that `pure_bind` applies after a rewrite. -/
theorem frandElements_answer {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ) (hist : C.Party → C.Term → List Bit)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (hN : NamesReceivers D names)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (s : W.State × C1Memory C E) (k : ℕ) :
    (leftAdversary (rightAdversary (c1WrapperWith K D W knownE knownB count hist names tails))).answer (s, k) () =
      (pure (((s, k + 1) : (c1WrapperWith K D W knownE knownB count hist names tails).State), knownE k) :
        OracleComp (LocalSpec C) _) := by
  simp only [leftAdversary, rightAdversary, c1Sims, frand_not_partial_names D names hN, ite_false]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- The wrapper answers a call of `F_rand` for bits with `knownB`, runs no tail and counts the call. -/
theorem frandBits_answer {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ) (hist : C.Party → C.Term → List Bit)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (hN : NamesReceivers D names)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (s : W.State × C1Memory C E) (k : ℕ) :
    (rightAdversary (rightAdversary (c1WrapperWith K D W knownE knownB count hist names tails))).answer (s, k) () =
      (pure (((s, k + 1) : (c1WrapperWith K D W knownE knownB count hist names tails).State), knownB) :
        OracleComp (LocalSpec C) _) := by
  simp only [rightAdversary, c1Sims, frand_not_partial_names D names hN, ite_false]
  rfl

end ThresholdLeanXmssSecurity.RealNetworkC1u

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1u

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1t

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real `randBits` on drawn values, then a continuation. -/
theorem drawn_randBits_bind {m : ℕ} {α : Type} (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (T : DrawTables C E m) (i : C.Party) (count : ℕ)
    (f : PrssOutput C Bit → RunM C E RealSpec α) (st : RunState C) :
    ((drawnCheckBuildingBlocks K D L knownE knownB T i).randBits count >>= f).run' st =
      (f (frandShare D 256 knownB.1 knownB.2 T.freshB T.freshPairB i)).run' ⟨st.history, st.label + 1, st.tag⟩ := by
  simp [drawnCheckBuildingBlocks, freshLabel, StateT.run'_eq, StateT.run_bind, StateT.run_modifyGet]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The coin of the drawn building blocks reads only the rows over `E`. -/
theorem drawn_coin_congr {m : ℕ} (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (T1 T2 : DrawTables C E m) (i : C.Party)
    (hE : T1.freshE = T2.freshE) (hP : T1.freshPairE = T2.freshPairE) :
    (drawnCheckBuildingBlocks K D L knownE knownB T1 i).coin = (drawnCheckBuildingBlocks K D L knownE knownB T2 i).coin := by
  simp only [drawnCheckBuildingBlocks, drawnE, hE, hP]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A challenge reads only the coin of the building blocks. -/
theorem challenge_congr {ι : Type} {G : OracleSpec ι} (K : Constants C E) (bb1 bb2 : CheckBuildingBlocks C E G)
    (h : bb1.coin = bb2.coin) : challenge K bb1 = challenge K bb2 := by
  simp only [challenge, coinKey, h]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The rest of the check in the hybrid model is the salts, the digest round, the last challenge and
`openTailOf`. -/
theorem checkRest_eq (K : Constants C E) (i : C.Party) (v : HeadOut C E) :
    checkRest K i v = (hybridCheckBuildingBlocks K i).randBits 256 >>= fun salts =>
      compareDigests (localContext i) salts.1 >>= fun _ =>
        challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) v r := by
  simp only [checkRest, finalRest, finalAfterDigests, finalOpenProgram, openTailOf]
  refine bind_congr fun s => bind_congr fun _ => bind_congr fun r => ?_
  apply StateT.ext
  intro st
  simp [StateT.run_bind, StateT.run_lift]
  rfl

theorem randBitsBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    RandBitsBlockStatement prims K D := by
  intro Ia W knownE knownB names hN count L tg hist hD T0 st mem v hs hlab
  have hH : ((fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
      (checkFunctionalities K) 5 ((st, mem), 2 * halvings count + 3) fun i =>
        StateT.run' ((fun i v => checkRest K i v) i (v i)) (hs i)) = (do
      let sa ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
      let sb ← liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C)
      (fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) 4 ((st, mem), 2 * halvings count + 4) fun i =>
          (compareDigests (localContext i) (frandShare D 256 knownB.1 knownB.2 sa sb i).1 >>= fun _ =>
            challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r).run'
            ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) := by
    simp only [checkRest_eq]
    rw [executePhase_randBits K D _ 4 _ (fun _ => 256) hs (fun i salts => compareDigests (localContext i) salts.1 >>=
      fun _ => challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r),
      runFunctionality_rand_local D _ _ _ (by intro i hi; simp [hi]), firstInput_honest_const,
      frandBits_answer K D W knownE knownB count hist names hN _ _ _, pure_bind]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun sa => bind_congr fun sb => ?_
    rw [executePhase_congr_honest D _ _ 4 _ _ _ fun i hi => ?_]
    simp only [randFinish, hi, ite_false]
    rfl
  rw [hH]
  refine (resampleBits prims _).trans ?_
  refine SameRun.bind_right _ fun sa => SameRun.bind_right _ fun sb => ?_
  refine (resample prims (2 * halvings count + 3) _).trans ?_
  refine SameRun.trans (SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => ?_)
    ((sameRun_drop prims _ _).trans (sameRun_drop prims _ _))
  have hE (T : DrawTables C E (RealNetworkV3.checkLabels count)) :
      (splice (2 * halvings count + 3) T0 (setSalts (setRow T (2 * halvings count + 3) a b) sa sb)).freshE =
        (splice (2 * halvings count + 4) (setRow T0 (2 * halvings count + 3) a b) T).freshE := by
    funext k
    simp only [splice, setSalts, setRow]
    split_ifs <;> first | rfl | omega
  have hP (T : DrawTables C E (RealNetworkV3.checkLabels count)) :
      (splice (2 * halvings count + 3) T0 (setSalts (setRow T (2 * halvings count + 3) a b) sa sb)).freshPairE =
        (splice (2 * halvings count + 4) (setRow T0 (2 * halvings count + 3) a b) T).freshPairE := by
    funext k
    simp only [splice, setSalts, setRow]
    split_ifs <;> first | rfl | omega
  refine SameRun.trans (SameRun.of_eq (bind_congr fun T => executePhase_congr_honest D W noFunctionality 6 st _
    (fun i => StateT.run' (compareDigests (localContext i) (frandShare D 256 knownB.1 knownB.2 sa sb i).1 >>= fun _ =>
      challenge K (drawnCheckBuildingBlocks K D L knownE knownB
        (splice (2 * halvings count + 4) (setRow T0 (2 * halvings count + 3) a b) T) i) >>= fun r =>
          openTailOf K (localContext i) (v i) r) ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩)
    fun i _ => ?_)) ?_
  · simp only [checkRestOf_eq, drawn_randBits_bind]
    rw [challenge_congr K _ _ (drawn_coin_congr K D L knownE knownB _ _ i (hE T) (hP T))]
    rfl
  · refine hD (setRow T0 (2 * halvings count + 3) a b) st mem (fun i => (frandShare D 256 knownB.1 knownB.2 sa sb i, v i))
      (fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) fun i hi => ?_
    obtain ⟨h1, h2⟩ := hlab i hi
    exact ⟨by simp only [h1]; omega, h2⟩

end ThresholdLeanXmssSecurity.RealNetworkC1u

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

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation that reads only the salts of a drawn table is a draw of the salts. -/
theorem sameRun_drawTables_freshB (prims : Primitives) {m : ℕ} {β : Type}
    (X : (C.Term → Fin 256 → Bit) → OracleComp (LocalSpec C) β) :
    SameRun prims (drawTables (C := C) (E := E) m >>= fun T => X T.freshB)
      (liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C) >>= X) := by
  unfold drawTables
  simp only [bind_assoc, pure_bind]
  refine (SameRun.bind_right _ fun _ => SameRun.bind_right _ fun _ => SameRun.bind_right _ fun _ =>
    sameRun_drop prims _ _).trans ?_
  exact (sameRun_drop prims _ _).trans (sameRun_drop prims _ _)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real rest at a live operator is the digest round with the salts of the table, from the run state
after the label of the salts. -/
theorem drawnRest_eq {m : ℕ} (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (T : DrawTables C E m) (i : C.Party)
    (p : HeadOut C E × RunState C) :
    drawnRestAt K D L knownE knownB T i p =
      (compareDigests (localContext i) (digestSalts D knownB T.freshB i) >>= fun _ =>
        challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
          openTailOf K (localContext i) p.1 r).run' { p.2 with label := p.2.label + 1 } :=
  rfl

omit [Fintype E] [DecidableEq E] in
theorem restPartial (prims : Primitives) (K : Constants C E) (D : C.Coalition) : RestPartialStatement prims K D := by
  intro Ia W knownE knownB count L T0 st o hp
  let inputs : C.Party → Option (RunState C) := fun i => (o i).map fun p => { p.2 with label := p.2.label + 1 }
  let o' : C.Party → Option (RunState C) := fun i => (o i).map Prod.snd
  have hlive : RealNetworkRC.liveSet D inputs = RealNetworkRC.liveSet D o' := by
    unfold RealNetworkRC.liveSet
    exact Finset.filter_congr fun i _ => by simp only [inputs, o', Option.isSome_map]
  have hhist : RealNetworkRC.histOf inputs = RealNetworkRC.histOf o' := by
    funext i
    cases hx : o i <;> simp only [RealNetworkRC.histOf, inputs, o', hx, Option.map_none, Option.map_some]
  obtain ⟨⟨i₀, hi₀, hn₀⟩, i₁, hi₁, hs₁⟩ := hp
  have hpo : RealNetworkRC.PartialOut D o' :=
    ⟨⟨i₀, hi₀, by simp only [o', hn₀, Option.map_none]⟩, i₁, hi₁, by simpa only [o', Option.isSome_map] using hs₁⟩
  have hpi : RealNetworkRC.PartialOut D inputs :=
    ⟨⟨i₀, hi₀, by simp only [inputs, hn₀, Option.map_none]⟩, i₁, hi₁,
      by simpa only [inputs, Option.isSome_map] using hs₁⟩
  have h1 : ∀ T : DrawTables C E (RealNetworkV3.checkLabels count),
      realRest K D W knownE knownB count L (splice (2 * halvings count + 3) T0 T) (st, o) =
        RealNetworkRC.realDigestPhase D W noFunctionality 6 st (digestSalts D knownB T.freshB) inputs
          (fun i _ => (o i).elim (pure ()) fun p =>
            challenge K (drawnCheckBuildingBlocks K D L knownE knownB (splice (2 * halvings count + 3) T0 T) i) >>=
              fun r => openTailOf K (localContext i) p.1 r) := by
    intro T
    unfold realRest RealNetworkRC.realDigestPhase
    congr 1
    funext i
    cases hx : o i with
    | none => simp only [inputs, hx, Option.map_none, Option.elim_none]
    | some p =>
      simp only [inputs, hx, Option.map_some, Option.elim_some]
      exact drawnRest_eq K D L knownE knownB _ i p
  simp only [h1]
  refine (SameRun.bind_right _ fun T =>
    RealNetworkRC.realDigestPhase_partial prims D W noFunctionality 5 st _ inputs hpi _).trans ?_
  refine SameRun.trans ?_ (SameRun.bind_right _ fun table =>
    RealNetworkRC.realDigestPhase_partial prims D W noFunctionality 0 st _ o' hpo _).symm
  rw [hlive, hhist]
  exact sameRun_drawTables_freshB prims fun b => do
    let v ← OverPermutation.sequenceFin fun i => C.terms.mapM fun T =>
      RealNetworkRC.liveCol (· ∈ RealNetworkRC.liveSet D o') (digestSalts D knownB b) (RealNetworkRC.histOf o') T i
    let r ← W.round st (RealNetworkRC.digestMsgs D (RealNetworkRC.liveSet D o') v)
    pure (r.1, fun _ => none)

end ThresholdLeanXmssSecurity.RealNetworkC1t

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1u.randBitsBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1u.randBitsBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1t.restPartial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1t.restPartial
