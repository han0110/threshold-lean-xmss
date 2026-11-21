import ThresholdLeanXmssSecurity.Proof.Check

/-!
# The final segment and the halving loop of the check

The programs of the final segment and of the halving loop of the check (GS20, Protocol 14) at one
operator, and the runs of these phases after a common challenge
(`executePhase_afterChallenge_common`, `executePhase_afterChallenge_common'`). The lemmas give the
form of each step, its outputs, and the case of an operator that misses an input.
-/

noncomputable section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Stages

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## The final segment of the check -/

/-- The check after the masked multiplication of the randomization. -/
def finalRest (K : Constants C E) (i : C.Party) (a b d : E) (w q : Shares C E) :
    RunM C E (CheckSpec C E) Unit := do
  let salts ← (hybridCheckBuildingBlocks K i).randBits 256
  compareDigests (localContext i) salts.1
  finalAfterDigests K i (conv K (localContext i) w 0) (conv K (localContext i) w 1) a b d
    (conv K (localContext i) q 0) (conv K (localContext i) q 1)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem finalStep_eq (K : Constants C E) (i : C.Party) (Av Bv : ℕ → E) (V : E) (A B : C.Party → E)
    (hA : A i = Av 0) (hB : B i = Bv 0) :
    finalStep K (localContext i) (hybridCheckBuildingBlocks K i) (Av, Bv, V) = (do
      let w ← (hybridCheckBuildingBlocks K i).randElements 2
      let q ← (hybridCheckBuildingBlocks K i).extendMult (maskedProducts K A B i w.1)
      finalRest K i (A i) (B i) V w.1 q) := by
  simp only [finalStep, finalRest, finalAfterDigests, finalOpenProgram, maskedProducts]
  rw [hA, hB]
  refine bind_congr fun w => bind_congr fun q => bind_congr fun s => bind_congr fun _ =>
    bind_congr fun r => ?_
  apply StateT.ext
  intro s
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  rfl

variable {Ia : Type}

/-- The program of an honest operator after the masked multiplication of the randomization. -/
def finalMaskedProgram (K : Constants C E) (D : C.Coalition) (A B V : C.Party → E) (hs : C.Party → RunState C)
    (known : Shares C E) (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (w q : MaskTable C E) (i : C.Party) : PartyM C E (CheckSpec C E) Unit :=
  afterExtend K i 2 ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
    (finalRest K i (A i) (B i) (V i) (randShares D 2 known w i))
    (multFinish D 2 (filler K .peer) (fun g => extendTotal K D (maskedInputs K D known w A B) g + attack g)
      knownQ offset receivers q i)

/-- The randomization phase: both adaptive replies come before the two hidden tables. -/
theorem finalStep_masks (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (Av Bv : C.Party → ℕ → E) (V : C.Party → E) (hs : C.Party → RunState C) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) st
        (fun i => (finalStep K (localContext i) (hybridCheckBuildingBlocks K i) (Av i, Bv i, V i)).run'
            (hs i)))
      (do
        let p ← (leftAdversary (rightAdversary Ad)).answer st ()
        let p' ← (rightAdversary (leftAdversary Ad)).answer p.1
          (maskedView K D p.2.1 0 (fun j => Av j 0) (fun j => Bv j 0))
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel p'.1
          (finalMaskedProgram K D (fun j => Av j 0) (fun j => Bv j 0) V hs p.2.1 p'.2.1 p'.2.2.1 p'.2.2.2.1
            p'.2.2.2.2 w q)) := by
  have he : (fun i => (finalStep K (localContext i) (hybridCheckBuildingBlocks K i) (Av i, Bv i, V i)).run'
      (hs i)) =
      (fun i => (do
        let w ← (hybridCheckBuildingBlocks K i).randElements 2
        let q ← (hybridCheckBuildingBlocks K i).extendMult
          (maskedProducts K (fun j => Av j 0) (fun j => Bv j 0) i w.1)
        finalRest K i (Av i 0) (Bv i 0) (V i) w.1 q).run' (hs i)) := by
    funext i
    rw [finalStep_eq K i (Av i) (Bv i) (V i) (fun j => Av j 0) (fun j => Bv j 0) rfl rfl]
  rw [he]
  exact executePhase_finalMasks prims K D Ad fuel st (fun j => Av j 0) (fun j => Bv j 0) hs
    (fun i w q => finalRest K i (Av i 0) (Bv i 0) (V i) w q)

/-- The output share of the masked multiplication at an honest receiver. -/
def finalOut (K : Constants C E) (D : C.Coalition) (A B : C.Party → E) (known : Shares C E) (attack : ℕ → E)
    (knownQ : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party) (w q : MaskTable C E)
    (i : C.Party) : Shares C E :=
  (multFinish D 2 (filler K .peer) (maskedResult K D known attack w A B)
    knownQ offset receivers q i).getD (fun _ _ => 0)

/-- The running state after the masked multiplication. -/
def finalState (K : Constants C E) (hs : C.Party → RunState C) (z : C.Party → Shares C E) (i : C.Party) :
    RunState C :=
  ⟨recordHistory K i (hs i).history (z i) 2, (hs i).label + 1, (hs i).tag⟩

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma multFinish_honest (D : C.Coalition) (width : ℕ) (filled : C.Term → ℕ → Option C.Party)
    (result : ℕ → E) (known : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (fresh : C.Term → Fin width → E) (i : C.Party) (hi : i ∉ D.1) :
    multFinish D width filled result known offset receivers fresh i =
      if i ∈ receivers then some ((multFinish D width filled result known offset receivers fresh i).getD 0)
      else none := by
  by_cases hr : i ∈ receivers <;> simp [multFinish, hi, hr]

/-- A missing receiver of the masked multiplication stops the salts for everyone. -/
theorem finalMasked_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (A B V : C.Party → E) (hs : C.Party → RunState C)
    (known : Shares C E) (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (w q : MaskTable C E) (hmiss : ∃ i, i ∉ D.1 ∧ i ∉ receivers) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (finalMaskedProgram K D A B V hs known attack knownQ offset receivers w q) = pure (st, fun _ => none) := by
  rw [executePhase_congr_honest D Ad _ _ st _
    (fun i => if i ∈ receivers then
      ((hybridCheckBuildingBlocks K i).randBits 256 >>= fun salts => (do
        compareDigests (localContext i) salts.1
        finalAfterDigests K i (conv K (localContext i) (randShares D 2 known w i) 0)
          (conv K (localContext i) (randShares D 2 known w i) 1) (A i) (B i) (V i)
          (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 0)
          (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 1))).run'
        (finalState K (fun j => ⟨(hs j).history, (hs j).label + 1, (hs j).tag⟩)
          (finalOut K D A B known attack knownQ offset receivers w q) i)
      else failure)]
  · convert executePhase_randBits_missing K D Ad fuel st 256 _ (fun i => i ∈ receivers) _ hmiss using 4
  · intro i hi
    unfold finalMaskedProgram
    rw [multFinish_honest D 2 _ _ _ _ _ _ i hi]
    by_cases hr : i ∈ receivers
    · simp only [ite_eq_left hr, afterExtend, finalRest, finalOut, finalState]
      rfl
    · simp only [ite_eq_right hr, afterExtend]

/-! ### Generic reorderings -/

/-- A challenge phase with some live honest operators. -/
theorem executePhase_challenge_live {α : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C)
    (g : C.Party → E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (fun i => if live i then (challenge K (hybridCheckBuildingBlocks K i) >>= g i).run' (hs i) else
          failure) =
    if ∀ i, i ∉ D.1 → live i then (do
      let p ← runFunctionality localRoles D (leftAdversary (leftAdversary Ad)) (Fcoin (E := E)) st
        (fun i => if i ∈ D.1 then none else some 2)
      executePhase localRoles D Ad (checkFunctionalities K) fuel p.1
        (fun i => afterChallenge K (hs i) (g i) (p.2 i)))
    else pure (st, fun _ => none) := by
  split_ifs with hall
  · rw [executePhase_congr_honest D Ad _ _ st _ (fun i => (challenge K (hybridCheckBuildingBlocks K i) >>= g i).run' (hs i))
      (fun i hi => ite_eq_left (hall i hi))]
    exact executePhase_challenge K D Ad fuel st hs g
  · push Not at hall
    let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
        PartyM C E (CheckSpec C E) α := fun i o => match o with
      | some (.inl (.inl v)) => oracleStep (challengeQuery K (hs i).tag (hs i).label v) >>= fun r => match r with
          | some r => (g i r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
          | none => failure
      | _ => failure
    have hp : (fun i => if live i then (challenge K (hybridCheckBuildingBlocks K i) >>= g i).run' (hs i) else failure) =
        (fun i => optionalCall (if live i then some (.inl (.inl 2)) else none) (next i)) := by
      funext i
      by_cases hi : live i <;> simp only [hi, ite_true, ite_false, optionalCall, challenge_run', next]
      apply bind_congr
      intro o
      rcases o with _ | ((a | b) | (c | d)) <;> rfl
    rw [hp]
    apply executePhase_partialCall_abort
    · intro i hi; rfl
    · obtain ⟨i, hi, hl⟩ := hall
      exact ⟨i, hi, ite_eq_right hl⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
omit [Field E] [Algebra Bit E] in
lemma localStep_pure' {ι α : Type} {G : OracleSpec ι} (a : α) :
    (localStep (pure a : OracleComp (LocalSpec C) α) : PartyM C E G α) = pure a := by
  simp [localStep]

omit [Fintype E] [DecidableEq E] in
/-- After a common coin, the honest operators read one common challenge. -/
theorem executePhase_afterChallenge_common (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (Ad : CheckAdversary C E Ia) (fuel : ℕ) (st : Ad.State) (hs : C.Party → RunState C) (tg L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tg ∧ (hs i).label = L) (v : List E) (rec : Finset C.Party)
    (hrec : ∃ i, i ∉ D.1 ∧ i ∈ rec) (P : C.Party → E → PartyM C E (CheckSpec C E) Unit) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) fuel st
        (fun i => afterChallenge K (hs i) (fun r => StateT.lift (P i r))
          (if i ∉ D.1 ∧ i ∈ rec then some v else none)))
      (do
        let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel st
          (fun i => match r with
            | some r => if i ∈ rec then P i r else failure
            | none => failure)) := by
  let f : C.Party → Option E → PartyM C E (CheckSpec C E) Unit := fun i r =>
    if i ∉ D.1 ∧ i ∈ rec then (match r with
      | some r => P i r
      | none => failure) else failure
  let oa : C.Party → OracleComp (LocalSpec C) (Option E) := fun i =>
    if i ∉ D.1 ∧ i ∈ rec then liftComp (challengeQuery K tg L v) (LocalSpec C) else pure none
  have hp : (fun i => afterChallenge K (hs i) (fun r => StateT.lift (P i r))
      (if i ∉ D.1 ∧ i ∈ rec then some v else none)) = (fun i => localStep (oa i) >>= f i) := by
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ rec
    · simp only [hi, afterChallenge, oa, f, oracleStep, (htag i hi.1).1, (htag i hi.1).2]
      refine bind_congr fun r => ?_
      rcases r with _ | r
      · rfl
      · simp [StateT.run'_eq, StateT.run_lift]
    · simp only [hi, ite_false, afterChallenge, oa, f, localStep_pure', pure_bind]
  rw [hp]
  refine (executePhase_local_fallback prims D Ad _ fuel st oa (fun _ => none) f).trans ?_
  have hsel : SameRun prims (OverPermutation.sequenceFin (fun i => if i ∈ D.1 then pure none else oa i))
      (do let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
          pure (fun i => if i ∉ D.1 ∧ i ∈ rec then r else none)) := by
    convert sameRun_sequenceFin_selected prims (challengeQuery K tg L v) none
      (fun i => i ∉ D.1 ∧ i ∈ rec) hrec using 2
    · funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr, oa]
    · funext r
      congr 1
      funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr]
  refine (hsel.bind fun vs => SameRun.refl prims _).trans ?_
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro r
  apply SameRun.of_eq
  apply executePhase_congr_honest
  intro i hi
  by_cases hr : i ∈ rec
  · rcases r with _ | r <;> simp [f, hi, hr]
  · rcases r with _ | r <;> simp [f, hi, hr]

/-- The program of an honest operator after the digests. -/
def finalTail (K : Constants C E) (D : C.Coalition) (known knownQ : Shares C E) (attack : ℕ → E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (A B V : C.Party → E) (w q : MaskTable C E)
    (i : C.Party) : RunM C E (CheckSpec C E) Unit :=
  finalAfterDigests K i (maskShare K D known w 0 i) (maskShare K D known w 1 i) (A i) (B i) (V i)
    (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 0)
    (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 1)

/-- The running states after the masked multiplication, from the states before the randomization. -/
def finalHs (K : Constants C E) (hs : C.Party → RunState C) (z : C.Party → Shares C E) : C.Party → RunState C :=
  finalState K (fun j => ⟨(hs j).history, (hs j).label + 1, (hs j).tag⟩) z

omit [Fintype E] [DecidableEq E] in
/-- With every honest receiver, the masked multiplication leads into the salts. -/
theorem finalMasked_all (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (A B V : C.Party → E) (hs : C.Party → RunState C)
    (known : Shares C E) (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (w q : MaskTable C E) (hall : ∀ i, i ∉ D.1 → i ∈ receivers) :
    executePhase localRoles D Ad (checkFunctionalities K) fuel st
      (finalMaskedProgram K D A B V hs known attack knownQ offset receivers w q) =
    executePhase localRoles D Ad (checkFunctionalities K) fuel st
      (fun i => ((hybridCheckBuildingBlocks K i).randBits 256 >>= fun salts =>
        compareDigests (localContext i) salts.1 >>= fun _ =>
          finalTail K D known knownQ attack offset receivers A B V w q i).run'
        (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)) := by
  apply executePhase_congr_honest
  intro i hi
  unfold finalMaskedProgram
  rw [multFinish_honest D 2 _ _ _ _ _ _ i hi, ite_eq_left (hall i hi)]
  simp only [afterExtend, finalRest, finalTail, finalOut, finalHs, finalState, maskShare]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- After a common coin, the honest operators read one common challenge, for any continuation. -/
theorem executePhase_afterChallenge_common' {α : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (Ad : CheckAdversary C E Ia) (fuel : ℕ) (st : Ad.State) (hs : C.Party → RunState C) (tg L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tg ∧ (hs i).label = L) (v : List E) (rec : Finset C.Party)
    (hrec : ∃ i, i ∉ D.1 ∧ i ∈ rec) (g : C.Party → E → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) fuel st
        (fun i => afterChallenge K (hs i) (g i) (if i ∉ D.1 ∧ i ∈ rec then some v else none)))
      (do
        let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel st
          (fun i => match r with
            | some r => if i ∈ rec then (g i r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure
            | none => failure)) := by
  let f : C.Party → Option E → PartyM C E (CheckSpec C E) α := fun i r =>
    if i ∉ D.1 ∧ i ∈ rec then (match r with
      | some r => (g i r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
      | none => failure) else failure
  let oa : C.Party → OracleComp (LocalSpec C) (Option E) := fun i =>
    if i ∉ D.1 ∧ i ∈ rec then liftComp (challengeQuery K tg L v) (LocalSpec C) else pure none
  have hp : (fun i => afterChallenge K (hs i) (g i)
      (if i ∉ D.1 ∧ i ∈ rec then some v else none)) = (fun i => localStep (oa i) >>= f i) := by
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ rec
    · simp only [hi, afterChallenge, oa, f, oracleStep, (htag i hi.1).1, (htag i hi.1).2]
      refine bind_congr fun r => ?_
      rcases r with _ | r <;> rfl
    · simp only [hi, ite_false, afterChallenge, oa, f, localStep_pure', pure_bind]
  rw [hp]
  refine (executePhase_local_fallback prims D Ad _ fuel st oa (fun _ => none) f).trans ?_
  have hsel : SameRun prims (OverPermutation.sequenceFin (fun i => if i ∈ D.1 then pure none else oa i))
      (do let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
          pure (fun i => if i ∉ D.1 ∧ i ∈ rec then r else none)) := by
    convert sameRun_sequenceFin_selected prims (challengeQuery K tg L v) none
      (fun i => i ∉ D.1 ∧ i ∈ rec) hrec using 2
    · funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr, oa]
    · funext r
      congr 1
      funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr]
  refine (hsel.bind fun vs => SameRun.refl prims _).trans ?_
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro r
  apply SameRun.of_eq
  apply executePhase_congr_honest
  intro i hi
  by_cases hr : i ∈ rec
  · rcases r with _ | r <;> simp [f, hi, hr]
  · rcases r with _ | r <;> simp [f, hi, hr]

/-! ### The loops -/

/-- A multiplication phase with some live honest operators. -/
theorem executePhase_extend_live {α : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C)
    (products : C.Party → List (Product C E)) (f : C.Party → Shares C E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (fun i => if live i then ((hybridCheckBuildingBlocks K i).extendMult (products i) >>= f i).run' (hs i)
        else failure) =
    if ∀ i, i ∉ D.1 → live i then (do
      let p ← runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st
        (fun i => if i ∈ D.1 then none else some (products i))
      executePhase localRoles D Ad (checkFunctionalities K) fuel p.1
        (fun i => afterExtend K i (products i).length (hs i) (f i) (p.2 i)))
    else pure (st, fun _ => none) := by
  split_ifs with hall
  · rw [executePhase_congr_honest D Ad _ _ st _
      (fun i => ((hybridCheckBuildingBlocks K i).extendMult (products i) >>= f i).run' (hs i))
      (fun i hi => ite_eq_left (hall i hi))]
    exact executePhase_extend K D Ad fuel st products hs f
  · push Not at hall
    let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
        PartyM C E (CheckSpec C E) α := fun i o => match o with
      | some (.inl (.inr z)) =>
          (f i z).run' ⟨recordHistory K i (hs i).history z (products i).length, (hs i).label + 1, (hs i).tag⟩
      | _ => failure
    have hp :
        (fun i => if live i then ((hybridCheckBuildingBlocks K i).extendMult (products i) >>= f i).run' (hs i)
        else failure) =
        (fun i => optionalCall (if live i then some (.inl (.inr (products i))) else none) (next i)) := by
      funext i
      by_cases hi : live i <;> simp only [hi, ite_true, ite_false, optionalCall, extendMult_run', next]
      apply bind_congr
      intro o
      rcases o with _ | ((a | b) | (c | d)) <;> rfl
    rw [hp]
    apply executePhase_partialCall_abort
    · intro i hi; rfl
    · obtain ⟨i, hi, hl⟩ := hall
      exact ⟨i, hi, ite_eq_right hl⟩

omit [Fintype E] [DecidableEq E] in
/-- A missing honest operator at the masks of the randomization stops everyone. -/
theorem finalStep_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C)
    (Av Bv : C.Party → ℕ → E) (V : C.Party → E) (hmiss : ∃ i, i ∉ D.1 ∧ ¬ live i) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (fun i => if live i then
        (finalStep K (localContext i) (hybridCheckBuildingBlocks K i) (Av i, Bv i, V i)).run' (hs i) else
            failure) =
      pure (st, fun _ => none) := by
  let g : C.Party → PrssOutput C E → RunM C E (CheckSpec C E) Unit := fun i w => do
    let q ← (hybridCheckBuildingBlocks K i).extendMult
      (maskedProducts K (fun j => Av j 0) (fun j => Bv j 0) i w.1)
    finalRest K i (Av i 0) (Bv i 0) (V i) w.1 q
  let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) Unit := fun i o => match o with
    | some (.inr (.inl w)) => (g i w).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
    | _ => failure
  have hp : (fun i => if live i then
      (finalStep K (localContext i) (hybridCheckBuildingBlocks K i) (Av i, Bv i, V i)).run' (hs i) else
          failure) =
      (fun i => optionalCall (if live i then some (.inr (.inl 2)) else none) (next i)) := by
    funext i
    by_cases hi : live i
    · simp only [hi, ite_true, optionalCall]
      rw [finalStep_eq K i (Av i) (Bv i) (V i) (fun j => Av j 0) (fun j => Bv j 0) rfl rfl, randElements_run']
      apply bind_congr
      intro o
      rcases o with _ | ((a | b) | (c | d)) <;> rfl
    · simp only [hi, ite_false, optionalCall]
  rw [hp]
  apply executePhase_partialCall_abort
  · intro i hi; rfl
  · obtain ⟨i, hi, hl⟩ := hmiss
    exact ⟨i, hi, ite_eq_right hl⟩

/-- The rest of the check from halving step `j`, with `n` steps left. -/
def halvProg (K : Constants C E) (width n j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) :
    RunM C E (CheckSpec C E) Unit :=
  (List.range' j n).foldlM (halvingStep K (localContext i) (hybridCheckBuildingBlocks K i) width)
      (A, B, V) >>=
    finalStep K (localContext i) (hybridCheckBuildingBlocks K i)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma halvProg_zero (K : Constants C E) (width j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) :
    halvProg K width 0 j A B V i = finalStep K (localContext i) (hybridCheckBuildingBlocks K i)
        (A, B, V) := by
  simp [halvProg]

/-- The halving vectors after a step with challenge `r`. -/
def halvFold (len : ℕ) (r : E) (v : ℕ → E) : ℕ → E := fun k =>
  v k + r * (v k + (if k + halvedLength len < len then v (k + halvedLength len) else 0))

/-- The two inner products of a halving step. -/
def halvProducts (len : ℕ) (A B : ℕ → E) : List (Product C E) :=
  [.shamir A B (halvedLength len),
   .shamir (fun k => A k + (if k + halvedLength len < len then A (k + halvedLength len) else 0))
    (fun k => B k + (if k + halvedLength len < len then B (k + halvedLength len) else 0)) (halvedLength len)]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma halvProg_succ (K : Constants C E) (width n j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) :
    halvProg K width (n + 1) j A B V i = (do
      let p ← (hybridCheckBuildingBlocks K i).extendMult (halvProducts (halvedLength^[j] width) A B)
      let r ← challenge K (hybridCheckBuildingBlocks K i)
      halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r A) (halvFold (halvedLength^[j] width) r B)
        (conv K (localContext i) p 0 + (V + conv K (localContext i) p 1) * r + conv K (localContext i) p 1 * r ^ 2)
        i) := by
  simp only [halvProg, List.range'_succ, List.foldlM_cons, halvingStep, bind_assoc, pure_bind]
  rfl

/-- The inputs of the multiplication of a halving step. -/
def halvInputs (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) : C.Party → Option (List (Product C E)) :=
  fun i => if i ∈ D.1 then none else some (halvProducts len (A i) (B i))

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma halvInputs_width (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) :
    (firstInput (halvInputs D len A B)).length = 2 := by
  obtain ⟨j, _, hj⟩ := firstInput_honest D (fun i => halvProducts (C := C) len (A i) (B i))
  change (firstInput (fun i => if i ∈ D.1 then none else some (halvProducts len (A i) (B i)))).length = 2
  rw [hj]
  rfl

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma halvInputs_some (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) :
    ∀ i, i ∉ D.1 → (halvInputs D len A B i).isSome := by
  intro i hi; simp [halvInputs, hi]

/-- The rest of a halving step after its multiplication. -/
def halvNext (K : Constants C E) (width n j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) (p : Shares C E) :
    RunM C E (CheckSpec C E) Unit := do
  let r ← challenge K (hybridCheckBuildingBlocks K i)
  halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r A) (halvFold (halvedLength^[j] width) r B)
    (conv K (localContext i) p 0 + (V + conv K (localContext i) p 1) * r + conv K (localContext i) p 1 * r ^ 2) i

/-- The multiplication of a halving step, with every honest operator live. -/
theorem halvExtend_local (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hall : ∀ i, i ∉ D.1 → live i) (hs : C.Party → RunState C)
    (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
    (do
      let pa ← (rightAdversary (leftAdversary Ad)).answer st
        (extendView K D.1 (halvInputs D (halvedLength^[j] width) A B))
      let fresh ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
      executePhase localRoles D Ad (checkFunctionalities K) F pa.1
        (fun i => afterExtend K i 2 (hs i) (halvNext K width n j (A i) (B i) (V i) i)
          (multFinish D 2 (filler K .peer)
            (fun g => extendTotal K D (halvInputs D (halvedLength^[j] width) A B) g + pa.2.1 g)
            pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i))) := by
  have hp : (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
      (fun i => if live i then ((hybridCheckBuildingBlocks K i).extendMult (halvProducts (halvedLength^[j] width) (A i) (B i))
        >>= halvNext K width n j (A i) (B i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [halvProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs
    (fun i => halvProducts (halvedLength^[j] width) (A i) (B i)) (fun i => halvNext K width n j (A i) (B i) (V i) i),
    ite_eq_left hall]
  change (runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st
    (halvInputs D (halvedLength^[j] width) A B) >>= _) = _
  rw [runFunctionality_extend_local K D (rightAdversary (leftAdversary Ad)) st _ (halvInputs_some D _ A B)]
  have hw := halvInputs_width D (halvedLength^[j] width) A B
  generalize (firstInput (halvInputs D (halvedLength^[j] width) A B)).length = w at hw ⊢
  subst hw
  simp only [bind_assoc, pure_bind]
  rfl

/-- A missing honest operator at the multiplication of a halving step stops everyone. -/
theorem halvExtend_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hmiss : ¬ ∀ i, i ∉ D.1 → live i) (hs : C.Party → RunState C)
    (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
      pure (st, fun _ => none) := by
  have hp : (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
      (fun i => if live i then ((hybridCheckBuildingBlocks K i).extendMult (halvProducts (halvedLength^[j] width) (A i) (B i))
        >>= halvNext K width n j (A i) (B i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [halvProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs _ _, ite_eq_right hmiss]

/-- The output share of the multiplication of a halving step at an honest receiver. -/
def halvOut {σ' : Type} (K : Constants C E) (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E)
    (pa : σ' × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (i : C.Party) : Shares C E :=
  (multFinish D 2 (filler K .peer) (fun g => extendTotal K D (halvInputs D len A B) g + pa.2.1 g)
    pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i).getD 0

omit [Fintype E] [DecidableEq E] in
/-- The programs after the multiplication of a halving step. -/
lemma halvAfter_form (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F' : ℕ) (st : Ad.State)
    (hs : C.Party → RunState C) (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (fresh : C.Term → Fin 2 → E) :
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => afterExtend K i 2 (hs i) (halvNext K width n j (A i) (B i) (V i) i)
        (multFinish D 2 (filler K .peer)
          (fun g => extendTotal K D (halvInputs D (halvedLength^[j] width) A B) g + pa.2.1 g)
          pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i)) =
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => if i ∈ pa.2.2.2.2 then
        (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
          halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r (A i))
            (halvFold (halvedLength^[j] width) r (B i))
            (conv K (localContext i) (halvOut K D (halvedLength^[j] width) A B pa fresh i) 0 +
              (V i + conv K (localContext i) (halvOut K D (halvedLength^[j] width) A B pa fresh i) 1) * r +
              conv K (localContext i) (halvOut K D (halvedLength^[j] width) A B pa fresh i) 1 * r ^ 2) i).run'
          ⟨recordHistory K i (hs i).history (halvOut K D (halvedLength^[j] width) A B pa fresh i) 2,
            (hs i).label + 1, (hs i).tag⟩
        else failure) := by
  apply executePhase_congr_honest
  intro i hi
  rw [multFinish_honest D 2 _ _ _ _ _ _ i hi]
  by_cases hr : i ∈ pa.2.2.2.2
  · simp only [hr, ite_true, afterExtend, halvOut, halvNext]
  · simp only [hr, ite_false, afterExtend]

/-- The challenge continuation of a halving step. -/
def halvCont (K : Constants C E) (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E)
    (z : C.Party → Shares C E) (i : C.Party) (r : E) : RunM C E (CheckSpec C E) Unit :=
  halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r (A i)) (halvFold (halvedLength^[j] width) r (B i))
    (conv K (localContext i) (z i) 0 + (V i + conv K (localContext i) (z i) 1) * r +
      conv K (localContext i) (z i) 1 * r ^ 2) i

end Stages

end ThresholdLeanXmssSecurity

end

/-- info: 'ThresholdLeanXmssSecurity.executePhase_afterChallenge_common'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.executePhase_afterChallenge_common'
