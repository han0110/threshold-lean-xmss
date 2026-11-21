import ThresholdLeanXmssSecurity.Proof.CheckStages
import ThresholdLeanXmssSecurity.Proof.CheckSecurity

/-!
# The slice loop and the start of the check

The programs of the slice loop and of the start of the check at one operator, the runs of the start
phase (`executePhase_start`, `executePhase_afterStart_common`), and the program of the check after
its start (`checkProtocol_startProg`). The last lemmas read the tuples of the honest inputs
(`tupleAt_part`, `lifted_real_at`).
-/

noncomputable section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## The slice loop -/

section Slice

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField
variable {Ia : Type}

/-- The half length of slice step `j`. -/
def sliceHalf (count j : ℕ) : ℕ := sliceWidth count * 2 ^ (sliceBits - 1 - j)

/-- The slice coins below the folded bit, the weight of position `k` in slice step `j`. -/
def sliceRest (τ : List E) (count j k : ℕ) : E := coinProduct τ 0 (sliceBits - 1 - j) (k / sliceWidth count)

/-- The two inner products of slice step `j`. -/
def sliceProducts (τ : List E) (count j : ℕ) (xs ys : Shares C E) : List (Product C E) :=
  [.replicated (fun T k => sliceRest τ count j k * xs T k) ys (sliceHalf count j),
   .replicated (fun T k => sliceRest τ count j k * (xs T k + xs T (k + sliceHalf count j)))
    (fun T k => ys T k + ys T (k + sliceHalf count j)) (sliceHalf count j)]

/-- The vectors after slice step `j` with challenge `r`. -/
def sliceFold (count j : ℕ) (r : E) (v : Shares C E) : Shares C E := fun T k =>
  v T k + r * (v T k + v T (k + sliceHalf count j))

/-- The claim after slice step `j`. -/
def sliceClaim (τ : List E) (j : ℕ) (r V t0 tInf : E) : E :=
  (1 + r) * t0 + r * ((V + t0) / τ.getD (sliceBits - 1 - j) 0) + r * (1 + r) * tInf

/-- The rest of the check from slice step `j`, with `n` slice steps left. -/
def sliceProg (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party) :
    RunM C E (CheckSpec C E) Unit :=
  (List.range' j n).foldlM (sliceStep K (localContext i) (hybridCheckBuildingBlocks K i) τ count)
      (xs, ys, V) >>=
    fun p => halvProg K (sliceWidth count) (halvingSteps (sliceWidth count)) 0 (conv K (localContext i) p.1)
      (conv K (localContext i) p.2.1) p.2.2 i

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma sliceProg_zero (K : Constants C E) (τ : List E) (count j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party) :
    sliceProg K τ count 0 j xs ys V i = halvProg K (sliceWidth count) (halvingSteps (sliceWidth count)) 0
      (conv K (localContext i) xs) (conv K (localContext i) ys) V i := by
  simp [sliceProg]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma sliceProg_succ (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party) :
    sliceProg K τ count (n + 1) j xs ys V i = (do
      let t ← (hybridCheckBuildingBlocks K i).extendMult (sliceProducts τ count j xs ys)
      let r ← challenge K (hybridCheckBuildingBlocks K i)
      sliceProg K τ count n (j + 1) (sliceFold count j r xs) (sliceFold count j r ys)
        (sliceClaim τ j r V (conv K (localContext i) t 0) (conv K (localContext i) t 1)) i) := by
  simp only [sliceProg, List.range'_succ, List.foldlM_cons, sliceStep, bind_assoc, pure_bind]
  rfl

/-- The length of the vectors before slice step `j`. -/
def sliceLen (count j : ℕ) : ℕ := sliceWidth count * 2 ^ (sliceBits - j)

/-- The weight of position `k` before slice step `j`. -/
def sliceWeight (τ : List E) (count j k : ℕ) : E := coinProduct τ 0 (sliceBits - j) (k / sliceWidth count)

/-- The inputs of the multiplication of slice step `j`. -/
def sliceInputs (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E) :
    C.Party → Option (List (Product C E)) :=
  fun i => if i ∈ D.1 then none else some (sliceProducts τ count j (xs i) (ys i))

/-- The rest of a slice step after its multiplication. -/
def sliceNext (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party)
    (t : Shares C E) : RunM C E (CheckSpec C E) Unit := do
  let r ← challenge K (hybridCheckBuildingBlocks K i)
  sliceProg K τ count n (j + 1) (sliceFold count j r xs) (sliceFold count j r ys)
    (sliceClaim τ j r V (conv K (localContext i) t 0) (conv K (localContext i) t 1)) i

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma sliceInputs_width (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E) :
    (firstInput (sliceInputs D τ count j xs ys)).length = 2 := by
  obtain ⟨j', _, hj⟩ := firstInput_honest D (fun i => sliceProducts (C := C) τ count j (xs i) (ys i))
  change (firstInput (fun i => if i ∈ D.1 then none else some (sliceProducts τ count j (xs i) (ys i)))).length = 2
  rw [hj]
  rfl

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma sliceInputs_some (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E) :
    ∀ i, i ∉ D.1 → (sliceInputs D τ count j xs ys i).isSome := by
  intro i hi; simp [sliceInputs, hi]

/-- The multiplication of a slice step, with every honest operator live. -/
theorem sliceExtend_local (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hall : ∀ i, i ∉ D.1 → live i)
    (hs : C.Party → RunState C) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i) else failure) =
    (do
      let pa ← (rightAdversary (leftAdversary Ad)).answer st (extendView K D.1 (sliceInputs D τ count j xs ys))
      let fresh ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
      executePhase localRoles D Ad (checkFunctionalities K) F pa.1
        (fun i => afterExtend K i 2 (hs i) (sliceNext K τ count n j (xs i) (ys i) (V i) i)
          (multFinish D 2 (filler K .peer)
            (fun g => extendTotal K D (sliceInputs D τ count j xs ys) g + pa.2.1 g)
            pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i))) := by
  have hp : (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i)
      else failure) =
      (fun i => if live i then
          ((hybridCheckBuildingBlocks K i).extendMult (sliceProducts τ count j (xs i) (ys i))
        >>= sliceNext K τ count n j (xs i) (ys i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [sliceProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs
    (fun i => sliceProducts τ count j (xs i) (ys i)) (fun i => sliceNext K τ count n j (xs i) (ys i) (V i) i),
    ite_eq_left hall]
  change (runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st
    (sliceInputs D τ count j xs ys) >>= _) = _
  rw [runFunctionality_extend_local K D (rightAdversary (leftAdversary Ad)) st _ (sliceInputs_some D τ count j xs ys)]
  have hw := sliceInputs_width D τ count j xs ys
  generalize (firstInput (sliceInputs D τ count j xs ys)).length = w at hw ⊢
  subst hw
  simp only [bind_assoc, pure_bind]
  rfl

/-- A missing honest operator at the multiplication of a slice step stops everyone. -/
theorem sliceExtend_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hmiss : ¬ ∀ i, i ∉ D.1 → live i)
    (hs : C.Party → RunState C) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i) else failure) =
      pure (st, fun _ => none) := by
  have hp : (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i)
      else failure) =
      (fun i => if live i then
          ((hybridCheckBuildingBlocks K i).extendMult (sliceProducts τ count j (xs i) (ys i))
        >>= sliceNext K τ count n j (xs i) (ys i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [sliceProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs _ _, ite_eq_right hmiss]

/-- The output share of the multiplication of a slice step at an honest receiver. -/
def sliceOut {σ' : Type} (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E)
    (pa : σ' × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (i : C.Party) : Shares C E :=
  (multFinish D 2 (filler K .peer) (fun g => extendTotal K D (sliceInputs D τ count j xs ys) g + pa.2.1 g)
    pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i).getD 0

omit [Fintype E] [DecidableEq E] in
/-- The programs after the multiplication of a slice step. -/
lemma sliceAfter_form (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F' : ℕ) (st : Ad.State)
    (hs : C.Party → RunState C) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (fresh : C.Term → Fin 2 → E) :
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => afterExtend K i 2 (hs i) (sliceNext K τ count n j (xs i) (ys i) (V i) i)
        (multFinish D 2 (filler K .peer)
          (fun g => extendTotal K D (sliceInputs D τ count j xs ys) g + pa.2.1 g)
          pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i)) =
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => if i ∈ pa.2.2.2.2 then
        (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
          sliceProg K τ count n (j + 1) (sliceFold count j r (xs i)) (sliceFold count j r (ys i))
            (sliceClaim τ j r (V i) (conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 0)
              (conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 1)) i).run'
          ⟨recordHistory K i (hs i).history (sliceOut K D τ count j xs ys pa fresh i) 2,
            (hs i).label + 1, (hs i).tag⟩
        else failure) := by
  apply executePhase_congr_honest
  intro i hi
  rw [multFinish_honest D 2 _ _ _ _ _ _ i hi]
  by_cases hr : i ∈ pa.2.2.2.2
  · simp only [hr, ite_true, afterExtend, sliceOut, sliceNext]
  · simp only [hr, ite_false, afterExtend]

/-- The challenge continuation of a slice step. -/
def sliceCont (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E)
    (z : C.Party → Shares C E) (i : C.Party) (r : E) : RunM C E (CheckSpec C E) Unit :=
  sliceProg K τ count n (j + 1) (sliceFold count j r (xs i)) (sliceFold count j r (ys i))
    (sliceClaim τ j r (V i) (conv K (localContext i) (z i) 0) (conv K (localContext i) (z i) 1)) i

end Slice

/-! ## The start of the check -/

section Start

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField
variable {Ia : Type}

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The coin key of the first coin with the label `ρ` and its `d` expanded values. -/
def startQuery (K : Constants C E) (tag ρ : ℕ) (values : List E) (d : ℕ) : OracleComp (RoSpec C) (List E) :=
  hashQuery (.coinKey tag ρ (values.flatMap fun v => List.ofFn (K.encode v))) >>= fun key =>
    (List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand key k)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem start_run' {α : Type} (K : Constants C E) (i : C.Party) (d : ℕ) (f : List E → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((coinKey K (hybridCheckBuildingBlocks K i) >>= fun key => expand K key d) >>= f).run' st =
      call (Sum.inl (Sum.inl 2)) >>= fun o => match o with
        | some (.inl (.inl v)) => oracleStep (startQuery K st.tag st.label v d) >>= fun τ =>
            (f τ).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [coinKey, expand, bind_assoc, hybridCheckBuildingBlocks, freshLabel, startQuery, oracleStep_bind]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, StateT.run_get]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift]

/-- The program of an operator after the first coin. -/
def afterStart {α : Type} (K : Constants C E) (hs : RunState C) (d : ℕ) (f : List E → RunM C E (CheckSpec C E) α)
    (out : Option (List E)) : PartyM C E (CheckSpec C E) α :=
  match out with
  | some v => oracleStep (startQuery K hs.tag hs.label v d) >>= fun τ => (f τ).run' ⟨hs.history, hs.label + 1, hs.tag⟩
  | none => failure

theorem executePhase_start {α : Type} (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (hs : C.Party → RunState C) (d : ℕ) (f : C.Party → List E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
      (fun i => ((coinKey K (hybridCheckBuildingBlocks K i) >>= fun key => expand K key d) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (leftAdversary (leftAdversary A)) (Fcoin (E := E)) st
        (fun i => if i ∈ D.1 then none else some 2)
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterStart K (hs i) d (f i) (p.2 i))) := by
  simp_rw [start_run']
  rw [executePhase_call, runCheck_coin, bind_map_left]
  apply bind_congr
  intro p
  dsimp only
  congr 1
  funext i
  cases he : p.2 i <;> rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma startQuery_no_digest (K : Constants C E) (tg L : ℕ) (v : List E) (d : ℕ) :
    IsQueryBoundP (liftComp (startQuery K tg L v d) (LocalSpec C)) DigestQuery 0 := by
  simp only [startQuery, liftComp_bind]
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (hashQuery_no_digest _ (by simp [DigestQuery, digestSaltProjection])) fun key _ => ?_
  generalize List.range d = l
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_map]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => ?_
    · rw [map_eq_bind_pure_comp]
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (hashQuery_no_digest _ (by simp [DigestQuery, digestSaltProjection])) fun _ _ => by simp
    · exact isQueryBoundP_bind (n := 0) (m := 0) ih fun _ _ => by simp

omit [Fintype E] [DecidableEq E] in
/-- After a common coin, the honest operators read common expanded coins. -/
theorem executePhase_afterStart_common {α : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (Ad : CheckAdversary C E Ia) (fuel d : ℕ) (st : Ad.State) (hs : C.Party → RunState C) (tg L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tg ∧ (hs i).label = L) (v : List E) (rec : Finset C.Party)
    (hrec : ∃ i, i ∉ D.1 ∧ i ∈ rec) (g : C.Party → List E → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) fuel st
        (fun i => afterStart K (hs i) d (g i) (if i ∉ D.1 ∧ i ∈ rec then some v else none)))
      (do
        let τ ← liftComp (startQuery K tg L v d) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel st
          (fun i => if i ∈ rec then (g i τ).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure)) := by
  let f : C.Party → List E → PartyM C E (CheckSpec C E) α := fun i τ =>
    if i ∉ D.1 ∧ i ∈ rec then (g i τ).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure
  let oa : C.Party → OracleComp (LocalSpec C) (List E) := fun i =>
    if i ∉ D.1 ∧ i ∈ rec then liftComp (startQuery K tg L v d) (LocalSpec C) else pure []
  have hp : (fun i => afterStart K (hs i) d (g i)
      (if i ∉ D.1 ∧ i ∈ rec then some v else none)) = (fun i => localStep (oa i) >>= f i) := by
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ rec
    · simp only [hi, afterStart, oa, f, oracleStep, (htag i hi.1).1, (htag i hi.1).2]
      rfl
    · simp only [hi, ite_false, afterStart, oa, f, localStep_pure', pure_bind]
  rw [hp]
  refine (executePhase_local_fallback prims D Ad _ fuel st oa (fun _ => []) f).trans ?_
  have hsel : SameRun prims (OverPermutation.sequenceFin (fun i => if i ∈ D.1 then pure [] else oa i))
      (do let r ← liftComp (startQuery K tg L v d) (LocalSpec C)
          pure (fun i => if i ∉ D.1 ∧ i ∈ rec then r else [])) := by
    convert sameRun_sequenceFin_selected prims (startQuery K tg L v d) []
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
  by_cases hr : i ∈ rec <;> simp [f, hi, hr]

/-- The check from its first coin, on the lifted vectors `X`, `Y`, `Z`. -/
def startProg (K : Constants C E) (count : ℕ) (X Y Z : Shares C E) (i : C.Party) : RunM C E (CheckSpec C E) Unit :=
  (coinKey K (hybridCheckBuildingBlocks K i) >>= fun key => expand K key (coins count)) >>= fun τ =>
    StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0)) >>= fun _ =>
      sliceProg K τ count sliceBits 0 (fun T k => wordWeightOf K τ count k * X T k) Y
        (conv K (localContext i) (claimOf K τ count Z) 0) i

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem check_startProg (K : Constants C E) (i : C.Party) (tuples : List (Tuple C))
    (h : (tuples.map (·.count)).sum ≠ 0) :
    check K (localContext i) (hybridCheckBuildingBlocks K i) tuples =
      startProg K (tuples.map (·.count)).sum (liftedPart tuples (·.x)) (liftedPart tuples (·.y))
        (liftedPart tuples (·.z)) i := by
  rw [check_eq K (localContext i) (hybridCheckBuildingBlocks K i) tuples h]
  unfold startProg sliceProg halvProg
  simp only [bind_assoc]
  refine bind_congr fun key => bind_congr fun τ => bind_congr fun _ => ?_
  have hh : halvings (tuples.map (·.count)).sum - sliceBits = halvingSteps (sliceWidth (tuples.map (·.count)).sum) := by
    unfold halvings; omega
  rw [hh, List.range_eq_range', List.range_eq_range']

omit [Fintype E] [DecidableEq E] [SampleableType E] in
omit [Field E] [Algebra Bit E] in
lemma require_bind_run' {α : Type} (P : Prop) (f : Unit → RunM C E (CheckSpec C E) α) (s : RunState C) :
    (StateT.lift (require P) >>= f).run' s = if P then (f ()).run' s else failure := by
  unfold require
  split_ifs <;> simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift]

end Start

/-! ## The check from its start -/

section Couple

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma checkProtocol_startProg (K : Constants C E) (i : C.Party) (tuples : List (Tuple C)) (counts : List ℕ)
    (hc : tuples.map (·.count) = counts) (h : counts.sum ≠ 0) :
    checkProtocol K i tuples = (startProg K counts.sum (liftedPart tuples (·.x)) (liftedPart tuples (·.y))
      (liftedPart tuples (·.z)) i).run' ⟨filledHistory K i tuples, 0, 0⟩ := by
  unfold checkProtocol
  rw [check_startProg K i tuples (by rw [hc]; exact h), hc]

end Couple

/-! ## The initial histories -/

section InitHist

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The filled values of a term depend only on the modes and the vectors of `z` at the term. -/
lemma filledHistory_congr (K : Constants C E) (i : C.Party) (a b : List (Tuple C)) (T : C.Term)
    (h : a.map (fun τ => (τ.mode, vector τ.count (τ.z T))) = b.map (fun τ => (τ.mode, vector τ.count (τ.z T)))) :
    filledHistory K i a T = filledHistory K i b T := by
  unfold filledHistory
  split_ifs
  · let G : ReshareMode × List Bit → List Bit := fun p =>
      ((List.range p.2.length).filter fun g => (filler K p.1 T g).isSome).map fun g => p.2.getD g 0
    have hG : ∀ τ : Tuple C, ((List.range τ.count).filter fun g => (filler K τ.mode T g).isSome).map (τ.z T) =
        G (τ.mode, vector τ.count (τ.z T)) := by
      intro τ
      simp only [G, vector, List.length_map, List.length_range]
      refine List.map_congr_left fun g hg => ?_
      have hg' : g < τ.count := List.mem_range.mp (List.mem_filter.mp hg).1
      simp [hg']
    rw [List.flatMap_congr (fun τ _ => hG τ), List.flatMap_congr (fun τ _ => hG τ)]
    rw [← List.flatMap_map (f := fun τ : Tuple C => (τ.mode, vector τ.count (τ.z T))) (g := G),
      ← List.flatMap_map (f := fun τ : Tuple C => (τ.mode, vector τ.count (τ.z T))) (g := G), h]
  · rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma map_pair_eq {α β γ : Type} : ∀ (a b : List α) (f : α → β) (g : α → γ), a.map f = b.map f → a.map g = b.map g →
    a.map (fun t => (f t, g t)) = b.map (fun t => (f t, g t))
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | s :: a, t :: b, f, g, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
    exact ⟨Prod.ext h1.1 h2.1, map_pair_eq a b f g h1.2 h2.2⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A reconstruction from views that exist exactly at the honest operators reads an honest holder. -/
lemma reconstruct_honest {α : Type} [Inhabited α] (D : C.Coalition) (views : C.Party → Option (C.Term → α))
    (T : C.Term) (hc : ∀ i, i ∈ D.1 → views i = none) (hh : ∀ i, i ∉ D.1 → (views i).isSome) :
    ∃ j ∈ C.holders T, j ∉ D.1 ∧ ∃ f, views j = some f ∧ reconstruct views T = f T := by
  obtain ⟨i₀, hi₀T, hi₀D⟩ := exists_honest_holder D T
  unfold reconstruct
  rcases hl : (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) with _ | ⟨f, rest⟩
  · exfalso
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hh i₀ hi₀D)
    have : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) :=
      List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [hi₀T, hf]⟩
    rw [hl] at this
    simp at this
  · have hmem : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) := by
      rw [hl]; exact List.mem_cons_self
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hmem
    split_ifs at hi with hiT
    have hiD : i ∉ D.1 := fun h => by rw [hc i h] at hi; cases hi
    exact ⟨i, hiT, hiD, f, hi, by simp⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma tupleInputs_count_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (i : C.Party) (hi : i ∉ D.1) (m : ℕ) :
    (x i)[m]?.map (·.count) = counts[m]? := by
  rw [← List.getElem?_map, hx.1 i hi]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The count of a reconstructed tuple is the count of the honest inputs. -/
lemma tupleAt_count (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (m : ℕ) :
    (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count = counts.getD m 0 := by
  obtain ⟨j0, hj0, hf⟩ := firstInput_honest D x
  simp only [tupleAt, hf, tupleInputs_count_at K hx j0 hj0 m, List.getD_eq_getElem?_getD]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma firstInput_length (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) :
    (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length = counts.length := by
  obtain ⟨j0, hj0, hf⟩ := firstInput_honest D x
  rw [hf, ← List.length_map (f := (·.count)), hx.1 j0 hj0]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- Agreeing honest copies, tuple by tuple. -/
lemma agree_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (T : C.Term) (i j : C.Party) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (m g : ℕ) (hm : m < counts.length) (hg : g < counts.getD m 0) :
    (x i)[m]?.map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) = (x j)[m]?.map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) := by
  have hlen := firstInput_length K hx
  have h1 := hagree m (by rw [hlen]; exact hm) T i hiT j hjT hi hj g (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by rw [hlen]; exact hm)]
    simpa [tupleAt_count K hx m] using hg)
  simpa [hi, hj] using h1

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma liftedPart_flat (tuples : List (Tuple C)) (part : Tuple C → Shares C Bit) (T : C.Term) (k : ℕ) :
    liftedPart (E := E) tuples part T k = match flatPos (tuples.map (·.count)) k with
      | some (m, g) => (tuples[m]?.map fun τ => algebraMap Bit E (part τ T g)).getD 0
      | none => 0 :=
  getD_flatMap_vector_pos (fun τ g => algebraMap Bit E (part τ T g)) tuples k

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma getElem?_some_of_lt {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)} (K : Constants C E)
    (hx : TupleInputs K counts D x) (i : C.Party) (hi : i ∉ D.1) (m : ℕ) (hm : m < counts.length) :
    ∃ τ, (x i)[m]? = some τ ∧ τ.count = counts.getD m 0 := by
  have h := tupleInputs_count_at K hx i hi m
  rw [List.getElem?_eq_getElem hm] at h
  rcases hτ : (x i)[m]? with _ | τ
  · rw [hτ] at h; cases h
  · rw [hτ] at h
    refine ⟨τ, rfl, ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h
    rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A part of a reconstructed real tuple is the part of any honest holder. -/
lemma tupleAt_part (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z))
    (T : C.Term) (i : C.Party) (hiT : i ∈ C.holders T) (hi : i ∉ D.1) (m g : ℕ) (hm : m < counts.length)
    (hg : g < counts.getD m 0) :
    (x i)[m]?.map (fun τ => part τ T g) = some (part (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m) T g) := by
  have key : ∀ j, j ∈ C.holders T → j ∉ D.1 →
      (x i)[m]?.map (fun τ => part τ T g) = (x j)[m]?.map (fun τ => part τ T g) := by
    intro j hjT hj
    have e := agree_at K hx hagree T i j hiT hjT hi hj m g hm hg
    rcases hpart with rfl | rfl | rfl
    · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map Prod.fst) e
    · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map fun p => p.2.1) e
    · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map fun p => p.2.2) e
  have hviews : ∀ (sel : Tuple C → Shares C Bit),
      ∃ j ∈ C.holders T, j ∉ D.1 ∧ ∃ f, Option.map sel ((if j ∈ D.1 then none else some (x j)).bind (·[m]?))
        = some f ∧ reconstruct (fun i => Option.map sel ((if i ∈ D.1 then none else some (x i)).bind (·[m]?))) T
        = f T := fun sel =>
    reconstruct_honest D _ T (fun i hi => by simp [hi]) (fun i hi => by
      obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx i hi m hm
      simp [hi, hτ])
  rcases hpart with rfl | rfl | rfl
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := hviews (·.x)
    rw [key j hjT (by exact hj)]
    simp only [hj, ite_false, Option.bind_some] at hf
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [hτ] at hf ⊢
    simp only [Option.map_some, Option.some.injEq] at hf ⊢
    have e : (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x T = f T := hr
    rw [e, ← hf]
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := hviews (·.y)
    rw [key j hjT (by exact hj)]
    simp only [hj, ite_false, Option.bind_some] at hf
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [hτ] at hf ⊢
    simp only [Option.map_some, Option.some.injEq] at hf ⊢
    have e : (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y T = f T := hr
    rw [e, ← hf]
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := hviews (·.z)
    rw [key j hjT (by exact hj)]
    simp only [hj, ite_false, Option.bind_some] at hf
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [hτ] at hf ⊢
    simp only [Option.map_some, Option.some.injEq] at hf ⊢
    have e : (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z T = f T := hr
    rw [e, ← hf]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A lifted real part at an honest holder, position by position. -/
lemma lifted_real_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z))
    (T : C.Term) (i : C.Party) (hiT : i ∈ C.holders T) (hi : i ∉ D.1) (k : ℕ) :
    liftedPart (E := E) (x i) part T k = match flatPos counts k with
      | some (m, g) => algebraMap Bit E (part (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m) T g)
      | none => 0 := by
  rw [liftedPart_flat, hx.1 i hi]
  rcases hp : flatPos counts k with _ | ⟨m, g⟩
  · rfl
  · obtain ⟨hm, hg⟩ := flatPos_spec counts k m g hp
    have e := tupleAt_part K hx hagree part hpart T i hiT hi m g hm hg
    simp only
    rw [show (x i)[m]?.map (fun τ => algebraMap Bit E (part τ T g)) =
        ((x i)[m]?.map fun τ => part τ T g).map (algebraMap Bit E) by rw [Option.map_map]; rfl, e]
    rfl

end InitHist

end ThresholdLeanXmssSecurity

end

/-- info: 'ThresholdLeanXmssSecurity.checkProtocol_startProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.checkProtocol_startProg
