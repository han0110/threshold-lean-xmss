import ThresholdLeanXmssSecurity.Proof.BatchCheck.Programs
import ThresholdLeanXmssSecurity.Proof.BatchCheck.Wrapper

/-!
# The head of the check as a plan

`Plan` is the program text of the head of the check after the first coin, as data, and `runPlan` runs
it. The cuts of the route give the steps of the head with any building blocks (`runTimed_checkHeadOf`,
`headTimed`). `HeadSuffix` is the claim of `C1aStatement` from a position of the schedule. The block
hops of `Coin` and of `extendMult` from a full start (`coinHop`, `extendHop`) follow GS20, Lemmas 3 and
5. The file also holds one computation of `H` before a phase (`hoist`), the state after a call under
the wrappers of the head, and a new uniform row of a drawn table (`resample`).
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1r

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- The values of the head of the check, as `checkHeadOf` returns them. -/
abbrev HeadOut (C : Committee) (E : Type) := E × E × E × Shares C E × Shares C E

/-- The head of the check after the first coin. A step is one `extendMult` on `products` and one
challenge. The last node holds the elements `A`, `B` and the claim `V` of the masked multiplication. -/
inductive Plan (C : Committee) (E : Type) : Type
  | mask (A B : ℕ → E) (V : E)
  | step (products : List (Product C E)) (next : Shares C E → E → Plan C E)

/-- The plan has `d` steps, and each step has two products. -/
def PlanOK : Plan C E → ℕ → Prop
  | .mask _ _ _, d => d = 0
  | .step products next, d => products.length = 2 ∧ ∃ d', d = d' + 1 ∧ ∀ t r, PlanOK (next t r) d'

section Programs

variable [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}

/-- The randomization of the check up to its masked multiplication. It is the end of `checkHeadOf`. -/
def maskHeadOf (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G) (A B : ℕ → E) (V : E) :
    RunM C E G (HeadOut C E) := do
  let w ← bb.randElements 2
  let wa := conv K ctx w.1 0
  let wb := conv K ctx w.1 1
  let q ← bb.extendMult [.shamir (fun _ => wa) (fun _ => wb) 1,
    .shamir (fun _ => wa + A 0) (fun _ => wb + B 0) 1]
  pure (A 0, B 0, V, w.1, q)

/-- The run of a plan with the building blocks `bb`. -/
def runPlan (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G) :
    Plan C E → RunM C E G (HeadOut C E)
  | .mask A B V => maskHeadOf K ctx bb A B V
  | .step products next => bb.extendMult products >>= fun t => challenge K bb >>= fun r => runPlan K ctx bb (next t r)

/-- The plan of `n` halving steps from step `j`, as `halvingStep` gives them. -/
def halvPlan (K : Constants C E) (ctx : Context C) (width : ℕ) : ℕ → ℕ → (ℕ → E) × (ℕ → E) × E → Plan C E
  | 0, _, a => .mask a.1 a.2.1 a.2.2
  | n + 1, j, a =>
    let length := halvedLength^[j] width
    let half := halvedLength length
    let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
    let sum := fun (v : ℕ → E) k => v k + hi v k
    .step [.shamir a.1 a.2.1 half, .shamir (sum a.1) (sum a.2.1) half] fun p r =>
      halvPlan K ctx width n (j + 1) (fun k => a.1 k + r * (a.1 k + hi a.1 k),
        fun k => a.2.1 k + r * (a.2.1 k + hi a.2.1 k),
        conv K ctx p 0 + (a.2.2 + conv K ctx p 1) * r + conv K ctx p 1 * r ^ 2)

/-- The plan of `n` slice steps from step `j` and then of the halving steps, as `sliceStep` gives them. -/
def slicePlan (K : Constants C E) (ctx : Context C) (τ : List E) (count : ℕ) :
    ℕ → ℕ → Shares C E × Shares C E × E → Plan C E
  | 0, _, a => halvPlan K ctx (sliceWidth count) (halvingSteps (sliceWidth count)) 0
      (conv K ctx a.1, conv K ctx a.2.1, a.2.2)
  | n + 1, j, a =>
    let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
    let rest := fun k => coinProduct τ 0 (sliceBits - 1 - j) (k / sliceWidth count)
    .step [.replicated (fun T k => rest k * a.1 T k) a.2.1 half,
        .replicated (fun T k => rest k * (a.1 T k + a.1 T (k + half))) (fun T k => a.2.1 T k + a.2.1 T (k + half)) half]
      fun t r =>
        let t₀ := conv K ctx t 0
        let tInf := conv K ctx t 1
        let t₁ := (a.2.2 + t₀) / τ.getD (sliceBits - 1 - j) 0
        let fold := fun (v : Shares C E) T k => v T k + r * (v T k + v T (k + half))
        slicePlan K ctx τ count n (j + 1) (fold a.1, fold a.2.1, (1 + r) * t₀ + r * t₁ + r * (1 + r) * tInf)

/-- The plan of the head of the check of `tuples` with the coins `τ`. -/
def headPlan (K : Constants C E) (ctx : Context C) (τ : List E) (tuples : List (Tuple C)) : Plan C E :=
  slicePlan K ctx τ (tuples.map (·.count)).sum sliceBits 0
    ((fun T k => wordWeightOf K τ (tuples.map (·.count)).sum k * liftedPart tuples (·.x) T k : Shares C E),
      liftedPart tuples (·.y), conv K ctx (claimOf K τ (tuples.map (·.count)).sum (liftedPart tuples (·.z))) 0)

theorem planOK_halvPlan (K : Constants C E) (ctx : Context C) (width : ℕ) :
    ∀ n j a, PlanOK (halvPlan K ctx width n j a) n
  | 0, _, _ => rfl
  | n + 1, j, _ => ⟨rfl, n, rfl, fun _ _ => planOK_halvPlan K ctx width n (j + 1) _⟩

theorem planOK_slicePlan (K : Constants C E) (ctx : Context C) (τ : List E) (count : ℕ) :
    ∀ n j a, PlanOK (slicePlan K ctx τ count n j a) (n + halvingSteps (sliceWidth count))
  | 0, _, _ => by
    rw [Nat.zero_add]
    exact planOK_halvPlan K ctx _ _ _ _
  | n + 1, j, a => ⟨rfl, n + halvingSteps (sliceWidth count), by omega,
      fun _ _ => planOK_slicePlan K ctx τ count n (j + 1) _⟩

/-- The plan of the head has `halvings count` steps. -/
theorem planOK_headPlan (K : Constants C E) (ctx : Context C) (τ : List E) (tuples : List (Tuple C)) :
    PlanOK (headPlan K ctx τ tuples) (halvings (tuples.map (·.count)).sum) :=
  planOK_slicePlan K ctx τ _ sliceBits 0 _

theorem runPlan_halvPlan (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G) (width : ℕ) :
    ∀ n j a, ((List.range' j n).foldlM (halvingStep K ctx bb width) a >>= fun p =>
      maskHeadOf K ctx bb p.1 p.2.1 p.2.2) = runPlan K ctx bb (halvPlan K ctx width n j a)
  | 0, _, _ => by
    simp only [List.range'_zero, List.foldlM_nil, pure_bind, halvPlan, runPlan]
  | n + 1, j, a => by
    obtain ⟨A, B, V⟩ := a
    simp only [List.range'_succ, List.foldlM_cons, halvingStep, bind_assoc, pure_bind, halvPlan, runPlan]
    exact bind_congr fun p => bind_congr fun r => runPlan_halvPlan K ctx bb width n (j + 1) _

theorem runPlan_slicePlan (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G) (τ : List E)
    (count : ℕ) : ∀ n j a, ((List.range' j n).foldlM (sliceStep K ctx bb τ count) a >>= fun p =>
      (List.range' 0 (halvingSteps (sliceWidth count))).foldlM (halvingStep K ctx bb (sliceWidth count))
        (conv K ctx p.1, conv K ctx p.2.1, p.2.2) >>= fun p' => maskHeadOf K ctx bb p'.1 p'.2.1 p'.2.2) =
      runPlan K ctx bb (slicePlan K ctx τ count n j a)
  | 0, _, a => by
    simp only [List.range'_zero, List.foldlM_nil, pure_bind, slicePlan]
    exact runPlan_halvPlan K ctx bb _ _ 0 _
  | n + 1, j, a => by
    obtain ⟨xs, ys, V⟩ := a
    simp only [List.range'_succ, List.foldlM_cons, sliceStep, bind_assoc, pure_bind, slicePlan, runPlan]
    exact bind_congr fun t => bind_congr fun r => runPlan_slicePlan K ctx bb τ count n (j + 1) _

/-- The head of the check is its first coin, the coins `τ`, the test of the slice coins, and then the run
of `headPlan`. This ties each plan of the step statements to `check`. -/
theorem headPlan_eq (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G)
    (tuples : List (Tuple C)) :
    checkHeadOf K ctx bb tuples = (do
      let τ ← expand K (← coinKey K bb) (coins (tuples.map (·.count)).sum)
      StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
      runPlan K ctx bb (headPlan K ctx τ tuples)) := by
  have hR : halvings (tuples.map (·.count)).sum - sliceBits = halvingSteps (sliceWidth (tuples.map (·.count)).sum) := by
    unfold halvings
    omega
  simp only [checkHeadOf, headPlan, List.range_eq_range', hR]
  refine bind_congr fun key => bind_congr fun τ => bind_congr fun _ => ?_
  rw [← runPlan_slicePlan K ctx bb τ _ sliceBits 0 _]
  simp only [maskHeadOf]

end Programs

/-! ## The split of the tables -/

/-- The table with the rows below `n` from `T0` and the other rows from `T`. The salts are those of `T`. -/
def splice {m : ℕ} (n : ℕ) (T0 T : DrawTables C E m) : DrawTables C E m where
  freshE k := if k.val < n then T0.freshE k else T.freshE k
  freshPairE k := if k.val < n then T0.freshPairE k else T.freshPairE k
  freshB := T.freshB
  freshPairB := T.freshPairB

/-- The table `T` with the row `n` replaced. -/
def setRow {m : ℕ} (T : DrawTables C E m) (n : ℕ) (a : C.Term → Fin 2 → E) (b : C.Pair → Fin 2 → E) :
    DrawTables C E m where
  freshE k := if k.val = n then a else T.freshE k
  freshPairE k := if k.val = n then b else T.freshPairE k
  freshB := T.freshB
  freshPairB := T.freshPairB

/-- The table `T` with the salts replaced. -/
def setSalts {m : ℕ} (T : DrawTables C E m) (a : C.Term → Fin 256 → Bit) (b : C.Pair → Fin 256 → Bit) :
    DrawTables C E m where
  freshE := T.freshE
  freshPairE := T.freshPairE
  freshB := a
  freshPairB := b

theorem splice_zero {m : ℕ} (T0 T : DrawTables C E m) : splice 0 T0 T = T := by
  cases T
  simp [splice]

/-- A new row `n` of `T` is a row `n` of `T0`, with one more row of `T0` in use. -/
theorem splice_setRow {m : ℕ} (n : ℕ) (T0 T : DrawTables C E m) (a : C.Term → Fin 2 → E)
    (b : C.Pair → Fin 2 → E) : splice n T0 (setRow T n a b) = splice (n + 1) (setRow T0 n a b) T := by
  simp only [splice, setRow, DrawTables.mk.injEq, and_true]
  constructor <;> funext k <;> by_cases h : k.val = n <;> by_cases h' : k.val < n <;> simp [h, h'] <;> omega

section Resample

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- A drawn table with a new uniform row `n` is a drawn table. -/
def ResampleStatement (prims : Primitives) (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E]
    [Algebra Bit E] [SampleableType E] : Prop :=
  ∀ {m : ℕ} {α : Type} (n : ℕ) (G : DrawTables C E m → OracleComp (LocalSpec C) α),
    SameRun prims (drawTables (C := C) (E := E) m >>= G)
      (do
        let a ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
        let b ← liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C)
        let T ← drawTables (C := C) (E := E) m
        G (setRow T n a b))

/-- A drawn table with new uniform salts is a drawn table. -/
def ResampleBitsStatement (prims : Primitives) (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E]
    [Algebra Bit E] [SampleableType E] : Prop :=
  ∀ {m : ℕ} {α : Type} (G : DrawTables C E m → OracleComp (LocalSpec C) α),
    SameRun prims (drawTables (C := C) (E := E) m >>= G)
      (do
        let a ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        let b ← liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C)
        let T ← drawTables (C := C) (E := E) m
        G (setSalts T a b))

end Resample

end ThresholdLeanXmssSecurity.RealNetworkC1r

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1p

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

section Head

variable [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}

/-- The head of a check takes one step for the first coin, two steps for each slice or halving step,
the steps `e` of the draw of the mask, and one step for the masked multiplication. -/
theorem runTimed_checkHeadOf (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G) (e : ℕ)
    (hcoin : ∀ n, RunTimed 1 (bb.coin n)) (hextend : ∀ products, RunTimed 1 (bb.extendMult products))
    (helements : ∀ n, RunTimed e (bb.randElements n)) (tuples : List (Tuple C)) :
    RunTimed (2 * halvings (tuples.map (·.count)).sum + 2 + e) (checkHeadOf K ctx bb tuples) := by
  have hlab : 2 * halvings (tuples.map (·.count)).sum + 2 + e =
      1 + (0 + (0 + ((List.range sliceBits).length * 2 +
        ((List.range (halvings (tuples.map (·.count)).sum - sliceBits)).length * 2 + (e + (1 + 0)))))) := by
    rw [List.length_range, List.length_range, halvings]
    omega
  rw [hlab]
  unfold checkHeadOf
  refine (runTimed_coinKey K bb hcoin).bind fun key => ?_
  refine (runTimed_expand K key _).bind fun τ => ?_
  refine (RunTimed.lift (timed_require _)).bind fun _ => ?_
  refine (RunTimed.foldlM _ (runTimed_sliceStep K ctx bb hcoin hextend τ _) _ _).bind fun p => ?_
  refine (RunTimed.foldlM _ (runTimed_halvingStep K ctx bb hcoin hextend _) _ _).bind fun p' => ?_
  refine (helements 2).bind fun w => ?_
  exact (hextend _).bind fun q => runTimed_pure _

/-- A call of `F_coin` in the hybrid model takes one step. -/
theorem runTimed_hybridCoin (K : Constants C E) (i : C.Party) (n : ℕ) :
    RunTimed 1 ((hybridCheckBuildingBlocks K i).coin n) := by
  refine RunTimed.bind (m := 0) (n := 1) runTimed_freshLabel fun _ st => ?_
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  refine Timed.call_bind 0 _ _ fun r => ?_
  rw [pure_bind]
  dsimp only
  split <;> first | exact runTimed_pure _ _ | exact RunTimed.lift (timed_failure 0) _

/-- A call of `F_extendMult` in the hybrid model takes one step. -/
theorem runTimed_hybridExtendMult (K : Constants C E) (i : C.Party) (products : List (Product C E)) :
    RunTimed 1 ((hybridCheckBuildingBlocks K i).extendMult products) := by
  refine RunTimed.bind (m := 0) (n := 1) runTimed_freshLabel fun _ st => ?_
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  refine Timed.call_bind 0 _ _ fun r => ?_
  rw [pure_bind]
  dsimp only
  split
  · exact RunTimed.bind (m := 0) (n := 0) (runTimed_record K _ _ _ _ _) (fun _ => runTimed_pure _) _
  · exact RunTimed.lift (timed_failure 0) _

/-- A call of `F_rand` in the hybrid model takes one step. -/
theorem runTimed_hybridRandElements (K : Constants C E) (i : C.Party) (n : ℕ) :
    RunTimed 1 ((hybridCheckBuildingBlocks K i).randElements n) := by
  refine RunTimed.bind (m := 0) (n := 1) runTimed_freshLabel fun _ st => ?_
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  refine Timed.call_bind 0 _ _ fun r => ?_
  rw [pure_bind]
  dsimp only
  split <;> first | exact runTimed_pure _ _ | exact RunTimed.lift (timed_failure 0) _

end Head

section Statements

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The head in the hybrid model takes `2 * R + 3` calls. -/
theorem headTimed (K : Constants C E) : HeadTimedStatement K := by
  intro L tg i tuples _
  rw [checkHead_eq]
  exact runTimed_checkHeadOf K _ _ 1 (runTimed_hybridCoin K i) (runTimed_hybridExtendMult K i)
    (runTimed_hybridRandElements K i) tuples _

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The head of operator `i` with a tuple of the public counts takes `2 * R + 3` calls. -/
theorem headAt_timed (K : Constants C E) (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C))
    (i : C.Party) (hsum : counts.sum ≠ 0) (hx : (x i).map (·.count) = counts) :
    Timed (2 * halvings counts.sum + 3) (headAt K L tg x i).run := by
  have h := headTimed K L tg i (x i) (by rw [hx]; exact hsum)
  rw [hx] at h
  exact h

omit [Fintype E] [DecidableEq E] in
/-- The check in the hybrid model is its head and then its rest. -/
theorem hybridCut (prims : Primitives) (K : Constants C E) (D : C.Coalition) : HybridCutStatement prims K D := by
  intro Ia A counts L tg x st hsum hx
  have hprog : executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st (checkAt K L tg x) =
      executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
        (fun i => headAt K L tg x i >>= restAt K i) := by
    refine executePhase_congr D A _ _ st _ _ fun i hi => ?_
    unfold checkAt headAt restAt
    rw [check_head_rest K i (x i) (by rw [hx i hi]; exact hsum)]
    simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  rw [hprog, show checkRounds counts.sum = (2 * halvings counts.sum + 3) + 5 by unfold checkRounds; omega]
  exact executePhase_bind prims D A _ _ _ st _ _ fun i hi => headAt_timed K counts L tg x i hsum (hx i hi)

section Drawn

variable {m : ℕ} (K : Constants C E) (D : C.Coalition) (L : ℕ)
  (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : DrawTables C E m) (i : C.Party)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real `Coin` on a drawn value takes one round. -/
theorem runTimed_drawnCoin (n : ℕ) : RunTimed 1 ((drawnCheckBuildingBlocks K D L knownE knownB tables i).coin n) := by
  refine RunTimed.bind (m := 0) (n := 1) runTimed_freshLabel fun _ => ?_
  unfold coinWith
  exact RunTimed.bind (m := 1) (n := 0) (RunTimed.lift (timed_openSh K _ _ n)) fun _ => runTimed_pure _

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real `extendMult` on a drawn value takes one round. -/
theorem runTimed_drawnExtendMult (products : List (Product C E)) :
    RunTimed 1 ((drawnCheckBuildingBlocks K D L knownE knownB tables i).extendMult products) :=
  RunTimed.bind (m := 0) (n := 1) runTimed_freshLabel fun _ => runTimed_reshare K _ _ _ _ _

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The draw of the mask is local. -/
theorem runTimed_drawnRandElements (n : ℕ) :
    RunTimed 0 ((drawnCheckBuildingBlocks K D L knownE knownB tables i).randElements n) :=
  RunTimed.bind (m := 0) (n := 0) runTimed_freshLabel fun _ => runTimed_pure _

end Drawn

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The head of the real check on drawn values takes `2 * R + 2` rounds. -/
theorem realHeadTimed (K : Constants C E) (D : C.Coalition) : RealHeadTimedStatement K D := by
  intro m L tg knownE knownB tables x i _
  exact runTimed_checkHeadOf K _ _ 0 (runTimed_drawnCoin K D L knownE knownB tables i)
    (runTimed_drawnExtendMult K D L knownE knownB tables i) (runTimed_drawnRandElements K D L knownE knownB tables i)
    (x i) _

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real check on drawn values is its head and then its rest. -/
theorem realCut (prims : Primitives) (K : Constants C E) (D : C.Coalition) : RealCutStatement prims K D := by
  intro Ia W knownE knownB counts L tg tables x st hsum hx
  have hprog : executePhase localRoles D W noFunctionality (checkRounds counts.sum) st
        (drawnCheckAt K D L tg knownE knownB tables x) =
      executePhase localRoles D W noFunctionality (checkRounds counts.sum) st
        (fun i => drawnHeadAt K D L tg knownE knownB tables x i >>= drawnRestAt K D L knownE knownB tables i) := by
    refine executePhase_congr D W _ _ st _ _ fun i hi => ?_
    unfold drawnCheckAt drawnHeadAt drawnRestAt
    rw [check_headOf_restOf K _ _ (x i) (by rw [hx i hi]; exact hsum)]
    simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  rw [hprog, show checkRounds counts.sum = (2 * halvings counts.sum + 2) + 6 by unfold checkRounds; omega]
  refine executePhase_bind prims D W _ _ _ st _ _ fun i hi => ?_
  have h := realHeadTimed K D L tg knownE knownB tables x i (by rw [hx i hi]; exact hsum)
  rw [hx i hi] at h
  exact h

omit [Fintype E] in
/-- With no tuple, the real check on drawn values and the check under the wrapper are `pure`. The
draw of the tables is not used. -/
theorem c1Zero (prims : Primitives) (K : Constants C E) (D : C.Coalition) : C1ZeroStatement prims K D := by
  intro Ia W knownE knownB counts L tg x st hsum hx
  have hreal : ∀ tables : DrawTables C E (RealNetworkV3.checkLabels counts.sum),
      executePhase localRoles D W noFunctionality (checkRounds counts.sum) st
        (drawnCheckAt K D L tg knownE knownB tables x) =
      pure (st, fun i => if i ∈ D.1 then none else some ()) := fun tables => by
    rw [← executePhase_pure D W noFunctionality (checkRounds counts.sum) st ()]
    refine executePhase_congr D W _ _ st _ _ fun i hi => ?_
    unfold drawnCheckAt
    rw [check_of_count_eq_zero K _ _ (x i) (by rw [hx i hi]; exact hsum)]
    simp only [StateT.run'_eq, StateT.run_pure, map_pure]
  have hhybrid : c1Hybrid K D W knownE knownB c1Names counts L tg x st =
      pure (st, fun i => if i ∈ D.1 then none else some ()) := by
    unfold c1Hybrid
    rw [executePhase_congr D _ _ _ _ _ (fun _ => pure ()) fun i hi => ?_, executePhase_pure, map_pure]
    unfold checkAt
    rw [check_of_count_eq_zero K _ _ (x i) (by rw [hx i hi]; exact hsum)]
    simp only [StateT.run'_eq, StateT.run_pure, map_pure]
  unfold c1Real drawTables
  simp only [hreal, hhybrid, bind_assoc, pure_bind]
  intro s
  simp only [simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left]
  exact (OracleComp.EvalDistEq.bind_const _ _).trans ((OracleComp.EvalDistEq.bind_const _ _).trans
    ((OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)))

end Statements

end ThresholdLeanXmssSecurity.RealNetworkC1p

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1r

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

section OpenTail

variable [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}

/-- The end of the check after its last challenge `r`, from the values `v` of the head. -/
def openTailOf (K : Constants C E) (ctx : Context C) (v : HeadOut C E) (r : E) : RunM C E G Unit := do
  let wa := conv K ctx v.2.2.2.1 0
  let wb := conv K ctx v.2.2.2.1 1
  let q₀ := conv K ctx v.2.2.2.2 0
  let q₂ := conv K ctx v.2.2.2.2 1
  let opened ← StateT.lift (openSh K ctx (fun k => match k with
    | 0 => wa + r * (wa + v.1)
    | 1 => wb + r * (wb + v.2.1)
    | _ => q₀ + (v.2.2.1 + q₀ + q₂) * r + q₂ * r ^ 2) 3)
  StateT.lift (require (opened 0 * opened 1 = opened 2))

/-- The rest of the check is the salts, the digest round, the last challenge and `openTailOf`. -/
theorem checkRestOf_eq (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G)
    (v : HeadOut C E) :
    checkRestOf K ctx bb v = bb.randBits 256 >>= fun salts => compareDigests ctx salts.1 >>= fun _ =>
      challenge K bb >>= fun r => openTailOf K ctx v r := rfl

end OpenTail

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## The runs and the claims at a position -/

section Runs

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
  (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- The rest of the real check on the table `T`, from the output of its head. -/
def realRest (T : DrawTables C E (RealNetworkV3.checkLabels count))
    (r : W.State × (C.Party → Option (HeadOut C E × RunState C))) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  executePhase localRoles D W noFunctionality 6 r.1
    (fun i => (r.2 i).elim failure (drawnRestAt K D L knownE knownB T i))

/-- The part of `c1Mid` after the head. After a partial output the live operators run the real digest
round on drawn salts. After each other output the rest of the check runs under the wrapper. -/
def midRest (r : (c1WrapperWith K D W knownE knownB count hist names
      (c1HeadTails K D W knownE knownB count L tg)).State × (C.Party → Option (HeadOut C E × RunState C))) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  if PartialOut D r.2 then do
    let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
    RealNetworkRC.realDigestPhase D W noFunctionality 1 r.1.1.1 (digestSalts D knownB table)
      (fun i => (r.2 i).map Prod.snd) (fun _ _ => (pure () : RunM C E RealSpec Unit))
  else
    (fun r' => (r'.1.1.1, r'.2)) <$> executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
      (checkFunctionalities K) 5 r.1 (fun i => (r.2 i).elim failure (restAt K i))

/-- The claim of `C1aStatement` from position `n`, for the continuations `kR` and `kH` of the head over
the data `b`. Each honest operator starts. Its label is `L + n` and its tag is `tg`. The real side has
`fR` steps of fuel and the other side has `fH`. -/
def HeadSuffix (n fR fH : ℕ) {β : Type} (Rel : (C.Party → β) → Prop)
    (kR : DrawTables C E (RealNetworkV3.checkLabels count) → C.Party → β → RunM C E RealSpec (HeadOut C E))
    (kH : C.Party → β → RunM C E (CheckSpec C E) (HeadOut C E)) : Prop :=
  ∀ (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E) (b : C.Party → β)
    (hs : C.Party → RunState C), Rel b → (∀ i, i ∉ D.1 → (hs i).label = L + n ∧ (hs i).tag = tg) →
    SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality fR st (fun i => (kR (splice n T0 T) i (b i)).run (hs i)) >>=
          realRest K D W knownE knownB count L (splice n T0 T))
      (executePhase localRoles D
          (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
          (checkFunctionalities K) fH ((st, mem), n) (fun i => (kH i (b i)).run (hs i)) >>=
        midRest K D W knownE knownB names count L tg hist)

/-- The claim before the `extendMult` of step `j`, with `d` steps to run. The position is `2 * j + 1`. -/
def PlanSuffix (j d : ℕ) : Prop :=
  HeadSuffix prims K D W knownE knownB names count L tg hist (2 * j + 1) (2 * d + 1) (2 * d + 2)
    (fun p : C.Party → Plan C E => ∀ i, i ∉ D.1 → PlanOK (p i) d)
    (fun T i p => runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) p)
    (fun i p => runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p)

/-- The claim before the coin of the challenge of step `j`, with `d` steps after it. The position is
`2 * j + 2`. -/
def CoinSuffix (j d : ℕ) : Prop :=
  HeadSuffix prims K D W knownE knownB names count L tg hist (2 * j + 2) (2 * d + 2) (2 * d + 3)
    (fun next : C.Party → E → Plan C E => ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d)
    (fun T i next => challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
      runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (next r))
    (fun i next => challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
      runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next r))

/-- The claim before the first coin. The position is 0. -/
def StartSuffix : Prop :=
  HeadSuffix prims K D W knownE knownB names count L tg hist 0 (2 * halvings count + 2) (2 * halvings count + 3)
    (fun next : C.Party → List E → Plan C E => ∀ i, i ∉ D.1 → ∀ τ, PlanOK (next i τ) (halvings count))
    (fun T i next => do
      let τ ← expand K (← coinKey K (drawnCheckBuildingBlocks K D L knownE knownB T i)) (coins count)
      StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
      runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) (next τ))
    (fun i next => do
      let τ ← expand K (← coinKey K (hybridCheckBuildingBlocks K i)) (coins count)
      StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
      runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next τ))

/-- The claim of `C1aStatement` for the rest of the check from position `n`, after a full output of the
head. The other side is the rest under the wrapper with `c1Tails`. -/
def RestSuffix (n fR fH : ℕ) {β : Type}
    (kR : DrawTables C E (RealNetworkV3.checkLabels count) → C.Party → β → RunM C E RealSpec Unit)
    (kH : C.Party → β → RunM C E (CheckSpec C E) Unit) : Prop :=
  ∀ (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State) (mem : C1Memory C E) (b : C.Party → β)
    (hs : C.Party → RunState C), (∀ i, i ∉ D.1 → (hs i).label = L + n ∧ (hs i).tag = tg) →
    SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        executePhase localRoles D W noFunctionality fR st (fun i => (kR (splice n T0 T) i (b i)).run' (hs i)))
      ((fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) fH ((st, mem), n) (fun i => (kH i (b i)).run' (hs i)))

/-- The rest of the check from the salts of the digests. The position is `2 * R + 3`. -/
def RestFull : Prop :=
  RestSuffix prims K D W knownE knownB names count L tg hist (2 * halvings count + 3) 6 5
    (fun T i (v : HeadOut C E) => checkRestOf K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i) v)
    (fun i v => checkRest K i v)

/-- The rest of the check from the digest round, with the salts `z.1` of each operator. The position is
`2 * R + 4`. -/
def DigestSuffix : Prop :=
  RestSuffix prims K D W knownE knownB names count L tg hist (2 * halvings count + 4) 6 4
    (fun T i (z : PrssOutput C Bit × HeadOut C E) => compareDigests (localContext i) z.1.1 >>= fun _ =>
      challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r => openTailOf K (localContext i) z.2 r)
    (fun i z => compareDigests (localContext i) z.1.1 >>= fun _ =>
      challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) z.2 r)

/-- The rest of the check from its last challenge. The position is `2 * R + 4`. -/
def ChallengeSuffix : Prop :=
  RestSuffix prims K D W knownE knownB names count L tg hist (2 * halvings count + 4) 5 3
    (fun T i (v : HeadOut C E) => challenge K (drawnCheckBuildingBlocks K D L knownE knownB T i) >>= fun r =>
      openTailOf K (localContext i) v r)
    (fun i v => challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) v r)

/-- The rest of the real check after a partial output `o` of the head is the real digest round on drawn
salts. The live operators send their digests, the adversary gets one step, and each operator aborts. -/
def RestPartial : Prop :=
  ∀ (T0 : DrawTables C E (RealNetworkV3.checkLabels count)) (st : W.State)
    (o : C.Party → Option (HeadOut C E × RunState C)), PartialOut D o →
    SameRun prims
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels count) >>= fun T =>
        realRest K D W knownE knownB count L (splice (2 * halvings count + 3) T0 T) (st, o))
      (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        RealNetworkRC.realDigestPhase D W noFunctionality 1 st (digestSalts D knownB table)
          (fun i => (o i).map Prod.snd) (fun _ _ => (pure () : RunM C E RealSpec Unit)))

/-- The round of `OpenSh` after the last challenge, from the outputs `o` of the last coin and its search.
A round under the wrapper at a position other than the digest round is a round of `W`. The outputs `o` can
be a partial abort, because the last coin has no tail. -/
def OpenRound : Prop :=
  ∀ (st : W.State) (mem : C1Memory C E) (k : ℕ) (o : C.Party → Option (HeadOut C E × E × RunState C)),
    k ≠ 2 * halvings count + 4 →
    SameRun prims
      (executePhase localRoles D W noFunctionality 4 st fun i =>
        (o i).elim failure fun z => (openTailOf (G := RealSpec) K (localContext i) z.1 z.2.1).run' z.2.2)
      ((fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) 2 ((st, mem), k) fun i =>
          (o i).elim failure fun z => (openTailOf (G := CheckSpec C E) K (localContext i) z.1 z.2.1).run' z.2.2)

end Runs

/-! ## The block statements -/

/-- The masked multiplication. Before it the real side draws the mask from row `2 * R + 1`, and the other
side calls `F_rand`. The reply to `F_extendMult` at `2 * R + 2` has no tail under `c1HeadTails`. A full
output goes to `RestFull`, and a partial output goes to `RestPartial`. -/
def MaskBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      RestFull prims K D W knownE knownB names count L tg hist →
      RestPartial prims K D W knownE knownB count L →
      PlanSuffix prims K D W knownE knownB names count L tg hist (halvings count) 0

/-- The `extendMult` of step `j`, at position `2 * j + 1`. After a partial reply the tail is `coinTail`
with the stream `2 * j + 2`. -/
def ExtendBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit) (j d : ℕ), j + d + 1 = halvings count →
      CoinSuffix prims K D W knownE knownB names count L tg hist j d →
      PlanSuffix prims K D W knownE knownB names count L tg hist j (d + 1)

/-- A challenge in the middle. The coin of step `j` at position `2 * j + 2`, with a step after it.
After a partial reply the tail is the search and `reshareTail` with the stream `2 * j + 3`. -/
def CoinBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit) (j d : ℕ), j + 1 + (d + 1) = halvings count →
      PlanSuffix prims K D W knownE knownB names count L tg hist (j + 1) (d + 1) →
      CoinSuffix prims K D W knownE knownB names count L tg hist j (d + 1)

/-- The last challenge. The coin of the last step at position `2 * R`. The next block draws the mask
and then runs the masked multiplication. After a partial reply the tail is the search and `reshareTail`
with the stream `2 * R + 2`. -/
def LastCoinBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit) (j : ℕ), j + 1 = halvings count →
      PlanSuffix prims K D W knownE knownB names count L tg hist (j + 1) 0 →
      CoinSuffix prims K D W knownE knownB names count L tg hist j 0

/-- The first coin, at position 0. After a partial reply the tail is `startQuery`, the test of the
slice coins and `reshareTail` with the stream 1. -/
def FirstCoinBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      PlanSuffix prims K D W knownE knownB names count L tg hist 0 (halvings count) →
      StartSuffix prims K D W knownE knownB names count L tg hist

/-- The salts. The real side reads them from the drawn table, and the other side calls `F_rand` at
position `2 * R + 3`. The reply to `F_rand` is not partial. -/
def RandBitsBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      DigestSuffix prims K D W knownE knownB names count L tg hist →
      RestFull prims K D W knownE knownB names count L tg hist

/-- The digest round from a full start. After a partial round the survivors play the round
of the last coin, which is the tail `c1Rtails` at position `2 * R + 4` with the stream `2 * R + 4`. -/
def DigestBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      ChallengeSuffix prims K D W knownE knownB names count L tg hist →
      DigestSuffix prims K D W knownE knownB names count L tg hist

/-- The last coin, at position `2 * R + 4`. Its reply has no tail, because the next block is the round
of `OpenSh` in both models. -/
def FinalCoinBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      OpenRound prims K D W knownE knownB names count L tg hist →
      ChallengeSuffix prims K D W knownE knownB names count L tg hist

/-- The round of `OpenSh` under the wrapper. -/
def OpenRoundStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit), OpenRound prims K D W knownE knownB names count L tg hist

/-- The rest of the real check after a partial output of the head. -/
def RestPartialStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L : ℕ),
    RestPartial prims K D W knownE knownB count L

/-! ## The block statements give `C1aStatement` -/

/-- The table with zeros. It fills the rows that `splice 0` does not read. -/
def zeroTables (m : ℕ) : DrawTables C E m := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

omit [Fintype E] in
/-- The block statements give `C1aStatement`. -/
theorem c1a_of_steps (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (hmask : MaskBlockStatement prims K D) (hextend : ExtendBlockStatement prims K D)
    (hcoin : CoinBlockStatement prims K D) (hlast : LastCoinBlockStatement prims K D)
    (hfirst : FirstCoinBlockStatement prims K D) (hbits : RandBitsBlockStatement prims K D)
    (hdigest : DigestBlockStatement prims K D) (hfinal : FinalCoinBlockStatement prims K D)
    (hopen : OpenRoundStatement prims K D) (hpartial : RestPartialStatement prims K D) :
    C1aStatement prims K D := by
  intro Ia W knownE knownB names hn counts L tg x st hpos hx
  have hrest : RestFull prims K D W knownE knownB names counts.sum L tg (knownHist K D x) :=
    hbits W knownE knownB names hn _ L tg _ (hdigest W knownE knownB names hn _ L tg _
      (hfinal W knownE knownB names hn _ L tg _ (hopen W knownE knownB names _ L tg _)))
  have hall : ∀ d j, j + d = halvings counts.sum →
      PlanSuffix prims K D W knownE knownB names counts.sum L tg (knownHist K D x) j d := by
    intro d
    induction d with
    | zero =>
      intro j h
      rw [show j = halvings counts.sum by omega]
      exact hmask W knownE knownB names hn _ L tg _ hrest (hpartial W knownE knownB _ L)
    | succ d ih =>
      intro j h
      refine hextend W knownE knownB names hn _ L tg _ j d (by omega) ?_
      cases d with
      | zero => exact hlast W knownE knownB names hn _ L tg _ j (by omega) (ih (j + 1) (by omega))
      | succ d' => exact hcoin W knownE knownB names hn _ L tg _ j d' (by omega) (ih (j + 1) (by omega))
  have hstart := hfirst W knownE knownB names hn _ L tg _ (hall _ 0 (by omega))
  have h := hstart (zeroTables _) st ⟨knownHist K D x, []⟩ (fun i τ => headPlan K (localContext i) τ (x i))
    (fun i => ⟨filledHistory K i (x i), L, tg⟩)
    (fun i hi τ => by
      have h := planOK_headPlan K (localContext i) τ (x i)
      rwa [hx i hi] at h)
    (fun i _ => ⟨rfl, rfl⟩)
  simp only [splice_zero] at h
  have hreal : SameRun prims (c1Real K D W knownE knownB counts L tg x st)
      (drawTables (C := C) (E := E) (RealNetworkV3.checkLabels counts.sum) >>= fun T =>
        executePhase localRoles D W noFunctionality (2 * halvings counts.sum + 2) st
            (drawnHeadAt K D L tg knownE knownB T x) >>= realRest K D W knownE knownB counts.sum L T) :=
    by
    unfold c1Real
    refine SameRun.bind_right _ fun T => ?_
    have hcut := RealNetworkC1p.realCut prims K D W knownE knownB counts L tg T x st hpos hx
    unfold realRest
    exact hcut
  have eR : ∀ T : DrawTables C E (RealNetworkV3.checkLabels counts.sum),
      executePhase localRoles D W noFunctionality (2 * halvings counts.sum + 2) st
          (drawnHeadAt K D L tg knownE knownB T x) =
        executePhase localRoles D W noFunctionality (2 * halvings counts.sum + 2) st (fun i => (do
          let τ ← expand K (← coinKey K (drawnCheckBuildingBlocks K D L knownE knownB T i)) (coins counts.sum)
          StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
          runPlan K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB T i)
            (headPlan K (localContext i) τ (x i))).run ⟨filledHistory K i (x i), L, tg⟩) := fun T =>
    executePhase_congr D W _ _ st _ _ fun i hi => by
      unfold drawnHeadAt
      rw [headPlan_eq, hx i hi]
  have eH : executePhase localRoles D
        (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
          (c1HeadTails K D W knownE knownB counts.sum L tg))
        (checkFunctionalities K) (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (headAt K L tg x) =
      executePhase localRoles D
        (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
          (c1HeadTails K D W knownE knownB counts.sum L tg))
        (checkFunctionalities K) (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (fun i => (do
          let τ ← expand K (← coinKey K (hybridCheckBuildingBlocks K i)) (coins counts.sum)
          StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
          runPlan K (localContext i) (hybridCheckBuildingBlocks K i)
            (headPlan K (localContext i) τ (x i))).run ⟨filledHistory K i (x i), L, tg⟩) :=
    executePhase_congr D _ _ _ _ _ _ fun i hi => by
      unfold headAt
      rw [checkHead_eq, headPlan_eq, hx i hi]
  have hmid : c1Mid K D W knownE knownB names counts L tg x st =
      executePhase localRoles D
          (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
            (c1HeadTails K D W knownE knownB counts.sum L tg))
          (checkFunctionalities K) (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (headAt K L tg x) >>=
        midRest K D W knownE knownB names counts.sum L tg (knownHist K D x) := rfl
  rw [hmid, eH]
  refine hreal.trans (SameRun.trans (SameRun.bind_right _ fun T => SameRun.of_eq ?_) h)
  rw [eR T]

end ThresholdLeanXmssSecurity.RealNetworkC1r

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1q

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- The program of operator `i` after the computation of `H`. An operator with no input or no value
aborts. -/
def hoistNext {I O α γ σ : Type} (inputs : C.Party → Option σ)
    (next : C.Party → γ → σ → PartyM C E (CallSpec I O) α) (i : C.Party) :
    Option γ → PartyM C E (CallSpec I O) α
  | some c => (inputs i).elim failure (next i c)
  | none => failure

theorem hoist (prims : Primitives) (D : C.Coalition) : HoistStatement (E := E) prims D := by
  intro Ia I O L R α γ σ A F fuel st oa inputs next hlive
  let oa' : C.Party → OracleComp (LocalSpec C) (Option γ) := fun i =>
    if (inputs i).isSome then liftComp (some <$> oa) (LocalSpec C) else pure none
  have hL : (fun i => (inputs i).elim failure fun hs => oracleStep oa >>= fun c => next i c hs) =
      fun i => localStep (oa' i) >>= hoistNext inputs next i := by
    funext i
    cases h : inputs i with
    | none => simp [oa', h, localStep, hoistNext]
    | some hs =>
      simp only [oa', h, Option.isSome_some, ite_true, Option.elim_some, oracleStep, localStep, liftComp_map]
      apply OptionT.ext
      simp [OptionT.run_bind, OptionT.run_lift, hoistNext, h]
  rw [hL]
  refine (executePhase_local_fallback prims D A F fuel st oa' (fun _ => none) (hoistNext inputs next)).trans ?_
  have hseq : (fun i => if i ∈ D.1 then pure none else oa' i) = fun i =>
      @ite _ (i ∉ D.1 ∧ (inputs i).isSome) (Classical.propDecidable _) (liftComp (some <$> oa) (LocalSpec C))
        (pure none) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp [oa', hi]
  rw [hseq]
  obtain ⟨i₀, hi₀, hs₀⟩ := hlive
  refine ((sameRun_sequenceFin_selected prims (some <$> oa) none (fun i => i ∉ D.1 ∧ (inputs i).isSome)
    ⟨i₀, hi₀, hs₀⟩).bind fun v => SameRun.refl prims _).trans (SameRun.of_eq ?_)
  simp only [map_eq_bind_pure_comp, liftComp_bind, liftComp_pure, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun c => executePhase_congr D A F fuel st _ _ fun i hi => ?_
  cases h : inputs i <;> simp [h, hi, hoistNext]

end ThresholdLeanXmssSecurity.RealNetworkC1q

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1q

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real `Coin` from a full start is one round and then `coinRes`. -/
theorem realCoinPhase_full {I O L R Ia : Type} (K : Constants C E) (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (rnd : C.Party → PrssOutput C E) (count fuel : ℕ) (st : A.State) :
    (fun r => (r.1, fun i => (r.2 i).map (vector count))) <$>
        realCoinPhase K D A F rnd count (fuel + 1) st (fun _ => some ()) =
      A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then coinOut K i count (rnd i) c else none) >>= fun b =>
        pure (b.1, fun i => if i ∈ D.1 then none else
          coinRes K i count (rnd i) fun k => if k ∈ D.1 then b.2 k i else coinOut K k count (rnd k) i) := by
  unfold realCoinPhase
  rw [roundPhase_full D A F _ (fun i => coinOut K i count (rnd i))
    (fun i inbox => openRes K i (conv K (localContext i) (rnd i).1) count inbox) (fun i _ => ?_) fuel st]
  · simp only [map_bind, map_pure]
    refine bind_congr fun b => ?_
    congr 2
    funext i
    by_cases hi : i ∈ D.1
    · simp only [hi, ↓reduceIte, Option.map_none]
    · simp only [hi, ↓reduceIte, coinRes]
      split_ifs <;> rfl
  · simp only [Option.elim_some]
    rw [openSh_eq]
    rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Three maps after a computation are one map. The types of the maps unify only up to the unfolding of the
state of the wrapper, so the goals use this form and not `simp`. -/
theorem bind_pure_three {α β γ δ : Type} (x : OracleComp (LocalSpec C) α) (f : α → β) (h : β → γ) (g : γ → δ)
    (r : α → δ) (hr : ∀ a, g (h (f a)) = r a) :
    ((x >>= fun a => pure (f a)) >>= fun b => pure (h b)) >>= (pure ∘ g) = x >>= pure ∘ r := by
  simp only [bind_assoc, pure_bind, Function.comp_apply, hr]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- The wrapper with no tail answers with its block simulator and counts the call. -/
theorem noTails_answer {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ) (hist : C.Party → C.Term → List Bit)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (st : (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails).State) (l : CheckLeak C E) :
    (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails).answer st l =
      (fun a => ((a.1, st.2 + 1), a.2)) <$> c1Sims K D W knownE knownB st.2 st.1 l := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun a => by split_ifs <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The output of `F_coin` after the extract `coinOutput`. -/
theorem coinOutputs_bind (D : C.Coalition) (v : CoinValues D E) (receivers : Finset C.Party) (j : C.Party) :
    (coinOutputs D v (Sum.inl (Sum.inl receivers)) j).bind coinOutput =
      if j ∉ D.1 ∧ j ∈ receivers then some (List.ofFn v) else none := by
  unfold coinOutputs
  have hr : coinReply (Sum.inl (Sum.inl receivers) : CheckAnswer C E) = receivers := rfl
  by_cases h : j ∉ D.1 ∧ j ∈ receivers
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hr ▸ h)), ite_eq_left_of_eq_true _ _ (eq_true h)]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (hr ▸ h)), ite_eq_right_of_eq_false _ _ (eq_false h)]
    rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- An honest output of the coin simulator is the value of `F_coin` exactly when `coinRes` on the
adjusted fresh terms does not abort. Then `coinRes` gives this value (`coinRes_robust`). -/
theorem coinSim_out (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (fresh' : C.Term → Fin c → E) (freshPair : C.Pair → Fin c → E)
    (v : Fin c → E) (b : C.Party → C.Party → Option (Msg E)) (j : C.Party) :
    (if j ∈ D.1 then none else
      if j ∉ D.1 ∧ j ∈ Finset.univ.filter (fun x => x ∉ D.1 ∧
        (coinRes K x c (frandShare D c known knownPairs (adjust D known fresh' v) freshPair x) fun k =>
          if k ∈ D.1 then b k x
          else coinOut K k c (frandShare D c known knownPairs (adjust D known fresh' v) freshPair k) x).isSome)
      then some (List.ofFn v) else none) =
    (if j ∈ D.1 then none else
      coinRes K j c (frandShare D c known knownPairs (adjust D known fresh' v) freshPair j) fun k =>
        if k ∈ D.1 then b k j
        else coinOut K k c (frandShare D c known knownPairs (adjust D known fresh' v) freshPair k) j) := by
  by_cases hj : j ∈ D.1
  · simp only [hj, ite_true]
  · have hsum : (List.ofFn fun g : Fin c => ∑ T, frandAt D known (adjust D known fresh' v) g T) = List.ofFn v :=
      congrArg List.ofFn (funext fun g => sum_frandAt_adjust D known fresh' v g)
    rcases coinRes_robust K D c known knownPairs (adjust D known fresh' v) freshPair b j hj with h | h
    · simp [hj, h]
    · rw [hsum] at h
      simp [hj, h]

omit [Fintype E] [DecidableEq E] in
/-- The adjusted fresh terms of the coin simulator are uniform (`dist_adjust`). -/
theorem sameRun_adjust (prims : Primitives) (D : C.Coalition) (known : Shares C E) {n : ℕ} {β : Type}
    (X : (C.Term → Fin n → E) → OracleComp (LocalSpec C) β) :
    SameRun prims (liftComp ($ᵗ (C.Term → Fin n → E)) (LocalSpec C) >>= X)
      (liftComp ($ᵗ (Fin n → E)) (LocalSpec C) >>= fun v =>
        liftComp ($ᵗ (C.Term → Fin n → E)) (LocalSpec C) >>= fun fresh' => X (adjust D known fresh' v)) := by
  intro s
  simp only [simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left]
  exact (dist_adjust D known fun fresh => (simulateQ (localAnswer prims) (X fresh)).run s).symm

theorem coinHop (prims : Primitives) (K : Constants C E) (D : C.Coalition) : CoinHopStatement prims K D := by
  intro Ia W knownE knownB count hist names hn k fuel fuel' s
  have hR : (fun r => (r.1.1.1, r.2)) <$> RealNetworkGP.callPhase D
      (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
      (checkFunctionalities K) (fuel' + 1) (s, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput) =
      liftComp ($ᵗ (CoinValues D E)) (LocalSpec C) >>= fun v =>
        (fun a => (a.1, fun j => if j ∈ D.1 then none else
          (coinOutputs D v (Sum.inl (Sum.inl a.2)) j).bind coinOutput)) <$>
          coinSimAnswer K D (frandAdv W (knownE k) s.1) (List.ofFn v).length (List.ofFn v) s.1 := by
    rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st), map_bind]
    refine bind_congr fun v => ?_
    have hans := noTails_answer K D W knownE knownB count hist names (s, k) (Sum.inl (Sum.inl (List.ofFn v)))
    rw [hans]
    simp only [c1Sims, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    exact bind_pure_three _ _ _ _ _ fun _ => rfl
  rw [hR]
  simp only [realCoinPhase_full, List.length_ofFn, coinOutputs_bind]
  unfold CoinValues
  have hc := firstInput_honest_const D 2
  generalize firstInput (fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 2) = c at hc ⊢
  subst hc
  simp only [coinSimAnswer, frandAdv, pure_bind, map_bind, map_pure, getD_ofFn_eq, coinSim_out]
  exact sameRun_adjust prims D (knownE k).1 _

end ThresholdLeanXmssSecurity.RealNetworkC1q

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1q

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] in
/-- The coupling of a peer reshare (GS20, Lemmas 4 and 5) with the codec `elementCodec K`. -/
theorem sameRun_peerE {γ : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition) (count : ℕ)
    (known : Shares C E) (knownPairs : C.Party → C.Party → ℕ → E) (v : C.Party → ℕ → E)
    (filled : C.Term → ℕ → Option C.Party)
    (hfilled : ∀ T g, (∃ j ∈ D.1, filled T g = some j) ↔ ∃ j ∈ D.1, K.filled j = T)
    (product : ℕ → E) (hproduct : ∀ g, product g = ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
    (Xc : (C.Party → C.Party → Option (Msg E)) →
      ((C.Party → C.Party → Option (Msg E)) → C.Party → Option (Shares C E)) → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (do
        let fresh ← liftComp ($ᵗ (C.Term → Fin count → E)) (LocalSpec C)
        let freshPair ← liftComp ($ᵗ (C.Pair → Fin count → E)) (LocalSpec C)
        Xc (realMsgs K D (elementCodec K) known knownPairs fresh freshPair v)
          (realOut K D (elementCodec K) known knownPairs fresh freshPair v))
      (do
        let fresh ← liftComp ($ᵗ (C.Term → Fin count → E)) (LocalSpec C)
        let freshPair ← liftComp ($ᵗ (C.Pair → Fin count → E)) (LocalSpec C)
        let freshF ← liftComp ($ᵗ (C.Term → Fin count → E)) (LocalSpec C)
        Xc (realMsgs K D (elementCodec K) known knownPairs fresh freshPair fun _ _ => 0)
          (fun sent => idealOut D filled product
            (peerReply K D (elementCodec K) known knownPairs fresh freshPair sent) freshF)) := by
  have : CharP E 2 := charTwo
  obtain ⟨T0, p, hpiv⟩ := exists_pivot K D
  intro s
  simp only [simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left]
  refine evalDist_shift _ _ (fun w => (termShift K D T0 p v w, pairShift p (pairDelta K D T0 p v w)))
    (fun fresh freshPair T g => termVal K D (elementCodec K) known knownPairs fresh freshPair (fun _ _ => 0)
      (fun _ _ => none) (refHolder D T) T g.val) fun w fresh freshPair => ?_
  have hout : realOut K D (elementCodec K) known knownPairs (fresh + termShift K D T0 p v w)
      (freshPair + pairShift p (pairDelta K D T0 p v w)) v = fun sent =>
        idealOut D filled product (peerReply K D (elementCodec K) known knownPairs fresh freshPair sent)
          (w + fun T g => termVal K D (elementCodec K) known knownPairs fresh freshPair (fun _ _ => 0)
            (fun _ _ => none) (refHolder D T) T g.val) :=
    funext fun sent => realOut_shift K D (elementCodec K) (elementCodec_roundTrip K) known knownPairs fresh
      freshPair hpiv v w filled hfilled product hproduct sent
  dsimp only
  rw [realMsgs_shift K D (elementCodec K) known knownPairs fresh freshPair hpiv v w, hout]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Two maps, a sample and a pure output after a computation are one computation. The types of the maps
unify only up to the unfolding of the state of the wrapper, so the goals use this form and not `simp`. -/
theorem map_bind_samp {α β γ δ ε ζ : Type} (x : OracleComp (LocalSpec C) α) (f₁ : α → β) (f : β → γ)
    (samp : OracleComp (LocalSpec C) ε) (H : γ → ε → ζ) (g : ζ → δ) (R : α → ε → δ)
    (hR : ∀ r F, g (H (f (f₁ r)) F) = R r F) :
    g <$> ((f <$> (f₁ <$> x)) >>= fun a => samp >>= fun F => pure (H a F)) =
      x >>= fun r => samp >>= fun F => pure (R r F) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, hR]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real `extendMult` at operator `i` is one round of a peer reshare, then `record` and a new
label. -/
theorem realExtendProg_eq (K : Constants C E) (rnd : C.Party → PrssOutput C E) (i : C.Party)
    (p : List (Product C E) × RunState C) :
    realExtendProg K rnd i p =
      exchange (reshareOut K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2 (productValues K i p.1)
        p.1.length) >>= fun inbox =>
        pure (reshareZ K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2 (productValues K i p.1)
            p.1.length inbox,
          ⟨recordHistory K i p.2.history (reshareZ K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2
            (productValues K i p.1) p.1.length inbox) p.1.length, p.2.label + 1, p.2.tag⟩) := by
  unfold realExtendProg freshLabel
  simp only [StateT.run_bind, StateT.run_modifyGet, pure_bind]
  unfold reshare
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  simp only [record, StateT.run_modify, StateT.run_pure, pure_bind]
  rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The real `extendMult` for two products from a full start is one round and then `realOut`. -/
theorem realExtendPhase_full {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (W : Adversary C E Ia PEmpty PEmpty) (known : Shares C E) (knownPairs : C.Party → C.Party → ℕ → E)
    (fresh : C.Term → Fin 2 → E) (freshPair : C.Pair → Fin 2 → E) (fuel : ℕ) (st : W.State)
    (products : C.Party → List (Product C E)) (hs : C.Party → RunState C)
    (hlen : ∀ i, i ∉ D.1 → (products i).length = 2) :
    executePhase localRoles D W noFunctionality (fuel + 1) st (fun i =>
        realExtendProg K (frandShare D 2 known knownPairs fresh freshPair) i (products i, hs i)) =
      W.round st (realMsgs K D (elementCodec K) known knownPairs fresh freshPair
          fun i => productValues K i (products i)) >>= fun b =>
        pure (b.1, fun i => (realOut K D (elementCodec K) known knownPairs fresh freshPair
          (fun i => productValues K i (products i)) b.2 i).map fun z => (z, extendState K i (hs i) z)) := by
  rw [roundPhase_full D W noFunctionality _
    (fun i => reshareOut K (localContext i) (elementCodec K) (frandShare D 2 known knownPairs fresh freshPair i).1
      (frandShare D 2 known knownPairs fresh freshPair i).2 (productValues K i (products i)) 2)
    (fun i inbox => some (reshareZ K (localContext i) (elementCodec K)
      (frandShare D 2 known knownPairs fresh freshPair i).1 (frandShare D 2 known knownPairs fresh freshPair i).2
      (productValues K i (products i)) 2 inbox, extendState K i (hs i) (reshareZ K (localContext i) (elementCodec K)
      (frandShare D 2 known knownPairs fresh freshPair i).1 (frandShare D 2 known knownPairs fresh freshPair i).2
      (productValues K i (products i)) 2 inbox)))
    (fun i hi => by rw [realExtendProg_eq, hlen i hi]; rfl) fuel st]
  refine bind_congr fun b => ?_
  congr 2
  funext i
  unfold realOut
  by_cases hi : i ∈ D.1
  · simp only [hi, ↓reduceIte, Option.map_none]
  · simp only [hi, ↓reduceIte]
    split_ifs <;> rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The output of `F_extendMult` for the products of the honest operators is `idealOut` with the
product `extendTotal`. -/
theorem extendOutputs_eq_idealOut (K : Constants C E) (D : C.Coalition) (products : C.Party → List (Product C E))
    (hs : C.Party → RunState C) (reply : (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (freshF : C.Term → Fin (firstInput (fullInputs D products)).length → E) (j : C.Party) :
    (if j ∈ D.1 then none else (extendOutputs K D products (Sum.inl (Sum.inr reply)) freshF j).bind
      fun o => (extendOutput o).map fun z => (z, extendState K j (hs j) z)) =
    (idealOut D (filler K .peer) (extendTotal K D (fullInputs D products)) reply freshF j).map
      fun z => (z, extendState K j (hs j) z) := by
  unfold extendOutputs idealOut multFinish
  by_cases hj : j ∈ D.1
  · simp only [hj, ↓reduceIte, true_or, Option.map_none]
  · by_cases hr : j ∈ reply.2.2.2
    · simp only [hj, hr, ↓reduceIte, not_true_eq_false, or_self, Option.map_some, Option.bind_some, extendOutput,
        extendReply, add_sub_assoc]
    · simp only [hj, hr, ↓reduceIte, not_false_eq_true, or_true, Option.map_none, Option.bind_none, extendReply]

theorem extendHop (prims : Primitives) (K : Constants C E) (D : C.Coalition) : ExtendHopStatement prims K D := by
  intro Ia W knownE knownB count hist names hn k fuel fuel' s products hs hlen
  have hR : (fun r => (r.1.1.1, r.2)) <$> RealNetworkGP.callPhase D
      (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
      (checkFunctionalities K) (fuel' + 1) (s, k) (fun i => Sum.inl (Sum.inr (products i)))
      (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)) =
      peerSimAnswer K D (frandAdv (I := Ia) W (knownE k) s.1) (elementCodec K) 2 s.1 >>= fun r =>
        liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C) >>=
          fun freshF => pure (r.1, fun j => if j ∈ D.1 then none else
            (extendOutputs K D products (Sum.inl (Sum.inr r.2)) freshF j).bind
              fun o => (extendOutput o).map fun z => (z, extendState K j (hs j) z)) := by
    rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
      (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
      (pure () : OracleComp (LocalSpec C) Unit)
      (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products),
      map_bind, pure_bind, noTails_answer]
    exact map_bind_samp _ _ _ _ _ _ _ fun _ _ => rfl
  rw [hR]
  simp only [realExtendPhase_full K D W _ _ _ _ fuel s.1 products hs hlen, peerSimAnswer_eq, frandAdv, pure_bind,
    bind_assoc]
  simp only [extendOutputs_eq_idealOut]
  clear hR
  obtain ⟨j₀, hj₀, hw⟩ := firstInput_honest D products
  have hw2 : (firstInput (fullInputs D products)).length = 2 := by
    change (firstInput fun i => if i ∈ D.1 then none else some (products i)).length = 2
    rw [hw]
    exact hlen j₀ hj₀
  generalize (firstInput (fullInputs D products)).length = w at hw2 ⊢
  subst hw2
  refine (sameRun_peerE prims K D 2 (knownE k).1 (knownE k).2 (fun i => productValues K i (products i))
    (filler K .peer) (fun T g => filler_peer_corrupt K D T g) (extendTotal K D (fullInputs D products)) ?_
    (fun msgs out => W.round s.1 msgs >>= fun b =>
      pure (b.1, fun i => (out b.2 i).map fun z => (z, extendState K i (hs i) z)))).trans ?_
  · intro g
    unfold extendTotal
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [fullInputs, (Finset.mem_filter.mp hi).2, ↓reduceIte, Option.map_some, Option.getD_some]
    rfl
  · refine SameRun.bind_right _ fun fresh => SameRun.bind_right _ fun freshPair => ?_
    exact sameRun_swap prims _ _ _

end ThresholdLeanXmssSecurity.RealNetworkC1q

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1r

open RealNetworkV3 RealNetworkC1s RealNetworkC1q

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## The statements -/

/-- The state after a call of `F_coin` with no tail. After a call of `F_coin` at position `k` the counter
is `k + 1`, the histories do not change, and the memory holds the values of each honest output. -/
def CoinMemoryNoTailsStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (fuel k : ℕ) (s : W.State × C1Memory C E) (cache : HashCache C),
    ∀ z ∈ support ((simulateQ (localAnswer prims) (RealNetworkGP.callPhase D
        (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
        (checkFunctionalities K) (fuel + 1) (s, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput))).run cache),
      z.1.1.2 = k + 1 ∧ z.1.1.1.2.hist = s.2.hist ∧ ∀ i values, z.1.2 i = some values → z.1.1.1.2.values = values

/-- The state after a call of `F_coin` with the tails of the head. -/
def CoinMemoryHeadStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (fuel k : ℕ) (s : W.State × C1Memory C E) (cache : HashCache C),
    ∀ z ∈ support ((simulateQ (localAnswer prims) (RealNetworkGP.callPhase D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (fuel + 1) (s, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput))).run cache),
      z.1.1.2 = k + 1 ∧ z.1.1.1.2.hist = s.2.hist ∧ ∀ i values, z.1.2 i = some values → z.1.1.1.2.values = values

/-- The state after a call of `F_extendMult` with the tails of the head. -/
def ExtendMemoryHeadStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (fuel k : ℕ) (s : W.State × C1Memory C E) (products : C.Party → List (Product C E))
    (hs : C.Party → RunState C) (cache : HashCache C), (∀ i, i ∉ D.1 → (products i).length = 2) →
    ∀ z ∈ support ((simulateQ (localAnswer prims) (RealNetworkGP.callPhase D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (fuel + 1) (s, k) (fun i => Sum.inl (Sum.inr (products i)))
        (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)))).run cache),
      z.1.1.2 = k + 1 ∧ z.1.1.1.2.values = s.2.values ∧
        ∀ i out, i ∉ D.1 → z.1.2 i = some out →
          (∀ T, KnownTo D.1 T → s.2.hist i T = (hs i).history T) →
          ∀ T, KnownTo D.1 T → z.1.1.1.2.hist i T = out.2.history T

omit [Fintype E] in
/-- The tails of the head keep the memory. -/
theorem c1HeadTails_memory {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg n : ℕ) (live : Finset C.Party)
    (s : W.State × C1Memory C E) :
    ∀ y ∈ support (c1HeadTails K D W knownE knownB count L tg n live s), y.2 = s.2 := by
  intro y hy
  unfold c1HeadTails at hy
  split_ifs at hy
  · rw [support_pure, Set.mem_singleton_iff] at hy
    rw [hy]
  · exact c1Tails_memory K D W knownE knownB count L tg n live s y hy

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem noTails_memory {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (n : ℕ) (live : Finset C.Party)
    (s : W.State × C1Memory C E) : ∀ y ∈ support (RealNetworkGP.noTails (C := C) n live s), y.2 = s.2 := by
  intro y hy
  rw [RealNetworkGP.noTails, support_pure, Set.mem_singleton_iff] at hy
  rw [hy]

/-- The memory after a call of `F_coin`, for each `tails` that keeps the memory. -/
theorem coinMemory_of_tails (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (htails : ∀ n live s, ∀ y ∈ support (tails n live s), y.2 = s.2)
    (fuel k : ℕ) (s : W.State × C1Memory C E) (cache : HashCache C) :
    ∀ z ∈ support ((simulateQ (localAnswer prims) (RealNetworkGP.callPhase D
        (c1WrapperWith K D W knownE knownB count hist names tails)
        (checkFunctionalities K) (fuel + 1) (s, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput))).run cache),
      z.1.1.2 = k + 1 ∧ z.1.1.1.2.hist = s.2.hist ∧ ∀ i values, z.1.2 i = some values → z.1.1.1.2.values = values := by
  intro z hz
  have h1 := fst_mem_support_run prims _ cache z hz
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
    (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
    (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
    (fun st => coinRun_form K D _ st)] at h1
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1
  obtain ⟨v, -, a, ha, -, -, hz1⟩ := h1
  rw [hz1]
  obtain ⟨r, hr, ha⟩ := (mem_support_bind_iff _ _ _).1 ha
  obtain ⟨r, -, rfl⟩ := exists_of_mem_support_map _ _ _ hr
  have hout : ∀ i values, (if i ∈ D.1 then none else (coinOutputs D v a.2 i).bind coinOutput) = some values →
      values = List.ofFn v := fun i values h => by
    unfold coinOutputs at h
    split_ifs at h <;> simp_all [coinOutput]
  split_ifs at ha
  · obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map _ _ _ ha
    have hm := htails k _ _ y hy
    refine ⟨rfl, by rw [hm], fun i values h => by rw [hm, hout i values h]⟩
  · rw [support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨rfl, rfl, fun i values h => (hout i values h).symm⟩

/-- The memory after a call of `F_extendMult`, for each `tails` that keeps the memory. -/
theorem extendMemory_of_tails (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (htails : ∀ n live s, ∀ y ∈ support (tails n live s), y.2 = s.2)
    (fuel k : ℕ) (s : W.State × C1Memory C E) (products : C.Party → List (Product C E))
    (hs : C.Party → RunState C) (cache : HashCache C) (hlen : ∀ i, i ∉ D.1 → (products i).length = 2) :
    ∀ z ∈ support ((simulateQ (localAnswer prims) (RealNetworkGP.callPhase D
        (c1WrapperWith K D W knownE knownB count hist names tails)
        (checkFunctionalities K) (fuel + 1) (s, k) (fun i => Sum.inl (Sum.inr (products i)))
        (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)))).run cache),
      z.1.1.2 = k + 1 ∧ z.1.1.1.2.values = s.2.values ∧
        ∀ i out, i ∉ D.1 → z.1.2 i = some out →
          (∀ T, KnownTo D.1 T → s.2.hist i T = (hs i).history T) →
          ∀ T, KnownTo D.1 T → z.1.1.1.2.hist i T = out.2.history T := by
  intro z hz
  have h1 := fst_mem_support_run prims _ cache z hz
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
    (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
    (pure () : OracleComp (LocalSpec C) Unit)
    (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
    (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
    (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products)] at h1
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1
  obtain ⟨-, -, a, ha, fresh, -, hz1⟩ := h1
  rw [hz1]
  obtain ⟨r, hr, ha⟩ := (mem_support_bind_iff _ _ _).1 ha
  obtain ⟨r, -, rfl⟩ := exists_of_mem_support_map _ _ _ hr
  have hkey : ∀ i out, i ∉ D.1 → (if i ∈ D.1 then none else (extendOutputs K D products
        (Sum.inl (Sum.inr r.2)) fresh i).bind fun o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)) =
        some out → (∀ T, KnownTo D.1 T → s.2.hist i T = (hs i).history T) →
      ∀ T, KnownTo D.1 T → recordKnown K D s.2.hist r.2 i T = out.2.history T := by
    intro i out hi h hh T hT
    obtain ⟨j, hj, hw⟩ := firstInput_honest D products
    have hw2 : (firstInput (fullInputs D products)).length = 2 := by
      change (firstInput fun i => if i ∈ D.1 then none else some (products i)).length = 2
      rw [hw]; exact hlen j hj
    simp only [hi, ite_false, extendOutputs, multFinish, extendReply, false_or] at h
    split_ifs at h with hrec <;> simp only [Option.map_none, Option.bind_none, reduceCtorEq, Option.map_some,
      Option.bind_some, extendOutput, Option.some.injEq] at h
    subst h
    simp only [recordKnown, hi, hT, not_false_eq_true, and_self, ite_true, extendState, recordHistory]
    have hn : lackedTerm D.1 ≠ some T := fun h => lackedTerm_unknown D T h hT
    rw [hh T hT]
    by_cases hiT : i ∈ C.holders T
    · simp only [hiT, ite_true]
      congr 1
      refine List.flatMap_congr fun g hg => ?_
      have hg2 : g < 2 := List.mem_range.1 (List.mem_filter.1 hg).1
      simp only [Function.comp_apply, hw2, hg2, and_self, ite_true, hn, ite_false]
    · simp only [hiT, ite_false]
  split_ifs at ha
  · obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map _ _ _ ha
    have hm := htails k _ _ y hy
    refine ⟨rfl, by rw [hm], fun i out hi h hh => by rw [hm]; exact hkey i out hi h hh⟩
  · rw [support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨rfl, rfl, hkey⟩

theorem coinMemoryNoTails (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    CoinMemoryNoTailsStatement prims K D :=
  fun W knownE knownB count hist names fuel k s cache =>
    coinMemory_of_tails prims K D W knownE knownB count hist names _ (fun n live s => noTails_memory W n live s)
      fuel k s cache

theorem coinMemoryHead (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    CoinMemoryHeadStatement prims K D :=
  fun W knownE knownB count L tg hist names fuel k s cache =>
    coinMemory_of_tails prims K D W knownE knownB count hist names _
      (c1HeadTails_memory K D W knownE knownB count L tg) fuel k s cache

theorem extendMemoryHead (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    ExtendMemoryHeadStatement prims K D :=
  fun W knownE knownB count L tg hist names fuel k s products hs cache hlen =>
    extendMemory_of_tails prims K D W knownE knownB count hist names _
      (c1HeadTails_memory K D W knownE knownB count L tg) fuel k s products hs cache hlen

/-! ## Corner cases -/

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A corner case of the hops of `F_rand`. Under `c1Names` the reply to `F_rand` names each honest operator, so
the reply is not partial and no tail runs. A `names` with no premise could start a tail. -/
theorem frand_not_partial (D : C.Coalition) (l : Unit ⊕ Unit) (r : CheckAnswer C E) :
    ¬ PartialOut D (receivers D c1Names (Sum.inr l : CheckLeak C E) r) := by
  rintro ⟨⟨i, hi, hn⟩, -⟩
  simp only [receivers, c1Names, hi, not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hn

end ThresholdLeanXmssSecurity.RealNetworkC1r

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

/-- A uniform sample keeps its distribution under a translation. -/
theorem sameRun_translate (prims : Primitives) {α β : Type} [AddGroup α] [SampleableType α] (m : α)
    (X : α → OracleComp (LocalSpec C) β) :
    SameRun prims (liftComp ($ᵗ α) (LocalSpec C) >>= fun y => X (y + m)) (liftComp ($ᵗ α) (LocalSpec C) >>= X) := by
  intro s
  simp only [simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left]
  exact evalDist_bind_add_uniform m (fun y => (simulateQ (localAnswer prims) (X y)).run s)

/-- An unused sample drops. -/
theorem sameRun_drop (prims : Primitives) {α β : Type} (p : ProbComp α) (X : OracleComp (LocalSpec C) β) :
    SameRun prims (liftComp p (LocalSpec C) >>= fun _ => X) X := by
  intro s
  simp only [simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left]
  exact EvalDistEq.bind_const p _

/-- A uniform table with a new uniform row `n` is a uniform table. -/
theorem sameRun_setRow (prims : Primitives) {X β : Type} [AddCommGroup X] [SampleableType X] {m : ℕ}
    [SampleableType (Fin m → X)] (n : ℕ) (F : (Fin m → X) → OracleComp (LocalSpec C) β) :
    SameRun prims
      (liftComp ($ᵗ X) (LocalSpec C) >>= fun a => liftComp ($ᵗ (Fin m → X)) (LocalSpec C) >>= fun f =>
        F (fun k => if k.val = n then a else f k))
      (liftComp ($ᵗ (Fin m → X)) (LocalSpec C) >>= F) := by
  by_cases hn : n < m
  · have hrow (a : X) (f : Fin m → X) :
        (fun k : Fin m => if k.val = n then a + f ⟨n, hn⟩ else f k) = f + Pi.single ⟨n, hn⟩ a := by
      funext k
      by_cases hk : k.val = n
      · have : k = ⟨n, hn⟩ := Fin.ext hk
        subst this
        simp [add_comm]
      · have : k ≠ ⟨n, hn⟩ := fun h => hk (by rw [h])
        simp [hk, this]
    have h1 := sameRun_swap prims (liftComp ($ᵗ X) (LocalSpec C)) (liftComp ($ᵗ (Fin m → X)) (LocalSpec C))
      fun a f => F (fun k => if k.val = n then a else f k)
    have h2 : SameRun prims
        (liftComp ($ᵗ (Fin m → X)) (LocalSpec C) >>= fun f => liftComp ($ᵗ X) (LocalSpec C) >>= fun a =>
          F (fun k => if k.val = n then a else f k))
        (liftComp ($ᵗ (Fin m → X)) (LocalSpec C) >>= fun f => liftComp ($ᵗ X) (LocalSpec C) >>= fun a =>
          F (f + Pi.single ⟨n, hn⟩ a)) := by
      refine SameRun.bind_right _ fun f => ?_
      refine (sameRun_translate prims (f ⟨n, hn⟩) (fun a => F (fun k => if k.val = n then a else f k))).symm.trans ?_
      simp only [hrow]
      exact SameRun.refl prims _
    have h3 := sameRun_swap prims (liftComp ($ᵗ (Fin m → X)) (LocalSpec C)) (liftComp ($ᵗ X) (LocalSpec C))
      fun f a => F (f + Pi.single ⟨n, hn⟩ a)
    have h4 : SameRun prims
        (liftComp ($ᵗ X) (LocalSpec C) >>= fun a => liftComp ($ᵗ (Fin m → X)) (LocalSpec C) >>= fun f =>
          F (f + Pi.single ⟨n, hn⟩ a))
        (liftComp ($ᵗ X) (LocalSpec C) >>= fun _ => liftComp ($ᵗ (Fin m → X)) (LocalSpec C) >>= F) :=
      SameRun.bind_right _ fun a => (sameRun_translate (C := C) (α := Fin m → X) prims (Pi.single ⟨n, hn⟩ a) F :)
    exact h1.trans (h2.trans (h3.trans (h4.trans (sameRun_drop prims _ _))))
  · have hrow (a : X) (f : Fin m → X) : (fun k : Fin m => if k.val = n then a else f k) = f :=
      funext fun k => by simp only [show k.val ≠ n by omega, ↓reduceIte]
    simp only [hrow]
    exact sameRun_drop prims _ _

section Resample

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

theorem resample (prims : Primitives) : ResampleStatement prims C E := by
  intro m α n G
  refine SameRun.symm ?_
  unfold drawTables
  simp only [bind_assoc, pure_bind, setRow]
  refine (SameRun.bind_right _ fun a => sameRun_swap prims (liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C))
    (liftComp ($ᵗ (Fin m → C.Term → Fin 2 → E)) (LocalSpec C)) _).trans ?_
  refine (sameRun_setRow (X := C.Term → Fin 2 → E) prims n (fun freshE =>
    liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun b =>
    liftComp ($ᵗ (Fin m → C.Pair → Fin 2 → E)) (LocalSpec C) >>= fun freshPairE =>
    liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C) >>= fun freshB =>
    liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C) >>= fun freshPairB =>
    G ⟨freshE, fun k => if k.val = n then b else freshPairE k, freshB, freshPairB⟩)).trans ?_
  refine SameRun.bind_right _ fun freshE => ?_
  exact sameRun_setRow (X := C.Pair → Fin 2 → E) prims n (fun freshPairE =>
    liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C) >>= fun freshB =>
    liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C) >>= fun freshPairB =>
    G ⟨freshE, freshPairE, freshB, freshPairB⟩)

theorem resampleBits (prims : Primitives) : ResampleBitsStatement prims C E := by
  intro m α G
  refine SameRun.symm ?_
  unfold drawTables
  simp only [bind_assoc, pure_bind, setSalts]
  have hdrop (X : OracleComp (LocalSpec C) α) : SameRun prims
      (liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C) >>= fun _ =>
        liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C) >>= fun _ => X) X :=
    (sameRun_drop prims _ _).trans (sameRun_drop prims _ _)
  let sB := liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
  let sPB := liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C)
  let sE := liftComp ($ᵗ (Fin m → C.Term → Fin 2 → E)) (LocalSpec C)
  let sPE := liftComp ($ᵗ (Fin m → C.Pair → Fin 2 → E)) (LocalSpec C)
  refine (SameRun.bind_right sB fun a => sameRun_swap prims sPB sE _).trans ?_
  refine (sameRun_swap prims sB sE _).trans ?_
  refine (SameRun.bind_right sE fun _ => SameRun.bind_right sB fun _ => sameRun_swap prims sPB sPE _).trans ?_
  refine (SameRun.bind_right sE fun _ => sameRun_swap prims sB sPE _).trans ?_
  exact SameRun.bind_right sE fun _ => SameRun.bind_right sPE fun _ => SameRun.bind_right sB fun _ =>
    SameRun.bind_right sPB fun _ => hdrop _

end Resample

end ThresholdLeanXmssSecurity.RealNetworkC1t

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.headPlan_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.headPlan_eq

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.planOK_headPlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.planOK_headPlan

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.splice_setRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.splice_setRow

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.headTimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.headTimed

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.hybridCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.hybridCut

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.realHeadTimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.realHeadTimed

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.realCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.realCut

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.c1Zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.c1Zero

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.c1a_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.c1a_of_steps

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1q.hoist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1q.hoist

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1q.coinHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1q.coinHop

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1q.extendHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1q.extendHop

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.coinMemoryNoTails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.coinMemoryNoTails

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.coinMemoryHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.coinMemoryHead

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.extendMemoryHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.extendMemoryHead

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1t.resample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1t.resample

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1t.resampleBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1t.resampleBits
