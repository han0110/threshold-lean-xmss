import ThresholdLeanXmssSecurity.Proof.TreeCheckGadgetBlocks
import ThresholdLeanXmssSecurity.Proof.TreeCheckGadgetPass

/-! # Coin and random-bit segments with retained PRSS blocks
The real sampled table is retained through a projection coupling. The common
optional outputs select the continuation at the next fresh label.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckGadgetCoin
open TreeCheckKernelCoupling TreeCheckGadgetBlocks TreeCheckGadgetPass TreeCheckRandRows
open TreeCheckWalkRecipe TreeCheckWalkCoupling
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E R α β σ : Type}

/-- The restriction law remains valid under an arbitrary subsequent computation. -/
theorem named_tables_bind [Finite R] [Nonempty R] [SampleableType R] (count : ℕ)
    (f : (C.Term → Fin count → R) → (C.Pair → Fin count → R) → ProbComp α) :
    𝒟[($ᵗ (KeyName C → Fin count → R)) >>= fun vals => f (termTable vals) (pairTable vals)] =
      𝒟[($ᵗ (C.Term → Fin count → R)) >>= fun t => ($ᵗ (C.Pair → Fin count → R)) >>= f t] := by
  calc
    _ = 𝒟[((fun vals : KeyName C → Fin count → R => (termTable vals, pairTable vals)) <$>
        ($ᵗ (KeyName C → Fin count → R))) >>= fun a => f a.1 a.2] := by
      simp only [bind_map_left]
    _ = _ := by
      rw [evalDist_bind, evalDist_keyName_tables, ← evalDist_bind]
      simp only [bind_assoc, pure_bind]

/-- Optional real outputs resume exactly once, including selective aborts. -/
theorem resumeAll_start (D : C.Coalition) (k : C.Party → α → PartyM C E RealSpec β)
    (out : C.Party → Option α) (corrupt : ∀ i, i ∈ D.1 → out i = none) :
    treeSimResumeAll k out = startSteps worldRoles D (fun i => (out i).elim failure (k i)) := by
  unfold treeSimResumeAll startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, treeSimResume, free_pure]
  · cases he : out i <;> simp [hi, he, treeSimResume, worldRoles, advance_pure, free_pure]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
local instance : SampleableType E := SampleableType.ofFintype E

/-- Retaining the real table does not lose the standard Coin round coupling. -/
theorem named_coin_round (count : ℕ) (known : Shares C E)
    (pairs : C.Party → C.Party → ℕ → E)
    (answer : (C.Party → Mail C E) → ProbComp (σ × (C.Party → Mail C E))) :
    RelTriple
      (do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        let rnd := frandShare D count known pairs (termTable vals) (pairTable vals)
        let b ← answer (treeSimCoinView K D count rnd)
        pure ((b.1, treeSimCoinOutput K D count rnd b.2), vals))
      (do
        let v ← $ᵗ (Fin count → E)
        let t ← $ᵗ (C.Term → Fin count → E)
        let p ← $ᵗ (C.Pair → Fin count → E)
        let rnd := frandShare D count known pairs (adjust D known t v) p
        let b ← answer (treeSimCoinView K D count rnd)
        pure (b.1, fun i => (treeSimCoinOutput K D count rnd b.2 i).map (fun _ => List.ofFn v)))
      (fun a b => a.1 = b) := by
  apply relTriple_of_map_left (f := Prod.fst)
  apply relTriple_of_evalDist_eq_left _ (treeSim_coin_round K D (c := count) known pairs answer)
  simp only [map_bind, map_pure]
  exact named_tables_bind (R := E) count (fun t p => do
    let rnd := frandShare D count known pairs t p
    let b ← answer (treeSimCoinView K D count rnd)
    pure (b.1, treeSimCoinOutput K D count rnd b.2))

def resumeCoinR (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec β)
    (out : C.Party → Option (List E)) : C.Party → PartyM C E RealSpec β :=
  fun i => (out i).elim failure (fun v => k i (v, nextLabel (st i)))

def resumeCoinH (hs : C.Party → RunState C)
    (k : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (out : C.Party → Option (List E)) : C.Party → PartyM C E (CheckSpec C E) Unit :=
  fun i => (out i).elim failure (fun v => (k i v).run' (nextLabel (hs i)))

/-- A ready Coin performs one rushing round and then the exact optional continuation. -/
theorem realRun_coin_ready (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (stA : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec β)
    (rnd : C.Party → PrssOutput C E) (h : HashCache C) (c : HiddenCache C)
    (ready : ∀ i, i ∉ D.1 → (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw (ctx i) (elementCodec K) (st i).label 1 count) (LocalSpec C)))).run (h,c) =
        pure (rnd i, (h,c))) :
    realRun prims D A (n+1) stA
      (fun i => ((realCheckGadgets K (ctx i)).coin count).run (st i) >>= k i) (h,c) =
    ((simulateQ (localAnswer prims) (A.round stA (treeSimCoinView K D count rnd))).run h >>= fun b =>
      realRun prims D A n b.1.1 (resumeCoinR st k (treeSimCoinOutput K D count rnd b.1.2)) (b.2,c)) := by
  have hn : ¬ ∀ i, i ∉ D.1 → (treeSimCoinWaiting K D count rnd st k i).isDone := by
    obtain ⟨i, hi⟩ := coalition_has_honest D
    intro hd
    simpa [treeSimCoinWaiting, hi, treeSimCoinStep, Step.isDone] using hd i hi
  unfold realRun
  simp only [simulateQ_bind, StateT.run_bind]
  rw [treeSimCheck_coin_start_ready prims K D ctx self count st k rnd (h,c) ready, pure_bind,
    executeSteps, if_neg hn, treeSim_coin_round_factor]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind]
  rw [adversary_run prims D, bind_map_left]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro b
  have hr := resumeAll_start D k (fun i => (treeSimCoinOutput K D count rnd b.1.2 i).map
    (fun v => (v,nextLabel (st i)))) (by intro i hi; simp [treeSimCoinOutput, hi])
  rw [hr]
  have hp : (fun i => ((treeSimCoinOutput K D count rnd b.1.2 i).map
      (fun v => (v,nextLabel (st i)))).elim failure (k i)) =
      resumeCoinR st k (treeSimCoinOutput K D count rnd b.1.2) := by
    funext i
    unfold resumeCoinR
    cases treeSimCoinOutput K D count rnd b.1.2 i <;> rfl
  rw [hp]




/-- The shared view depends only on honest rows below the requested count. -/
theorem coin_view_below (count : ℕ) (r s : C.Party → PrssOutput C E)
    (agree : ∀ i, i ∉ D.1 → ∀ T g, g < count → (r i).1 T g = (s i).1 T g) :
    treeSimCoinView K D count r = treeSimCoinView K D count s := by
  funext j i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinView, hi]
  · simp only [treeSimCoinView, coinOut_below K i (r i) (s i) (agree i hi)]

/-- Each optional Coin output depends on the same bounded honest rows. -/
theorem coin_output_below (count : ℕ) (r s : C.Party → PrssOutput C E)
    (agree : ∀ i, i ∉ D.1 → ∀ T g, g < count → (r i).1 T g = (s i).1 T g)
    (sent : C.Party → Mail C E) :
    treeSimCoinOutput K D count r sent = treeSimCoinOutput K D count s sent := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinOutput, hi]
  · simp only [treeSimCoinOutput, if_neg hi]
    have inbox : (fun j => if j ∈ D.1 then sent j i else coinOut K j count (r j) i) =
        (fun j => if j ∈ D.1 then sent j i else coinOut K j count (s j) i) := by
      funext j
      by_cases hj : j ∈ D.1
      · simp [hj]
      · rw [if_neg hj, if_neg hj, coinOut_below K j (r j) (s j) (agree j hj)]
    rw [inbox, coinRes_below K i (r i) (s i) _ (agree i hi)]

/-- One hybrid Coin functionality call, before interpreting the adapter answer. -/
theorem hybRun_coin (Ad : CheckAdversary C E (List (Tuple C))) (n : ℕ) (stA : Ad.State)
    (count : ℕ) (hs : C.Party → RunState C)
    (k : C.Party → List E → RunM C E (CheckSpec C E) Unit) (h : HashCache C) :
    hybRun prims K D Ad (n+1) stA
      (fun i => ((hybridCheckGadgets K i).coin count >>= k i).run' (hs i)) h =
    ((simulateQ (localAnswer prims)
      (runFunctionality localRoles D (leftAdversary (leftAdversary Ad)) (Fcoin (E := E)) stA
        (fun i => if i ∈ D.1 then none else some count))).run h >>= fun b =>
      hybRun prims K D Ad n b.1.1 (resumeCoinH hs k b.1.2) b.2) := by
  have phase : executePhase localRoles D Ad (checkFunctionalities K) (n+1) stA
      (fun i => ((hybridCheckGadgets K i).coin count >>= k i).run' (hs i)) =
      (runFunctionality localRoles D (leftAdversary (leftAdversary Ad)) (Fcoin (E := E)) stA
        (fun i => if i ∈ D.1 then none else some count) >>= fun b =>
      executePhase localRoles D Ad (checkFunctionalities K) n b.1 (resumeCoinH hs k b.2)) := by
    simp_rw [coin_run']
    rw [executePhase_call, runCheck_coin, bind_map_left]
    apply bind_congr
    intro b
    dsimp only
    congr 1
    funext i
    unfold resumeCoinH
    cases b.2 i <;> rfl
  unfold hybRun
  rw [phase]
  simp only [simulateQ_bind, StateT.run_bind]

/-- The adapter's Coin call is the standard chosen-coin experiment, with the whole hash cache. -/
theorem adapter_coin_call (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C)
    (label0 ℓ : ℕ) (stA : A.State) (h : HashCache C) :
    (simulateQ (localAnswer prims)
      (runFunctionality localRoles D
        (leftAdversary (leftAdversary (adapter prims K D A x prss cache0 label0))) (Fcoin (E := E))
        (stA,ℓ) (fun i => if i ∈ D.1 then none else some 1))).run h =
    (do
      let v ← $ᵗ (Fin 1 → E)
      let t ← $ᵗ (C.Term → Fin 1 → E)
      let p ← $ᵗ (C.Pair → Fin 1 → E)
      let known := knownRows D (fieldRow prims K D prss cache0 ℓ 1 1)
      let rnd := frandShare D 1 known.1 known.2 (adjust D known.1 t v) p
      let b ← (simulateQ (localAnswer prims) (A.round stA (treeSimCoinView K D 1 rnd))).run h
      pure (((b.1.1,ℓ+1), fun i => (treeSimCoinOutput K D 1 rnd b.1.2 i).map
        (fun _ => List.ofFn v)), b.2)) := by
  rw [runFunctionality_coin_local D _ _ _ (by intro i hi; simp [hi]), firstInput_honest_const]
  simp only [adapter, TreeCheckWalkRecipe.checkAdversary, leftAdversary,
    coinSimAnswer, randomAdversary, List.length_ofFn, getD_ofFn_eq,
    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    run_liftComp_prob, bind_map_left]
  apply bind_congr
  intro v
  apply bind_congr
  intro t
  apply bind_congr
  intro p
  apply bind_congr
  intro b
  congr 1
  congr 1
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinOutput, hi]
  · simp only [treeSimCoinOutput, hi, if_false, not_false_eq_true, true_and,
      Finset.mem_filter, Finset.mem_univ]
    have hc (o : Option (List E)) (v : List E) :
        (if o.isSome then some v else none) = o.map (fun _ => v) := by
      cases o <;> rfl
    exact hc _ _


/-- The all-live Coin segment, with its actual installed cache and optional outputs. -/
theorem coupled_coin_all (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' ℓ : ℕ)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = ℓ)
    (kR : C.Party → List E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ out : C.Party → Option (List E),
      Coupled prims K D A x prss cache0 label0 n n' (ℓ+1)
        (resumeCoinR st kR out) (resumeCoinH hs kH out)) :
    Coupled prims K D A x prss cache0 label0 (n+1) (n'+1) ℓ
      (fun i => ((realCheckGadgets K (ctx i)).coin 1).run (st i) >>= kR i)
      (fun i => ((hybridCheckGadgets K i).coin 1 >>= kH i).run' (hs i)) := by
  intro stA h c grow fresh
  let known := knownRows D (fieldRow prims K D prss cache0 ℓ 1 1)
  let inst := fun vals => treeSimCheckPrssCache K D (streamKey D prss) ℓ 1 1 vals c
  let rnd := fun vals => frandShare D 1 known.1 known.2 (termTable vals) (pairTable vals)
  let ans := fun view => (fun b : (A.State × (C.Party → Mail C E)) × HashCache C =>
    ((b.1.1,b.2),b.1.2)) <$> (simulateQ (localAnswer prims) (A.round stA view)).run h
  have step := named_coin_round K D 1 known.1 known.2 ans
  have grown := relTriple_support_left step (P := fun a => h ≤ a.1.1.2) (by
    intro a ha
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at ha
    obtain ⟨vals, hv, b, hb, he⟩ := ha
    subst a
    simp only [ans, support_map, Set.mem_image] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    exact (grows_localAnswer prims).simulateQ _ h z hz)
  have full := relTriple_bind grown (S := Final D A)
    (fa := fun a => realRun prims D A n a.1.1.1 (resumeCoinR st kR a.1.2) (a.1.1.2,inst a.2))
    (fb := fun b => hybRun prims K D (adapter prims K D A x prss cache0 label0) n'
      (b.1.1,ℓ+1) (resumeCoinH hs kH b.2) b.1.2) (by
        rintro a b ⟨he, hg⟩
        subst b
        exact next a.1.2 a.1.1.1 a.1.1.2 (inst a.2) (grow.trans hg)
          (futureEmpty_block K D (streamKey D prss) ℓ 1 1 a.2 c fresh))
  apply relTriple_of_evalDist_eq_left
    (realRun_presample_fields prims K D A (n+1) stA _ (streamKey D prss) ℓ 1 1 h c fresh)
  have real : ∀ vals : KeyName C → Fin 1 → E,
      realRun prims D A (n+1) stA
        (fun i => ((realCheckGadgets K (ctx i)).coin 1).run (st i) >>= kR i) (h,inst vals) =
      (ans (treeSimCoinView K D 1 (rnd vals)) >>= fun b =>
        realRun prims D A n b.1.1 (resumeCoinR st kR (treeSimCoinOutput K D 1 (rnd vals) b.2))
          (b.1.2,inst vals)) := by
    intro vals
    let actual := treeSimCheckPrssRows prims K D (derivedKey D prss cache0) ℓ 1 1 vals
    have ready i (hi : i ∉ D.1) : (simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw (ctx i) (elementCodec K) (st i).label 1 1) (LocalSpec C)))).run (h,inst vals) =
        pure (actual i,(h,inst vals)) := by
      rw [labels i hi]
      have hh : (ctx i).self ∉ D.1 := by rw [self i hi]; exact hi
      simpa only [self i hi] using prssDraw_rows_used prims K D prss cache0 h (ctx i) hh
        (terms i hi) (pairs i hi) cached grow ℓ 1 1 vals c (inst vals) le_rfl
    have agree : ∀ i, i ∉ D.1 → ∀ T g, g < 1 → (actual i).1 T g = (rnd vals i).1 T g := by
      intro i hi T g hg
      exact (prssRows_frandShare_below prims K D prss cache0 ℓ 1 1 vals i hi g hg).1 T
    rw [realRun_coin_ready prims K D A n stA ctx self 1 st kR actual h (inst vals) ready,
      coin_view_below K D 1 actual (rnd vals) agree]
    simp only [ans, bind_map_left]
    apply bind_congr
    intro b
    rw [coin_output_below K D 1 actual (rnd vals) agree b.1.2]
  rw [funext real]
  rw [hybRun_coin, adapter_coin_call]
  simpa only [rnd, ans, inst, known, bind_assoc, pure_bind, bind_map_left]
    using full



/-- Only honest programs are run by either side of the coupling. -/
theorem coupled_congr_honest (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 n n' ℓ : ℕ)
    (P P' : C.Party → PartyM C E RealSpec β)
    (Q Q' : C.Party → PartyM C E (CheckSpec C E) Unit)
    (hp : ∀ i, i ∉ D.1 → P i = P' i) (hq : ∀ i, i ∉ D.1 → Q i = Q' i)
    (coupled : Coupled prims K D A x prss cache0 label0 n n' ℓ P' Q') :
    Coupled prims K D A x prss cache0 label0 n n' ℓ P Q := by
  have starts : startSteps worldRoles D P = startSteps worldRoles D P' := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, hp i]
  intro stA h c grow fresh
  have hc := coupled stA h c grow fresh
  unfold realRun hybRun at hc ⊢
  rw [starts, executePhase_congr_honest D (adapter prims K D A x prss cache0 label0)
    (checkFunctionalities K) n' (stA,ℓ) Q Q' hq]
  exact hc

/-- The Coin segment includes all partial-live and all-aborted entries. -/
theorem coupled_coin (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' ℓ : ℕ)
    (live : C.Party → Prop)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = ℓ)
    (kR : C.Party → List E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ out : C.Party → Option (List E),
      Coupled prims K D A x prss cache0 label0 n n' (ℓ+1)
        (resumeCoinR st kR out) (resumeCoinH hs kH out)) :
    Coupled prims K D A x prss cache0 label0 (n+1) (n'+1) ℓ
      (fun i => if live i then ((realCheckGadgets K (ctx i)).coin 1).run (st i) >>= kR i else failure)
      (fun i => if live i then ((hybridCheckGadgets K i).coin 1 >>= kH i).run' (hs i) else failure) := by
  by_cases all : ∀ i, i ∉ D.1 → live i
  · apply coupled_congr_honest prims K D A x prss cache0 label0 (n+1) (n'+1) ℓ _ _ _ _
      (fun i hi => if_pos (all i hi)) (fun i hi => if_pos (all i hi))
    exact coupled_coin_all prims K D A x prss cache0 label0 ctx self terms pairs cached
      n n' ℓ st hs labels kR kH next
  · push Not at all
    intro stA h c grow fresh
    apply doomed_post prims D K A (adapter prims K D A x prss cache0 label0) n n' stA (stA,ℓ) _ _ (h,c) h
    · intro i hi
      by_cases hl : live i
      · rw [if_pos hl]
        exact (treeSimCheck_realCoin_exchange K (ctx i) 1 (st i)).bind (kR i)
      · rw [if_neg hl]
        intro step hs
        change step ∈ support (pure (.done none) : OracleComp (LocalSpec C) (Step C E RealSpec β)) at hs
        have he := (mem_support_pure_iff _ _).mp hs
        subst step
        rfl
    · obtain ⟨i, hi, hl⟩ := all
      exact ⟨i, hi, if_neg hl⟩



def resumeBitsR (st : C.Party → RunState C)
    (k : C.Party → PrssOutput C Bit × RunState C → PartyM C E RealSpec β)
    (out : C.Party → Option (PrssOutput C Bit)) : C.Party → PartyM C E RealSpec β :=
  fun i => (out i).elim failure (fun v => k i (v, nextLabel (st i)))

def resumeBitsH (hs : C.Party → RunState C)
    (k : C.Party → PrssOutput C Bit → RunM C E (CheckSpec C E) Unit)
    (out : C.Party → Option (PrssOutput C Bit)) : C.Party → PartyM C E (CheckSpec C E) Unit :=
  fun i => (out i).elim failure (fun v => (k i v).run' (nextLabel (hs i)))

/-- The adapter's bit call samples both complete fresh tables and keeps the hash cache. -/
theorem hybRun_randBits (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C)
    (label0 ℓ n : ℕ) (stA : A.State) (hs : C.Party → RunState C)
    (k : C.Party → PrssOutput C Bit → RunM C E (CheckSpec C E) Unit) (h : HashCache C) :
    hybRun prims K D (adapter prims K D A x prss cache0 label0) (n+1) (stA,ℓ)
      (fun i => ((hybridCheckGadgets K i).randBits 256 >>= k i).run' (hs i)) h =
    (do
      let t ← $ᵗ (C.Term → Fin 256 → Bit)
      let p ← $ᵗ (C.Pair → Fin 256 → Bit)
      let known := knownRows D (bitRow prims D prss cache0 ℓ 2 256)
      hybRun prims K D (adapter prims K D A x prss cache0 label0) n (stA,ℓ+1)
        (resumeBitsH hs k (randFinish D 256 known.1 known.2 t p)) h) := by
  unfold hybRun
  rw [executePhase_randBits, runFunctionality_rand_local D _ _ _ (by intro i hi; simp [hi]),
    firstInput_honest_const]
  simp only [adapter, TreeCheckWalkRecipe.checkAdversary, rightAdversary,
    bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    run_liftComp_prob, bind_map_left]
  apply bind_congr
  intro t
  apply bind_congr
  intro p
  congr 3
  funext i
  unfold afterRandom resumeBitsH
  cases randFinish D 256 (knownRows D (bitRow prims D prss cache0 ℓ 2 256)).1
    (knownRows D (bitRow prims D prss cache0 ℓ 2 256)).2 t p i <;> rfl

/-- The all-live bit segment preserves complete term and pair rows. -/
theorem coupled_randBits_all (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' ℓ : ℕ)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = ℓ)
    (kR : C.Party → PrssOutput C Bit × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → PrssOutput C Bit → RunM C E (CheckSpec C E) Unit)
    (next : ∀ out : C.Party → Option (PrssOutput C Bit),
      Coupled prims K D A x prss cache0 label0 (n+1) n' (ℓ+1)
        (resumeBitsR st kR out) (resumeBitsH hs kH out)) :
    Coupled prims K D A x prss cache0 label0 (n+1) (n'+1) ℓ
      (fun i => ((realCheckGadgets K (ctx i)).randBits 256).run (st i) >>= kR i)
      (fun i => ((hybridCheckGadgets K i).randBits 256 >>= kH i).run' (hs i)) := by
  intro stA h c grow fresh
  let known := knownRows D (bitRow prims D prss cache0 ℓ 2 256)
  let inst := fun vals => bitCache D (streamKey D prss) ℓ 2 256 vals c
  let out := fun t p => randFinish D 256 known.1 known.2 t p
  have smp := relTriple_of_map_left (relTriple_eqRel_of_evalDist_eq
    (evalDist_keyName_tables (C := C) (R := Bit) 256))
  have full := relTriple_bind smp (S := Final D A)
    (fa := fun vals => realRun prims D A (n+1) stA
      (resumeBitsR st kR (out (termTable vals) (pairTable vals))) (h,inst vals))
    (fb := fun tp => hybRun prims K D (adapter prims K D A x prss cache0 label0) n'
      (stA,ℓ+1) (resumeBitsH hs kH (out tp.1 tp.2)) h) (by
        rintro vals tp he
        subst tp
        exact next _ stA h (inst vals) grow (futureEmpty_bitBlock D (streamKey D prss) ℓ 2 256 vals c fresh))
  apply relTriple_of_evalDist_eq_left
    (realRun_presample_bits prims D A (n+1) stA _ (streamKey D prss) ℓ 2 256 h c fresh)
  have real : ∀ vals : KeyName C → Fin 256 → Bit,
      realRun prims D A (n+1) stA
        (fun i => ((realCheckGadgets K (ctx i)).randBits 256).run (st i) >>= kR i) (h,inst vals) =
      realRun prims D A (n+1) stA (resumeBitsR st kR (out (termTable vals) (pairTable vals))) (h,inst vals) := by
    intro vals
    apply realRun_localPass_congr prims D A cache0 (inst vals) _ _ _ (n+1) stA (h,inst vals) grow le_rfl
    intro i hi s hg hc
    change (simulateQ (streamWorld prims D) (worldRoles.honest (advance
      (((prssRandomness (ctx i) (bitCodec (E := E)) 2 256).run (st i) >>= kR i).run)))).run s = _
    rw [realRand_run, bind_assoc]
    simp only [pure_bind]
    have hh : (ctx i).self ∉ D.1 := by rw [self i hi]; exact hi
    have ready := prssBits_rows_used (E := E) prims D prss cache0 s.1 (ctx i) hh (terms i hi) (pairs i hi)
      cached hg ℓ 2 256 vals c s.2 hc
    rw [self i hi] at ready
    rw [labels i hi]
    rw [advance_ready_bind prims D _ _ _ s ready]
    rw [bitRows_frandShare prims D prss cache0 ℓ 2 256 vals i hi]
    have hout : out (termTable vals) (pairTable vals) i = some
        (frandShare D 256 known.1 known.2 (termTable vals) (pairTable vals) i) := by
      simp only [out, randFinish, if_neg hi]
      rfl
    simp only [resumeBitsR, hout, Option.elim_some]
    rfl
  rw [funext real, hybRun_randBits]
  simpa only [known, inst, out, bind_assoc, pure_bind] using full


/-- The bit segment retains aborted parties and uses the next real exchange to stop survivors. -/
theorem coupled_randBits (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' ℓ : ℕ)
    (live : C.Party → Prop)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = ℓ)
    (kR : C.Party → PrssOutput C Bit × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → PrssOutput C Bit → RunM C E (CheckSpec C E) Unit)
    (exchange : ∀ i, i ∉ D.1 → live i → ∀ out,
      TreeSimCheckExchange (kR i (out,nextLabel (st i))))
    (next : ∀ out : C.Party → Option (PrssOutput C Bit),
      Coupled prims K D A x prss cache0 label0 (n+1) n' (ℓ+1)
        (resumeBitsR st kR out) (resumeBitsH hs kH out)) :
    Coupled prims K D A x prss cache0 label0 (n+1) (n'+1) ℓ
      (fun i => if live i then ((realCheckGadgets K (ctx i)).randBits 256).run (st i) >>= kR i else failure)
      (fun i => if live i then ((hybridCheckGadgets K i).randBits 256 >>= kH i).run' (hs i) else failure) := by
  by_cases all : ∀ i, i ∉ D.1 → live i
  · apply coupled_congr_honest prims K D A x prss cache0 label0 (n+1) (n'+1) ℓ _ _ _ _
      (fun i hi => if_pos (all i hi)) (fun i hi => if_pos (all i hi))
    exact coupled_randBits_all prims K D A x prss cache0 label0 ctx self terms pairs cached
      n n' ℓ st hs labels kR kH next
  · push Not at all
    intro stA h c grow fresh
    apply doomed_post prims D K A (adapter prims K D A x prss cache0 label0) n n' stA (stA,ℓ) _ _ (h,c) h
    · intro i hi
      by_cases hl : live i
      · rw [if_pos hl]
        change TreeSimCheckExchange
          ((prssRandomness (ctx i) (bitCodec (E := E)) 2 256).run (st i) >>= kR i)
        rw [realRand_run, bind_assoc]
        simp only [pure_bind]
        apply TreeSimCheckExchange.oracle_bind
        intro rnd
        exact exchange i hi hl rnd
      · rw [if_neg hl]
        intro step hs
        change step ∈ support (pure (.done none) : OracleComp (LocalSpec C) (Step C E RealSpec β)) at hs
        have he := (mem_support_pure_iff _ _).mp hs
        subst step
        rfl
    · obtain ⟨i, hi, hl⟩ := all
      exact ⟨i, hi, if_neg hl⟩

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.named_coin_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms named_coin_round

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.realRun_coin_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_coin_ready

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.adapter_coin_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms adapter_coin_call

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.coupled_coin_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_coin_all

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.coupled_coin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_coin

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.hybRun_randBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hybRun_randBits

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.coupled_randBits_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_randBits_all

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetCoin.coupled_randBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_randBits

end ThresholdLeanXmssSecurity.TreeCheckGadgetCoin
