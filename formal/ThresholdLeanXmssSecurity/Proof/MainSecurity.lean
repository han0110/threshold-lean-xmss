import ThresholdLeanXmssSecurity.Proof.Main

/-!
# A batch: the distance half of `MainStatement`

`MainSecurityDistance` splits at a hybrid game. The hybrid runs `mainSimulator`, but each accepting
honest operator outputs the copies that it opened, as in the real run.

1. `mainHybridIdeal` (proved): the hybrid and the ideal run differ only when an opened copy differs
   from the rebuilt sharing. Outside a collision in the `.copy` domain, `main_openCopy_sound` rules
   this out (`mainOpenSound_holds`), and `main_copy_birthday` bounds the collision by `copyHashError`.
2. `MainRealHybrid`: the real run and the hybrid accept with the same probability (GS20, Theorem 2).
   It moves to one shared cache (`mainRealHybrid_of_core`, proved) and splits at `mainRealGame`, the
   real phase in the shape of the simulator:
   * `MainEngineReal` (open): the network runs the real phase as `mainRealGame`. Proved pieces:
     `main_startSteps`, `main_fmultBit_run`, `main_sum_run_left`, `main_sumLeft_leak`,
     `main_sumLeft_liftComp`, `main_callImpl_leak`.
   * `MainRealSim` (open): `mainRealGame` and the simulator give the same run. The uniform terms of
     the layers stay hidden, the leaks are the known views, the differences are `mainDifference`
     (`mainDifference_correct`), and after acceptance the copies of `Rerand` are `mainRebuild` of the
     outputs.

`mainSecurityDistance` and `mainStatementProof` take the two open stages as hypotheses.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-! ## Runs in the world

The local copies of `probEvent_runWorld_fst` and `abs_accepts_bind_sub_le` of `KeygenSecurity`. -/

theorem main_probEvent_runWorld_fst (prims : Primitives) {β : Type} (oa : OracleComp (WorldSpec C) β)
    (Q : β → Prop) :
    Pr[fun r => Q r.1 | runWorld prims oa] = Pr[Q | (simulateQ (worldAnswer prims) oa).run' ∅] := by
  rw [← fst_map_runWorld, probEvent_map]
  rfl

theorem main_simulateQ_liftComp_local {α : Type}
    (impl : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp))
    (oa : OracleComp (LocalSpec C) α) :
    simulateQ (impl + programAnswer (C := C)) (liftComp oa (SimulatorSpec C)) = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, simulateQ_bind]
    simp only [ih]
    congr 1
    rw [liftComp_query]
    rcases t with t | t | t <;>
    exact ((simulateQ_query _ _).trans (id_map _)).trans ((simulateQ_query _ _).trans (id_map _)).symm

theorem main_simulateQ_adversary (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary oa) = simulateQ (localAnswer prims) oa := by
  simp only [worldAnswer, worldRoles, simulateQ_counted]
  exact main_simulateQ_liftComp_local _ oa

theorem main_run'_bind_world (prims : Primitives) {R β : Type} (g : OracleComp (WorldSpec C) R)
    (k : R → OracleComp (WorldSpec C) β) :
    (simulateQ (worldAnswer prims) (g >>= k)).run' ∅ =
      (simulateQ (worldAnswer prims) g).run ∅ >>= fun p => (simulateQ (worldAnswer prims) (k p.1)).run' p.2 := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Two continuations of one game differ by at most the probability that they differ. -/
theorem main_abs_accepts_bind_sub_le (prims : Primitives) {R : Type} (g : OracleComp (WorldSpec C) R)
    (k₁ k₂ : R → OracleComp (WorldSpec C) Bool) :
    |accepts prims (g >>= k₁) - accepts prims (g >>= k₂)| ≤
      (Pr[fun r => k₁ r.1 ≠ k₂ r.1 | runWorld prims g]).toReal := by
  let flag (k : R → OracleComp (WorldSpec C) Bool) : OracleComp (WorldSpec C) (Bool × Bool) :=
    g >>= fun r => (fun b => (b, decide (k₁ r ≠ k₂ r))) <$> k r
  have hfst (k : R → OracleComp (WorldSpec C) Bool) : Prod.fst <$> flag k = g >>= k := by
    simp only [flag, map_bind, Functor.map_map, id_map']
  have hbad (k : R → OracleComp (WorldSpec C) Bool) :
      Pr[fun r => r.1.2 = true | runWorld prims (flag k)] =
        Pr[fun r => k₁ r.1 ≠ k₂ r.1 | runWorld prims g] := by
    rw [main_probEvent_runWorld_fst prims (flag k) (fun p => p.2 = true),
      main_probEvent_runWorld_fst prims g (fun r => k₁ r ≠ k₂ r), main_run'_bind_world]
    rw [StateT.run'_eq, probEvent_map, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    apply tsum_congr
    intro p
    rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, probEvent_map]
    by_cases hp : k₁ p.1 ≠ k₂ p.1
    · simp [Function.comp_def, hp]
    · simp [Function.comp_def, hp]
  have heq : Pr[fun r => r.1 = (true, false) | runWorld prims (flag k₁)] =
      Pr[fun r => r.1 = (true, false) | runWorld prims (flag k₂)] := by
    rw [main_probEvent_runWorld_fst prims (flag k₁) (fun p => p = (true, false)),
      main_probEvent_runWorld_fst prims (flag k₂) (fun p => p = (true, false)), main_run'_bind_world,
      main_run'_bind_world, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    apply tsum_congr
    intro p
    congr 1
    by_cases hp : k₁ p.1 = k₂ p.1
    · rw [hp]
    · rw [simulateQ_map, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, StateT.run_map,
        probEvent_map, probEvent_map, probEvent_map, probEvent_map]
      simp [Function.comp_def, hp]
  have h := abs_accepts_sub_le_of_eq_until_bad prims (flag k₁) (flag k₂) heq
  rw [hfst, hfst, hbad, hbad, max_self] at h
  exact h

/-! ## The simulator with the opened copies -/

theorem main_seq_isSome {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {n : ℕ}
    (f : Fin n → m (Option α)) (g : Fin n → m Bool) (h : ∀ i, g i = f i >>= fun o => pure o.isSome)
    (k : (Fin n → Bool) → m β) (k' : (Fin n → Option α) → m β)
    (hk : ∀ v, k (fun i => (v i).isSome) = k' v) :
    Concrete.sequenceFin g >>= k = Concrete.sequenceFin f >>= k' := by
  rw [show g = fun i => f i >>= fun o => pure ((fun _ o => o.isSome) i o) from funext h,
    sequenceFin_bind_pure, bind_assoc]
  simp only [pure_bind, hk]

/-- The receivers of a result with opened values. -/
def mainAccepted {σ : Type} (r : σ × (C.Party → Option (ℕ → Bit))) : σ × Finset C.Party :=
  (r.1, Finset.univ.filter fun i => (r.2 i).isSome)

/-- `mainSimOpen`, where each accepting operator also returns its opened values. -/
def mainOpenVr (n : ℕ) (V : Shares C Bit) : C.Party → Shares C Bit :=
  fun i T g => if i ∈ C.holders T ∧ g < n then V T g else 0

def mainOpenInbox (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party) (n : ℕ)
    (vr : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) : Mail C E := fun k =>
  if k ∈ D.1 then sent k i else if k ∈ receivers then repOutbox K k (vr k) n (ds k) i else some .abort

/-- The end of `OpenRep` at operator `i`, with its opened values. -/
def mainOpenOne (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party) (n : ℕ)
    (vr : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) :
    OracleComp (LocalSpec C) (Option (ℕ → Bit)) :=
  if ¬ (i ∉ D.1 ∧ i ∈ receivers) then pure none else
  if C.parties.any (fun k => Msg.isAbort (mainOpenInbox K D receivers n vr ds sent i k)) then pure none else
  mainCopyHashes (repCopy K i (vr i) n (mainOpenInbox K D receivers n vr ds sent i)) n >>= fun cds =>
    pure (if repCheck K i (mainOpenInbox K D receivers n vr ds sent i) cds then
      some (fun g => ∑ T, repCopy K i (vr i) n (mainOpenInbox K D receivers n vr ds sent i) T g) else none)

def mainSimOpenX (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (jobs : List Circuit) (st : A.State) (receivers : Finset C.Party)
    (known : C.Party → Shares C Bit) (outputs : List (List Bit)) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) :=
  liftComp ($ᵗ (C.Term → Fin (outputsOf jobs).length → Bit)) (LocalSpec C) >>= fun fresh =>
  Concrete.sequenceFin (fun i => if i ∉ D.1 ∧ i ∈ receivers then
    mainCopyHashes (mainOpenVr (outputsOf jobs).length
      (mainRebuild D (outputsOf jobs).length known outputs fresh) i) (outputsOf jobs).length
    else pure []) >>= fun ds =>
  if ¬ ∃ i, i ∉ D.1 ∧ i ∈ receivers then pure (st, fun _ => none) else
  A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
    repOutbox K i (mainOpenVr (outputsOf jobs).length
      (mainRebuild D (outputsOf jobs).length known outputs fresh) i) (outputsOf jobs).length (ds i) c
    else none) >>= fun p =>
  Concrete.sequenceFin (mainOpenOne K D receivers (outputsOf jobs).length
    (mainOpenVr (outputsOf jobs).length (mainRebuild D (outputsOf jobs).length known outputs fresh))
    ds p.2) >>= fun opened =>
  pure (p.1, opened)

theorem mainSimOpen_eq (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (st : A.State) (receivers : Finset C.Party)
    (known : C.Party → Shares C Bit) (outputs : List (List Bit)) :
    mainSimOpen K D A mode jobs st receivers known outputs =
      mainAccepted <$> mainSimOpenX K D A jobs st receivers known outputs := by
  unfold mainSimOpen mainSimOpenX mainOpenOne mainOpenInbox mainOpenVr
  simp only [map_bind]
  refine bind_congr fun fresh => bind_congr fun ds => ?_
  by_cases h : ∃ i, i ∉ D.1 ∧ i ∈ receivers
  · rw [if_neg (not_not.2 h), if_neg (not_not.2 h)]
    simp only [map_bind, pure_bind]
    refine bind_congr fun p => ?_
    refine main_seq_isSome _ _ (fun i => ?_) _ _ (fun v => ?_)
    · split_ifs
      all_goals try simp
      congr 1
      funext a
      split_ifs <;> simp_all
    · simp [mainAccepted]
  · rw [if_pos h, if_pos h]
    simp [mainAccepted]

/-- `mainSimTail` with the opened values. -/
def mainSimTailX (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (jobs : List Circuit) (st : A.State) (data : MainSimData C)
    (outputs : List (List Bit)) : OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) := do
  let X := fun i => outputShares K jobs (data.wires i)
  let Y := fun _ : C.Party => one K
  let n := (outputsOf jobs).length
  let (st, reply) ← A.answer st (.inl (.inr (mainMultLeak D n X Y)))
  let r := match reply with | .inl (.inr r) => r | _ => default
  if ¬ mainAllReceive D r.2.2.2 then return (st, fun _ => none)
  let Z := mainKnownMult K D .peer n r
  let tuples := fun i => data.tuples i ++ [⟨knownView D.1 n (X i), knownView D.1 n (Y i), Z i, n, .peer⟩]
  let differences := data.differences ++ [mainDifference K D .peer n X Y r]
  let agree := mainKnownAgree D tuples
  let accept := decide (agree ∧ ∀ d ∈ differences, ∀ g, d g = 0)
  let (st, reply) ← A.answer st (.inr (fun i => if i ∈ D.1 then none else some (tuples i),
    if agree then differences else [], accept))
  let receivers := match reply with | .inr rs => rs | _ => ∅
  if ¬ accept then return (st, fun _ => none)
  mainSimOpenX K D A jobs st receivers Z outputs

theorem mainSimTail_eq (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (st : A.State) (data : MainSimData C)
    (outputs : List (List Bit)) :
    mainSimTail K D A mode jobs st data outputs =
      mainAccepted <$> mainSimTailX K D A jobs st data outputs := by
  unfold mainSimTail mainSimTailX
  simp only [map_bind]
  refine bind_congr fun p => ?_
  obtain ⟨st', reply⟩ := p
  rcases reply with (r | r) | rs <;> dsimp only
  all_goals
    split
    · simp [mainAccepted]
    · simp only [map_bind, pure_bind]
      refine bind_congr fun p' => ?_
      split
      · simp [mainAccepted]
      · exact mainSimOpen_eq K D A mode jobs _ _ _ _

/-- The answer of `mainSimulator` with the opened values. -/
def mainSimAnswerX (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (st : A.State) (l : MainIdealLeak C) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) := do
  let data : MainSimData C := ⟨fun i => (l.1 i).getD [], fun _ => [], []⟩
  let (st, out) ← mainSimLayers K D A mode jobs (List.range (depth jobs)) st data
  match out with
  | none => pure (st, fun _ => none)
  | some data => mainSimTailX K D A jobs st data l.2

/-- The common part of the hybrid and of the ideal run: the start of the adversary and the
simulator with the opened values. -/
def mainCommon (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) := do
  let st ← A.start (corruptInputs D x) z
  mainSimAnswerX K D A mode jobs st (mainIdealLeak D jobs x)

/-- The outputs of the ideal run. -/
def mainIdealOut {σ : Type} (D : C.Coalition) (jobs : List Circuit) (x : C.Party → MainInput C)
    (r : σ × (C.Party → Option (ℕ → Bit))) : σ × (C.Party → Option (List (List Bit))) :=
  (r.1, fun i => if i ∉ D.1 ∧ (r.2 i).isSome then some (mainIdealLeak D jobs x).2 else none)

/-- The outputs of the hybrid run: the opened values of each accepting operator. -/
def mainHybridOut {σ : Type} (D : C.Coalition) (jobs : List Circuit)
    (r : σ × (C.Party → Option (ℕ → Bit))) : σ × (C.Party → Option (List (List Bit))) :=
  (r.1, fun i => if i ∉ D.1 then (r.2 i).map (assemble jobs) else none)

theorem mainSimulator_answer_eq (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (st : A.State) (l : MainIdealLeak C) :
    (mainSimulator K D A mode jobs).answer st l = mainAccepted <$> mainSimAnswerX K D A mode jobs st l := by
  change (do
    let data : MainSimData C := ⟨fun i => (l.1 i).getD [], fun _ => [], []⟩
    let (st, out) ← mainSimLayers K D A mode jobs (List.range (depth jobs)) st data
    match out with
    | none => pure (st, ∅)
    | some data => mainSimTail K D A mode jobs st data l.2) = _
  unfold mainSimAnswerX
  simp only [map_bind]
  refine bind_congr fun p => ?_
  obtain ⟨st', out⟩ := p
  rcases out with _ | data <;> dsimp only
  · simp [mainAccepted]
  · exact mainSimTail_eq K D A mode jobs _ _ _

theorem mainIdealLocal_eq_common (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux) :
    mainIdealLocal K D A mode jobs x z = mainIdealOut D jobs x <$> mainCommon K D A mode jobs x z := by
  unfold mainIdealLocal mainCommon
  simp only [map_bind, mainSimulator_answer_eq]
  refine bind_congr fun st => ?_
  erw [bind_map_left, map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  simp [mainIdealOut, mainAccepted]

/-- The hybrid game. -/
def mainHybridGame (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux)
    (Z : Distinguisher C A.State (List (List Bit))) : OracleComp (WorldSpec C) Bool :=
  worldRoles.adversary (mainCommon K D A mode jobs x z) >>= fun r =>
    worldRoles.adversary (Z (mainHybridOut D jobs r))

theorem mainIdealGame_eq (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux)
    (Z : Distinguisher C A.State (List (List Bit))) :
    distinguish (idealExecution worldRoles.adversary D (Fmain jobs) (mainSimulator K D A mode jobs) x z) Z =
      worldRoles.adversary (mainCommon K D A mode jobs x z) >>= fun r =>
        worldRoles.adversary (Z (mainIdealOut D jobs x r)) := by
  rw [distinguish, mainIdealLocal_eq, mainIdealLocal_eq_common, map_eq_bind_pure_comp,
    main_worldRoles_bind, bind_assoc]
  refine bind_congr fun r => ?_
  rw [Function.comp_apply, main_worldRoles_pure, pure_bind]

/-- The common part makes at most `q + termHashes C` counted calls. -/
theorem mainCommon_bound (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux)
    (Z : Distinguisher C A.State (List (List Bit))) (q : ℕ)
    (hq : IsQueryBounded A Z (mainRounds jobs) q) :
    IsQueryBoundP (mainCommon K D A mode jobs x z) Counted (q + termHashes C) := by
  obtain ⟨start, step, final, hq, hstart, hround, hanswer, hZ⟩ := hq
  unfold mainCommon
  apply IsQueryBoundP.mono (n := start + ((depth jobs + 3) * step + 2 * C.n * C.n.choose (C.t - 1))) _
    (by simp only [termHashes, termCount, mainRounds] at hq ⊢; omega)
  refine main_bound_bind (hstart _ _) fun st => ?_
  have h := mainSimulator_answer_bound K D A step hanswer hround mode jobs st (mainIdealLeak D jobs x)
  rw [mainSimulator_answer_eq] at h
  exact (isQueryBoundP_map_iff (p := Counted) _ mainAccepted _).1 h

/-- Outside a collision in the `.copy` domain, every opened value of the hybrid is an output of
`F_main`. -/
def MainOpenSound (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit) (D : C.Coalition) (A : MainAdversary C E)
    (x : C.Party → MainInput C) (z : Aux),
    ∀ p ∈ support ((simulateQ (localAnswer prims) (mainCommon K D A mode jobs x z)).run ∅),
      mainHybridOut D jobs p.1 ≠ mainIdealOut D jobs x p.1 → MainCopyCollision p.2

theorem mainHybridIdeal (prims : Primitives) (K : Constants C E) (hsound : MainOpenSound prims K)
    (mode : ReshareMode) (jobs : List Circuit) (D : C.Coalition) (A : MainAdversary C E)
    (x : C.Party → MainInput C) (z : Aux) (Z : Distinguisher C A.State (List (List Bit))) (q : ℕ)
    (hq : IsQueryBounded A Z (mainRounds jobs) q) :
    |accepts prims (worldRoles.adversary (mainCommon K D A mode jobs x z) >>= fun r =>
        worldRoles.adversary (Z (mainHybridOut D jobs r))) -
      accepts prims (worldRoles.adversary (mainCommon K D A mode jobs x z) >>= fun r =>
        worldRoles.adversary (Z (mainIdealOut D jobs x r)))| ≤ copyHashError C q := by
  refine (main_abs_accepts_bind_sub_le prims _ _ _).trans ?_
  set oa := mainCommon K D A mode jobs x z
  have h1 : Pr[fun r => (worldRoles.adversary (Z (mainHybridOut D jobs r.1)) : OracleComp (WorldSpec C) Bool) ≠
        worldRoles.adversary (Z (mainIdealOut D jobs x r.1)) | runWorld prims (worldRoles.adversary oa)] ≤
      Pr[fun z => MainCopyCollision z.2 | (simulateQ (localAnswer prims) oa).run ∅] := by
    rw [main_probEvent_runWorld_fst prims _ (fun r => (worldRoles.adversary (Z (mainHybridOut D jobs r)) :
        OracleComp (WorldSpec C) Bool) ≠ worldRoles.adversary (Z (mainIdealOut D jobs x r))),
      main_simulateQ_adversary, StateT.run'_eq, probEvent_map]
    refine probEvent_mono fun p hp hne => hsound mode jobs D A x z p hp fun heq => hne ?_
    simp only [heq]
  refine (ENNReal.toReal_mono probEvent_ne_top h1).trans ?_
  refine (main_copy_birthday prims oa _ (mainCommon_bound K D A mode jobs x z Z q hq)).trans ?_
  simp [copyHashError]

/-- The real run and the hybrid accept with the same probability (GS20, Theorem 2). -/
def MainRealHybrid (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit) (D : C.Coalition) (A : MainAdversary C E)
    (x : C.Party → MainInput C) (z : Aux) (Z : Distinguisher C A.State (List (List Bit))),
    MainInputs jobs D x →
    accepts prims (distinguish (realExecution D A (mainFunctionalities K mode)
        (mainRounds jobs) (mainProtocol K mode jobs) x z) Z) =
      accepts prims (mainHybridGame K D A mode jobs x z Z)

/-! ## The opened values of the hybrid -/

theorem liftComp_mapM_local {α β : Type} (f : α → OracleComp (RoSpec C) β) :
    ∀ L : List α, liftComp (L.mapM f) (LocalSpec C) = L.mapM fun a => liftComp (f a) (LocalSpec C)
  | [] => by simp
  | a :: L => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure]
    refine bind_congr fun b => ?_
    rw [← liftComp_mapM_local f L]

theorem mainCopyHashes_support (prims : Primitives) (v : Shares C Bit) (n : ℕ) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (mainCopyHashes v n)).run s)) :
    z.1.length = C.terms.length ∧ s ≤ z.2 ∧
      ∀ T, ∃ u, z.1[C.terms.idxOf T]? = some u ∧ z.2 (.copy (vector n (v T))) = some u := by
  unfold mainCopyHashes at hz
  rw [← liftComp_mapM_local] at hz
  obtain ⟨hlen, hle, hc⟩ := support_hashes prims C.terms (fun T => .copy (vector n (v T)))
    (fun T ⟨_, h, _⟩ => by cases h) s z hz
  refine ⟨hlen, hle, fun T => ?_⟩
  have hm : C.terms.idxOf T < C.terms.length := List.idxOf_lt_length_of_mem (mem_terms T)
  refine ⟨_, List.getElem?_eq_getElem (hlen ▸ hm), ?_⟩
  have := hc _ hm
  rwa [List.getElem_idxOf] at this

/-- An accepted opening outside a copy collision gives the shared value. -/
theorem mainOpen_value (K : Constants C E) (D : C.Coalition) (n : ℕ) (V : Shares C Bit)
    (target : ℕ → Bit) (hV : ∀ g < n, shareValue V g = target g)
    (vr : C.Party → Shares C Bit) (hvr : ∀ h T g, h ∉ D.1 → h ∈ C.holders T → g < n → vr h T g = V T g)
    (ds : C.Party → List HashOutput) (hlen : ∀ h, h ∉ D.1 → (ds h).length = C.terms.length)
    (i : C.Party) (hiD : i ∉ D.1) (inbox : Mail C E)
    (hinbox : ∀ h, h ∉ D.1 → inbox h = repOutbox K h (vr h) n (ds h) i)
    (cds : List HashOutput) (hcdlen : cds.length = C.terms.length)
    (s : HashCache C) (hs : ¬ MainCopyCollision s)
    (hds : ∀ h T, h ∉ D.1 → ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      s (.copy (vector n (vr h T))) = some u)
    (hcds : ∀ T, ∃ u, cds[C.terms.idxOf T]? = some u ∧
      s (.copy (vector n (repCopy K i (vr i) n inbox T))) = some u)
    (hcheck : repCheck K i inbox cds) :
    ∀ g < n, ∑ T, repCopy K i (vr i) n inbox T g = target g := by
  intro g hg
  rw [← hV g hg, shareValue]
  let ds' : C.Party → List HashOutput := fun h =>
    if h ∉ D.1 then ds h else List.replicate C.terms.length 0
  refine Finset.sum_congr rfl fun T _ => ?_
  refine main_openCopy_sound K D V vr n hvr ds' (fun h => ?_) i hiD inbox (fun h hh => ?_) cds hcdlen s hs
    (fun h T hh => ?_) hcds hcheck T g hg
  · by_cases hh : h ∉ D.1
    · simp only [ds', if_pos hh, hlen h hh]
    · simp only [ds', if_neg hh, List.length_replicate]
  · simp only [ds', if_pos hh, hinbox h hh]
  · simp only [ds', if_pos hh]
    exact hds h T hh

/-- The opened values of the honest operators are the target values. -/
def MainOpenedGood (D : C.Coalition) (n : ℕ) (target : ℕ → Bit) (r : C.Party → Option (ℕ → Bit)) : Prop :=
  ∀ i, i ∉ D.1 → ∀ o, r i = some o → ∀ g < n, o g = target g

/-- Every run from every cache ends in `P`. -/
def MainRunInv (prims : Primitives) {α : Type} (P : α → HashCache C → Prop)
    (oa : OracleComp (LocalSpec C) α) : Prop :=
  ∀ s z, z ∈ support ((simulateQ (localAnswer prims) oa).run s) → P z.1 z.2

theorem MainRunInv.bind {prims : Primitives} {α β : Type} {P : β → HashCache C → Prop}
    {oa : OracleComp (LocalSpec C) α} {f : α → OracleComp (LocalSpec C) β}
    (h : ∀ a, MainRunInv prims P (f a)) : MainRunInv prims P (oa >>= f) := by
  intro s z hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p, -, hz⟩ := hz
  exact h p.1 p.2 z hz

theorem MainRunInv.ite {prims : Primitives} {α : Type} {P : α → HashCache C → Prop} (c : Prop) [Decidable c]
    {a b : OracleComp (LocalSpec C) α} (ha : c → MainRunInv prims P a) (hb : ¬ c → MainRunInv prims P b) :
    MainRunInv prims P (if c then a else b) := by
  split_ifs with hc
  · exact ha hc
  · exact hb hc

theorem MainRunInv.pure {prims : Primitives} {α : Type} {P : α → HashCache C → Prop} (x : α)
    (h : ∀ s, P x s) : MainRunInv prims P (pure x : OracleComp (LocalSpec C) α) := by
  intro s z hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact h s

theorem mainOpenedGood_none (D : C.Coalition) (n : ℕ) (target : ℕ → Bit) :
    MainOpenedGood D n target (fun _ => none) := fun _ _ _ h => by cases h

theorem mainOpenedGood_pure_none (prims : Primitives) {σ : Type} (D : C.Coalition) (n : ℕ)
    (target : ℕ → Bit) (st : σ) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims)
      (pure (st, fun _ => none) : OracleComp (LocalSpec C) (σ × (C.Party → Option (ℕ → Bit))))).run s)) :
    MainOpenedGood D n target z.1.2 := by
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact mainOpenedGood_none D n target

set_option linter.constructorNameAsVariable false in
theorem mainSimOpenX_inv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (jobs : List Circuit) (st : A.State) (receivers : Finset C.Party)
    (known : C.Party → Shares C Bit) (outputs : List (List Bit)) :
    MainRunInv prims (fun z s => ¬ MainCopyCollision s →
      MainOpenedGood D (outputsOf jobs).length (fun g => outputs.flatten.getD g 0) z.2)
      (mainSimOpenX K D A jobs st receivers known outputs) := by
  intro s z hz hs
  unfold mainSimOpenX at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨fresh, s₁⟩, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨ds, s₂⟩, h₂, hz⟩ := hz
  dsimp only at h₂ hz
  obtain ⟨V, hV⟩ : ∃ V, V = mainRebuild D (outputsOf jobs).length known outputs fresh := ⟨_, rfl⟩
  obtain ⟨vr, hvr⟩ : ∃ vr, vr = mainOpenVr (outputsOf jobs).length V := ⟨_, rfl⟩
  rw [← hV, ← hvr] at h₂ hz
  rw [simulateQ_sequenceFin] at h₂
  have hds := support_sequenceFin_state s₁ _
    (fun i a s' => i ∉ D.1 ∧ i ∈ receivers → a.length = C.terms.length ∧
      ∀ T, ∃ u, a[C.terms.idxOf T]? = some u ∧
        s' (.copy (vector (outputsOf jobs).length (vr i T))) = some u)
    (fun i s _ z hz => by
      split_ifs at hz with hi
      · obtain ⟨hlen, hle, hc⟩ := mainCopyHashes_support prims _ _ s z hz
        exact ⟨hle, fun _ => ⟨hlen, hc⟩⟩
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨le_rfl, fun h => absurd h hi⟩)
    (fun i a s s' h hle hi => by
      obtain ⟨h1, h2⟩ := h hi
      exact ⟨h1, fun T => (h2 T).imp fun u hu => ⟨hu.1, hle hu.2⟩⟩)
    s₁ le_rfl _ h₂
  obtain ⟨-, hds⟩ := hds
  dsimp only at hds
  by_cases hex : ∃ i, i ∉ D.1 ∧ i ∈ receivers
  swap
  · rw [if_pos hex] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    intro i _ o ho
    simp at ho
  rw [if_neg (not_not.2 hex)] at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨p, s₃⟩, h₃, hz⟩ := hz
  have hle₃ : s₂ ≤ s₃ := Grows.simulateQ (grows_localAnswer prims) _ s₂ _ h₃
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨op, s₄⟩, h₄, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rw [simulateQ_sequenceFin] at h₄
  dsimp only at h₄ hs ⊢
  have hop := support_sequenceFin_state s₃ _
    (fun i o s' => ∀ o', o = some o' → (i ∉ D.1 ∧ i ∈ receivers) ∧
      (C.parties.any fun k => Msg.isAbort
        (mainOpenInbox K D receivers (outputsOf jobs).length vr ds p.2 i k)) = false ∧
      ∃ cds : List HashOutput, cds.length = C.terms.length ∧
        (∀ T, ∃ u, cds[C.terms.idxOf T]? = some u ∧
          s' (.copy (vector (outputsOf jobs).length (repCopy K i (vr i) (outputsOf jobs).length
            (mainOpenInbox K D receivers (outputsOf jobs).length vr ds p.2 i) T))) = some u) ∧
        repCheck K i (mainOpenInbox K D receivers (outputsOf jobs).length vr ds p.2 i) cds ∧
        o' = fun g => ∑ T, repCopy K i (vr i) (outputsOf jobs).length
          (mainOpenInbox K D receivers (outputsOf jobs).length vr ds p.2 i) T g)
    (fun i s _ z hz => by
      unfold mainOpenOne at hz
      by_cases h1 : i ∉ D.1 ∧ i ∈ receivers
      · rw [if_neg (not_not.2 h1)] at hz
        by_cases h2 : (C.parties.any fun k => Msg.isAbort
            (mainOpenInbox K D receivers (outputsOf jobs).length vr ds p.2 i k)) = true
        · rw [if_pos h2] at hz
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨le_rfl, fun o' h => by cases h⟩
        · rw [if_neg h2] at hz
          rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
          obtain ⟨⟨cds, s'⟩, hc, hz⟩ := hz
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          obtain ⟨hlen, hle, hcs⟩ := mainCopyHashes_support prims _ _ s _ hc
          refine ⟨hle, fun o' ho' => ?_⟩
          dsimp only at ho'
          split_ifs at ho' with hchk
          · exact ⟨h1, by simpa using h2, cds, hlen, hcs, hchk, (Option.some.inj ho').symm⟩
      · rw [if_pos h1] at hz
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨le_rfl, fun o' h => by cases h⟩)
    (fun i a s s' h hle o' ho' => by
      obtain ⟨h1, h2, cds, h3, h4, h5, h6⟩ := h o' ho'
      exact ⟨h1, h2, cds, h3, fun T => (h4 T).imp fun u hu => ⟨hu.1, hle hu.2⟩, h5, h6⟩)
    s₃ le_rfl _ h₄
  obtain ⟨hle₄, hop⟩ := hop
  dsimp only at hle₄ hop
  intro i hiD o ho g hg
  obtain ⟨-, hab, cds, hcdlen, hcds, hchk, rfl⟩ := hop i o ho
  have hrecv : ∀ h, h ∉ D.1 → h ∈ receivers := by
    intro h hh
    by_contra hn
    rw [List.any_eq_false] at hab
    exact hab h (List.mem_finRange h) (by simp [mainOpenInbox, hh, hn, Msg.isAbort])
  dsimp only
  refine mainOpen_value K D (outputsOf jobs).length V (fun g => outputs.flatten.getD g 0) (fun g _ => ?_) vr (fun h T g _ hT hg => ?_) ds
    (fun h hh => (hds h ⟨hh, hrecv h hh⟩).1) i hiD _ (fun h hh => ?_) cds hcdlen s₄ hs
    (fun h T hh => ((hds h ⟨hh, hrecv h hh⟩).2 T).imp fun u hu => ⟨hu.1, (hle₃.trans hle₄) hu.2⟩)
    hcds hchk g hg
  · obtain ⟨T₀, hT₀⟩ := main_lacked_exists D
    rw [hV, mainRebuild]
    exact mainMultSharing_sum D _ _ T₀ hT₀ g
  · simp [hvr, mainOpenVr, hT, hg]
  · simp [mainOpenInbox, hh, hrecv h hh]

set_option linter.constructorNameAsVariable false in
theorem mainSimTailX_inv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (jobs : List Circuit) (st : A.State) (data : MainSimData C) (outputs : List (List Bit)) :
    MainRunInv prims (fun z s => ¬ MainCopyCollision s →
      MainOpenedGood D (outputsOf jobs).length (fun g => outputs.flatten.getD g 0) z.2)
      (mainSimTailX K D A jobs st data outputs) := by
  unfold mainSimTailX
  refine MainRunInv.bind fun p => ?_
  rcases p with ⟨st₁, (r | r) | rs⟩ <;> dsimp only
  all_goals
    refine MainRunInv.ite _ (fun _ => MainRunInv.pure _ fun _ _ => mainOpenedGood_none _ _ _) fun _ => ?_
    refine MainRunInv.bind fun _ => MainRunInv.bind fun p' => ?_
    rcases p' with ⟨st₂, _ | rs'⟩ <;> dsimp only
    all_goals
      refine MainRunInv.ite _ (fun _ => MainRunInv.pure _ fun _ _ => mainOpenedGood_none _ _ _) fun _ => ?_
      refine MainRunInv.bind fun _ => ?_
      exact mainSimOpenX_inv prims K D A jobs _ _ _ _

theorem mainSimAnswerX_inv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (st : A.State) (l : MainIdealLeak C) :
    MainRunInv prims (fun z s => ¬ MainCopyCollision s →
      MainOpenedGood D (outputsOf jobs).length (fun g => l.2.flatten.getD g 0) z.2)
      (mainSimAnswerX K D A mode jobs st l) := by
  unfold mainSimAnswerX
  refine MainRunInv.bind fun p => ?_
  rcases p with ⟨st', _ | data⟩ <;> dsimp only
  · exact MainRunInv.pure _ fun _ _ => mainOpenedGood_none _ _ _
  · exact mainSimTailX_inv prims K D A jobs _ _ _

theorem mainCommon_inv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux) :
    MainRunInv prims (fun r s => ¬ MainCopyCollision s →
      MainOpenedGood D (outputsOf jobs).length (fun g => (mainIdealLeak D jobs x).2.flatten.getD g 0) r.2)
      (mainCommon K D A mode jobs x z) := by
  unfold mainCommon
  exact MainRunInv.bind fun st => mainSimAnswerX_inv prims K D A mode jobs st _

theorem assemble_cons (j : Circuit) (js : List Circuit) (o : ℕ → Bit) :
    assemble (j :: js) o = vector j.outputs.length o :: assemble js (fun g => o (j.outputs.length + g)) := by
  unfold assemble
  rw [List.map_cons, List.zipIdx_cons, List.map_cons, List.zipIdx_succ, List.map_map]
  congr 1
  · simp
  · refine List.map_congr_left fun p _ => ?_
    simp [List.take_succ_cons, Nat.add_assoc]

theorem main_assemble_eq : ∀ (jobs : List Circuit) (L : List (List Bit)) (o : ℕ → Bit),
    List.Forall₂ (fun (l : List Bit) (j : Circuit) => l.length = j.outputs.length) L jobs →
    (∀ g < (jobs.map (·.outputs.length)).sum, o g = L.flatten.getD g 0) → assemble jobs o = L
  | [], [], o, _, _ => rfl
  | j :: js, l :: L, o, h, ho => by
    obtain ⟨hl, hL⟩ := List.forall₂_cons.1 h
    rw [assemble_cons]
    congr 1
    · refine List.ext_getElem (by simp [vector, hl]) fun g h₁ h₂ => ?_
      have hg : g < j.outputs.length := by simpa [vector] using h₁
      simp only [vector, List.getElem_map, List.getElem_range]
      rw [ho g (by simp; omega), List.flatten_cons, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), List.getElem?_eq_getElem h₂, Option.getD_some]
    · refine main_assemble_eq js L _ hL fun g hg => ?_
      rw [ho _ (by simp; omega), List.flatten_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega)]
      congr 2
      omega

theorem main_forall₂_zipIdx (g : Circuit × ℕ → List Bit) (hg : ∀ p, (g p).length = p.1.outputs.length) :
    ∀ (jobs : List Circuit) (n : ℕ),
      List.Forall₂ (fun (l : List Bit) (j : Circuit) => l.length = j.outputs.length) ((jobs.zipIdx n).map g) jobs
  | [], _ => by simp
  | j :: js, n => by
    rw [List.zipIdx_cons, List.map_cons]
    exact List.Forall₂.cons (hg _) (main_forall₂_zipIdx g hg js (n + 1))

theorem main_length_flatMap_zipIdx {β : Type} (f : Circuit → List β) :
    ∀ (jobs : List Circuit) (n : ℕ),
      ((jobs.zipIdx n).flatMap fun p => (f p.1).map fun a => (p.2, a)).length = (jobs.map fun j => (f j).length).sum
  | [], _ => by simp
  | j :: js, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, main_length_flatMap_zipIdx f js (n + 1)]
    simp

theorem main_outputsOf_length (jobs : List Circuit) :
    (outputsOf jobs).length = (jobs.map (·.outputs.length)).sum :=
  main_length_flatMap_zipIdx (·.outputs) jobs 0

theorem mainOpenSound_holds (prims : Primitives) (K : Constants C E) : MainOpenSound prims K := by
  intro mode jobs D A x z p hp hne
  by_contra hs
  apply hne
  have hgood := mainCommon_inv prims K D A mode jobs x z ∅ p hp hs
  have hL := main_forall₂_zipIdx (fun p => p.1.eval (inputValue (reconstruct fun i =>
      ((if i ∈ D.1 then none else some (x i)) : Option (MainInput C)).bind (·[p.2]?))))
    (fun p => by simp [Circuit.eval]) jobs 0
  unfold mainHybridOut mainIdealOut
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · rcases ho : p.1.2 i with _ | o
    · simp [hi]
    · simp only [hi, not_false_eq_true, if_true, Option.map_some, Option.isSome_some, and_self]
      congr 1
      refine main_assemble_eq jobs _ o hL fun g hg => ?_
      exact hgood i hi o ho g (by rw [main_outputsOf_length]; exact hg)

/-! ## The network through one oracle implementation

Local copies of `mapRoles` and `simulateQ_executePhase` of `CheckSecurity`. -/

section MapRoles

variable {E' : Type}

/-- Interpret both network roles through one oracle implementation. -/
def mainMapRoles {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec)) : Roles C m :=
  ⟨fun oa => simulateQ impl (roles.adversary oa), fun oa => simulateQ impl (roles.honest oa)⟩

theorem main_simulateQ_stateT_run {ι κ σ α : Type} {S : OracleSpec ι} {T : OracleSpec κ}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (φ : QueryImpl T m) (impl : QueryImpl S (StateT σ (OracleComp T))) (oa : OracleComp S α) (s : σ) :
    simulateQ φ ((simulateQ impl oa).run s) =
      (simulateQ (fun t => (StateT.mk fun s => simulateQ φ ((impl t).run s) : StateT σ m _)) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind, simulateQ_bind]
    show _ = (StateT.mk fun s => simulateQ φ ((impl t).run s)).run s >>= _
    refine bind_congr fun p => ?_
    exact ih _ _

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
  (φ : QueryImpl spec m) (Ro : Roles C (OracleComp spec))
  {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E' Ia L R) (F : Functionality C I O L R)

theorem main_simulateQ_runFunctionality (st : A.State) (inputs : C.Party → Option I) :
    simulateQ φ (runFunctionality Ro D A F st inputs) =
      runFunctionality (mainMapRoles φ Ro) D A F st inputs := by
  unfold runFunctionality
  by_cases h : ∀ i ∉ D.1, (inputs i).isSome = true
  · rw [if_neg (not_not.mpr h), if_neg (not_not.mpr h)]
    simp only [simulateQ_pure, pure_bind, simulateQ_bind]
    rw [main_simulateQ_stateT_run]
    congr 1
    congr 1
    congr 1
    funext t
    rcases t with t | l
    · apply StateT.ext
      intro s
      change simulateQ φ ((StateT.lift (Ro.honest (OracleComp.lift (OracleSpec.query t)))).run s) =
        (StateT.lift (simulateQ φ (Ro.honest (OracleComp.lift (OracleSpec.query t))))).run s
      simp [StateT.run_lift]
    · apply StateT.ext
      intro s
      change simulateQ φ (Ro.adversary (A.answer s l) >>= fun d => pure (d.2, d.1)) =
        (simulateQ φ (Ro.adversary (A.answer s l)) >>= fun d => pure (d.2, d.1))
      simp
  · simp [h]

theorem main_simulateQ_stepRound (state : A.State) (steps : C.Party → Step C E' (CallSpec I O) α) :
    simulateQ φ (stepRound Ro D A F state steps) = stepRound (mainMapRoles φ Ro) D A F state steps := by
  unfold stepRound
  split_ifs
  · rw [simulateQ_bind, main_simulateQ_runFunctionality]
    refine bind_congr fun r => ?_
    rcases r with ⟨st, out⟩
    dsimp only
    rw [simulateQ_bind, simulateQ_sequenceFin]
    simp only [simulateQ_pure]
    congr 1
    congr 1
    funext j
    cases steps j with
    | done out => simp
    | wait outbox resume => simp
    | call input resume => by_cases hj : j ∈ D.1 <;> simp [hj, mainMapRoles]
  · rw [simulateQ_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨st, sent⟩
    dsimp only
    rw [simulateQ_bind, simulateQ_sequenceFin]
    simp only [simulateQ_pure]
    congr 1
    congr 1
    funext j
    cases steps j with
    | done out => simp
    | wait outbox resume => by_cases hj : j ∈ D.1 <;> simp [hj, mainMapRoles]
    | call input resume => simp

theorem main_simulateQ_executeRounds :
    ∀ fuel state (steps : C.Party → Step C E' (CallSpec I O) α),
    simulateQ φ (executeRounds Ro D A F fuel state steps) =
      executeRounds (mainMapRoles φ Ro) D A F fuel state steps
  | 0, state, steps => by simp [executeRounds]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · simp
    · rw [simulateQ_bind, main_simulateQ_stepRound]
      refine bind_congr fun r => ?_
      exact main_simulateQ_executeRounds fuel r.1 r.2.1

theorem main_simulateQ_startSteps (program : C.Party → PartyM C E' (CallSpec I O) α) :
    simulateQ φ (startSteps Ro D program) = startSteps (mainMapRoles φ Ro) D program := by
  unfold startSteps
  rw [simulateQ_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1 <;> simp [hi, mainMapRoles]

theorem main_simulateQ_executePhase (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E' (CallSpec I O) α) :
    simulateQ φ (executePhase Ro D A F fuel state program) =
      executePhase (mainMapRoles φ Ro) D A F fuel state program := by
  unfold executePhase
  rw [simulateQ_bind, main_simulateQ_startSteps]
  exact bind_congr fun steps => main_simulateQ_executeRounds φ Ro D A F fuel state steps

end MapRoles

theorem main_mapRoles_world (prims : Primitives) :
    mainMapRoles (worldAnswer (C := C) prims) worldRoles = mainMapRoles (localAnswer prims) localRoles := by
  unfold mainMapRoles
  congr 1
  · funext β oa
    exact main_simulateQ_adversary prims oa
  · funext β oa
    exact simulateQ_free _ _ oa

/-! ## The real run and the hybrid on one cache -/

/-- The real run of a batch on the shared cache. -/
def mainRealLocal (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (List (List Bit)))) := do
  let st ← A.start (corruptInputs D x) z
  executePhase localRoles D A (mainFunctionalities K mode) (mainRounds jobs) st
    fun i => mainProtocol K mode jobs i (x i)

theorem main_accepts_eq_local (prims : Primitives) (oa : OracleComp (WorldSpec C) Bool)
    (ob : OracleComp (LocalSpec C) Bool)
    (h : simulateQ (worldAnswer prims) oa = simulateQ (localAnswer prims) ob) :
    accepts prims oa = (Pr[fun b => b = true | (simulateQ (localAnswer prims) ob).run' ∅]).toReal := by
  unfold accepts
  congr 1
  rw [← h, ← fst_map_runWorld, probEvent_map]
  rfl

/-- GS20, Theorem 2, on the shared cache: from each state of the adversary after its start, the
real phase and the simulator with the opened values give the same run. -/
def MainRealHybridCore (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit) (D : C.Coalition) (A : MainAdversary C E)
    (x : C.Party → MainInput C), MainInputs jobs D x → ∀ st : A.State,
    SameRun prims
      (executePhase localRoles D A (mainFunctionalities K mode) (mainRounds jobs) st
        fun i => mainProtocol K mode jobs i (x i))
      (mainHybridOut D jobs <$> mainSimAnswerX K D A mode jobs st (mainIdealLeak D jobs x))

theorem mainRealHybrid_of_core (prims : Primitives) (K : Constants C E)
    (h : MainRealHybridCore prims K) : MainRealHybrid prims K := by
  intro mode jobs D A x z Z hx
  have hreal := main_accepts_eq_local prims (distinguish (realExecution D A (mainFunctionalities K mode)
      (mainRounds jobs) (mainProtocol K mode jobs) x z) Z)
    (mainRealLocal K D A mode jobs x z >>= Z) (by
      unfold distinguish realExecution mainRealLocal
      simp only [simulateQ_bind, bind_assoc, main_simulateQ_executePhase, main_mapRoles_world,
        main_simulateQ_adversary])
  have hhyb := main_accepts_eq_local prims (mainHybridGame K D A mode jobs x z Z)
    ((mainHybridOut D jobs <$> mainCommon K D A mode jobs x z) >>= Z) (by
      unfold mainHybridGame
      simp only [simulateQ_bind, main_simulateQ_adversary, bind_map_left])
  have hsame : SameRun prims (mainRealLocal K D A mode jobs x z >>= Z)
      ((mainHybridOut D jobs <$> mainCommon K D A mode jobs x z) >>= Z) := by
    refine SameRun.bind ?_ fun r => SameRun.refl prims (Z r)
    unfold mainRealLocal mainCommon
    rw [map_bind]
    exact SameRun.bind_right _ fun st => h mode jobs D A x hx st
  rw [hreal, hhyb, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  simp only [probOutput_def, SameRun.run'_eq hsame]

/-! ## The real phase as a game

The real phase written in the shape of the simulator: one answer of the adversary for each call of
`F_mult`, the uniform terms of `F_mult`, the leak of `F_multVerify`, and `OpenRep` with the copies of
the honest operators. -/

/-- The honest outputs of `F_mult` (`Fmult`), with the products of the honest views. -/
def mainFmultOut (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (X Y : C.Party → Shares C Bit) (r : MainMultReply C) (fresh : C.Term → Fin n → Bit) :
    C.Party → Shares C Bit := fun i T g =>
  if i ∈ C.holders T ∧ g < n then
    (if lackedTerm D.1 = some T then
      (∑ j ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext j) (X j) (Y j) g) + r.1 g -
        ∑ T' ∈ Finset.univ.erase T, mainMultBase D n r.2.1 fresh T' g
      else mainMultBase D n r.2.1 fresh T g) +
      (if ∃ j ∈ D.1, filler K mode T g = some j then r.2.2.1 i T g else 0)
  else 0

/-- The real layers. A partial abort ends the calls of the functionalities. -/
def mainRealLayers (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) :
    List ℕ → A.State → (C.Party → MainInput C × List (Tuple C)) →
      OracleComp (LocalSpec C) (A.State × Option (C.Party → MainInput C × List (Tuple C)))
  | [], st, p => pure (st, some p)
  | l :: ls, st, p =>
    A.answer st (.inl (.inl (mainMultLeak D (gatesAt jobs l).length (fun i => layerX K jobs l (p i).1)
      (fun i => layerY K jobs l (p i).1)))) >>= fun a =>
    liftComp ($ᵗ (C.Term → Fin (gatesAt jobs l).length → Bit)) (LocalSpec C) >>= fun fresh =>
    let r : MainMultReply C := match a.2 with | .inl (.inl r) => r | _ => default
    if ¬ mainAllReceive D r.2.2.2 then pure (a.1, none) else
    let z := mainFmultOut K D mode (gatesAt jobs l).length (fun i => layerX K jobs l (p i).1)
      (fun i => layerY K jobs l (p i).1) r fresh
    mainRealLayers K D A mode jobs ls a.1 fun i =>
      (appendLayer jobs l (p i).1 (z i), (p i).2 ++
        [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1, z i, (gatesAt jobs l).length, mode⟩])

/-- The leak of `F_multVerify` and its acceptance, on the views of the honest operators. -/
def mainVerifyLeak (D : C.Coalition) (inputs : C.Party → Option (List (Tuple C))) :
    (C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool :=
  let count := (firstInput inputs).length
  let tuples := (List.range count).map (tupleAt inputs)
  let differences := tuples.map fun τ g =>
    if g < τ.count then shareValue τ.z g - shareValue τ.x g * shareValue τ.y g else 0
  let agree := ∀ k < count, ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 →
    ∀ g < (tuples.getD k ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count,
      ((inputs i).bind (·[k]?)).map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) =
        ((inputs j).bind (·[k]?)).map fun τ => (τ.x T g, τ.y T g, τ.z T g)
  let accept := decide (agree ∧ ∀ τ ∈ tuples, ∀ g < τ.count,
    shareValue τ.z g = shareValue τ.x g * shareValue τ.y g)
  let known := fun i => if i ∈ D.1 then none else (inputs i).map fun views =>
    views.map fun τ => (⟨knownView D.1 τ.count τ.x, knownView D.1 τ.count τ.y, knownView D.1 τ.count τ.z,
      τ.count, τ.mode⟩ : Tuple C)
  (known, (if agree then differences else []), accept)

/-- `OpenRep` with the copies `vr` of the honest receivers. -/
def mainOpenWith (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E) (st : A.State)
    (receivers : Finset C.Party) (n : ℕ) (vr : C.Party → Shares C Bit) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) :=
  Concrete.sequenceFin (fun i => if i ∉ D.1 ∧ i ∈ receivers then mainCopyHashes (vr i) n else pure []) >>= fun ds =>
  if ¬ ∃ i, i ∉ D.1 ∧ i ∈ receivers then pure (st, fun _ => none) else
  A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then repOutbox K i (vr i) n (ds i) c
    else none) >>= fun p =>
  Concrete.sequenceFin (mainOpenOne K D receivers n vr ds p.2) >>= fun opened =>
  pure (p.1, opened)

theorem mainSimOpenX_eq_with (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (jobs : List Circuit) (st : A.State) (receivers : Finset C.Party)
    (known : C.Party → Shares C Bit) (outputs : List (List Bit)) :
    mainSimOpenX K D A jobs st receivers known outputs =
      liftComp ($ᵗ (C.Term → Fin (outputsOf jobs).length → Bit)) (LocalSpec C) >>= fun fresh =>
        mainOpenWith K D A st receivers (outputsOf jobs).length
          (mainOpenVr (outputsOf jobs).length (mainRebuild D (outputsOf jobs).length known outputs fresh)) :=
  rfl

/-- `Rerand`, `F_multVerify` and `OpenRep` in the real phase. -/
def mainRealTail (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (jobs : List Circuit) (st : A.State) (p : C.Party → MainInput C × List (Tuple C)) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) :=
  A.answer st (.inl (.inr (mainMultLeak D (outputsOf jobs).length (fun i => outputShares K jobs (p i).1)
    (fun _ => one K)))) >>= fun a =>
  liftComp ($ᵗ (C.Term → Fin (outputsOf jobs).length → Bit)) (LocalSpec C) >>= fun fresh =>
  let r : MainMultReply C := match a.2 with | .inl (.inr r) => r | _ => default
  if ¬ mainAllReceive D r.2.2.2 then pure (a.1, fun _ => none) else
  let v := mainFmultOut K D .peer (outputsOf jobs).length (fun i => outputShares K jobs (p i).1)
    (fun _ => one K) r fresh
  let leak := mainVerifyLeak D fun i => if i ∈ D.1 then none else
    some ((p i).2 ++ [⟨outputShares K jobs (p i).1, one K, v i, (outputsOf jobs).length, .peer⟩])
  A.answer a.1 (.inr leak) >>= fun b =>
  let receivers : Finset C.Party := match b.2 with | .inr rs => rs | _ => ∅
  if ¬ leak.2.2 = true then pure (b.1, fun _ => none) else
  mainOpenWith K D A b.1 receivers (outputsOf jobs).length v

/-- The real phase as a game. -/
def mainRealGame (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (st : A.State) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) :=
  mainRealLayers K D A mode jobs (List.range (depth jobs)) st (fun i => (x i, [])) >>= fun a =>
  match a.2 with
  | none => pure (a.1, fun _ => none)
  | some p => mainRealTail K D A jobs a.1 p

/-- The first steps of a batch: each honest operator calls `F_mult` for the first layer. -/
theorem main_startSteps (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (jobs : List Circuit)
    (x : C.Party → MainInput C) :
    startSteps localRoles D (fun i => mainProtocol K mode jobs i (x i)) =
      pure (fun i => if i ∈ D.1 then .done none else
        callStep K mode jobs i (List.range (depth jobs)) (x i, [])) := by
  unfold startSteps
  rw [← sequenceFin_pure]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, if_false]
    rw [mainProtocol_eq]
    exact advance_progAt K mode jobs i _ _

/-- The outputs of `F_mult` on the layer inputs, as the network gives them to the operators. -/
def mainMultOutputs (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (X Y : C.Party → Shares C Bit) (r : MainMultReply C) (fresh : C.Term → Fin n → Bit) :
    C.Party → Option (Shares C Bit) := fun i =>
  if i ∈ D.1 ∨ i ∉ r.2.2.2 then none else some (mainFmultOut K D mode n X Y r fresh i)

theorem main_honest_exists (D : C.Coalition) : ∃ i : C.Party, i ∉ D.1 := by
  obtain ⟨T, -⟩ := main_lacked_exists D
  obtain ⟨i, -, hi⟩ := main_exists_honest_holder D T
  exact ⟨i, hi⟩

theorem main_firstInput_count {β : Type} [Inhabited β] (D : C.Coalition) (u : C.Party → β)
    {f : β → ℕ} {n : ℕ} (hu : ∀ i, f (u i) = n) :
    f (firstInput fun i => if i ∈ D.1 then none else some (u i)) = n := by
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  unfold firstInput
  have hmem : u i₀ ∈ C.parties.filterMap fun i => if i ∈ D.1 then none else some (u i) :=
    List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [hi₀]⟩
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hl, List.headD_cons]
  have ha : a ∈ C.parties.filterMap fun i => if i ∈ D.1 then none else some (u i) := hl ▸ List.mem_cons_self
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 ha
  split_ifs at hj
  cases hj
  exact hu j

theorem main_fmultBit_run (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (X Y : C.Party → Shares C Bit) :
    (FmultBit K mode).run D (fun i => if i ∈ D.1 then none else some (X i, Y i, n)) =
      leak (mainMultLeak D n X Y) >>= fun r =>
        sample (C.Term → Fin n → Bit) >>= fun fresh => pure (mainMultOutputs K D mode n X Y r fresh) := by
  have hcount := main_firstInput_count (f := fun x : Shares C Bit × Shares C Bit × ℕ => x.2.2) D
    (fun i => (X i, Y i, n)) (fun _ => rfl)
  unfold FmultBit Fmult
  dsimp only
  rw [hcount]
  have hl : ∀ i, (if i ∈ D.1 then none else Option.map (fun x : Shares C Bit × Shares C Bit × ℕ =>
      (knownView D.1 x.2.2 x.1, knownView D.1 x.2.2 x.2.1)) (if i ∈ D.1 then none else some (X i, Y i, n))) =
      (mainMultLeak D n X Y).2 i := by
    intro i
    by_cases hi : i ∈ D.1 <;> simp [hi, mainMultLeak]
  simp only [hl]
  show leak (mainMultLeak D n X Y) >>= _ = _
  refine bind_congr fun r => bind_congr fun fresh => ?_
  · refine congrArg pure ?_
    funext i
    unfold mainMultOutputs mainFmultOut mainMultBase
    by_cases hi : i ∈ D.1 ∨ i ∉ r.2.2.2
    · simp only [hi, if_true]
    · simp only [hi, if_false]
      congr 1
      funext T g
      have hsum : ∀ g, (∑ j ∈ Finset.univ.filter (· ∉ D.1),
          (Option.map (fun x : Shares C Bit × Shares C Bit × ℕ => mulRep K (localContext j) x.1 x.2.1 g)
            (if j ∈ D.1 then none else some (X j, Y j, n))).getD 0) =
          ∑ j ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext j) (X j) (Y j) g := fun g =>
        Finset.sum_congr rfl fun j hj => by simp [(Finset.mem_filter.1 hj).2]
      simp only [hsum]

section Sum

set_option linter.unusedSectionVars false

variable {I₁ O₁ L₁ R₁ I₂ O₂ L₂ R₂ : Type} [Inhabited R₁] [Inhabited R₂]

/-- The left handler of `Functionality.sum`. -/
def mainSumLeft : QueryImpl (LocalSpec C + (L₁ →ₒ R₁)) (OracleComp (LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂))) :=
  (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂)) (Sum.inl t))) +
  (fun (l : L₁) => leak (C := C) (R := R₁ ⊕ R₂) (Sum.inl l : L₁ ⊕ L₂) >>= fun r =>
    match r with
    | .inl r => pure r
    | .inr _ => pure default)

theorem main_sum_run_left (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂)
    (D : C.Coalition) (inputs : C.Party → Option I₁) :
    (F₁.sum F₂).run D (fun i => (inputs i).map Sum.inl) =
      (fun out i => (out i).map Sum.inl) <$>
        simulateQ (mainSumLeft (L₂ := L₂) (R₂ := R₂)) (F₁.run D inputs) := by
  unfold Functionality.sum
  dsimp only
  rw [if_pos (fun i x hx => by
    obtain ⟨y, -, rfl⟩ := Option.mem_map.1 hx
    rfl)]
  have : (fun i => (Option.map (Sum.inl (β := I₂)) (inputs i)).bind Sum.getLeft?) = inputs := by
    funext i
    cases inputs i <;> rfl
  rw [this]
  rfl

theorem main_sumLeft_leak (l : L₁) :
    simulateQ (mainSumLeft (C := C) (L₂ := L₂) (R₂ := R₂)) (leak (C := C) (R := R₁) l) =
      leak (C := C) (R := R₁ ⊕ R₂) (Sum.inl l : L₁ ⊕ L₂) >>= fun r =>
        match r with
        | .inl r => pure r
        | .inr _ => pure default := by
  unfold leak
  rw [simulateQ_query]
  exact id_map _

theorem main_sumLeft_liftComp {α : Type} (p : ProbComp α) :
    simulateQ (mainSumLeft (C := C) (L₁ := L₁) (R₁ := R₁) (L₂ := L₂) (R₂ := R₂))
        (liftComp p (LocalSpec C + (L₁ →ₒ R₁))) = liftComp p _ := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_bind, simulateQ_bind]
    simp only [ih]
    congr 1

end Sum

section RunFunctionality

variable {E' Ia L R : Type} (D : C.Coalition) (A : Adversary C E' Ia L R)

/-- The handler of the functionality calls in `runFunctionality` with the local roles. -/
def mainCallImpl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT A.State (OracleComp (LocalSpec C))) :=
  (fun (t : (LocalSpec C).Domain) => (StateT.lift (localRoles.honest (OracleComp.lift (OracleSpec.query t))) :
    StateT A.State (OracleComp (LocalSpec C)) _)) +
  (fun (l : L) => (StateT.mk fun st => do
    let (st, r) ← localRoles.adversary (A.answer st l)
    pure (r, st) : StateT A.State (OracleComp (LocalSpec C)) R))

theorem main_callImpl_leak (l : L) (st : A.State) :
    (simulateQ (mainCallImpl A) (leak (C := C) (R := R) l)).run st =
      A.answer st l >>= fun a => pure (a.2, a.1) := by
  simp [leak, mainCallImpl, localRoles]
  rfl

end RunFunctionality

/-- The network runs the real phase as `mainRealGame`: each step of `executeRounds` is one call of a
functionality or the round of `OpenRep`. -/
def MainEngineReal (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit) (D : C.Coalition) (A : MainAdversary C E)
    (x : C.Party → MainInput C), MainInputs jobs D x → ∀ st : A.State,
    SameRun prims
      (executePhase localRoles D A (mainFunctionalities K mode) (mainRounds jobs) st
        fun i => mainProtocol K mode jobs i (x i))
      (mainHybridOut D jobs <$> mainRealGame K D A mode jobs x st)

/-- GS20, Theorem 2: the real phase and the simulator give the same run. The uniform terms of the
layers stay hidden, the leaks are the known views, the differences are `mainDifference`, and after
acceptance the copies of `Rerand` are `mainRebuild` of the outputs. -/
def MainRealSim (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit) (D : C.Coalition) (A : MainAdversary C E)
    (x : C.Party → MainInput C), MainInputs jobs D x → ∀ st : A.State,
    SameRun prims (mainRealGame K D A mode jobs x st) (mainSimAnswerX K D A mode jobs st (mainIdealLeak D jobs x))

theorem mainRealHybridCore_of (prims : Primitives) (K : Constants C E)
    (h₁ : MainEngineReal prims K) (h₂ : MainRealSim prims K) : MainRealHybridCore prims K :=
  fun mode jobs D A x hx st => (h₁ mode jobs D A x hx st).trans ((h₂ mode jobs D A x hx st).map _)

/-- `MainSecurityDistance` from its two halves. -/
theorem mainSecurityDistance_of {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (prims : Primitives) (K : Constants C E)
    (hreal : MainRealHybrid prims K) (hsound : MainOpenSound prims K) : MainSecurityDistance prims K := by
  intro mode jobs D A x z Z q hx hq
  rw [hreal mode jobs D A x z Z hx, mainIdealGame_eq, mainHybridGame]
  exact mainHybridIdeal prims K hsound mode jobs D A x z Z q hq

/-- `MainSecurityDistance`, open only at `MainEngineReal` and `MainRealSim`. -/
theorem mainSecurityDistance {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (prims : Primitives) (K : Constants C E) (hengine : MainEngineReal prims K) (hsim : MainRealSim prims K) :
    MainSecurityDistance prims K :=
  mainSecurityDistance_of prims K
    (mainRealHybrid_of_core prims K (mainRealHybridCore_of prims K hengine hsim)) (mainOpenSound_holds prims K)

/-- `MainStatement` (GS20, Theorem 2), open only at `MainEngineReal` and `MainRealSim`. -/
theorem mainStatementProof {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (prims : Primitives) (K : Constants C E) (hengine : MainEngineReal prims K) (hsim : MainRealSim prims K) :
    MainStatement prims K :=
  mainStatement_of_simulator_distance prims K (mainSecurityDistance prims K hengine hsim)

/-- info: 'ThresholdLeanXmssSecurity.mainOpenSound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainOpenSound_holds

/-- info: 'ThresholdLeanXmssSecurity.mainStatementProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainStatementProof

end ThresholdLeanXmssSecurity
