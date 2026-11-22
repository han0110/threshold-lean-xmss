import ThresholdLeanXmss.Ideal
import ThresholdLeanXmss.Scheme
import ThresholdLeanXmss.Statement.Execution
import ThresholdLeanXmss.Statement.RandomOracle
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.SlotHybrid
import ThresholdLeanXmssSecurity.Proof.SeedGenFinish

/-!
# The hybrid of the hop on the used keys, the top slots

`fixedSlot` numbers the setups of a game with the top slots first, and `fixedGame j` is hybrid `j`,
which draws fresh hidden keys for the slots below `j`. `fixedStart` states that hybrid `0` has the
probability of the event of `UsedHitHop`. `topReduction` is the
reduction of top slot `j` as code. `TopSlotPartCosts`, `TopLawReal` and `TopLawFresh` state its cost
and its two laws, and `topSlotContract_of_reduction` gives the contract of the top slots from them.
`usedHitHop_of_fixedHybrids` proves `UsedHitHop` from the contracts of both slot kinds and `FixedEnd`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## The hybrid games -/

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

variable (prims : Primitives)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The telescope of `n` adjacent steps of size at most `ε`. -/
theorem le_add_of_steps (p : ℕ → ℝ) (ε : ℝ) :
    ∀ n, (∀ j < n, |p j - p (j + 1)| ≤ ε) → p 0 ≤ p n + n * ε
  | 0, _ => by simp
  | n + 1, h => by
    have ih := le_add_of_steps p ε n fun j hj => h j (by omega)
    have hn := (abs_le.1 (h n (by omega))).2
    push_cast
    linarith

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

/-! ## The slots with the top slots first -/

section Slots

variable {C : Committee} (runLimit : ℕ)

/-- The first slot of a run of `tree` after the runs `runs`. Top run `r` takes slot `r`. The runs of
the bottom trees take the slots from `runLimit` on, two for each run. -/
def fixedSlot (runs : Tree → ℕ) : Tree → ℕ
  | .top => runs .top
  | .bottom _ => runLimit + ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) * treeSetups (.bottom b)

end Slots

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The hybrid games with the top slots first -/

/-- One run of `tree` in hybrid `j`, as `hybridTreeRun` with `fixedSlot`. -/
def fixedTreeRun (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  let fresh ← StateT.lift (free (liftComp ((List.range (treeSetups tree)).mapM fun c =>
    sampleSlot (C := C) j (fixedSlot runLimit s.runs tree + c)) _))
  let (state, outputs) ← StateT.lift (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
    s.adversary fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) tree)
  let bad ← StateT.lift (monitor (fun i => (s.operators i).keys) tree outputs)
  let operators := fun i => (s.operators i).keep (outputs i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag || bad⟩ : RealState C net.State)

/-- At most `count` runs of `tree` in hybrid `j`. -/
def fixedTreeRuns (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ℕ → RealM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      fixedTreeRun K circuits settings runLimit j monitor D net tree
      fixedTreeRuns j monitor D net tree count

/-- A request of bottom tree `b` in hybrid `j`. -/
def fixedTreeRequest (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) : RealM C net.State (Option (BottomTree × Digest)) := do
  fixedTreeRuns K circuits settings runLimit j monitor D net (.bottom b) 1
  let s ← get
  match heldBottom D s.operators b with
  | some tree => pure (some (tree, ← gameValue D s.operators (.randomizer topLayer (topKey b))))
  | none => pure none

/-- The signing oracles in hybrid `j`. -/
def fixedOracles (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => StateT.lift (fixedTreeRequest K circuits settings runLimit j monitor D A.net b)
  | .round1 i J e message => signRequest D i e (.round1 i J e message)
  | .round2 i J e message parts => signRequest D i e (.round2 i J e message parts)

/-- The signing phase in hybrid `j`. -/
def fixedSigning (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    RealM C A.net.State Bool := do
  let s ← get
  let some (keys, top) := topHolder D s.operators | pure false
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  let (forgery, st) ← (simulateQ (forger + (fixedOracles K circuits settings runLimit j monitor D A + cell))
    (A.forge ⟨top.root, keys.parameter⟩ top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
  let s ← get
  forgeryWins realLift (canonicalDealt D s.operators keys.parameter top) st forgery

/-- The run of the game in hybrid `j`. -/
def fixedRun (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) (Bool × Bool) := do
  let (state, keys) ← realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (win, s) ← (do
      fixedTreeRuns K circuits settings runLimit j monitor D A.net .top runLimit
      fixedSigning K circuits settings runLimit j monitor D A).run (startState D state keys)
  pure (win, s.flag)

/-- Hybrid `j` with the top slots first. The slots below `j` have fresh hidden keys. -/
def fixedGame (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool :=
  Prod.snd <$> fixedRun K circuits settings runLimit j (wrongOutput D) D A

variable (prims : Primitives)

/-- `p j`, the probability of `UsedHit` at the end of hybrid `j` in `jointKeyWorld`. -/
def fixedProb (D : C.Coalition) (A : DkgTsigAdversary C E) (j : ℕ) : ℝ :=
  usedHitProb prims D (fixedGame K circuits settings runLimit j D A)

/-! ## The start point, proved -/

omit [Fintype E] [DecidableEq E] in
theorem fixedTreeRun_zero (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) :
    fixedTreeRun K circuits settings runLimit 0 monitor D net tree = treeRun K circuits settings monitor D net tree := by
  unfold fixedTreeRun treeRun
  have hnone : (fun c => (List.map (fun _ => (none : Option (FreshKeys C)))
      (List.range (treeSetups tree))).getD c none) = fun _ => none := by
    funext c
    simp [List.getD_eq_getElem?_getD]
  have hlift : ∀ {α : Type} (a : α),
      (StateT.lift (pure a : OracleComp (WorldSpec C) α) : RealM C net.State α) = pure a := fun a => rfl
  simp only [HybridStartProof.mapM_sampleSlot_zero, liftComp_pure, free, simulateQ_pure, hlift, pure_bind, hnone,
    HybridStartProof.slotProgram_eq K circuits settings D (fun _ => none) (fun _ => rfl)]

omit [Fintype E] [DecidableEq E] in
theorem fixedTreeRuns_zero (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ∀ count, fixedTreeRuns K circuits settings runLimit 0 monitor D net tree count =
      treeRuns K circuits settings runLimit monitor D net tree count
  | 0 => rfl
  | count + 1 => by
    simp only [fixedTreeRuns, treeRuns, fixedTreeRun_zero, fixedTreeRuns_zero monitor D net tree count]

omit [Fintype E] [DecidableEq E] in
theorem fixedGame_zero (D : C.Coalition) (A : DkgTsigAdversary C E) :
    fixedGame K circuits settings runLimit 0 D A = dkgTreeGame K circuits settings runLimit D A := by
  have horacles : fixedOracles K circuits settings runLimit 0 (wrongOutput D) D A =
      realOracles K circuits settings runLimit (wrongOutput D) D A := by
    funext q
    cases q with
    | tree b =>
      simp only [fixedOracles, realOracles, fixedTreeRequest, treeRequest, fixedTreeRuns_zero]
      rfl
    | _ => rfl
  have hsigning : fixedSigning K circuits settings runLimit 0 (wrongOutput D) D A =
      dkgSigning K circuits settings runLimit (wrongOutput D) D A := by
    simp only [fixedSigning, dkgSigning, horacles]
    rfl
  simp only [fixedGame, dkgTreeGame, fixedRun, dkgTsigRun, fixedTreeRuns_zero, hsigning]

omit [Fintype E] [DecidableEq E] in
/-- The start point. Hybrid `0` has the probability of the event of `UsedHitHop`. -/
theorem fixedStart (D : C.Coalition) (A : DkgTsigAdversary C E) :
    fixedProb K circuits settings runLimit prims D A 0 =
      usedHitProb prims D (dkgTreeGame K circuits settings runLimit D A) := by
  unfold fixedProb
  rw [fixedGame_zero]

/-! ## The reduction of top slot `j` as code -/

/-- The handler of the reduction. A call of the class `prssSetup` on either copy goes to the oracle of
the challenger. Each other query runs `jointKeyWorld` on the private state with private coins. -/
def slotHandler (D : C.Coalition) :
    QueryImpl (WorldSpec C) (StateT (KeyJointState C) (OracleComp (LocalSpec C))) := fun t =>
  match t with
  | .inl (.inl (.inr (.inl q))) =>
      if queryClass q = .prssSetup then liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))
      else StateT.mk fun s => liftComp ((jointKeyWorld prims D false (.inl (.inl (.inr (.inl q))))).run s) _
  | .inr (.inr (.inl q)) =>
      if queryClass q = .prssSetup then liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))
      else StateT.mk fun s => liftComp ((jointKeyWorld prims D false (.inr (.inr (.inl q)))).run s) _
  | t => StateT.mk fun s => liftComp ((jointKeyWorld prims D false t).run s) _

/-- The place of top slot `j` after the prefix of the game. -/
inductive TopPlace (C : Committee) (σ : Type)
  /-- Top run `j` starts and each honest operator has keys. Its setup is the slot. -/
  | live (s : RealState C σ)
  /-- No live slot. With `runJ`, top run `j` starts and an honest operator has no keys, so the slot is
  dead. Without `runJ`, the loop of the top runs ended before run `j`, so the slot is absent. -/
  | skip (s : RealState C σ) (runJ : Bool)

/-- The first `count` top runs of hybrid `j`. The result is true when each of them ran. -/
def topLoop (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : ℕ → RealM C net.State Bool
  | 0 => pure true
  | count + 1 => do
    if mayRun runLimit D (← get) .top then
      fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net .top
      topLoop j D net count
    else pure false

/-- The prefix of hybrid `j` up to top slot `j`. It runs the seed generation and top runs `0` to
`j - 1`, and it stops before the fresh keys and the setup of top run `j`. -/
def topPrefix (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) (TopPlace C A.net.State) := do
  let (state, keys) ← realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (ran, s) ← (topLoop K circuits settings runLimit j D A.net j).run (startState D state keys)
  if ran = true ∧ mayRun runLimit D s .top then
    if ∀ i, i ∉ D.1 → (s.operators i).keys.isSome then pure (.live s) else pure (.skip s true)
  else pure (.skip s false)

/-- The program of operator `i` in a top run after its PRSS setup, with the PRSS keys `prss`. It is
the rest of `newTree` at `.top`. -/
def topAfterSetup (i : C.Party) (keys : Keys C) (prss : PrssKeys C) : PartyM C E RealSpec TreeOutput := do
  let ctx : Context C := ⟨i, keys, prss⟩
  let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (batched settings.batchSize (fun jobs => do
        let (label, k) ← get
        let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
        let (outputs, state) ← StateT.lift ((runJobs K (realRunBuildingBlocks K ctx settings.mode)
          (jobs.map (circuits keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩)
        set (state.label, k + 1)
        pure (some outputs))) emptyTop .top).run' (0, 0) | failure
  pure output

/-- The game after top run `j` from the state `s`, in hybrid `j + 1`, namely the later top runs and
the signing. It gives the flag. -/
def topRest (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (s : RealState C A.net.State) :
    OracleComp (WorldSpec C) Bool :=
  (fun r => r.2.flag) <$> (do
    fixedTreeRuns K circuits settings runLimit (j + 1) (wrongOutput D) D A.net .top (runLimit - (j + 1))
    fixedSigning K circuits settings runLimit (j + 1) (wrongOutput D) D A).run s

/-- The rest of a live top run `j` after its setup, from the state `s` of the prefix, the state of
the adversary and the setup outputs `r`, and then `topRest`. -/
def topLiveRest (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (s : RealState C A.net.State)
    (r : A.net.State × (C.Party → Option (Keys C))) : OracleComp (WorldSpec C) Bool := do
  let (state, outputs) ← executePhase worldRoles D A.net noFunctionality
    (treeFuel circuits settings - setupRounds) r.1 fun i =>
      match (s.operators i).keys, r.2 i with
      | some keys, some k => topAfterSetup K circuits settings i keys ⟨k.seed, k.pairKey⟩
      | _, _ => failure
  let bad ← wrongOutput D (fun i => (s.operators i).keys) .top outputs
  topRest K circuits settings runLimit j D A
    ⟨state, fun i => (s.operators i).keep (outputs i) .top, Function.update s.runs .top (s.runs .top + 1),
      s.closed, s.flag || bad⟩

/-- The rest of the game when top slot `j` is dead (`runJ`) or absent. A dead run `j` runs as in
hybrid `j + 1`. -/
def topSkipRest (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (s : RealState C A.net.State)
    (runJ : Bool) : OracleComp (WorldSpec C) Bool :=
  if runJ then do
    let ((), s) ← (fixedTreeRun K circuits settings runLimit (j + 1) (wrongOutput D) D A.net .top).run s
    topRest K circuits settings runLimit j D A s
  else (fun r => r.2.flag) <$> (fixedSigning K circuits settings runLimit (j + 1) (wrongOutput D) D A).run s

/-- The adversary of the reduction of top slot `j`. Its state is the private part of `jointKeyWorld`
and the place of the slot. -/
def topReduction (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) : Adversary C E Unit PEmpty PEmpty where
  State := KeyJointState C × TopPlace C A.net.State
  start _ _ := (fun r => (r.2, r.1)) <$>
    (simulateQ (slotHandler prims D) (topPrefix K circuits settings runLimit j D A)).run keyJointInitial
  round st sent := match st.2 with
    | .live s => (fun r => ((r.2, .live { s with adversary := r.1.1 }), r.1.2)) <$>
        (simulateQ (slotHandler prims D) (worldRoles.adversary (A.net.round s.adversary sent))).run st.1
    | .skip _ _ => pure (st, fun _ _ => none)
  answer _ l := l.elim

/-- The distinguisher of the reduction of top slot `j`. It runs the rest of the game on the private
state and reads `UsedHit`. -/
def topDistinguisher (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Distinguisher C (topReduction K circuits settings runLimit prims j D A).State (Keys C) := fun r =>
  let rest := match r.1.2 with
    | .live s => topLiveRest K circuits settings runLimit j D A s (s.adversary, r.2)
    | .skip s runJ => topSkipRest K circuits settings runLimit j D A s runJ
  (fun x => decide (UsedHit D x.2)) <$> (simulateQ (slotHandler prims D) rest).run r.1.1

/-! ## The cost certificate -/

/-- The calls of the class `prssSetup` of one PRSS setup, at most `n (4 n + termCount C)`. -/
def setupClassCalls (C : Committee) : ℕ := C.n * (4 * C.n + termCount C)

/-- The cost of each part of the reduction of top slot `j` in the class `prssSetup`, for an adversary
with the class budget `start`, `step`, `forge`. The start holds the adversary calls of the seed
generation and of `j` top runs, and the honest calls of `j` setups. Each of the three rounds holds one
round of the adversary. The distinguisher holds, for each state and each setup output, at most
`runLimit - j` top runs (a dead run `j` included) and `runLimit` runs of each bottom tree, each with
its setups, and `forge`. -/
def TopSlotPartCosts : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (start step forge : ℕ),
    (∀ x z, IsQueryBoundP (A.net.start x z) (InClass .prssSetup) start) →
    (∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step) →
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) →
    ∀ j < runLimit,
      (∀ x z, IsQueryBoundP ((topReduction K circuits settings runLimit prims j D A).start x z) Counted
        (start + (setupRounds + j * treeFuel circuits settings) * step + j * setupClassCalls C)) ∧
      (∀ st sent, IsQueryBoundP ((topReduction K circuits settings runLimit prims j D A).round st sent) Counted
        step) ∧
      (∀ r, IsQueryBoundP (topDistinguisher K circuits settings runLimit prims j D A r) Counted
        ((runLimit - j) * (treeFuel circuits settings * step + setupClassCalls C) + forge +
          runLimit * 2 ^ layerHeight * (treeFuel circuits settings * step + 2 * setupClassCalls C)))

/-- The cost certificate of top slot `j`. The reduction is `q`-query bounded at the budget of
`HybridContract`. -/
def TopSlotCost : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ j < runLimit, IsQueryBounded (topReduction K circuits settings runLimit prims j D A)
      (topDistinguisher K circuits settings runLimit prims j D A) setupRounds (2 * q + honestSetupCalls runLimit C)

omit [Fintype E] [DecidableEq E] in
/-- The honest calls of the class `prssSetup` of a game are `gameSetups` setups. -/
theorem honestSetupCalls_eq : honestSetupCalls runLimit C = gameSetups runLimit * setupClassCalls C := by
  simp only [honestSetupCalls, setupClassCalls, Nat.mul_assoc]

omit [Fintype E] [DecidableEq E] in
/-- The sum of the part costs. Start, three rounds and distinguisher stay within `2 q + honestSetupCalls`,
because the parts hold `dkgTsigRounds + 3` rounds and `gameSetups` setups. -/
theorem topSlotCost_arith (q j start step forge : ℕ) (hj : j < runLimit)
    (hq : start + dkgTsigRounds circuits settings runLimit * step + forge ≤ q) :
    (start + (setupRounds + j * treeFuel circuits settings) * step + j * setupClassCalls C) + setupRounds * step +
      ((runLimit - j) * (treeFuel circuits settings * step + setupClassCalls C) + forge +
        runLimit * 2 ^ layerHeight * (treeFuel circuits settings * step + 2 * setupClassCalls C)) ≤
      2 * q + honestSetupCalls runLimit C := by
  obtain ⟨m, rfl⟩ : ∃ m, runLimit = j + 1 + m := ⟨runLimit - (j + 1), by omega⟩
  have hsub : j + 1 + m - j = m + 1 := by omega
  rw [hsub, honestSetupCalls_eq]
  simp only [dkgTsigRounds, gameSetups, setupRounds] at hq ⊢
  set t := treeFuel circuits settings
  set h := setupClassCalls C
  set L := 2 ^ layerHeight
  have h3 : 3 * step ≤ q :=
    (Nat.mul_le_mul_right step (Nat.le_add_right 3 ((j + 1 + m) * (1 + L) * t))).trans (by omega)
  nlinarith

omit [Fintype E] [DecidableEq E] in
/-- The parts give the cost certificate. -/
theorem topSlotCost_of_parts (parts : TopSlotPartCosts K circuits settings runLimit prims) :
    TopSlotCost K circuits settings runLimit prims := by
  intro D A q bounded j hj
  obtain ⟨start, step, forge, hsum, hs, hr, hf⟩ :=
    dkgTsigBounded_classBounded circuits settings runLimit bounded .prssSetup
  obtain ⟨hstart, hround, hfinal⟩ := parts D A start step forge hs hr hf j hj
  exact ⟨_, _, _, topSlotCost_arith circuits settings runLimit q j start step forge hj hsum, hstart, hround,
    fun _ l => l.elim, hfinal⟩

/-! ## The acceptance laws -/

/-- The real law. The reduction with the real challenger accepts with the probability of hybrid `j`. -/
def TopLawReal : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E), ∀ j < runLimit,
    fixedProb K circuits settings runLimit prims D A j =
      accepts prims (distinguish (setupExec D (topReduction K circuits settings runLimit prims j D A) [])
        (topDistinguisher K circuits settings runLimit prims j D A))

/-- The fresh law. The reduction with the challenger of the fresh hidden keys accepts with the
probability of hybrid `j + 1`. -/
def TopLawFresh : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E), ∀ j < runLimit,
    fixedProb K circuits settings runLimit prims D A (j + 1) =
      accepts prims (distinguish (setupExec D (topReduction K circuits settings runLimit prims j D A) [])
        (seedGenHiddenZ D (topDistinguisher K circuits settings runLimit prims j D A)))

/-! ## The two commutations that the laws need -/

/-- One step of the hybrid at slot `j`, in the form of `HybridContract`, at the budget `budget`. -/
def SlotStep (budget : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (j : ℕ) : Prop :=
  ∃ (Aj : Adversary C E Unit PEmpty PEmpty) (Zj : Distinguisher C Aj.State (Keys C)) (z : Aux),
    IsQueryBounded Aj Zj setupRounds budget ∧
    fixedProb K circuits settings runLimit prims D A j = accepts prims (distinguish (setupExec D Aj z) Zj) ∧
    fixedProb K circuits settings runLimit prims D A (j + 1) =
      accepts prims (distinguish (setupExec D Aj z) (seedGenHiddenZ D Zj))

/-- `HybridContract` on the top slots. -/
def TopSlotContract : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ j < runLimit, SlotStep K circuits settings runLimit prims (2 * q + honestSetupCalls runLimit C) D A j

/-- `HybridContract` on the slots of the bottom trees. `bottomSlotContract_of_reduction` gives it from
the reduction of a bottom slot. -/
def BottomSlotContract : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ j, runLimit ≤ j → j < gameSetups runLimit →
      SlotStep K circuits settings runLimit prims (2 * q + honestSetupCalls runLimit C) D A j

/-- `HybridEnd` for the hybrids with the top slots first. -/
def FixedEnd : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    fixedProb K circuits settings runLimit prims D A (gameSetups runLimit) ≤ freshKeyError runLimit C q

omit [Fintype E] [DecidableEq E] in
/-- The reduction as code with its cost and its two laws gives the contract on the top slots. -/
theorem topSlotContract_of_reduction (cost : TopSlotCost K circuits settings runLimit prims)
    (real : TopLawReal K circuits settings runLimit prims) (fresh : TopLawFresh K circuits settings runLimit prims) :
    TopSlotContract K circuits settings runLimit prims := by
  intro D A q bounded j hj
  exact ⟨topReduction K circuits settings runLimit prims j D A, topDistinguisher K circuits settings runLimit prims j D A,
    [], cost D A q bounded j hj, real D A j hj, fresh D A j hj⟩

omit [Fintype E] [DecidableEq E] in
/-- `UsedHitHop` from the hybrid with the top slots first. -/
theorem usedHitHop_of_fixedHybrids (top : TopSlotContract K circuits settings runLimit prims)
    (bottom : BottomSlotContract K circuits settings runLimit prims)
    (finish : FixedEnd K circuits settings runLimit prims) :
    UsedHitHop prims K circuits settings runLimit (setupHybridError runLimit C) := by
  intro D A q bounded
  rw [← fixedStart K circuits settings runLimit prims D A]
  have steps : ∀ j < gameSetups runLimit,
      |fixedProb K circuits settings runLimit prims D A j - fixedProb K circuits settings runLimit prims D A (j + 1)| ≤
        prssSetupHashError C (2 * q + honestSetupCalls runLimit C) / 2 := by
    intro j hj
    have step : SlotStep K circuits settings runLimit prims (2 * q + honestSetupCalls runLimit C) D A j := by
      by_cases hjt : j < runLimit
      · exact top D A q bounded j hjt
      · exact bottom D A q bounded j (by omega) hj
    obtain ⟨Aj, Zj, z, budget, real, fresh⟩ := step
    rw [real, fresh, ← setupHashError_prss]
    exact setupHiddenFresh prims .prss D Aj (fun _ => ()) z Zj _ budget
  have telescope := le_add_of_steps _ _ _ steps
  have last := finish D A q bounded
  unfold setupHybridError
  linarith

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.fixedStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.fixedStart
