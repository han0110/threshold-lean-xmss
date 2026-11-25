import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cores
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Slots

/-!
# The hybrid of the hop on the used keys, the bottom slots

`bottomReduction` is the reduction of a bottom slot as code. It pauses the game at the request of
the run of slot `j` (`BottomPause`). `BottomSlotPartCosts`, `BottomLawReal` and `BottomLawFresh` state
its cost and its two laws, and `EndPointsAgree` relates the end points of the two numberings.
`usedHitHop_of_reductions` proves `UsedHitHop` at the error `setupHybridError` from these, from the
statements of the top slots and from `HybridEnd`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The setup of a bottom run that slot `j` takes, `0` or `1`. -/
def slotParity (j : ℕ) : ℕ := (j - runLimit) % 2

/-- The result of the head of a bottom run at one operator, as `bottomHead` gives it. -/
abbrev HeadOut := (List (List Bit) × Digest × Randomizer × Encoding) × (ℕ × ℕ)

/-! ## The programs of an operator around the two setups of a bottom run -/

/-- The batches of `jobs` at operator `i` with the PRSS keys `prss`, as `ceremonyRun` after its setup. -/
def batchesWith (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))) := do
  let outputs ← (chunks settings.batchSize jobs).mapM (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter)
  pure (outputs.foldlM (fun acc batch => batch.map (acc ++ ·)) [])

/-- `CheckTiming.firstPart` after its PRSS setup, with the PRSS keys `prss`. -/
def firstAfter (i : C.Party) (keys : Keys C) (b : Fin (2 ^ layerHeight)) (prss : PrssKeys C) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit) × Digest × Randomizer × Encoding)) := do
  let some outputs ← batchesWith K circuits settings i keys prss (bottomJobs b) | pure none
  let root ← StateT.lift (oracleStep (tweakable
    (merkleNode keys.parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)))
  let base ← StateT.lift (oracleStep (tweakable (truncateHash <$> Verification.oracleHashWithHash
    (randomizerInput keys.parameter topLayer (topKey b) (bRho b outputs) (littleEndianBytes 16 root)))))
  let some (randomness, encoding) ← StateT.lift (oracleStep (tweakable
      (grind keys.parameter topLayer (topKey b) (littleEndianBytes 16 root) base randomizerAttemptLimit 0))) | pure none
  pure (some (outputs, root, randomness, encoding))

/-- `CheckTiming.secondPart` after its PRSS setup, with the PRSS keys `prss`. -/
def secondAfter (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (prss : PrssKeys C) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option TreeOutput) := do
  let some values ← batchesWith K circuits settings i keys prss (signJobs b x.2.2.2) | pure none
  let path ← StateT.lift (oracleStep (tweakable (merklePath keys.parameter topLayer top.chainEnd (topKey b))))
  let signature : LayerSignature := ⟨x.2.2.1, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← StateT.lift (oracleStep (tweakable
    (Verification.layerRootWithHash keys.parameter topLayer (topKey b) (littleEndianBytes 16 x.2.1) signature)))
  if topRoot ≠ some top.root then pure none else
  pure (some (.bottom ⟨bCpk b x.1, bCommitment b x.1, x.2.1, signature⟩))

/-- The PRSS keys `prss` with the hidden coordinates of `fresh`, when a fresh draw exists. -/
def withFresh (D : C.Coalition) (i : C.Party) (fresh : Option (FreshKeys C)) (prss : PrssKeys C) : PrssKeys C :=
  (fresh.map (prssOverlay D i prss)).getD prss

/-- The head of a bottom run in the hybrid: the first setup with the fresh keys `fresh`, the first
ceremony and the search. It is `CheckTiming.bottomHead` with the overlay. -/
def headWith (D : C.Coalition) (fresh : Option (FreshKeys C)) (i : C.Party) (operator : OperatorState C)
    (b : Fin (2 ^ layerHeight)) : PartyM C E RealSpec HeadOut :=
  match operator.keys, operator.top with
  | some keys, some _ => prssSetup i >>= fun prss =>
      (firstAfter K circuits settings i keys b (withFresh D i fresh prss)).run (0, 0) >>= fun p =>
        p.1.elim failure fun x => pure (x, p.2)
  | _, _ => failure

/-- The rest of a bottom run after its first setup, from the output `out` of that setup. -/
def afterFirstSetup (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (out : Option (Keys C)) : PartyM C E RealSpec TreeOutput :=
  match operator.keys, operator.top, out with
  | some keys, some _, some k => (firstAfter K circuits settings i keys b ⟨k.seed, k.pairKey⟩).run (0, 0) >>= fun p =>
      p.1.elim failure fun x => CheckTiming.bottomTail K circuits settings i operator b (x, p.2)
  | _, _, _ => failure

/-- The rest of a bottom run after its second setup, from the head `head` and the output `out` of that
setup. -/
def afterSecondSetup (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (head : Option HeadOut) (out : Option (Keys C)) : PartyM C E RealSpec TreeOutput :=
  match operator.keys, operator.top, head, out with
  | some keys, some top, some x, some k =>
      (secondAfter K circuits settings i keys top b x.1 ⟨k.seed, k.pairKey⟩).run x.2 >>= fun p => p.1.elim failure pure
  | _, _, _, _ => failure

/-- The game at the request of the run of slot `j`: the state at the start of the run, the state of
the signing oracles, the keys and the top tree of the win test, the tree, and the continuation of
`forge`. -/
structure BottomPause (C : Committee) (σ : Type) where
  state : RealState C σ
  tsig : TsigState C
  keys : Keys C
  top : TopTree
  b : Fin (2 ^ layerHeight)
  next : Option (BottomTree × Digest) → OracleComp (LocalSpec C + (TsigSpec C + StateSpec σ)) Forgery

/-- The place of a bottom slot after the prefix. -/
inductive BottomPlace (C : Committee) (σ : Type)
  /-- The game ended before the run of the slot. The slot is absent. -/
  | finished
  /-- The run of the slot has an honest operator without keys or top tree. The slot is dead. -/
  | dead (p : BottomPause C σ)
  /-- The setup of the slot starts with each honest operator alive, from the state `adversary` of the
  adversary. For the second setup `heads` holds the head of each operator. -/
  | live (p : BottomPause C σ) (adversary : σ) (heads : C.Party → Option HeadOut)
  /-- Second setup only. The head stopped an honest operator, so the slot is dead. -/
  | skip (p : BottomPause C σ) (adversary : σ) (heads : C.Party → Option HeadOut)

/-- The oracles of `forge` in hybrid `j`, as in `fixedSigning`. -/
def signingImpl (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) (StateT (TsigState C) (RealM C A.net.State)) :=
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  QueryImpl.add forger (QueryImpl.add (fixedOracles K circuits settings runLimit j (wrongOutput D) D A) cell)

/-- The parameter of the honest operators of the state `s`. -/
def stateParameter {σ : Type} (D : C.Coalition) (s : RealState C σ) : PublicParameter :=
  gameParameter D fun i => (s.operators i).keys

/-- The rounds of the head of the run of the pause `p`. -/
def headRounds {σ : Type} (D : C.Coalition) (p : BottomPause C σ) : ℕ :=
  CheckTiming.firstRounds circuits settings (stateParameter D p.state) (.bottom p.b)

/-- Each honest operator has keys and a top tree. -/
def AliveAtStart {σ : Type} (D : C.Coalition) (s : RealState C σ) : Prop :=
  ∀ i, i ∉ D.1 → (s.operators i).keys.isSome ∧ (s.operators i).top.isSome

/-- The place at the request of the run of slot `j`. For the second setup it runs the first setup and
the head of the run, with the fresh keys of hybrid `j`. -/
def pauseAt (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State) :
    OracleComp (WorldSpec C) (BottomPlace C A.net.State) :=
  if ¬ AliveAtStart D p.state then pure (.dead p)
  else if slotParity runLimit j = 0 then pure (.live p p.state.adversary fun _ => none)
  else do
    let fresh ← free (liftComp ((List.range (treeSetups (.bottom p.b))).mapM fun c =>
      sampleSlot (C := C) j (fixedSlot runLimit p.state.runs (.bottom p.b) + c)) _)
    let (adversary, heads) ← executePhase worldRoles D A.net noFunctionality (headRounds circuits settings D p)
      p.state.adversary fun i => headWith K circuits settings D (fresh.getD 0 none) i (p.state.operators i) p.b
    if ∀ i, i ∉ D.1 → (heads i).isSome then pure (.live p adversary heads) else pure (.skip p adversary heads)

/-- `forge` with the oracles of hybrid `j`, query by query, up to the request of the run of slot `j`.
At the end of `forge` it runs the win test, as `fixedSigning`. -/
def forgeWalk (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree) :
    OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery →
      StateT (TsigState C) (RealM C A.net.State) (BottomPlace C A.net.State)
  | .pure forgery => do
      let st ← get
      let _ ← StateT.lift (do
        let s ← get
        forgeryWins realLift (canonicalDealt D s.operators keys.parameter top) st forgery)
      pure .finished
  | .liftBind (Sum.inr (Sum.inl (.tree b))) next => do
      let s ← StateT.lift get
      if mayRun runLimit D s (.bottom b) ∧ fixedSlot runLimit s.runs (.bottom b) + slotParity runLimit j = j then do
        let tsig ← get
        StateT.lift (StateT.lift (pauseAt K circuits settings runLimit j D A ⟨s, tsig, keys, top, b, next⟩))
      else do
        let answer ← signingImpl K circuits settings runLimit j D A (Sum.inr (Sum.inl (.tree b)))
        forgeWalk j D A keys top (next answer)
  | .liftBind t next => do
      let answer ← signingImpl K circuits settings runLimit j D A t
      forgeWalk j D A keys top (next answer)

/-- The prefix of hybrid `j` up to bottom slot `j`. -/
def bottomPrefix (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) (BottomPlace C A.net.State) := do
  let (state, keys) ← realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (state, ok) ← voteRound worldRoles D A.net state fun i => (keys i).map seedVote
  let (place, _) ← (do
      fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D A.net .top runLimit
      let s ← get
      match topHolder D s.operators with
      | none => pure BottomPlace.finished
      | some (keys, top) => (forgeWalk K circuits settings runLimit j D A keys top
          (A.forge ⟨top.root, keys.parameter⟩ top)).run' ⟨D.1, fun _ => none, [], fun _ => none⟩ :
        RealM C A.net.State (BottomPlace C A.net.State)).run (seedState D state keys ok)
  pure place

/-- The state after the run of the pause `p` with the result `r` of its phase and the vote, as
`fixedTreeRun`. -/
def finishRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (p : BottomPause C net.State)
    (r : net.State × (C.Party → Option TreeOutput)) : OracleComp (WorldSpec C) (RealState C net.State) := do
  let s := p.state
  let bad ← wrongOutput D (fun i => (s.operators i).keys) (.bottom p.b) r.2
  let (state, ok) ← voteRound worldRoles D net r.1 fun i => (r.2 i).map (treeVote (.bottom p.b))
  let kept := committed ok r.2
  pure ⟨state, fun i => (s.operators i).keep (kept i) (.bottom p.b),
    Function.update s.runs (.bottom p.b) (s.runs (.bottom p.b) + 1), s.closed, s.flag || bad || split D kept⟩

/-- The game after the run of the pause `p` ended in the state `s`, in hybrid `j + 1`: the answer of
the request, the rest of `forge` and the win test. -/
def resumeAfter (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State)
    (s : RealState C A.net.State) : OracleComp (WorldSpec C) Unit := do
  let (answer, s) ← (do
      let s ← get
      match heldBottom D s.operators p.b with
      | some tree => pure (some (tree, ← gameValue D s.operators (.randomizer topLayer (topKey p.b))))
      | none => pure none : RealM C A.net.State (Option (BottomTree × Digest))).run s
  let ((forgery, st), s) ← ((simulateQ (signingImpl K circuits settings runLimit (j + 1) D A)
    (p.next answer)).run p.tsig).run s
  let _ ← (forgeryWins realLift (canonicalDealt D s.operators p.keys.parameter p.top) st forgery).run s
  pure ()

/-- The game after bottom slot `j`, from the place and the outputs `out` of the setup of the slot. -/
def bottomRest (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    BottomPlace C A.net.State → (C.Party → Option (Keys C)) → OracleComp (WorldSpec C) Unit
  | .finished, _ => pure ()
  | .dead p, _ => do
      let ((), s) ← (fixedTreeRun K circuits settings runLimit (j + 1) (wrongOutput D) D A.net (.bottom p.b)).run p.state
      resumeAfter K circuits settings runLimit j D A p s
  | .live p adversary heads, out => do
      let r ← if slotParity runLimit j = 0 then
          executePhase worldRoles D A.net noFunctionality (treeFuel circuits settings - setupRounds) adversary
            fun i => afterFirstSetup K circuits settings i (p.state.operators i) p.b (out i)
        else
          executePhase worldRoles D A.net noFunctionality
            (treeFuel circuits settings - headRounds circuits settings D p - setupRounds) adversary
            fun i => afterSecondSetup K circuits settings i (p.state.operators i) p.b (heads i) (out i)
      resumeAfter K circuits settings runLimit j D A p (← finishRun D A.net p r)
  | .skip p adversary heads, _ => do
      let r ← executePhase worldRoles D A.net noFunctionality
        (treeFuel circuits settings - headRounds circuits settings D p) adversary
        fun i => (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (p.state.operators i) p.b)
      resumeAfter K circuits settings runLimit j D A p (← finishRun D A.net p r)

variable (prims : Primitives)

/-- The adversary of the reduction of bottom slot `j`. -/
def bottomReduction (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) : Adversary C E Unit PEmpty PEmpty where
  State := KeyJointState C × BottomPlace C A.net.State
  start _ _ := (fun r => (r.2, r.1)) <$>
    (simulateQ (slotHandler prims D) (bottomPrefix K circuits settings runLimit j D A)).run keyJointInitial
  round st sent := match st.2 with
    | .live p adversary heads => (fun r => ((r.2, .live p r.1.1 heads), r.1.2)) <$>
        (simulateQ (slotHandler prims D) (worldRoles.adversary (A.net.round adversary sent))).run st.1
    | _ => pure (st, fun _ _ => none)
  answer _ l := l.elim

/-- The pause belongs to slot `j`, each tree has at most `runLimit` runs, the run of the pause is
allowed, and the continuation of
`forge` has at most `forge` calls of the class `prssSetup` for each answer. -/
def PauseInRange {σ : Type} (forge j : ℕ) (p : BottomPause C σ) : Prop :=
  fixedSlot runLimit p.state.runs (.bottom p.b) + slotParity runLimit j = j ∧ (∀ t, p.state.runs t ≤ runLimit) ∧
    p.state.runs (.bottom p.b) < runLimit ∧ ∀ a, IsQueryBoundP (p.next a) (ForgeInClass .prssSetup) forge

/-- The test of the distinguisher on the data of the place. A dead place must be dead at its start. -/
def PlaceGuard {σ : Type} (forge j : ℕ) (D : C.Coalition) : BottomPlace C σ → Prop
  | .finished => True
  | .dead p => PauseInRange runLimit forge j p ∧ ¬ AliveAtStart D p.state
  | .live p _ _ => PauseInRange runLimit forge j p
  | .skip p _ _ => PauseInRange runLimit forge j p

/-- The distinguisher of the reduction of bottom slot `j`. Under the guard it runs the rest of the
game on the private state and reads `UsedHit`. -/
def bottomDistinguisher (forge j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Distinguisher C (bottomReduction K circuits settings runLimit prims j D A).State (Keys C) := fun r =>
  if PlaceGuard runLimit forge j D r.1.2 then
    (fun x => decide (UsedHit D x.2)) <$>
      (simulateQ (slotHandler prims D) (bottomRest K circuits settings runLimit j D A r.1.2 r.2)).run r.1.1
  else pure false

/-! ## The cost certificate -/

/-- The cost of each part of the reduction of bottom slot `j` in the class `prssSetup`. With
`k = (j - runLimit) / 2` and `c = slotParity runLimit j`, the start holds the seed generation, at most
`runLimit` top runs, `k` bottom runs, for `c = 1` the first setup and the head of run `k`, and the
calls of `forge` before the request. The seed generation and each run have one vote round. Its honest
calls are those of the `j` slots before slot `j`. The distinguisher holds the rest of run `k` (at most
one setup) with its vote, the other bottom runs, and the rest of `forge`. -/
def BottomSlotPartCosts : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (start step forge : ℕ),
    (∀ x z, IsQueryBoundP (A.net.start x z) (InClass .prssSetup) start) →
    (∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step) →
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) →
    ∀ j, runLimit ≤ j → j < gameSetups runLimit →
      (∀ x z, IsQueryBoundP ((bottomReduction K circuits settings runLimit prims j D A).start x z) Counted
        (start + (setupRounds + 1 + (runLimit + (j - runLimit) / 2 + slotParity runLimit j) *
          (treeFuel circuits settings + 1)) * step + forge + j * setupClassCalls C)) ∧
      (∀ st sent, IsQueryBoundP ((bottomReduction K circuits settings runLimit prims j D A).round st sent) Counted
        step) ∧
      (∀ r, IsQueryBoundP (bottomDistinguisher K circuits settings runLimit prims forge j D A r) Counted
        (forge + (treeFuel circuits settings + 1) * step + setupClassCalls C +
          (runLimit * 2 ^ layerHeight - (j - runLimit) / 2 - 1) *
            ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C)))

/-- The cost certificate of bottom slot `j`, for the class budget of the adversary. -/
def BottomSlotCost : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q start step forge : ℕ),
    start + dkgTsigRounds circuits settings runLimit * step + forge ≤ q →
    (∀ x z, IsQueryBoundP (A.net.start x z) (InClass .prssSetup) start) →
    (∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step) →
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) →
    ∀ j, runLimit ≤ j → j < gameSetups runLimit →
      IsQueryBounded (bottomReduction K circuits settings runLimit prims j D A)
        (bottomDistinguisher K circuits settings runLimit prims forge j D A) setupRounds
        (2 * q + honestSetupCalls runLimit C)

omit [Fintype E] [DecidableEq E] in
/-- The sum of the part costs of a bottom slot. It holds `dkgTsigRounds + 3 + (treeFuel + 1)` rounds,
two copies of `forge` and `gameSetups` setups. A game round count of at least `3 + (treeFuel + 1)`
pays the extra rounds and the second `forge` from the second `q`. -/
theorem bottomSlotCost_arith (q j start step forge : ℕ) (hlo : runLimit ≤ j) (hhi : j < gameSetups runLimit)
    (hq : start + dkgTsigRounds circuits settings runLimit * step + forge ≤ q) :
    (start + (setupRounds + 1 + (runLimit + (j - runLimit) / 2 + slotParity runLimit j) *
        (treeFuel circuits settings + 1)) * step + forge + j * setupClassCalls C) + setupRounds * step +
      (forge + (treeFuel circuits settings + 1) * step + setupClassCalls C +
        (runLimit * 2 ^ layerHeight - (j - runLimit) / 2 - 1) *
          ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C)) ≤
      2 * q + honestSetupCalls runLimit C := by
  rw [honestSetupCalls_eq]
  simp only [gameSetups, slotParity, dkgTsigRounds, setupRounds] at hhi hq ⊢
  set t := treeFuel circuits settings
  set h := setupClassCalls C
  set B := 2 ^ layerHeight
  obtain ⟨m, rfl⟩ : ∃ m, j = runLimit + m := ⟨j - runLimit, by omega⟩
  have hm : runLimit + m - runLimit = m := by omega
  rw [hm]
  obtain ⟨k, c, hc, rfl⟩ : ∃ k c, c < 2 ∧ m = 2 * k + c := ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
  have hdiv : (2 * k + c) / 2 = k := by omega
  have hmod : (2 * k + c) % 2 = c := by omega
  rw [hdiv, hmod]
  have hk : k + 1 ≤ runLimit * B := by nlinarith
  obtain ⟨r, hr⟩ : ∃ r, runLimit * B = k + 1 + r := ⟨runLimit * B - (k + 1), by omega⟩
  have hsub : runLimit * B - k - 1 = r := by omega
  rw [hsub]
  have hL : 1 ≤ runLimit := by
    rcases Nat.eq_zero_or_pos runLimit with h0 | h0
    · subst h0; simp at hhi
    · exact h0
  have hB : 1 ≤ B := Nat.one_le_two_pow
  have hround : (3 + (t + 1)) * step ≤ (3 + (1 + runLimit * (1 + B) * (t + 1))) * step := by
    apply Nat.mul_le_mul_right
    have : t + 1 ≤ runLimit * (1 + B) * (t + 1) := Nat.le_mul_of_pos_left (t + 1) (by positivity)
    omega
  have hc1 : c * (t + 1) * step ≤ (t + 1) * step := by
    have : c ≤ 1 := by omega
    calc c * (t + 1) * step ≤ 1 * (t + 1) * step := by gcongr
      _ = (t + 1) * step := by ring
  have hch : c * h ≤ h := by
    have : c ≤ 1 := by omega
    calc c * h ≤ 1 * h := by gcongr
      _ = h := by ring
  nlinarith

omit [Fintype E] [DecidableEq E] in
/-- The parts give the cost certificate of a bottom slot. -/
theorem bottomSlotCost_of_parts (parts : BottomSlotPartCosts K circuits settings runLimit prims) :
    BottomSlotCost K circuits settings runLimit prims := by
  intro D A q start step forge hsum hs hr hf j hlo hhi
  obtain ⟨hstart, hround, hfinal⟩ := parts D A start step forge hs hr hf j hlo hhi
  exact ⟨_, _, _, bottomSlotCost_arith circuits settings runLimit q j start step forge hlo hhi hsum, hstart, hround,
    fun _ l => l.elim, hfinal⟩

/-! ## The acceptance laws -/

/-- The real law of bottom slot `j`, for an adversary whose `forge` has at most `forge` calls of the
class `prssSetup`. -/
def BottomLawReal : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (forge : ℕ),
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) →
    ∀ j, runLimit ≤ j → j < gameSetups runLimit →
      fixedProb K circuits settings runLimit prims D A j =
        accepts prims (distinguish (setupExec D (bottomReduction K circuits settings runLimit prims j D A) [])
          (bottomDistinguisher K circuits settings runLimit prims forge j D A))

/-- The fresh law of bottom slot `j`. -/
def BottomLawFresh : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (forge : ℕ),
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) →
    ∀ j, runLimit ≤ j → j < gameSetups runLimit →
      fixedProb K circuits settings runLimit prims D A (j + 1) =
        accepts prims (distinguish (setupExec D (bottomReduction K circuits settings runLimit prims j D A) [])
          (seedGenHiddenZ D (bottomDistinguisher K circuits settings runLimit prims forge j D A)))

/-- The end points of the fixed and of the old numbering have one probability. Each slot of an allowed
run is below `gameSetups` in both numberings, so both draw fresh keys for each slot that a run
reaches. -/
def EndPointsAgree : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    fixedProb K circuits settings runLimit prims D A (gameSetups runLimit) =
      hybridProb K circuits settings runLimit prims D A (gameSetups runLimit)

omit [Fintype E] [DecidableEq E] in
/-- The old end point gives `FixedEnd`. -/
theorem fixedEnd_of_hybridEnd (agree : EndPointsAgree K circuits settings runLimit prims)
    (finish : HybridEnd K circuits settings runLimit prims) : FixedEnd K circuits settings runLimit prims := by
  intro D A q bounded
  rw [agree D A]
  exact finish D A q bounded

/-! ## The glue -/

omit [Fintype E] [DecidableEq E] in
/-- The reduction of the bottom slots with its cost and its laws gives `BottomSlotContract`. -/
theorem bottomSlotContract_of_reduction (cost : BottomSlotCost K circuits settings runLimit prims)
    (real : BottomLawReal K circuits settings runLimit prims) (fresh : BottomLawFresh K circuits settings runLimit prims) :
    BottomSlotContract K circuits settings runLimit prims := by
  intro D A q bounded j hlo hhi
  obtain ⟨start, step, forge, hsum, hs, hr, hf⟩ :=
    dkgTsigBounded_classBounded circuits settings runLimit bounded .prssSetup
  exact ⟨bottomReduction K circuits settings runLimit prims j D A,
    bottomDistinguisher K circuits settings runLimit prims forge j D A, [],
    cost D A q start step forge hsum hs hr hf j hlo hhi, real D A forge hf j hlo hhi, fresh D A forge hf j hlo hhi⟩

omit [Fintype E] [DecidableEq E] in
/-- `UsedHitHop` at the error `setupHybridError` from the reductions of both slot kinds. No premise is an
existential contract. -/
theorem usedHitHop_of_reductions (topCost : TopSlotPartCosts K circuits settings runLimit prims)
    (topReal : TopLawReal K circuits settings runLimit prims) (topFresh : TopLawFresh K circuits settings runLimit prims)
    (bottomCost : BottomSlotPartCosts K circuits settings runLimit prims)
    (bottomReal : BottomLawReal K circuits settings runLimit prims)
    (bottomFresh : BottomLawFresh K circuits settings runLimit prims)
    (agree : EndPointsAgree K circuits settings runLimit prims) (finish : HybridEnd K circuits settings runLimit prims) :
    UsedHitHop prims K circuits settings runLimit (setupHybridError runLimit C) :=
  usedHitHop_of_fixedHybrids K circuits settings runLimit prims
    (topSlotContract_of_reduction K circuits settings runLimit prims
      (topSlotCost_of_parts K circuits settings runLimit prims topCost) topReal topFresh)
    (bottomSlotContract_of_reduction K circuits settings runLimit prims
      (bottomSlotCost_of_parts K circuits settings runLimit prims bottomCost) bottomReal bottomFresh)
    (fixedEnd_of_hybridEnd K circuits settings runLimit prims agree finish)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.usedHitHop_of_reductions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.usedHitHop_of_reductions
