import ThresholdLeanXmssSecurity.Proof.LifetimeRealBad
import ThresholdLeanXmssSecurity.Proof.LifetimeIdealBad
import ThresholdLeanXmssSecurity.Proof.LifetimeJointHop

/-!
# The reveal of run `n` in hybrid `n`

This module splits hybrid `n` of the lifetime PRF pass at the reveal step of run `n`, in the `false`
key world. The split is exact, and it uses the program `program4` of `LifetimePrfTransportProof`.
In `program4`, run `n` has its own copy of the local oracles.

* `runTo` runs the adversary up to a lifetime query that a stop condition selects.
  `simulateQ_eq_runTo` states that this run, followed by the simulation of the rest, is the
  simulation of the adversary.
* `setup4` runs `program4` up to the admitted start of run `n` (the run counter is `n`). It then
  runs the start, the commit round and the reveal round of run `n` in the form of
  `startSteps_prssSetup_bind`, `stepRound_prssCommit_bind` and `stepRound_prssReveal_bind`. Other
  queries of the adversary, signing requests included, run between the rounds. The reveal round
  returns the reveal rows of run `n`. `tail4` runs the rest of the lifetime and the win test.
  `program4_split` states that `program4` is `setup4` followed by `tail4`.
* `worldSetup` and `worldTail` are the images of `setup4` and `tail4` in hybrid `n`.
  `reductionGame_split` states that the world game of hybrid `n` is `worldSetup` followed by
  `worldTail`.
* `setup4_quiet` states that `setup4` makes no free PRG call of the keygen, the signing or run `n`.
  So `worldSetup` makes no free stream under a hidden name, and `probBad_reductionGame_eq` states
  that the stream-key bad event of hybrid `n` is the bad event of the ideal joint world that starts
  after `worldSetup` on its cache (`runBoundary`).
* `tailAllowed` states that the tail makes no emulated call of an earlier run and no free call that
  the rows of run `n` do not allow. It holds when the keygen and the signing hash no stream key on
  the free copy (`FreeStreamKeyQuiet`). The steps of run `n` after its reveal round follow
  `afterDerivationAllowed`, and the later runs use the adversary copy.
* `reductionGame_bad` states the cover. On the support of `runBoundary`, a raised flag comes with
  keys of the rows of run `n` that are not apart, or with apart keys and a hit in the final cache.

The rows are `none` when run `n` does not reach its reveal step. The leanVM proof directories have
no lifetime scheduler. The module reuses the step lemmas of `Tree.lean`, `stepRound_ok`,
`jointKeyWorld_run_inv` and the zero-query lemmas of `LifetimeIdealBad`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace ThresholdLeanXmssSecurity.LifetimeRunBoundary

attribute [local instance] Classical.propDecidable

section Pause

variable {C : Committee} {E : Type}

/-- The program of a lifetime adversary after the keygen. -/
abbrev Program (C : Committee) (E : Type) := OracleComp (LocalSpec C + LifetimeSpec C E) Forgery

/-- The adversary, done or paused before a lifetime query. -/
inductive Pause (C : Committee) (E : Type) where
  | done (forgery : Forgery)
  | wait (q : LifetimeQuery C E) (k : LifetimeSpec C E q → Program C E)

variable {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Run the adversary with `impl` until it ends or it makes a lifetime query that `stop` selects. -/
def runTo (impl : QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT σ m))
    (stop : σ → LifetimeQuery C E → Prop) : Program C E → StateT σ m (Pause C E)
  | .pure f => pure (.done f)
  | .queryBind (.inr q) k => do
      if stop (← get) q then pure (.wait q k) else
        let a ← impl (.inr q)
        runTo impl stop (k a)
  | .queryBind (.inl t) k => do
      let a ← impl (.inl t)
      runTo impl stop (k a)

/-- The program that a pause leaves. -/
def Pause.rest : Pause C E → Program C E
  | .done f => (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery)
  | .wait q k => OracleComp.queryBind (spec := LocalSpec C + LifetimeSpec C E) (.inr q) k

theorem simulateQ_queryBind {α : Type} (impl : QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT σ m))
    (t : (LocalSpec C + LifetimeSpec C E).Domain)
    (k : (LocalSpec C + LifetimeSpec C E).Range t → OracleComp (LocalSpec C + LifetimeSpec C E) α) :
    simulateQ impl (OracleComp.queryBind t k) = impl t >>= fun a => simulateQ impl (k a) := by
  change simulateQ impl ((liftM (OracleSpec.query (spec := LocalSpec C + LifetimeSpec C E) t) :
    OracleComp (LocalSpec C + LifetimeSpec C E) _) >>= k) = _
  rw [simulateQ_query_bind]
  rfl

/-- The simulation of a program is the run up to a pause, then the simulation of the rest. -/
theorem simulateQ_eq_runTo (impl : QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT σ m))
    (stop : σ → LifetimeQuery C E → Prop) (p : Program C E) :
    simulateQ impl p = runTo impl stop p >>= fun pause => simulateQ impl pause.rest := by
  induction p using OracleComp.recOn with
  | pure f =>
    change simulateQ impl (pure f) = (pure (Pause.done f) : StateT σ m _) >>= _
    simp [Pause.rest]
  | queryBind t k ih =>
    rcases t with t | q
    · simp only [runTo, simulateQ_queryBind, bind_assoc, ih]
    · apply StateT.ext
      intro s
      by_cases hs : stop s q
      · simp [runTo, hs, Pause.rest, StateT.run_bind, StateT.run_get]
      · simp [runTo, hs, simulateQ_queryBind, ih, StateT.run_bind, StateT.run_get]

end Pause

section Steps

open LifetimePrfTransportProof LifetimeEmulatedBudget

variable {C : Committee} {E β : Type}

/-- The counted copy of the world on the adversary copy, and the free copy on the run-`n` copy.
The programming copy is not used by `worldRoles`. -/
def worldTo4 : QueryImpl (WorldSpec C) (OracleComp (Spec4 C))
  | .inl (.inl t) => (liftM ((Spec4 C).query (.inl (.inl (.inl t)))) : OracleComp (Spec4 C) _)
  | .inl (.inr _) => (pure false : OracleComp (Spec4 C) Bool)
  | .inr t => (liftM ((Spec4 C).query (.inr t)) : OracleComp (Spec4 C) _)

/-- `worldTo4` as a monad map. -/
def toRun4 : OracleComp (WorldSpec C) →ᵐ OracleComp (Spec4 C) where
  toFun _ p := simulateQ worldTo4 p
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

theorem toRun4_free {α : Type} (p : OracleComp (LocalSpec C) α) :
    toRun4 (free p) = targetCopy4 p := by
  change simulateQ worldTo4 (simulateQ _ p) = simulateQ _ p
  rw [LifetimeEmulatedBudget.simulateQ_comp]
  congr 1

theorem toRun4_counted {α : Type} (p : OracleComp (LocalSpec C) α) :
    toRun4 (worldRoles.adversary p) = advCopy4 p := by
  change simulateQ worldTo4 (worldRoles.adversary p) = _
  rw [LifetimeRealBad.worldAdversary_eq_simulateQ, LifetimeEmulatedBudget.simulateQ_comp]
  unfold advCopy4
  congr 1
  funext t
  rw [LifetimeRealBad.adversary_query]
  exact simulateQ_spec_query _ _

theorem roles4_self (n : ℕ) : roles4 (C := C) n n = ⟨advCopy4, targetCopy4⟩ := by
  simp [roles4]

theorem rolesHom_run4 (n : ℕ) : RolesHom toRun4 worldRoles (roles4 (C := C) n n) := by
  rw [roles4_self]
  exact ⟨fun p => toRun4_counted p, fun p => toRun4_free p⟩

/-- `stepRound` reads only the round of `roundAdversary`. -/
theorem stepRound_roundAdversary {α : Type} (Ro : Roles C (OracleComp (Spec4 C))) (D : C.Coalition)
    (sent : C.Party → C.Party → Option (Msg E)) (steps : C.Party → Step C E RealSpec α) :
    stepRound Ro D (roundAdversary (I := PEmpty) sent) noFunctionality () steps =
      stepRound Ro D (roundAdversary (I := Keys C) sent) noFunctionality () steps := rfl

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (D : C.Coalition) (n : ℕ)

/-- The start of run `n`, through its first setup data. -/
theorem startSteps_run4 (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    startSteps (roles4 n n) D (fun i => prssSetup i >>= k i) =
      (fun data i => suspendStep (k i) (prssInitialSteps D data i)) <$> targetCopy4 (prssInitialData D) := by
  rw [← hom_startSteps toRun4 worldRoles _ (rolesHom_run4 n), startSteps_prssSetup_bind,
    MonadHom.mmap_map, toRun4_free]

/-- The commit round of run `n` makes no oracle call. -/
theorem stepRound_commit4 (sent : C.Party → C.Party → Option (Msg E))
    (data : C.Party → Parts C × List HashOutput) (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    stepRound (roles4 n n) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
      (fun i => suspendStep (k i) (prssInitialSteps D data i)) =
      pure ((), (fun i => suspendStep (k i) (prssRevealStep D
        (fun i => (C.parties.any fun j => Msg.isAbort (prssCommitInbox D data sent i j)) = false)
        (fun i => (data i).1) (prssCommitInbox D data sent) i)), sent) := by
  rw [stepRound_roundAdversary, ← hom_stepRound toRun4 worldRoles _ (rolesHom_run4 n),
    stepRound_prssCommit_bind]
  simp [roundAdversary, worldRoles, counted]

/-- The reveal round of run `n` computes the reveal rows. -/
theorem stepRound_reveal4 (sent : C.Party → C.Party → Option (Msg E))
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    stepRound (roles4 n n) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
      (fun i => suspendStep (k i) (prssRevealStep D active parts committed i)) = (do
      let rows ← targetCopy4 (prssRevealRows D active parts committed sent)
      pure ((), (fun i => suspendStep (k i) (prssFinishStep i (rows i))), sent)) := by
  rw [stepRound_roundAdversary, ← hom_stepRound toRun4 worldRoles _ (rolesHom_run4 n),
    stepRound_prssReveal_bind]
  simp [roundAdversary, worldRoles, counted, toRun4_free]

end Steps

section Segments

open LifetimePrfTransportProof LifetimeEmulatedBudget

variable {C : Committee} {E : Type}

/-- The messages of a ceremony round. -/
abbrev Sent (C : Committee) (E : Type) := C.Party → C.Party → Option (Msg E)

/-- Branch on a pause before a start query. -/
def Pause.atStart {γ : Type} (p : Pause C E) (other : γ)
    (start : ThresholdLeanXmss.Tree → (Option (Sent C E) → Program C E) → γ) : γ :=
  match p with
  | .wait (.start tree) k => start tree k
  | _ => other

/-- Branch on a pause before a round query. -/
def Pause.atRound {γ : Type} (p : Pause C E) (other : γ)
    (round : Sent C E → (Option (Sent C E) → Program C E) → γ) : γ :=
  match p with
  | .wait (.round sent) k => round sent k
  | _ => other

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ)

/-- The free value oracle of the lifetime in `program4`. -/
def value4 (keys : C.Party → Keys C) (x : Point) : OracleComp (Spec4 C) Digest :=
  (base4 (C := C)).honest (liftComp (prfValue (honestSeeds D keys) x) _)

/-- The oracles of the adversary in `program4`, as `lifetimeGameWith` builds them. -/
def oracles4 (keys : C.Party → Keys C) (h : C.Party) :
    QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT (LifetimeState C E) (OracleComp (Spec4 C))) :=
  (fun t => StateT.lift ((base4 (C := C)).adversary (OracleComp.lift (OracleSpec.query t)))) +
    lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys (value4 D keys) h

/-- The run counter is `n`. A named proposition, so that its decision stays classical and no tactic
evaluates the counter. -/
def CountIs (n : ℕ) (st : LifetimeState C E) : Prop := st.runCount = n

/-- The admitted start of run `n`. -/
def StartStop (st : LifetimeState C E) : LifetimeQuery C E → Prop
  | .start tree => LifetimeProof.canStart attempts D st tree ∧ CountIs n st
  | _ => False

/-- A round query. -/
def RoundStop (_ : LifetimeState C E) : LifetimeQuery C E → Prop
  | .round _ => True
  | _ => False

/-- The program of operator `i` in run `n` after its PRSS setup. -/
def cont (keys : C.Party → Keys C) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (i : C.Party)
    (prss : PrssKeys C) : PartyM C E RealSpec TreeOutput :=
  ceremonyAfterSetup K circuits settings ⟨i, keys i, prss⟩ ((st.top i).getD emptyTop) tree

/-- The reveal round of run `n`. The adversary runs up to its next round query. When run `n` still
runs at the reveal step, the round computes the reveal rows. -/
def revealSegment (keys : C.Party → Keys C) (h : C.Party)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (prog : Program C E)
    (st : LifetimeState C E) :
    OracleComp (Spec4 C) ((Option (RevealRows C) × Program C E) × LifetimeState C E) :=
  (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st >>= fun r =>
    r.1.atRound (pure ((none, r.1.rest), r.2)) fun sent k' =>
      match r.2.running with
      | some (tree, fuel, steps) =>
        if CountIs (n + 1) r.2 ∧ steps = fun i => suspendStep (k i) (prssRevealStep D active parts committed i)
        then do
          let rows ← targetCopy4 (prssRevealRows D active parts committed sent)
          let next := fun i => suspendStep (k i) (prssFinishStep i (rows i))
          pure ((some rows, k' (some (toCoalition D next))),
            ({ r.2 with running := some (tree, fuel - 1, next) }).settle D)
        else pure ((none, r.1.rest), r.2)
      | none => pure ((none, r.1.rest), r.2)

/-- The commit round of run `n`. It makes no oracle call. -/
def commitSegment (keys : C.Party → Keys C) (h : C.Party)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (data : C.Party → Parts C × List HashOutput) (prog : Program C E) (st : LifetimeState C E) :
    OracleComp (Spec4 C) ((Option (RevealRows C) × Program C E) × LifetimeState C E) :=
  (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st >>= fun r =>
    r.1.atRound (pure ((none, r.1.rest), r.2)) fun sent k' =>
      match r.2.running with
      | some (tree, fuel, steps) =>
        if CountIs (n + 1) r.2 ∧ steps = fun i => suspendStep (k i) (prssInitialSteps D data i) then
          let committed := prssCommitInbox D data sent
          let active := fun i => (C.parties.any fun j => Msg.isAbort (committed i j)) = false
          let next := fun i => suspendStep (k i) (prssRevealStep D active (fun i => (data i).1) committed i)
          revealSegment K circuits settings attempts D n keys h k active (fun i => (data i).1) committed
            (k' (some (toCoalition D next))) (({ r.2 with running := some (tree, fuel - 1, next) }).settle D)
        else pure ((none, r.1.rest), r.2)
      | none => pure ((none, r.1.rest), r.2)

/-- The lifetime up to the reveal of run `n`. The adversary runs up to the admitted start of run
`n`, which samples the first setup data of run `n`, and then through the two setup rounds of run
`n`. -/
def startSegment (keys : C.Party → Keys C) (h : C.Party) (prog : Program C E) (st : LifetimeState C E) :
    OracleComp (Spec4 C) ((Option (RevealRows C) × Program C E) × LifetimeState C E) :=
  (runTo (oracles4 K circuits settings attempts D n keys h) (StartStop attempts D n) prog).run st >>=
    fun r => r.1.atStart (pure ((none, r.1.rest), r.2)) fun tree k' =>
      if LifetimeProof.canStart attempts D r.2 tree ∧ CountIs n r.2 then do
        let data ← targetCopy4 (prssInitialData D)
        let k := cont K circuits settings keys r.2 tree
        let next := fun i => suspendStep (k i) (prssInitialSteps D data i)
        commitSegment K circuits settings attempts D n keys h k data (k' (some (toCoalition D next)))
          (({ LifetimeProof.increment r.2 tree with
            running := some (tree, ceremonyFuel circuits settings, next) }).settle D)
      else pure ((none, r.1.rest), r.2)

theorem oracles4_inr (keys : C.Party → Keys C) (h : C.Party) (q : LifetimeQuery C E) :
    oracles4 K circuits settings attempts D n keys h (.inr q) =
      lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys (value4 D keys) h q := rfl

theorem run_rest_round (keys : C.Party → Keys C) (h : C.Party) (sent : Sent C E)
    (k' : Option (Sent C E) → Program C E) (st : LifetimeState C E) :
    (simulateQ (oracles4 K circuits settings attempts D n keys h) (Pause.wait (.round sent) k').rest).run st =
      (lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys (value4 D keys) h
        (.round sent)).run st >>= fun a =>
        (simulateQ (oracles4 K circuits settings attempts D n keys h) (k' a.1)).run a.2 := by
  simp only [Pause.rest, simulateQ_queryBind, StateT.run_bind, oracles4_inr]
  rfl

/-- The reveal segment followed by the rest is the simulation of the program. -/
theorem reveal_split (keys : C.Party → Keys C) (h : C.Party)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (prog : Program C E)
    (st : LifetimeState C E) :
    (simulateQ (oracles4 K circuits settings attempts D n keys h) prog).run st =
      revealSegment K circuits settings attempts D n keys h k active parts committed prog st >>= fun r =>
        (simulateQ (oracles4 K circuits settings attempts D n keys h) r.1.2).run r.2 := by
  rw [simulateQ_eq_runTo _ RoundStop prog, StateT.run_bind]
  unfold revealSegment
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with ⟨p, st'⟩
  cases p with
  | done f => simp [Pause.atRound]
  | wait q k' =>
    cases q with
    | round sent =>
      simp only [Pause.atRound]
      cases hr : st'.running with
      | none => simp
      | some x =>
        rcases x with ⟨tree, fuel, steps⟩
        dsimp only
        split_ifs with hg
        · obtain ⟨hc, rfl⟩ := hg
          have hc' : st'.runCount = n + 1 := hc
          rw [run_rest_round, LifetimeProof.run_round, hr]
          simp only [hc', Nat.add_sub_cancel, stepRound_reveal4, bind_assoc, pure_bind]
        · simp
    | _ => simp [Pause.atRound]

/-- The commit segment followed by the rest is the simulation of the program. -/
theorem commit_split (keys : C.Party → Keys C) (h : C.Party)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (data : C.Party → Parts C × List HashOutput) (prog : Program C E) (st : LifetimeState C E) :
    (simulateQ (oracles4 K circuits settings attempts D n keys h) prog).run st =
      commitSegment K circuits settings attempts D n keys h k data prog st >>= fun r =>
        (simulateQ (oracles4 K circuits settings attempts D n keys h) r.1.2).run r.2 := by
  rw [simulateQ_eq_runTo _ RoundStop prog, StateT.run_bind]
  unfold commitSegment
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with ⟨p, st'⟩
  cases p with
  | done f => simp [Pause.atRound]
  | wait q k' =>
    cases q with
    | round sent =>
      simp only [Pause.atRound]
      cases hr : st'.running with
      | none => simp
      | some x =>
        rcases x with ⟨tree, fuel, steps⟩
        dsimp only
        split_ifs with hg
        · obtain ⟨hc, rfl⟩ := hg
          have hc' : st'.runCount = n + 1 := hc
          rw [run_rest_round, LifetimeProof.run_round, hr]
          simp only [hc', Nat.add_sub_cancel, stepRound_commit4, pure_bind]
          exact reveal_split K circuits settings attempts D n keys h k _ _ _ _ _
        · simp
    | _ => simp [Pause.atRound]

set_option maxRecDepth 200000 in
/-- The start segment followed by the rest is the simulation of the program. -/
theorem start_split (keys : C.Party → Keys C) (h : C.Party) (prog : Program C E)
    (st : LifetimeState C E) :
    (simulateQ (oracles4 K circuits settings attempts D n keys h) prog).run st =
      startSegment K circuits settings attempts D n keys h prog st >>= fun r =>
        (simulateQ (oracles4 K circuits settings attempts D n keys h) r.1.2).run r.2 := by
  rw [simulateQ_eq_runTo _ (StartStop attempts D n) prog, StateT.run_bind]
  unfold startSegment
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with ⟨p, st'⟩
  cases p with
  | done f => simp [Pause.atStart]
  | wait q k' =>
    cases q with
    | start tree =>
      simp only [Pause.atStart]
      split_ifs with hg
      · obtain ⟨hc, hn⟩ := hg
        simp only [Pause.rest, simulateQ_queryBind, StateT.run_bind, oracles4_inr]
        rw [LifetimeProof.run_start, if_neg (not_not.mpr hc), show st'.runCount = n from hn]
        simp only [ceremony_eq_prssSetup_bind, bind_assoc]
        change ((startSteps (roles4 n n) D fun i =>
          prssSetup i >>= cont K circuits settings keys st' tree i) >>= _) = _
        rw [startSteps_run4, bind_map_left]
        refine bind_congr fun data => ?_
        simp only [pure_bind]
        apply commit_split
      · simp
    | _ => simp [Pause.atStart]

variable (A : LifetimeAdversary C E)

/-- The state of the lifetime at the reveal of run `n`. It holds the keys and the operator `h` of the
keygen, the reveal rows of run `n`, the rest of the adversary and the state of the lifetime
oracles. The rows are `none` when run `n` does not reach its reveal step. -/
structure Boundary (C : Committee) (E : Type) where
  keys : C.Party → Keys C
  h : C.Party
  rows : Option (RevealRows C)
  rest : Program C E
  state : LifetimeState C E

/-- `program4` up to the reveal of run `n`. It is `none` when the lifetime ends after the keygen. -/
def setup4 : OracleComp (Spec4 C) (Option (Boundary C E)) := do
  let state ← (base4 (C := C)).adversary (A.keygen.start (corruptInputs D fun _ => ()) [])
  let (state, outputs) ← executePhase base4 D A.keygen noFunctionality setupRounds state
    fun i => (keygen i : PartyM C E RealSpec (Keys C))
  let some h := C.parties.find? (· ∉ D.1) | pure none
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure none else do
  let keys := fun i => (outputs i).getD default
  let r ← startSegment K circuits settings attempts D n keys h (A.run state (keys h).parameter)
    (LifetimeProof.initial D)
  pure (some ⟨keys, h, r.1.1, r.1.2, r.2⟩)

/-- The win test of `program4`. -/
def finish4 (keys : C.Party → Keys C) (h : C.Party) (r : Forgery × LifetimeState C E) :
    OracleComp (Spec4 C) Bool :=
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (Spec4 C) β :=
    fun oa => (base4 (C := C)).honest (liftComp oa _)
  if ¬ ∀ i, i ∉ D.1 → (r.2.top i).isSome then pure false else do
  let some (_, top) := r.2.publicKey (keys h).parameter h | pure false
  forgeryWins lift (dealtWith lift (keys h).parameter keys top (value4 D keys)) r.2.sign r.1

/-- `program4` after the reveal of run `n`. -/
def tail4 : Option (Boundary C E) → OracleComp (Spec4 C) Bool
  | none => pure false
  | some b => (simulateQ (oracles4 K circuits settings attempts D n b.keys b.h) b.rest).run b.state >>=
      finish4 D b.keys b.h

/-- `program4` is its run up to the reveal of run `n`, then the rest. -/
theorem program4_split :
    program4 D K circuits settings attempts A n =
      setup4 K circuits settings attempts D n A >>= tail4 K circuits settings attempts D n := by
  unfold program4 lifetimeGameWith setup4
  simp only [bind_assoc]
  refine bind_congr fun state => ?_
  refine bind_congr fun r => ?_
  rcases r with ⟨state', outputs⟩
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => simp [tail4]
  | some h =>
    dsimp only
    by_cases hall : ∀ i, i ∉ D.1 → (outputs i).isSome
    · rw [if_neg (not_not.mpr hall), if_neg (not_not.mpr hall)]
      change (simulateQ (oracles4 K circuits settings attempts D n (fun i => (outputs i).getD default) h)
        (A.run state' ((outputs h).getD default).parameter)).run (LifetimeProof.initial D) >>=
          finish4 D (fun i => (outputs i).getD default) h = _
      rw [start_split K circuits settings attempts D n _ h, bind_assoc, bind_assoc]
      refine bind_congr fun r => ?_
      rw [pure_bind]
      rfl
    · simp [hall, tail4]

end Segments

section World

open LifetimePrfTransportProof LifetimeHybridOrder

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E)

/-- The interpretation of `program4` as hybrid `n` (`program4_left`). -/
abbrev hybridImpl : QueryImpl (Spec4 C) (EmulationM C) := impl4 D (lifetimeHybridRoles D 0 0)

/-- Hybrid `n` up to the reveal of run `n`. It returns the state at the reveal, the stream table of
the earlier runs and the log. -/
def worldSetup : OracleComp (WorldSpec C) ((Option (Boundary C E) × StreamCache C) × CallLog C) :=
  ((simulateQ (hybridImpl D) (setup4 K circuits settings attempts D n A)).run ∅).run

/-- Hybrid `n` after the reveal of run `n`. -/
def worldTail (r : (Option (Boundary C E) × StreamCache C) × CallLog C) : OracleComp (WorldSpec C) Bool :=
  (fun y => y.1.1) <$> ((simulateQ (hybridImpl D) (tail4 K circuits settings attempts D n r.1.1)).run r.1.2).run

/-- The world game of hybrid `n` is its run up to the reveal of run `n`, then the rest. -/
theorem hybrid_split :
    emulationGame (lifetimeGameWith K circuits settings attempts (lifetimeHybridRoles D n)
      (lifetimeHybridRoles D n n) D A) =
      worldSetup K circuits settings attempts D n A >>= worldTail K circuits settings attempts D n := by
  rw [← program4_left, program4_split, simulateQ_bind]
  unfold emulationGame worldSetup worldTail
  simp [StateT.run_bind, WriterT.run_bind, map_bind]

end World

section KeyWorld

variable {C : Committee}

/-- A free stream under a hidden name, the only call that records a private stream key. -/
def FreeHidden (D : C.Coalition) : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr x)) => Hidden D x.1
  | _ => False

/-- Without a private key in use, the ideal joint world answers a call other than a free stream under
a hidden name as the world does on the public cache. -/
theorem jointKeyWorld_false_run_eq_hidden (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (hq : ¬ FreeHidden D q) (s : KeyJointState C) (hs : ∀ k, s.used k = none) :
    (jointKeyWorld prims D false q).run s =
      (fun r => (r.1, { s with hash := r.2 })) <$> (worldAnswer prims q).run s.hash := by
  rcases q with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · exact jointKeyWorld_false_run_eq prims D _ (by simp [FreeStream]) s hs
  · exact jointKeyWorld_false_run_eq prims D _ (by simp [FreeStream]) s hs
  · exact jointKeyWorld_false_run_eq prims D _ (by simp [FreeStream]) s hs
  · exact jointKeyWorld_false_run_eq prims D _ (by simp [FreeStream]) s hs
  · exact jointKeyWorld_false_run_eq prims D _ (by simp [FreeStream]) s hs
  · exact jointKeyWorld_false_run_eq prims D _ (by simp [FreeStream]) s hs
  · have hh : ¬ Hidden D x.1 := hq
    have hrisk : keyJointRisk D (.inr (.inr (.inr x))) s = false := by
      simp [keyJointRisk, hh, hs]
    have hcore : (jointKeyWorldCore prims D false (.inr (.inr (.inr x)))).run s =
        (fun r => (r.1, { s with hash := r.2 })) <$> (worldAnswer prims (.inr (.inr (.inr x)))).run s.hash := by
      simp only [jointKeyWorldCore, if_neg hh, jointLocal_false, onJointHash]
      rfl
    simp only [jointKeyWorld, StateT.run_mk, hcore, hrisk, Bool.or_false, Functor.map_map]

/-- A computation without a free stream under a hidden name runs in the ideal joint world as in the
world, from a state with no private key in use. -/
theorem jointKeyWorld_false_simulate_eq_hidden (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (hoa : IsQueryBoundP oa (FreeHidden D) 0)
    (s : KeyJointState C) (hs : ∀ k, s.used k = none) :
    (simulateQ (jointKeyWorld prims D false) oa).run s =
      (fun r => (r.1, { s with hash := r.2 })) <$> (simulateQ (worldAnswer prims) oa).run s.hash := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ FreeHidden D t := by
      rcases hoa.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (FreeHidden D) 0 := fun u => by
      have := hoa.2 u
      rwa [if_neg ht] at this
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, map_bind]
    rw [jointKeyWorld_false_run_eq_hidden prims D t ht s hs, bind_map_left]
    refine bind_congr fun r => ?_
    exact ih r.1 (hk r.1) { s with hash := r.2 } hs

variable (prims : Primitives) (D : C.Coalition) {β : Type}

/-- The ideal joint world after a boundary, paired with the run of the world up to it. -/
def boundaryOf (setup : OracleComp (WorldSpec C) β) (tail : β → OracleComp (WorldSpec C) Bool) :
    ProbComp ((β × HashCache C) × (Bool × KeyJointState C)) :=
  worldRun prims setup >>= fun r => (fun y => (r, y)) <$>
    (simulateQ (jointKeyWorld prims D false) (tail r.1)).run (boundaryState r.2)

/-- The stream-key bad event of a game is the bad event after a boundary before which no free stream
runs under a hidden name. -/
theorem probBad_eq_boundaryOf (game : OracleComp (WorldSpec C) Bool)
    (setup : OracleComp (WorldSpec C) β) (tail : β → OracleComp (WorldSpec C) Bool)
    (hsplit : game = setup >>= tail) (hquiet : IsQueryBoundP setup (FreeHidden D) 0) :
    probBad_streamKey prims D game =
      (Pr[fun y => y.2.2.bad = true | boundaryOf prims D setup tail]).toReal := by
  rw [probBad_streamKey_eq_ideal, hsplit, simulateQ_bind, StateT.run_bind,
    jointKeyWorld_false_simulate_eq_hidden prims D _ hquiet keyJointInitial (fun _ => rfl),
    bind_map_left]
  simp only [boundaryOf, probEvent_bind_eq_tsum, probEvent_map]
  rfl

/-- After a boundary whose tail makes only free calls that the rows allow, a raised flag comes with
keys that are not apart or with a hit. -/
theorem boundaryOf_bad (setup : OracleComp (WorldSpec C) β) (tail : β → OracleComp (WorldSpec C) Bool)
    (rowsAt : β → RevealRows C)
    (hallowed : ∀ r ∈ support setup, IsQueryBoundP (tail r) (Unallowed (rowsAt r)) 0) :
    ∀ y ∈ support (boundaryOf prims D setup tail), y.2.2.bad = true →
      ¬ KeysApart D (rowsAt y.1.1) ∨
        (KeysApart D (rowsAt y.1.1) ∧ KeyHit D (rowsAt y.1.1) y.2.2.hash) := by
  intro y hy hbad
  simp only [boundaryOf, support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hy
  obtain ⟨r, hr, w, hw, rfl⟩ := hy
  have hr' : r.1 ∈ support setup := by
    apply support_simulateQ_run'_subset (worldAnswer prims) setup ∅
    simp only [StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨r, hr, rfl⟩
  by_cases hg : KeysApart D (rowsAt r.1)
  · right
    refine ⟨hg, ?_⟩
    have h := jointKeyWorld_run_inv prims D (rowsAt r.1) hg _ (hallowed r.1 hr') (boundaryState r.2)
      (jointInv_boundaryState D _ _) w hw
    exact h.1.2 hbad
  · exact Or.inl hg

end KeyWorld

section Transfer

open LifetimePrfTransportProof LifetimeHybridOrder LifetimeKeygenPrograms LifetimeIdealBad

variable {C : Committee}

/-- A world predicate that no counted or programming call meets. -/
def FreeOnly (P : (WorldSpec C).Domain → Prop) : Prop := ∀ t, ¬ P (.inl t)

/-- No call in `P`, from every stream table. -/
def QuietP (P : (WorldSpec C).Domain → Prop) {α : Type} (x : EmulationM C α) : Prop :=
  ∀ cache, IsQueryBoundP ((x.run cache).run) P 0

theorem quietP_bind {P : (WorldSpec C).Domain → Prop} {α β : Type} {x : EmulationM C α}
    {f : α → EmulationM C β} (hx : QuietP P x) (hf : ∀ a, QuietP P (f a)) : QuietP P (x >>= f) := by
  intro cache
  simp only [StateT.run_bind, WriterT.run_bind']
  exact qb0_bind' (hx cache) fun r => (isQueryBoundP_map_iff _ _ _).2 (hf r.1.1 r.1.2)

/-- A simulation is quiet when each step outside `P4` is quiet and the computation makes no call in
`P4`. -/
theorem quietP_simulate {P : (WorldSpec C).Domain → Prop} {ι α : Type} {spec : OracleSpec ι}
    {P4 : ι → Prop} (impl : QueryImpl spec (EmulationM C))
    (h : ∀ t, ¬ P4 t → QuietP P (impl t)) (oa : OracleComp spec α) (hoa : IsQueryBoundP oa P4 0) :
    QuietP P (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ P4 t := hoa.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact quietP_bind (h t ht) fun u => ih u (by simpa [ht] using hoa.2 u)

theorem quietP_lift {P : (WorldSpec C).Domain → Prop} {α : Type} {y : OracleComp (WorldSpec C) α}
    (hy : IsQueryBoundP y P 0) : QuietP P (StateT.lift (liftM y) : EmulationM C α) := by
  intro cache
  simp only [StateT.run_lift, WriterT.run_bind', WriterT.run_monadLift', liftM]
  exact qb0_bind' ((isQueryBoundP_map_iff _ _ _).2 hy) fun _ =>
    isQueryBoundP_map_iff _ _ _ |>.2 (isQueryBoundP_pure _ _ _)

theorem counted_quietP {P : (WorldSpec C).Domain → Prop} (hP : FreeOnly P) {α : Type}
    (oa : OracleComp (LocalSpec C) α) : IsQueryBoundP (worldRoles.adversary oa) P 0 := by
  change IsQueryBoundP (counted (liftComp oa _)) P 0
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [liftComp_bind, counted_bind]
    have e : counted (liftComp (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _)
        (SimulatorSpec C)) =
        (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) := by
      rcases t with t | (q | x) <;> rfl
    rw [e]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (hP _), fun u => by simpa [hP] using ih u⟩

theorem observe_quietP {P : (WorldSpec C).Domain → Prop} (hP : FreeOnly P) {α : Type}
    (p : OracleComp (LocalSpec C) α) : IsQueryBoundP (observe p) P 0 := by
  unfold observe
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind']
    refine qb0_bind' ?_ fun r => (isQueryBoundP_map_iff _ _ _).2 (ih r.1)
    rcases t with u | q | x
    · simp only [WriterT.run_monadLift', liftM]
      exact (isQueryBoundP_map_iff _ _ _).2 (counted_quietP hP _)
    · simp only [WriterT.run_bind', WriterT.run_monadLift', liftM]
      refine qb0_bind' ((isQueryBoundP_map_iff _ _ _).2 (counted_quietP hP _)) fun r => ?_
      rw [isQueryBoundP_map_iff]
      exact qb0_bind' (isQueryBoundP_pure _ _ _) fun _ => (isQueryBoundP_map_iff _ _ _).2
        (isQueryBoundP_pure _ _ _)
    · simp only [WriterT.run_monadLift', liftM]
      exact (isQueryBoundP_map_iff _ _ _).2 (counted_quietP hP _)

theorem free_query_quietP {P : (WorldSpec C).Domain → Prop} (t : (LocalSpec C).Domain)
    (ht : ¬ P (.inr t)) :
    IsQueryBoundP (free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))) P 0 := by
  have e : free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t)) =
      (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) := by
    simp only [free]
    exact simulateQ_spec_query _ _
  rw [e]
  exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h ht

theorem free_sample_quietP {P : (WorldSpec C).Domain → Prop} (hP : ∀ u, ¬ P (.inr (.inl u)))
    {α : Type} (p : ProbComp α) : IsQueryBoundP (free (liftComp p (LocalSpec C))) P 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [liftComp_bind]
    unfold free
    rw [simulateQ_bind]
    refine qb0_bind' ?_ fun u => ih u
    rw [liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hP _)

theorem adversary_quietP {P : (WorldSpec C).Domain → Prop} (hP : FreeOnly P) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C) α) : QuietP P ((emulatedRoles D).adversary p) := by
  intro cache
  simp only [emulatedRoles, StateT.run_lift, WriterT.run_bind']
  exact qb0_bind' (observe_quietP hP p) fun _ =>
    (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_pure _ _ _)

theorem base_quietP {P : (WorldSpec C).Domain → Prop} (D : C.Coalition) (t : (LocalSpec C).Domain)
    (ht : ¬ P (.inr t)) :
    QuietP P ((lifetimeHybridRoles D 0 0).honest (OracleComp.lift (OracleSpec.query t))) := by
  simpa [lifetimeHybridRoles] using quietP_lift (C := C) (free_query_quietP t ht)

/-- A free PRG call of the keygen and the signing, or of run `n`. Every other call of `program4`
reaches the world without a free stream under a hidden name. -/
def Prefix4 : (Spec4 C).Domain → Prop
  | .inl (.inr t) => PrgCall t
  | .inr t => PrgCall t
  | _ => False

/-- The calls that the tail of `program4` must avoid. They are an emulated call of an earlier run,
and a free call of the keygen, the signing or run `n` that the rows do not allow. -/
def Tail4 (rows : RevealRows C) : (Spec4 C).Domain → Prop
  | .inl (.inl (.inl _)) => False
  | .inl (.inl (.inr _)) => True
  | .inl (.inr t) => ¬ Allowed rows t
  | .inr t => ¬ Allowed rows t

theorem impl4_quiet_hidden (D : C.Coalition) (t : (Spec4 C).Domain) (ht : ¬ Prefix4 t) :
    QuietP (FreeHidden D) (impl4 D (lifetimeHybridRoles D 0 0) t) := by
  have hP : FreeOnly (FreeHidden D) := fun t => by simp [FreeHidden]
  rcases t with ((t | t) | t) | t
  · exact adversary_quietP hP D _
  · change QuietP _ ((emulatedRoles D).honest (OracleComp.lift (OracleSpec.query t)))
    simp only [emulatedRoles]
    rw [simulateQ_spec_query]
    rcases t with u | q | x
    · exact quietP_lift (free_query_quietP _ (by simp [FreeHidden]))
    · exact quietP_lift (free_query_quietP _ (by simp [FreeHidden]))
    · dsimp only
      split
      · intro cache
        simp only [StateT.run_mk, WriterT.run_monadLift', liftM]
        exact (isQueryBoundP_map_iff _ _ _).2 (free_sample_quietP (by simp [FreeHidden]) _)
      · rename_i hh
        exact quietP_lift (free_query_quietP _ hh)
  · exact base_quietP D t (fun h => ht (by rcases t with u | q | x <;> simp_all [FreeHidden, Prefix4, PrgCall]))
  · exact base_quietP D t (fun h => ht (by rcases t with u | q | x <;> simp_all [FreeHidden, Prefix4, PrgCall]))

theorem impl4_quiet_tail (D : C.Coalition) (rows : RevealRows C) (t : (Spec4 C).Domain)
    (ht : ¬ Tail4 rows t) : QuietP (Unallowed rows) (impl4 D (lifetimeHybridRoles D 0 0) t) := by
  have hP : FreeOnly (Unallowed rows) := fun t => by simp [Unallowed]
  rcases t with ((t | t) | t) | t
  · exact adversary_quietP hP D _
  · exact absurd trivial ht
  · exact base_quietP D t ht
  · exact base_quietP D t ht

/-- Every output of an emulation comes from an output of the simulated computation. -/
theorem support_emulation {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (EmulationM C))
    (oa : OracleComp spec α) (cache : StreamCache C) :
    ∀ r ∈ support ((simulateQ impl oa).run cache).run, r.1.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure] at hr
    simp_all
  | query_bind t k ih =>
    intro r hr
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
      support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hr
    obtain ⟨x, -, y, hy, rfl⟩ := hr
    exact (mem_support_bind_iff _ _ _).mpr ⟨x.1.1, mem_support_query _ _, ih x.1.1 x.1.2 y hy⟩

end Transfer

section Walk

open LifetimePrfTransportProof LifetimeIdealBad

variable {C : Committee} {E : Type}

/-- The adversary copy and the free copy of `program4` never meet `P`. -/
def BaseFree (P : (Spec4 C).Domain → Prop) : Prop :=
  ∀ t, ¬ P (.inl (.inl (.inl t))) ∧ ¬ P (.inl (.inr t))

/-- Both roles meet `P` on no call. -/
def RolesQuiet (P : (Spec4 C).Domain → Prop) (Ro : Roles C (OracleComp (Spec4 C))) : Prop :=
  ∀ {α : Type} (p : OracleComp (LocalSpec C) α),
    IsQueryBoundP (Ro.adversary p) P 0 ∧ IsQueryBoundP (Ro.honest p) P 0

section Copies

variable {P : (Spec4 C).Domain → Prop} {α : Type} (p : OracleComp (LocalSpec C) α)

theorem advCopy4_quietP (h : ∀ t, ¬ P (.inl (.inl (.inl t)))) : IsQueryBoundP (advCopy4 p) P 0 :=
  LifetimeKeygenPrograms.qb0_simulateQ (p := P) _
    (fun (t : (LocalSpec C).Domain) => (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (h t)) p

theorem emulCopy4_quietP (h : ∀ t, ¬ P (.inl (.inl (.inr t)))) : IsQueryBoundP (emulCopy4 p) P 0 :=
  LifetimeKeygenPrograms.qb0_simulateQ (p := P) _
    (fun (t : (LocalSpec C).Domain) => (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (h t)) p

theorem freeCopy4_quietP (h : ∀ t, ¬ P (.inl (.inr t))) : IsQueryBoundP (freeCopy4 p) P 0 :=
  LifetimeKeygenPrograms.qb0_simulateQ (p := P) _
    (fun (t : (LocalSpec C).Domain) => (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (h t)) p

theorem targetCopy4_quietP (h : ∀ t, ¬ P (.inr t)) : IsQueryBoundP (targetCopy4 p) P 0 :=
  LifetimeKeygenPrograms.qb0_simulateQ (p := P) _
    (fun (t : (LocalSpec C).Domain) => (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (h t)) p

end Copies

theorem base4_quiet {P : (Spec4 C).Domain → Prop} (hP : BaseFree P) : RolesQuiet P (base4 (C := C)) :=
  fun p => ⟨advCopy4_quietP p (fun t => (hP t).1), freeCopy4_quietP p (fun t => (hP t).2)⟩

theorem roFree_quietP {P : (Spec4 C).Domain → Prop} (hP : BaseFree P) {α : Type}
    (p : OracleComp (RoSpec C) α) : IsQueryBoundP (roFree p) P 0 :=
  freeCopy4_quietP _ (fun t => (hP t).2)

/-- A later run uses the adversary copy only. -/
theorem roles4_later_quiet {P : (Spec4 C).Domain → Prop} (hP : BaseFree P) {n r : ℕ} (hr : n < r) :
    RolesQuiet P (roles4 (C := C) n r) := by
  simp only [roles4, show ¬ r < n by omega, show r ≠ n by omega, if_false]
  exact fun p => ⟨advCopy4_quietP p (fun t => (hP t).1), advCopy4_quietP p (fun t => (hP t).1)⟩

/-- An earlier run uses the adversary copy and the emulated copy. -/
theorem roles4_earlier_quiet {P : (Spec4 C).Domain → Prop} (hP : BaseFree P)
    (h2 : ∀ t, ¬ P (.inl (.inl (.inr t)))) {n r : ℕ} (hr : r < n) :
    RolesQuiet P (roles4 (C := C) n r) := by
  simp only [roles4, hr, if_true]
  exact fun p => ⟨advCopy4_quietP p (fun t => (hP t).1), emulCopy4_quietP p h2⟩

variable {P : (Spec4 C).Domain → Prop} {Ro : Roles C (OracleComp (Spec4 C))}

theorem startSteps_quietP (hR : RolesQuiet P Ro) {α : Type} (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec α) : IsQueryBoundP (startSteps Ro D program) P 0 := by
  apply isQueryBoundP_sequenceFin
  intro i
  split
  · exact isQueryBoundP_pure _ _ _
  · exact (hR _).2

theorem stepRound_quietP (hR : RolesQuiet P Ro) {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (stepRound Ro D A noFunctionality state steps) P 0 := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  refine zero_bind P (hR _).1 fun r _ => zero_bind P (zero_sequenceFin _ _ fun j => ?_)
    fun _ _ => isQueryBoundP_pure _ _ _
  cases steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | wait out resume =>
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact (hR _).2
  | call input _ => exact input.elim

theorem executeRounds_quietP (hR : RolesQuiet P Ro) {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (executeRounds Ro D A noFunctionality fuel state steps) P 0 := by
  induction fuel generalizing state steps with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ fuel ih =>
    rw [executeRounds]
    split
    · exact isQueryBoundP_pure _ _ _
    · exact zero_bind P (stepRound_quietP hR D A state steps) fun r _ => ih r.1 r.2.1

theorem executePhase_quietP (hR : RolesQuiet P Ro) {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    IsQueryBoundP (executePhase Ro D A noFunctionality fuel state program) P 0 := by
  unfold executePhase
  exact zero_bind P (startSteps_quietP hR D program) fun steps _ =>
    executeRounds_quietP hR D A fuel state steps

/-- A run of the adversary up to a pause keeps an invariant and avoids `P`, when each step that it
runs does. At a pause, `stop` holds. -/
theorem runTo_quietP {σ : Type} (impl : QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT σ (OracleComp (Spec4 C))))
    (stop : σ → LifetimeQuery C E → Prop) (Inv : σ → Prop)
    (hstep : ∀ t s, Inv s → (∀ q, t = .inr q → ¬ stop s q) →
      IsQueryBoundP ((impl t).run s) P 0 ∧ ∀ r ∈ support ((impl t).run s), Inv r.2)
    (prog : Program C E) (s : σ) (hs : Inv s) :
    IsQueryBoundP ((runTo impl stop prog).run s) P 0 ∧
      ∀ r ∈ support ((runTo impl stop prog).run s), Inv r.2 ∧
        ∀ q k, r.1 = .wait q k → stop r.2 q := by
  induction prog using OracleComp.recOn generalizing s with
  | pure f =>
    refine ⟨isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
    change r ∈ support (pure (Pause.done f, s) : OracleComp (Spec4 C) _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hs, fun q k h => by cases h⟩
  | queryBind t k ih =>
    rcases t with t | q
    · have h := hstep (.inl t) s hs (fun q h => by cases h)
      simp only [runTo, StateT.run_bind]
      refine ⟨zero_bind P h.1 fun r hr => (ih r.1 r.2 (h.2 r hr)).1, fun r hr => ?_⟩
      obtain ⟨x, hx, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      exact (ih x.1 x.2 (h.2 x hx)).2 r hr
    · by_cases hq : stop s q
      · simp only [runTo, StateT.run_bind, StateT.run_get, pure_bind, hq, if_true, StateT.run_pure]
        refine ⟨isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        refine ⟨hs, fun q' k' h => ?_⟩
        cases h
        exact hq
      · have h := hstep (.inr q) s hs (fun q' h => by cases h; exact hq)
        simp only [runTo, StateT.run_bind, StateT.run_get, pure_bind, hq, if_false]
        refine ⟨zero_bind P h.1 fun r hr => (ih r.1 r.2 (h.2 r hr)).1, fun r hr => ?_⟩
        obtain ⟨x, hx, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
        exact (ih x.1 x.2 (h.2 x hx)).2 r hr

theorem signerDealt_quietP (hP : BaseFree P) (keys : C.Party → Keys C)
    (value : Point → OracleComp (Spec4 C) Digest) (hv : ∀ x, IsQueryBoundP (value x) P 0)
    (st : LifetimeState C E) (i : C.Party) :
    DealtQuiet P (ThresholdLeanXmss.signerDealt roFree keys value st i) :=
  ⟨hv, fun _ _ _ _ => roFree_quietP hP _, fun _ => isQueryBoundP_pure _ _ _⟩

theorem signAs_quietP (hP : BaseFree P) (keys : C.Party → Keys C)
    (value : Point → OracleComp (Spec4 C) Digest) (hv : ∀ x, IsQueryBoundP (value x) P 0)
    (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E) :
    IsQueryBoundP (LifetimeProof.signAs base4 keys value i q st) P 0 := by
  unfold LifetimeProof.signAs
  exact zero_bind P (tsig_quiet P roFree (fun p _ => roFree_quietP hP p) _
    (signerDealt_quietP hP keys value hv st i) q st.sign) fun _ _ => isQueryBoundP_pure _ _ _

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ)

theorem value4_quietP (hP : BaseFree P) (keys : C.Party → Keys C) (x : Point) :
    IsQueryBoundP (value4 D keys x) P 0 :=
  roFree_quietP hP _

set_option maxRecDepth 4000 in
/-- One step of the oracles of `program4` avoids `P`, when the roles of the run that it starts or
steps avoid `P`. -/
theorem oracles4_quietP (hP : BaseFree P) (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (hstart : ∀ tree, t = .inr (.start tree) → LifetimeProof.canStart attempts D st tree →
      RolesQuiet P (roles4 (C := C) n st.runCount))
    (hround : ∀ sent, t = .inr (.round sent) → st.running ≠ none →
      RolesQuiet P (roles4 (C := C) n (st.runCount - 1))) :
    IsQueryBoundP ((oracles4 K circuits settings attempts D n keys h t).run st) P 0 := by
  have hv := value4_quietP D hP keys
  rcases t with t | q
  · change IsQueryBoundP ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) P 0
    rw [StateT.run_lift]
    exact zero_bind P (advCopy4_quietP _ fun t => (hP t).1) fun _ _ => isQueryBoundP_pure _ _ _
  · rw [oracles4_inr]
    cases q with
    | sign q =>
      cases q with
      | corrupt i => exact isQueryBoundP_pure _ _ _
      | tree b =>
        rw [LifetimeProof.run_sign_tree]
        exact signAs_quietP hP keys _ hv _ _ st
      | round1 i J e message =>
        rw [LifetimeProof.run_round1]
        split
        · exact isQueryBoundP_pure _ _ _
        · exact signAs_quietP hP keys _ hv _ _ _
      | round2 i J e message parts =>
        rw [LifetimeProof.run_round2]
        split
        · exact isQueryBoundP_pure _ _ _
        · exact signAs_quietP hP keys _ hv _ _ _
    | publicKey => exact isQueryBoundP_pure _ _ _
    | start tree =>
      rw [LifetimeProof.run_start]
      split
      · exact isQueryBoundP_pure _ _ _
      · rename_i hc
        exact zero_bind P (startSteps_quietP (hstart tree rfl (not_not.mp hc)) D _) fun _ _ =>
          isQueryBoundP_pure _ _ _
    | round sent =>
      rw [LifetimeProof.run_round]
      cases hr : st.running with
      | none => exact isQueryBoundP_pure _ _ _
      | some x =>
        rcases x with ⟨tree, fuel, steps⟩
        exact zero_bind P (stepRound_quietP (hround sent rfl (by simp [hr])) D _ _ _) fun _ _ =>
          isQueryBoundP_pure _ _ _

/-- One step of the oracles keeps the run counter, or it starts a run that it may start. -/
theorem oracles4_runCount (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (r : _ × LifetimeState C E) (hr : r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run st)) :
    r.2.runCount = st.runCount ∨ ∃ tree, t = .inr (.start tree) ∧
      LifetimeProof.canStart attempts D st tree ∧ r.2.runCount = st.runCount + 1 := by
  rcases t with t | q
  · left
    change r ∈ support ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) at hr
    rw [StateT.run_lift] at hr
    obtain ⟨a, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  · rw [oracles4_inr] at hr
    have hc := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts _ _ D keys _ h q st r hr
    cases q with
    | start tree =>
      by_cases hs : LifetimeProof.canStart attempts D st tree
      · cases hn : LifetimeProof.newRun (LifetimeQuery.start tree) r.1 with
        | none => left; simpa [hn] using hc
        | some x => right; exact ⟨tree, rfl, hs, by simpa [hn] using hc⟩
      · left
        rw [LifetimeProof.run_start, if_pos hs] at hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
    | _ => left; simpa [LifetimeProof.newRun] using hc

theorem oracles4_invariant (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (hs : LifetimeProof.RunInvariant attempts st)
    (r : _ × LifetimeState C E) (hr : r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run st)) :
    LifetimeProof.RunInvariant attempts r.2 := by
  rcases t with t | q
  · change r ∈ support ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) at hr
    rw [StateT.run_lift] at hr
    obtain ⟨a, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact hs
  · rw [oracles4_inr] at hr
    exact LifetimeProof.lifetimeOracles_invariant K circuits settings attempts _ _ D keys _ h q st hs r hr

end Walk

section SetupQuiet

open LifetimePrfTransportProof LifetimeIdealBad

variable {C : Committee} {E : Type}

theorem atRound_quietP {ι γ : Type} {spec : OracleSpec ι} {P : ι → Prop} (p : Pause C E)
    {other : OracleComp spec γ} {f : Sent C E → (Option (Sent C E) → Program C E) → OracleComp spec γ}
    (ho : IsQueryBoundP other P 0) (hf : ∀ sent k, IsQueryBoundP (f sent k) P 0) :
    IsQueryBoundP (p.atRound other f) P 0 := by
  rcases p with f | ⟨q, k⟩
  · exact ho
  · cases q <;> first | exact ho | exact hf _ _

theorem atStart_quietP {ι γ : Type} {spec : OracleSpec ι} {P : ι → Prop} (p : Pause C E)
    {other : OracleComp spec γ}
    {f : ThresholdLeanXmss.Tree → (Option (Sent C E) → Program C E) → OracleComp spec γ}
    (ho : IsQueryBoundP other P 0) (hf : ∀ tree k, IsQueryBoundP (f tree k) P 0) :
    IsQueryBoundP (p.atStart other f) P 0 := by
  rcases p with f | ⟨q, k⟩
  · exact ho
  · cases q <;> first | exact ho | exact hf _ _

/-- A PRG call of run `n`. -/
def TargetPrg : (Spec4 C).Domain → Prop
  | .inr t => PrgCall t
  | _ => False

theorem targetPrg_baseFree : BaseFree (TargetPrg (C := C)) := fun _ => ⟨id, id⟩

theorem targetCopy4_prg {α : Type} (p : OracleComp (LocalSpec C) α) (hp : IsQueryBoundP p LocalStream 0) :
    IsQueryBoundP (targetCopy4 p) TargetPrg 0 :=
  qb0_simulateQ (p := LocalStream) (q := TargetPrg) _ (fun t ht => (isQueryBoundP_query_iff _ _ _).2
    fun h => absurd (show LocalStream t by
      rcases t with u | q | x <;> simp_all [TargetPrg, PrgCall, LocalStream]) ht) p hp

theorem runCount_start (D : C.Coalition) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (x : Option (ThresholdLeanXmss.Tree × ℕ × (C.Party → Step C E RealSpec TreeOutput))) :
    (({ LifetimeProof.increment st tree with running := x } : LifetimeState C E).settle D).runCount =
      st.runCount + 1 := by
  rw [LifetimeProof.settle_runCount]
  exact LifetimeProof.increment_runCount st tree

theorem runCount_round (D : C.Coalition) (st : LifetimeState C E)
    (x : Option (ThresholdLeanXmss.Tree × ℕ × (C.Party → Step C E RealSpec TreeOutput))) :
    (({ st with running := x } : LifetimeState C E).settle D).runCount = st.runCount := by
  rw [LifetimeProof.settle_runCount]
  rfl

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ)

/-- After the start of run `n`, the oracles make no PRG call of run `n` on a call other than a round. -/
theorem later_step_quiet (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E) (hs : n + 1 ≤ st.runCount)
    (ht : ∀ q, t = .inr q → ¬ RoundStop st q) :
    IsQueryBoundP ((oracles4 K circuits settings attempts D n keys h t).run st) TargetPrg 0 ∧
      ∀ r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run st), n + 1 ≤ r.2.runCount := by
  refine ⟨oracles4_quietP K circuits settings attempts D n targetPrg_baseFree keys h t st
    (fun _ _ _ => roles4_later_quiet targetPrg_baseFree (by omega))
    (fun sent he _ => absurd trivial (ht _ he)), fun r hr => ?_⟩
  rcases oracles4_runCount K circuits settings attempts D n keys h t st r hr with he | ⟨_, _, _, he⟩ <;> omega

set_option maxRecDepth 200000 in
theorem reveal_quiet (keys : C.Party → Keys C) (h : C.Party)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (prog : Program C E)
    (st : LifetimeState C E) (hs : n + 1 ≤ st.runCount) :
    IsQueryBoundP (revealSegment K circuits settings attempts D n keys h k active parts committed prog st)
      TargetPrg 0 := by
  have hw := runTo_quietP (P := TargetPrg) (oracles4 K circuits settings attempts D n keys h) RoundStop
    (fun s => n + 1 ≤ s.runCount)
    (fun t s hs ht => later_step_quiet K circuits settings attempts D n keys h t s hs ht) prog st hs
  refine zero_bind _ hw.1 fun r _ => atRound_quietP _ (isQueryBoundP_pure _ _ _) fun sent k' => ?_
  generalize r.2.running = o
  cases o with
  | none => exact isQueryBoundP_pure _ _ _
  | some x =>
    obtain ⟨tree, fuel, steps⟩ := x
    dsimp only
    split
    · exact zero_bind _ (targetCopy4_prg _ (qb0_prssRevealRows D _ _ _ _)) fun _ _ => isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _

set_option maxRecDepth 200000 in
theorem commit_quiet (keys : C.Party → Keys C) (h : C.Party)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (data : C.Party → Parts C × List HashOutput) (prog : Program C E) (st : LifetimeState C E)
    (hs : n + 1 ≤ st.runCount) :
    IsQueryBoundP (commitSegment K circuits settings attempts D n keys h k data prog st) TargetPrg 0 := by
  have hw := runTo_quietP (P := TargetPrg) (oracles4 K circuits settings attempts D n keys h) RoundStop
    (fun s => n + 1 ≤ s.runCount)
    (fun t s hs ht => later_step_quiet K circuits settings attempts D n keys h t s hs ht) prog st hs
  refine zero_bind _ hw.1 fun r hr => atRound_quietP _ (isQueryBoundP_pure _ _ _) fun sent k' => ?_
  have hc := (hw.2 r hr).1
  generalize r.2.running = o
  cases o with
  | none => exact isQueryBoundP_pure _ _ _
  | some x =>
    obtain ⟨tree, fuel, steps⟩ := x
    dsimp only
    split
    · exact reveal_quiet K circuits settings attempts D n keys h k _ _ _ _ _ (by rw [runCount_round]; exact hc)
    · exact isQueryBoundP_pure _ _ _

/-- Before the start of run `n`, every step keeps the run invariant and the counter at most `n`, and
makes no PRG call of run `n`. -/
theorem early_step (keys : C.Party → Keys C) (h : C.Party) (t : (LocalSpec C + LifetimeSpec C E).Domain)
    (s : LifetimeState C E) (hs : LifetimeProof.RunInvariant attempts s ∧ s.runCount ≤ n)
    (ht : ∀ q, t = .inr q → ¬ StartStop attempts D n s q) :
    IsQueryBoundP ((oracles4 K circuits settings attempts D n keys h t).run s) TargetPrg 0 ∧
      ∀ r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run s),
        LifetimeProof.RunInvariant attempts r.2 ∧ r.2.runCount ≤ n := by
  have hne : ∀ tree, t = .inr (.start tree) → LifetimeProof.canStart attempts D s tree →
      s.runCount < n := fun tree he hc => by
    have h' := ht _ he
    simp only [StartStop, CountIs, not_and] at h'
    have := h' hc
    omega
  refine ⟨oracles4_quietP K circuits settings attempts D n targetPrg_baseFree keys h t s
    (fun tree he hc => roles4_earlier_quiet targetPrg_baseFree (fun _ => id) (hne tree he hc))
    (fun sent _ hr => roles4_earlier_quiet targetPrg_baseFree (fun _ => id)
      (by have := hs.1.2.2 hr; omega)), fun r hr => ⟨?_, ?_⟩⟩
  · exact oracles4_invariant K circuits settings attempts D n keys h t s hs.1 r hr
  · rcases oracles4_runCount K circuits settings attempts D n keys h t s r hr with he | ⟨tree, he, hc, hr'⟩
    · omega
    · have := hne tree he hc
      omega

set_option maxRecDepth 200000 in
theorem start_quiet (keys : C.Party → Keys C) (h : C.Party) (prog : Program C E) (st : LifetimeState C E)
    (hs : LifetimeProof.RunInvariant attempts st ∧ st.runCount ≤ n) :
    IsQueryBoundP (startSegment K circuits settings attempts D n keys h prog st) TargetPrg 0 := by
  have hw := runTo_quietP (P := TargetPrg) (oracles4 K circuits settings attempts D n keys h)
    (StartStop attempts D n) (fun s => LifetimeProof.RunInvariant attempts s ∧ s.runCount ≤ n)
    (early_step K circuits settings attempts D n keys h) prog st hs
  refine zero_bind _ hw.1 fun r hr => atStart_quietP _ (isQueryBoundP_pure _ _ _) fun tree k' => ?_
  split
  · rename_i hg
    have hc : r.2.runCount = n := hg.2
    refine zero_bind _ (targetCopy4_prg _ (qb0_prssInitialData D)) fun data _ => ?_
    exact commit_quiet K circuits settings attempts D n keys h _ _ _ _ (by rw [runCount_start, hc])
  · exact isQueryBoundP_pure _ _ _

theorem qb0_bind_left {ι α β : Type} {spec : OracleSpec ι} {P : ι → Prop} {oa : OracleComp spec α}
    {f : α → OracleComp spec β} (h : IsQueryBoundP (oa >>= f) P 0) : IsQueryBoundP oa P 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    rw [isQueryBoundP_query_bind_iff]
    have ht : ¬ P t := h.1.resolve_right (by omega)
    exact ⟨Or.inl ht, fun u => by simpa [ht] using ih u (by simpa [ht] using h.2 u)⟩

theorem qb0_or {ι α : Type} {spec : OracleSpec ι} {P Q : ι → Prop} {oa : OracleComp spec α}
    (hp : IsQueryBoundP oa P 0) (hq : IsQueryBoundP oa Q 0) :
    IsQueryBoundP oa (fun t => P t ∨ Q t) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp hq ⊢
    have h1 : ¬ P t := hp.1.resolve_right (by omega)
    have h2 : ¬ Q t := hq.1.resolve_right (by omega)
    refine ⟨Or.inl (by tauto), fun u => ?_⟩
    simpa [h1, h2] using ih u (by simpa [h1] using hp.2 u) (by simpa [h2] using hq.2 u)

variable (A : LifetimeAdversary C E)

/-- `program4` up to the reveal of run `n` makes no free PRG call of the keygen, the signing or
run `n`. -/
theorem setup4_quiet : IsQueryBoundP (setup4 K circuits settings attempts D n A) Prefix4 0 := by
  have h3 : IsQueryBoundP (setup4 K circuits settings attempts D n A) FreePrgCall 0 := by
    have h := program4_quiet K circuits settings attempts n D A
    rw [program4_split] at h
    exact qb0_bind_left h
  have h4 : IsQueryBoundP (setup4 K circuits settings attempts D n A) TargetPrg 0 := by
    unfold setup4
    refine zero_bind _ (advCopy4_quietP _ fun t => (targetPrg_baseFree t).1) fun state _ => ?_
    refine zero_bind _ (executePhase_quietP (base4_quiet targetPrg_baseFree) D _ _ _ _) fun r _ => ?_
    rcases r with ⟨state', outputs⟩
    dsimp only
    split
    · split
      · exact isQueryBoundP_pure _ _ _
      · exact zero_bind _ (start_quiet K circuits settings attempts D n _ _ _ _
          ⟨LifetimeProof.initial_invariant attempts D, by simp [LifetimeProof.initial, LifetimeState.runCount]⟩)
          fun _ _ => isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
  refine IsQueryBoundP.of_imp (fun t ht => ?_) (qb0_or h3 h4)
  rcases t with ((t | t) | t) | t
  · exact ht.elim
  · exact ht.elim
  · exact Or.inl ht
  · exact Or.inr ht

end SetupQuiet

section TailRun

open LifetimePrfTransportProof LifetimeIdealBad LifetimeEmulatedBudget

variable {C : Committee} {E : Type}

/-- An emulated call of an earlier run, or a call of run `n` that the rows do not allow. -/
def TailRun (rows : RevealRows C) : (Spec4 C).Domain → Prop
  | .inl (.inl (.inr _)) => True
  | .inr t => ¬ Allowed rows t
  | _ => False

theorem tailRun_baseFree (rows : RevealRows C) : BaseFree (TailRun rows) := fun _ => ⟨id, id⟩

/-- A simulation keeps an invariant and avoids `P`, when each step does. -/
theorem simulate_quietP {ι ι' σ α : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {P : ι' → Prop}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (hstep : ∀ t s, Inv s → IsQueryBoundP ((impl t).run s) P 0 ∧ ∀ r ∈ support ((impl t).run s), Inv r.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) : IsQueryBoundP ((simulateQ impl oa).run s) P 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact zero_bind P (hstep t s hs).1 fun r hr => ih r.1 r.2 ((hstep t s hs).2 r hr)

theorem toRun4_quiet (rows : RevealRows C) {α : Type} (m : OracleComp (WorldSpec C) α)
    (hm : IsQueryBoundP m (Unallowed rows) 0) : IsQueryBoundP (toRun4 m) (TailRun rows) 0 := by
  change IsQueryBoundP (simulateQ worldTo4 m) (TailRun rows) 0
  refine qb0_simulateQ _ (fun t ht => ?_) m hm
  rcases t with (t | x) | t
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
  · exact isQueryBoundP_pure _ _ _
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h ht

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (D : C.Coalition) (n : ℕ)

/-- A round of run `n` on steps that the rows allow makes no call that the rows do not allow, and its
next steps are allowed again. -/
theorem stepRound_run4_ok (rows : RevealRows C) (sent : Sent C E)
    (steps : C.Party → Step C E RealSpec TreeOutput) (hs : ∀ j, StepOk rows (steps j)) :
    IsQueryBoundP (stepRound (roles4 n n) D (roundAdversary (I := PEmpty) sent) noFunctionality () steps)
      (TailRun rows) 0 ∧
    ∀ r ∈ support (stepRound (roles4 n n) D (roundAdversary (I := PEmpty) sent) noFunctionality () steps),
      ∀ j, StepOk rows (r.2.1 j) := by
  rw [stepRound_roundAdversary, ← hom_stepRound toRun4 worldRoles _ (rolesHom_run4 n)]
  have h := stepRound_ok rows D (roundAdversary (I := Keys C) sent) () steps hs
  exact ⟨toRun4_quiet rows _ h.1, fun r hr => h.2 r (support_simulateQ_subset _ _ hr)⟩

/-- After the reveal of run `n`, every later start counts past run `n`, and the steps of run `n`,
while it runs, make only calls that the rows allow. -/
def TailInv (rows : RevealRows C) (st : LifetimeState C E) : Prop :=
  n + 1 ≤ st.runCount ∧ ∀ tree fuel steps, st.running = some (tree, fuel, steps) →
    CountIs (n + 1) st → ∀ j, StepOk rows (steps j)

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)

/-- A signing request and the public key query keep the running ceremony. -/
theorem lifetime_running_eq (keys : C.Party → Keys C) (h : C.Party) (q : LifetimeQuery C E)
    (hq : ∀ tree, q ≠ .start tree) (hr : ∀ sent, q ≠ .round sent) (st : LifetimeState C E)
    (r : _ × LifetimeState C E)
    (hmem : r ∈ support ((lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys
      (value4 D keys) h q).run st)) : r.2.running = st.running := by
  cases q with
  | sign q =>
    cases q with
    | corrupt i =>
      have heq : r = (none, st) := hmem
      rw [heq]
    | tree b =>
      rw [LifetimeProof.run_sign_tree] at hmem
      exact (LifetimeProof.signAs_frame base4 keys (value4 D keys) h (.tree b) st r hmem).2
    | round1 i J e message =>
      rw [LifetimeProof.run_round1] at hmem
      split at hmem
      · have heq : r = (none, st) := hmem
        rw [heq]
      · exact (LifetimeProof.signAs_frame base4 keys (value4 D keys) i (.round1 i J e message) _ r hmem).2
    | round2 i J e message parts =>
      rw [LifetimeProof.run_round2] at hmem
      split at hmem
      · have heq : r = (none, st) := hmem
        rw [heq]
      · exact (LifetimeProof.signAs_frame base4 keys (value4 D keys) i (.round2 i J e message parts) _ r
          hmem).2
  | publicKey =>
    have heq : r = (st.publicKey (keys h).parameter h, st) := hmem
    rw [heq]
  | start tree => exact absurd rfl (hq tree)
  | round sent => exact absurd rfl (hr sent)

set_option maxRecDepth 200000 in
/-- One step of the oracles after the reveal of run `n` keeps `TailInv` and makes no call in
`TailRun`. -/
theorem oracles4_tail_step (rows : RevealRows C) (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E) (hs : TailInv n rows st) :
    IsQueryBoundP ((oracles4 K circuits settings attempts D n keys h t).run st) (TailRun rows) 0 ∧
      ∀ r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run st), TailInv n rows r.2 := by
  have hP := tailRun_baseFree (C := C) rows
  have hlater : ∀ r, n < r → RolesQuiet (TailRun rows) (roles4 (C := C) n r) :=
    fun r hr => roles4_later_quiet hP hr
  have other : ∀ q : LifetimeQuery C E, (∀ tree, q ≠ .start tree) → (∀ sent, q ≠ .round sent) →
      IsQueryBoundP ((oracles4 K circuits settings attempts D n keys h (.inr q)).run st) (TailRun rows) 0 ∧
        ∀ r ∈ support ((oracles4 K circuits settings attempts D n keys h (.inr q)).run st),
          TailInv n rows r.2 := by
    intro q hq hq'
    refine ⟨oracles4_quietP K circuits settings attempts D n hP keys h _ st
      (fun tree he => absurd (Sum.inr.inj he) (hq tree))
      (fun sent he => absurd (Sum.inr.inj he) (hq' sent)), fun r hr => ?_⟩
    have hc := oracles4_runCount K circuits settings attempts D n keys h _ st r hr
    have hrun := lifetime_running_eq D n K circuits settings attempts keys h q hq hq' st r hr
    rcases hc with hc | ⟨tree, he, _, _⟩
    · refine ⟨by rw [hc]; exact hs.1, fun tree fuel steps hr' hcount => ?_⟩
      rw [hrun] at hr'
      exact hs.2 tree fuel steps hr' (by unfold CountIs at hcount ⊢; omega)
    · exact absurd (Sum.inr.inj he) (hq tree)
  rcases t with t | q
  · refine ⟨oracles4_quietP K circuits settings attempts D n hP keys h _ st
      (fun _ he => by cases he) (fun _ he => by cases he), fun r hr => ?_⟩
    change r ∈ support ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) at hr
    rw [StateT.run_lift] at hr
    obtain ⟨a, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact hs
  · cases q with
    | start tree =>
      refine ⟨oracles4_quietP K circuits settings attempts D n hP keys h _ st
        (fun _ _ _ => hlater _ (by have := hs.1; omega)) (fun _ he => by cases he), fun r hr => ?_⟩
      have hc := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (roles4 n) base4 D keys
        (value4 D keys) h (.start tree) st r hr
      cases h1 : r.1 with
      | none =>
        rw [oracles4_inr, LifetimeProof.run_start] at hr
        split at hr
        · rw [support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact hs
        · obtain ⟨steps, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
          rw [support_pure, Set.mem_singleton_iff] at hr
          have h2 := congrArg Prod.fst hr
          rw [h1] at h2
          cases h2
      | some x =>
        have h2 : r.2.runCount = st.runCount + 1 := by
          simpa [LifetimeProof.newRun, h1] using hc
        have := hs.1
        refine ⟨by omega, fun _ _ _ _ hc' => ?_⟩
        have : r.2.runCount = n + 1 := hc'
        omega
    | round sent =>
      rw [oracles4_inr, LifetimeProof.run_round]
      cases hrun : st.running with
      | none =>
        refine ⟨isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
        rw [support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
        exact hs
      | some x =>
        obtain ⟨tree, fuel, steps⟩ := x
        dsimp only
        by_cases hc : CountIs (n + 1) st
        · have hc' : st.runCount - 1 = n := by
            have : st.runCount = n + 1 := hc
            omega
          rw [hc']
          have hok := stepRound_run4_ok D n rows sent steps (hs.2 tree fuel steps hrun hc)
          refine ⟨zero_bind _ hok.1 fun _ _ => isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
          obtain ⟨y, hy, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
          rw [support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          refine ⟨by rw [runCount_round]; exact hs.1, fun tree' fuel' steps' hrun' _ => ?_⟩
          have he := LifetimeProof.settle_running D _ (by rw [hrun']; simp)
          rw [hrun'] at he
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          rw [he.2.2]
          exact hok.2 y hy
        · have hlt : n < st.runCount - 1 := by
            have h1 := hs.1
            have h2 : st.runCount ≠ n + 1 := hc
            omega
          refine ⟨zero_bind _ (stepRound_quietP (hlater _ hlt) D _ _ _) fun _ _ => isQueryBoundP_pure _ _ _,
            fun r hr => ?_⟩
          obtain ⟨y, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
          rw [support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          refine ⟨by rw [runCount_round]; exact hs.1, fun _ _ _ _ hc' => absurd ?_ hc⟩
          have : (({ st with running := some (tree, fuel - 1, y.2.1) } : LifetimeState C E).settle D).runCount
            = n + 1 := hc'
          rw [runCount_round] at this
          exact this
    | sign q => exact other (.sign q) (fun _ => by simp) (fun _ => by simp)
    | publicKey => exact other .publicKey (fun _ => by simp) (fun _ => by simp)

theorem finish4_quietP {P : (Spec4 C).Domain → Prop} (hP : BaseFree P) (keys : C.Party → Keys C)
    (h : C.Party) (r : Forgery × LifetimeState C E) : IsQueryBoundP (finish4 D keys h r) P 0 := by
  unfold finish4
  split
  · exact isQueryBoundP_pure _ _ _
  · split
    · exact forgeryWins_quiet P roFree (fun p _ => roFree_quietP hP p) _
        (dealtWith_quiet P roFree (fun p _ => roFree_quietP hP p) _ _ _ _
          (fun x => value4_quietP D hP keys x)) _ _
    · exact isQueryBoundP_pure _ _ _

variable (A : LifetimeAdversary C E)

/-- The tail from a boundary makes no call in `TailRun`, when the adversary is done or `TailInv`
holds at the boundary. -/
theorem tail4_run_quiet (b : Boundary C E)
    (hb : (∃ f : Forgery, b.rest = (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery)) ∨
      TailInv n (rowsOf b.rows) b.state) :
    IsQueryBoundP (tail4 K circuits settings attempts D n (some b)) (TailRun (rowsOf b.rows)) 0 := by
  refine zero_bind _ ?_ fun r _ => finish4_quietP D (tailRun_baseFree _) b.keys b.h r
  rcases hb with ⟨f, hf⟩ | hb
  · rw [hf, simulateQ_pure]
    exact isQueryBoundP_pure _ _ _
  · exact simulate_quietP _ (TailInv n (rowsOf b.rows))
      (fun t s hs => oracles4_tail_step D n K circuits settings attempts _ b.keys b.h t s hs) _ _ hb

/-- A step other than a round keeps the run counter and the running ceremony, or it starts a run. -/
theorem oracles4_frame (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (ht : ∀ sent, t ≠ .inr (.round sent))
    (st : LifetimeState C E) (r : _ × LifetimeState C E)
    (hr : r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run st)) :
    (r.2.runCount = st.runCount ∧ r.2.running = st.running) ∨ r.2.runCount = st.runCount + 1 := by
  rcases t with t | q
  · left
    change r ∈ support ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) at hr
    rw [StateT.run_lift] at hr
    obtain ⟨a, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact ⟨rfl, rfl⟩
  · have hc := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (roles4 n) base4 D keys
      (value4 D keys) h q st r hr
    cases q with
    | start tree =>
      cases h1 : r.1 with
      | none =>
        left
        rw [oracles4_inr, LifetimeProof.run_start] at hr
        split at hr
        · rw [support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact ⟨rfl, rfl⟩
        · obtain ⟨steps, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
          rw [support_pure, Set.mem_singleton_iff] at hr
          have h2 := congrArg Prod.fst hr
          rw [h1] at h2
          cases h2
      | some x =>
        right
        simpa [LifetimeProof.newRun, h1] using hc
    | round sent => exact absurd rfl (ht sent)
    | sign q =>
      left
      refine ⟨by simpa [LifetimeProof.newRun] using hc, ?_⟩
      exact lifetime_running_eq D n K circuits settings attempts keys h (.sign q) (fun _ => by simp)
        (fun _ => by simp) st r hr
    | publicKey =>
      left
      refine ⟨by simpa [LifetimeProof.newRun] using hc, ?_⟩
      exact lifetime_running_eq D n K circuits settings attempts keys h .publicKey (fun _ => by simp)
        (fun _ => by simp) st r hr

/-- The steps of run `n` after its reveal round make only calls that the rows allow. -/
theorem finish_stepOk (rows : RevealRows C) (keys : C.Party → Keys C) (st : LifetimeState C E)
    (tree : ThresholdLeanXmss.Tree) (i : C.Party) :
    StepOk rows (suspendStep (cont K circuits settings keys st tree i) (prssFinishStep i (rows i))) := by
  rcases hrow : rows i with _ | ⟨out, shared⟩
  · exact trivial
  · intro inbox
    unfold exchangeResume
    dsimp only
    split_ifs
    · simp
    · have hp : POk (G := RealSpec) (⟨i, keys i, out⟩ : Context C)
          ((do require (∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0]); pure out) >>=
            fun prss => (cont K circuits settings keys st tree i prss : PartyM C E RealSpec TreeOutput)) := by
        rw [bind_assoc]
        refine POk.bind (POk.require _) fun _ => ?_
        rw [pure_bind]
        exact POk.ceremonyAfterSetup K circuits settings _ tree
      exact IsQueryBoundP.of_imp (partyUnallowed_of_bad rows (ctx := ⟨i, keys i, out⟩) hrow) hp

/-- No call. -/
def Never (_ : (Spec4 C).Domain) : Prop := False

theorem qb0_never {α : Type} (oa : OracleComp (Spec4 C) α) : IsQueryBoundP oa Never 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl id, fun u => by simpa [Never] using ih u⟩

/-- Between two rounds of run `n`, every later start counts past run `n`, and while run `n` runs it
holds the steps `expected`. -/
def SegInv (expected : C.Party → Step C E RealSpec TreeOutput) (st : LifetimeState C E) : Prop :=
  n + 1 ≤ st.runCount ∧ ∀ x, st.running = some x → CountIs (n + 1) st → x.2.2 = expected

theorem segInv_step (keys : C.Party → Keys C) (h : C.Party) (expected : C.Party → Step C E RealSpec TreeOutput)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (s : LifetimeState C E) (hs : SegInv n expected s)
    (ht : ∀ q, t = .inr q → ¬ RoundStop s q) :
    IsQueryBoundP ((oracles4 K circuits settings attempts D n keys h t).run s) Never 0 ∧
      ∀ r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run s), SegInv n expected r.2 := by
  refine ⟨qb0_never _, fun r hr => ?_⟩
  have ht' : ∀ sent, t ≠ .inr (.round sent) := fun sent he => ht _ he trivial
  rcases oracles4_frame D n K circuits settings attempts keys h t ht' s r hr with ⟨hc, hrun⟩ | hc
  · refine ⟨by rw [hc]; exact hs.1, fun x hx hcount => ?_⟩
    rw [hrun] at hx
    exact hs.2 x hx (by unfold CountIs at hcount ⊢; omega)
  · have := hs.1
    refine ⟨by omega, fun x _ hcount => ?_⟩
    have : r.2.runCount = n + 1 := hcount
    omega

set_option maxRecDepth 200000 in
/-- After the reveal segment, the adversary is done or `TailInv` holds for the rows that it
returns. -/
theorem reveal_tail (keys : C.Party → Keys C) (h : C.Party) (st₀ : LifetimeState C E)
    (tree₀ : ThresholdLeanXmss.Tree) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) (prog : Program C E) (st : LifetimeState C E)
    (hs : SegInv n (fun i => suspendStep (cont K circuits settings keys st₀ tree₀ i)
      (prssRevealStep D active parts committed i)) st) :
    ∀ r ∈ support (revealSegment K circuits settings attempts D n keys h
      (cont K circuits settings keys st₀ tree₀) active parts committed prog st),
      (∃ f : Forgery, r.1.2 = (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery)) ∨
        TailInv n (rowsOf r.1.1) r.2 := by
  intro r hr
  unfold revealSegment at hr
  obtain ⟨r₀, hr₀, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have hw := (runTo_quietP (P := Never) (oracles4 K circuits settings attempts D n keys h)
    RoundStop (SegInv n _) (fun t s hs ht => segInv_step D n K circuits settings attempts keys h _ t s hs ht)
    prog st hs).2 r₀ hr₀
  rcases r₀ with ⟨p, st'⟩
  rcases p with f | ⟨q, k'⟩
  · simp only [Pause.atRound, support_pure, Set.mem_singleton_iff] at hr
    exact Or.inl ⟨f, by rw [hr]; rfl⟩
  · cases q with
    | round sent =>
      simp only [Pause.atRound] at hr
      right
      rcases hrun : st'.running with _ | ⟨tree, fuel, steps⟩
      · rw [hrun] at hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
        exact ⟨hw.1.1, fun tree fuel steps h' => by rw [hrun] at h'; cases h'⟩
      · rw [hrun] at hr
        dsimp only at hr
        split at hr
        · obtain ⟨rows, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
          rw [support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          refine ⟨by rw [runCount_round]; exact hw.1.1, fun tree' fuel' steps' h' _ => ?_⟩
          have he := LifetimeProof.settle_running D _ (by rw [h']; simp)
          rw [h'] at he
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          rw [he.2.2]
          exact fun j => finish_stepOk K circuits settings rows keys st₀ tree₀ j
        · rename_i hg
          rw [support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          refine ⟨hw.1.1, fun tree' fuel' steps' h' hc => ?_⟩
          rw [hrun] at h'
          simp only [Option.some.injEq] at h'
          exact absurd ⟨hc, hw.1.2 _ hrun hc⟩ hg
    | _ => exact absurd (hw.2 _ _ rfl) (by simp [RoundStop])

set_option maxRecDepth 200000 in
/-- After the commit segment, the adversary is done or `TailInv` holds for the rows that it
returns. -/
theorem commit_tail (keys : C.Party → Keys C) (h : C.Party) (st₀ : LifetimeState C E)
    (tree₀ : ThresholdLeanXmss.Tree) (data : C.Party → Parts C × List HashOutput) (prog : Program C E)
    (st : LifetimeState C E)
    (hs : SegInv n (fun i => suspendStep (cont K circuits settings keys st₀ tree₀ i)
      (prssInitialSteps D data i)) st) :
    ∀ r ∈ support (commitSegment K circuits settings attempts D n keys h
      (cont K circuits settings keys st₀ tree₀) data prog st),
      (∃ f : Forgery, r.1.2 = (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery)) ∨
        TailInv n (rowsOf r.1.1) r.2 := by
  intro r hr
  unfold commitSegment at hr
  obtain ⟨r₀, hr₀, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have hw := (runTo_quietP (P := Never) (oracles4 K circuits settings attempts D n keys h)
    RoundStop (SegInv n _) (fun t s hs ht => segInv_step D n K circuits settings attempts keys h _ t s hs ht)
    prog st hs).2 r₀ hr₀
  rcases r₀ with ⟨p, st'⟩
  rcases p with f | ⟨q, k'⟩
  · simp only [Pause.atRound, support_pure, Set.mem_singleton_iff] at hr
    exact Or.inl ⟨f, by rw [hr]; rfl⟩
  · cases q with
    | round sent =>
      simp only [Pause.atRound] at hr
      rcases hrun : st'.running with _ | ⟨tree, fuel, steps⟩
      · rw [hrun] at hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
        exact Or.inr ⟨hw.1.1, fun tree fuel steps h' => by rw [hrun] at h'; cases h'⟩
      · rw [hrun] at hr
        dsimp only at hr
        split at hr
        · refine reveal_tail D n K circuits settings attempts keys h st₀ tree₀ _ _ _ _ _ ⟨?_, ?_⟩ r hr
          · rw [runCount_round]
            exact hw.1.1
          · intro x hx _
            have he := LifetimeProof.settle_running D _ (by rw [hx]; simp)
            rw [hx] at he
            simp only [Option.some.injEq] at he
            rw [he]
        · rename_i hg
          rw [support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          refine Or.inr ⟨hw.1.1, fun tree' fuel' steps' h' hc => ?_⟩
          exact absurd ⟨hc, hw.1.2 _ hrun hc⟩ hg
    | _ => exact absurd (hw.2 _ _ rfl) (by simp [RoundStop])

set_option maxRecDepth 200000 in
/-- After the start segment, the adversary is done or `TailInv` holds for the rows that it
returns. -/
theorem start_tail (keys : C.Party → Keys C) (h : C.Party) (prog : Program C E) (st : LifetimeState C E)
    (hs : LifetimeProof.RunInvariant attempts st ∧ st.runCount ≤ n) :
    ∀ r ∈ support (startSegment K circuits settings attempts D n keys h prog st),
      (∃ f : Forgery, r.1.2 = (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery)) ∨
        TailInv n (rowsOf r.1.1) r.2 := by
  intro r hr
  unfold startSegment at hr
  obtain ⟨r₀, hr₀, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have hw := (runTo_quietP (P := TargetPrg) (oracles4 K circuits settings attempts D n keys h)
    (StartStop attempts D n) (fun s => LifetimeProof.RunInvariant attempts s ∧ s.runCount ≤ n)
    (early_step K circuits settings attempts D n keys h) prog st hs).2 r₀ hr₀
  rcases r₀ with ⟨p, st'⟩
  rcases p with f | ⟨q, k'⟩
  · simp only [Pause.atStart, support_pure, Set.mem_singleton_iff] at hr
    exact Or.inl ⟨f, by rw [hr]; rfl⟩
  · cases q with
    | start tree =>
      have hstop : LifetimeProof.canStart attempts D st' tree ∧ CountIs n st' := hw.2 _ _ rfl
      simp only [Pause.atStart, if_pos hstop] at hr
      obtain ⟨data, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      refine commit_tail D n K circuits settings attempts keys h st' tree data _ _ ⟨?_, ?_⟩ r hr
      · rw [runCount_start]
        have : st'.runCount = n := hstop.2
        omega
      · intro x hx _
        have he := LifetimeProof.settle_running D _ (by rw [hx]; simp)
        rw [hx] at he
        simp only [Option.some.injEq] at he
        rw [he]
    | _ => exact absurd (hw.2 _ _ rfl) (by simp [StartStop])

/-- At every boundary that `setup4` reaches, the adversary is done or `TailInv` holds. -/
theorem setup4_tail :
    ∀ b' ∈ support (setup4 K circuits settings attempts D n A), ∀ b, b' = some b →
      (∃ f : Forgery, b.rest = (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery)) ∨
        TailInv n (rowsOf b.rows) b.state := by
  intro b' hb' b hb
  unfold setup4 at hb'
  obtain ⟨state, -, hb'⟩ := (mem_support_bind_iff _ _ _).mp hb'
  obtain ⟨⟨state', outputs⟩, -, hb'⟩ := (mem_support_bind_iff _ _ _).mp hb'
  dsimp only at hb'
  split at hb'
  · split at hb'
    · rw [support_pure, Set.mem_singleton_iff] at hb'
      rw [hb'] at hb
      cases hb
    · obtain ⟨r, hr, hb'⟩ := (mem_support_bind_iff _ _ _).mp hb'
      rw [support_pure, Set.mem_singleton_iff] at hb'
      rw [hb'] at hb
      cases hb
      exact start_tail D n K circuits settings attempts _ _ _ _
        ⟨LifetimeProof.initial_invariant attempts D, by simp [LifetimeProof.initial, LifetimeState.runCount]⟩ r hr
  · rw [support_pure, Set.mem_singleton_iff] at hb'
    rw [hb'] at hb
    cases hb

end TailRun

section TailAllowed

open LifetimePrfTransportProof LifetimeIdealBad

variable {C : Committee} {E : Type}

/-- A free hash of a stream key by the keygen or the signing. -/
def FreeStreamKey : (Spec4 C).Domain → Prop
  | .inl (.inr (.inr (.inl (.streamKey _)))) => True
  | _ => False

theorem qb0_bind_right {ι α β : Type} {spec : OracleSpec ι} {P : ι → Prop} {oa : OracleComp spec α}
    {f : α → OracleComp spec β} (h : IsQueryBoundP (oa >>= f) P 0) :
    ∀ a ∈ support oa, IsQueryBoundP (f a) P 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro a' ha
    rw [support_pure, Set.mem_singleton_iff] at ha
    subst ha
    simpa using h
  | query_bind t k ih =>
    intro a ha
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    have ht : ¬ P t := h.1.resolve_right (by omega)
    obtain ⟨u, -, hu⟩ := (mem_support_bind_iff _ _ _).mp ha
    exact ih u (by simpa [ht] using h.2 u) a hu

theorem qb0_cover {ι α : Type} {spec : OracleSpec ι} {P Q R : ι → Prop} {iP : DecidablePred P}
    {iQ : DecidablePred Q} [DecidablePred R] {oa : OracleComp spec α}
    (hp : @IsQueryBoundP ι spec α oa P iP 0) (hq : @IsQueryBoundP ι spec α oa Q iQ 0)
    (hR : ∀ t, R t → P t ∨ Q t) : IsQueryBoundP oa R 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp hq ⊢
    have h1 : ¬ P t := hp.1.resolve_right (by omega)
    have h2 : ¬ Q t := hq.1.resolve_right (by omega)
    have h3 : ¬ R t := fun h => (hR t h).elim h1 h2
    refine ⟨Or.inl h3, fun u => ?_⟩
    simpa [h3] using ih u (by simpa [h1] using hp.2 u) (by simpa [h2] using hq.2 u)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E)

/-- The keygen and the signing of `program4` hash no stream key on the free copy. -/
def FreeStreamKeyQuiet : Prop :=
  IsQueryBoundP (program4 D K circuits settings attempts A n) FreeStreamKey 0

/-- After the reveal of run `n`, `program4` makes no emulated call and no free call that the rows of
run `n` do not allow. -/
def TailAllowed : Prop :=
  ∀ b ∈ support (setup4 K circuits settings attempts D n A),
    IsQueryBoundP (tail4 K circuits settings attempts D n b) (Tail4 (rowsOf (b.bind Boundary.rows))) 0

theorem tailAllowed (hkey : FreeStreamKeyQuiet K circuits settings attempts D n A) :
    TailAllowed K circuits settings attempts D n A := by
  intro b hb
  have hprg := qb0_bind_right (by
    have h := program4_quiet K circuits settings attempts n D A
    rwa [program4_split] at h) b hb
  have hkey' := qb0_bind_right (by
    have h := hkey
    unfold FreeStreamKeyQuiet at h
    rwa [program4_split] at h) b hb
  cases b with
  | none => exact isQueryBoundP_pure _ _ _
  | some b =>
    have hrun := tail4_run_quiet D n K circuits settings attempts b
      (setup4_tail D n K circuits settings attempts A _ hb b rfl)
    refine qb0_cover hrun (qb0_cover (R := fun t => FreePrgCall t ∨ FreeStreamKey t) hprg hkey'
      (fun _ h => h)) fun t ht => ?_
    rcases t with ((t | t) | t) | t
    · exact ht.elim
    · exact Or.inl trivial
    · right
      rcases t with u | q | x
      · exact absurd trivial ht
      · right
        cases q with
        | streamKey k => trivial
        | _ => exact ht fun k hk => by cases hk
      · left
        trivial
    · exact Or.inl ht

end TailAllowed

section Boundary

open LifetimePrfTransportProof LifetimeHybridOrder

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E) (prims : Primitives)

/-- The reveal rows of run `n` at the boundary, with no row when run `n` does not reach its reveal
step. -/
def rowsAt (r : (Option (Boundary C E) × StreamCache C) × CallLog C) : RevealRows C :=
  rowsOf (r.1.1.bind Boundary.rows)

theorem worldSetup_quiet :
    IsQueryBoundP (worldSetup K circuits settings attempts D n A) (FreeHidden D) 0 :=
  quietP_simulate (hybridImpl D) (impl4_quiet_hidden D) _
    (setup4_quiet K circuits settings attempts D n A) ∅

theorem worldTail_allowed (h : TailAllowed K circuits settings attempts D n A) :
    ∀ r ∈ support (worldSetup K circuits settings attempts D n A),
      IsQueryBoundP (worldTail K circuits settings attempts D n r) (Unallowed (rowsAt r)) 0 := by
  intro r hr
  have hb := support_emulation (hybridImpl D) _ ∅ r hr
  exact (isQueryBoundP_map_iff _ _ _).2
    (quietP_simulate (hybridImpl D) (impl4_quiet_tail D _) _ (h _ hb) r.1.2)

/-- Hybrid `n` in the ideal joint world. The world runs up to the reveal of run `n`, and then the
ideal joint world runs from the boundary state on the cache of the world. -/
def runBoundary :=
  boundaryOf prims D (worldSetup K circuits settings attempts D n A)
    (worldTail K circuits settings attempts D n)

/-- The stream-key bad event of hybrid `n` is the bad event after the reveal of run `n`. -/
theorem probBad_hybrid_eq :
    probBad_streamKey prims D (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) =
      (Pr[fun y => y.2.2.bad = true | runBoundary K circuits settings attempts D n A prims]).toReal :=
  probBad_eq_boundaryOf prims D _ _ _ (hybrid_split K circuits settings attempts D n A)
    (worldSetup_quiet K circuits settings attempts D n A)

/-- After the reveal of run `n`, a raised flag comes with keys of the rows of run `n` that are not
apart, or with apart keys and a hit in the final cache. -/
theorem runBoundary_bad (hkey : FreeStreamKeyQuiet K circuits settings attempts D n A) :
    ∀ y ∈ support (runBoundary K circuits settings attempts D n A prims), y.2.2.bad = true →
      ¬ KeysApart D (rowsAt y.1.1) ∨
        (KeysApart D (rowsAt y.1.1) ∧ KeyHit D (rowsAt y.1.1) y.2.2.hash) :=
  boundaryOf_bad prims D _ _ rowsAt (worldTail_allowed K circuits settings attempts D n A
    (tailAllowed K circuits settings attempts D n A hkey))

end Boundary

section Reduction

open LifetimePrfTransportProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ) (aes : Aes)
variable (circuitsOf : (HashInput → HashOutput) → Circuits) (D : C.Coalition) (A : LifetimeAdversary C E)
variable (values : MpcDomain → HashOutput) (n : ℕ)

/-- The world game of hybrid `n` for one `Th` is its run up to the reveal of run `n`, then the rest. -/
theorem reductionGame_split :
    reductionGame K settings attempts circuitsOf D A values n =
      worldSetup K (circuitsOf (thOf values)) settings attempts D n A >>=
        worldTail K (circuitsOf (thOf values)) settings attempts D n :=
  hybrid_split K _ settings attempts D n A

/-- The stream-key bad event of hybrid `n` for one `Th` is the bad event after the reveal of
run `n`. -/
theorem probBad_reductionGame_eq :
    probBad_streamKey ⟨thOf values, aes⟩ D (reductionGame K settings attempts circuitsOf D A values n) =
      (Pr[fun y => y.2.2.bad = true |
        runBoundary K (circuitsOf (thOf values)) settings attempts D n A ⟨thOf values, aes⟩]).toReal :=
  probBad_hybrid_eq K _ settings attempts D n A _

/-- The cover of the stream-key bad event of hybrid `n` for one `Th`. -/
theorem reductionGame_bad
    (hkey : FreeStreamKeyQuiet K (circuitsOf (thOf values)) settings attempts D n A) :
    ∀ y ∈ support (runBoundary K (circuitsOf (thOf values)) settings attempts D n A ⟨thOf values, aes⟩),
      y.2.2.bad = true →
        ¬ KeysApart D (rowsAt y.1.1) ∨
          (KeysApart D (rowsAt y.1.1) ∧ KeyHit D (rowsAt y.1.1) y.2.2.hash) :=
  runBoundary_bad K _ settings attempts D n A _ hkey

end Reduction

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunBoundary.program4_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program4_split

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunBoundary.reductionGame_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reductionGame_split

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunBoundary.setup4_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setup4_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunBoundary.probBad_reductionGame_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probBad_reductionGame_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunBoundary.tailAllowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tailAllowed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRunBoundary.reductionGame_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reductionGame_bad

end ThresholdLeanXmssSecurity.LifetimeRunBoundary
