import ThresholdLeanXmssSecurity.Proof.PhaseSplit
import ThresholdLeanXmssSecurity.Proof.Pilot.Pilot
import ThresholdLeanXmssSecurity.Proof.PrssRealRand
import ThresholdLeanXmssSecurity.Proof.SigningSelection

/-!
# The game after the PRF hop and the statements of its hops

`firstRun` runs `dkgTreeGame` in the state of `streamWorld`, where each stream under a hidden key is a
random function, and it records the first bad event. `RunReady` is the readiness of a state at the
start of a run, and `HiddenKeyBound` bounds the keys of the hidden streams. `StreamHop`, `FlagFirstHop`,
`SeedsHop`, `EchoHop`, `ReuseHop`, `CopyHop`, `SplitHop` and `UsedHitHop` state the hops of the game
with their error terms, and `streamHop` proves `StreamHop`. The last part counts the calls of the game
by class.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## The work of one operator in the signing game -/

section Operator

variable {C : Committee} {m : Type → Type} [Monad m]

/-- `ownAnswer` is `tsigOracles` on the state with the bottom trees of the operator. -/
theorem ownAnswer_run [LawfulMonad m] (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (dealt : Dealt C m) (bottoms : Fin (2 ^ layerHeight) → Option BottomTree) (q : TsigQuery C)
    (st : TsigState C) :
    (ownAnswer lift dealt bottoms q).run st =
      (tsigOracles lift dealt q).run { st with trees := fun b => some (bottoms b) } := by
  simp [ownAnswer]

end Operator

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The adversary -/

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The game after the PRF hop -/

/-- The stage of the first bad event. The seeds differ after the seed generation, a run starts from
a state that is not ready, or run `index` of `tree` sets the flag. -/
inductive Stage
  | seeds
  | unready (tree : Tree) (index : ℕ)
  | run (tree : Tree) (index : ℕ)

/-- The state of the game after the PRF hop. It is the state of the real game and the stage of the
first bad event with the state of the world at that time. -/
structure FirstState (C : Committee) (σ : Type) where
  real : RealState C σ
  first : Option (Stage × StreamState C)

/-- The monad of the game after the PRF hop. -/
abbrev FirstM (C : Committee) (σ : Type) := StateT (FirstState C σ) (StateT (StreamState C) ProbComp)

/-- The bounds of the hash cache and of the cache of the hidden streams at the start of a run. -/
structure StartBudget where
  split : ℕ
  coins : ℕ
  keys : ℕ
  salts : ℕ
  hiddenKeys : ℕ

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget)

/-- A computation of the world, answered by `streamWorld`. -/
def inStream (D : C.Coalition) {σ β : Type} (oa : OracleComp (WorldSpec C) β) : FirstM C σ β :=
  StateT.lift (simulateQ (streamWorld prims D) oa)

/-- The local oracles of the honest operators on the free copy, answered by `streamWorld`. -/
def firstLift (D : C.Coalition) {σ β : Type} (oa : OracleComp (RoSpec C) β) : FirstM C σ β :=
  inStream prims D (free (liftComp oa _))

/-- `F` on the seeds of the game, answered by `streamWorld`. -/
def firstValue (D : C.Coalition) {σ : Type} (operators : C.Party → OperatorState C) (x : Point) :
    FirstM C σ Digest :=
  firstLift prims D (prfValue (gameSeeds D fun i => (operators i).keys) x)

/-- The hidden streams have at most `count` keys under each name. -/
def HiddenKeyBound (hidden : HiddenCache C) (count : ℕ) : Prop :=
  ∀ name, ∃ keys : Finset HashOutput, keys.card ≤ count ∧
    ∀ key ρ idx position, hidden ((name, key), ρ, idx, position) ≠ none → key ∈ keys

/-- The keys, the top trees and the caches are ready for a run. The honest operators with keys hold
the keys of one dealing, and each honest top tree is the reference top tree on the seeds and the
parameter of the game in the world `world`. The hash cache has at most `budget.split` history and
digest cells, its coin keys and expansions have the ledger `SoundCache` with at most `budget.coins`
charged inputs and `budget.keys` expansion keys, and its digests have at most `budget.salts` salts.
The hidden streams have at most `budget.hiddenKeys` keys under each name. -/
def RunReady (D : C.Coalition) {σ : Type} (s : RealState C σ) (world : StreamState C) : Prop :=
  seedsDiffer D (fun i => (s.operators i).keys) = false ∧
    (∀ i, i ∉ D.1 → ∀ top, (s.operators i).top = some top →
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp
          (referenceTree (fun oa => tweakable oa) (prfValue (gameSeeds D fun j => (s.operators j).keys))
            (gameParameter D fun j => (s.operators j).keys) emptyTop .top) _))).run world),
        z.1 = some (.top top)) ∧
    SplitCacheBound (splitRegionCache SplitHashDomain world.1) budget.split ∧
    (∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 world.1 seen keys ∧
      seen.card ≤ budget.coins ∧ keys.card ≤ budget.keys) ∧
    (∃ salts : Finset (List Bit), DigestSaltsCovered world.1 salts ∧ salts.card ≤ budget.salts) ∧
    HiddenKeyBound world.2 budget.hiddenKeys

/-- One run of `tree` from the state `s`, answered by `streamWorld`. It gives the outputs of the
honest operators and the result of `wrongOutput`. -/
def streamTreeRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) :
    StateT (StreamState C) ProbComp ((net.State × (C.Party → Option TreeOutput)) × Bool) :=
  simulateQ (streamWorld prims D) (do
    let r ← executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary fun i =>
      treeProgram K circuits settings i (s.operators i) tree
    let bad ← wrongOutput D (fun i => (s.operators i).keys) tree r.2
    pure (r, bad))

/-- One run of `tree`. It is `treeRun` with `wrongOutput`. The game first records a start that is not
`RunReady`, and then a run that sets the flag, each with the state of the world. -/
def firstTreeRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    FirstM C net.State Unit := do
  let s ← get
  let before ← StateT.lift get
  let first := s.first <|> if RunReady prims budget D s.real before then none
    else some (.unready tree (s.real.runs tree), before)
  let ((state, outputs), bad) ← StateT.lift (streamTreeRun prims K circuits settings D net tree s.real)
  let after ← StateT.lift get
  let operators := fun i => (s.real.operators i).keep (outputs i) tree
  let runs := Function.update s.real.runs tree (s.real.runs tree + 1)
  set (⟨⟨state, operators, runs, s.real.closed, s.real.flag || bad⟩,
    first <|> if bad then some (.run tree (s.real.runs tree), after) else none⟩ : FirstState C net.State)

/-- At most `count` runs of `tree`, each while a run is allowed. -/
def firstTreeRuns (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ℕ → FirstM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get).real tree then
      firstTreeRun prims K circuits settings budget D net tree
      firstTreeRuns D net tree count

/-- A request of bottom tree `b`, as `treeRequest`. -/
def firstTreeRequest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) :
    FirstM C net.State (Option (BottomTree × Digest)) := do
  firstTreeRuns prims K circuits settings runLimit budget D net (.bottom b) 1
  let s ← get
  match heldBottom D s.real.operators b with
  | some tree => pure (some (tree, ← firstValue prims D s.real.operators (.randomizer topLayer (topKey b))))
  | none => pure none

/-- A signing request to operator `i` at key `e`, as `signRequest`. -/
def firstSignRequest (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    StateT (TsigState C) (FirstM C σ) (TsigSpec C q) := do
  StateT.lift (modify fun s : FirstState C σ =>
    { s with real := { s.real with closed := Function.update s.real.closed (treeOf e) true } })
  let s ← StateT.lift get
  operatorAnswer (firstLift prims D) (firstValue prims D s.real.operators) (s.real.operators i) e q

/-- The signing oracles, as `realOracles`. -/
def firstOracles (D : C.Coalition) (A : DkgTsigAdversary C E) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (FirstM C A.net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => StateT.lift (firstTreeRequest prims K circuits settings runLimit budget D A.net b)
  | .round1 i J e message => firstSignRequest prims D i e (.round1 i J e message)
  | .round2 i J e message parts => firstSignRequest prims D i e (.round2 i J e message parts)

/-- The signing phase, as `dkgSigning` without the win test. The win test comes after the last run,
so it does not change the flag. -/
def firstSigning (D : C.Coalition) (A : DkgTsigAdversary C E) : FirstM C A.net.State Unit := do
  let s ← get
  let some (keys, top) := topHolder D s.real.operators | pure ()
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (FirstM C A.net.State)) :=
    fun t => StateT.lift (inStream prims D (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (FirstM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.real.adversary) <$> (get : FirstM C A.net.State _))
    | .write state => StateT.lift (modify fun s : FirstState C A.net.State =>
        { s with real := { s.real with adversary := state } })
  let _ ← (simulateQ (forger + (firstOracles prims K circuits settings runLimit budget D A + cell))
    (A.forge ⟨top.root, keys.parameter⟩ top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩

/-- The run of `dkgTreeGame` after the PRF hop, from the empty caches. It gives the final state of
the game and of the world. -/
def firstRun (D : C.Coalition) (A : DkgTsigAdversary C E) : ProbComp (FirstState C A.net.State × StreamState C) :=
  (do
    let (state, keys) ← simulateQ (streamWorld prims D) (realExecution D A.net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])
    let world ← get
    let start := startState D state keys
    let (_, s) ← (do
        firstTreeRuns prims K circuits settings runLimit budget D A.net .top runLimit
        firstSigning prims K circuits settings runLimit budget D A).run
      ⟨start, if start.flag then some (.seeds, world) else none⟩
    pure s).run (∅, ∅)

/-! ## The events -/

/-- Two cells of the domain `P` of the hash cache have one output. -/
def DomainCollision (P : Query C → Prop) (cache : HashCache C) : Prop :=
  CacheHasCollision (splitRegionCache P cache)

/-- The echo hashes of the PRSS setups. -/
def EchoDomain : Query C → Prop
  | .sharedKeys .prss _ => True
  | _ => False

/-- The derived keys of the PRSS setups. -/
def DeriveDomain : Query C → Prop
  | .derive .prss _ _ => True
  | _ => False

/-- The copy hashes of `OpenRep`. -/
def CopyDomain : Query C → Prop
  | .copy _ => True
  | _ => False

/-- The global events of the game. Two echo hashes, two derived keys, two copy hashes, or two
history and digest cells collide. -/
def GlobalEvent (world : StreamState C) : Prop :=
  DomainCollision EchoDomain world.1 ∨ DomainCollision DeriveDomain world.1 ∨
    DomainCollision CopyDomain world.1 ∨ DomainCollision SplitHashDomain world.1

/-- The probability of `event` on the final state of `firstRun`. -/
def firstProb (D : C.Coalition) (A : DkgTsigAdversary C E)
    (event : FirstState C A.net.State × StreamState C → Prop) : ℝ :=
  (Pr{let r ← firstRun prims K circuits settings runLimit budget D A}[event r]).toReal

/-- The probability that the first bad event has a world state with a collision in the domain `P`. -/
def firstCollision (D : C.Coalition) (A : DkgTsigAdversary C E) (P : Query C → Prop) : ℝ :=
  firstProb prims K circuits settings runLimit budget D A fun r =>
    ∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision P world.1

/-! ## The counts and the error terms -/

/-- The PRF hop for each game. The streams under the hidden keys become a random function, with
the stream-key event and the PRF advantage. The right side keeps the final state of `streamWorld`. -/
def StreamHop (D : C.Coalition) : Prop :=
  ∀ game : OracleComp (WorldSpec C) Bool,
    accepts prims game ≤
      (Pr{let r ← (simulateQ (streamWorld prims D) game).run (∅, ∅)}[r.1 = true]).toReal +
        probBad_streamKey prims D game + streamAdvantage prims D game

/-- The flag of `dkgTreeGame` in `streamWorld` comes with a first bad event of `firstRun`. -/
def FlagFirstHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    (Pr{let r ← (simulateQ (streamWorld prims D) (dkgTreeGame K circuits settings runLimit D A)).run (∅, ∅)}[
        r.1 = true]).toReal ≤
      firstProb prims K circuits settings runLimit budget D A fun r => r.1.first ≠ none

/-- The seeds differ after the seed generation with probability at most `seedGenHashError`. -/
def SeedsHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    firstProb prims K circuits settings runLimit budget D A (fun r => ∃ world, r.1.first = some (.seeds, world)) ≤
      seedGenHashError C q

/-- At the world of the first bad record, two echo hashes of the PRSS setups collide with probability at
most `echoError`. -/
def EchoHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    firstCollision prims K circuits settings runLimit budget D A EchoDomain ≤ echoError runLimit C q

/-- The probability of `UsedHit` at the end of `game` in the world with the joint keys and
independent AES keys. -/
def usedHitProb (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr{let r ← (simulateQ (jointKeyWorld prims D false) game).run keyJointInitial}[UsedHit D r.2]).toReal

/-- The stream-key event of the game. It lives in the world with the joint keys, before the
step to `streamWorld`. -/
def UsedHitHop (usedHit : ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    usedHitProb prims D (dkgTreeGame K circuits settings runLimit D A) ≤ usedHit q

/-- At the world of the first bad record, two PRSS setups derive one hidden key under one name with
probability at most `reuseError`. -/
def ReuseHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    firstCollision prims K circuits settings runLimit budget D A DeriveDomain ≤ reuseError runLimit C q

/-- At the world of the first bad record, two copy hashes collide with probability at most `copyError`.
-/
def CopyHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    firstCollision prims K circuits settings runLimit budget D A CopyDomain ≤ copyError settings runLimit C q

/-- At the world of the first bad record, two history or digest cells collide with probability at most
`splitError`, one time for the game. -/
def SplitHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    firstCollision prims K circuits settings runLimit budget D A SplitHashDomain ≤ splitError settings runLimit C q

/-- `StreamHop` holds for each game. It joins `keyWorld_coupling` with the two experiments of `prgReduction`. -/
theorem streamHop (D : C.Coalition) : StreamHop prims D := by
  intro game
  have coupling := keyWorld_coupling prims D game
  have real : reductionReal prims D game = (Pr{let z ← ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
      (simulateQ (keyWorld prims D keys) game).run' ∅}[z = true]).toReal := by
    unfold reductionReal
    rw [prfRealExp_prgReduction]
  have ideal : reductionIdeal prims D game =
      (Pr{let r ← (simulateQ (streamWorld prims D) game).run (∅, ∅)}[r.1 = true]).toReal := by
    unfold reductionIdeal
    rw [prfIdealExp_prgReduction, StateT.run'_eq, prEvent_map]
  have advantage : |reductionReal prims D game - reductionIdeal prims D game| = streamAdvantage prims D game := by
    unfold reductionReal reductionIdeal streamAdvantage PRFScheme.prfAdvantage
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
    exact (MeasureTheory.Measure.toReal_boolDist _ _).symm
  rw [← real] at coupling
  rw [← ideal]
  have h₁ := (abs_le.mp coupling).2
  have h₂ := (abs_le.mp advantage.le).2
  linarith

/-! ## The assembly -/

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_sequenceFin)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace GameCount

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The calls of the monitor -/

/-- A call of `H` on `.hash` or on `.prf`. -/
def SignCall : (RoSpec C).Domain → Prop
  | .inl (.hash _) => True
  | .inl (.prf ..) => True
  | _ => False

/-- Each call of `oa` is a call of `H` on `.hash` or on `.prf`. It is irreducible, so that
unification never unfolds a deep computation. -/
@[irreducible] def OnlySign {α : Type} (oa : OracleComp (RoSpec C) α) : Prop :=
  AllQueriesSatisfy oa SignCall

theorem onlySign_iff {α : Type} (oa : OracleComp (RoSpec C) α) :
    OnlySign oa ↔ AllQueriesSatisfy oa SignCall := by
  unfold OnlySign; rfl

theorem onlySign_pure {α : Type} (a : α) : OnlySign (pure a : OracleComp (RoSpec C) α) := by
  rw [onlySign_iff]; exact allQueriesSatisfy_pure _ _

theorem onlySign_bind {α β : Type} {oa : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β}
    (h : OnlySign oa) (hf : ∀ a, OnlySign (f a)) : OnlySign (oa >>= f) := by
  rw [onlySign_iff] at h ⊢
  exact allQueriesSatisfy_bind h fun a => (onlySign_iff _).1 (hf a)

theorem onlySign_map {α β : Type} {oa : OracleComp (RoSpec C) α} (f : α → β) (h : OnlySign oa) :
    OnlySign (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact onlySign_bind h fun _ => onlySign_pure _

theorem onlySign_mapM {α β : Type} (xs : List α) (f : α → OracleComp (RoSpec C) β)
    (hf : ∀ a, OnlySign (f a)) : OnlySign (xs.mapM f) := by
  induction xs with
  | nil => exact onlySign_pure _
  | cons a xs ih =>
    simp only [List.mapM_cons]
    exact onlySign_bind (hf a) fun _ => onlySign_bind ih fun _ => onlySign_pure _

theorem onlySign_tweakable {α : Type} (oa : OracleComp HashSpec α) : OnlySign (tweakable (C := C) oa) := by
  rw [onlySign_iff]
  exact AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (fun _ => trivial) oa)
    fun _ _ => (allQueriesSatisfy_query_iff _ _).2 trivial

theorem onlySign_prfValue (seeds : C.Term → HashOutput) (x : Point) : OnlySign (prfValue seeds x) := by
  unfold prfValue
  refine onlySign_bind (onlySign_mapM _ _ fun T => ?_) fun _ => onlySign_pure _
  unfold prf
  refine onlySign_map _ ?_
  rw [onlySign_iff]
  exact (allQueriesSatisfy_query_iff _ _).2 trivial

/-- `referenceJob_bound` of `ThresholdLeanXmssSecurity/Proof/SigningSelection.lean` for the
predicate `SignCall`. -/
theorem onlySign_referenceJob (seeds : C.Term → HashOutput) (parameter : PublicParameter) (job : Job) :
    OnlySign (referenceJob tweakable (prfValue seeds) parameter job) := by
  unfold referenceJob
  refine onlySign_bind (onlySign_mapM _ _ fun x => onlySign_prfValue seeds x) fun values => ?_
  cases job.kind with
  | chainEnd key l => exact onlySign_map _ (onlySign_tweakable _)
  | chainRow key l =>
    exact onlySign_bind (onlySign_tweakable _) fun _ => onlySign_bind (onlySign_tweakable _) fun _ =>
      onlySign_bind (onlySign_tweakable _) fun _ => onlySign_pure _
  | chainValue key l p => exact onlySign_map _ (onlySign_tweakable _)
  | commitment key => exact onlySign_map _ (onlySign_tweakable _)
  | randomizer => exact onlySign_pure _

theorem onlySign_run (seeds : C.Term → HashOutput) (parameter : PublicParameter) (jobs : List Job) :
    OnlySign (some <$> jobs.mapM (referenceJob tweakable (prfValue seeds) parameter)) :=
  onlySign_map _ (onlySign_mapM _ _ fun job => onlySign_referenceJob seeds parameter job)

/-- `referenceTree_bound` of `ThresholdLeanXmssSecurity/Proof/SigningSelection.lean` for the
predicate `SignCall`. -/
theorem onlySign_referenceTree (seeds : C.Term → HashOutput) (parameter : PublicParameter) (top : TopTree)
    (tree : Tree) : OnlySign (referenceTree tweakable (prfValue seeds) parameter top tree) := by
  unfold referenceTree ceremonyOutput
  cases tree with
  | top =>
    refine onlySign_bind (onlySign_run seeds parameter _) fun outputs => ?_
    rcases outputs with _ | outputs
    · exact onlySign_pure _
    exact onlySign_bind (onlySign_tweakable _) fun _ => onlySign_pure _
  | bottom b =>
    refine onlySign_bind (onlySign_run seeds parameter _) fun outputs => ?_
    rcases outputs with _ | outputs
    · exact onlySign_pure _
    refine onlySign_bind (onlySign_tweakable _) fun root => ?_
    refine onlySign_bind (onlySign_tweakable _) fun base => ?_
    refine onlySign_bind (onlySign_tweakable _) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact onlySign_pure _
    refine onlySign_bind (onlySign_run seeds parameter _) fun values => ?_
    rcases values with _ | values
    · exact onlySign_pure _
    refine onlySign_bind (onlySign_tweakable _) fun path => ?_
    refine onlySign_bind (onlySign_tweakable _) fun topRoot => ?_
    split_ifs <;> exact onlySign_pure _

/-- A call of the free copy on `.hash` or on `.prf`. -/
def MonitorCall : (WorldSpec C).Domain → Prop
  | .inr (.inr t) => SignCall t
  | _ => False

/-- A computation of `H` and `PRG` with only calls on `.hash` and `.prf` makes on the free copy only
such calls. -/
theorem allQueries_free_liftComp {α : Type} {oa : OracleComp (RoSpec C) α} (h : OnlySign oa) :
    AllQueriesSatisfy (free (liftComp oa (LocalSpec C))) MonitorCall := by
  rw [onlySign_iff] at h
  have hl : AllQueriesSatisfy (liftComp oa (LocalSpec C)) fun t => match t with
      | .inr t => SignCall t
      | .inl _ => False :=
    AllQueriesSatisfy.simulateQ h fun _ ht => (allQueriesSatisfy_query_iff _ _).2 ht
  exact AllQueriesSatisfy.simulateQ hl fun t ht => (allQueriesSatisfy_query_iff _ _).2 (by
    rcases t with _ | t
    · exact ht.elim
    · exact ht)

/-- A computation of `H` and `PRG` with only calls on `.hash` and `.prf`, run on the free copy and
followed by a pure value, makes no call of `Q` when `Q` excludes each such call. It is an equation
for `rw`, because the elaboration of a term against the unfolded monitor reaches the recursion limit. -/
theorem noCall_free_bind_pure {α β : Type} (Q : (WorldSpec C).Domain → Prop)
    (hQ : ∀ t, MonitorCall t → ¬ Q t) (oa : OracleComp (RoSpec C) α) (f : α → β) (h : OnlySign oa) :
    NoCall Q (free (liftComp oa (LocalSpec C)) >>= fun r => pure (f r)) ↔ True := by
  refine iff_true_intro ((noCall_iff Q _).2 ?_)
  have hall := allQueriesSatisfy_bind (allQueries_free_liftComp h) fun r =>
    allQueriesSatisfy_pure (spec := WorldSpec C) (f r) MonitorCall
  have h' := (isQueryBoundP_zero_iff _ _).2 (hall.mono hQ)
  exact (isQueryBoundP_congr_pred fun t => not_not).1 h'

/-- The monitor `wrongOutput D` makes no call of `Q` when `Q` excludes each call of the free copy on
`.hash` and on `.prf`. With `Q` the complement of `MonitorCall`, each call of the monitor is a call of
the free copy on `.hash` or on `.prf`. -/
theorem wrongOutput_noCall (D : C.Coalition) (Q : (WorldSpec C).Domain → Prop)
    (hQ : ∀ t, MonitorCall t → ¬ Q t) (keys : C.Party → Option (Keys C)) (tree : Tree)
    (outputs : C.Party → Option TreeOutput) : NoCall Q (wrongOutput D keys tree outputs) := by
  unfold wrongOutput
  dsimp only
  rw [noCall_free_bind_pure Q hQ]
  · trivial
  refine onlySign_bind (onlySign_referenceTree _ _ _ _) fun top => ?_
  rcases tree with _ | b
  · exact onlySign_pure _
  · rcases TreeOutput.topTree top with _ | topTree
    · exact onlySign_pure _
    · exact onlySign_referenceTree _ _ _ _

/-! ## The honest calls of the setups -/

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- A computation makes at most `n` calls of `p`. It is irreducible, so that unification never unfolds
a deep computation of the game. -/
@[irreducible] def Bound {ι α : Type} {spec : OracleSpec ι} (p : ι → Prop) (oa : OracleComp spec α) (n : ℕ) :
    Prop :=
  oa.IsQueryBoundP p n

theorem bound_iff {ι α : Type} {spec : OracleSpec ι} (p : ι → Prop) (oa : OracleComp spec α) (n : ℕ) :
    Bound p oa n ↔ oa.IsQueryBoundP p n := by
  unfold Bound; rfl

theorem bound_bind {ι α β : Type} {spec : OracleSpec ι} {p : ι → Prop} {oa : OracleComp spec α}
    {k : α → OracleComp spec β} {n m : ℕ} (h : Bound p oa n) (hk : ∀ a, Bound p (k a) m) :
    Bound p (oa >>= k) (n + m) := by
  rw [bound_iff] at h ⊢
  exact isQueryBoundP_bind h fun a _ => (bound_iff p _ _).1 (hk a)

theorem bound_mono {ι α : Type} {spec : OracleSpec ι} {p : ι → Prop} {oa : OracleComp spec α} {n m : ℕ}
    (h : Bound p oa n) (hnm : n ≤ m) : Bound p oa m := by
  rw [bound_iff] at h ⊢
  exact h.mono hnm

theorem bound_pure {ι α : Type} {spec : OracleSpec ι} (p : ι → Prop) (a : α) :
    Bound p (pure a : OracleComp spec α) 0 := by
  rw [bound_iff]; trivial

/-- A cell of `H` in class `c`. A cell of `Th` on an input of the MPC is in no class. A call of `PRG`
adds the cell of its `.streamKey`, which is in class `stream`. -/
def CellIn (c : HashClass) : Query C → Prop
  | .hash input => ¬ MpcInput input ∧ c = .signing
  | q => queryClass q = c

end GameCount

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.streamHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.streamHop
