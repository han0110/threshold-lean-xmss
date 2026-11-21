import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Cover

/-!
# The bound of the flag of the real game with the shared event

`sharedBadBound_of_parts` proves `SharedBadBound`, the bound `flagError` of the flag of the real
game with the shared event, from three statements. `PassLaw` is the joint law of the cut and of one
ceremony with the record of a pass, and `passLaw` proves it. `PassReadyHop` states that each start
up to the first record passes the test `PassReady`. `PassFlagFirst` states that the flag comes with a
first record. `sharedBadBound_of_ready` proves `SharedBadBound` from these two statements.

* `first_le` splits a first record into the seeds, a start that does not pass the test, a run with
  its event, and the four collisions at its world, as `firstProbWith_le`.
* `PassRunBound` is the bound `runError` of one recorded run from a start that passes `PassReady`.
  `passRunBound_of_parts` proves it from `PassLaw`, `PassFresh`, `PassTopCover` and
  `PassBottomBound`.
* `sharedBadBound_of_hops` gives `SharedBadBound` from the hops of the game with the first record and
  `PassRunBound`. `sharedBadBound_of_parts` fills in each premise that the library proves, the six
  hops of `passFirst`, `passFresh`, `passTopCover` and `passBottomBound`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The bound of one recorded run with the shared event from a ready start. The top tree has one
ceremony, and `passCeremonyBad` at `topStart` is its bound. A bottom tree has the cut of the library
before its second ceremony, and `passCeremonyBad` is the bound of each of its two ceremonies. -/
def PassRunBound : Prop :=
  0 < settings.batchSize → 0 < runLimit → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      PassRunBad prims K circuits settings D A.net (PassReady (startBudget circuits settings runLimit C q) D)
        (runError (E := E) circuits settings runLimit C q)

omit [DecidableEq E] in
/-- `PassRunBound` from `PassLaw`, `PassFresh`, `PassTopCover` and `PassBottomBound`. The top tree is
`PassTopCover` and `passCeremonyBad` at `topStart`, as `runBad_top` of the library. A bottom tree is
`PassBottomBound`. -/
theorem passRunBound_of_parts (law : PassLaw prims K circuits settings) (fresh : PassFresh prims K circuits settings)
    (top : PassTopCover prims K circuits settings) (bottom : PassBottomBound prims K circuits settings runLimit) :
    PassRunBound prims K circuits settings runLimit := by
  intro batch runs compute D A q bounded tree s world ready flag
  obtain ⟨start, step, forge, hsum, -, hround, -⟩ := id bounded
  have hstep : ∀ st sent, IsQueryBoundP (A.net.round st sent) Counted step := fun st sent =>
    isQueryBoundP_of_queryCostAtMost (hround st sent) fun _ ht =>
      one_le_ownCost (exists_inClass ht).choose_spec
  have hq : dkgTsigRounds circuits settings runLimit * step ≤ q := by omega
  cases tree with
  | bottom b => exact bottom batch runs compute D A q bounded b s world ready flag
  | top =>
    have hcover := ENNReal.toReal_mono (prEvent_ne_top _) (top D A.net s world ready.1)
    have hready : CeremonyReady D (startBudget circuits settings runLimit C q) (topStart s) world := ready
    have hjobs : (topStart (σ := A.net.State) s).jobs = topJobs := by simp only [topStart]
    have hbatches : (chunks settings.batchSize (topStart (σ := A.net.State) s).jobs).length =
        treeBatches settings .top := by
      rw [hjobs]
      exact topBatches settings
    have hroom := ledgerRoom_first (C := C) circuits settings runLimit runs .top q step (treeFuel circuits settings)
      (chunks settings.batchSize (topStart (σ := A.net.State) s).jobs).length le_rfl hbatches.le hq
    have hfuel : CheckTiming.ceremonyRounds circuits settings (gameParameter D (topStart s).keys)
        (topStart (σ := A.net.State) s).jobs ≤ treeFuel circuits settings := by
      rw [hjobs]
      exact topFuel circuits settings _
    have hbad := passCeremonyBad prims K circuits settings runLimit law fresh D A.net q step
      (treeFuel circuits settings) hstep _ (topStart s) world
      (admissible_of_protocol circuits settings 0 (fun _ => digit 0) _ (Or.inl hjobs)) hready hroom
      (padded_le circuits settings runLimit runs q step _ le_rfl hq) hfuel
    have hfresh := topFresh_le (C := C) runLimit
    rw [hbatches] at hbad hcover
    unfold runError
    unfold ceremonyFresh at hfresh hbad
    have hk : (startBudget circuits settings runLimit C q).hiddenKeys = gameSetups runLimit := rfl
    rw [hk] at hbad
    linarith

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A first record splits into the seeds, a start that does not pass the test, a run with its
event, and the four collisions at its world, as `firstProbWith_le`. -/
theorem first_le {σ : Type} (mx : ProbComp (FirstState C σ × StreamState C)) :
    (Pr{let r ← mx}[r.1.first ≠ none]).toReal ≤
      (Pr{let r ← mx}[∃ world, r.1.first = some (.seeds, world)]).toReal +
      (Pr{let r ← mx}[∃ tree index world, r.1.first = some (.unready tree index, world) ∧
        ¬ GlobalEvent world]).toReal +
      (Pr{let r ← mx}[∃ tree index world, r.1.first = some (.run tree index, world) ∧ ¬ GlobalEvent world]).toReal +
      ((Pr{let r ← mx}[∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision EchoDomain world.1]).toReal +
        (Pr{let r ← mx}[∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision DeriveDomain world.1]).toReal +
        (Pr{let r ← mx}[∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision CopyDomain world.1]).toReal +
        (Pr{let r ← mx}[∃ stage world, r.1.first = some (stage, world) ∧
          DomainCollision SplitHashDomain world.1]).toReal) := by
  have cover := prReal_mono mx (fun r => r.1.first ≠ none) (fun r =>
      (∃ world, r.1.first = some (.seeds, world)) ∨
      ((∃ tree index world, r.1.first = some (.unready tree index, world) ∧ ¬ GlobalEvent world) ∨
      ((∃ tree index world, r.1.first = some (.run tree index, world) ∧ ¬ GlobalEvent world) ∨
      ((∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision EchoDomain world.1) ∨
      ((∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision DeriveDomain world.1) ∨
      ((∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision CopyDomain world.1) ∨
      (∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision SplitHashDomain world.1)))))))
    (by
      intro r _ hfirst
      obtain ⟨⟨stage, world⟩, hsome⟩ := Option.ne_none_iff_exists'.mp hfirst
      cases stage with
      | seeds => exact Or.inl ⟨world, hsome⟩
      | unready tree index =>
        by_cases hglobal : GlobalEvent world
        · rcases hglobal with h | h | h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, world, hsome, h⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, world, hsome, h⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, world, hsome, h⟩)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, world, hsome, h⟩)))))
        · exact Or.inr (Or.inl ⟨tree, index, world, hsome, hglobal⟩)
      | run tree index =>
        by_cases hglobal : GlobalEvent world
        · rcases hglobal with h | h | h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, world, hsome, h⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, world, hsome, h⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, world, hsome, h⟩)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, world, hsome, h⟩)))))
        · exact Or.inr (Or.inr (Or.inl ⟨tree, index, world, hsome, hglobal⟩)))
  refine cover.trans ((prReal_or7_le mx _ _ _ _ _ _ _).trans ?_)
  linarith

omit [DecidableEq E] in
/-- `SharedBadBound` from the hops of the game with the first record and the bound `run` of one
recorded run. -/
theorem sharedBadBound_of_hops
    (flagFirst : PassFlagFirst prims K circuits settings runLimit)
    (seeds : PassSeedsHop prims K circuits settings runLimit)
    (echo : PassCollisionHop prims K circuits settings runLimit EchoDomain (echoError runLimit C))
    (reuse : PassCollisionHop prims K circuits settings runLimit DeriveDomain (reuseError runLimit C))
    (copy : PassCollisionHop prims K circuits settings runLimit CopyDomain (copyError settings runLimit C))
    (split : PassCollisionHop prims K circuits settings runLimit SplitHashDomain (splitError settings runLimit C))
    (union : PassRunsUnion prims K circuits settings runLimit)
    (ready : PassReadyHop prims K circuits settings runLimit)
    (run : PassRunBound prims K circuits settings runLimit) :
    SharedBadBound prims K circuits settings runLimit := by
  intro batch runs compute D A q bounded
  have h₁ := flagFirst D A (PassReady (startBudget circuits settings runLimit C q) D)
  have hsplit := first_le (passFirst prims K circuits settings runLimit D A
    (PassReady (startBudget circuits settings runLimit C q) D))
  have h₂ := seeds D A q (PassReady (startBudget circuits settings runLimit C q) D) bounded
  have hsign : ∀ tree, 0 ≤ runError (E := E) circuits settings runLimit C q tree := fun tree =>
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (checkErrorMax_nonneg circuits settings runLimit q))
      (by unfold freshError; positivity)
  have h₃ := union D A (PassReady (startBudget circuits settings runLimit C q) D) _ hsign
    (run batch runs compute D A q bounded)
  have h₄ := ready D A q bounded
  have h₅ := echo D A q (PassReady (startBudget circuits settings runLimit C q) D) bounded
  have h₆ := reuse D A q (PassReady (startBudget circuits settings runLimit C q) D) bounded
  have h₇ := copy D A q (PassReady (startBudget circuits settings runLimit C q) D) bounded
  have h₈ := split D A q (PassReady (startBudget circuits settings runLimit C q) D) bounded
  unfold passCollision at h₅ h₆ h₇ h₈
  unfold passFirstProb at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  unfold flagError
  linarith

/-- `SharedBadBound` from the three statements `PassLaw`, `PassReadyHop` and `PassFlagFirst`. The
other premises of `sharedBadBound_of_hops` are the theorems of the game with the first record and
the bound of one recorded run by `passRunBound_of_parts`, with `passFresh`, `passTopCover` and
`passBottomBound`. -/
theorem sharedBadBound_of_parts (law : PassLaw prims K circuits settings)
    (ready : PassReadyHop prims K circuits settings runLimit)
    (flagFirst : PassFlagFirst prims K circuits settings runLimit) :
    SharedBadBound prims K circuits settings runLimit :=
  sharedBadBound_of_hops prims K circuits settings runLimit flagFirst
    (passSeedsHop prims K circuits settings runLimit)
    (passEchoHop prims K circuits settings runLimit) (passReuseHop prims K circuits settings runLimit)
    (passCopyHop prims K circuits settings runLimit) (passSplitHop prims K circuits settings runLimit)
    (passRunsUnion prims K circuits settings runLimit) ready
    (passRunBound_of_parts prims K circuits settings runLimit law (passFresh prims K circuits settings)
      (passTopCover prims K circuits settings)
      (passBottomBound prims K circuits settings runLimit law (passFresh prims K circuits settings)))

/-- `SharedBadBound` from the two statements `PassReadyHop` and `PassFlagFirst`, by
`sharedBadBound_of_parts` with `passLaw`. -/
theorem sharedBadBound_of_ready (ready : PassReadyHop prims K circuits settings runLimit)
    (flagFirst : PassFlagFirst prims K circuits settings runLimit) :
    SharedBadBound prims K circuits settings runLimit :=
  sharedBadBound_of_parts prims K circuits settings runLimit (passLaw prims K circuits settings) ready flagFirst

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedBadBound_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedBadBound_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedBadBound_of_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedBadBound_of_ready
