import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Represent

/-!
# The erasure of the log of the real game with the shared event, with the flag kept

`sharedRestOf_eq_program` of the library represents the shared rest with the signing of the dealer
by a program with reads. `peekRep_sharedRestOf_own` adds the walk of the signing of the real game,
and `sharedRestOf_eq_programOf` holds for each `own`. The shared rest in `loggedWorld` from a state
with a log is then the shared rest in `streamWorld` from that state with no log
(`sharedRestOf_logged_stream`). The result keeps the win and the flag.

`sharedStream` is `sharedReal` in `streamWorld` with no log. `sharedReal_run'` states that the win
and the flag of `sharedReal` have the law of `sharedStream`, and `realProb_eq_stream` is its form
for the probability of an event.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The walk of the signing of the real game -/

section Walk

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
variable {M : Type → Type} [Monad M] [LawfulMonad M] {W : Type}
  (impl : QueryImpl (WorldSpec C) (StateT W M)) (view : W → StreamState C)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An answer of an honest operator. -/
theorem peekRepT_sign (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    PeekRepT impl view
      (do
        StateT.lift (modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true })
        let s ← StateT.lift get
        operatorAnswer (sharedLift impl)
          (fun x => sharedLift impl (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) (s.operators i) e q :
        StateT (TsigState C) (SharedM C M W σ) (TsigSpec C q))
      (do
        StateT.lift (modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true })
        let s ← StateT.lift get
        operatorAnswer (sharedLift peekHandler)
          (fun x => sharedLift peekHandler (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) (s.operators i) e q :
        StateT (TsigState C) (SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ) (TsigSpec C q)) := by
  refine (peekRepT_lift (peekRepS_modify _)).bind fun _ => peekRepT_get_bind fun s => ?_
  exact fun st => (peekRepS_inWorld _).of_eq
    (hom_operatorAnswer (worldHomOver impl σ) (fun oa => free (liftComp oa _))
      (fun x => free (liftComp (prfValue (gameSeeds D fun j => (s.operators j).keys) x) _)) (s.operators i) e q st)
    (hom_operatorAnswer (worldHomOver peekHandler σ) (fun oa => free (liftComp oa _))
      (fun x => free (liftComp (prfValue (gameSeeds D fun j => (s.operators j).keys) x) _)) (s.operators i) e q st)

omit [Fintype E] [DecidableEq E] in
/-- The signing oracles of the real game, in the real mode. -/
theorem peekRepT_ownOracles (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (q : TsigQuery C) :
    PeekRepT impl view
      (sharedOwnOracles K circuits settings runLimit impl view Mode.real D A.net parameter seeds dealt emu q)
      (sharedOwnOracles K circuits settings runLimit peekHandler id Mode.real D A.net parameter seeds dealt emu q) := by
  unfold sharedOwnOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact peekRepT_pure _
  · dsimp only
    refine peekRepT_lift ((peekRepS_sharedRuns_real K circuits settings runLimit impl view D A.net parameter seeds
      dealt emu _ 1).bind fun _ => peekRepS_get_bind fun s => ?_)
    split
    · exact (peekRepS_inWorld _).bind fun _ => peekRepS_pure _
    · exact peekRepS_pure _
  · exact peekRepT_sign impl view D i e _
  · exact peekRepT_sign impl view D i e _

omit [Fintype E] [DecidableEq E] in
/-- The signing phase of the real game, in the real mode. -/
theorem peekRepS_ownSigning (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) :
    PeekRepS impl view
      (sharedSigning K circuits settings runLimit impl view true Mode.real D A parameter seeds dealt emu)
      (sharedSigning K circuits settings runLimit peekHandler id true Mode.real D A parameter seeds dealt emu) := by
  unfold sharedSigning
  refine peekRepS_get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact peekRepS_pure _
  | some kt =>
    rcases kt with ⟨keys, top⟩
    simp only [↓reduceIte]
    refine (peekRepT_simulateQ _ _ (fun t => ?_) _ _).bind fun p => ?_
    · rcases t with t | q | q
      · exact peekRepT_lift (peekRepS_inWorld _)
      · exact peekRepT_ownOracles K circuits settings runLimit impl view D A parameter seeds dealt emu q
      · rcases q with _ | state
        · exact peekRepT_lift (peekRepS_mapGet _)
        · exact peekRepT_lift (peekRepS_modify _)
    · rcases p with ⟨forgery, st⟩
      refine peekRepS_get_bind fun s => ?_
      have hdealt : ∀ (M' : Type → Type) [Monad M'] [LawfulMonad M'] (W' : Type)
          (impl' : QueryImpl (WorldSpec C) (StateT W' M')),
          SeedHitProof.Dealt.hmap (worldHomOver impl' A.net.State) (worldDealt D s.operators keys.parameter top) =
            { dealtWith (m := SharedM C M' W' A.net.State) (sharedLift impl') keys.parameter
                (fun i => ((s.operators i).keys).getD noKeys) top
                (fun x => sharedLift impl' (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) with
              bottom := fun b => pure (heldBottom D s.operators b) } := by
        intro M' _ _ W' impl'
        unfold SeedHitProof.Dealt.hmap worldDealt
        congr 1
        funext b
        exact (worldHomOver impl' A.net.State).toFun_pure' _
      have h₁ := hom_forgeryWins (worldHomOver impl A.net.State) (fun oa => free (liftComp oa _))
        (worldDealt D s.operators keys.parameter top) st forgery
      have h₂ := hom_forgeryWins (worldHomOver peekHandler A.net.State) (fun oa => free (liftComp oa _))
        (worldDealt D s.operators keys.parameter top) st forgery
      rw [hdealt] at h₁ h₂
      exact (peekRepS_inWorld _).of_eq h₁ h₂

omit [Fintype E] [DecidableEq E] in
/-- The shared rest with real runs, for each `own`. -/
theorem peekRep_sharedRestOf_own (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) :
    PeekRep impl view (sharedRestOf K circuits settings runLimit impl view own D A state keys)
      (sharedRestOf K circuits settings runLimit peekHandler id own D A state keys) := by
  cases own with
  | false => exact peekRep_sharedRestOf K circuits settings runLimit impl view D A state keys
  | true =>
    unfold sharedRestOf sharedRest
    have h := (peekRepS_sharedRuns_real K circuits settings runLimit impl view D A.net (gameParameter D keys)
      (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none) .top runLimit).bind fun _ =>
        peekRepS_ownSigning K circuits settings runLimit impl view D A (gameParameter D keys) (gameSeeds D keys)
          (fun i => (keys i).getD noKeys) (fun _ => none)
    exact (h (startState D state keys)).bind fun p => by
      rcases p with ⟨win, s⟩
      exact peekRep_pure _

end Walk

/-! ## The representation and the log -/

/-- The shared rest with real runs as a program with reads, for each `own`. -/
def sharedProgramOf (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (own : Bool)
    (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State) (keys : C.Party → Option (Keys C)) :
    OracleComp (PeekSpec C) (Bool × Bool) :=
  programOf (sharedRestOf K circuits settings runLimit peekHandler id own D A state keys)

omit [Fintype E] [DecidableEq E] in
/-- The representation of the shared rest for each `own`, each handler `impl` of the world over a
lawful monad and each view `view` of its state. -/
theorem sharedRestOf_eq_programOf (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
    {M : Type → Type} [Monad M] [LawfulMonad M] {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W M))
    (view : W → StreamState C) (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) (w : W) :
    (sharedRestOf K circuits settings runLimit impl view own D A state keys).run' w =
      (simulateQ (withPeek impl view) (sharedProgramOf K circuits settings runLimit own D A state keys)).run' w :=
  run'_eq_programOf (peekRep_sharedRestOf_own K circuits settings runLimit impl view own D A state keys) w

omit [Fintype E] [DecidableEq E] in
/-- The shared rest in `loggedWorld` from a state with a log is the shared rest in `streamWorld` from
that state. The win and the flag are kept. -/
theorem sharedRestOf_logged_stream (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (runLimit : ℕ) (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (state : A.net.State) (keys : C.Party → Option (Keys C)) (w : StreamState C) (log : List (Query C)) :
    (sharedRestOf K circuits settings runLimit (loggedWorld prims D) Prod.fst own D A state keys).run' (w, log) =
      (sharedRestOf K circuits settings runLimit (streamWorld prims D) id own D A state keys).run' w := by
  rw [sharedRestOf_eq_programOf, sharedRestOf_eq_programOf, withPeek_loggedWorld, StateT.run'_eq, StateT.run'_eq,
    ← withLog_run _ peekCells _ w log, Functor.map_map]

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The game with the real seed generation and real runs with the shared event, in `streamWorld`
with no log. It is `sharedReal` with `streamWorld` in the place of `loggedWorld`. -/
def sharedStream (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    StateT (StreamState C) ProbComp (Bool × Bool) := do
  let (state, keys) ← simulateQ (streamWorld prims D) (realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])
  sharedRestOf K circuits settings runLimit (streamWorld prims D) id own D A state keys

omit [Fintype E] [DecidableEq E] in
/-- The win and the flag of `sharedReal` from a state with a log have the law of `sharedStream` from
that state. -/
theorem sharedReal_run' (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) (w : StreamState C)
    (log : List (Query C)) :
    (sharedReal prims K circuits settings runLimit own D A).run' (w, log) =
      (sharedStream prims K circuits settings runLimit own D A).run' w := by
  unfold sharedReal sharedStream
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  rw [loggedWorld_eq, ← withLog_run (streamWorld prims D) countedCells _ w log, bind_map_left]
  refine bind_congr fun p => ?_
  rcases p with ⟨⟨state, keys⟩, w', log'⟩
  exact sharedRestOf_logged_stream prims K circuits settings runLimit own D A state keys w' log'

omit [Fintype E] [DecidableEq E] in
/-- The probability of an event on the win and the flag of `sharedReal` is its probability on
`sharedStream` from the empty state. -/
theorem realProb_eq_stream (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) (event : Bool × Bool → Prop) :
    realProb prims K circuits settings runLimit own D A event =
      (Pr{let r ← (sharedStream prims K circuits settings runLimit own D A).run' (∅, ∅)}[event r]).toReal := by
  unfold realProb
  rw [← sharedReal_run' prims K circuits settings runLimit own D A (∅, ∅) [], StateT.run'_eq, prEvent_map]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRestOf_eq_programOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRestOf_eq_programOf

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.realProb_eq_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.realProb_eq_stream
