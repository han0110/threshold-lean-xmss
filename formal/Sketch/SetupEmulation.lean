import Sketch.PartitionedOracle
import Sketch.Count
import ThresholdLeanXmssSecurity.Proof.SeedGen

/-!
# The private table through a phase, and the honest steps of a setup

The cells outside the setups of `phase` are `outsideSetup phase`, the cells whose class of `queryClass` is
not the class of `phase`. For `phase = .prss` these are the cells with `decide (queryClass q ≠ .prssSetup)`.

* `setupKeys_public` shows that the honest program of one setup makes no call in a cell outside the setup.
  So it makes no call of `PRG` and no call of `.hash`. `advance_worldSafe` lifts this to each honest step
  of a phase on the free copy.
* `tableAdversary Q prims A` runs the adversary `A` with one private table for the cells with `Q` in its
  state. `executeRounds_coupling` and `executePhase_coupling` show that a phase on the world from
  `merge Q s p` equals the phase of `tableAdversary` from `s` with the table `p` in the state, with the
  table merged into the cache. So the result composes over the phases of a game.
* `distinguish_coupling` and `accepts_table` give the law of a real execution with its distinguisher.
  `accepts_prssSetup_table` is the instance of one PRSS setup.
* `adversary_toLocal` moves the calls of both copies to the counted copy, under `baseAnswer` only.
  `executePhase_toLocal` is the case of a phase on the real network.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch.SetupEmulation

open Partitioned (isPrivate tableLocal)

variable {C : Committee} {E : Type}

/-- The cells outside the setups of `phase`. -/
def outsideSetup (phase : Phase) (q : Query C) : Bool := decide (queryClass q ≠ phaseClass phase)

theorem outsideSetup_prss : outsideSetup (C := C) .prss = fun q => decide (queryClass q ≠ .prssSetup) := rfl

theorem isPrivate_prg (phase : Phase) (x : PrgInput C) :
    isPrivate (outsideSetup phase) (.inr (.inr x)) = true := by
  cases phase <;> rfl

theorem isPrivate_hash (phase : Phase) (input : HashInput) :
    isPrivate (outsideSetup phase) (.inr (.inl (.hash input)) : (LocalSpec C).Domain) = true := by
  cases phase <;> rfl

/-! ## Programs with no private call -/

section Programs

variable (Q : Query C → Bool) {ι : Type} {G : OracleSpec ι}

/-- A query of the program of an operator whose local part is no private call. -/
def PartyPublic : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => isPrivate Q t = false
  | _ => True

/-- A program of an operator that makes no private call on any path. -/
def PublicProg {α : Type} (p : OracleComp (PartySpec C E G) α) : Prop :=
  AllQueriesSatisfy p (PartyPublic (E := E) (G := G) Q)

/-- A program of `PartyM` that makes no private call on any path. -/
def PublicM {α : Type} (x : PartyM C E G α) : Prop := PublicProg Q x.run

/-- A step whose continuations make no private call. -/
def StepPublic {α : Type} : Step C E G α → Prop
  | .done _ => True
  | .wait _ k => ∀ m, PublicProg Q (k m)
  | .call _ k => ∀ r, PublicProg Q (k r)

variable {Q}

theorem PublicM.pure {α : Type} (a : α) : PublicM (E := E) (G := G) Q (Pure.pure a : PartyM C E G α) := by
  unfold PublicM PublicProg
  rw [OptionT.run_pure]
  exact allQueriesSatisfy_pure _ _

theorem PublicM.failure {α : Type} : PublicM (E := E) (G := G) Q (Alternative.failure : PartyM C E G α) := by
  unfold PublicM PublicProg
  rw [OptionT.run_failure]
  exact allQueriesSatisfy_pure _ _

theorem PublicM.bind {α β : Type} {x : PartyM C E G α} {f : α → PartyM C E G β} (hx : PublicM Q x)
    (hf : ∀ a, PublicM Q (f a)) : PublicM Q (x >>= f) := by
  unfold PublicM PublicProg at *
  rw [OptionT.run_bind]
  refine allQueriesSatisfy_bind hx fun o => ?_
  cases o with
  | none => exact allQueriesSatisfy_pure _ _
  | some a => exact hf a

theorem PublicM.localStep {β : Type} {oa : OracleComp (LocalSpec C) β}
    (h : AllQueriesSatisfy oa fun t => isPrivate Q t = false) :
    PublicM (E := E) (G := G) Q (localStep oa) := by
  unfold PublicM PublicProg ThresholdLeanXmss.localStep
  simp only [OptionT.run_lift]
  refine allQueriesSatisfy_bind (AllQueriesSatisfy.simulateQ h fun t ht => ?_) fun _ => allQueriesSatisfy_pure _ _
  rw [liftM_query_local]
  exact (allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inl t)) _).2 ht

theorem PublicM.oracleStep {β : Type} {oa : OracleComp (RoSpec C) β}
    (h : AllQueriesSatisfy oa fun x => isPrivate Q (.inr x) = false) :
    PublicM (E := E) (G := G) Q (oracleStep oa) := by
  refine PublicM.localStep (AllQueriesSatisfy.simulateQ h fun x hx => ?_)
  rcases x with q | x
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inl q)) _).2 hx
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inr x)) _).2 hx

theorem PublicM.sample {β : Type} (pc : ProbComp β) :
    PublicM (E := E) (G := G) Q (ThresholdLeanXmss.localStep (liftComp pc (LocalSpec C))) := by
  refine PublicM.localStep (AllQueriesSatisfy.simulateQ
    (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) pc) fun t _ => ?_)
  exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inl t) _).2 rfl

theorem PublicM.exchange (outbox : Mail C E) : PublicM (G := G) Q (ThresholdLeanXmss.exchange outbox) := by
  unfold PublicM PublicProg ThresholdLeanXmss.exchange
  simp only [OptionT.run_bind, OptionT.run_lift]
  refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inr outbox)) _).2
    trivial) fun inbox => ?_
  rcases inbox with _ | x
  · exact allQueriesSatisfy_pure _ _
  · dsimp only [Option.elim]
    split_ifs
    exacts [PublicM.failure (Q := Q) (E := E) (G := G) (α := Mail C E), PublicM.pure (Q := Q) (E := E) (G := G) x]

theorem PublicM.require (c : Prop) : PublicM (E := E) (G := G) Q (ThresholdLeanXmss.require c) := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact PublicM.pure _
  · exact PublicM.failure

end Programs

/-! ## The honest program of a setup -/

section Setup

variable {ι : Type} {G : OracleSpec ι}

-- Ported from `formal/Sketch/SeedGenEnd.lean` (`mapM_safe`).
theorem mapM_safe {κ : Type} {spec : OracleSpec κ} {α β : Type} (P : κ → Prop) (f : α → OracleComp spec β)
    (hf : ∀ a, AllQueriesSatisfy (f a) P) : ∀ l : List α, AllQueriesSatisfy (l.mapM f) P
  | [] => allQueriesSatisfy_pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (hf a) fun _ =>
      allQueriesSatisfy_bind (mapM_safe P f hf l) fun _ => allQueriesSatisfy_pure _ _

theorem hashQuery_public (phase : Phase) {q : Query C} (hq : queryClass q = phaseClass phase) :
    AllQueriesSatisfy (ThresholdLeanXmss.hashQuery q) fun x => isPrivate (outsideSetup phase) (.inr x) = false :=
  (allQueriesSatisfy_query_iff (spec := RoSpec C) (.inl q) _).2 (by simp [isPrivate, outsideSetup, hq])

theorem deriveKeys_public (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    AllQueriesSatisfy (deriveKeys phase i view) fun x => isPrivate (outsideSetup phase) (.inr x) = false := by
  unfold ThresholdLeanXmss.deriveKeys
  have hq : ∀ (k : KeyKind) (l : List HashOutput),
      AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.derive phase k l))
        fun x => isPrivate (outsideSetup phase) (.inr x) = false :=
    fun _ _ => hashQuery_public phase rfl
  have hrest : ∀ parameter : HashOutput, AllQueriesSatisfy (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        ThresholdLeanXmss.hashQuery (C := C)
          (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else Pure.pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then Pure.pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        ThresholdLeanXmss.hashQuery (C := C) (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      Pure.pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun (j : C.Party) => pair.getD j.val 0))
      fun x => isPrivate (outsideSetup phase) (.inr x) = false := fun parameter =>
    allQueriesSatisfy_bind (mapM_safe _ _ (fun T => by split_ifs; exacts [hq _ _, allQueriesSatisfy_pure _ _]) _)
      fun _ => allQueriesSatisfy_bind
        (mapM_safe _ _ (fun j => by split_ifs; exacts [allQueriesSatisfy_pure _ _, hq _ _]) _)
        fun _ => allQueriesSatisfy_pure _ _
  split_ifs
  · exact allQueriesSatisfy_bind (hq _ _) hrest
  · exact allQueriesSatisfy_bind (allQueriesSatisfy_pure _ _) hrest

theorem commitRevealEcho_public (phase : Phase) (i : C.Party) (own : Parts C) :
    PublicM (E := E) (G := G) (outsideSetup phase) (commitRevealEcho phase i own) := by
  have hc : ∀ a b l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.commit phase a b l))
      fun x => isPrivate (outsideSetup phase) (.inr x) = false := fun _ _ _ => hashQuery_public phase rfl
  have hs : ∀ l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.sharedKeys phase l))
      fun x => isPrivate (outsideSetup phase) (.inr x) = false := fun _ => hashQuery_public phase rfl
  unfold commitRevealEcho
  refine PublicM.bind (PublicM.oracleStep (mapM_safe _ _ (fun _ => hc _ _ _) _)) fun commitments => ?_
  refine PublicM.bind (PublicM.exchange _) fun committed => ?_
  refine PublicM.bind (PublicM.exchange _) fun revealed => ?_
  refine PublicM.bind (PublicM.oracleStep (mapM_safe _ _ (fun _ => hc _ _ _) _)) fun opens => ?_
  refine PublicM.bind (PublicM.require _) fun _ => ?_
  refine PublicM.bind (PublicM.oracleStep (deriveKeys_public _ _ _)) fun keys => ?_
  refine PublicM.bind (PublicM.oracleStep (mapM_safe _ _ (fun _ => hs _) _)) fun shared => ?_
  refine PublicM.bind (PublicM.exchange _) fun received => ?_
  refine PublicM.bind (PublicM.require _) fun _ => ?_
  exact PublicM.pure _

/-- The honest program of one setup of `phase` makes no call in a cell outside the setup. -/
theorem setupKeys_public (phase : Phase) (i : C.Party) :
    PublicProg (outsideSetup phase) (setupKeys (E := E) phase i).run := by
  change PublicM _ (setupKeys (E := E) phase i)
  unfold setupKeys setupWith
  refine PublicM.bind (PublicM.sample _) fun own => ?_
  exact PublicM.bind (commitRevealEcho_public _ _ _) fun _ => PublicM.pure _

end Setup

/-! ## The honest steps on the free copy -/

section Honest

variable (Q : Query C → Bool) {ι : Type} {G : OracleSpec ι}

/-- The local steps of a program with no private call make no private call. -/
theorem advance_public {α : Type} (p : OracleComp (PartySpec C E G) (Option α)) (hp : PublicProg Q p) :
    AllQueriesSatisfy (advance p) fun t => isPrivate Q t = false := by
  induction p using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    rw [PublicProg, allQueriesSatisfy_query_bind_iff] at hp
    rcases t with (t | outbox) | input
    · change AllQueriesSatisfy
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (k r)) _
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := LocalSpec C) t _).2 hp.1)
        fun r => ih r (hp.2 r)
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_pure _ _

/-- `advance` of a program with no private call stops at a step whose continuations make no private
call. -/
theorem advance_stepPublic {α : Type} (p : OracleComp (PartySpec C E G) (Option α)) (hp : PublicProg Q p) :
    ∀ z ∈ support (advance p), StepPublic Q z := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro z hz
    change z ∈ support (pure (Step.done x) : OracleComp (LocalSpec C) _) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    trivial
  | query_bind t k ih =>
    intro z hz
    rw [PublicProg, allQueriesSatisfy_query_bind_iff] at hp
    rcases t with (t | outbox) | input
    · change z ∈ support
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (k r)) at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨r, -, hz⟩ := hz
      exact ih r (hp.2 r) z hz
    · change z ∈ support (pure (Step.wait outbox k) : OracleComp (LocalSpec C) _) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hp.2
    · change z ∈ support (pure (Step.call input k) : OracleComp (LocalSpec C) _) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hp.2

/-- A local computation with no private call makes only `WorldSafe Q` queries on the free copy. -/
theorem free_worldSafe {β : Type} {oa : OracleComp (LocalSpec C) β}
    (h : AllQueriesSatisfy oa fun t => isPrivate Q t = false) :
    AllQueriesSatisfy (worldRoles.honest oa) (Partitioned.WorldSafe Q) :=
  AllQueriesSatisfy.simulateQ h fun t ht => (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inr t) _).2 ht

/-- An honest step of a program with no private call makes only `WorldSafe Q` queries. -/
theorem advance_worldSafe {α : Type} (p : OracleComp (PartySpec C E G) (Option α)) (hp : PublicProg Q p) :
    AllQueriesSatisfy (worldRoles.honest (advance p)) (Partitioned.WorldSafe Q) :=
  free_worldSafe Q (advance_public Q p hp)

/-- The first honest step of one setup of `phase` makes only `WorldSafe (outsideSetup phase)` queries. -/
theorem setupKeys_worldSafe (phase : Phase) (i : C.Party) :
    AllQueriesSatisfy (worldRoles.honest (advance (setupKeys (E := E) phase i).run))
      (Partitioned.WorldSafe (outsideSetup phase)) :=
  advance_worldSafe _ _ (setupKeys_public phase i)

/-- The first honest step of one PRSS setup, up to its first round, makes only `WorldSafe Q` queries for
the cells outside the class `prssSetup`. -/
theorem prssSetup_worldSafe (i : C.Party) :
    AllQueriesSatisfy (worldRoles.honest (advance (setupKeys (E := E) .prss i).run))
      (Partitioned.WorldSafe fun q : Query C => decide (queryClass q ≠ .prssSetup)) :=
  setupKeys_worldSafe .prss i

/-- The honest program of one PRSS setup makes no call in a cell outside the class `prssSetup`, on every
path. -/
theorem prssSetup_public (i : C.Party) :
    PublicProg (fun q : Query C => decide (queryClass q ≠ .prssSetup)) (setupKeys (E := E) .prss i).run :=
  setupKeys_public .prss i

end Honest

/-! ## One private table through a phase -/

section Phase

variable (Q : Query C → Bool) (prims : Primitives)

/-- The adversary `A` with one private table for the cells with `Q` in its state. Each piece of `A` runs
under `tableLocal Q prims` on the table of the state, and the start begins with the table `p0`. -/
abbrev tableAdversary {I L R : Type} (A : Adversary C E I L R) (p0 : HashCache C) : Adversary C E I L R where
  State := A.State × HashCache C
  start x z := (simulateQ (tableLocal Q prims) (A.start x z)).run p0
  round st sent :=
    (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (tableLocal Q prims) (A.round st.1 sent)).run st.2
  answer st l :=
    (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (tableLocal Q prims) (A.answer st.1 l)).run st.2

/-- The distinguisher `Z` on the table of the state of `tableAdversary`. -/
def tableDistinguisher {σ O : Type} (Z : Distinguisher C σ O) : Distinguisher C (σ × HashCache C) O :=
  fun r => (simulateQ (tableLocal Q prims) (Z (r.1.1, r.2))).run' r.1.2

theorem adversary_map {α β : Type} (f : α → β) (oa : OracleComp (LocalSpec C) α) :
    worldRoles.adversary (f <$> oa) = f <$> worldRoles.adversary oa := by
  rw [map_eq_bind_pure_comp, Partitioned.adversary_bind, map_eq_bind_pure_comp]
  rfl

/-- The next honest steps of a round on the real network, after the messages `sent` of the coalition. -/
def nextSteps {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (sent : C.Party → C.Party → Option (Msg E)) : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec α) :=
  OverPermutation.sequenceFin fun j => match steps j with
    | .done out => pure (Step.done out)
    | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
        worldRoles.honest (advance (resume fun k => if k ∈ D.1 then sent k j else (steps k).delivered j))
    | .call _ _ => pure (Step.done none)

theorem stepRound_real {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D A noFunctionality st steps =
      worldRoles.adversary (A.round st fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) >>=
        fun r => nextSteps D steps r.2 >>= fun steps' => pure (r.1, steps', r.2) := by
  simp only [stepRound, callInput_real, Option.isSome_none, Bool.false_eq_true, and_false,
    exists_false, false_and, ite_false]
  refine bind_congr fun r => ?_
  unfold nextSteps
  congr 2
  funext j
  cases steps j <;> rfl

theorem nextSteps_worldSafe {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepPublic Q (steps i)) (sent : C.Party → C.Party → Option (Msg E)) :
    AllQueriesSatisfy (nextSteps D steps sent) (Partitioned.WorldSafe Q) := by
  refine sequenceFin_safe _ fun j => ?_
  have hj := hsteps j
  split
  · exact allQueriesSatisfy_pure _ _
  · rename_i heq
    rw [heq] at hj
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact advance_worldSafe Q _ (hj _)
  · exact allQueriesSatisfy_pure _ _

theorem stepRound_coupling {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (p0 : HashCache C)
    (st : A.State) (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepPublic Q (steps i))
    (s p : HashCache C) :
    (simulateQ (baseAnswer prims) (stepRound worldRoles D A noFunctionality st steps)).run (Partitioned.merge Q s p) =
      (fun z => ((z.1.1.1, z.1.2.1, z.1.2.2), Partitioned.merge Q z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims)
          (stepRound worldRoles D (tableAdversary Q prims A p0) noFunctionality (st, p) steps)).run s := by
  rw [stepRound_real, stepRound_real, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
    Partitioned.adversary_coupling Q prims]
  change _ = _ <$> ((simulateQ (baseAnswer prims) (worldRoles.adversary ((fun r => ((r.1.1, r.2), r.1.2)) <$>
    (simulateQ (tableLocal Q prims) (A.round st _)).run p))).run s >>= _)
  rw [adversary_map, simulateQ_map, StateT.run_map, bind_map_left, bind_map_left, map_bind]
  refine bind_congr fun z => ?_
  rw [Partitioned.simulate_frame Q prims (allQueriesSatisfy_bind (nextSteps_worldSafe Q D steps hsteps _)
    fun _ => allQueriesSatisfy_pure _ _)]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]

/-- Each next step of a round of steps with no private call has no private call. -/
theorem stepRound_stepPublic {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (st : A.State) (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepPublic Q (steps i))
    (s : HashCache C) (z : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) ×
      HashCache C)
    (hz : z ∈ support ((simulateQ (baseAnswer prims) (stepRound worldRoles D A noFunctionality st steps)).run s)) :
    ∀ i, StepPublic Q (z.1.2.1 i) := by
  have h1 : z.1 ∈ support (stepRound worldRoles D A noFunctionality st steps) := by
    refine support_simulateQ_run'_subset (baseAnswer prims) _ s ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  rw [stepRound_real, mem_support_bind_iff] at h1
  obtain ⟨r, -, h1⟩ := h1
  rw [mem_support_bind_iff] at h1
  obtain ⟨steps', hsteps', h1⟩ := h1
  rw [support_pure, Set.mem_singleton_iff] at h1
  rw [h1]
  intro i
  change StepPublic Q (steps' i)
  have hi := mem_support_sequenceFin_oc _ steps' hsteps' i
  have hpi := hsteps i
  revert hi hpi
  cases steps i with
  | done out =>
    intro hi _
    simp only [support_pure, Set.mem_singleton_iff] at hi
    rw [hi]
    trivial
  | wait outbox resume =>
    intro hi hpi
    dsimp only at hi
    split_ifs at hi
    · simp only [support_pure, Set.mem_singleton_iff] at hi
      rw [hi]
      trivial
    · exact advance_stepPublic Q _ (hpi _) _ (support_simulateQ_subset _ _ hi)
  | call input resume => exact input.elim

/-- The rounds of a phase on the world from `merge Q s p` equal the rounds of `tableAdversary` from `s`
with the table `p` in its state, with the table merged into the cache. -/
theorem executeRounds_coupling {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (p0 : HashCache C) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E RealSpec α), (∀ i, StepPublic Q (steps i)) →
      ∀ s p : HashCache C,
        (simulateQ (baseAnswer prims) (executeRounds worldRoles D A noFunctionality fuel st steps)).run
            (Partitioned.merge Q s p) =
          (fun z => ((z.1.1.1, z.1.2), Partitioned.merge Q z.2 z.1.1.2)) <$>
            (simulateQ (baseAnswer prims)
              (executeRounds worldRoles D (tableAdversary Q prims A p0) noFunctionality fuel (st, p) steps)).run s
  | 0, st, steps, _, s, p => by simp [executeRounds]
  | fuel + 1, st, steps, hsteps, s, p => by
    simp only [executeRounds]
    split_ifs with h
    · simp
    · rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
        stepRound_coupling Q prims D A p0 st steps hsteps s p, bind_map_left, map_bind]
      refine bind_congr_of_forall_mem_support _ fun z hz => ?_
      exact executeRounds_coupling D A p0 fuel z.1.1.1 z.1.2.1
        (stepRound_stepPublic Q prims D _ _ steps hsteps s z hz) z.2 z.1.1.2

theorem startSteps_worldSafe {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (hprog : ∀ i, PublicM Q (program i)) :
    AllQueriesSatisfy (startSteps worldRoles D program) (Partitioned.WorldSafe Q) := by
  refine sequenceFin_safe _ fun i => ?_
  split_ifs
  · exact allQueriesSatisfy_pure _ _
  · exact advance_worldSafe Q _ (hprog i)

theorem startSteps_stepPublic {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (hprog : ∀ i, PublicM Q (program i)) (s : HashCache C)
    (z : (C.Party → Step C E RealSpec α) × HashCache C)
    (hz : z ∈ support ((simulateQ (baseAnswer prims) (startSteps worldRoles D program)).run s)) :
    ∀ i, StepPublic Q (z.1 i) := by
  have h1 : z.1 ∈ support (startSteps worldRoles D program) := by
    refine support_simulateQ_run'_subset (baseAnswer prims) _ s ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  intro i
  have hi := mem_support_sequenceFin_oc _ z.1 h1 i
  split_ifs at hi
  · simp only [support_pure, Set.mem_singleton_iff] at hi
    rw [hi]
    trivial
  · exact advance_stepPublic Q _ (hprog i) _ (support_simulateQ_subset _ _ hi)

/-- A phase on the world from `merge Q s p` equals the phase of `tableAdversary` from `s` with the table
`p` in its state, with the table merged into the cache. The honest programs make no private call. -/
theorem executePhase_coupling {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (p0 : HashCache C) (fuel : ℕ) (st : A.State) (program : C.Party → PartyM C E RealSpec α)
    (hprog : ∀ i, PublicM Q (program i)) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) (executePhase worldRoles D A noFunctionality fuel st program)).run
        (Partitioned.merge Q s p) =
      (fun z => ((z.1.1.1, z.1.2), Partitioned.merge Q z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims)
          (executePhase worldRoles D (tableAdversary Q prims A p0) noFunctionality fuel (st, p) program)).run s := by
  unfold executePhase
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
    Partitioned.simulate_frame Q prims (startSteps_worldSafe Q D program hprog), bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  exact executeRounds_coupling Q prims D A p0 fuel st z.1 (startSteps_stepPublic Q prims D program hprog s z hz) z.2 p

/-- A real execution on the world from `merge Q s p0` equals the real execution of `tableAdversary`
with the start table `p0` from `s`, with the table merged into the cache. -/
theorem realExecution_coupling {I O : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → I → PartyM C E RealSpec O) (hprog : ∀ i a, PublicM Q (program i a))
    (x : C.Party → I) (z : Aux) (s p0 : HashCache C) :
    (simulateQ (baseAnswer prims) (realExecution D A noFunctionality fuel program x z)).run
        (Partitioned.merge Q s p0) =
      (fun w => ((w.1.1.1, w.1.2), Partitioned.merge Q w.2 w.1.1.2)) <$>
        (simulateQ (baseAnswer prims)
          (realExecution D (tableAdversary Q prims A p0) noFunctionality fuel program x z)).run s := by
  unfold realExecution
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
    Partitioned.adversary_coupling Q prims, bind_map_left, map_bind]
  refine bind_congr fun w => ?_
  exact executePhase_coupling Q prims D A p0 fuel w.1.1 (fun i => program i (x i)) (fun i => hprog i (x i))
    w.2 w.1.2

/-- A real execution with its distinguisher has the same law of its result on the world from
`merge Q s p0` as the run of `tableAdversary` and `tableDistinguisher` with the start table `p0` from `s`. -/
theorem distinguish_coupling {I O : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → I → PartyM C E RealSpec O) (hprog : ∀ i a, PublicM Q (program i a))
    (x : C.Party → I) (z : Aux) (Z : Distinguisher C A.State O) (s p0 : HashCache C) :
    (simulateQ (baseAnswer prims) (distinguish (realExecution D A noFunctionality fuel program x z) Z)).run'
        (Partitioned.merge Q s p0) =
      (simulateQ (baseAnswer prims) (distinguish
        (realExecution D (tableAdversary Q prims A p0) noFunctionality fuel program x z)
        (tableDistinguisher Q prims Z))).run' s := by
  unfold distinguish
  rw [run'_bind, run'_bind, realExecution_coupling Q prims D A fuel program hprog x z s p0, bind_map_left]
  refine bind_congr fun w => ?_
  simp only [StateT.run'_eq, Partitioned.adversary_coupling Q prims, tableDistinguisher, adversary_map,
    simulateQ_map, StateT.run_map, Functor.map_map]

/-- From the empty cache, a real execution with its distinguisher accepts with the same probability as
the run of `tableAdversary` and `tableDistinguisher` with the empty start table. -/
theorem accepts_table {I O : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → I → PartyM C E RealSpec O) (hprog : ∀ i a, PublicM Q (program i a))
    (x : C.Party → I) (z : Aux) (Z : Distinguisher C A.State O) :
    accepts prims (distinguish (realExecution D (tableAdversary Q prims A ∅) noFunctionality fuel program x z)
        (tableDistinguisher Q prims Z)) =
      accepts prims (distinguish (realExecution D A noFunctionality fuel program x z) Z) := by
  rw [accepts_eq, accepts_eq, ← distinguish_coupling Q prims D A fuel program hprog x z Z ∅ ∅,
    Partitioned.merge_empty]

/-- The instance of one PRSS setup. With one private table for the cells outside the class `prssSetup`
from the empty cache, the setup run with its distinguisher accepts with the same probability. -/
theorem accepts_prssSetup_table (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (distinguish (realExecution D (tableAdversary (fun q => decide (queryClass q ≠ .prssSetup)) prims A ∅)
        noFunctionality setupRounds (fun i (_ : Unit) => setupKeys .prss i) x z)
        (tableDistinguisher (fun q => decide (queryClass q ≠ .prssSetup)) prims Z)) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => setupKeys .prss i) x z) Z) :=
  accepts_table _ prims D A setupRounds _ (fun i _ => setupKeys_public .prss i) x z Z

/-- Each honest step of a round of one PRSS setup makes only `WorldSafe Q` queries for the cells outside
the class `prssSetup`, for each messages of the coalition. -/
theorem prssSetup_nextSteps_worldSafe {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepPublic (fun q : Query C => decide (queryClass q ≠ .prssSetup)) (steps i))
    (sent : C.Party → C.Party → Option (Msg E)) :
    AllQueriesSatisfy (nextSteps D steps sent)
      (Partitioned.WorldSafe fun q : Query C => decide (queryClass q ≠ .prssSetup)) :=
  nextSteps_worldSafe _ D steps hsteps sent

/-- The first honest steps of one PRSS setup make only `WorldSafe Q` queries for the cells outside the
class `prssSetup`. -/
theorem prssSetup_startSteps_worldSafe (D : C.Coalition) :
    AllQueriesSatisfy (startSteps worldRoles D fun i => (setupKeys (E := E) .prss i : PartyM C E RealSpec (Keys C)))
      (Partitioned.WorldSafe fun q : Query C => decide (queryClass q ≠ .prssSetup)) :=
  startSteps_worldSafe _ D _ fun i => setupKeys_public .prss i

end Phase

/-! ## The honest calls on the counted copy -/

section Counted

variable (prims : Primitives)

/-- A query of the world that is no programming query. -/
def NoProgram : (WorldSpec C).Domain → Prop
  | .inl (.inr _) => False
  | _ => True

/-- The handler that sends a call of either copy to one local call. A programming query gets `false`,
and `NoProgram` excludes it. -/
def toLocal : QueryImpl (WorldSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inl (.inl t) => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t)
  | .inl (.inr _) => (pure false : OracleComp (LocalSpec C) Bool)
  | .inr t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t)

/-- Under `baseAnswer`, a computation with no programming query has the same run when each call of the
free copy moves to the counted copy, so that the whole computation runs on the counted copy. -/
theorem adversary_toLocal {α : Type} (oa : OracleComp (WorldSpec C) α) (h : AllQueriesSatisfy oa NoProgram) :
    simulateQ (baseAnswer prims) (worldRoles.adversary (simulateQ toLocal oa)) =
      simulateQ (baseAnswer prims) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [simulateQ_query_bind, Partitioned.adversary_bind, simulateQ_bind, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, monadLift_self]
    rcases t with (t | y) | t
    · exact (SeedHitProof.simulateQ_adversary_query (baseAnswer prims) t).symm ▸ bind_congr fun u => ih u (h.2 u)
    · exact h.1.elim
    · exact (SeedHitProof.simulateQ_adversary_query (baseAnswer prims) t).symm ▸ bind_congr fun u => ih u (h.2 u)

theorem adversary_noProgram {β : Type} (oa : OracleComp (LocalSpec C) β) :
    AllQueriesSatisfy (worldRoles.adversary oa) NoProgram := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    rw [Partitioned.adversary_bind, ThresholdLeanXmssSecurity.adversary_query]
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inl t)) _).2 trivial) ih

theorem honest_noProgram {β : Type} (oa : OracleComp (LocalSpec C) β) :
    AllQueriesSatisfy (worldRoles.honest oa) NoProgram :=
  AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) oa)
    fun t _ => (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inr t) _).2 trivial

theorem executeRounds_noProgram {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E RealSpec α),
      AllQueriesSatisfy (executeRounds worldRoles D A noFunctionality fuel st steps) NoProgram
  | 0, _, _ => allQueriesSatisfy_pure _ _
  | fuel + 1, st, steps => by
    simp only [executeRounds]
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · rw [stepRound_real]
      refine allQueriesSatisfy_bind (allQueriesSatisfy_bind (adversary_noProgram _) fun r =>
        allQueriesSatisfy_bind (sequenceFin_safe _ fun j => ?_) fun _ => allQueriesSatisfy_pure _ _)
        fun r => executeRounds_noProgram D A fuel r.1 r.2.1
      split
      · exact allQueriesSatisfy_pure _ _
      · split_ifs
        · exact allQueriesSatisfy_pure _ _
        · exact honest_noProgram _
      · exact allQueriesSatisfy_pure _ _

theorem executePhase_noProgram {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (fuel : ℕ)
    (st : A.State) (program : C.Party → PartyM C E RealSpec α) :
    AllQueriesSatisfy (executePhase worldRoles D A noFunctionality fuel st program) NoProgram := by
  unfold executePhase
  refine allQueriesSatisfy_bind (sequenceFin_safe _ fun i => ?_) fun steps => executeRounds_noProgram D A fuel st steps
  split_ifs
  · exact allQueriesSatisfy_pure _ _
  · exact honest_noProgram _

/-- Under `baseAnswer`, a phase on the real network has the same run as its local code on the counted
copy, so that an emulator can run the phase as its own local code. -/
theorem executePhase_toLocal {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (fuel : ℕ)
    (st : A.State) (program : C.Party → PartyM C E RealSpec α) :
    simulateQ (baseAnswer prims)
        (worldRoles.adversary (simulateQ toLocal (executePhase worldRoles D A noFunctionality fuel st program))) =
      simulateQ (baseAnswer prims) (executePhase worldRoles D A noFunctionality fuel st program) :=
  adversary_toLocal prims _ (executePhase_noProgram D A fuel st program)

end Counted

/-- info: 'ThresholdLeanXmss.Sketch.SetupEmulation.prssSetup_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prssSetup_public

/-- info: 'ThresholdLeanXmss.Sketch.SetupEmulation.prssSetup_startSteps_worldSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prssSetup_startSteps_worldSafe

/-- info: 'ThresholdLeanXmss.Sketch.SetupEmulation.executePhase_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms executePhase_coupling

/-- info: 'ThresholdLeanXmss.Sketch.SetupEmulation.distinguish_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms distinguish_coupling

/-- info: 'ThresholdLeanXmss.Sketch.SetupEmulation.accepts_prssSetup_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepts_prssSetup_table

/-- info: 'ThresholdLeanXmss.Sketch.SetupEmulation.adversary_toLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms adversary_toLocal

/-- info: 'ThresholdLeanXmss.Sketch.SetupEmulation.executePhase_toLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms executePhase_toLocal


end ThresholdLeanXmss.Sketch.SetupEmulation
