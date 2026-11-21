import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Partition

/-!
# The private table through the seed generation

* `seedGen_public` shows that the honest program of the seed generation makes no call in a cell
  outside the class of the seed generation. So it makes no call of `PRG`.
* `realExecution_coupling` shows that the real seed generation in `streamWorld` from the merged cache
  equals the real seed generation of `tableNet` over the world from the outer cache, with the table
  merged into the cache. The cache of the hidden streams stays.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedEmulation

open ThresholdLeanXmssSecurity.DkgCorrectnessProof.Partitioned (isPrivate)

variable {C : Committee} {E : Type}

/-- The cells outside the class of the seed generation. -/
def seedGenOutside (q : Query C) : Bool := !isSeedGenQuery q

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

/-! ## The honest program of the seed generation -/

section Setup

variable {ι : Type} {G : OracleSpec ι}

theorem hashQuery_public {q : Query C} (hq : isSeedGenQuery q = true) :
    AllQueriesSatisfy (ThresholdLeanXmss.hashQuery q) fun x => isPrivate seedGenOutside (.inr x) = false :=
  (allQueriesSatisfy_query_iff (spec := RoSpec C) (.inl q) _).2 (by simp [isPrivate, seedGenOutside, hq])

theorem deriveKeys_public (i : C.Party) (view : C.Party → Parts C) :
    AllQueriesSatisfy (deriveKeys .seedGen i view) fun x => isPrivate seedGenOutside (.inr x) = false := by
  unfold ThresholdLeanXmss.deriveKeys
  have hq : ∀ (k : KeyKind) (l : List HashOutput),
      AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.derive .seedGen k l))
        fun x => isPrivate seedGenOutside (.inr x) = false :=
    fun _ _ => hashQuery_public rfl
  refine allQueriesSatisfy_bind (hq _ _)
    fun parameter => ?_
  exact allQueriesSatisfy_bind
    (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun T => by split_ifs; exacts [hq _ _, allQueriesSatisfy_pure _ _]) _)
    fun _ => allQueriesSatisfy_bind
      (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun j => by split_ifs; exacts [allQueriesSatisfy_pure _ _, hq _ _]) _)
      fun _ => allQueriesSatisfy_pure _ _

theorem commitRevealEcho_public (i : C.Party) (own : Parts C) :
    PublicM (E := E) (G := G) seedGenOutside (commitRevealEcho .seedGen i own) := by
  have hc : ∀ a b l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.commit .seedGen a b l))
      fun x => isPrivate seedGenOutside (.inr x) = false := fun _ _ _ => hashQuery_public rfl
  have hs : ∀ l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.sharedKeys .seedGen l))
      fun x => isPrivate seedGenOutside (.inr x) = false := fun _ => hashQuery_public rfl
  unfold commitRevealEcho
  refine PublicM.bind (PublicM.oracleStep (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun _ => hc _ _ _) _))
    fun commitments => ?_
  refine PublicM.bind (PublicM.exchange _) fun committed => ?_
  refine PublicM.bind (PublicM.exchange _) fun revealed => ?_
  refine PublicM.bind (PublicM.oracleStep (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun _ => hc _ _ _) _))
    fun opens => ?_
  refine PublicM.bind (PublicM.require _) fun _ => ?_
  refine PublicM.bind (PublicM.oracleStep (deriveKeys_public _ _)) fun keys => ?_
  refine PublicM.bind (PublicM.oracleStep (DkgCorrectnessProof.UsedHit.mapM_satisfy _ _ (fun _ => hs _) _))
    fun shared => ?_
  refine PublicM.bind (PublicM.exchange _) fun received => ?_
  refine PublicM.bind (PublicM.require _) fun _ => ?_
  exact PublicM.pure _

/-- The honest program of the seed generation from its parts makes no call outside the class. -/
theorem seedGenWith_public (i : C.Party) (own : Parts C) :
    PublicM (E := E) (G := G) seedGenOutside (seedGenWith i own) :=
  PublicM.bind (commitRevealEcho_public _ _) fun _ => PublicM.pure _

/-- The honest program of the seed generation makes no call outside the class. -/
theorem seedGen_public (i : C.Party) : PublicM (E := E) (G := G) seedGenOutside (seedGen i) :=
  PublicM.bind (PublicM.sample _) fun own => seedGenWith_public i own

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

/-- A local computation with no private call makes only `WorldSafe Q` queries on the free copy, when
each stream key is private. -/
theorem free_worldSafe (hQ : ∀ k, Q (.streamKey k) = true) {β : Type} {oa : OracleComp (LocalSpec C) β}
    (h : AllQueriesSatisfy oa fun t => isPrivate Q t = false) :
    AllQueriesSatisfy (worldRoles.honest oa) (SeedPartition.WorldSafe Q) := by
  refine AllQueriesSatisfy.simulateQ h fun t ht => ?_
  refine (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inr t) _).2 ?_
  rcases t with n | q | x
  · exact ht
  · exact ht
  · simp [isPrivate, hQ] at ht

theorem advance_worldSafe (hQ : ∀ k, Q (.streamKey k) = true) {α : Type}
    (p : OracleComp (PartySpec C E G) (Option α)) (hp : PublicProg Q p) :
    AllQueriesSatisfy (worldRoles.honest (advance p)) (SeedPartition.WorldSafe Q) :=
  free_worldSafe Q hQ (advance_public Q p hp)

end Honest

/-! ## The private table of `tableNet` through a phase -/

section Phase

variable (prims : Primitives)

theorem seedGenOutside_streamKey (k : HashOutput) : seedGenOutside (C := C) (.streamKey k) = true := rfl

/-- The handler of `tableNet` is the handler of the private table of the cells outside the class. -/
theorem tableLocal_eq : DkgSecurityProof.tableLocal (C := C) prims = DkgCorrectnessProof.Partitioned.tableLocal seedGenOutside prims := by
  funext t
  rcases t with n | q | x
  · rfl
  · by_cases hq : isSeedGenQuery q = true
    · simp [DkgSecurityProof.tableLocal, DkgCorrectnessProof.Partitioned.tableLocal, isPrivate, seedGenOutside, hq]
      rfl
    · simp [DkgSecurityProof.tableLocal, DkgCorrectnessProof.Partitioned.tableLocal, isPrivate, seedGenOutside, hq]
      rfl
  · simp [DkgSecurityProof.tableLocal, DkgCorrectnessProof.Partitioned.tableLocal, isPrivate, seedGenOutside]
    rfl

theorem adversary_map {α β : Type} (f : α → β) (oa : OracleComp (LocalSpec C) α) :
    worldRoles.adversary (f <$> oa) = f <$> worldRoles.adversary oa := by
  rw [map_eq_bind_pure_comp, ThresholdLeanXmssSecurity.adversary_bind, map_eq_bind_pure_comp]
  rfl

theorem tableNet_round (net : Adversary C E Unit PEmpty PEmpty) (st : net.State × HashCache C)
    (sent : C.Party → C.Party → Option (Msg E)) :
    (tableNet prims net).round st sent =
      (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (DkgCorrectnessProof.Partitioned.tableLocal seedGenOutside prims) (net.round st.1 sent)).run st.2 := by
  simp only [tableNet, tableLocal_eq, map_eq_bind_pure_comp]
  rfl

theorem tableNet_start (net : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Option Unit) (z : Aux) :
    (tableNet prims net).start x z = (simulateQ (DkgCorrectnessProof.Partitioned.tableLocal seedGenOutside prims) (net.start x z)).run ∅ := by
  simp only [tableNet, tableLocal_eq]

theorem nextSteps_worldSafe {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepPublic seedGenOutside (steps i)) (sent : C.Party → C.Party → Option (Msg E)) :
    AllQueriesSatisfy (DkgCorrectnessProof.UsedHit.nextSteps D steps sent) (SeedPartition.WorldSafe seedGenOutside) := by
  refine DkgCorrectnessProof.UsedHit.sequenceFin_setup _ fun j => ?_
  have hj := hsteps j
  split
  · exact allQueriesSatisfy_pure _ _
  · rename_i heq
    rw [heq] at hj
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact advance_worldSafe _ seedGenOutside_streamKey _ (hj _)
  · exact allQueriesSatisfy_pure _ _

theorem stepRound_coupling (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) {α : Type}
    (st : net.State) (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepPublic seedGenOutside (steps i))
    (s p : HashCache C) (H : HiddenCache C) :
    (simulateQ (streamWorld prims D) (stepRound worldRoles D net noFunctionality st steps)).run
        (SeedPartition.merge seedGenOutside s p, H) =
      (fun z => ((z.1.1.1, z.1.2.1, z.1.2.2), (SeedPartition.merge seedGenOutside z.2 z.1.1.2, H))) <$>
        (simulateQ (worldAnswer prims)
          (stepRound worldRoles D (tableNet prims net) noFunctionality (st, p) steps)).run s := by
  rw [DkgCorrectnessProof.UsedHit.stepRound_real D net st steps,
    DkgCorrectnessProof.UsedHit.stepRound_real D (tableNet prims net) (st, p) steps, simulateQ_bind,
    StateT.run_bind, simulateQ_bind, StateT.run_bind, SeedPartition.adversary_coupling seedGenOutside prims D,
    tableNet_round]
  erw [adversary_map, simulateQ_map, StateT.run_map]
  rw [bind_map_left, bind_map_left, map_bind]
  refine bind_congr fun z => ?_
  rw [simulateQ_bind, StateT.run_bind, SeedPartition.simulate_frame seedGenOutside prims D
    (nextSteps_worldSafe D steps hsteps _)]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure, bind_map_left]

/-- Each next step of a round of steps with no private call has no private call. -/
theorem stepRound_stepPublic (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) {α : Type}
    (st : A.State) (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepPublic seedGenOutside (steps i))
    (s : HashCache C) (z : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) ×
      HashCache C)
    (hz : z ∈ support ((simulateQ (worldAnswer prims) (stepRound worldRoles D A noFunctionality st steps)).run s)) :
    ∀ i, StepPublic seedGenOutside (z.1.2.1 i) := by
  have h1 : z.1 ∈ support (stepRound worldRoles D A noFunctionality st steps) := by
    refine support_simulateQ_run'_subset (worldAnswer prims) _ s ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  rw [DkgCorrectnessProof.UsedHit.stepRound_real, mem_support_bind_iff] at h1
  obtain ⟨r, -, h1⟩ := h1
  rw [mem_support_bind_iff] at h1
  obtain ⟨steps', hsteps', h1⟩ := h1
  rw [support_pure, Set.mem_singleton_iff] at h1
  rw [h1]
  intro i
  change StepPublic seedGenOutside (steps' i)
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
    · exact advance_stepPublic seedGenOutside _ (hpi _) _ (support_simulateQ_subset _ _ hi)
  | call input resume => exact input.elim

/-- The rounds of a phase in `streamWorld` from the merged cache equal the rounds of `tableNet` from
the outer cache with the table in its state, with the table merged into the cache. -/
theorem executeRounds_coupling (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) {α : Type} :
    ∀ (fuel : ℕ) (st : net.State) (steps : C.Party → Step C E RealSpec α), (∀ i, StepPublic seedGenOutside (steps i)) →
      ∀ (s p : HashCache C) (H : HiddenCache C),
        (simulateQ (streamWorld prims D) (executeRounds worldRoles D net noFunctionality fuel st steps)).run
            (SeedPartition.merge seedGenOutside s p, H) =
          (fun z => ((z.1.1.1, z.1.2), (SeedPartition.merge seedGenOutside z.2 z.1.1.2, H))) <$>
            (simulateQ (worldAnswer prims)
              (executeRounds worldRoles D (tableNet prims net) noFunctionality fuel (st, p) steps)).run s
  | 0, st, steps, _, s, p, H => by simp [executeRounds]
  | fuel + 1, st, steps, hsteps, s, p, H => by
    simp only [executeRounds]
    split_ifs with h
    · simp
    · rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
        stepRound_coupling prims D net st steps hsteps s p H, bind_map_left, map_bind]
      refine bind_congr_of_forall_mem_support _ fun z hz => ?_
      exact executeRounds_coupling D net fuel z.1.1.1 z.1.2.1
        (stepRound_stepPublic prims D _ _ steps hsteps s z hz) z.2 z.1.1.2 H

theorem startSteps_worldSafe {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (hprog : ∀ i, PublicM seedGenOutside (program i)) :
    AllQueriesSatisfy (startSteps worldRoles D program) (SeedPartition.WorldSafe seedGenOutside) := by
  refine DkgCorrectnessProof.UsedHit.sequenceFin_setup _ fun i => ?_
  split_ifs
  · exact allQueriesSatisfy_pure _ _
  · exact advance_worldSafe _ seedGenOutside_streamKey _ (hprog i)

theorem startSteps_stepPublic {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (hprog : ∀ i, PublicM seedGenOutside (program i)) (s : HashCache C)
    (z : (C.Party → Step C E RealSpec α) × HashCache C)
    (hz : z ∈ support ((simulateQ (worldAnswer prims) (startSteps worldRoles D program)).run s)) :
    ∀ i, StepPublic seedGenOutside (z.1 i) := by
  have h1 : z.1 ∈ support (startSteps worldRoles D program) := by
    refine support_simulateQ_run'_subset (worldAnswer prims) _ s ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  intro i
  have hi := mem_support_sequenceFin_oc _ z.1 h1 i
  split_ifs at hi
  · simp only [support_pure, Set.mem_singleton_iff] at hi
    rw [hi]
    trivial
  · exact advance_stepPublic seedGenOutside _ (hprog i) _ (support_simulateQ_subset _ _ hi)

/-- A phase in `streamWorld` from the merged cache equals the phase of `tableNet` from the outer
cache with the table in its state, with the table merged into the cache. -/
theorem executePhase_coupling (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) {α : Type} (fuel : ℕ)
    (st : net.State) (program : C.Party → PartyM C E RealSpec α) (hprog : ∀ i, PublicM seedGenOutside (program i))
    (s p : HashCache C) (H : HiddenCache C) :
    (simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality fuel st program)).run
        (SeedPartition.merge seedGenOutside s p, H) =
      (fun z => ((z.1.1.1, z.1.2), (SeedPartition.merge seedGenOutside z.2 z.1.1.2, H))) <$>
        (simulateQ (worldAnswer prims)
          (executePhase worldRoles D (tableNet prims net) noFunctionality fuel (st, p) program)).run s := by
  unfold executePhase
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
    SeedPartition.simulate_frame seedGenOutside prims D (startSteps_worldSafe D program hprog), bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  exact executeRounds_coupling prims D net fuel st z.1 (startSteps_stepPublic prims D program hprog s z hz) z.2 p H

/-- The real seed generation in `streamWorld` from the merged cache equals the real seed generation
of `tableNet` from the outer cache, with the table merged into the cache. -/
theorem realExecution_coupling (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (z : Aux)
    (s : HashCache C) (H : HiddenCache C) :
    (simulateQ (streamWorld prims D) (realExecution D net noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) z)).run
        (SeedPartition.merge seedGenOutside s ∅, H) =
      (fun w => ((w.1.1.1, w.1.2), (SeedPartition.merge seedGenOutside w.2 w.1.1.2, H))) <$>
        (simulateQ (worldAnswer prims) (realExecution D (tableNet prims net) noFunctionality setupRounds
          (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) z)).run s := by
  unfold realExecution
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
    SeedPartition.adversary_coupling seedGenOutside prims D, bind_map_left, map_bind]
  erw [tableNet_start]
  refine bind_congr fun w => ?_
  exact executePhase_coupling prims D net setupRounds w.1.1 _ (fun i => seedGen_public i) w.2 w.1.2 H

end Phase

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedEmulation

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedEmulation.realExecution_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedEmulation.realExecution_coupling
