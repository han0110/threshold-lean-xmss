import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Real

/-!
# The ideal end of the seed generation claim

`idealExecution_worldSeedGen` writes `FseedGen` with `seedGenSimulator D A` as `worldSeedGen D A`
with the outputs of the dealer at the receivers, for each adversary `A`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

open SeedPartition SeedEmulation

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-- The outputs of `FseedGen` at the receivers, from a result of `worldSeedGen`. -/
def receivedKeys {σ : Type} (D : C.Coalition)
    (r : σ × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C))) :
    σ × (C.Party → Option (Keys C)) :=
  (r.1, fun i => if i ∉ D.1 ∧ (r.2.2.2.2 i).isSome then some (r.2.2.2.1 i) else none)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `FseedGen` with the simulator of `A` is `worldSeedGen D A` with the keys of the dealer at the
receivers. -/
theorem idealExecution_worldSeedGen (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) (fun _ => ()) [] =
      receivedKeys D <$> worldSeedGen D A := by
  rw [idealExecution_FseedGen]
  unfold worldSeedGen prawnsKeyGen
  simp only [seedGenSimulator, setupSimulator, ite_true, Option.map_map, map_bind, map_pure,
    liftComp_bind, liftComp_pure, free_bind, free_pure, bind_assoc]
  apply bind_congr; intro a
  obtain ⟨s0, l0⟩ := a
  simp only [pure_bind]
  apply bind_congr; intro parameter
  apply bind_congr; intro seeds
  apply bind_congr; intro pairs
  apply bind_congr; intro parts
  apply bind_congr; intro steps
  apply bind_congr; intro r
  apply bind_congr; intro high
  apply bind_congr; intro _
  congr 1
  · congr 1
    funext T
    rcases hj : List.find? (fun j => decide (j ∈ D.1 ∧ j ∈ C.holders T)) C.parties with _ | j
    · rfl
    · have hD : j ∈ D.1 := by
        have := List.find?_some hj
        simp only [decide_eq_true_eq] at this
        exact this.1
      dsimp only
      congr 1
      simp [hD]
  funext _
  congr 1
  · congr 1
    funext j
    congr 1
    funext i
    by_cases h : j ∈ D.1 ∧ i ∉ D.1
    · simp [h]
    · simp only [h, dite_false]
  funext _
  apply bind_congr; intro r'
  simp [receivedKeys]

/-! ## The keys of the corrupt operators -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem startSteps_corrupt {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (steps : C.Party → Step C E RealSpec α) (h : steps ∈ support (startSteps worldRoles D program)) :
    ∀ i ∈ D.1, steps i = .done none := by
  intro i hi
  have := mem_support_sequenceFin_oc _ steps h i
  simp only [hi, ite_true, support_pure, Set.mem_singleton_iff] at this
  exact this

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem stepRound_corrupt {α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i ∈ D.1, steps i = .done none)
    (z : A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E)))
    (hz : z ∈ support (stepRound worldRoles D A noFunctionality st steps)) : ∀ i ∈ D.1, z.2.1 i = .done none := by
  rw [UsedHit.stepRound_real, mem_support_bind_iff] at hz
  obtain ⟨r, -, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨steps', hsteps', hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  intro i hi
  have := mem_support_sequenceFin_oc _ steps' hsteps' i
  rw [hsteps i hi] at this
  simpa using this

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem executeRounds_corrupt {α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E RealSpec α), (∀ i ∈ D.1, steps i = .done none) →
      ∀ z ∈ support (executeRounds worldRoles D A noFunctionality fuel st steps), ∀ i ∈ D.1, z.2 i = none
  | 0, st, steps, hsteps, z, hz, i, hi => by
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp [hsteps i hi, Step.output]
  | fuel + 1, st, steps, hsteps, z, hz, i, hi => by
    simp only [executeRounds] at hz
    split_ifs at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [hsteps i hi, Step.output]
    · rw [mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      exact executeRounds_corrupt D A fuel r.1 r.2.1 (stepRound_corrupt D A st steps hsteps r hr) z hz i hi

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An emulated corrupt operator ends with no keys. -/
theorem worldSeedGen_corrupt (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (r : A.State × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C)))
    (hr : r ∈ support (worldSeedGen D A)) : ∀ i ∈ D.1, r.2.2.2.2 i = none := by
  have erase : ∀ {α : Type} (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) (z : α × CallLog C),
      z ∈ support p.run → z.1 ∈ support (seedGenEraseLog p) := fun p z hz => by
    rw [seedGenEraseLog, support_map]
    exact ⟨z, hz, rfl⟩
  unfold worldSeedGen at hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨a, -, b, -, parts, -, steps, hsteps, c, hc, high, -, -, -, -, -, -, -, d, hd, rfl⟩ := hr
  have h1 := startSteps_corrupt D _ steps hsteps
  have h2 := stepRound_corrupt D A _ steps h1 c.1 (by
    have := erase _ c hc
    rwa [seedGenEraseLog_stepRound] at this)
  have h3 := erase _ d hd
  rw [seedGenEraseLog_executeRounds] at h3
  exact executeRounds_corrupt D A _ _ _ h2 d.1 h3

/-! ## The ideal end from the coupling of `worldSeedGen` -/

/-- The seed generation of the simulator with `net` in `streamWorld` from the merged cache is the one
with `tableNet net` over the world from the outer cache, with the table merged into the cache. -/
def WorldSeedGenCoupling (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (S : HashCache C) (H : HiddenCache C),
    (simulateQ (streamWorld prims D) (worldSeedGen D net)).run (merge seedGenOutside S ∅, H) =
      (fun w => ((w.1.1.1, w.1.2), (merge seedGenOutside w.2 w.1.1.2, H))) <$>
        (simulateQ (worldAnswer prims) (worldSeedGen D (tableNet prims net))).run S

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem seedIdealGeneral_of_coupling (prims : Primitives) (coupling : WorldSeedGenCoupling (C := C) (E := E) prims) :
    SeedIdealGeneral (C := C) (E := E) prims := by
  intro D net β rest hrest
  rw [idealExecution_worldSeedGen]
  have hR := coupling D net ∅ ∅
  rw [merge_empty] at hR
  rw [hR, bind_map_left]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_map_left]
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  congr 2
  refine bind_congr_of_forall_mem_support _ fun w hw => ?_
  have hsupp : w.1 ∈ support (worldSeedGen D (tableNet prims net)) :=
    support_simulateQ_run'_subset (worldAnswer prims) _ ∅ (by rw [StateT.run'_eq, support_map]; exact ⟨w, hw, rfl⟩)
  have hkeys : (fun i => (w.1.2.2.2.2 i).map fun _ => w.1.2.2.2.1 i) = (receivedKeys D w.1).2 := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [receivedKeys, hi, worldSeedGen_corrupt D _ w.1 hsupp i hi]
    · cases h : w.1.2.2.2.2 i <;> simp [receivedKeys, hi, h]
  rw [hkeys, rest_split prims D _ (hrest _ _) w.2 w.1.1.2 ∅]
  simp only [Functor.map_map, adversary_map, simulateQ_map, StateT.run_map, receivedKeys]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.seedIdealGeneral_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.seedIdealGeneral_of_coupling
