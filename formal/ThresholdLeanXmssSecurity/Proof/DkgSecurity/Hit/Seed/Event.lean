import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Defs
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Count
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Cells

/-!
# The first hit under an emulated seed as a hit of a hidden cell

`dealtPartsRun` is `dealtRun` with the draw of the parts of the emulated operators in its result.
`CellHitOf` states that a counted call asks a PRF cell under the end value of the cache at the derive
input `hiddenInput parts T` of a hidden term `T`. `CellHit` bounds this event by `hitSeedError`.

`hitSeed_of_cellHit` states that `CellHit` gives `HitSeed`. An honest holder of a hidden term with keys
holds the value of the cache at the derive input of the term at the end of the seed generation
(`termCached`), and the cache only grows after it. So the event `HitSeedOf` is inside `CellHitOf`, and
it no longer reads which honest operator ends with keys.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The cache only grows along a world program in `loggedWorld`. -/
theorem loggedWorld_run_mono (D : C.Coalition) {β : Type} (oa : OracleComp (WorldSpec C) β) (w : LogState C)
    (z : β × LogState C) (hz : z ∈ support ((simulateQ (loggedWorld prims D) oa).run w)) : w.1.1 ≤ z.2.1.1 := by
  have h := withLog_run (streamWorld prims D) countedCells oa w.1 w.2
  rw [← loggedWorld_eq] at h
  have hz' : (z.1, z.2.1) ∈ support ((simulateQ (streamWorld prims D) oa).run w.1) := by
    rw [← h, support_map]
    exact ⟨z, hz, rfl⟩
  exact streamWorld_run_mono prims D oa w.1 _ hz'

/-- `dealtRun` with the parts of the emulated operators in its result. -/
def dealtPartsRun (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) ((C.Party → Parts C) ×
      (Bool × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C)))) := do
  let (state, early) ← observe (A.net.start (corruptInputs D fun _ => ()) [])
  let (parameter, seeds, dealt) ← free (liftComp (prawnsKeyGen (C := C)) _)
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
  let (state, emu) ← seedGenRest D A.net state early parameter dealt parts
  let keys := fun i => (emu i).map fun _ => dealt i
  let win ← (secRest K circuits settings runLimit m D A parameter seeds dealt emu).run' (startState D state keys)
  pure (parts, (win, parameter, seeds, dealt, emu))

omit [Fintype E] [DecidableEq E] in
theorem snd_dealtPartsRun (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Prod.snd <$> dealtPartsRun K circuits settings runLimit m D A = dealtRun K circuits settings runLimit m D A := by
  unfold dealtPartsRun dealtRun
  rw [worldSeedGen_eq]
  simp only [seedGenTail_eq_rest, map_bind, bind_assoc, pure_bind, map_pure]

/-- A counted call asks a PRF cell under the end value of the cache at the derive input of a hidden
term. -/
def CellHitOf (D : C.Coalition) (z : ((C.Party → Parts C) ×
    (Bool × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C)))) ×
      LogState C) : Prop :=
  ∃ q ∈ z.2.2, ∃ (T : C.Term) (v : HashOutput) (x : Point), ¬ KnownTo D.1 T ∧
    z.2.1.1 (hiddenInput z.1.1 T) = some v ∧ q = .prf v x

/-- The bound of `CellHitOf` in the game with the keys of the dealer and no emulated run. -/
def CellHit : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    (Pr{let z ← (simulateQ (loggedWorld prims D)
      (dealtPartsRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[CellHitOf D z]).toReal ≤
      hitSeedError C q

omit [Fintype E] [DecidableEq E] in
/-- On the support of `dealtPartsRun`, `HitSeedOf` is inside `CellHitOf`. -/
theorem cellHitOf_of_hit (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (z : ((C.Party → Parts C) ×
      (Bool × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C)))) ×
        LogState C)
    (hz : z ∈ support ((simulateQ (loggedWorld prims D) (dealtPartsRun K circuits settings runLimit m D A)).run
      ((∅, ∅), [])))
    (hit : ∃ q ∈ z.2.2, ∃ (i : C.Party) (keys : Keys C) (T : C.Term) (x : Point), i ∉ D.1 ∧
      z.1.2.2.2.2.2 i = some keys ∧ i ∈ C.holders T ∧ ¬ KnownTo D.1 T ∧ q = .prf (keys.seed T) x) :
    CellHitOf D z := by
  obtain ⟨q, hq, i, keys, T, x, hi, hk, hiT, hT, rfl⟩ := hit
  unfold dealtPartsRun at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, rfl⟩ := hz
  have hcache := termCached prims D A.net a.1.1 a.1.2 b.1.1 b.1.2.2 c.1 c.2 d hd i keys T hi hk hiT hT
  have hmono := loggedWorld_run_mono prims D _ d.2 e he
  exact ⟨_, hq, T, keys.seed T, x, hT, hmono hcache, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- `CellHit` gives `HitSeed`. -/
theorem hitSeed_of_cellHit (cell : CellHit prims K circuits settings runLimit) :
    HitSeed prims K circuits settings runLimit := by
  intro D A q bounded
  refine le_trans ?_ (cell D A q bounded)
  unfold dealtProb
  have e₁ := congrArg (fun x => StateT.run x (((∅, ∅), []) : LogState C))
    (sharedDealt_erase K circuits settings runLimit D prims ⟨true, fun _ => 0⟩ A)
  have e₂ := congrArg (fun x => StateT.run (simulateQ (loggedWorld prims D) x) (((∅, ∅), []) : LogState C))
    (snd_dealtPartsRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)
  simp only [StateT.run_map, simulateQ_map] at e₁ e₂
  have h₁ : Pr{let r ← (sharedDealt prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A).run ((∅, ∅), [])}[
      HitSeedOf D r] = Pr{let r ← (simulateQ (loggedWorld prims D)
        (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[
      ∃ q ∈ r.2.2, ∃ (i : C.Party) (keys : Keys C) (T : C.Term) (x : Point), i ∉ D.1 ∧
        r.1.2.2.2.2 i = some keys ∧ i ∈ C.holders T ∧ ¬ KnownTo D.1 T ∧ q = .prf (keys.seed T) x] := by
    rw [← e₁, prEvent_map]
    rfl
  rw [h₁, ← e₂, prEvent_map]
  refine ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_mono_of_support _ _ _ fun z hz hit => ?_)
  exact cellHitOf_of_hit prims K circuits settings runLimit _ D A z hz hit

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.hitSeed_of_cellHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.hitSeed_of_cellHit

