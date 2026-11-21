import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.PassFuel

/-!
# One ceremony with the record of a pass

`passGhost_erase` gives the ghost run of `ghostCeremony` with the starts, the honest batch outputs and
the outputs of a ghost run with the record of a pass. `passGhost_start` gives the shape of each
recorded start. `passGhost_started` gives the start of each check at each honest operator from one
honest output (`started_of_output`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem mapSteps_output {α ρ : Type} (D : C.Coalition) (f : C.Party → ρ → ρ)
    (steps : C.Party → RStep C E RealSpec α ρ) (l : C.Party) : (mapSteps D f steps l).output = (steps l).output := by
  unfold mapSteps
  split_ifs
  · rfl
  · cases steps l <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ceremonyRecord_eraseOpened (D : C.Coalition) (steps : CeremonySteps C E) (l : C.Party) (hl : l ∉ D.1) :
    ceremonyRecord (mapSteps D (fun _ => filterOpened) steps) l = filterOpened (ceremonyRecord steps l) := by
  unfold ceremonyRecord mapSteps
  rw [ite_eq_right hl]
  cases steps l <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem batchOutputsOf_filterOpened (record : Record C E) : batchOutputsOf (filterOpened record) = batchOutputsOf record := by
  induction record with
  | nil => rfl
  | cons e record ih =>
    cases e <;> simp [filterOpened, batchOutputsOf] at ih ⊢ <;> exact ih

/-- The ghost run of one ceremony with the record of a pass has the starts, the honest batch outputs,
the outputs and the world of a ghost run of `ghostCeremony`. -/
theorem passGhost_erase (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((passGhost prims K circuits settings D net rounds c).run world)) :
    ∃ ω' ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world), ω'.2 = ω.2 ∧
      (∀ l, startsOf (ceremonyRecord ω'.1.2 l) = startsOf (ceremonyRecord ω.1.2 l)) ∧
      (∀ l, l ∉ D.1 → batchOutputsOf (ceremonyRecord ω'.1.2 l) = batchOutputsOf (ceremonyRecord ω.1.2 l)) ∧
      ∀ l, (ω'.1.2 l).output = (ω.1.2 l).output := by
  have hmap : eraseOpened D ω ∈ support (eraseOpened D <$> (ghostCeremony prims K circuits settings D net rounds c).run
      world) := by
    rw [← passGhost_eraseOpened, support_map]
    exact ⟨ω, hω, rfl⟩
  rw [support_map] at hmap
  obtain ⟨ω', hω', heq⟩ := hmap
  have hsteps : ∀ l, mapSteps D (fun _ => filterOpened) ω'.1.2 l = mapSteps D (fun _ => filterOpened) ω.1.2 l :=
    fun l => congrFun (congrArg (fun x => x.1.2) heq) l
  have hfilter : ∀ l, l ∉ D.1 → filterOpened (ceremonyRecord ω'.1.2 l) = filterOpened (ceremonyRecord ω.1.2 l) := by
    intro l hl
    have e := congrArg (fun st => ceremonyRecord (fun _ => st) l) (hsteps l)
    simp only at e
    have e' : ceremonyRecord (mapSteps D (fun _ => filterOpened) ω'.1.2) l =
        ceremonyRecord (mapSteps D (fun _ => filterOpened) ω.1.2) l := e
    rwa [ceremonyRecord_eraseOpened D _ l hl, ceremonyRecord_eraseOpened D _ l hl] at e'
  refine ⟨ω', hω', by have e := congrArg Prod.snd heq; exact e, fun l => ?_, fun l hl => ?_, fun l => ?_⟩
  · by_cases hl : l ∈ D.1
    · have e := hsteps l
      unfold mapSteps at e
      rw [ite_eq_left hl, ite_eq_left hl] at e
      unfold ceremonyRecord
      rw [e]
    · rw [← startsOf_filterOpened, hfilter l hl, startsOf_filterOpened]
  · rw [← batchOutputsOf_filterOpened, hfilter l hl, batchOutputsOf_filterOpened]
  · rw [← mapSteps_output D (fun _ => filterOpened) ω'.1.2 l, hsteps l, mapSteps_output]

omit [DecidableEq E] in
/-- A start that an honest operator recorded in the ghost run of one ceremony with the record of a
pass is a start of the batch of the job list at its index, with the public facts of its keys. -/
theorem passGhost_start (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((passGhost prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (k : ℕ) (b : BatchStart C) (hb : (startsOf (ceremonyRecord ω.1.2 i))[k]? = some b) :
    ∃ keys, c.keys i = some keys ∧ (chunks settings.batchSize c.jobs)[k]? = some b.jobs ∧
      BatchCounters.Shape circuits settings i keys b := by
  obtain ⟨ω', hω', -, hstarts, -, -⟩ := passGhost_erase prims K circuits settings D net rounds c world ω hω
  exact ceremony_start prims K circuits settings D net rounds c world ω' hω' i hi k b (by rw [hstarts]; exact hb)

/-- In the ghost run of one ceremony with the record of a pass from consistent keys, an honest output
gives the start of each check at each honest operator. -/
theorem passGhost_started (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((passGhost prims K circuits settings D net rounds c).run world)) (i : C.Party) (hi : i ∉ D.1)
    (hiout : (ω.1.2 i).output.isSome) (k : ℕ) (hk : k < (chunks settings.batchSize c.jobs).length) :
    StartedAt D k ω.1.2 := by
  obtain ⟨ω', hω', -, hstarts, -, houtput⟩ := passGhost_erase prims K circuits settings D net rounds c world ω hω
  have hiout' : (ω'.1.2 i).output.isSome := by rw [houtput i]; exact hiout
  have hst : StartedAt D k ω'.1.2 := by
    by_cases hdead : ∃ j, j ∉ D.1 ∧ c.keys j = none
    · exfalso
      have hr : ((ω'.1.1, ceremonyOutputs ω'.1.2), ω'.2) ∈
          support ((ceremonyPhase prims K circuits settings D net rounds c).run world) := by
        rw [ghostCeremony_erase, support_map]
        exact ⟨ω', hω', rfl⟩
      have hnone := ceremonyDead prims K circuits settings D net rounds c world _ hr hdead i hi
      change (ω'.1.2 i).output = none at hnone
      rw [hnone] at hiout'
      exact absurd hiout' (by simp)
    push Not at hdead
    exact started_of_output prims K circuits settings D net rounds c world hseeds
      (fun j hj => Option.isSome_iff_ne_none.2 (hdead j hj)) ω' hω' ⟨i, hi, hiout'⟩ k hk
  intro j hj
  rw [← hstarts j]
  exact hst j hj

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passGhost_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passGhost_erase

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passGhost_started' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passGhost_started
