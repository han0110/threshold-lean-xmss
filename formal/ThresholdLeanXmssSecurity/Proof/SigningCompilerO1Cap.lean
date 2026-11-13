import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1NoFalse

/-! # The early cap of the O1 source

Each stored cap tag is below the final cap of the run, so a cap part of the tag of the first share
failure stays up to the final cap of the lazy run. A share failure of the lazy run gives a final
hidden flag that is up, because no first failure has a false tag.

`tableRunCO1_capEarly_le` states that a table run with the flag up and an early cap costs at most a
pad run with the flag up and the cap. The events before the first failure and the erased first
failure have the same law in the lazy run and in the table run.

The lemmas are the lemmas of `SigningCompilerShareCap` for the O1 program.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Cap
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareCap
open SigningCompilerO1SourceProof SigningCompilerO1Share SigningCompilerO1Tables
open SigningCompilerO1Marks SigningCompilerO1Runs SigningCompilerO1NoFalse
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
attribute [local irreducible] sourceProgramO1X sourceProgramO1 sourceGameO1X sourceGameO1

/-- A first failure with a cap part that is up is a failure with a true cap part. -/
theorem badCap_iffO1 (z : CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) :
    BadCap (SigningShareLazy.erase z.2).bad ↔
      ∃ m k l, z.2.bad = some ((m, true), k, l) := by
  simp only [BadCap, SigningShareLazy.erase]
  cases hb : z.2.bad with
  | none => simp
  | some r => rcases r with ⟨⟨m, c⟩, k, l⟩; cases c <;> simp

/-- Disjoint events add exactly. This lemma is a port of the private
`SigningCompilerShareCap.probEvent_or_eq`. -/
private theorem probEvent_or_eq {α : Type} (oa : ProbComp α) (P Q : α → Prop)
    (disjoint : ∀ z, P z → Q z → False) :
    Pr[fun z => P z ∨ Q z | oa] = Pr[P | oa] + Pr[Q | oa] := by
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro z
  by_cases hp : P z <;> by_cases hq : Q z <;> simp_all

section CapRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- Each stored cap tag is below the final cap of the run. -/
theorem capRunO1_tagLe (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (z : CompilerOutcomeO1 C × ShareState C)
    (hz : z ∈ support ((simulateQ (Marks.handler τ draw finish)
      (shareRunTagO1 prims A x q s pads capOnly)).run SigningShareLazy.init)) :
    Marks.TagLe z.1.2.2.2 z.2 := by
  simp only [shareRunTagO1, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨r, hr, view, hv, rfl⟩ := hz
  have h := capJoint_tagLe x.1 x.2.1 q s pads τ draw finish
    (sourceProgramO1X prims A x) _ _ (fun _ _ _ hb => by cases hb) r hr
  change view ∈ support (pure ((r.2.cache, r.2.done), r.2) : ProbComp _) at hv
  simp only [mem_support_pure_iff] at hv
  subst view
  exact h

/-- A cap part of the tag of the first share failure stays up to the final cap of the lazy run. -/
theorem lazyRunCO1_capTrue (τ : CPoint → Digest)
    (z : CompilerOutcomeO1 C × ShareStateT C (Bool × Bool))
    (hz : z ∈ support (lazyRunCO1 prims A x q s pads τ))
    (m : Bool) (k : SigningShareLazy.Kind) (l : Bool)
    (hb : z.2.bad = some ((m, true), k, l)) : z.1.2.2.2 = true := by
  have h := lazyRun_retag (C := C) (Tag := Bool × Bool) Prod.snd τ
    (shareRunTagO1 prims A x q s pads capTag) SigningShareLazy.init
  rw [← shareRunTagO1_retag] at h
  have hz' : (z.1, mapBad Prod.snd z.2) ∈ support
      ((simulateQ (lazyHandlerTag τ) (shareRunTagO1 prims A x q s pads capOnly)).run
        SigningShareLazy.init) := by
    erw [h]
    rw [support_map]
    exact Set.mem_image_of_mem _ hz
  have bound := capRunO1_tagLe prims A x q s pads τ (fun _ => $ᵗ SigningShareLazy.HashOutput)
    Witness.lazyFinish (z.1, mapBad Prod.snd z.2) hz'
  exact Bool.le_iff_imp.mp (bound true k l (by simp [mapBad, hb])) rfl

/-- A share failure of the lazy run gives a final hidden flag that is up. -/
theorem lazyRunCO1_bad_hidden (hinj : Function.Injective x.2.1)
    (z : CompilerOutcomeO1 C × ShareStateT C (Bool × Bool))
    (hz : z ∈ support (lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)))
    (m c : Bool) (k : SigningShareLazy.Kind) (l : Bool)
    (hb : z.2.bad = some ((m, c), k, l)) : z.1.1.2.base.hiddenFlag = true := by
  have hz' : projectO1 z ∈ support (lazyRunO1 prims A x q s pads (NoFalse.tau s pads)) := by
    rw [← lazyRunCO1_project, support_map]
    exact Set.mem_image_of_mem _ hz
  cases m with
  | false =>
      have hn := (probEvent_eq_zero_iff.mp
        (lazyRunO1_falseBad_zero prims A x q s pads hinj k)) (projectO1 z) hz'
      exact (hn (by simp [projectO1, mapBad, SigningShareLazy.erase, hb])).elim
  | true =>
      exact shareRunO1_tagTrue prims A x q s pads (NoFalse.tau s pads)
        (fun _ => $ᵗ SigningShareLazy.HashOutput) Witness.lazyFinish (projectO1 z) hz' k l
        (by simp [projectO1, mapBad, hb])

/-- A table run with the flag up and an early cap costs at most a pad run with the flag up and the
cap. -/
theorem tableRunCO1_capEarly_le (hinj : Function.Injective x.2.1) :
    Pr[fun z => z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z |
      tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] ≤
    Pr[fun z => z.1.2.base.hiddenFlag = true ∧ z.2.2.2 = true |
      compilerRunPadsO1 prims A x q s pads] := by
  let N : CompilerOutcomeO1 C × ShareStateT C (Bool × Bool) → Prop :=
    fun z => (z.1.1.2.base.hiddenFlag = true ∧ z.1.2.2.2 = true) ∧ z.2.bad = none
  let B : CompilerOutcomeO1 C × ShareStateT C (Bool × Bool) → Prop :=
    fun z => BadCap (SigningShareLazy.erase z.2).bad
  have disjoint : ∀ z, N z → B z → False := by
    intro z hn hb
    obtain ⟨m, k, l, h⟩ := (badCap_iffO1 z).mp hb
    rw [hn.2] at h
    cases h
  have hn : Pr[N | lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)] =
      Pr[N | tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] :=
    nonbad_lawCO1 prims A x q s pads (NoFalse.tau s pads)
      (fun z => z.1.1.2.base.hiddenFlag = true ∧ z.1.2.2.2 = true)
  have hb : Pr[B | lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)] =
      Pr[B | tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] := by
    have h : Pr[BadCap | (fun z => (SigningShareLazy.erase z.2).bad) <$>
        lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)] =
        Pr[BadCap | (fun z => (SigningShareLazy.erase z.2).bad) <$>
          tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (erased_bad_lawCO1 prims A x q s pads (NoFalse.tau s pads))
    simpa only [probEvent_map, Function.comp_def, B] using h
  calc
    _ ≤ Pr[fun z => N z ∨ B z | tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] := by
      apply probEvent_mono
      intro z _ h
      rcases h.2 with noBad | bad
      · exact Or.inl ⟨⟨h.1, noBad.2⟩, noBad.1⟩
      · exact Or.inr ((badCap_iffO1 z).mpr bad)
    _ = Pr[N | tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] +
        Pr[B | tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] :=
      probEvent_or_eq _ N B disjoint
    _ = Pr[N | lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)] +
        Pr[B | lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)] := by rw [hn, hb]
    _ = Pr[fun z => N z ∨ B z | lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)] :=
      (probEvent_or_eq _ N B disjoint).symm
    _ ≤ Pr[fun z => z.1.1.2.base.hiddenFlag = true ∧ z.1.2.2.2 = true |
        lazyRunCO1 prims A x q s pads (NoFalse.tau s pads)] := by
      apply probEvent_mono
      intro z hz h
      rcases h with hn | hb
      · exact hn.1
      · obtain ⟨m, k, l, hb⟩ := (badCap_iffO1 z).mp hb
        exact ⟨lazyRunCO1_bad_hidden prims A x q s pads hinj z hz m true k l hb,
          lazyRunCO1_capTrue prims A x q s pads (NoFalse.tau s pads) z hz m k l hb⟩
    _ = _ := by
      rw [compilerRunPadsO1_eq_lazy prims A x q s pads hinj (NoFalse.tau s pads), probEvent_map]
      rfl

end CapRuns

end ThresholdLeanXmssSecurity.SigningCompilerO1Cap

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Cap.badCap_iffO1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Cap.badCap_iffO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Cap.capRunO1_tagLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Cap.capRunO1_tagLe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Cap.lazyRunCO1_capTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Cap.lazyRunCO1_capTrue

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Cap.lazyRunCO1_bad_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Cap.lazyRunCO1_bad_hidden

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Cap.tableRunCO1_capEarly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Cap.tableRunCO1_capEarly_le
