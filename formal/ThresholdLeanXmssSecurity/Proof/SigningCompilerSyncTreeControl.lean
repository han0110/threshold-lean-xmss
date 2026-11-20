import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTreeRows

/-! # Source control and stored bottom-tree row preservation

Structural ports of SigningCompilerCoupling.SourceKeeps and its sourceControl
lemmas to SourceMX; their oracle answers and control fields are unchanged.
-/
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeRows
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def SourceKeepsX {α β : Type} (field : SourceState C → β) (oa : SourceMX C α) : Prop :=
  ∀ source r, r ∈ support (oa.run source) → field r.2 = field source

theorem SourceKeepsX.pure {α β : Type} {field : SourceState C → β} (value : α) :
    SourceKeepsX field (pure value) := by
  intro source r hr
  simp only [StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  rfl

theorem SourceKeepsX.get {β : Type} {field : SourceState C → β} :
    SourceKeepsX field (get : SourceMX C (SourceState C)) := by
  intro source r hr
  simp only [StateT.run_get, mem_support_pure_iff] at hr
  subst r
  rfl

theorem SourceKeepsX.modify {β : Type} {field : SourceState C → β}
    (f : SourceState C → SourceState C) (hf : ∀ source, field (f source) = field source) :
    SourceKeepsX field (modify f : SourceMX C Unit) := by
  intro source r hr
  simp only [StateT.run_modify, mem_support_pure_iff] at hr
  subst r
  exact hf source

theorem SourceKeepsX.lift {α β : Type} {field : SourceState C → β}
    (oa : OracleComp (SpecX C) α) :
    SourceKeepsX field (liftM oa : SourceMX C α) := by
  intro source r hr
  change r ∈ support (oa >>= fun value => Pure.pure (value, source)) at hr
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem SourceKeepsX.bind {α β γ : Type} {field : SourceState C → γ}
    {oa : SourceMX C α} (h : SourceKeepsX field oa) (next : α → SourceMX C β)
    (hn : ∀ value, SourceKeepsX field (next value)) : SourceKeepsX field (oa >>= next) := by
  intro source r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact (hn a.1 a.2 r hr).trans (h source a ha)

theorem SourceKeepsX.mapM {α β γ : Type} {field : SourceState C → γ}
    (items : List α) (oa : α → SourceMX C β)
    (h : ∀ a ∈ items, SourceKeepsX field (oa a)) : SourceKeepsX field (items.mapM oa) := by
  induction items with
  | nil => exact SourceKeepsX.pure []
  | cons a items ih =>
      rw [List.mapM_cons]
      refine (h a (List.mem_cons_self ..)).bind _ fun value => ?_
      exact (ih (fun b hb => h b (List.mem_cons_of_mem _ hb))).bind _
        (fun values => SourceKeepsX.pure (value :: values))

/-- A field property proved for all source answers applies to the actual capped
interpreter by VCVio's support inclusion for stateful simulation. -/
theorem SourceKeepsX.run {α β : Type} {field : SourceState C → β} {oa : SourceMX C α}
    (h : SourceKeepsX field oa)
    (B : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (src : SourceState C) (st : FullState C Tag)
    (r : (α × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX B oa src st)) : field r.1.2 = field src := by
  apply h src r.1
  apply support_simulateQ_run'_subset B (oa.run src) st
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

theorem sourceControl_sourceReveal (key : HiddenKey) :
    SourceKeepsX (sourceControl (C := C)) (sourceRevealX key) := by
  unfold sourceRevealX
  refine SourceKeepsX.get.bind _ fun source => ?_
  cases source.revealed key with
  | some value => exact SourceKeepsX.pure value
  | none =>
      refine (SourceKeepsX.lift (revealQueryX key)).bind _ fun value => ?_
      exact (SourceKeepsX.modify (fun st => { st with revealed := Function.update st.revealed key (some value) }) (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure value)

theorem sourceControl_sourceRevealDigest (value : DeferredDigest) :
    SourceKeepsX (sourceControl (C := C)) (sourceRevealDigestX value) := by
  cases value with
  | known digest => exact SourceKeepsX.pure digest
  | secret key => exact sourceControl_sourceReveal key

theorem sourceControl_sourcePlant (P : PublicParameter) (p : PendingInput) :
    SourceKeepsX (sourceControl (C := C)) (sourcePlantX P p) := by
  unfold sourcePlantX
  refine (SourceKeepsX.lift (deferredQueryX (.inspect p))).bind _ fun answer => ?_
  cases answer with
  | none => exact SourceKeepsX.pure ()
  | some answer =>
      refine (sourceControl_sourceReveal p.key).bind _ fun input => ?_
      refine (sourceControl_sourceRevealDigest answer.low).bind _ fun low => ?_
      exact (SourceKeepsX.lift (deferredQueryX (.plant (.pending P p input)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, low))))).bind _
          (fun ok => SourceKeepsX.modify (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl))

theorem sourceControl_sourceReleaseOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceKeepsX sourceControl (sourceReleaseOpeningX P seeds e) := by
  unfold sourceReleaseOpeningX
  refine SourceKeepsX.get.bind _ fun source => ?_
  split
  · refine (sourceControl_sourceReveal (.opening bottomLayer e)).bind _ fun value => ?_
    refine (SourceKeepsX.lift (completeQ (.randomizer bottomLayer e) value)).bind _ fun ok => ?_
    refine (SourceKeepsX.modify (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl)).bind _ fun _ => ?_
    refine SourceKeepsX.get.bind _ fun current => ?_
    exact (SourceKeepsX.mapM _ (sourcePlantX P) (fun p _ => sourceControl_sourcePlant P p)).bind _
      (fun _ => SourceKeepsX.pure ())
  · exact SourceKeepsX.pure ()

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourceHash (P : PublicParameter) (seeds : C.Term → HashOutput) (query : Query C) :
    SourceKeepsX sourceControl (sourceHashX P seeds query) := by
  have hquery (query : Query C) :
      SourceKeepsX sourceControl (liftM (deferredQueryX (.hash query)) : SourceMX C HashOutput) := SourceKeepsX.lift _
  unfold sourceHashX
  cases query with
  | prf seed point =>
      cases point with
      | randomizer lay e =>
          dsimp only
          split
          · refine (SourceKeepsX.lift (deferredQueryX .snapshot)).bind _ fun backend => ?_
            refine SourceKeepsX.get.bind _ fun source => ?_
            split
            · exact (sourceControl_sourceReleaseOpening P seeds e).bind _ (fun _ => hquery _)
            · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
          · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
      | _ => simpa only [pure_bind] using hquery _
  | _ => simpa only [pure_bind] using hquery _

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourceVirtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (point : Point) : SourceKeepsX sourceControl (sourceVirtualX P seeds T point) := by
  unfold sourceVirtualX
  refine (SourceKeepsX.lift (deferredQueryX (.virtual T point))).bind _ fun _ => ?_
  cases point with
  | randomizer lay e =>
      dsimp only
      split
      · refine (SourceKeepsX.lift (deferredQueryX .snapshot)).bind _ fun backend => ?_
        refine SourceKeepsX.get.bind _ fun source => ?_
        split
        · exact sourceControl_sourceReleaseOpening P seeds e
        · exact SourceKeepsX.pure ()
      · exact SourceKeepsX.pure ()
  | _ => exact SourceKeepsX.pure ()

/-- Every stored successful or failed tree has its complete allocated row domain. -/
def TreeRows (x : Keys3 C) (src : SourceState C) (st : FullState C Tag) : Prop :=
  ∀ b, src.trees b ≠ none → BottomRows x b st

/-- Source initialization has no stored bottom tree. -/
theorem treeRows_initial (x : Keys3 C) (st : FullState C Tag) :
    TreeRows x sourceInit st := by
  intro b hb
  simp [sourceInit] at hb

end ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.get

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.modify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.lift

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReveal

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceRevealDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceRevealDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourcePlant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourcePlant

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReleaseOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReleaseOpening

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceVirtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceVirtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.treeRows_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.treeRows_initial
