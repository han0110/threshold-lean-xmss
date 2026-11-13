import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackRead

/-! # Builds of the base source that keep the linked invariant

The source frames, the raw backend calls, the pending handler, the virtual call and the pad read
keep `LinkedInvariant`. So the typed hash programs, the bottom rows, the top tree, the
commitments, the stored top values, their verification suffix and the bottom tree keep it too.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackSteps
open SigningCompilerO1SlackRun SigningCompilerO1SlackRead
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Steps
variable (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
  (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)

theorem sourceModify_linked (f : SourceState C → SourceState C)
    (hs : ∀ source, (f source).signing = source.signing)
    (hr : ∀ source, (f source).revealed = source.revealed) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (modify f : SourceM C Unit) :=
  SourcePreserves.modify f (fun source _ h =>
    ⟨by rw [hs source]; exact h.1, ReleaseInvariantO1.source_frame h.2 rfl (hr source)⟩)

set_option backward.isDefEq.respectTransparency false in
theorem sourceUniform_linked (n : ℕ) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (liftM (deferredQuery (C := C) (.uniform n))) := by
  intro source backend h r hr
  rw [runSource_deferredQuery_uncounted P seeds q s (.uniform n) (by exact not_false)] at hr
  simp only [compilerImpl, StateT.run, deferredImpl, Functor.map_map] at hr
  change r ∈ support ((fun value : Fin (n + 1) => ((value, source), backend)) <$>
    (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))) at hr
  rw [support_map] at hr
  obtain ⟨value, _, rfl⟩ := hr
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem sourceRawPending_linked (p : PendingInput) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (liftM (deferredQuery (C := C) (.pending p))) := by
  refine linked_of_signing P seeds q s sig starts _ (SourceKeeps.lift _) ?_
  intro source backend h r hr
  refine ⟨?_, sourceReveals_deferredQuery P seeds q s (.pending p) source backend h.2.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2.2 r hr⟩
  rw [runSource_deferredQuery_no_candidate P seeds q s (.pending p) rfl] at hr
  simp only [compilerImpl, StateT.run, support_map] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  cases hp : backend.1.1.data.pending p with
  | some value =>
      simp only [deferredImpl, hp, mem_support_pure_iff] at hb
      subst b
      exact h.2.1
  | none =>
      simp only [deferredImpl, hp, support_map] at hb
      obtain ⟨value, _, rfl⟩ := hb
      exact ReleaseSlackO1.frame h.2.1 (fun _ _ => rfl) rfl rfl (fun _ he => he)

set_option backward.isDefEq.respectTransparency false in
theorem sourceInspect_linked (p : PendingInput) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (liftM (deferredQuery (C := C) (.inspect p))) := by
  intro source backend h r hr
  rw [runSource_inspect, mem_support_pure_iff] at hr
  subst r
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem sourceRecord_linked (p : PendingInput) (value : HashOutput) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (liftM (deferredQuery (C := C) (.record p value))) := by
  refine linked_of_signing P seeds q s sig starts _ (SourceKeeps.lift _) ?_
  intro source backend h r hr
  refine ⟨?_, sourceReveals_deferredQuery P seeds q s (.record p value) source backend h.2.2.1
    r hr, runSource_pendingValid P seeds q s _ source backend h.2.2.2 r hr⟩
  rw [runSource_deferredQuery_uncounted P seeds q s (.record p value) (by exact not_false)] at hr
  simp only [compilerImpl, deferredImpl, StateT.run, support_map] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  simp only [mem_support_pure_iff] at hb
  subst b
  exact ReleaseSlackO1.frame h.2.1 (fun _ _ => rfl) rfl rfl (fun _ he => he)

set_option backward.isDefEq.respectTransparency false in
theorem sourcePending_linked (hinj : Function.Injective seeds) (p : PendingInput) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts) (sourcePending P p) := by
  have tail (prior : Option DeferredOutput) :
      SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts) (do
        let value ← liftM (deferredQuery (C := C) (.pending p))
        if prior.isNone then
          modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
        pure value : SourceM C DeferredOutput) := by
    refine (sourceRawPending_linked P seeds q s sig starts p).bind _ fun value => ?_
    split
    · exact (sourceModify_linked P seeds q s sig starts
        (fun st => { st with allocated := st.allocated ++ [p] })
        (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure value)
    · exact SourcePreserves.pure value
  unfold sourcePending
  refine (sourceInspect_linked P seeds q s sig starts p).bind _ fun prior => ?_
  refine SourcePreserves.get.bind _ fun source => ?_
  dsimp only
  split
  · rename_i priorCopy known next input hknown hnext
    have hhash := sourceHash_linked P seeds q s sig starts hinj (.hash (p.input P input))
        (fun _ _ he => by cases he)
    simp only [sourceHash, pure_bind] at hhash
    refine hhash.bind _ fun value => ?_
    refine (sourceRecord_linked P seeds q s sig starts p value).bind _ fun _ => ?_
    exact (sourceModify_linked P seeds q s sig starts
      (fun st => { st with allocated := st.allocated ++ [p] })
      (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (sourceModify_linked P seeds q s sig starts (fun st => { st with consistent := false })
        (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => tail original)
    · simpa only [pure_bind] using tail original

theorem sourceVirtual_linked (hinj : Function.Injective seeds) (T : C.Term) (point : Point) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceVirtual P seeds T point) := by
  refine linked_of_signing P seeds q s sig starts _
    ((sourceControl_sourceVirtual P seeds T point).comp Prod.fst) ?_
  intro source backend h r hr
  exact ⟨sourceVirtual_slackO1 P seeds q s sig starts hinj T point source backend h.1 h.2.1
      h.2.2.2 h.2.2.1 r hr,
    sourceReveals_sourceVirtual P seeds q s T point source backend h.2.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2.2 r hr⟩

theorem sourcePad_linked (point : Point) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (liftM (deferredQuery (C := C) (.pad point))) := by
  refine linked_of_signing P seeds q s sig starts _ (SourceKeeps.lift _) ?_
  intro source backend h r hr
  exact ⟨(SigningCompilerO1Release.sourcePad_slack P seeds q s sig starts point source backend
      h.2.1 r hr).1,
    sourceReveals_deferredQuery P seeds q s (.pad point) source backend h.2.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2.2 r hr⟩

theorem sourceHashProgram_linked {α : Type} (hinj : Function.Injective seeds)
    (oa : OracleComp HashSpec α) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceHashProgram P seeds oa) := by
  unfold sourceHashProgram deferredHash
  induction oa using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact SourcePreserves.pure value
  | query_bind input next ih =>
      simp only [simulateQ_bind, backendQuery, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact (sourceHash_linked P seeds q s sig starts hinj (.hash input)
        (fun _ _ he => by cases he)).bind _ ih

set_option backward.isDefEq.respectTransparency false in
theorem sourceBottomRow_linked (hinj : Function.Injective seeds) (e : KeyIndex) (l : ChainIndex) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceBottomRow P seeds e l) := by
  simp only [sourceBottomRow, deferredBottomRow, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_pure, backendQuery, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  refine (SourcePreserves.mapM _ _ (fun t ht => ?_)).bind _ fun _ => ?_
  · obtain ⟨pos, _, hm⟩ := List.mem_flatMap.mp ht
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hm
    exact (sourceVirtual_linked P seeds q s sig starts hinj T _).bind _
      (fun _ => SourcePreserves.pure ())
  · refine (sourcePad_linked P seeds q s sig starts _).bind _ fun first => ?_
    refine (sourcePad_linked P seeds q s sig starts _).bind _ fun second => ?_
    exact (SourcePreserves.mapM _ _
      (fun p _ => sourcePending_linked P seeds q s sig starts hinj p)).bind _
      (fun _ => SourcePreserves.pure _)

set_option backward.isDefEq.respectTransparency false in
theorem sourceTopEnd_linked (hinj : Function.Injective seeds) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (simulateQ (sourceBackend P seeds) (deferredTopEnd b l)) := by
  simp only [deferredTopEnd, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_pure, backendQuery, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, sourceBackend]
  refine (SourcePreserves.mapM _ _
    (fun T _ => sourceVirtual_linked P seeds q s sig starts hinj T _)).bind _ fun _ => ?_
  refine (sourcePending_linked P seeds q s sig starts hinj _).bind _ fun _ => ?_
  refine (sourcePending_linked P seeds q s sig starts hinj _).bind _ fun _ => ?_
  exact (sourcePending_linked P seeds q s sig starts hinj _).bind _
    (fun _ => SourcePreserves.pure _)

theorem sourceTopTree_linked (hinj : Function.Injective seeds) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts) (sourceTopTree P seeds) := by
  simp only [sourceTopTree, deferredTopTree, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  refine (SourcePreserves.mapM _ _
    (fun bl _ => sourceTopEnd_linked P seeds q s sig starts hinj bl.1 bl.2)).bind _ fun ends => ?_
  exact (sourceHashProgram_linked P seeds q s sig starts hinj _).bind _
    (fun _ => SourcePreserves.pure _)

theorem sourceCommitment_linked (hinj : Function.Injective seeds) (e : KeyIndex) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceCommitment P seeds e) := by
  unfold sourceCommitment
  refine (SourcePreserves.mapM _ _
    (fun T _ => sourceVirtual_linked P seeds q s sig starts hinj T _)).bind _ fun _ => ?_
  exact (sourcePending_linked P seeds q s sig starts hinj _).bind _
    (fun _ => SourcePreserves.pure _)

theorem sourceTopValue_linked (hinj : Function.Injective seeds) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (pos : Digit) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceTopValue P seeds b l pos) := by
  unfold sourceTopValue
  refine (SourcePreserves.mapM _ _
    (fun T _ => sourceVirtual_linked P seeds q s sig starts hinj T _)).bind _ fun _ => ?_
  exact (SourcePreserves.mapM _ _
    (fun _ _ => sourcePending_linked P seeds q s sig starts hinj _)).bind _
    (fun _ => SourcePreserves.pure _)

theorem sourceTopRecover_linked (hinj : Function.Injective seeds) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (pos : Digit) (initial : DeferredDigest) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceTopRecover P b l pos initial) := by
  unfold sourceTopRecover
  refine (SourcePreserves.mapM _ _
    (fun _ _ => sourcePending_linked P seeds q s sig starts hinj _)).bind _ fun values => ?_
  dsimp only
  split
  · exact SourcePreserves.pure _
  · exact (sourceModify_linked P seeds q s sig starts (fun st => { st with consistent := false })
      (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure _)

set_option backward.isDefEq.respectTransparency false in
theorem sourceBottomTree_linked (hinj : Function.Injective seeds) (top : TopTree)
    (b : XmssSecurity.TopIndex) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceBottomTree P seeds top b) := by
  unfold sourceBottomTree
  refine (SourcePreserves.mapM _ _
    (fun el _ => sourceBottomRow_linked P seeds q s sig starts hinj el.1 el.2)).bind _
    fun rows => ?_
  refine (SourcePreserves.mapM _ _
    (fun k _ => sourceCommitment_linked P seeds q s sig starts hinj (bottomKey b k))).bind _
    fun commitments => ?_
  refine (SourcePreserves.mapM _ _
    (fun T _ => sourceVirtual_linked P seeds q s sig starts hinj T _)).bind _ fun _ => ?_
  refine (sourceHashProgram_linked P seeds q s sig starts hinj _).bind _ fun root => ?_
  refine (sourcePending_linked P seeds q s sig starts hinj _).bind _ fun base => ?_
  refine (sourceHashProgram_linked P seeds q s sig starts hinj _).bind _ fun found => ?_
  cases found with
  | none => exact SourcePreserves.pure none
  | some answer =>
      rcases answer with ⟨randomness, encoding⟩
      refine (SourcePreserves.sequenceFin _ _
        (fun l => sourceTopValue_linked P seeds q s sig starts hinj b l (encoding l))).bind _
        fun values => ?_
      refine (sourceHashProgram_linked P seeds q s sig starts hinj _).bind _ fun path => ?_
      refine (sourceHashProgram_linked P seeds q s sig starts hinj _).bind _ fun digest => ?_
      cases hd : Codeword.decode digest with
      | none =>
          dsimp only
          exact SourcePreserves.pure none
      | some checked =>
          dsimp only
          split
          · exact (sourceModify_linked P seeds q s sig starts
              (fun st => { st with consistent := false })
              (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure none)
          · refine (SourcePreserves.sequenceFin _ _ (fun l => sourceTopRecover_linked
              P seeds q s sig starts hinj b l (encoding l) (values l))).bind _ fun ends => ?_
            refine (sourceHashProgram_linked P seeds q s sig starts hinj _).bind _ fun leaf => ?_
            refine (sourceHashProgram_linked P seeds q s sig starts hinj _).bind _ fun root => ?_
            split <;> exact SourcePreserves.pure _

theorem sourceBottomOnce_linked (hinj : Function.Injective seeds) (top : TopTree)
    (b : XmssSecurity.TopIndex) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceBottomOnce P seeds top b) := by
  unfold sourceBottomOnce
  refine SourcePreserves.get.bind _ fun source => ?_
  cases source.trees b with
  | some tree => exact SourcePreserves.pure tree
  | none =>
      refine (sourceBottomTree_linked P seeds q s sig starts hinj top b).bind _ fun tree => ?_
      exact (sourceModify_linked P seeds q s sig starts
        (fun st => { st with trees := Function.update st.trees b (some tree) })
        (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure tree)

end Steps

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceModify_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceModify_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceUniform_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceUniform_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceRawPending_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceRawPending_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceInspect_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceInspect_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceRecord_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceRecord_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourcePending_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourcePending_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceVirtual_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceVirtual_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourcePad_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourcePad_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceHashProgram_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceHashProgram_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceBottomRow_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceBottomRow_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopEnd_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopEnd_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopTree_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopTree_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceCommitment_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceCommitment_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopValue_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopValue_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopRecover_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceTopRecover_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceBottomTree_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceBottomTree_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceBottomOnce_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBuild.sourceBottomOnce_linked
