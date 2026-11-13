import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackSteps
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackRun

/-! # Reads of the base source that keep the linked invariant

A permitted hash call keeps `LinkedInvariant`. An honest PRF evaluation at one readable point keeps
`ReadInvariantO1`. The part of a signer at a recorded chain point of its key keeps
`LinkedInvariant`, because the signer reads only the seeds of its held terms, and its mask queries
are no PRF queries. Typed hashes and the codeword search keep `LinkedInvariant`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackSteps
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Steps
variable (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
  (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)

/-- A permitted hash call keeps the linked invariant. -/
theorem sourceHash_allowed (hinj : Function.Injective seeds) (query : Query C)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : LinkedInvariant seeds s sig starts source backend)
    (ha : ReadAllowedO1 seeds sig starts backend.1.1.data query)
    (r : (HashOutput × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceHash P seeds query) source backend)) :
    LinkedInvariant seeds s sig starts r.1.2 r.2 := by
  have control := (sourceControl_sourceHash P seeds query).run P seeds q s source backend r hr
  have hsign : r.1.2.signing = source.signing := congrArg Prod.fst control
  refine ⟨hsign ▸ h.1, ?_, ?_, ?_⟩
  · exact sourceHash_slackO1 P seeds q s sig starts hinj query source backend h.1 h.2.1 ha
      h.2.2.2 h.2.2.1 r hr
  · exact sourceReveals_sourceHash P seeds q s query source backend h.2.2.1 r hr
  · exact runSource_pendingValid P seeds q s (sourceHash P seeds query) source backend
      h.2.2.2 r hr

theorem sourceHash_linked (hinj : Function.Injective seeds) (query : Query C)
    (hquery : ∀ seed point, query ≠ .prf seed point) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts) (sourceHash P seeds query) :=
  fun source backend h r hr => sourceHash_allowed P seeds q s sig starts hinj query source
    backend h (fun T p he => (hquery (seeds T) p he).elim) r hr

theorem sourceHash_readO1 (hinj : Function.Injective seeds) (point : Point) (query : Query C)
    (hquery : ∀ seed p, query = .prf seed p → p = point) :
    SourcePreserves P seeds q s (ReadInvariantO1 seeds s sig starts point)
      (sourceHash P seeds query) := by
  intro source backend h r hr
  have control := (sourceControl_sourceHash P seeds query).run P seeds q s source backend r hr
  exact ⟨sourceHash_allowed P seeds q s sig starts hinj query source backend h.1
      (PointReadable.allowedO1 h.2 h.1.1 query hquery) r hr,
    h.2.mono (congrArg Prod.fst control)
      (runSource_cache_le P seeds q s (sourceHash P seeds query) source backend r hr)⟩

set_option backward.isDefEq.respectTransparency false in
theorem sourcePrfValue_readO1 (prims : Primitives) (hinj : Function.Injective seeds)
    (point : Point) :
    SourcePreserves P seeds q s (ReadInvariantO1 seeds s sig starts point)
      (sourceRoProgram prims P seeds (prfValue seeds point)) := by
  simp only [sourceRoProgram, prfValue, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  refine (SourcePreserves.mapM _ _ (fun T _ => ?_)).bind _ (fun _ => SourcePreserves.pure _)
  simp only [prf, hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
  exact (sourceHash_readO1 P seeds q s sig starts hinj point (.prf (seeds T) point)
    (fun seed p he => (Query.prf.inj he).2.symm)).map truncateHash

set_option backward.isDefEq.respectTransparency false in
theorem sourceEval_readO1 (prims : Primitives) (hinj : Function.Injective seeds)
    (keys : Keys C) (i : C.Party) (J : C.Quorum) (point : Point) (message : Message) :
    SourcePreserves P seeds q s (ReadInvariantO1 seeds s sig starts point)
      (sourceRoProgram prims P seeds (eval keys i J point message)) := by
  simp only [sourceRoProgram, eval, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  refine (SourcePreserves.mapM _ _ (fun T _ => ?_)).bind _ fun terms => ?_
  · simp only [prf, hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
    exact (sourceHash_readO1 P seeds q s sig starts hinj point (.prf (keys.seed T) point)
      (fun seed p he => (Query.prf.inj he).2.symm)).map truncateHash
  · refine (SourcePreserves.mapM _ _ (fun j _ => ?_)).bind _ (fun _ => SourcePreserves.pure _)
    simp only [hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
    exact (sourceHash_readO1 P seeds q s sig starts hinj point
      (.mask (keys.pairKey j) point message J) (fun seed p he => by cases he)).map truncateHash

theorem sourceTweakable_linked {α : Type} (prims : Primitives) (hinj : Function.Injective seeds)
    (oa : OracleComp HashSpec α) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceRoProgram prims P seeds (tweakable oa)) := by
  unfold sourceRoProgram tweakable
  induction oa using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact SourcePreserves.pure value
  | query_bind input next ih =>
      simp only [simulateQ_bind, hashQuery, HasQuery.instOfMonadLift_query,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact (sourceHash_linked P seeds q s sig starts hinj (.hash input)
        (fun _ _ he => by cases he)).bind _ ih

theorem sourceCodeword_linked (prims : Primitives) (hinj : Function.Injective seeds)
    (commitment : Digest) (e : KeyIndex) (message : Message) (opening : Digest) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceRoProgram prims P seeds (signCodeword P commitment e message opening)) :=
  sourceTweakable_linked P seeds q s sig starts prims hinj _

end Steps

section BaseHandlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)

theorem sourcePart_readO1 (hinj : Function.Injective x.2.1) (i : C.Party) (J : C.Quorum)
    (point : Point) (message : Message) :
    SourcePreserves x.1 x.2.1 q s (ReadInvariantO1 x.2.1 s sig starts point)
      (sourcePart prims x i J point message) :=
  sourceEval_readO1 x.1 x.2.1 q s sig starts prims hinj _ i J point message

set_option backward.isDefEq.respectTransparency false in
/-- The part of a signer at a recorded chain point of its key keeps the invariant. The signer reads
only its held terms. -/
theorem sourcePart_held (hinj : Function.Injective x.2.1) (i : C.Party) (J : C.Quorum)
    (point : Point) (message : Message) (hheld : HeldReadable sig starts i point) :
    SourcePreserves x.1 x.2.1 q s (LinkedInvariant x.2.1 s sig starts)
      (sourcePart prims x i J point message) := by
  simp only [sourcePart, sourceRoProgram, eval, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_pure]
  refine (SourcePreserves.mapM _ _ (fun T hT => ?_)).bind _ fun terms => ?_
  · have hholder : i ∈ C.holders T :=
      TprfCorrectnessProof.mem_holders_of_mem_L (of_decide_eq_true (List.mem_filter.mp hT).2)
    have hseed : (dealtKeys x.1 x.2.1 x.2.2 i).seed T = x.2.1 T := by
      simp [dealtKeys, hholder]
    simp only [prf, hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo, hseed]
    refine SourcePreserves.map (fun source backend h r hr => ?_) truncateHash
    exact sourceHash_allowed x.1 x.2.1 q s sig starts hinj _ source backend h
      (HeldReadable.allowed hinj hheld T hholder) r hr
  · refine (SourcePreserves.mapM _ _ (fun j _ => ?_)).bind _ (fun _ => SourcePreserves.pure _)
    simp only [hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
    exact (sourceHash_linked x.1 x.2.1 q s sig starts hinj _
      (fun seed p he => by cases he)).map truncateHash

end BaseHandlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceHash_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceHash_allowed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceHash_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceHash_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceHash_readO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceHash_readO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourcePrfValue_readO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourcePrfValue_readO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceEval_readO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceEval_readO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceTweakable_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceTweakable_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceCodeword_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourceCodeword_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourcePart_readO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourcePart_readO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourcePart_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRead.sourcePart_held
