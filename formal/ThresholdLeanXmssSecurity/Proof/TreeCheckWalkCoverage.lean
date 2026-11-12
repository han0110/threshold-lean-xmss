import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkRecipe

/-!
# Coverage clauses of the fixed source walk

This file concerns `WalkBad` of the fixed family `family` of
`TreeCheckWalkRecipe`. The family, its decoder and its witness are not changed.

## Lemmas

* `walkJobs` gives the `Jobs` clause from `WalkOpening` and `WalkUnreached` of
  the same family. The indexed record of a bad continuation is at index `j` of
  an honest record list. Records that follow a common encoding put chunk `j` of
  that encoding at this index. The opening clause gives these jobs to the
  selected batch. `jobs_of_indexed` is the same step for any walk.
* `walkBad_of_parts` gives `WalkBad` from `WalkOpening`, `WalkUnreached` and
  `WalkConsistent`. These two Props are the `Unreached` and `Consistent`
  clauses of the same fixed family.
* `openResume_tail` writes the resumed `openRep` of `treeSimOpenStep` as the
  rejecting local tail `openTail`, followed by the value
  `∑ T, treeSimOpenCopy … T g`.
* `signingMatches_rejected` shows that `SigningMatches` does not fix the
  outputs of a party whose tail is `pure none`.
  `signingHead_rejected` shows that the gate of such a party has no value.

## Mid-batch recognition

The cut of a batch `j` that is not the first batch of its phase is in the local
pass after the `openRep` exchange of batch `j - 1`. By `openResume_tail` the
received mail and the own shares fix the opened value. The pending digest
queries change only the rejection. So the output `assemble jobs opened` of
batch `j - 1` and its record are fixed before the local pass starts.

A caller for this cut holds the earlier outputs, the `j` earlier records and
`tail i = openTail …`. The second phase also holds the fixed choice. A hit at
this cut also needs these facts, which this file does not give.

* Each honest program at that walk state equals the caller program. This needs
  the reassociation of `mapM` and of the writer, as in `auditChunks_cons`.
  `segments_reach` gives only the exchange counts.
* The actual counters after batch `j - 1` equal `(lockstepStart … j, j)` of
  `callerBatch`. `treeLockstepRecords_audit` gives the start labels only on
  complete runs.

## The chosen signing point

`prepare` takes a point by `Classical.choose`. By `resume`, an aborted party
has the stored program `failure`. An adversary can send an abort frame to one
honest party in the last opening of the first phase. Then the tail of that
party is `pure none` in a matching point. By `signingMatches_rejected`, a
point with other outputs at that party also matches. So the `common`
premise of `source_signing_decode_hit` does not follow for every matching
point. In this example an honest party stops, so the honest parties stop at
the next exchange (`treeSimCheck_exchange_round_abort`).

For every matching point a hit can go through `selected_signing_decode_hit`.
Its `fixed` premise is per party. It holds for a rejecting party by
`signingHead_rejected`. For a live honest party, `fixed` must come from the
program equality of `SigningMatches` and from the agreement of the live honest
outputs.

The agreement of the outputs has two sources.

* A term that an honest party does not hold has an honest holder that is not
  its owner, because each term has `t` holders and at most `t - 1` operators
  are corrupt. The `.copy` comparison then rejects a wrong owner copy, except
  for a `.copy` collision. `TreeSimHashDomain` holds `.copy`.
* If the coalition has `t - 1` operators, then every honest party holds the
  term `D`, and no `.copy` comparison covers it. The agreement on its shares
  must come from the check of the batch.

A live party with a wrong copy whose `.copy` query is not in the cache can
accept only in a collision branch. In that branch `fixed` can fail, so the
decoder can miss that state. A proof of `Unreached` thus starts from the
counted bad result and not from a hit at every boundary state.
`treeLockstepEncoding` gives the encoding agreement on reachable
configurations of `TreeStagesReach`, also on aborted prefixes.

## Consistency

`WalkConsistent` is the third clause of `TupleInputs` at each live checkpoint
of the walk. It concerns the layers of the actual prefix of the selected
batch, and it does not use the coverage of the walk.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkCoverage

open TreeCheckWalkRecipe

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

section OpenTail

/-- The local work of `openRep` after its exchange. It queries the digests of
the copies and returns only the result of the comparison. -/
def openTail (i : C.Party) (count : ℕ) (v : Shares C Bit) (inbox : Mail C E) :
    OracleComp (LocalSpec C) (Option Unit) := do
  let copyDigests ← liftComp (treeSimOpenCopyHashes count (treeSimOpenCopy K i count v inbox))
    (LocalSpec C)
  pure (if TreeSimOpenValid K i inbox copyDigests then some () else none)

omit [Fintype E] [DecidableEq E] in
/-- The resumed `openRep` of `treeSimOpenStep` is a rejecting local tail
followed by a fixed value. The opened value is the sum of the copies, so the
received mail and the own shares fix it before the digest queries run. -/
theorem openResume_tail {α : Type} (i : C.Party) (count : ℕ) (v : Shares C Bit)
    (inbox : Mail C E) (k : (ℕ → Bit) → PartyM C E RealSpec α) :
    (do
      let copy := treeSimOpenCopy K i count v inbox
      let copyDigests ← oracleStep (treeSimOpenCopyHashes count copy)
      require (TreeSimOpenValid K i inbox copyDigests)
      k (fun g => ∑ T, copy T g)) =
    (treeLockstepLocalPrelude (openTail K i count v inbox) >>= fun _ =>
      k (fun g => ∑ T, treeSimOpenCopy K i count v inbox T g)) := by
  apply OptionT.ext
  simp only [treeLockstepLocalPrelude, openTail, oracleStep, localStep, require, OptionT.run_bind,
    OptionT.lift, OptionT.run_mk, liftComp_bind, bind_assoc, pure_bind, Option.elimM]
  apply bind_congr
  intro copyDigests
  simp only [Option.elim_some]
  by_cases valid : TreeSimOpenValid K i inbox copyDigests
  · rw [if_pos valid, if_pos valid]
    simp
  · rw [if_neg valid, if_neg valid]
    simp

end OpenTail

section SigningPoints

variable (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (top : TopTree) (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (j : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- `SigningMatches` does not fix the outputs of a party whose tail always
rejects. Any other outputs at that party give a matching point too, so the
point that `prepare` chooses can differ from the other honest outputs there. -/
theorem signingMatches_rejected (b : Fin (2 ^ layerHeight)) (p : TreeCheckWalkDef.Pending A)
    (point : SigningPoint C)
    (matching : SigningMatches K D A circuits settings top x setup j b p point)
    (i : C.Party) (rejects : point.tail i = pure none) (outputs : List (List Bit)) :
    SigningMatches K D A circuits settings top x setup j b p
      { point with outputs := Function.update point.outputs i outputs } := by
  refine ⟨matching.1, fun k hk => ?_⟩
  rw [matching.2 k hk]
  by_cases same : k = i
  · subst same
    simp only [rejects, localPrelude_none, failure_bind]
  · simp only [Function.update_of_ne same]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A rejecting tail gives a gate with no successful value, for all outputs. -/
theorem signingHead_rejected (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) :
    signingHead (C := C) parameter b outputs (pure none) = pure none := by
  simp [signingHead]

end SigningPoints

/-- The `Unreached` clause of `WalkBad`, for the fixed family. -/
def WalkUnreached : Prop :=
  AtWalk prims K circuits settings fun top tree D _ x z _ _ _ j _ W =>
    W.Unreached prims K circuits settings D top tree x z j

/-- The `Consistent` clause of `WalkBad`, for the fixed family. -/
def WalkConsistent : Prop :=
  AtWalk prims K circuits settings fun top tree D _ x z Z _ _ j _ W =>
    W.Consistent prims K circuits settings D top tree x z Z j

/-- The `Jobs` clause of `WalkBad`, for the fixed family. -/
def WalkJobs : Prop :=
  AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j

set_option linter.constructorNameAsVariable false in
/-- The indexed record of a bad continuation is at index `j` of an honest
record list. The records of a common encoding put the jobs of chunk `j` at
this index, and the opening clause gives these jobs to the selected batch.
A finished branch has no counted bad result. -/
theorem jobs_of_indexed {top : TopTree} {tree : Tree} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckTailWalk A}
    (parameter : ∀ c i, ((W.boundary c).batch.ctx i).keys.parameter = (W.boundary c).batch.parameter)
    (indexed : W.IndexedOpening prims K circuits settings top tree D A x z Z j)
    (finished : W.Unreached prims K circuits settings D top tree x z j) :
    (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j := by
  rintro (⟨c, o⟩ | r') hs r hr bad counted common enc follows i hi
  · obtain ⟨record, keys, jobs, -, -, -⟩ := indexed c o hs r hr bad counted
    obtain ⟨-, atIndex⟩ := follows record.party record.honest record.output record.records record.result
    obtain ⟨below, entry⟩ := List.getElem?_eq_some_iff.mp record.indexed
    have chunk := (atIndex j.val below).1
    rw [entry] at chunk
    have sameParameter : (x i).parameter = (W.boundary c).batch.parameter := by
      rw [← keys i hi]
      exact parameter c i
    change tupleCount (((lockstepChunks settings enc tree).getD j.val []).map
        (circuits (x i).parameter ·.kind)) =
      tupleCount ((W.boundary c).batch.jobs.map (circuits (W.boundary c).batch.parameter ·.kind))
    rw [← chunk, ← jobs, sameParameter]
  · have same : r = r' := by
      simpa only [TreeCheckTailWalk.cut, support_pure, Set.mem_singleton_iff] using hr
    subst same
    exact absurd ⟨bad, counted⟩ (finished r (TreeCheckTailWalk.mem_support_cut_pre_inr hs))

set_option maxRecDepth 2000 in
/-- `Jobs` for the fixed family, from the opening clause and `Unreached` of
the same family. -/
theorem walkJobs (opening : WalkOpening prims K circuits settings)
    (unreached : WalkUnreached prims K circuits settings) :
    WalkJobs prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨⟨-, parameter⟩, -, -⟩ :=
    walkSplit prims K circuits settings hb top tree D A x z Z q dealt bounded small j p hp
  have indexed := opening hb top tree D A x z Z q dealt bounded small j p hp
  have finished := unreached hb top tree D A x z Z q dealt bounded small j p hp
  with_reducible exact jobs_of_indexed prims K circuits settings parameter indexed finished

/-- `WalkBad` for the fixed family follows from the opening clause and the two
remaining clauses of the same family. -/
theorem walkBad_of_parts (opening : WalkOpening prims K circuits settings)
    (unreached : WalkUnreached prims K circuits settings)
    (consistent : WalkConsistent prims K circuits settings) :
    WalkBad prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  exact ⟨walkJobs prims K circuits settings opening unreached hb top tree D A x z Z q dealt bounded small j p hp,
    unreached hb top tree D A x z Z q dealt bounded small j p hp,
    consistent hb top tree D A x z Z q dealt bounded small j p hp⟩

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoverage.openResume_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms openResume_tail

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoverage.signingMatches_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingMatches_rejected

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoverage.signingHead_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingHead_rejected

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoverage.jobs_of_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jobs_of_indexed

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoverage.walkJobs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkJobs

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoverage.walkBad_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkBad_of_parts

end TreeCheckWalkCoverage
end ThresholdLeanXmssSecurity
