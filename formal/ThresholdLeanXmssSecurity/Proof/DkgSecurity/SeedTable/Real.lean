import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.General
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.SetupEmulation

/-!
# The real end of the seed generation claim

`seedRealGeneral` proves `SeedRealGeneral`. The real seed generation with `tableNet` is the real
seed generation with `net`, with the table merged into the cache (`realExecution_coupling`). A rest
with no programming query on `tableWorld`, run on the counted copy of the world, is the same rest in
`streamWorld` on the merged cache (`rest_split`). The read of the rest gives the blind view, which
is the same on the table and on the merged cache.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

open SeedPartition SeedEmulation
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.Partitioned (isPrivate)

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## A run along a map of states -/

/-- A map of states that each allowed query respects is respected by each program with only
allowed queries. -/
theorem run_simulateQ_stateMap {ι : Type} {spec : OracleSpec ι} {σ τ : Type}
    (impl₁ : QueryImpl spec (StateT σ ProbComp)) (impl₂ : QueryImpl spec (StateT τ ProbComp)) (f : σ → τ)
    (P : ι → Prop) (h : ∀ t, P t → ∀ s, (impl₂ t).run (f s) = (fun z => (z.1, f z.2)) <$> (impl₁ t).run s)
    {α : Type} (oa : OracleComp spec α) (hoa : AllQueriesSatisfy oa P) (s : σ) :
    (simulateQ impl₂ oa).run (f s) = (fun z => (z.1, f z.2)) <$> (simulateQ impl₁ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self]
    rw [h t hoa.1 s, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ (hoa.2 _) z.2

/-! ## One local call with the private table -/

/-- One local call on the merged cache is the call under the private table over the local oracles
on the outer cache. -/
theorem local_coupling (Q : Query C → Bool) (prims : Primitives) (u : (LocalSpec C).Domain) (S T : HashCache C) :
    (localAnswer prims u).run (merge Q S T) =
      (fun z => (z.1.1, merge Q z.2 z.1.2)) <$> (simulateQ (localAnswer prims) ((Partitioned.tableLocal Q prims u).run T)).run S := by
  by_cases hu : isPrivate Q u = true
  · have e : (Partitioned.tableLocal Q prims u).run T = liftComp ((localAnswer prims u).run T) (LocalSpec C) := by
      simp [Partitioned.tableLocal, hu]
    rw [e, simulateQ_local_sample_seedGensecurity, StateT.run_lift, localAnswer_right Q prims u hu S T, map_bind]
    simp only [pure_bind, map_eq_bind_pure_comp]
    rfl
  · have hf : isPrivate Q u = false := by simpa using hu
    have e : (Partitioned.tableLocal Q prims u).run T =
        OracleComp.lift (OracleSpec.query (spec := LocalSpec C) u) >>= fun a => pure (a, T) := by
      simp only [Partitioned.tableLocal, hf, Bool.false_eq_true, ite_false]
      rw [StateT.run_monadLift, monadLift_self]
    rw [e, simulateQ_bind, StateT.run_bind, simulateQ_spec_query, localAnswer_left Q prims u hf S T]
    simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

/-! ## The rest on the private table -/

/-- The blind view does not see the class cells. -/
theorem blind_merge (S T : HashCache C) (H : HiddenCache C) :
    blind (merge seedGenOutside S T, H) = blind (T, H) := by
  refine Prod.ext ?_ rfl
  refine QueryCache.ext fun q => ?_
  by_cases hq : isSeedGenQuery q = true
  · simp [blind, eraseSeedGen, hq]
  · simp [blind, eraseSeedGen, merge, seedGenOutside, hq]

/-- The handler of a rest on the private table over the local oracles of the world. -/
abbrev tableRun (prims : Primitives) (D : C.Coalition) :
    QueryImpl (PeekSpec C) (StateT (StreamState C × HashCache C) ProbComp) :=
  fuse (withPeek (tableWorld prims D) id) (localAnswer prims)

/-- The merged state of a rest on the private table. -/
def mergedState (w : StreamState C × HashCache C) : StreamState C := (merge seedGenOutside w.2 w.1.1, w.1.2)

theorem local_step (prims : Primitives) (u : (LocalSpec C).Domain) (S T : HashCache C) (H : HiddenCache C) :
    (onHash (localAnswer prims u)).run (merge seedGenOutside S T, H) =
      (fun z => (z.1, merge seedGenOutside z.2.2 z.2.1.1, z.2.1.2)) <$> (fun r => (r.1.1, r.1.2, r.2)) <$>
        (simulateQ (localAnswer prims)
          ((fun r => (r.1, r.2, H)) <$> (Partitioned.tableLocal seedGenOutside prims u).run T)).run S := by
  simp only [onHash, StateT.run_mk, local_coupling, simulateQ_map, StateT.run_map, Functor.map_map]

theorem tableRun_step (prims : Primitives) (D : C.Coalition) (t : (PeekSpec C).Domain) (ht : ¬ PeekProgramQuery t)
    (w : StreamState C × HashCache C) :
    (withPeek (streamWorld prims D) id t).run (mergedState w) =
      (fun z => (z.1, mergedState z.2)) <$> (tableRun prims D t).run w := by
  obtain ⟨⟨T, H⟩, S⟩ := w
  rcases t with ((((n | q | x) | p) | (n | q | x)) | u)
  all_goals simp only [withPeek, tableRun, fuse, tableWorld, streamWorld, mergedState, StateT.run_mk,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, tableLocal_eq]
  · exact local_step prims (.inl n) S T H
  · exact local_step prims (.inr (.inl q)) S T H
  · exact local_step prims (.inr (.inr x)) S T H
  · exact (ht trivial).elim
  · exact local_step prims (.inl n) S T H
  · exact local_step prims (.inr (.inl q)) S T H
  · split_ifs with hx
    · simp only [StateT.run_mk, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, simulateQ_local_sample_seedGensecurity, StateT.run_lift, bind_assoc, pure_bind,
        Function.comp_def]
    · simp only [StateT.run_mk]
      exact local_step prims (.inr (.inr x)) S T H
  · simp [blind_merge]

/-- A rest with no programming query on the private table, run on the counted copy of the world, is
the same rest in `streamWorld` on the merged cache. -/
theorem rest_split (prims : Primitives) (D : C.Coalition) {β : Type} (rest : OracleComp (PeekSpec C) β)
    (hrest : AllQueriesSatisfy rest fun t => ¬ PeekProgramQuery t) (S T : HashCache C) (H : HiddenCache C) :
    (simulateQ (withPeek (streamWorld prims D) id) rest).run (merge seedGenOutside S T, H) =
      (fun z => (z.1.1, (merge seedGenOutside z.2 z.1.2.1, z.1.2.2))) <$>
        (simulateQ (worldAnswer prims) (worldRoles.adversary
          ((simulateQ (withPeek (tableWorld prims D) id) rest).run (T, H)))).run S := by
  rw [SeedHitProof.simulateQ_adversary_split]
  have e : ((fun t => worldAnswer prims (.inl (.inl t))) : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp)) =
      localAnswer prims := rfl
  rw [e, run_simulateQ_fuse, Functor.map_map]
  exact run_simulateQ_stateMap (tableRun prims D) _ mergedState _ (tableRun_step prims D) rest hrest ((T, H), S)

/-! ## The real end -/

theorem seedRealGeneral (prims : Primitives) [Field E] [Algebra Bit E] : SeedRealGeneral (C := C) (E := E) prims := by
  intro D net β rest hrest
  have hR := realExecution_coupling prims D net [] ∅ ∅
  rw [merge_empty] at hR
  rw [hR, bind_map_left]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [rest_split prims D _ (hrest _ _), Functor.map_map, adversary_map, simulateQ_map, StateT.run_map]
  exact fun _ => rfl

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.seedRealGeneral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.seedRealGeneral
