import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndTable

/-!
# The end of the hybrid of the hop on the used keys, the renaming of the world

`worldRenaming` proves `WorldRenaming`. A renaming of the hidden keys commutes with `lazyKeyWorld`
(`lazyKeyWorld_rename`). `hybridEnd_of_statements` proves `HybridEnd` from `EagerDraw`,
`KeyProvenance`, `KeyParametric` and `CellsCount`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The table of the AES keys with the key `σ k` in place of `k`. -/
def renameCache (σ : Equiv.Perm HashOutput) (c : KeyCache C) : KeyCache C :=
  QueryCache.ofFn fun x : KeyName C × HashOutput => c (x.1, σ x.2)

/-- The state of `lazyKeyWorld` with the renamed table. -/
def renameState (σ : Equiv.Perm HashOutput) (st : HashCache C × KeyCache C) : HashCache C × KeyCache C :=
  (st.1, renameCache σ st.2)

theorem renameCache_cacheQuery (σ : Equiv.Perm HashOutput) (c : KeyCache C) (n : KeyName C) (k : HashOutput)
    (v : Digest) : renameCache σ (c.cacheQuery (n, σ k) v) = (renameCache σ c).cacheQuery (n, k) v := by
  refine QueryCache.ext fun x => ?_
  by_cases hx : x = (n, k)
  · subst hx
    simp [renameCache]
  · have hne : (x.1, σ x.2) ≠ (n, σ k) := fun h =>
      hx (Prod.ext (Prod.mk.inj h).1 (σ.injective (Prod.mk.inj h).2))
    simp [renameCache, QueryCache.cacheQuery_of_ne _ _ hx, QueryCache.cacheQuery_of_ne _ _ hne]

/-- The lazy table at `(n, σ k)` is the renamed lazy table at `(n, k)`. -/
theorem randomOracle_rename (σ : Equiv.Perm HashOutput) (c : KeyCache C) (n : KeyName C) (k : HashOutput) :
    (fun r => (r.1, renameCache σ r.2)) <$> (((KeyName C × HashOutput) →ₒ Digest).randomOracle (n, σ k)).run c =
      (((KeyName C × HashOutput) →ₒ Digest).randomOracle (n, k)).run (renameCache σ c) := by
  cases hc : c (n, σ k) with
  | some v =>
    rw [QueryImpl.withCaching_run_some _ hc, QueryImpl.withCaching_run_some _ (show renameCache σ c (n, k) = some v from hc)]
    simp
  | none =>
    rw [QueryImpl.withCaching_run_none _ hc, QueryImpl.withCaching_run_none _ (show renameCache σ c (n, k) = none from hc)]
    simp only [Functor.map_map, renameCache_cacheQuery]
    rfl

/-- One step of `lazyKeyWorld` on a renamed call is the step on the call from the renamed state. -/
theorem lazyKeyWorld_rename_step (D : C.Coalition) (σ : Equiv.Perm HashOutput) (t : (WorldSpec C).Domain)
    (st : HashCache C × KeyCache C) :
    Prod.map id (renameState σ) <$> (simulateQ (lazyKeyWorld prims D) (renameImpl D σ t)).run st =
      (lazyKeyWorld prims D t).run (renameState σ st) := by
  rcases t with t | u | q | x
  · simp only [renameImpl, simulateQ_spec_query, lazyKeyWorld, StateT.run_mk, Functor.map_map, renameState]
    rfl
  · simp only [renameImpl, simulateQ_spec_query, lazyKeyWorld, StateT.run_mk, Functor.map_map, renameState]
    rfl
  · simp only [renameImpl, simulateQ_spec_query, lazyKeyWorld, StateT.run_mk, Functor.map_map, renameState]
    rfl
  · by_cases hh : Hidden D x.1
    · simp only [renameImpl, hh, ↓reduceIte, simulateQ_spec_query, lazyKeyWorld, StateT.run_mk, Functor.map_map,
        renameState]
      rw [← randomOracle_rename σ st.2 x.1 x.2.1]
      simp only [Functor.map_map]
      rfl
    · simp only [renameImpl, hh, ↓reduceIte, simulateQ_spec_query, lazyKeyWorld, StateT.run_mk, Functor.map_map,
        renameState]
      rfl

/-- A run of `lazyKeyWorld` on a renamed computation is the run on the computation from the renamed
state. -/
theorem lazyKeyWorld_rename (D : C.Coalition) (σ : Equiv.Perm HashOutput) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (st : HashCache C × KeyCache C) :
    Prod.map id (renameState σ) <$> (simulateQ (lazyKeyWorld prims D) (renameComp D σ oa)).run st =
      (simulateQ (lazyKeyWorld prims D) oa).run (renameState σ st) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp [renameComp]
  | query_bind t k ih =>
    have hrun : (simulateQ (lazyKeyWorld prims D) (renameComp D σ (liftM (OracleSpec.query t) >>= k))).run st =
        (simulateQ (lazyKeyWorld prims D) (renameImpl D σ t)).run st >>= fun p =>
          (simulateQ (lazyKeyWorld prims D) (renameComp D σ (k p.1))).run p.2 := by
      simp only [renameComp, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        StateT.run_bind]
    rw [hrun, map_bind]
    simp only [ih]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, ← lazyKeyWorld_rename_step prims D σ t st, bind_map_left, Prod.map, id_eq]

/-- The second part of the research step. -/
theorem worldRenaming : WorldRenaming (C := C) prims := by
  intro D σ α oa
  have hproj : ∀ game : OracleComp (WorldSpec C) α,
      (fun r => (r.1, r.2.hash)) <$> (simulateQ (jointKeyWorld prims D false) game).run keyJointInitial =ᵈ
        (fun r => (r.1, r.2.1)) <$> (simulateQ (lazyKeyWorld prims D) game).run (∅, ∅) := by
    intro game
    have h := (evalDist_simulateQ_state_projection (jointKeyWorld prims D false) (lazyKeyWorld prims D)
      keyJointIdealProjection (jointKeyWorld_false_query_projection prims D) game (keyJointInitial (C := C))).map
        fun r : α × HashCache C × KeyCache C => (r.1, r.2.1)
    have he : keyJointIdealProjection (keyJointInitial (C := C)) = (∅, ∅) := rfl
    rw [he] at h
    simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq, keyJointIdealProjection] using h
  refine (hproj (renameComp D σ oa)).trans (EvalDistEq.trans ?_ (hproj oa).symm)
  have h := congrArg (fun m => (fun r : α × HashCache C × KeyCache C => (r.1, r.2.1)) <$> m)
    (lazyKeyWorld_rename prims D σ oa (∅, ∅))
  have he : renameState σ ((∅, ∅) : HashCache C × KeyCache C) = (∅, ∅) :=
    Prod.ext rfl (QueryCache.ext fun _ => rfl)
  simp only [Functor.map_map, he] at h
  rw [← h]
  exact EvalDistEq.rfl

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- `HybridEnd` from `EagerDraw`, `KeyProvenance`, `KeyParametric` and `CellsCount`, with
`worldRenaming`. -/
theorem hybridEnd_of_statements (eager : EagerDraw K circuits settings runLimit prims)
    (prov : KeyProvenance K circuits settings runLimit prims)
    (param : KeyParametric K circuits settings runLimit)
    (count : CellsCount K circuits settings runLimit prims) :
    HybridEnd K circuits settings runLimit prims :=
  hybridEnd_of_parts K circuits settings runLimit prims eager prov param (worldRenaming prims) count

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.worldRenaming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.worldRenaming

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.hybridEnd_of_statements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.hybridEnd_of_statements
