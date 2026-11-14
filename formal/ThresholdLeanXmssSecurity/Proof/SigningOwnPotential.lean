import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SeedHit

/-!
# The completion potential at an honest block

The completion potential of a recorded completion does not rise in expectation at a call that each
completion takes as its own target, nor in a block of calls that the completion covers. The block
can run on the free copy of the logged signing world.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SigningOwnPotential

open SigningHitProof SigningHitLaneProof SigningCostProof

variable {C : Committee} (prims : Primitives)

open Classical in
/-- The completion potential does not rise at a call that each completion takes as
its own target. The step `completionPotential_randomOracle_step` charges each relevant
input. -/
theorem completionPotential_covered_step (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C)) (input : Query C)
    (cache : HashCache C)
    (hcovered : ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle completion).run cache),
      relevant input → (z.1 input).1 = input) :
    (∑' r, Pr{let z ← ((Query C →ₒ HashOutput).randomOracle input).run cache}[z = r] *
      completionPotential relevant completion r.2) ≤ completionPotential relevant completion cache := by
  classical
  cases hcache : cache input with
  | some output =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hcache, OracleComp.tsum_prEvent_pure_mul]
  | none =>
  let Q := (Query C →ₒ HashOutput).randomOracle input
  let F := simulateQ (Query C →ₒ HashOutput).randomOracle completion
  let event : (HashOutput × CompletionTargets C) × HashCache C → Prop :=
    fun z => CompletedHit relevant z.1.2 (cache.cacheQuery input z.1.1)
  have hcomm : Commutes Q F := by
    simpa [Q, F] using commutes_simulateQ (Query C →ₒ HashOutput).randomOracle
      commutes_randomOracle_randomOracle
      (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input)) completion
  have hforward : (∑' r, Pr{let z ← Q.run cache}[z = r] * completionPotential relevant completion r.2) =
      Pr{let z ← (do let u ← Q; let targets ← F; pure (u, targets)).run cache}[event z] := by
    simp only [StateT.run_bind, bind_pure_comp, OracleComp.prEvent_bind_eq_tsum]
    apply tsum_congr
    intro r
    by_cases hr : r ∈ support (Q.run cache)
    · have hc := randomOracle_result_cache input cache r hr
      simp only [completionPotential, F, event, hc, StateT.run_map, prEvent_map, Function.comp_def]
    · simp [prEvent_eq_zero_of_not_mem_support _ hr]
  change (∑' r, Pr{let z ← Q.run cache}[z = r] * completionPotential relevant completion r.2) ≤ _
  rw [hforward, (hcomm cache).prEvent_eq _]
  simp only [StateT.run_bind, bind_pure_comp, OracleComp.prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' r, Pr{let z ← F.run cache}[z = r] * (if CompletedHit relevant r.1 cache then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro r
      by_cases hr : r ∈ support (F.run cache)
      · refine mul_le_mul_right ?_ _
        simp only [StateT.run_map, prEvent_map]
        change Pr{let z ← Q.run r.2}[CompletedHit relevant r.1 (cache.cacheQuery input z.1)] ≤ _
        by_cases hbad : CompletedHit relevant r.1 cache
        · rw [if_pos hbad]
          exact (prEvent_le_one _)
        · rw [if_neg hbad]
          calc
            _ ≤ Pr{let _ ← Q.run r.2}[False] := by
              apply prEvent_mono_of_support _ _ _
              intro z _ hh
              obtain ⟨hrel, hne, _⟩ := completedHit_cacheQuery relevant r.1 cache input z.1 hbad hh
              exact hne (hcovered r hr hrel).symm
            _ = 0 := by simp
      · simp [prEvent_eq_zero_of_not_mem_support _ hr]
    _ = completionPotential relevant completion cache := by
      simp only [completionPotential, F, mul_ite, mul_one, mul_zero]
      exact (OracleComp.prEvent_eq_tsum_ite _ _).symm

open Classical in
/-- The completion potential does not rise in a block of calls, if
each relevant input that the block reads after a completion is a read of that completion or is in
the cache at the start. The premise reads the block only from a completed cache. -/
theorem completionPotential_recorded_block_le {α β : Type} (relevant : Query C → Prop)
    (oa : OracleComp (Query C →ₒ HashOutput) α) (target : α → HashCache C → CompletionTargets C)
    (block : OracleComp (Query C →ₒ HashOutput) β) (cache : HashCache C)
    (hcovered : ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (recordReads oa ∅)).run cache),
      ∀ w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle (recordReads block ∅)).run z.2),
      ∀ input, relevant input → (w.1.2 input).isSome → (z.1.2 input).isSome ∨ (cache input).isSome) :
    (∑' w, Pr{let z ← (simulateQ (Query C →ₒ HashOutput).randomOracle (recordReads block ∅)).run cache}[z = w] *
      completionPotential relevant (recordedCompletion oa target) w.2) ≤
        completionPotential relevant (recordedCompletion oa target) cache := by
  classical
  let B := simulateQ (Query C →ₒ HashOutput).randomOracle (recordReads block ∅)
  let F := simulateQ (Query C →ₒ HashOutput).randomOracle (recordReads oa ∅)
  let T : α × HashCache C → CompletionTargets C := fun r => recordedTargets (target r.1 r.2) r.2
  let merged : HashCache C → HashCache C := fun record => QueryCache.ofFn fun input =>
    match record input with
    | some value => some value
    | none => cache input
  have hpot : ∀ c, completionPotential relevant (recordedCompletion oa target) c =
      Pr{let z ← F.run c}[CompletedHit relevant (T z.1) c] := by
    intro c
    simp only [completionPotential, recordedCompletion, simulateQ_map, StateT.run_map, prEvent_map,
      Function.comp_def, F, T]
  have hcomm : Commutes B F := by
    simpa [B, F] using commutes_simulateQ (Query C →ₒ HashOutput).randomOracle
      commutes_randomOracle_randomOracle (recordReads block ∅) (recordReads oa ∅)
  let event : ((β × HashCache C) × (α × HashCache C)) × HashCache C → Prop :=
    fun z => CompletedHit relevant (T z.1.2) (merged z.1.1.2)
  have hforward : (∑' w, Pr{let z ← B.run cache}[z = w] *
        completionPotential relevant (recordedCompletion oa target) w.2) =
      Pr{let z ← (do let u ← B; let v ← F; pure (u, v)).run cache}[event z] := by
    simp only [StateT.run_bind, bind_pure_comp, OracleComp.prEvent_bind_eq_tsum]
    apply tsum_congr
    intro w
    by_cases hw : w ∈ support (B.run cache)
    · have hc : w.2 = merged w.1.2 := by
        refine QueryCache.ext fun input => ?_
        cases hi : w.1.2 input with
        | none =>
            simpa only [merged, QueryCache.ofFn_apply, hi] using recordReads_preserves_unrecorded block cache ∅ cache
              (fun _ _ => rfl) w hw input hi
        | some value =>
            have hrecord := (recordReads_resolves block ∅ cache
              (by intro i v h; cases h) w hw).2.2.1
            simpa only [merged, QueryCache.ofFn_apply, hi] using hrecord hi
      simp only [hpot, event, hc, StateT.run_map, prEvent_map, Function.comp_def]
    · simp [prEvent_eq_zero_of_not_mem_support _ hw]
  change (∑' w, Pr{let z ← B.run cache}[z = w] *
    completionPotential relevant (recordedCompletion oa target) w.2) ≤ _
  rw [hforward, (hcomm cache).prEvent_eq _, hpot cache]
  simp only [StateT.run_bind, bind_pure_comp, OracleComp.prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' r, Pr{let z ← F.run cache}[z = r] * (if CompletedHit relevant (T r.1) cache then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro r
      by_cases hr : r ∈ support (F.run cache)
      · refine mul_le_mul_right ?_ _
        simp only [StateT.run_map, prEvent_map]
        change Pr{let w ← B.run r.2}[CompletedHit relevant (T r.1) (merged w.1.2)] ≤ _
        by_cases hbad : CompletedHit relevant (T r.1) cache
        · rw [if_pos hbad]
          exact (prEvent_le_one _)
        · rw [if_neg hbad]
          calc
            _ ≤ Pr{let _ ← B.run r.2}[False] := by
              apply prEvent_mono_of_support _ _ _
              intro w hw hh
              apply hbad
              obtain ⟨hgrow, -, hreadF, -⟩ := recordReads_resolves oa ∅ cache
                (by intro i v h; cases h) r hr
              obtain ⟨hgrowB, -, hreadB, -⟩ := recordReads_resolves block ∅ r.2
                (by intro i v h; cases h) w hw
              obtain ⟨input, output, hout, hnone, hrel, hne, heq⟩ :=
                (completedHit_recordedTargets relevant (target r.1.1 r.1.2) r.1.2 _).mp hh
              refine (completedHit_recordedTargets relevant (target r.1.1 r.1.2) r.1.2 cache).mpr
                ⟨input, output, ?_, hnone, hrel, hne, heq⟩
              cases hi : w.1.2 input with
              | none => simpa only [merged, QueryCache.ofFn_apply, hi] using hout
              | some value =>
                  have hval : value = output := by
                    simpa only [merged, QueryCache.ofFn_apply, hi, Option.some.injEq] using hout
                  subst hval
                  rcases hcovered r hr w hw input hrel (by simp [hi]) with h | h
                  · simp [hnone] at h
                  · obtain ⟨other, hother⟩ := Option.isSome_iff_exists.mp h
                    have h1 := hgrowB (hgrow hother)
                    have h2 := hreadB hi
                    rw [h1] at h2
                    rw [hother, Option.some.inj h2]
            _ = 0 := by simp
      · simp [prEvent_eq_zero_of_not_mem_support _ hr]
    _ = Pr{let z ← F.run cache}[CompletedHit relevant (T z.1) cache] := by
      simp only [mul_ite, mul_one, mul_zero]
      exact (OracleComp.prEvent_eq_tsum_ite _ _).symm

/-- `completionPotential_recorded_block_le` for the block itself. A run of `recordReads`
forgets to the run of the block. -/
theorem completionPotential_block_le {α β : Type} (relevant : Query C → Prop)
    (oa : OracleComp (Query C →ₒ HashOutput) α) (target : α → HashCache C → CompletionTargets C)
    (block : OracleComp (Query C →ₒ HashOutput) β) (cache : HashCache C)
    (hcovered : ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (recordReads oa ∅)).run cache),
      ∀ w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle (recordReads block ∅)).run z.2),
      ∀ input, relevant input → (w.1.2 input).isSome → (z.1.2 input).isSome ∨ (cache input).isSome) :
    (∑' r, Pr{let z ← (simulateQ (Query C →ₒ HashOutput).randomOracle block).run cache}[z = r] *
      completionPotential relevant (recordedCompletion oa target) r.2) ≤
        completionPotential relevant (recordedCompletion oa target) cache := by
  have hforget : ∀ (b : OracleComp (Query C →ₒ HashOutput) β) (record start : HashCache C),
      (fun w : (β × HashCache C) × HashCache C => (w.1.1, w.2)) <$>
          (simulateQ (Query C →ₒ HashOutput).randomOracle (recordReads b record)).run start =
        (simulateQ (Query C →ₒ HashOutput).randomOracle b).run start := by
    intro b
    induction b using OracleComp.inductionOn with
    | pure a =>
        intro record start
        change (fun w : (β × HashCache C) × HashCache C => (w.1.1, w.2)) <$>
          (simulateQ (Query C →ₒ HashOutput).randomOracle
            (pure (a, record) : OracleComp (Query C →ₒ HashOutput) (β × HashCache C))).run start = _
        simp
    | query_bind input next ih =>
        intro record start
        change (fun w : (β × HashCache C) × HashCache C => (w.1.1, w.2)) <$>
          (simulateQ (Query C →ₒ HashOutput).randomOracle
            (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input) >>= fun answer =>
              recordReads (next answer) (record.cacheQuery input answer))).run start = _
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, map_bind]
        refine bind_congr fun r => ?_
        exact ih r.1 _ r.2
  have h := completionPotential_recorded_block_le relevant oa target block cache hcovered
  rw [← hforget block ∅ cache, OracleComp.tsum_prEvent_map_mul]
  exact h

/-- `completionPotential_block_le` for a block of the honest operators in the logged world. -/
theorem logged_block_potential_le {α β : Type} (relevant : Query C → Prop)
    (oa : OracleComp (Query C →ₒ HashOutput) α) (target : α → HashCache C → CompletionTargets C)
    (block : OracleComp (Query C →ₒ HashOutput) β) (s : LoggedState C)
    (hcovered : ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (recordReads oa ∅)).run s.1.1),
      ∀ w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle (recordReads block ∅)).run z.2),
      ∀ input, relevant input → (w.1.2 input).isSome → (z.1.2 input).isSome ∨ (s.1.1 input).isSome) :
    (∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
        (SigningSecurityProof.liftFree (hashEmbed block))).run s)}[z = r] *
      completionPotential relevant (recordedCompletion oa target) r.2.1.1) ≤
        completionPotential relevant (recordedCompletion oa target) s.1.1 := by
  have hlog := SigningCoreProof.simulateQ_run_forget (loggedImpl prims)
    (SigningCacheProof.countImpl prims) (fun t s b => by simp [loggedImpl, Functor.map_map])
    (SigningSecurityProof.liftFree (hashEmbed block)) s.1 s.2
  have hforget : (fun z : β × LoggedState C => (z.1, z.2.1.1)) <$>
      (simulateQ (loggedImpl prims) (SigningSecurityProof.liftFree (hashEmbed block))).run s =
        (simulateQ (Query C →ₒ HashOutput).randomOracle block).run s.1.1 := by
    rw [← SelectedKeygen.hashEmbed_count_forget prims block s.1.1 s.1.2, ← hlog, Functor.map_map]
  have h := completionPotential_block_le relevant oa target block s.1.1 hcovered
  rw [← hforget, OracleComp.tsum_prEvent_map_mul] at h
  exact h

end SigningOwnPotential

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnPotential.completionPotential_covered_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigningOwnPotential.completionPotential_covered_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnPotential.completionPotential_recorded_block_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigningOwnPotential.completionPotential_recorded_block_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnPotential.completionPotential_block_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigningOwnPotential.completionPotential_block_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnPotential.logged_block_potential_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigningOwnPotential.logged_block_potential_le

end ThresholdLeanXmssSecurity
