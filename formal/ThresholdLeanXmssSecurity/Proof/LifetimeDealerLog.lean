import ThresholdLeanXmssSecurity.Proof.Dealer

/-! # The complete dealer log under reference evaluation

Replacing circuit evaluation by reference jobs preserves every batch opening,
the public tree result and the final hash cache, for arbitrary batch sizes.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeDealerLog
variable {C : Committee}

def referenceDealer (settings : Settings) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    OracleComp (RoSpec C) (Option TreeOutput × List (List (List Bit))) :=
  (ceremonyOutput (m := WriterT (List (List (List Bit))) (OracleComp (RoSpec C)))
    (fun p => liftM (tweakable (C := C) p)) parameter
    (batched settings.batchSize fun jobs => do
      let outputs ← liftM (jobs.mapM (referenceJob tweakable (prfValue seeds) parameter))
      tell [outputs]
      pure (some outputs)) top tree).run

/-- Interpret the oracle program while retaining its writer output. -/
def writerRoHom (prims : Primitives) {ω : Type} :
    WriterT (List ω) (OracleComp (RoSpec C)) →ᵐ
      WriterT (List ω) (StateT (HashCache C) ProbComp) where
  toFun _ p := WriterT.mk (simulateQ (roImpl prims) p.run)
  toFun_pure' _ := by ext; simp
  toFun_bind' _ _ := by ext; simp [simulateQ_bind]

theorem allArity_chunk {jobs batch : List Job} (hjobs : AllArity jobs) (size : ℕ)
    (hbatch : batch ∈ chunks size jobs) : AllArity batch := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hbatch
  intro job hjob
  exact hjobs job (List.mem_of_mem_drop (List.mem_of_mem_take hjob))

theorem dealer_reference_log (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (hc : CircuitsCompute circuits prims.Th) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) (c : HashCache C) :
    roRun prims (dealerCeremony circuits settings parameter seeds top tree) c =
      roRun prims (referenceDealer settings parameter seeds top tree) c := by
  have h : writerRoHom (C := C) prims
      (ceremonyOutput (fun p => liftM (tweakable (C := C) p)) parameter
        (batched settings.batchSize fun jobs => do
          let outputs ← liftM (jobs.mapM (evalJob circuits parameter seeds))
          tell [outputs]
          pure (some outputs)) top tree) =
      writerRoHom (C := C) prims
      (ceremonyOutput (fun p => liftM (tweakable (C := C) p)) parameter
        (batched settings.batchSize fun jobs => do
          let outputs ← liftM (jobs.mapM (referenceJob tweakable (prfValue seeds) parameter))
          tell [outputs]
          pure (some outputs)) top tree) := by
    rw [monadHom_ceremonyOutput, monadHom_ceremonyOutput]
    apply ceremonyOutput_congr
    intro jobs hjobs
    rw [monadHom_batched, monadHom_batched]
    unfold batched
    congr 1
    apply keygen_mapM_congr
    intro batch hbatch
    apply WriterT.ext
    apply StateT.ext
    intro s
    change roRun prims _ s = roRun prims _ s
    simp only [WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell,
      WriterT.run_pure, bind_map_left, map_pure, pure_bind]
    rw [roRun_bind, roRun_bind,
      roRun_mapM_congr prims _ _ batch
        (fun job hjob s' => roRun_evalJob prims circuits hc parameter seeds job
          (allArity_chunk hjobs settings.batchSize hbatch job hjob) s') s]
  exact congrArg (fun p => p.run.run c) h

end ThresholdLeanXmssSecurity.LifetimeDealerLog

/-- info: 'ThresholdLeanXmssSecurity.LifetimeDealerLog.writerRoHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeDealerLog.writerRoHom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeDealerLog.allArity_chunk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeDealerLog.allArity_chunk

/-- info: 'ThresholdLeanXmssSecurity.LifetimeDealerLog.dealer_reference_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeDealerLog.dealer_reference_log
