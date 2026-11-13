import ThresholdLeanXmssSecurity.Proof.Dealer

/-! # Deterministic evaluation of complete dealer batch logs

The writer records one output list per batch. Positive batch size combines the
returned rows into their original job order while retaining every log entry.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeDealerBatches
attribute [local irreducible] D
variable {C : Committee}

theorem D_logged_batches (prims : Primitives) (h : Query C → HashOutput)
    (f : Job → OracleComp (RoSpec C) (List Bit)) (batches : List (List Job)) :
    D prims h ((batches.mapM fun jobs => do
      let outputs ← liftM (jobs.mapM f)
      tell [outputs]
      pure (some outputs) : WriterT (List (List (List Bit))) (OracleComp (RoSpec C))
        (List (Option (List (List Bit))))).run) =
      (batches.map (fun jobs => some (jobs.map fun job => D prims h (f job))),
       batches.map (fun jobs => jobs.map fun job => D prims h (f job))) := by
  induction batches with
  | nil => simp [D_pure]
  | cons batch batches ih =>
    simp only [List.mapM_cons, WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell,
      WriterT.run_pure, D_bind, D_map, D_mapM, D_pure, ih, List.map_cons]
    simp

theorem D_logged_batched (prims : Primitives) (h : Query C → HashOutput)
    (f : Job → OracleComp (RoSpec C) (List Bit)) (jobs : List Job)
    (size : ℕ) (hsize : 0 < size) :
    D prims h ((batched size (fun js => do
      let outputs ← liftM (js.mapM f)
      tell [outputs]
      pure (some outputs)) jobs :
        WriterT (List (List (List Bit))) (OracleComp (RoSpec C))
          (Option (List (List Bit)))).run) =
      (some (jobs.map fun job => D prims h (f job)),
       (chunks size jobs).map fun js => js.map fun job => D prims h (f job)) := by
  simp only [batched, WriterT.run_bind, D_bind, D_logged_batches, WriterT.run_pure,
    D_map, D_pure, chunks_outputs size hsize]
  simp

end ThresholdLeanXmssSecurity.LifetimeDealerBatches

/-- info: 'ThresholdLeanXmssSecurity.LifetimeDealerBatches.D_logged_batches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeDealerBatches.D_logged_batches

/-- info: 'ThresholdLeanXmssSecurity.LifetimeDealerBatches.D_logged_batched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeDealerBatches.D_logged_batched
