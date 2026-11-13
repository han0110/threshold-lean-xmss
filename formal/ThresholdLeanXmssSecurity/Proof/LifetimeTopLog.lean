import ThresholdLeanXmssSecurity.Proof.LifetimeDealerLog
import ThresholdLeanXmssSecurity.Proof.LifetimeFixedCache
import ThresholdLeanXmssSecurity.Proof.LifetimeDealerBatches

/-! # Reconstructing all top-tree batch openings

Every supported reference top ceremony succeeds. Its full writer log is the
ordered batch opening list reconstructed from the returned top tree.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeTopLog
open LifetimeDealerLog LifetimeFixedCache LifetimeDealerBatches
attribute [local irreducible] D
variable {C : Committee}

theorem D_top_body (prims : Primitives) (h : Query C → HashOutput)
    (f : Job → OracleComp (RoSpec C) (List Bit)) (jobs : List Job)
    (size : ℕ) (hsize : 0 < size)
    (root : List (List Bit) → OracleComp (RoSpec C) Digest)
    (output : List (List Bit) → Digest → TreeOutput) :
    D prims h ((do
      let some outputs ← batched size (fun js => do
        let values ← liftM (js.mapM f)
        tell [values]
        pure (some values)) jobs | pure none
      let value ← liftM (root outputs)
      pure (some (output outputs value)) :
        WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) (Option TreeOutput)).run) =
      (D prims h (do
        let some outputs ← some <$> jobs.mapM f | pure none
        let value ← root outputs
        pure (some (output outputs value))),
       (chunks size jobs).map fun js => js.map fun job => D prims h (f job)) := by
  simp only [WriterT.run_bind, D_bind, D_logged_batched prims h _ _ _ hsize,
    WriterT.run_liftM, D_map, WriterT.run_pure, D_pure, D_mapM,
    List.empty_eq, List.append_nil]

theorem D_reference_top (prims : Primitives) (h : Query C → HashOutput)
    (settings : Settings) (hsize : 0 < settings.batchSize) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) :
    D prims h (referenceDealer settings parameter seeds top .top) =
      (D prims h (referenceTree tweakable (prfValue seeds) parameter top .top),
       (chunks settings.batchSize topJobs).map fun jobs =>
         jobs.map fun job => D prims h (referenceJob tweakable (prfValue seeds) parameter job)) := by
  exact D_top_body prims h (referenceJob tweakable (prfValue seeds) parameter)
    topJobs settings.batchSize hsize
    (fun outputs => tweakable (merkleNode parameter topLayer
      (fun e l => digestAt (outputs.getD
        (((List.finRange (2 ^ layerHeight)).flatMap fun b =>
          (List.finRange numChains).map fun l => (topKey b, l)).idxOf (e, l)) []) 0)
      layerHeight 0))
    (fun outputs root => .top ⟨fun e l => digestAt (outputs.getD
      (((List.finRange (2 ^ layerHeight)).flatMap fun b =>
        (List.finRange numChains).map fun l => (topKey b, l)).idxOf (e, l)) []) 0, root⟩)

theorem reference_top_log (prims : Primitives) (settings : Settings)
    (hsize : 0 < settings.batchSize) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (c : HashCache C)
    (r : (Option TreeOutput × List (List (List Bit))) × HashCache C)
    (hr : r ∈ support (roRun prims (referenceDealer settings parameter seeds top .top) c)) :
    ∃ out : TopTree, r.1.1 = some (.top out) ∧
      r.1.2 = treeOpenings settings 0 .top (.top out) := by
  have hr' : (r.1, eraseFixed r.2) ∈ support
      (roRun prims (referenceDealer settings parameter seeds top .top) (eraseFixed c)) := by
    rw [← roRun_eraseFixed]
    rw [support_map]
    exact ⟨r, hr, rfl⟩
  obtain ⟨_, hn, hd⟩ := roRun_support prims _ _ _ hr'
  have hn' := hn (eraseFixed_noMpc c)
  let h := hashOf prims (eraseFixed r.2)
  have heq := hd h (good_hashOf prims _) (agrees_hashOf prims hn')
  obtain ⟨out, hout, hchain, _⟩ := D_refTop (prims := prims) (h := h) parameter seeds top
  rw [D_reference_top prims h settings hsize, hout] at heq
  refine ⟨out, congrArg Prod.fst heq, (congrArg Prod.snd heq).trans ?_⟩
  unfold treeOpenings
  apply List.map_congr_left
  intro jobs hjobs
  apply List.map_congr_left
  intro job hjob
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hjobs
  have hj : job ∈ topJobs := List.mem_of_mem_drop (List.mem_of_mem_take hjob)
  simp only [topJobs, List.mem_flatMap, List.mem_map] at hj
  obtain ⟨b, _, l, _, rfl⟩ := hj
  simp [D_referenceJob, hchain]

end ThresholdLeanXmssSecurity.LifetimeTopLog

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTopLog.D_top_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTopLog.D_top_body

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTopLog.D_reference_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTopLog.D_reference_top

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTopLog.reference_top_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTopLog.reference_top_log
