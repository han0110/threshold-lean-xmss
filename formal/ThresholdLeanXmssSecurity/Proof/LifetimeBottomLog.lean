import ThresholdLeanXmssSecurity.Proof.LifetimeDealerLog
import ThresholdLeanXmssSecurity.Proof.LifetimeDealerBatches
import ThresholdLeanXmssSecurity.Proof.LifetimeFixedCache
import ThresholdLeanXmssSecurity.Proof.LifetimeTableReplay

/-! # Successful bottom-tree openings and randomizer replay

A successful reference bottom ceremony retains exactly the public output's batch
openings. Its opened top-key randomizer is the actual PRF value and is replayed
without changing any extension of the ceremony's final cache.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeBottomLog
open LifetimeDealerLog LifetimeDealerBatches LifetimeFixedCache LifetimeTableReplay
attribute [local irreducible] D bottomJobs signJobs
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
variable {C : Committee}

/-- Dropping the reference dealer's writer keeps the original reference tree. -/
theorem fst_referenceDealer (settings : Settings) (hsize : 0 < settings.batchSize)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    Prod.fst <$> referenceDealer settings parameter seeds top tree =
      referenceTree tweakable (prfValue seeds) parameter top tree := by
  unfold referenceDealer referenceTree
  change dropLog _ = _
  rw [monadHom_ceremonyOutput]
  congr 1
  · funext β oa
    exact dropLog_liftM _
  · funext js
    rw [monadHom_batched, ← batched_some settings.batchSize hsize]
    congr 1
    funext js'
    simp only [MonadHom.toFun_bind', MonadHom.toFun_pure', dropLog_liftM,
      dropLog_tell, pure_bind]
    rw [map_eq_bind_pure_comp]
    rfl

/-- The last first-run row contains the whole top-key randomizer digest. -/
theorem bottomOutputs_randomizer (prims : Primitives) (h : Query C → HashOutput)
    (seeds : C.Term → HashOutput) (P : PublicParameter) (b : Fin (2 ^ layerHeight)) :
    digestAt ((bottomOutputs prims h seeds P b).getD
      ((bottomKeys b).length + 2 ^ layerHeight) []) 0 =
        D prims h (prfValue seeds (.randomizer topLayer (topKey b))) := by
  simp only [bottomOutputs, bottomJobs_eq, List.map_append]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_append, List.length_map, List.length_finRange]
  simp [D_referenceJob, digestAt_bits]

/-- The chain indices and batch boundaries of signature jobs do not depend on their positions. -/
theorem sign_openings (prims : Primitives) (h : Query C → HashOutput)
    (seeds : C.Term → HashOutput) (P : PublicParameter) (b : Fin (2 ^ layerHeight))
    (encoding : Encoding) (size : ℕ) (out : BottomTree)
    (hvalues : ∀ l, out.topSignature.chainValues l =
      digestAt (((signJobs b encoding).map fun job =>
        D prims h (referenceJob tweakable (prfValue seeds) P job)).getD l.val []) 0) :
    (chunks size (signJobs b encoding)).map (fun jobs => jobs.map fun job =>
      D prims h (referenceJob tweakable (prfValue seeds) P job)) =
    (chunks size (signJobs b fun _ => digit 0)).map (fun jobs => jobs.map fun job =>
      match job.kind with
      | .chainRow e l => bitsOfDigest (out.cpk e l).1 ++
          bitsOfDigest (out.cpk e l).2.1 ++ bitsOfDigest (out.cpk e l).2.2
      | .chainValue _ l _ => bitsOfDigest (out.topSignature.chainValues l)
      | .commitment e => bitsOfDigest (out.commitment e)
      | .randomizer => bitsOfDigest (D prims h (prfValue seeds (.randomizer topLayer (topKey b))))
      | _ => []) := by
  simp only [chunks, signJobs, List.length_map, List.map_map, ← List.map_drop, ← List.map_take, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro k hk
  apply List.map_congr_left
  intro l hl
  rw [hvalues, signOutputs_value]
  simp [D_referenceJob]

/-- All three blocks of a first-run chain row are recovered, together with every commitment. -/
theorem bottom_openings (prims : Primitives) (h : Query C → HashOutput)
    (seeds : C.Term → HashOutput) (P : PublicParameter) (b : Fin (2 ^ layerHeight))
    (size : ℕ) (out : BottomTree)
    (hcpk : ∀ k l, out.cpk (bottomKey b k) l =
      let bits := (bottomOutputs prims h seeds P b).getD ((bottomKeys b).idxOf (bottomKey b k, l)) []
      (digestAt bits 0, digestAt bits 1, digestAt bits 2))
    (hcommit : ∀ k, out.commitment (bottomKey b k) =
      digestAt ((bottomOutputs prims h seeds P b).getD
        ((bottomKeys b).length + (bottomKey b k).val % 2 ^ layerHeight) []) 0) :
    (chunks size (bottomJobs b)).map (fun jobs => jobs.map fun job =>
      D prims h (referenceJob tweakable (prfValue seeds) P job)) =
    (chunks size (bottomJobs b)).map (fun jobs => jobs.map fun job =>
      match job.kind with
      | .chainRow e l => bitsOfDigest (out.cpk e l).1 ++
          bitsOfDigest (out.cpk e l).2.1 ++ bitsOfDigest (out.cpk e l).2.2
      | .chainValue _ l _ => bitsOfDigest (out.topSignature.chainValues l)
      | .commitment e => bitsOfDigest (out.commitment e)
      | .randomizer => bitsOfDigest (D prims h (prfValue seeds (.randomizer topLayer (topKey b))))
      | _ => []) := by
  apply List.map_congr_left
  intro jobs hjobs
  apply List.map_congr_left
  intro job hjob
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hjobs
  have hj : job ∈ bottomJobs b := List.mem_of_mem_drop (List.mem_of_mem_take hjob)
  simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_singleton] at hj
  rcases hj with (⟨k, _, l, _, rfl⟩ | ⟨k, _, rfl⟩) | rfl
  · obtain ⟨h0, h1, h2⟩ := bottomOutputs_cpk (prims := prims) (h := h) seeds P b k l
    simp only [hcpk, h0, h1, h2]
    simp [D_referenceJob]
  · simp only [hcommit, bottomOutputs_commitment]
    simp [D_referenceJob]
  · simp [D_referenceJob]

/-- Successful two-run writer computations retain both ordered batches. -/
theorem D_bottom_body (prims : Primitives) (h : Query C → HashOutput)
    (f : Job → OracleComp (RoSpec C) (List Bit)) (jobs : List Job)
    (signs : Encoding → List Job) (size : ℕ) (hsize : 0 < size)
    (root : List (List Bit) → OracleComp (RoSpec C) Digest)
    (base : List (List Bit) → Digest → OracleComp (RoSpec C) Randomness)
    (find : Digest → Randomness → OracleComp (RoSpec C) (Option (Randomness × Encoding)))
    (path : OracleComp (RoSpec C) (Fin layerHeight → Digest))
    (check : Digest → Randomness → List (List Bit) → (Fin layerHeight → Digest) →
      OracleComp (RoSpec C) (Option Digest)) (target : Digest)
    (output : List (List Bit) → Digest → Randomness → List (List Bit) →
      (Fin layerHeight → Digest) → BottomTree) :
    let program : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) (Option TreeOutput) := do
      let some outputs ← batched size (fun js => do
        let values ← liftM (js.mapM f)
        tell [values]
        pure (some values)) jobs | pure none
      let value ← liftM (root outputs)
      let start ← liftM (base outputs value)
      let some (randomness, encoding) ← liftM (find value start) | pure none
      let some values ← batched size (fun js => do
        let values ← liftM (js.mapM f)
        tell [values]
        pure (some values)) (signs encoding) | pure none
      let branch ← liftM path
      let actual ← liftM (check value randomness values branch)
      if actual ≠ some target then pure none else
        pure (some (.bottom (output outputs value randomness values branch)))
    (D prims h program.run).1 ≠ none →
      ∃ value randomness encoding branch,
        D prims h program.run =
          (some (.bottom (output (jobs.map fun j => D prims h (f j)) value randomness
            ((signs encoding).map fun j => D prims h (f j)) branch)),
           (chunks size jobs).map (fun js => js.map fun j => D prims h (f j)) ++
             (chunks size (signs encoding)).map (fun js => js.map fun j => D prims h (f j))) := by
  intro program hsuccess
  dsimp only [program] at hsuccess ⊢
  simp only [WriterT.run_bind, D_bind, D_logged_batched prims h _ _ _ hsize,
    WriterT.run_liftM, D_map] at hsuccess ⊢
  split at hsuccess
  next randomness encoding hfound =>
    simp only [WriterT.run_bind, D_bind, D_logged_batched prims h _ _ _ hsize,
      WriterT.run_liftM, D_map] at hsuccess ⊢
    split at hsuccess
    next hcheck =>
      simp only [WriterT.run_pure, D_pure] at hsuccess
      exact False.elim (hsuccess rfl)
    next hcheck =>
      refine ⟨D prims h (root (jobs.map fun j => D prims h (f j))),
        randomness, encoding, D prims h path, ?_⟩
      simp only [if_neg hcheck, WriterT.run_pure, D_pure,
        List.empty_eq, List.nil_append, List.append_nil]
  next hfound =>
    simp only [WriterT.run_pure, D_pure] at hsuccess
    exact False.elim (hsuccess rfl)

/-- A successful deterministic bottom ceremony determines its complete ordered log. -/
theorem D_reference_bottom (prims : Primitives) (h : Query C → HashOutput)
    (settings : Settings) (hsize : 0 < settings.batchSize) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (hsuccess : (D prims h (referenceDealer settings P seeds top (.bottom b))).1 ≠ none) :
    ∃ out : BottomTree,
      D prims h (referenceDealer settings P seeds top (.bottom b)) =
        (some (.bottom out), treeOpenings settings
          (D prims h (prfValue seeds (.randomizer topLayer (topKey b)))) (.bottom b) (.bottom out)) := by
  have hb := D_bottom_body prims h (referenceJob tweakable (prfValue seeds) P)
    (bottomJobs b) (signJobs b) settings.batchSize hsize
    (fun outputs => tweakable (merkleNode P bottomLayer
      (fun e l => digestAt (outputs.getD ((bottomKeys b).idxOf (e, l)) []) 2) layerHeight b.val))
    (fun outputs value => tweakable (truncateHash <$> Concrete.oracleHash
      (randomizerInput P topLayer (topKey b)
        (digestAt (outputs.getD ((bottomKeys b).length + 2 ^ layerHeight) []) 0) (bytesLE 16 value))))
    (fun value start => tweakable (grind P topLayer (topKey b) (bytesLE 16 value) start
      randomizerAttemptLimit 0))
    (tweakable (merklePath P topLayer top.chainEnd (topKey b)))
    (fun value randomness values branch => tweakable (Concrete.layerRoot P topLayer (topKey b)
      (bytesLE 16 value) ⟨randomness, fun l => digestAt (values.getD l.val []) 0, branch⟩))
    top.root
    (fun outputs value randomness values branch =>
      ⟨fun e l => let bits := outputs.getD ((bottomKeys b).idxOf (e, l)) []
          (digestAt bits 0, digestAt bits 1, digestAt bits 2),
       fun e => digestAt (outputs.getD ((bottomKeys b).length + e.val % 2 ^ layerHeight) []) 0,
       value, ⟨randomness, fun l => digestAt (values.getD l.val []) 0, branch⟩⟩)
    hsuccess
  obtain ⟨value, randomness, encoding, branch, he⟩ := hb
  let out : BottomTree :=
    ⟨fun e l => let bits := (bottomOutputs prims h seeds P b).getD ((bottomKeys b).idxOf (e, l)) []
        (digestAt bits 0, digestAt bits 1, digestAt bits 2),
     fun e => digestAt ((bottomOutputs prims h seeds P b).getD
       ((bottomKeys b).length + e.val % 2 ^ layerHeight) []) 0,
     value, ⟨randomness, fun l => digestAt
       (((signJobs b encoding).map fun job => D prims h
         (referenceJob tweakable (prfValue seeds) P job)).getD l.val []) 0, branch⟩⟩
  refine ⟨out, he.trans ?_⟩
  apply Prod.ext
  · rfl
  · dsimp only [treeOpenings]
    rw [List.map_append]
    congr 1
    · exact bottom_openings prims h seeds P b settings.batchSize _
        (fun _ _ => rfl) (fun _ => rfl)
    · exact sign_openings prims h seeds P b encoding settings.batchSize _ (fun _ => rfl)

/-- A member of an executed job list has a supported subrun below its final cache. -/
theorem roRun_mapM_member (prims : Primitives) {α β : Type}
    (f : α → OracleComp (RoSpec C) β) (xs : List α) (a : α) (ha : a ∈ xs)
    {c : HashCache C} {z : List β × HashCache C}
    (hz : z ∈ support (roRun prims (xs.mapM f) c)) :
    ∃ before after v, (v, after) ∈ support (roRun prims (f a) before) ∧ after ≤ z.2 := by
  have hrel := roRun_mapM_forall₂ prims f xs hz
  have hp := hrel.imp (fun x y hxy =>
    And.intro (show ∃ before after v,
      (v, after) ∈ support (roRun prims (f x) before) ∧ after ≤ z.2 from by
        obtain ⟨before, after, hs, hle⟩ := hxy
        exact ⟨before, after, y, hs, hle⟩) True.intro)
  exact ((List.forall₂_and_left xs z.1).mp hp).1 a ha

/-- A supported prefix cache is below the cache after the continuation. -/
theorem roRun_bind_prefix (prims : Primitives) {α β : Type}
    (p : OracleComp (RoSpec C) α) (k : α → OracleComp (RoSpec C) β)
    {c : HashCache C} {z : β × HashCache C}
    (hz : z ∈ support (roRun prims (p >>= k) c)) :
    ∃ middle, middle ∈ support (roRun prims p c) ∧ middle.2 ≤ z.2 := by
  rw [roRun_bind, mem_support_bind_iff] at hz
  obtain ⟨middle, hp, hk⟩ := hz
  exact ⟨middle, hp, (roRun_support prims (k middle.1) middle.2 z hk).1⟩

/-- The first run contains a supported call of the actual top-key randomizer PRF. -/
theorem reference_randomizer_supported (prims : Primitives) (settings : Settings)
    (hsize : 0 < settings.batchSize) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (c : HashCache C)
    (r : (Option TreeOutput × List (List (List Bit))) × HashCache C)
    (hr : r ∈ support (roRun prims (referenceDealer settings P seeds top (.bottom b)) c)) :
    ∃ before z, z ∈ support
      (roRun prims (prfValue seeds (.randomizer topLayer (topKey b))) before) ∧ z.2 ≤ r.2 := by
  have hr0 : (r.1.1, r.2) ∈ support
      (roRun prims (referenceTree tweakable (prfValue seeds) P top (.bottom b)) c) := by
    rw [← fst_referenceDealer settings hsize, roRun_map]
    rw [support_map]
    exact ⟨r, hr, rfl⟩
  rw [refBottom_eq] at hr0
  obtain ⟨middle, hjobs, hle⟩ := roRun_bind_prefix prims
    ((bottomJobs b).mapM (referenceJob tweakable (prfValue seeds) P))
    (referenceBottomRest seeds P top b) hr0
  have hm : (⟨.randomizer, [.randomizer topLayer (topKey b)]⟩ : Job) ∈ bottomJobs b := by
    unfold bottomJobs
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨before, after, v, hjob, hafter⟩ := roRun_mapM_member prims _ _ _ hm hjobs
  have hj : referenceJob tweakable (prfValue seeds) P
      (⟨.randomizer, [.randomizer topLayer (topKey b)]⟩ : Job) =
      bitsOfDigest <$> prfValue seeds (.randomizer topLayer (topKey b)) := by
    simp [referenceJob, List.mapM_cons, List.mapM_nil]
  rw [hj, roRun_map, support_map] at hjob
  obtain ⟨z, hz, he⟩ := hjob
  refine ⟨before, z, hz, ?_⟩
  have he' : z.2 = after := congrArg Prod.snd he
  simpa only [he'] using hafter.trans hle

/-- Successful public bottom outputs determine every opening and the later PRF answer. -/
theorem reference_bottom_log (prims : Primitives) (settings : Settings)
    (hsize : 0 < settings.batchSize) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (b : Fin (2 ^ layerHeight)) (c : HashCache C)
    (r : (Option TreeOutput × List (List (List Bit))) × HashCache C)
    (hr : r ∈ support (roRun prims (referenceDealer settings parameter seeds top (.bottom b)) c))
    (hout : r.1.1 ≠ none) :
    ∃ (out : BottomTree) (ρ : Digest), r.1.1 = some (.bottom out) ∧
      r.1.2 = treeOpenings settings ρ (.bottom b) (.bottom out) ∧
      ∀ c' : HashCache C, r.2 ≤ c' →
        roRun prims (prfValue seeds (.randomizer topLayer (topKey b))) c' = pure (ρ, c') := by
  have hr' : (r.1, eraseFixed r.2) ∈ support
      (roRun prims (referenceDealer settings parameter seeds top (.bottom b)) (eraseFixed c)) := by
    rw [← roRun_eraseFixed]
    rw [support_map]
    exact ⟨r, hr, rfl⟩
  obtain ⟨_, hn, hd⟩ := roRun_support prims _ _ _ hr'
  have hn' := hn (eraseFixed_noMpc c)
  let h := hashOf prims (eraseFixed r.2)
  have hg : Good prims h := good_hashOf prims _
  have ha : Agrees h (eraseFixed r.2) := agrees_hashOf prims hn'
  have heq := hd h hg ha
  have hs : (D prims h (referenceDealer settings parameter seeds top (.bottom b))).1 ≠ none := by
    rw [← heq]
    exact hout
  obtain ⟨out, ho⟩ := D_reference_bottom prims h settings hsize parameter seeds top b hs
  have he := heq.trans ho
  refine ⟨out, D prims h (prfValue seeds (.randomizer topLayer (topKey b))),
    congrArg Prod.fst he, congrArg Prod.snd he, ?_⟩
  obtain ⟨before, z, hz, hzle⟩ :=
    reference_randomizer_supported prims settings hsize parameter seeds top b _ _ hr'
  have hzvalue := (roRun_support prims _ _ _ hz).2.2 h hg (ha.mono hzle)
  intro c' hc'
  have hfinal : z.2 ≤ c' := hzle.trans ((eraseFixed_le r.2).trans hc')
  simpa only [hzvalue] using roRun_rerun_pure prims _ hz hfinal

end ThresholdLeanXmssSecurity.LifetimeBottomLog

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.fst_referenceDealer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.fst_referenceDealer

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.bottomOutputs_randomizer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.bottomOutputs_randomizer

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.sign_openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.sign_openings

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.bottom_openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.bottom_openings

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.D_bottom_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.D_bottom_body

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.D_reference_bottom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.D_reference_bottom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.roRun_mapM_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.roRun_mapM_member

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.roRun_bind_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.roRun_bind_prefix

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.reference_randomizer_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.reference_randomizer_supported

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBottomLog.reference_bottom_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeBottomLog.reference_bottom_log
