import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Engine

/-!
# One ceremony in the hybrid model of GS20, the proof

`ceremonyHybridSecurity` gives `CeremonyHybridSecurityStatement`. The proof follows GS20, Theorem 2, with the
simulator `ceremonyHybridSimulator`.

* `hybridCommon` is the common run of the hybrid and of the ideal run. It starts the adversary,
  computes every output as `F_ceremony` does, and runs the simulator with the opened values.
* `ceremony_real_hybrid` states that the real run accepts as the common run with the opened outputs.
  It follows from `engine` and `lazyBatches_eager`.
* `ceremony_ideal_common` states that the ideal run is the common run with the outputs of
  `F_ceremony`.
* `ceremony_hybrid_ideal` states that the two differ only when two copy hashes collide
  (`simBatches_inv`). The bound is `copy_birthday` on the calls of the common run in the copy domain.
* `ceremony_queryBound` states that the ideal run makes at most `q + hybridOverhead` counted calls.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

section Games

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (jobs : List Job) (D : C.Coalition) (A : CeremonyAdversary C E)
  {x : C.Party → Keys C} {parameter : PublicParameter} {seeds : C.Term → HashOutput}
  {pairKeys : C.Pair → HashOutput}

/-- The common run of the hybrid and of the ideal run. It gives every output of `F_ceremony`, the
state of the adversary, and the opened outputs of each operator. -/
def hybridCommon (x : C.Party → Keys C) (z : Aux) (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    OracleComp (LocalSpec C) (List (List Bit) × A.State × (C.Party → Option (List (List Bit)))) :=
  A.start (corruptInputs D x) z >>= fun st =>
  liftComp (jobs.mapM (evalJob circuits parameter seeds)) (LocalSpec C) >>= fun outputs =>
  simBatches K circuits settings.mode D (batchAdversary A) parameter (knownSeed (corruptInputs D x))
    (chunks settings.batchSize jobs) outputs (fun _ => some []) st >>= fun r =>
  pure (outputs, r)

/-- The joint output of the ideal run, from the common run. An operator with opened outputs gets the
outputs of `F_ceremony`. -/
def ceremonyIdealOut {σ : Type} (D : C.Coalition) (r : List (List Bit) × σ × (C.Party → Option (List (List Bit)))) :
    σ × (C.Party → Option (List (List Bit))) :=
  (r.2.1, fun i => if i ∉ D.1 ∧ (r.2.2 i).isSome then some r.1 else none)

/-- A run with the adversary of a ceremony is the run with the adversary of a batch. -/
theorem executePhase_batchAdversary {α : Type} (mode : ReshareMode) (fuel : ℕ) (st : A.State)
    (p : C.Party → PartyM C E (MainSpec C) α) :
    executePhase localRoles D A (mainFunctionalities K mode) fuel st p =
      executePhase localRoles D (batchAdversary A) (mainFunctionalities K mode) fuel st p := by
  unfold executePhase
  refine bind_congr fun steps => ?_
  induction fuel generalizing st steps with
  | zero => rfl
  | succ n ih =>
    simp only [executeRounds]
    split_ifs
    · rfl
    · exact bind_congr fun r => ih _ _

/-- Dealt keys give `F_ceremony` the parameter and the seeds of the dealer. -/
theorem fceremony_dealt (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) :
    (firstInput fun i => if i ∈ D.1 then none else some (x i)).parameter = parameter ∧
      knownSeed (fun i => if i ∈ D.1 then none else some (x i)) = seeds := by
  obtain ⟨j, -, hj⟩ := firstInput_honest D x
  refine ⟨by rw [hj, hx j]; rfl, funext fun T => ?_⟩
  obtain ⟨i, hiT, hiD⟩ := main_exists_honest_holder D T
  have hsome : (C.parties.findSome? fun j => if j ∈ C.holders T then
      ((fun i => if i ∈ D.1 then none else some (x i)) j).map (·.seed T) else none).isSome := by
    rw [List.findSome?_isSome_iff]
    exact ⟨i, by simp [Committee.parties], by simp [hiT, hiD]⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some hv
  unfold knownSeed
  rw [hv]
  split_ifs at hk with hkT
  simp_all [dealtKeys]

/-- A handler that runs each local call on the free copy runs a computation of `H` on the free copy. -/
private theorem simulateQ_stateT_free_ro {σ L R α : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ (t : (LocalSpec C).Domain) st,
      (impl (.inl t)).run st = (fun a => (a, st)) <$> free (OracleComp.lift (OracleSpec.query t)))
    (p : OracleComp (RoSpec C) α) (st : σ) :
    (simulateQ impl (liftComp p (LocalSpec C + (L →ₒ R)))).run st =
      (fun a => (a, st)) <$> free (liftComp p (LocalSpec C)) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    have hq : simulateQ impl (liftComp (liftM (OracleSpec.query t) : OracleComp (RoSpec C) _)
        (LocalSpec C + (L →ₒ R))) = impl (.inl (.inr t)) := by
      rw [liftComp_def, simulateQ_query]
      simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
      erw [simulateQ_query]
      rcases t with q | x <;> exact id_map _
    rw [hq]
    erw [himpl (.inr t) st]
    simp only [bind_map_left, ih, liftComp_bind, free_bind, map_bind]
    rfl

/-- The ideal run of `F_ceremony` with a simulator. The functionality computes every output on the
free copy, and the simulator runs on the counted copy. -/
theorem idealExecution_Fceremony {σ : Type}
    (S : Simulator (C := C) (LocalSpec C) (Keys C) (PublicParameter × List (List Bit)) (Finset C.Party) σ)
    (x : C.Party → Keys C) (z : Aux) :
    idealExecution worldRoles.adversary D (Fceremony circuits jobs) S x z = (do
      let st ← worldRoles.adversary (S.start (corruptInputs D x) z)
      let outputs ← free (liftComp (jobs.mapM (evalJob circuits
        (firstInput fun i => if i ∈ D.1 then none else some (x i)).parameter
        (knownSeed fun i => if i ∈ D.1 then none else some (x i)))) (LocalSpec C))
      let a ← worldRoles.adversary (S.answer st
        ((firstInput fun i => if i ∈ D.1 then none else some (x i)).parameter, outputs))
      let out ← worldRoles.adversary (S.output a.1)
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ a.2 then some outputs else none)) := by
  unfold idealExecution Fceremony
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine bind_congr fun st => ?_
  rw [simulateQ_stateT_free_ro _ (by intros; rfl)]
  simp only [bind_map_left]
  refine bind_congr fun outputs => ?_
  have hleak {σ' L R : Type} (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ' (OracleComp (WorldSpec C))))
      (l : L) : simulateQ impl (leak (C := C) (R := R) l) = impl (.inr l) := by
    unfold leak
    exact (simulateQ_query _ _).trans (id_map _)
  rw [hleak]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  change ((worldRoles.adversary (S.answer st _) >>= fun p => pure (p.2, p.1)) >>= fun p =>
    worldRoles.adversary (S.output p.2) >>= fun out =>
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ p.1 then some outputs else none)) = _
  simp only [bind_assoc, pure_bind]

/-- The real run accepts as the common run with the opened outputs (GS20, Theorem 2). The fuel is the
steps of the batches and any more steps. -/
theorem ceremony_real_hybrid (hsize : 0 < settings.batchSize)
    (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (counters : ℕ × ℕ) (z : Aux)
    (Z : Distinguisher C A.State (List (List Bit))) (extra : ℕ) :
    accepts prims (distinguish (realExecution D A (mainFunctionalities K settings.mode)
        (hybridRounds circuits parameter (chunks settings.batchSize jobs) + extra)
        (fun i keys => ceremonyHybrid K circuits settings i keys counters jobs) x z) Z) =
      accepts prims (worldRoles.adversary (hybridCommon K circuits settings jobs D A x z parameter seeds) >>=
        fun r => worldRoles.adversary (Z r.2)) := by
  have hcore := mainRealHybridCore_of prims K (mainEngineReal prims K) (mainRealSim prims K)
  have hprog : (fun i => ceremonyHybrid K circuits settings i (x i) counters jobs) =
      restProgram K circuits settings.mode x (chunks settings.batchSize jobs) (fun _ => some []) := by
    funext i
    rw [ceremonyHybrid_eq]
    simp [restProgram]
  rw [main_accepts_eq_local prims _ ((A.start (corruptInputs D x) z >>= fun st =>
      executePhase localRoles D A (mainFunctionalities K settings.mode)
        (hybridRounds circuits parameter (chunks settings.batchSize jobs) + extra) st
        fun i => ceremonyHybrid K circuits settings i (x i) counters jobs) >>= Z) (by
      unfold distinguish realExecution
      simp only [simulateQ_bind, bind_assoc, main_simulateQ_executePhase, main_mapRoles_world,
        main_simulateQ_adversary]),
    main_accepts_eq_local prims _ (hybridCommon K circuits settings jobs D A x z parameter seeds >>= fun r => Z r.2)
      (by simp only [simulateQ_bind, main_simulateQ_adversary])]
  refine congrArg ENNReal.toReal (ObsEq.prob_eq ?_)
  rw [hprog]
  unfold hybridCommon
  simp only [bind_assoc]
  refine ObsEq.bind_right _ fun st => ?_
  rw [executePhase_batchAdversary]
  have h1 := engine prims K circuits settings.mode D (batchAdversary A) hcore hx (chunks settings.batchSize jobs)
    (fun _ => some []) st extra
  have h2 := lazyBatches_eager prims K circuits settings.mode D (batchAdversary A) (parameter := parameter)
    (knownSeed (corruptInputs D x))
    seeds (chunks settings.batchSize jobs) (fun _ => some []) st
  rw [chunks_flatten _ hsize] at h2
  refine ((h1.trans h2).bind_left Z).trans (ObsEq.of_eq ?_)
  exact bind_assoc _ _ _

/-- The ideal run accepts as the common run with the outputs of `F_ceremony`. -/
theorem ceremony_ideal_common (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (z : Aux)
    (Z : Distinguisher C A.State (List (List Bit))) :
    accepts prims (distinguish (idealExecution worldRoles.adversary D (Fceremony circuits jobs)
        (ceremonyHybridSimulator K circuits settings jobs D A) x z) Z) =
      accepts prims (worldRoles.adversary (hybridCommon K circuits settings jobs D A x z parameter seeds) >>=
        fun r => worldRoles.adversary (Z (ceremonyIdealOut D r))) := by
  obtain ⟨hparam, hseed⟩ := fceremony_dealt D hx
  refine (main_accepts_eq_local prims _
    (hybridCommon K circuits settings jobs D A x z parameter seeds >>= fun r => Z (ceremonyIdealOut D r)) ?_).trans
    (main_accepts_eq_local prims _
      (hybridCommon K circuits settings jobs D A x z parameter seeds >>= fun r => Z (ceremonyIdealOut D r))
      (by simp only [simulateQ_bind, main_simulateQ_adversary])).symm
  unfold distinguish
  rw [idealExecution_Fceremony, hparam, hseed]
  unfold hybridCommon ceremonyHybridSimulator ceremonyIdealOut
  simp [simulateQ_bind, main_simulateQ_adversary, worldAnswer, simulateQ_free, bind_assoc]

/-- The calls of the common run in the copy domain, the calls of the adversary and the copy hashes of
`OpenRep` of each batch. -/
theorem hybridCommon_copyBound (x : C.Party → Keys C) (z : Aux) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (Z : Distinguisher C A.State (List (List Bit))) (fuel q : ℕ)
    (hfuel : hybridRounds circuits parameter (chunks settings.batchSize jobs) ≤ fuel)
    (hq : IsQueryBounded A Z fuel q) :
    IsQueryBoundP (hybridCommon K circuits settings jobs D A x z parameter seeds) CopyCall
      (q + (chunks settings.batchSize jobs).length * termHashes C) := by
  obtain ⟨start, step, final, hsum, hstart, hround, hanswer, -⟩ := hq
  unfold hybridCommon
  refine (isQueryBoundP_bind ((hstart _ _).of_imp counted_of_copyCall) fun st _ =>
    isQueryBoundP_bind (evalJobs_copyBound circuits parameter jobs seeds) fun outputs _ =>
      isQueryBoundP_bind (simBatches_copyBound K circuits settings.mode D (batchAdversary A) parameter
        (knownSeed (corruptInputs D x)) step hanswer hround (chunks settings.batchSize jobs) outputs
        (fun _ => some []) st) fun r _ => isQueryBoundP_pure CopyCall (outputs, r) 0).mono ?_
  have := Nat.mul_le_mul_right step hfuel
  omega

/-- Each output of `F_ceremony` has the length of the outputs of its circuit. -/
private theorem evalJobs_forall₂ (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    ∀ (jobs : List Job) (outputs : List (List Bit)),
      outputs ∈ support (jobs.mapM (evalJob circuits parameter seeds)) →
      List.Forall₂ (fun (l : List Bit) (job : Job) => l.length = (circuits parameter job.kind).outputs.length)
        outputs jobs
  | [], o, h => by
    simp at h
    simp [h]
  | j :: js, o, h => by
    simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨b, hb, os, hos, rfl⟩ := h
    refine List.Forall₂.cons ?_ (evalJobs_forall₂ parameter seeds js os hos)
    simp only [evalJob, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hb
    obtain ⟨v, -, rfl⟩ := hb
    simp [Circuit.eval]

/-- The opened outputs are the outputs of `F_ceremony`, or two copy hashes collide. -/
theorem hybridCommon_sound (hsize : 0 < settings.batchSize) (x : C.Party → Keys C) (z : Aux)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    ∀ p ∈ support ((simulateQ (localAnswer prims)
        (hybridCommon K circuits settings jobs D A x z parameter seeds)).run ∅),
      p.1.2 ≠ ceremonyIdealOut D p.1 → MainCopyCollision p.2 := by
  intro p hp hne
  unfold hybridCommon at hp
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hp
  obtain ⟨a, -, o, ho, r, hr, rfl⟩ := hp
  have hout : o.1 ∈ support (jobs.mapM (evalJob circuits parameter seeds)) := by
    have h := support_simulateQ_run'_subset (localAnswer (C := C) prims)
      ((jobs.mapM (evalJob circuits parameter seeds)).liftComp (LocalSpec C)) a.2
      (by rw [StateT.run'_eq, support_map]; exact ⟨o, ho, rfl⟩)
    rwa [OracleComp.support_liftComp] at h
  have hlen := evalJobs_forall₂ circuits parameter seeds jobs o.1 hout
  rw [← chunks_flatten _ hsize jobs] at hlen
  obtain ⟨hD, hH⟩ := simBatches_inv prims K circuits settings.mode D (batchAdversary A) parameter
    (knownSeed (corruptInputs D x)) (chunks settings.batchSize jobs) o.1 (fun _ => some []) a.1 hlen o.2 r hr
  by_contra hcol
  refine hne (Prod.ext rfl (funext fun i => ?_))
  by_cases hi : i ∈ D.1
  · simp [ceremonyIdealOut, hi, hD i hi]
  · cases hri : r.1.2 i with
    | none => simp [ceremonyIdealOut, hri]
    | some u =>
      obtain ⟨o₀, ho₀, rfl⟩ := hH hcol i hi u hri
      simp_all [ceremonyIdealOut]

/-- The hybrid and the ideal run differ only when two copy hashes collide (MPClan, App. B). -/
theorem ceremony_hybrid_ideal (hsize : 0 < settings.batchSize) (x : C.Party → Keys C) (z : Aux)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (Z : Distinguisher C A.State (List (List Bit))) (fuel q : ℕ)
    (hfuel : hybridRounds circuits parameter (chunks settings.batchSize jobs) ≤ fuel)
    (hq : IsQueryBounded A Z fuel q) :
    |accepts prims (worldRoles.adversary (hybridCommon K circuits settings jobs D A x z parameter seeds) >>=
        fun r => worldRoles.adversary (Z r.2)) -
      accepts prims (worldRoles.adversary (hybridCommon K circuits settings jobs D A x z parameter seeds) >>=
        fun r => worldRoles.adversary (Z (ceremonyIdealOut D r)))| ≤
      (((q + (chunks settings.batchSize jobs).length * termHashes C) ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
  refine (main_abs_accepts_bind_sub_le prims _ _ _).trans ?_
  have h1 : Pr{let r ← runWorld prims (worldRoles.adversary
        (hybridCommon K circuits settings jobs D A x z parameter seeds))}[
        (worldRoles.adversary (Z r.1.2) : OracleComp (WorldSpec C) Bool) ≠
          worldRoles.adversary (Z (ceremonyIdealOut D r.1))] ≤
      Pr{let z ← (simulateQ (localAnswer prims)
        (hybridCommon K circuits settings jobs D A x z parameter seeds)).run ∅}[MainCopyCollision z.2] := by
    rw [main_probEvent_runWorld_fst prims _ (fun r => (worldRoles.adversary (Z r.2) : OracleComp (WorldSpec C) Bool) ≠
        worldRoles.adversary (Z (ceremonyIdealOut D r))), main_simulateQ_adversary, StateT.run'_eq, prEvent_map]
    exact prEvent_mono_of_support _ _ _ fun p hp hne =>
      hybridCommon_sound prims K circuits settings jobs D A hsize x z parameter seeds p hp fun heq =>
        hne (by simp only [heq])
  exact (ENNReal.toReal_mono (prEvent_ne_top _) h1).trans (copy_birthday prims _ _
    (hybridCommon_copyBound K circuits settings jobs D A x z parameter seeds Z fuel q hfuel hq))

/-- The ideal run makes at most `q + hybridOverhead` counted calls. The simulator makes one step of
the adversary for each step of a batch, the copy hashes of each batch, and one call for each known
term and point. -/
theorem ceremony_queryBound (hsize : 0 < settings.batchSize) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State (List (List Bit))) (fuel q : ℕ)
    (hfuel : ∀ parameter, hybridRounds circuits parameter (chunks settings.batchSize jobs) ≤ fuel)
    (hq : IsQueryBounded A Z fuel q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution worldRoles.adversary D
        (Fceremony circuits jobs) (ceremonyHybridSimulator K circuits settings jobs D A) x z) Z))
      (q + hybridOverhead settings C jobs) := by
  obtain ⟨start, step, final, hsum, hstart, hround, hanswer, hZ⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  simp only [bind_assoc]
  have hs : CostLe prims (worldRoles.adversary
      ((ceremonyHybridSimulator K circuits settings jobs D A).start (corruptInputs D x) z)) start :=
    CostLe.of_counted prims _ start
      ((isQueryBoundP_bind (hstart _ _) fun st _ => isQueryBoundP_pure Counted _ 0).mono (Nat.add_zero _).le)
  have ha := fun s l => CostLe.of_counted prims _ _
    (ceremonyHybridSimulator_answer_bound K circuits settings jobs D A hsize step fuel hanswer hround hfuel s l)
  refine CostLe.mono prims (CostLe.bind prims hs
    (m := 0 + ((fuel * step + hybridOverhead settings C jobs + 0) + (0 + (0 + (0 + final))))) fun st => ?_) ?_
  · unfold Fceremony
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine (costLe_liftComp_ro prims _ _ st).bind prims fun p => ?_
    refine (costLe_simulateQ_leak prims _ _ _ ?hl).bind prims fun r => ?_
    case hl => exact (ha _ _).bind prims fun _ => CostLe.pure prims _
    refine (CostLe.pure prims _).bind prims fun out => ?_
    refine (CostLe.of_counted prims _ 0 (isQueryBoundP_pure Counted _ 0)).bind prims fun o => ?_
    refine (CostLe.pure prims _).bind prims fun r' => ?_
    exact CostLe.of_counted prims _ _ (hZ _)
  · omega

end Games

section Final

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The steps of the batches of a ceremony fit in the fuel of the claim. -/
theorem hybridRounds_le_fuel (b : Fin (2 ^ layerHeight)) (encoding : Encoding) (jobs : List Job)
    (hjobs : jobs ∈ [topJobs, bottomJobs b, signJobs b encoding]) (parameter : PublicParameter) :
    hybridRounds circuits parameter (chunks settings.batchSize jobs) ≤
      ceremonyBatches settings * maxBatch circuits settings mainRounds := by
  have key : jobs = topJobs ∨ jobs = bottomJobs b ∨ jobs = signJobs b encoding := by
    rcases List.mem_cons.1 hjobs with h | h
    · exact Or.inl h
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (List.mem_singleton.1 h))
  have hmem : ∀ batch ∈ chunks settings.batchSize jobs, batch ∈ chunks settings.batchSize topJobs ∨
      batch ∈ chunks settings.batchSize (bottomJobs b) ∨ batch ∈ chunks settings.batchSize (signJobs b encoding) := by
    intro batch hb
    rcases key with h | h | h <;> rw [h] at hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
  have hlen : (chunks settings.batchSize jobs).length ≤ ceremonyBatches settings := by
    unfold ceremonyBatches
    rcases key with h | h | h <;> rw [h]
    · exact le_max_left _ _
    · rw [length_chunks settings.batchSize (bottomJobs b), length_bottomJobs, ← length_chunks]
      omega
    · rw [length_chunks_signJobs settings b 0 encoding (fun _ => digit 0)]
      omega
  exact (sum_map_le_length_mul _ _ _ fun batch hb => measure_le_maxBatch circuits settings mainRounds parameter
    b encoding batch (hmem batch hb)).trans (Nat.mul_le_mul_right _ hlen)

/-- One ceremony securely computes `F_ceremony` with selective abort in the
`{F_mult, F_multVerify}`-hybrid model (GS20, Theorem 2). -/
theorem ceremonyHybridSecurity : CeremonyHybridSecurityStatement prims K circuits settings := by
  intro hsize counters b encoding jobs hjobs D A
  refine ⟨ceremonyHybridSimulator K circuits settings jobs D A, fun x z Z q hx hq => ?_⟩
  obtain ⟨parameter, seeds, pairKeys, hx⟩ := hx
  have hfuel := hybridRounds_le_fuel circuits settings b encoding jobs hjobs
  refine ⟨ceremony_queryBound prims K circuits settings jobs D A hsize x z Z _ q hfuel hq, ?_⟩
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le (hfuel parameter)
  have hreal := ceremony_real_hybrid prims K circuits settings jobs D A hsize hx counters z Z extra
  rw [← hextra] at hreal
  rw [hreal, ceremony_ideal_common prims K circuits settings jobs D A hx z Z]
  exact ceremony_hybrid_ideal prims K circuits settings jobs D A hsize x z parameter seeds Z _ q
    (hfuel parameter) hq

end Final

end ThresholdLeanXmssSecurity
