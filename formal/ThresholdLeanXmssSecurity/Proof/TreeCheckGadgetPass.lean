import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling
import ThresholdLeanXmssSecurity.Proof.Check

/-! # Substitution of ready draws in a stream-world local pass
Local substitutions preserve both caches and all subsequent rounds. Hash prefixes
are separated after the continuation is pure up to its next suspension. The
existing `treeSim_coin_start` and `treeSim_extendMult_start` provide the ready
coin and peer entries. A stopped real execution makes the original `Final`
predicate vacuous, independently of the hybrid execution.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckGadgetPass
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} (prims : Primitives)

-- Ported from TreeTwinPassPrefill:17–49 to avoid the independent tree-track imports.
private theorem hidden_query_grows (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : HashCache C × HiddenCache C) (r : (WorldSpec C).Range t × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((streamWorld prims D t).run s)) : s.2 ≤ r.2.2 := by
  have onhash {α : Type} (m : StateT (HashCache C) ProbComp α)
      (z : α × (HashCache C × HiddenCache C)) (hz : z ∈ support ((onHash m).run s)) : s.2 ≤ z.2.2 := by
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact le_rfl
  rcases t with t | n | q | x
  · exact onhash _ r hr
  · exact onhash _ r hr
  · exact onhash _ r hr
  · by_cases hidden : Hidden D x.1
    · simp only [streamWorld, hidden, if_true, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      exact QueryImpl.withCaching_cache_le _ _ _ _ hu
    · simp only [streamWorld, hidden, if_false] at hr
      exact onhash _ r hr

/-- Hidden entries survive arbitrary stream-world programs. -/
theorem treeSim_hidden_grows {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (s : HashCache C × HiddenCache C) (r : α × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) p).run s)) : s.2 ≤ r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact le_rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      support_bind, Set.mem_iUnion] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact (hidden_query_grows prims D t s u hu).trans (ih u.1 u.2 r hr)

/-- Local pass equalities compose while retaining both installed caches. -/
theorem stream_localPass_congr (D : C.Coalition) {β : Type}
    (base : HashCache C) (inst : HiddenCache C) :
    ∀ {n : ℕ} (left right : Fin n → OracleComp (WorldSpec C) β)
      (_same : ∀ i s, base ≤ s.1 → inst ≤ s.2 →
        (simulateQ (streamWorld prims D) (left i)).run s =
          (simulateQ (streamWorld prims D) (right i)).run s)
      (s : HashCache C × HiddenCache C), base ≤ s.1 → inst ≤ s.2 →
      (simulateQ (streamWorld prims D) (Concrete.sequenceFin left)).run s =
        (simulateQ (streamWorld prims D) (Concrete.sequenceFin right)).run s
  | 0, left, right, same, s, grows, installed => rfl
  | n + 1, left, right, same, s, grows, installed => by
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rw [same 0 s grows installed]
      apply bind_congr_of_forall_mem_support
      intro r hr
      rw [stream_localPass_congr D base inst (fun i : Fin n => left i.succ) (fun i => right i.succ)
        (fun i => same i.succ) r.2
        (grows.trans (treeSim_stream_grows prims D (right 0) s r hr))
        (installed.trans (treeSim_hidden_grows prims D (right 0) s r hr))]



open TreeCheckKernelCoupling
variable {E : Type} {α β X : Type} (D : C.Coalition)

/-- A ready draw is replaced together with its exact unchanged stream state. -/
theorem advance_ready_bind (d : OracleComp (RoSpec C) X) (r : X)
    (k : X → PartyM C E RealSpec β) (s : HashCache C × HiddenCache C)
    (ready : (simulateQ (streamWorld prims D) (free (liftComp d (LocalSpec C)))).run s =
      pure (r, s)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (oracleStep d >>= k).run))).run s =
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (k r).run))).run s := by
  simp only [worldRoles, advance_oracleStep_bind, free_bind, simulateQ_bind, StateT.run_bind]
  rw [ready, pure_bind]

/-- Readiness persists through a hash prefix because both caches only grow. -/
theorem advance_prefix_ready_bind (base : HashCache C) (inst : HiddenCache C)
    (W : OracleComp (Query C →ₒ HashOutput) X)
    (d : X → OracleComp (RoSpec C) α) (r : X → α)
    (k : X → α → PartyM C E RealSpec β)
    (ready : ∀ x s, base ≤ s.1 → inst ≤ s.2 →
      (simulateQ (streamWorld prims D) (free (liftComp (d x) (LocalSpec C)))).run s =
        pure (r x, s))
    (s : HashCache C × HiddenCache C) (grows : base ≤ s.1) (installed : inst ≤ s.2) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (oracleStep (liftComp W (RoSpec C)) >>= fun x => oracleStep (d x) >>= k x).run))).run s =
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (oracleStep (liftComp W (RoSpec C)) >>= fun x => k x (r x)).run))).run s := by
  simp only [worldRoles, advance_oracleStep_bind, free_bind, simulateQ_bind, StateT.run_bind]
  apply bind_congr_of_forall_mem_support
  intro z hz
  rw [ready z.1 z.2 (grows.trans (treeSim_stream_grows prims D _ s z hz))
    (installed.trans (treeSim_hidden_grows prims D _ s z hz)), pure_bind]

/-- The state-monad randomness operation exposes the same ready draw and next label. -/
theorem advance_prssRandomness_ready_bind [Field E] [Algebra Bit E] {R : Type} [Zero R]
    (ctx : Context C) (codec : Codec C E R) (idx count : ℕ)
    (f : PrssOutput C R → RunM C E RealSpec β) (st : RunState C)
    (rnd : PrssOutput C R) (s : HashCache C × HiddenCache C)
    (ready : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx codec st.label idx count) (LocalSpec C)))).run s = pure (rnd, s)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((prssRandomness ctx codec idx count >>= f).run st).run))).run s =
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((f rnd).run (nextLabel st)).run))).run s := by
  rw [prssRandomness_run]
  exact advance_ready_bind prims D _ rnd _ s ready

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- Equal first local passes preserve the entire subsequent real execution. -/
theorem realRun_localPass_congr (base : HashCache C) (inst : HiddenCache C)
    (P Q : C.Party → PartyM C E RealSpec β)
    (same : ∀ i, i ∉ D.1 → ∀ s, base ≤ s.1 → inst ≤ s.2 →
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (P i).run))).run s =
        (simulateQ (streamWorld prims D) (worldRoles.honest (advance (Q i).run))).run s)
    (n : ℕ) (stA : A.State) (s : HashCache C × HiddenCache C)
    (grows : base ≤ s.1) (installed : inst ≤ s.2) :
    realRun prims D A n stA P s = realRun prims D A n stA Q s := by
  have starts : (simulateQ (streamWorld prims D) (startSteps worldRoles D P)).run s =
      (simulateQ (streamWorld prims D) (startSteps worldRoles D Q)).run s := by
    apply stream_localPass_congr prims D base inst _ _ _ s grows installed
    intro i t ht hc
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
    · simp only [if_neg hi]
      exact same i hi t ht hc
  simp only [realRun, simulateQ_bind, StateT.run_bind, starts]

/-- Replace ready draws for every honest operator before executing the same rounds. -/
theorem realRun_ready_subst (base : HashCache C) (inst : HiddenCache C)
    (d : C.Party → OracleComp (RoSpec C) X) (r : C.Party → X)
    (k : C.Party → X → PartyM C E RealSpec β)
    (ready : ∀ i, i ∉ D.1 → ∀ s, base ≤ s.1 → inst ≤ s.2 →
      (simulateQ (streamWorld prims D) (free (liftComp (d i) (LocalSpec C)))).run s = pure (r i, s))
    (n : ℕ) (stA : A.State) (s : HashCache C × HiddenCache C)
    (grows : base ≤ s.1) (installed : inst ≤ s.2) :
    realRun prims D A n stA (fun i => oracleStep (d i) >>= k i) s =
      realRun prims D A n stA (fun i => k i (r i)) s := by
  apply realRun_localPass_congr prims D A base inst _ _ _ n stA s grows installed
  intro i hi t ht hc
  exact advance_ready_bind prims D (d i) (r i) (k i) t (ready i hi t ht hc)

/-- The real hash prefix leaves the hidden cache unchanged and retains all later rounds. -/
theorem realRun_prefix (n : ℕ) (stA : A.State)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (gR : C.Party → X → PartyM C E RealSpec β) (sR : C.Party → X → Step C E RealSpec β)
    (pureR : ∀ i x, advance (gR i x).run = pure (sR i x))
    (h : HashCache C) (c : HiddenCache C) :
    realRun prims D A n stA (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gR i) (h, c) =
      ((simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        (fun out => (out.1, out.2.1)) <$> (simulateQ (streamWorld prims D)
          (executeSteps worldRoles D A noFunctionality n stA (prefixSteps sR r.1))).run (r.2, c)) := by
  unfold realRun
  rw [startSteps_world_prefix D W gR sR pureR]
  simp only [simulateQ_bind, StateT.run_bind, bind_map_left, map_bind]
  rw [hashPrefix_run prims D W h c, bind_map_left]

/-- The hybrid prefix has exactly the same hash-only sampling law. -/
theorem hybRun_prefix (Ad : CheckAdversary C E (List (Tuple C))) (n : ℕ) (st : Ad.State)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (gH : C.Party → X → PartyM C E (CheckSpec C E) Unit)
    (sH : C.Party → X → Step C E (CheckSpec C E) Unit)
    (pureH : ∀ i x, advance (gH i x).run = pure (sH i x)) (h : HashCache C) :
    hybRun prims K D Ad n st (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gH i) h =
      ((simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        letI : SampleableType E := SampleableType.ofFintype E
        (simulateQ (localAnswer prims)
          (executeRounds localRoles D Ad (checkFunctionalities K) n st (prefixSteps sH r.1))).run r.2) := by
  unfold hybRun executePhase
  rw [startSteps_local_prefix D W gH sH pureH]
  simp only [simulateQ_bind, StateT.run_bind, bind_map_left]

/-- An independent table draw commutes with the complete hash prefix. -/
theorem prefix_sample_comm [SampleableType α]
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X) (h : HashCache C)
    (k : α → ((C.Party → Option X) × HashCache C) → ProbComp β) :
    𝒟[($ᵗ α) >>= fun vals => (simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= k vals] =
      𝒟[(simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r => ($ᵗ α) >>= fun vals => k vals r] := by
  exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

/-- Once the real exchange stops everyone, Final holds against every hybrid run. -/
theorem doomed_post (Ad : CheckAdversary C E (List (Tuple C))) (n n' : ℕ)
    (stA : A.State) (st : Ad.State) (P : C.Party → PartyM C E RealSpec β)
    (Q : C.Party → PartyM C E (CheckSpec C E) Unit)
    (w : HashCache C × HiddenCache C) (h : HashCache C)
    (exchange : ∀ i, i ∉ D.1 → TreeSimCheckExchange (P i))
    (dead : ∃ j, j ∉ D.1 ∧ P j = failure) :
    RelTriple (realRun prims D A (n + 1) stA P w)
      (hybRun prims K D Ad (n' + 1) st Q h) (Final D A) := by
  apply relTriple_of_support
  intro a ha b hb i hi alive
  exact (alive (realRun_doomed prims D A n stA P w exchange dead a ha i hi)).elim

/-- Failure programs have already stopped before the first round. -/
theorem realRun_failure (n : ℕ) (stA : A.State)
    (P : C.Party → PartyM C E RealSpec β) (failed : ∀ i, i ∉ D.1 → P i = failure)
    (s : HashCache C × HiddenCache C) :
    realRun prims D A n stA P s = pure ((stA, fun _ => Step.done none), s.1) := by
  have start : startSteps worldRoles D P = pure (fun _ => Step.done none) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp [hi, failed i hi, worldRoles, advance_pure, free_pure]
  unfold realRun
  rw [start, pure_bind, executeSteps_done worldRoles D A noFunctionality n stA
    (fun _ => Step.done none) (fun _ _ => trivial)]
  simp

/-- Failure at every honest real operator makes the original Final predicate vacuous. -/
theorem coupled_failure (x : C.Party → Keys C) (prss : C.Party → PrssKeys C)
    (cache0 : HashCache C) (label0 n n' ℓ : ℕ)
    (P : C.Party → PartyM C E RealSpec β) (Q : C.Party → PartyM C E (CheckSpec C E) Unit)
    (failed : ∀ i, i ∉ D.1 → P i = failure) :
    Coupled prims K D A x prss cache0 label0 n n' ℓ P Q := by
  intro stA h c _ _
  rw [realRun_failure prims D A n stA P failed (h, c)]
  apply relTriple_of_support
  intro a ha b hb
  have he := (mem_support_pure_iff _ _).mp ha
  subst a
  intro i hi alive
  exact (alive rfl).elim

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.treeSim_hidden_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_hidden_grows

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.stream_localPass_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stream_localPass_congr

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.advance_ready_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms advance_ready_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.advance_prefix_ready_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms advance_prefix_ready_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.advance_prssRandomness_ready_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms advance_prssRandomness_ready_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.realRun_ready_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_ready_subst

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.realRun_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.hybRun_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hybRun_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.prefix_sample_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_sample_comm

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.doomed_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms doomed_post

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetPass.coupled_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_failure

end ThresholdLeanXmssSecurity.TreeCheckGadgetPass
