import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Security

/-!
# Tools for the tree claim in the hybrid model

Each lemma is generic. It holds for every coalition and every adversary.

* `acc` is the accept probability of a local game, and `acc_obsEq` moves it along `ObsEq`.
* `obsEq_rerun` states that a computation of `H` that runs again gives its first value (BR93).
* `ceremony_cut` cuts a run at the end of one ceremony, from every state and every set of operators
  that still run (GS20, Theorem 2, with `engine` and `lazyBatches_eager`).
* `executePhase_search` is the local step between two ceremonies. Each operator that still runs
  computes one value of `H`. After a partial abort no operator gets an output.
* `executePhase_localOnly` is a phase with only local work.
* `hybridCommon_swap` changes the opened outputs of a ceremony to the outputs of the functionality, at
  the cost of the birthday bound of the copy hashes (MPClan, App. B).
* `tweakable_calls`, `merkleNode_calls` and `grind_calls` count the calls of the local steps of a tree.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-! ## Accept probabilities and repeated work -/

section Accept

variable (prims : Primitives)

/-- The accept probability of a local game. -/
def acc (G : OracleComp (LocalSpec C) Bool) : ℝ := accepts prims (worldRoles.adversary G)

theorem acc_obsEq {G G' : OracleComp (LocalSpec C) Bool} (h : ObsEq prims G G') : acc prims G = acc prims G' := by
  unfold acc
  rw [main_accepts_eq_local prims _ G (main_simulateQ_adversary prims G),
    main_accepts_eq_local prims _ G' (main_simulateQ_adversary prims G')]
  exact congrArg ENNReal.toReal h.prob_eq

/-- A computation of `H` that runs again after other work gives its first value. -/
theorem obsEq_rerun {β γ δ : Type} (u : OracleComp (RoSpec C) β) (M : β → OracleComp (LocalSpec C) γ)
    (k : β → γ → β → OracleComp (LocalSpec C) δ) :
    ObsEq prims
      (liftComp u (LocalSpec C) >>= fun a => M a >>= fun m => liftComp u (LocalSpec C) >>= fun a' => k a m a')
      (liftComp u (LocalSpec C) >>= fun a => M a >>= fun m => k a m a) := by
  have hdrop : ObsEq prims
      (liftComp u (LocalSpec C) >>= fun a => M a >>= fun m => liftComp u (LocalSpec C) >>= fun _ => k a m a)
      (liftComp u (LocalSpec C) >>= fun a => M a >>= fun m => k a m a) :=
    ObsEq.bind_right _ fun a => ObsEq.bind_right _ fun m => obsEq_drop prims _ _
  refine ObsEq.trans ?_ hdrop
  intro s hs ε k'
  simp only [bind_assoc, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun p hp => ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun q hq => ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun r hr => ?_
  obtain ⟨-, hn1, hd1⟩ := localRun_support (prims := prims) _ s p hp
  obtain ⟨hle2, hn2, -⟩ := localRun_support (prims := prims) _ p.2 q hq
  obtain ⟨hle3, hn3, hd3⟩ := localRun_support (prims := prims) _ q.2 r hr
  have hn := hn3 (hn2 (hn1 hs))
  have hg := good_hashOf prims r.2
  have ha := agrees_hashOf prims hn
  have e1 := hd1 _ hg ((ha.mono hle3).mono hle2)
  have e3 := hd3 _ hg ha
  rw [simulateQ_fixedLocal_liftComp, support_pure, Set.mem_singleton_iff] at e1 e3
  rw [e3, ← e1]

/-- The value of a sequence of computations of `H` with `H` fixed. -/
theorem valueAt_sequenceFin (h : Query C → HashOutput) {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (RoSpec C) α),
      ThresholdLeanXmssSecurity.D prims h (OverPermutation.sequenceFin f) = fun i => ThresholdLeanXmssSecurity.D prims h (f i)
  | 0, f => by funext i; exact i.elim0
  | n + 1, f => by
    rw [OverPermutation.sequenceFin, D_bind, D_bind, valueAt_sequenceFin h, D_pure]
    funext i
    cases i using Fin.cases <;> rfl

end Accept

/-! ## Phases -/

section Phases

variable (prims : Primitives) {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
  (F : Functionality C I O L R)

/-- The local step between two phases. Each operator that still runs computes the value `u` of `H`
and continues with it. If an honest operator does not run, and the next step of each other operator
is a call, no operator gets an output and the adversary gets no step. -/
theorem executePhase_search {β γ : Type} (d : γ) (fuel : ℕ) (st : A.State) (pre : C.Party → Option β)
    (u : OracleComp (RoSpec C) γ) (prog : C.Party → γ → PartyM C E (CallSpec I O) α)
    (hcall : ∀ i w, ∀ step ∈ support (advance (prog i w).run), step = .done none ∨
      ∃ input resume, step = .call input resume ∧ advance (resume none) = pure (.done none)) :
    ObsEq prims
      (executePhase localRoles D A F fuel st (fun i => (pre i).elim failure fun _ => oracleStep u >>= prog i))
      (if ∀ i, i ∉ D.1 → (pre i).isSome then
        liftComp u (LocalSpec C) >>= fun w =>
          executePhase localRoles D A F fuel st (fun i => (pre i).elim failure fun _ => prog i w)
       else pure (st, fun _ => none)) := by
  split_ifs with halive
  · have h1 := executePhase_congr D A F fuel st
      (fun i => (pre i).elim failure fun _ => oracleStep u >>= prog i) (fun i => oracleStep u >>= prog i)
      fun i hi => by
        obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (halive i hi)
        simp only [ho, Option.elim]
    rw [h1]
    refine (executePhase_oracleStep_bind prims D A F d fuel st (fun _ => u) prog).obsEq.trans ?_
    refine obsEq_hash prims _ u _ _ fun h _ => ObsEq.of_eq ?_
    refine executePhase_congr D A F fuel st _ _ fun i hi => ?_
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (halive i hi)
    simp only [ho, Option.elim, valueAt_sequenceFin, hi, ↓reduceIte]
  · have hex : ∃ i, i ∉ D.1 ∧ ((pre i).elim failure fun _ => oracleStep u >>= prog i) = failure := by
      push Not at halive
      obtain ⟨i, hi, hpre⟩ := halive
      refine ⟨i, hi, ?_⟩
      have hnone : pre i = none := by simpa using hpre
      simp only [hnone, Option.elim]
    refine (executePhase_partial prims D A F fuel st _ hex fun i _ step hs => ?_).obsEq.trans
      (obsEq_drop prims _ _)
    cases hpre : pre i with
    | none =>
      rw [hpre] at hs
      simp only [Option.elim] at hs
      rw [advance_run_failure, support_pure, Set.mem_singleton_iff] at hs
      exact Or.inl hs
    | some o =>
      rw [hpre] at hs
      simp only [Option.elim] at hs
      rw [advance_oracleStep_bind, mem_support_bind_iff] at hs
      obtain ⟨w, -, hs⟩ := hs
      exact hcall i w step hs

/-- A phase with only local work. Each honest operator computes one value of `H`, and it has an
output when the value is not `none`. -/
theorem executePhase_localOnly (fuel : ℕ) (st : A.State) (q : C.Party → OracleComp (RoSpec C) (Option α)) :
    executePhase localRoles D A F fuel st (fun i => oracleStep (q i) >>= fun r => r.elim failure pure) =
      liftComp (OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure none else q i) (LocalSpec C) >>=
        fun outs => pure (st, outs) := by
  have hadv : ∀ i, advance (oracleStep (q i) >>= fun r => (r.elim failure pure : PartyM C E (CallSpec I O) α)).run =
      liftComp (q i) (LocalSpec C) >>= fun r => pure (.done r) := by
    intro i
    rw [advance_oracleStep_bind]
    refine bind_congr fun r => ?_
    cases r <;> rfl
  have hl : liftComp (OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure none else q i) (LocalSpec C) =
      OverPermutation.sequenceFin fun i =>
        liftComp (if i ∈ D.1 then pure none else q i) (LocalSpec C) := simulateQ_sequenceFin _ _
  have hs : startSteps localRoles D (fun i => oracleStep (q i) >>= fun r => (r.elim failure pure : PartyM C E (CallSpec I O) α)) =
      OverPermutation.sequenceFin (fun i => liftComp (if i ∈ D.1 then pure none else q i) (LocalSpec C) >>=
        fun r => pure ((fun _ r => Step.done r) i r)) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp only [hi, ↓reduceIte, liftComp_pure, pure_bind]
    · simp only [hi, ↓reduceIte, localRoles, hadv]
  unfold executePhase
  rw [hs, sequenceFin_bind_pure, hl, bind_assoc]
  refine bind_congr fun rs => ?_
  rw [pure_bind]
  exact stages_executeRounds_allDone D A F fuel st (fun i => Step.done (rs i)) fun i => trivial

end Phases

/-! ## One ceremony from every state -/

section Ceremony

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (mode : ReshareMode)
  (D : C.Coalition) (A : MainAdversary C E)
  {x : C.Party → Keys C} {parameter : PublicParameter} {seeds : C.Term → HashOutput}
  {pairKeys : C.Pair → HashOutput}

/-- The batches of a ceremony take the steps of their batches. -/
theorem timed_hybridBatches (i : C.Party) (keys : Keys C) : ∀ bs : List (List Job),
    Timed (hybridRounds circuits keys.parameter bs) (hybridBatches K circuits mode i keys bs).run
  | [] => timed_pure _
  | batch :: rest => by
    have h := (timed_hybridBatch K circuits mode i keys batch).bind fun out =>
      (timed_hybridBatches i keys rest).bind fun outs => timed_pure (out ++ outs)
    simpa only [hybridBatches, hybridRounds, List.map_cons, List.sum_cons, Nat.add_zero] using h

/-- The cut at the end of one ceremony (GS20, Theorem 2). From every state, the operators with a value
in `pre` run the batches `bs` and then the programs `k`. The run is the outputs of the jobs, the
simulator of the batches, and then the programs `k` at each operator with an output. -/
theorem ceremony_cut {α : Type} (hcore : MainRealHybridCore prims K)
    (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (bs : List (List Job))
    (pre : C.Party → Option (List (List Bit))) (st : A.State) (extra : ℕ)
    (k : C.Party → List (List Bit) → PartyM C E (MainSpec C) α) :
    ObsEq prims
      (executePhase localRoles D A (mainFunctionalities K mode) (hybridRounds circuits parameter bs + extra) st
        (fun i => (pre i).elim failure fun _ => hybridBatches K circuits mode i (x i) bs >>= k i))
      (liftComp (bs.flatten.mapM (evalJob circuits parameter seeds)) (LocalSpec C) >>= fun outputs =>
        simBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) bs outputs
          (fun i => (pre i).map fun _ => []) st >>= fun r =>
        executePhase localRoles D A (mainFunctionalities K mode) extra r.1
          (fun i => (r.2 i).elim failure (k i))) := by
  have hprog : (fun i => (pre i).elim failure fun _ => hybridBatches K circuits mode i (x i) bs >>= k i) =
      fun i => restProgram K circuits mode x bs (fun j => (pre j).map fun _ => []) i >>= k i := by
    funext i
    unfold restProgram
    dsimp only
    cases pre i with
    | none => simp only [Option.map_none, Option.elim_none, failure_bind]
    | some o => simp only [Option.map_some, Option.elim_some, List.nil_append, id_map']
  have htimed : ∀ i, i ∉ D.1 → Timed (hybridRounds circuits parameter bs)
      (restProgram K circuits mode x bs (fun j => (pre j).map fun _ => []) i).run := by
    intro i _
    unfold restProgram
    dsimp only
    cases pre i with
    | none => exact timed_failure _
    | some o =>
      have h := (timed_hybridBatches K circuits mode i (x i) bs).map (([] : List (List Bit)) ++ ·)
      rw [show (x i).parameter = parameter by rw [hx i]; rfl] at h
      simpa only [Option.map_some, Option.elim_some] using h
  rw [hprog]
  refine (executePhase_bind prims D A _ _ extra st _ k htimed).obsEq.trans ?_
  have heng := engine prims K circuits mode D A hcore hx bs (fun j => (pre j).map fun _ => []) st 0
  rw [Nat.add_zero] at heng
  have he := lazyBatches_eager prims K circuits mode D A (parameter := parameter)
    (knownSeed (corruptInputs D x)) seeds bs (fun j => (pre j).map fun _ => []) st
  have h := (heng.trans he).bind_left fun r =>
    executePhase localRoles D A (mainFunctionalities K mode) extra r.1 (fun i => (r.2 i).elim failure (k i))
  simpa only [bind_assoc] using h

end Ceremony

/-! ## Opened outputs and the outputs of the functionality -/

section Swap

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (jobs : List Job) (D : C.Coalition) (A : CeremonyAdversary C E)

/-- After one ceremony, each continuation accepts with the opened outputs as with the outputs of the
functionality, up to the birthday bound of the copy hashes (MPClan, App. B). `Z` gives only the
budget of the adversary. -/
theorem hybridCommon_swap (hsize : 0 < settings.batchSize) (x : C.Party → Keys C) (z : Aux)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (Z : Distinguisher C A.State (List (List Bit))) (fuel q : ℕ)
    (hfuel : hybridRounds circuits parameter (chunks settings.batchSize jobs) ≤ fuel)
    (hq : IsQueryBounded A Z fuel q)
    (k : A.State × (C.Party → Option (List (List Bit))) → OracleComp (LocalSpec C) Bool) :
    |acc prims (hybridCommon K circuits settings jobs D A x z parameter seeds >>= fun r => k r.2) -
      acc prims (hybridCommon K circuits settings jobs D A x z parameter seeds >>= fun r =>
        k (ceremonyIdealOut D r))| ≤
      (((q + (chunks settings.batchSize jobs).length * termHashes C) ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
  unfold acc
  rw [main_worldRoles_bind, main_worldRoles_bind]
  refine (main_abs_accepts_bind_sub_le prims _ _ _).trans ?_
  have h1 : Pr{let r ← runWorld prims (worldRoles.adversary
        (hybridCommon K circuits settings jobs D A x z parameter seeds))}[
        (worldRoles.adversary (k r.1.2) : OracleComp (WorldSpec C) Bool) ≠
          worldRoles.adversary (k (ceremonyIdealOut D r.1))] ≤
      Pr{let z ← (simulateQ (localAnswer prims)
        (hybridCommon K circuits settings jobs D A x z parameter seeds)).run ∅}[MainCopyCollision z.2] := by
    rw [main_probEvent_runWorld_fst prims _ (fun r => (worldRoles.adversary (k r.2) : OracleComp (WorldSpec C) Bool) ≠
        worldRoles.adversary (k (ceremonyIdealOut D r))), main_simulateQ_adversary, StateT.run'_eq, prEvent_map]
    exact prEvent_mono_of_support _ _ _ fun p hp hne =>
      hybridCommon_sound prims K circuits settings jobs D A hsize x z parameter seeds p hp fun heq =>
        hne (by simp only [heq])
  exact (ENNReal.toReal_mono (prEvent_ne_top _) h1).trans (copy_birthday prims _ _
    (hybridCommon_copyBound K circuits settings jobs D A x z parameter seeds Z fuel q hfuel hq))

end Swap

/-! ## The calls of the local steps of a tree -/

section Calls

/-- A computation of leanXMSS on the domain `Th` makes one call of `H` for each of its calls. -/
theorem tweakable_calls {α : Type} (p : (RoSpec C).Domain → Prop) (oa : OracleComp HashSpec α) :
    ∀ n, IsQueryBoundP oa (fun _ => True) n → IsQueryBoundP (tweakable (C := C) oa) p n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    have hn : 0 < n := h.1.resolve_left fun hf => hf trivial
    have hk := fun u => ih u (n - 1) (by simpa using h.2 u)
    have ht : tweakable (C := C) (liftM (HashSpec.query t) >>= k) =
        hashQuery (.hash t) >>= fun u => tweakable (k u) := by
      simp only [tweakable, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
    rw [ht]
    refine (isQueryBoundP_bind (n := 1) (m := n - 1) ?_ fun u _ => hk u).mono (by omega)
    unfold hashQuery
    erw [isQueryBoundP_query_iff]
    exact fun _ => Nat.one_pos

/-- One tweakable hash is one call. -/
theorem tweakableHash_calls (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    IsQueryBoundP (Verification.tweakableHashWithHash parameter domain payload : OracleComp HashSpec Digest)
      (fun _ => True) 1 := by
  unfold Verification.tweakableHashWithHash Verification.thWithHash Verification.oracleHashWithHash
  exact isQueryBoundP_bind (n := 1) (m := 0) ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    fun _ _ => isQueryBoundP_pure _ _ _

/-- A node at `level` costs one call for each node of its subtree. -/
theorem merkleNode_calls (parameter : PublicParameter) (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest) :
    ∀ level idx, IsQueryBoundP (merkleNode parameter lay chainEnd level idx) (fun _ => True)
      (2 ^ (level + 1) - 1) := by
  intro level
  induction level with
  | zero =>
    intro idx
    exact tweakableHash_calls parameter _ _
  | succ level ih =>
    intro idx
    rw [merkleNode]
    refine (isQueryBoundP_bind (ih _) fun _ _ => isQueryBoundP_bind (ih _) fun _ _ =>
      tweakableHash_calls parameter _ _).mono ?_
    have := Nat.one_le_two_pow (n := level + 1)
    rw [pow_succ 2 (level + 1)]
    omega

/-- A randomizer search costs one call for each trial. -/
theorem grind_calls (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (base : Randomizer) : ∀ attempts trial,
    IsQueryBoundP (grind parameter lay key message base attempts trial) (fun _ => True) attempts
  | 0, _ => isQueryBoundP_pure _ _ _
  | attempts + 1, trial => by
    rw [grind]
    refine (isQueryBoundP_bind (n := 1) (m := attempts) (tweakableHash_calls parameter _ _) fun _ _ => ?_).mono
      (by omega)
    split
    · exact isQueryBoundP_pure _ _ _
    · exact grind_calls parameter lay key message base attempts (trial + 1)

end Calls

end ThresholdLeanXmssSecurity
