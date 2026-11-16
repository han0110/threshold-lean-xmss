import ThresholdLeanXmssSecurity.Proof.TreeHybrid.Top

/-!
# A bottom tree in the hybrid model

A bottom tree has two ceremonies. The codeword of the signature ceremony comes from the opened outputs
of the first ceremony, so the proof changes opened outputs to the outputs of the dealer two times.

* `bottom_cut_acc` cuts the real run at the end of the first ceremony (`ceremony_cut`).
* `hybridCommon_swap` gives each operator with an output the outputs of the dealer. Then all operators
  that still run compute one codeword.
* `bottomRest_obsEq` is the rest of the run from that state. It is the search (`executePhase_search`),
  the cut of the signature ceremony (`ceremony_cut`) and the check of each operator
  (`executePhase_localOnly`). After a partial abort of the first ceremony no operator gets an output.
* `bottom_swap2` changes the opened chain values to the chain values of the dealer.
* `bottom_ideal_acc` moves the work of the dealer to the time of its use (`sameRun_swap`, `obsEq_drop`,
  `obsEq_rerun`).
* `bottom_distance` is the distance of the real run and the ideal run.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

section Bottom

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (A : CeremonyAdversary C E)

/-- The run of a bottom tree after its first ceremony. Operator `i` continues from its outputs `pre i`,
and an operator with no output does not start. -/
def bottomRestRun (x : C.Party → Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight)) (fuel : ℕ) (st : A.State)
    (pre : C.Party → Option (List (List Bit))) : OracleComp (LocalSpec C) (A.State × (C.Party → Option TreeOutput)) :=
  executePhase localRoles D (batchAdversary A) (mainFunctionalities K settings.mode) fuel st
    (fun i => (pre i).elim failure (bottomTail K circuits settings i (x i) top b))

/-- The run of a bottom tree after its first ceremony in the form of the simulator, when each operator
that still runs has the outputs `o₁`. With `ideal`, each operator with chain values has the chain
values of the dealer. -/
def bottomMid (x : C.Party → Keys C) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (ideal : Bool) (o₁ : List (List Bit)) (st : A.State)
    (pre : C.Party → Option (List (List Bit))) : OracleComp (LocalSpec C) (A.State × (C.Party → Option TreeOutput)) :=
  if ∀ i, i ∉ D.1 → (pre i).isSome then
    liftComp (bottomSearch (C := C) parameter b o₁) (LocalSpec C) >>= fun w =>
    match w.2 with
    | none => pure (st, fun _ => none)
    | some re =>
      liftComp ((signJobs b re.2).mapM (evalJob circuits parameter seeds)) (LocalSpec C) >>= fun o₂ =>
      simBatches K circuits settings.mode D (batchAdversary A) parameter (knownSeed (corruptInputs D x))
        (chunks settings.batchSize (signJobs b re.2)) o₂ (fun i => (pre i).map fun _ => []) st >>= fun r₂ =>
      localFinish D (bottomCheck parameter top b o₁ w.1 re.1) r₂.1
        (if ideal then fun i => if i ∉ D.1 ∧ (r₂.2 i).isSome then some o₂ else none else r₂.2)
  else pure (st, fun _ => none)

variable {x : C.Party → Keys C} {parameter : PublicParameter} {seeds : C.Term → HashOutput}
  {pairKeys : C.Pair → HashOutput}

/-- The real run of a bottom tree is the common run of its first ceremony and then the rest of the run
from the opened outputs. -/
theorem bottom_cut_acc (hsize : 0 < settings.batchSize) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (z : Aux) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (Z : Distinguisher C A.State TreeOutput) (e : ℕ) :
    acc prims (treeRealLocal K circuits settings D A x z top (.bottom b)
        (hybridRounds circuits parameter (chunks settings.batchSize (bottomJobs b)) + e) >>= Z) =
      acc prims (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>= fun r =>
        bottomRestRun K circuits settings D A x top b e r.2.1 r.2.2 >>= Z) := by
  have hprog : (fun i => newTreeHybrid K circuits settings i (x i) top (.bottom b)) = fun i =>
      (some ([] : List (List Bit))).elim failure fun _ =>
        newTreeHybrid K circuits settings i (x i) top (.bottom b) := by
    funext i
    rw [Option.elim_some]
  have hcore := mainRealHybridCore_of prims K (mainEngineReal prims K) (mainRealSim prims K)
  refine acc_obsEq prims ?_
  unfold treeRealLocal hybridCommon bottomRestRun
  simp only [bind_assoc]
  refine ObsEq.bind_right _ fun st => ?_
  rw [hprog, executePhase_batchAdversary]
  simp only [newTreeHybrid_bottom]
  refine ((ceremony_cut prims K circuits settings.mode D (batchAdversary A) hcore hx _ (fun _ => some []) st
    e _).bind_left Z).trans (ObsEq.of_eq ?_)
  rw [chunks_flatten _ hsize]
  exact (bind_assoc _ _ _).trans (bind_congr fun o => (bind_assoc _ _ _).trans (bind_congr fun r => by
    rw [pure_bind]
    exact rfl))

omit [Field E] [Algebra Bit E] in
/-- A phase with only local work, where an operator with no value does not start. Each honest operator
with a value computes one value of `H`, and it has an output when the value is not `none`. -/
private theorem executePhase_finish {I O L R Ia α β : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (v : C.Party → Option β)
    (q : C.Party → β → OracleComp (RoSpec C) (Option α)) :
    executePhase localRoles D A F fuel st
        (fun i => (v i).elim failure fun a => oracleStep (q i a) >>= fun r => r.elim failure pure) =
      liftComp (OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure none else (v i).elim (pure none) (q i))
        (LocalSpec C) >>= fun outs => pure (st, outs) := by
  have hadv : ∀ i, advance ((v i).elim failure fun a => oracleStep (q i a) >>= fun r =>
      (r.elim failure pure : PartyM C E (CallSpec I O) α)).run =
      liftComp ((v i).elim (pure none) (q i)) (LocalSpec C) >>= fun r => pure (.done r) := by
    intro i
    cases v i with
    | none => simp only [Option.elim, advance_run_failure, liftComp_pure, pure_bind]
    | some a =>
      simp only [Option.elim]
      rw [advance_oracleStep_bind]
      refine bind_congr fun r => ?_
      cases r <;> rfl
  have hl : liftComp (OverPermutation.sequenceFin fun i =>
      if i ∈ D.1 then pure none else (v i).elim (pure none) (q i)) (LocalSpec C) =
      OverPermutation.sequenceFin fun i =>
        liftComp (if i ∈ D.1 then pure none else (v i).elim (pure none) (q i)) (LocalSpec C) :=
    simulateQ_sequenceFin _ _
  have hs : startSteps localRoles D (fun i => (v i).elim failure fun a => oracleStep (q i a) >>= fun r =>
      (r.elim failure pure : PartyM C E (CallSpec I O) α)) =
      OverPermutation.sequenceFin (fun i => liftComp (if i ∈ D.1 then pure none else
        (v i).elim (pure none) (q i)) (LocalSpec C) >>= fun r => pure ((fun _ r => Step.done r) i r)) := by
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

/-- The rest of the run of a bottom tree, when each operator that still runs has the outputs `o₁`
(GS20, Theorem 2, for the signature ceremony). The fuel `e` covers the signature ceremony of each
codeword. -/
theorem bottomRest_obsEq (hsize : 0 < settings.batchSize) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (e : ℕ)
    (he : ∀ encoding, hybridRounds circuits parameter (chunks settings.batchSize (signJobs b encoding)) ≤ e)
    (o₁ : List (List Bit)) (st : A.State) (pre : C.Party → Option (List (List Bit)))
    (hpre : ∀ i, i ∉ D.1 → ∀ o, pre i = some o → o = o₁) :
    ObsEq prims (bottomRestRun K circuits settings D A x top b e st pre)
      (bottomMid K circuits settings D A x parameter seeds top b false o₁ st pre) := by
  have hcore := mainRealHybridCore_of prims K (mainEngineReal prims K) (mainRealSim prims K)
  have hpar : ∀ i, (x i).parameter = parameter := fun i => by rw [hx i]; rfl
  have h1 : bottomRestRun K circuits settings D A x top b e st pre =
      executePhase localRoles D (batchAdversary A) (mainFunctionalities K settings.mode) e st
        (fun i => (pre i).elim failure fun _ => oracleStep (bottomSearch (C := C) parameter b o₁) >>=
          bottomSign K circuits settings i (x i) top b o₁) := by
    refine executePhase_congr D (batchAdversary A) _ e st _ _ fun i hi => ?_
    cases hp : pre i with
    | none => simp only [Option.elim]
    | some o => simp only [Option.elim, bottomTail, hpar, hpre i hi o hp]
  rw [h1]
  refine (executePhase_search prims D (batchAdversary A) (mainFunctionalities K settings.mode)
    (Classical.arbitrary _) e st pre (bottomSearch parameter b o₁)
    (fun i => bottomSign K circuits settings i (x i) top b o₁)
    fun i w => bottomSign_call K circuits settings hsize i (x i) top b o₁ w).trans ?_
  unfold bottomMid
  by_cases halive : ∀ i, i ∉ D.1 → (pre i).isSome
  · rw [ite_eq_left halive, ite_eq_left halive]
    refine ObsEq.bind_right _ fun w => ?_
    rcases w with ⟨root, _ | re⟩
    · have hp := executePhase_finish D (batchAdversary A) (mainFunctionalities K settings.mode) e st
        (fun _ => (none : Option Unit)) fun _ _ => (pure none : OracleComp (RoSpec C) (Option TreeOutput))
      simp only [Option.elim, ite_self, sequenceFin_pure, liftComp_pure, pure_bind] at hp
      refine ObsEq.of_eq (Eq.trans ?_ hp)
      exact executePhase_congr D (batchAdversary A) _ e st _ _ fun i _ => by cases pre i <;> rfl
    · obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le (he re.2)
      rw [hextra]
      refine (ceremony_cut prims K circuits settings.mode D (batchAdversary A) hcore hx
        (chunks settings.batchSize (signJobs b re.2)) pre st extra
        (fun i values => oracleStep (bottomCheck (x i).parameter top b o₁ root re.1 values) >>=
          fun res => res.elim failure pure)).trans ?_
      dsimp only
      rw [chunks_flatten _ hsize]
      refine ObsEq.bind_right _ fun o₂ => ObsEq.bind_right _ fun r₂ => ObsEq.of_eq ?_
      simp only [hpar, Bool.false_eq_true, ↓reduceIte]
      exact executePhase_finish _ _ _ _ _ _ _
  · rw [ite_eq_right halive, ite_eq_right halive]
    exact ObsEq.refl _

/-- A computation of leanXMSS on the domain `Th` makes no copy call. -/
private theorem tweakable_copyBound {α : Type} (oa : OracleComp HashSpec α) :
    IsQueryBoundP (liftComp (tweakable (C := C) oa) (LocalSpec C)) CopyCall 0 := by
  refine IsQueryBoundP.liftComp_subSpec (p := fun t => CopyCall (.inr t)) (fun t => Iff.rfl) ?_
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    have ht : tweakable (C := C) (liftM (HashSpec.query t) >>= k) =
        hashQuery (.hash t) >>= fun u => tweakable (k u) := by
      simp only [tweakable, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
    rw [ht]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun u _ => ih u
    unfold hashQuery
    erw [isQueryBoundP_query_iff]
    exact fun h => h.elim

/-- The codeword of a root makes no copy call. -/
private theorem searchAt_copyBound (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (o : List (List Bit))
    (H L : ℕ) : IsQueryBoundP (liftComp (searchAt (C := C) parameter b o H L) (LocalSpec C)) CopyCall 0 := by
  unfold searchAt
  exact tweakable_copyBound _

/-- Each output of `F_ceremony` has the length of the outputs of its circuit. -/
private theorem evalJobs_forall₂' (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
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
    refine List.Forall₂.cons ?_ (evalJobs_forall₂' circuits parameter seeds js os hos)
    simp only [evalJob, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hb
    obtain ⟨v, -, rfl⟩ := hb
    simp [Circuit.eval]

/-- The last local step reads only the values of the honest operators. -/
private theorem localFinish_congr {σ : Type} (check : List (List Bit) → OracleComp (RoSpec C) (Option TreeOutput))
    (st : σ) (v v' : C.Party → Option (List (List Bit))) (h : ∀ i, i ∉ D.1 → v i = v' i) :
    localFinish D check st v = localFinish D check st v' := by
  unfold localFinish
  congr 3
  funext i
  by_cases hi : i ∈ D.1
  · simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte, h i hi]

/-- The data of the last local step of a bottom tree: the outputs of the first ceremony, the root,
the randomizer, the chain values of the dealer and the run of the signature ceremony. -/
private abbrev BottomData (σ : Type) :=
  List (List Bit) × Digest × Randomizer × List (List Bit) × σ × (C.Party → Option (List (List Bit)))

/-- The run of a bottom tree from the end of the first ceremony to the end of the signature ceremony.
It gives the state of the adversary after an early end, or the data of the last local step. -/
private def bottomSignRun (x : C.Party → Keys C) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (b : Fin (2 ^ layerHeight)) (r : List (List Bit) × A.State × (C.Party → Option (List (List Bit)))) :
    OracleComp (LocalSpec C) (A.State ⊕ BottomData (C := C) A.State) :=
  if ∀ i, i ∉ D.1 → ((ceremonyIdealOut D r).2 i).isSome then
    liftComp (bottomSearch (C := C) parameter b r.1) (LocalSpec C) >>= fun w =>
    match w.2 with
    | none => pure (.inl r.2.1)
    | some re =>
      liftComp ((signJobs b re.2).mapM (evalJob circuits parameter seeds)) (LocalSpec C) >>= fun o₂ =>
      simBatches K circuits settings.mode D (batchAdversary A) parameter (knownSeed (corruptInputs D x))
        (chunks settings.batchSize (signJobs b re.2)) o₂ (fun i => ((ceremonyIdealOut D r).2 i).map fun _ => [])
        r.2.1 >>= fun r₂ =>
      pure (.inr (r.1, w.1, re.1, o₂, r₂))
  else pure (.inl r.2.1)

/-- The last local step of a bottom tree and the distinguisher. -/
private def bottomEnd (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (Z : Distinguisher C A.State TreeOutput) (ideal : Bool) :
    A.State ⊕ BottomData (C := C) A.State → OracleComp (LocalSpec C) Bool
  | .inl st => Z (st, fun _ => none)
  | .inr (o₁, root, randomness, o₂, r₂) =>
    localFinish D (bottomCheck parameter top b o₁ root randomness) r₂.1
      (if ideal then fun i => if i ∉ D.1 ∧ (r₂.2 i).isSome then some o₂ else none else r₂.2) >>= Z

private theorem bottomMid_split (top : TopTree) (b : Fin (2 ^ layerHeight)) (Z : Distinguisher C A.State TreeOutput)
    (ideal : Bool) (r : List (List Bit) × A.State × (C.Party → Option (List (List Bit)))) :
    bottomMid K circuits settings D A x parameter seeds top b ideal r.1 (ceremonyIdealOut D r).1
        (ceremonyIdealOut D r).2 >>= Z =
      bottomSignRun K circuits settings D A x parameter seeds b r >>= bottomEnd D A parameter top b Z ideal := by
  unfold bottomMid bottomSignRun
  by_cases halive : ∀ i, i ∉ D.1 → ((ceremonyIdealOut D r).2 i).isSome
  · rw [ite_eq_left halive, ite_eq_left halive]
    simp only [bind_assoc]
    refine bind_congr fun w => ?_
    rcases w with ⟨root, _ | re⟩
    · simp only [pure_bind, bottomEnd, ceremonyIdealOut]
    · simp only [bind_assoc, pure_bind, bottomEnd, ceremonyIdealOut]
  · rw [ite_eq_right halive, ite_eq_right halive]
    simp only [pure_bind, bottomEnd, ceremonyIdealOut]

/-- The opened chain values against the chain values of the dealer, at the cost of the birthday bound
of the copy hashes of both ceremonies (MPClan, App. B). -/
theorem bottom_swap2 (hsize : 0 < settings.batchSize) (z : Aux) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (Z : Distinguisher C A.State TreeOutput) (fuel q : ℕ)
    (hfuel : TreeFuel circuits settings (.bottom b) fuel) (hq : IsQueryBounded A Z fuel q) :
    |acc prims (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>= fun r =>
        bottomMid K circuits settings D A x parameter seeds top b false r.1 (ceremonyIdealOut D r).1
          (ceremonyIdealOut D r).2 >>= Z) -
      acc prims (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>= fun r =>
        bottomMid K circuits settings D A x parameter seeds top b true r.1 (ceremonyIdealOut D r).1
          (ceremonyIdealOut D r).2 >>= Z)| ≤
      (((q + treeBatches settings (.bottom b) * termHashes C) ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
  have hsplit : ∀ ideal, (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>= fun r =>
      bottomMid K circuits settings D A x parameter seeds top b ideal r.1 (ceremonyIdealOut D r).1
        (ceremonyIdealOut D r).2 >>= Z) =
      (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>=
        bottomSignRun K circuits settings D A x parameter seeds b) >>= bottomEnd D A parameter top b Z ideal := by
    intro ideal
    rw [bind_assoc]
    exact bind_congr fun r => bottomMid_split K circuits settings D A top b Z ideal r
  have hsound : MainRunInv prims (fun v s => ¬ MainCopyCollision s →
      bottomEnd D A parameter top b Z false v = bottomEnd D A parameter top b Z true v)
      (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>=
        bottomSignRun K circuits settings D A x parameter seeds b) := by
    refine MainRunInv.bind fun r => ?_
    unfold bottomSignRun
    refine MainRunInv.ite _ (fun _ => ?_) fun _ => MainRunInv.pure _ fun _ _ => rfl
    refine MainRunInv.bind fun w => ?_
    rcases w with ⟨root, _ | re⟩
    · exact MainRunInv.pure _ fun _ _ => rfl
    intro s v hv
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hv
    obtain ⟨o, ho, r₂, hr₂, rfl⟩ := hv
    have hout : o.1 ∈ support ((signJobs b re.2).mapM (evalJob circuits parameter seeds)) := by
      have h := support_simulateQ_run'_subset (localAnswer (C := C) prims)
        (((signJobs b re.2).mapM (evalJob circuits parameter seeds)).liftComp (LocalSpec C)) s
        (by rw [StateT.run'_eq, support_map]; exact ⟨o, ho, rfl⟩)
      rwa [OracleComp.support_liftComp] at h
    have hlen := evalJobs_forall₂' circuits parameter seeds _ o.1 hout
    rw [← chunks_flatten _ hsize (signJobs b re.2)] at hlen
    obtain ⟨-, hH⟩ := simBatches_inv prims K circuits settings.mode D (batchAdversary A) parameter
      (knownSeed (corruptInputs D x)) (chunks settings.batchSize (signJobs b re.2)) o.1 _ r.2.1 hlen o.2 r₂ hr₂
    intro hcol
    simp only [bottomEnd, Bool.false_eq_true, ↓reduceIte]
    refine congrArg (· >>= Z) (localFinish_congr D _ _ _ _ fun i hi => ?_)
    cases hri : r₂.1.2 i with
    | none => simp
    | some u =>
      obtain ⟨o₀, ho₀, rfl⟩ := hH hcol i hi u hri
      simp only [Option.map_eq_some_iff] at ho₀
      obtain ⟨_, _, rfl⟩ := ho₀
      simp [hi]
  have hbound : IsQueryBoundP (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>=
      bottomSignRun K circuits settings D A x parameter seeds b) CopyCall
      (q + treeBatches settings (.bottom b) * termHashes C) := by
    obtain ⟨start, step, final, hsum, hstart, hround, hanswer, -⟩ := hq
    have hR := hfuel parameter fun _ => digit 0
    have hrest : ∀ r, IsQueryBoundP (bottomSignRun K circuits settings D A x parameter seeds b r) CopyCall
        ((fuel - hybridRounds circuits parameter (chunks settings.batchSize (bottomJobs b))) * step +
          (chunks settings.batchSize (signJobs b fun _ => digit 0)).length * termHashes C) := by
      intro r
      unfold bottomSignRun
      split_ifs
      · refine (isQueryBoundP_bind (n := 0)
          (searchAt_copyBound parameter b r.1 layerHeight randomizerAttemptLimit) fun w _ => ?_).mono
            (Nat.zero_add _).le
        rcases w with ⟨root, _ | re⟩
        · exact isQueryBoundP_pure _ _ _
        have h2 := hfuel parameter re.2
        have hl : (chunks settings.batchSize (signJobs b re.2)).length =
            (chunks settings.batchSize (signJobs b fun _ => digit 0)).length := by
          simp [chunks, signJobs]
        have h3 := Nat.mul_le_mul_right step (show hybridRounds circuits parameter
          (chunks settings.batchSize (signJobs b re.2)) ≤
            fuel - hybridRounds circuits parameter (chunks settings.batchSize (bottomJobs b)) by omega)
        refine (isQueryBoundP_bind (evalJobs_copyBound circuits parameter _ seeds) fun o₂ _ =>
          isQueryBoundP_bind (simBatches_copyBound K circuits settings.mode D (batchAdversary A) parameter
            (knownSeed (corruptInputs D x)) step hanswer hround _ o₂ _ r.2.1) fun _ _ =>
              isQueryBoundP_pure _ _ 0).mono ?_
        rw [hl]
        omega
      · exact isQueryBoundP_pure _ _ _
    rw [show treeBatches settings (.bottom b) = (chunks settings.batchSize (bottomJobs b)).length +
      (chunks settings.batchSize (signJobs b fun _ => digit 0)).length from rfl]
    generalize bottomJobs b = jobs at hR hrest ⊢
    unfold hybridCommon
    simp only [bind_assoc, pure_bind]
    refine (isQueryBoundP_bind ((hstart _ _).of_imp counted_of_copyCall) fun st _ =>
      isQueryBoundP_bind (evalJobs_copyBound circuits parameter jobs seeds) fun outputs _ =>
        isQueryBoundP_bind (simBatches_copyBound K circuits settings.mode D (batchAdversary A) parameter
          (knownSeed (corruptInputs D x)) step hanswer hround (chunks settings.batchSize jobs) outputs
          (fun _ => some []) st) fun r _ => hrest (outputs, r)).mono ?_
    have h3 : (fuel - hybridRounds circuits parameter (chunks settings.batchSize jobs)) * step +
        hybridRounds circuits parameter (chunks settings.batchSize jobs) * step = fuel * step := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    rw [Nat.add_mul]
    omega
  rw [hsplit, hsplit]
  generalize (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>=
    bottomSignRun K circuits settings D A x parameter seeds b) = P at hsound hbound ⊢
  unfold acc
  rw [main_worldRoles_bind, main_worldRoles_bind]
  refine (main_abs_accepts_bind_sub_le prims _ _ _).trans ?_
  have h1 : Pr{let r ← runWorld prims (worldRoles.adversary P)}[
        (worldRoles.adversary (bottomEnd D A parameter top b Z false r.1) : OracleComp (WorldSpec C) Bool) ≠
          worldRoles.adversary (bottomEnd D A parameter top b Z true r.1)] ≤
      Pr{let z ← (simulateQ (localAnswer prims) P).run ∅}[MainCopyCollision z.2] := by
    rw [main_probEvent_runWorld_fst prims _ (fun r =>
        (worldRoles.adversary (bottomEnd D A parameter top b Z false r) : OracleComp (WorldSpec C) Bool) ≠
          worldRoles.adversary (bottomEnd D A parameter top b Z true r)),
      main_simulateQ_adversary, StateT.run'_eq, prEvent_map]
    exact prEvent_mono_of_support _ _ _ fun p hp hne => by
      by_contra hcol
      exact hne (by rw [hsound ∅ p hp hcol])
  exact (ENNReal.toReal_mono (prEvent_ne_top _) h1).trans (copy_birthday prims _ _ hbound)

/-- The batches of the dealer give one list for each batch. -/
private theorem evalBatches_length (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    ∀ (bs : List (List Job)) (l : List (List (List Bit))),
      l ∈ support (evalBatches (C := C) circuits parameter seeds bs) → l.length = bs.length
  | [], l, h => by simp [evalBatches] at h; simp [h]
  | j :: bs, l, h => by
    simp only [evalBatches, List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨_, -, ls, hls, rfl⟩ := h
    simp [evalBatches_length circuits parameter seeds bs ls hls]

/-- The signature ceremony of the dealer of bottom tree `b` and its check, from the outputs `o` of the
first ceremony and the codeword `w`. It gives the tree and the log of the signature ceremony. -/
private def dealerSign (circuits : Circuits) (settings : Settings) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (b : Fin (2 ^ layerHeight)) (o : List (List Bit))
    (w : Digest × Option (Randomizer × Encoding)) :
    OracleComp (RoSpec C) (Option TreeOutput × List (List (List Bit))) :=
  match w.2 with
  | none => pure (none, [])
  | some re =>
    evalBatches circuits parameter seeds (chunks settings.batchSize (signJobs b re.2)) >>= fun l₂ =>
      bottomCheck parameter top b o w.1 re.1 l₂.flatten >>= fun res => pure (res, l₂)

/-- The dealer of a bottom tree, with the log of the first ceremony in front. -/
private theorem dealerCeremony_bottom' (circuits : Circuits) (settings : Settings) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (hsize : 0 < settings.batchSize) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    dealerCeremony circuits settings parameter seeds top (.bottom b) =
      evalBatches circuits parameter seeds (chunks settings.batchSize (bottomJobs b)) >>= fun l₁ =>
        bottomSearch parameter b l₁.flatten >>= fun w =>
          (fun p => (p.1, l₁ ++ p.2)) <$> dealerSign circuits settings parameter seeds top b l₁.flatten w := by
  rw [dealerCeremony_bottom circuits settings parameter seeds hsize top b]
  refine bind_congr fun l₁ => bind_congr fun w => ?_
  rcases w with ⟨root, _ | re⟩
  · rw [dealerSign, map_pure, List.append_nil]
  · rw [dealerSign, map_bind]
    refine bind_congr fun l₂ => ?_
    rw [map_bind]
    refine bind_congr fun res => ?_
    rw [map_pure]

/-- With the outputs and the chain values of the dealer, the run is the ideal run. -/
theorem bottom_ideal_acc (hsize : 0 < settings.batchSize) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (z : Aux) (top : TopTree) (b : Fin (2 ^ layerHeight)) (Z : Distinguisher C A.State TreeOutput) :
    acc prims (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>= fun r =>
        bottomMid K circuits settings D A x parameter seeds top b true r.1 (ceremonyIdealOut D r).1
          (ceremonyIdealOut D r).2 >>= Z) =
      acc prims (treeIdealLocal K circuits settings D A x z parameter seeds top (.bottom b) >>= Z) := by
  refine acc_obsEq prims ?_
  unfold hybridCommon treeIdealLocal
  rw [dealerCeremony_bottom' circuits settings parameter seeds hsize top b]
  simp only [bind_assoc, liftComp_bind, liftComp_map, bind_map_left, pure_bind]
  refine ObsEq.bind_right _ fun st => ?_
  have hM : (bottomJobs b).mapM (evalJob circuits parameter seeds) =
      List.flatten <$> evalBatches (C := C) circuits parameter seeds (chunks settings.batchSize (bottomJobs b)) := by
    rw [evalBatches_flatten, chunks_flatten _ hsize]
  rw [hM, liftComp_map, bind_map_left]
  unfold treeSimRun bottomMid
  refine ObsEq.bind_support _ fun l hl => ?_
  rw [OracleComp.support_liftComp] at hl
  have hlen := evalBatches_length circuits parameter seeds _ l hl
  simp only [List.take_left' hlen, List.drop_left' hlen, bind_assoc, ↓reduceIte]
  generalize simBatches K circuits settings.mode D (batchAdversary A) parameter (knownSeed (corruptInputs D x))
    (chunks settings.batchSize (bottomJobs b)) l.flatten (fun _ => some []) st = S1
  conv_rhs => rw [← bind_assoc]
  refine ObsEq.trans ?_ (sameRun_swap prims _ S1 fun p r₁ => _).symm.obsEq
  refine ObsEq.bind_right _ fun r₁ => ?_
  split_ifs with h1 h2 h2
  · simp only [bind_assoc]
    refine ObsEq.trans ?_ (obsEq_rerun prims _ _ _).symm
    refine ObsEq.bind_right _ fun w => ?_
    rcases w with ⟨root, _ | re⟩
    · unfold dealerSign
      dsimp only [ceremonyIdealOut]
      simp only [liftComp_pure, pure_bind, Finset.notMem_empty, and_false, ite_false]
      exact ObsEq.refl _
    · unfold dealerSign
      dsimp only [ceremonyIdealOut]
      simp only [liftComp_bind, liftComp_pure, bind_assoc, pure_bind, Finset.mem_filter, Finset.mem_univ,
        true_and]
      have hM2 : (signJobs b re.2).mapM (evalJob circuits parameter seeds) =
          List.flatten <$> evalBatches (C := C) circuits parameter seeds
            (chunks settings.batchSize (signJobs b re.2)) := by
        rw [evalBatches_flatten, chunks_flatten _ hsize]
      rw [hM2, liftComp_map, bind_map_left]
      refine ObsEq.bind_right _ fun l₂ => ?_
      have hS := simBatches_congr K circuits settings.mode D (batchAdversary A) parameter
        (knownSeed (corruptInputs D x)) (chunks settings.batchSize (signJobs b re.2)) l₂.flatten
        (fun i => Option.map (fun _ => []) (if i ∉ D.1 ∧ (r₁.2 i).isSome = true then some l.flatten else none))
        (fun i => Option.map (fun _ => []) (r₁.2 i)) r₁.1 fun i hi => by
          cases hr : r₁.2 i <;> simp [hi]
      rw [hS]
      generalize simBatches K circuits settings.mode D (batchAdversary A) parameter (knownSeed (corruptInputs D x))
        (chunks settings.batchSize (signJobs b re.2)) l₂.flatten (fun i => Option.map (fun _ => []) (r₁.2 i))
        r₁.1 = S2
      refine ObsEq.trans ?_ (sameRun_swap prims
        (liftComp (bottomCheck parameter top b l.flatten root re.1 l₂.flatten) (LocalSpec C)) S2
        (fun res r => Z (r.1, fun i => if i ∉ D.1 ∧ (r.2 i).isSome = true then res else none))).symm.obsEq
      refine ObsEq.bind_right _ fun r => ?_
      unfold localFinish
      simp only [bind_assoc, pure_bind]
      refine obsEq_hash prims _ _ _ _ fun h _ => ObsEq.of_eq ?_
      rw [valueAt_sequenceFin]
      refine congrArg (fun outs => Z (r.1, outs)) (funext fun i => ?_)
      by_cases hi : i ∈ D.1
      · rw [ite_eq_left hi, ite_eq_right (fun h => h.1 hi), D_pure]
      · by_cases hs : (r.2 i).isSome = true
        · rw [ite_eq_right hi, ite_eq_left ⟨hi, hs⟩, ite_eq_left ⟨hi, hs⟩, Option.elim_some]
        · rw [ite_eq_right hi, ite_eq_right (fun h => hs h.2), ite_eq_right (fun h => hs h.2), Option.elim_none, D_pure]
  · refine absurd (fun i hi => ?_) h2
    have h := h1 i hi
    simp only [ceremonyIdealOut] at h
    split_ifs at h with h'
    · exact h'.2
    · exact absurd h (by simp)
  · refine absurd (fun i hi => ?_) h1
    simp only [ceremonyIdealOut]
    rw [ite_eq_left ⟨hi, h2 i hi⟩]
    rfl
  · simp only [pure_bind, Finset.notMem_empty, and_false, ite_false]
    dsimp only [ceremonyIdealOut]
    exact (obsEq_drop prims _ _).symm

/-- The distance of the real run and the ideal run of a bottom tree. -/
theorem bottom_distance (hsize : 0 < settings.batchSize) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (z : Aux) (top : TopTree) (b : Fin (2 ^ layerHeight)) (Z : Distinguisher C A.State TreeOutput) (fuel q : ℕ)
    (hfuel : TreeFuel circuits settings (.bottom b) fuel) (hq : IsQueryBounded A Z fuel q) :
    |accepts prims (distinguish (realExecution D A (mainFunctionalities K settings.mode) fuel
        (fun i keys => newTreeHybrid K circuits settings i keys top (.bottom b)) x z) Z) -
      accepts prims (distinguish (idealExecution worldRoles.adversary D (Ftree circuits settings top (.bottom b))
        (treeHybridSimulator K circuits settings D A (.bottom b)) x z) Z)| ≤
      treeHybridError settings C (.bottom b) q := by
  have hR : hybridRounds circuits parameter (chunks settings.batchSize (bottomJobs b)) ≤ fuel :=
    (Nat.le_add_right _ _).trans (hfuel parameter fun _ => digit 0)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hR
  have he' : ∀ encoding, hybridRounds circuits parameter (chunks settings.batchSize (signJobs b encoding)) ≤ e :=
    fun encoding => by have := hfuel parameter encoding; omega
  have h1 := bottom_cut_acc prims K circuits settings D A hsize hx z top b Z e
  rw [← he] at h1
  have h2 := hybridCommon_swap prims K circuits settings (bottomJobs b) D A hsize x z parameter seeds
    (fun _ => pure true) fuel q hR (isQueryBounded_const hq)
    (fun p => bottomRestRun K circuits settings D A x top b e p.1 p.2 >>= Z)
  have h3 : acc prims (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>= fun r =>
        bottomRestRun K circuits settings D A x top b e (ceremonyIdealOut D r).1 (ceremonyIdealOut D r).2 >>= Z) =
      acc prims (hybridCommon K circuits settings (bottomJobs b) D A x z parameter seeds >>= fun r =>
        bottomMid K circuits settings D A x parameter seeds top b false r.1 (ceremonyIdealOut D r).1
          (ceremonyIdealOut D r).2 >>= Z) :=
    acc_obsEq prims (ObsEq.bind_right _ fun r =>
      (bottomRest_obsEq prims K circuits settings D A hsize hx top b e he' r.1 (ceremonyIdealOut D r).1
        (ceremonyIdealOut D r).2 fun i _ o ho => by
          simp only [ceremonyIdealOut] at ho
          split_ifs at ho
          exact (Option.some.inj ho).symm).bind_left Z)
  have h4 := bottom_swap2 prims K circuits settings D A (x := x) (parameter := parameter) (seeds := seeds)
    hsize z top b Z fuel q hfuel hq
  have h5 := bottom_ideal_acc prims K circuits settings D A hsize hx z top b Z
  rw [tree_real_acc, tree_ideal_acc prims K circuits settings D A hx z top (.bottom b) Z, h1, ← h5]
  beta_reduce at h2
  rw [h3] at h2
  exact (abs_sub_le _ _ _).trans (add_le_add h2 h4)

end Bottom

end ThresholdLeanXmssSecurity
