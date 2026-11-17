import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Observation
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# The simulator of the hybrid ceremony

The simulator of GS20, Theorem 2, for every batch of a ceremony. It gets the keys of the corrupt
operators, the parameter and every output of `F_ceremony`.

* For each batch, it computes the input terms that a corrupt operator holds, with one counted call
  for each known term and point (`knownInputQuery`). `F_ceremony` does not leak them.
* Then it runs the simulator of a batch, `mainSimAnswerX` of `Proof/MainSecurity.lean`, on the outputs
  of that batch.
* It runs the next batch only if every honest operator opened its outputs. After a partial abort, the
  functionality of the next call does not run, so the adversary gets no more step.
* It does not read the outputs of a batch that it does not run.

`simBatches_bound` is the count of its calls, and `simBatches_copyBound` is the count of its calls
in the copy domain. `simBatches_inv` states that an operator with an output has the outputs of
`F_ceremony`, or two copy hashes collide.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-! ## Definitions -/

/-- The adversary of a hybrid ceremony. -/
abbrev CeremonyAdversary (C : Committee) (E : Type) :=
  Adversary C E (Keys C) (MainHybridLeak C) (MainHybridReply C)

/-- The adversary of a ceremony as the adversary of a batch. A batch does not start it. -/
def batchAdversary (A : CeremonyAdversary C E) : MainAdversary C E :=
  ⟨A.State, fun _ z => A.start (fun _ => none) z, A.round, A.answer⟩

/-- Operator `i` in the hybrid ceremony. It has no PRSS keys. -/
def hybridContext (i : C.Party) (keys : Keys C) : Context C := ⟨i, keys, ⟨fun _ => 0, fun _ => 0⟩⟩

/-- The input wires of a batch at operator `i`. -/
def batchInputQuery (i : C.Party) (keys : Keys C) (batch : List Job) : OracleComp (RoSpec C) (MainInput C) :=
  batch.mapM (inputQuery (hybridContext i keys))

/-- The input wires of a batch at each honest operator. A corrupt operator has none. -/
def honestInputQuery (D : C.Coalition) (x : C.Party → Keys C) (batch : List Job) :
    OracleComp (RoSpec C) (C.Party → MainInput C) :=
  OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure [] else batchInputQuery i (x i) batch

/-- The seed of a term from its first holder with keys. -/
def knownSeed (keys : C.Party → Option (Keys C)) (T : C.Term) : HashOutput :=
  (C.parties.findSome? fun j => if j ∈ C.holders T then (keys j).map (·.seed T) else none).getD 0

/-- The input wires of a job at the terms that a corrupt operator holds, one call for each such term
and each point. -/
def knownInputQuery (D : C.Coalition) (seed : C.Term → HashOutput) (job : Job) :
    OracleComp (RoSpec C) (C.Term → List Bit) := do
  let terms ← C.terms.mapM fun T =>
    if KnownTo D.1 T then job.points.flatMapM fun x => bitsOfDigest <$> prf (seed T) x else pure []
  pure fun T => terms.getD (C.terms.idxOf T) []

/-- The view of each honest operator of the known input wires, as `F_main` leaks it. -/
def knownViews (D : C.Coalition) (known : MainInput C) : C.Party → Option (MainInput C) := fun i =>
  if i ∈ D.1 then none else some (known.map fun v T => if i ∈ C.holders T then v T else [])

/-- The steps of the batches, one call for each AND layer and for `Rerand`, one call of the check and
one round for `OpenRep`. -/
def hybridRounds (circuits : Circuits) (parameter : PublicParameter) (bs : List (List Job)) : ℕ :=
  (bs.map fun batch => mainRounds (batch.map (circuits parameter ·.kind))).sum

/-- The outputs of each operator that still runs, after a batch with the opened values `opened`. -/
def nextOutputs (cs : List Circuit) (pre : C.Party → Option (List (List Bit)))
    (opened : C.Party → Option (ℕ → Bit)) : C.Party → Option (List (List Bit)) := fun i =>
  (pre i).bind fun o => (opened i).map fun v => o ++ assemble cs v

section Batches

variable (K : Constants C E) (circuits : Circuits) (mode : ReshareMode) (D : C.Coalition)
  (A : MainAdversary C E) (parameter : PublicParameter) (seed : C.Term → HashOutput)

/-- The simulator of the batches `bs` on the outputs `outputs` of their jobs, with the opened values.
`pre` holds the outputs so far of each operator that still runs. -/
def simBatches : List (List Job) → List (List Bit) → (C.Party → Option (List (List Bit))) → A.State →
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (List (List Bit))))
  | [], _, pre, st => pure (st, fun i => if i ∈ D.1 then none else pre i)
  | batch :: rest, outputs, pre, st =>
    if ∀ i, i ∉ D.1 → (pre i).isSome then
      liftComp (batch.mapM (knownInputQuery D seed)) (LocalSpec C) >>= fun known =>
      mainSimAnswerX K D A mode (batch.map (circuits parameter ·.kind)) st
        (knownViews D known, outputs.take batch.length) >>= fun r =>
      simBatches rest (outputs.drop batch.length)
        (nextOutputs (batch.map (circuits parameter ·.kind)) pre r.2) r.1
    else pure (st, fun _ => none)

/-- The simulator of the batches, where the outputs of a batch come from the seeds `seeds` at the
start of that batch. -/
def lazyBatches (seeds : C.Term → HashOutput) : List (List Job) → (C.Party → Option (List (List Bit))) → A.State →
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (List (List Bit))))
  | [], pre, st => pure (st, fun i => if i ∈ D.1 then none else pre i)
  | batch :: rest, pre, st =>
    if ∀ i, i ∉ D.1 → (pre i).isSome then
      liftComp (batch.mapM (evalJob circuits parameter seeds)) (LocalSpec C) >>= fun outs =>
      liftComp (batch.mapM (knownInputQuery D seed)) (LocalSpec C) >>= fun known =>
      mainSimAnswerX K D A mode (batch.map (circuits parameter ·.kind)) st (knownViews D known, outs) >>= fun r =>
      lazyBatches seeds rest (nextOutputs (batch.map (circuits parameter ·.kind)) pre r.2) r.1
    else pure (st, fun _ => none)

end Batches

/-- The simulator of the hybrid ceremony (GS20, Theorem 2). Its state holds the keys of the corrupt
operators. -/
def ceremonyHybridSimulator (K : Constants C E) (circuits : Circuits) (settings : Settings) (jobs : List Job)
    (D : C.Coalition) (A : CeremonyAdversary C E) :
    Simulator (C := C) (LocalSpec C) (Keys C) (PublicParameter × List (List Bit)) (Finset C.Party) A.State where
  State := A.State × (C.Party → Option (Keys C))
  start keys z := do
    let st ← A.start keys z
    pure (st, keys)
  answer s l := do
    let r ← simBatches K circuits settings.mode D (batchAdversary A) l.1 (knownSeed s.2)
      (chunks settings.batchSize jobs) l.2 (fun _ => some []) s.1
    pure ((r.1, s.2), Finset.univ.filter fun i => (r.2 i).isSome)
  output s := pure s.1

/-! ## The count of the calls -/

section Counting

variable {ι : Type} {spec : OracleSpec ι} {α β : Type} (p : ι → Prop)

theorem isQueryBoundP_mapM_sum (f : α → OracleComp spec β) (n : α → ℕ)
    (h : ∀ a, IsQueryBoundP (f a) p (n a)) : ∀ xs : List α, IsQueryBoundP (xs.mapM f) p (xs.map n).sum
  | [] => by simp
  | a :: xs => by
    simp only [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (isQueryBoundP_bind (h a) fun b _ =>
      isQueryBoundP_bind (isQueryBoundP_mapM_sum f n h xs) fun bs _ => isQueryBoundP_pure p (b :: bs) 0).mono
        (by omega)

theorem isQueryBoundP_flatMapM (f : α → OracleComp spec (List β)) (n : ℕ)
    (h : ∀ a, IsQueryBoundP (f a) p n) : ∀ xs : List α, IsQueryBoundP (xs.flatMapM f) p (xs.length * n)
  | [] => by simp
  | a :: xs => by
    rw [List.flatMapM_cons, List.length_cons]
    exact (isQueryBoundP_bind (h a) fun b _ =>
      isQueryBoundP_bind (isQueryBoundP_flatMapM f n h xs) fun bs _ => isQueryBoundP_pure p (b ++ bs) 0).mono
        (by rw [Nat.succ_mul]; omega)

theorem sum_map_mul_const (f : α → ℕ) (c : ℕ) : ∀ l : List α, (l.map fun a => f a * c).sum = (l.map f).sum * c
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_mul_const f c l, Nat.add_mul]

end Counting

section Bounds

theorem length_terms : C.terms.length = termCount C := by
  simp only [Committee.terms, Finset.length_toList, Finset.card_univ, termCount]
  simp

/-- The known input wires of a job cost one call of `H` in the domain `p` for each term and point, or
none when `p` does not hold at the PRF domain. -/
theorem knownInputQuery_bound_of (p : (LocalSpec C).Domain → Prop) (c : ℕ)
    (hc : ∀ seed x, p (.inr (.inl (.prf seed x))) → 0 < c) (D : C.Coalition) (seed : C.Term → HashOutput)
    (job : Job) :
    IsQueryBoundP (liftComp (knownInputQuery D seed job) (LocalSpec C)) p (job.points.length * c * termCount C) := by
  refine IsQueryBoundP.liftComp_subSpec (p := fun t => p (.inr t)) (fun t => Iff.rfl) ?_
  unfold knownInputQuery
  have hterm : ∀ T : C.Term, IsQueryBoundP
      (if KnownTo D.1 T then job.points.flatMapM fun x => bitsOfDigest <$> prf (C := C) (seed T) x else pure [])
      (fun t => p (.inr t)) (job.points.length * c) := by
    intro T
    split_ifs
    · refine isQueryBoundP_flatMapM _ _ c (fun x => ?_) _
      unfold prf hashQuery
      rw [isQueryBoundP_map_iff, isQueryBoundP_map_iff]
      erw [isQueryBoundP_query_iff]
      exact hc (seed T) x
    · exact isQueryBoundP_pure _ _ _
  have h := isQueryBoundP_mapM_sum (fun t => p (.inr t)) _ (fun _ : C.Term => job.points.length * c) hterm C.terms
  rw [List.map_const', List.sum_replicate, length_terms, smul_eq_mul, Nat.mul_comm] at h
  exact (isQueryBoundP_bind h fun terms _ => isQueryBoundP_pure _ _ 0).mono (by omega)

theorem knownInputQuery_bound (D : C.Coalition) (seed : C.Term → HashOutput) (job : Job) :
    IsQueryBoundP (liftComp (knownInputQuery D seed job) (LocalSpec C)) Counted
      (job.points.length * termCount C) := by
  simpa using knownInputQuery_bound_of Counted 1 (fun _ _ _ => Nat.one_pos) D seed job

theorem knownInputQuery_copyBound (D : C.Coalition) (seed : C.Term → HashOutput) (job : Job) :
    IsQueryBoundP (liftComp (knownInputQuery D seed job) (LocalSpec C)) CopyCall 0 := by
  simpa using knownInputQuery_bound_of CopyCall 0 (fun _ _ h => h.elim) D seed job

end Bounds

section SimBounds

variable (K : Constants C E) (circuits : Circuits) (mode : ReshareMode) (D : C.Coalition)
  (A : MainAdversary C E) (parameter : PublicParameter) (seed : C.Term → HashOutput) (step : ℕ)

/-- The simulator of a batch with the opened values makes at most one step of the adversary for each
step of the batch, and the copy hashes of `OpenRep`. -/
theorem mainSimAnswerX_bound (hanswer : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (hround : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (jobs : List Circuit) (st : A.State) (l : MainIdealLeak C) :
    IsQueryBoundP (mainSimAnswerX K D A mode jobs st l) Counted (mainRounds jobs * step + termHashes C) := by
  have h := mainSimulator_answer_bound K D A step hanswer hround mode jobs st l
  rw [mainSimulator_answer_eq] at h
  exact (isQueryBoundP_map_iff (p := Counted) _ mainAccepted _).1 h

/-- The count of the calls of the simulator in a domain `p`, from the count of a batch and the count
`c` of one known input wire. -/
theorem simBatches_bound_of (p : (LocalSpec C).Domain → Prop) (c : ℕ)
    (hknown : ∀ job, IsQueryBoundP (liftComp (knownInputQuery D seed job) (LocalSpec C)) p (job.points.length * c))
    (hsim : ∀ jobs st l, IsQueryBoundP (mainSimAnswerX K D A mode jobs st l) p
      (mainRounds jobs * step + termHashes C)) :
    ∀ (bs : List (List Job)) (outputs : List (List Bit)) (pre : C.Party → Option (List (List Bit)))
      (st : A.State),
      IsQueryBoundP (simBatches K circuits mode D A parameter seed bs outputs pre st) p
        (hybridRounds circuits parameter bs * step + bs.length * termHashes C +
          (bs.flatten.map (·.points.length)).sum * c)
  | [], outputs, pre, st => isQueryBoundP_pure _ _ _
  | batch :: rest, outputs, pre, st => by
    rw [simBatches]
    split_ifs
    · rw [liftComp_mapM_local]
      have h1 := isQueryBoundP_mapM_sum p _ (fun job : Job => job.points.length * c) hknown batch
      have h2 := fun known => hsim (batch.map (circuits parameter ·.kind)) st
        (knownViews D known, outputs.take batch.length)
      have h3 := fun (r : A.State × (C.Party → Option (ℕ → Bit))) =>
        simBatches_bound_of p c hknown hsim rest (outputs.drop batch.length)
          (nextOutputs (batch.map (circuits parameter ·.kind)) pre r.2) r.1
      refine (isQueryBoundP_bind h1 fun known _ => isQueryBoundP_bind (h2 known) fun r _ => h3 r).mono ?_
      have e := sum_map_mul_const (fun job : Job => job.points.length) c batch
      simp only [hybridRounds, List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
        List.sum_append, List.length_cons, e, Nat.add_mul, Nat.one_mul]
      omega
    · exact isQueryBoundP_pure _ _ _

/-- The calls of the simulator of the batches. It makes one step of the adversary for each step of a
batch, the copy hashes of `OpenRep` of each batch, and one call for each known term and point. -/
theorem simBatches_bound (hanswer : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (hround : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (bs : List (List Job)) (outputs : List (List Bit)) (pre : C.Party → Option (List (List Bit)))
    (st : A.State) :
    IsQueryBoundP (simBatches K circuits mode D A parameter seed bs outputs pre st) Counted
      (hybridRounds circuits parameter bs * step + bs.length * termHashes C +
        (bs.flatten.map (·.points.length)).sum * termCount C) :=
  simBatches_bound_of K circuits mode D A parameter seed step Counted (termCount C)
    (knownInputQuery_bound D seed) (mainSimAnswerX_bound K mode D A step hanswer hround) bs outputs pre st

/-- The calls of the simulator of the batches in the copy domain. The known input wires need none. -/
theorem simBatches_copyBound (hanswer : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (hround : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (bs : List (List Job)) (outputs : List (List Bit)) (pre : C.Party → Option (List (List Bit)))
    (st : A.State) :
    IsQueryBoundP (simBatches K circuits mode D A parameter seed bs outputs pre st) CopyCall
      (hybridRounds circuits parameter bs * step + bs.length * termHashes C) := by
  have h := simBatches_bound_of K circuits mode D A parameter seed step CopyCall 0
    (fun job => by simpa using knownInputQuery_copyBound D seed job)
    (fun jobs st l => (mainSimAnswerX_bound K mode D A step hanswer hround jobs st l).of_imp
      counted_of_copyCall) bs outputs pre st
  simpa using h

/-- `F_ceremony` makes no call in the copy domain. It asks only the PRF of each term. -/
theorem evalJobs_copyBound (jobs : List Job) (seeds : C.Term → HashOutput) :
    IsQueryBoundP (liftComp (jobs.mapM (evalJob (C := C) circuits parameter seeds)) (LocalSpec C)) CopyCall 0 := by
  refine IsQueryBoundP.liftComp_subSpec (p := fun t => CopyCall (.inr t)) (fun t => Iff.rfl) ?_
  have hprf : ∀ (s : HashOutput) (x : Point),
      IsQueryBoundP (prf (C := C) s x) (fun t => CopyCall (.inr t)) 0 := by
    intro s x
    unfold prf hashQuery
    rw [isQueryBoundP_map_iff]
    erw [isQueryBoundP_query_iff]
    exact fun h => h.elim
  have hvalue : ∀ x : Point, IsQueryBoundP (prfValue (C := C) seeds x) (fun t => CopyCall (.inr t)) 0 := by
    intro x
    unfold prfValue
    have h := isQueryBoundP_mapM_sum (fun t => CopyCall (C := C) (.inr t)) (fun T => prf (seeds T) x)
      (fun _ => 0) (fun T => hprf (seeds T) x) C.terms
    rw [List.map_const', List.sum_replicate, smul_zero] at h
    exact isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ 0
  have hjob : ∀ job : Job, IsQueryBoundP (evalJob (C := C) circuits parameter seeds job)
      (fun t => CopyCall (.inr t)) 0 := by
    intro job
    unfold evalJob
    have h := isQueryBoundP_mapM_sum (fun t => CopyCall (C := C) (.inr t)) (prfValue seeds)
      (fun _ => 0) hvalue job.points
    rw [List.map_const', List.sum_replicate, smul_zero] at h
    exact isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ 0
  have h := isQueryBoundP_mapM_sum (fun t => CopyCall (C := C) (.inr t)) (evalJob circuits parameter seeds)
    (fun _ => 0) hjob jobs
  rwa [List.map_const', List.sum_replicate, smul_zero] at h

end SimBounds

section SimulatorBound

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (jobs : List Job) (D : C.Coalition)
  (A : CeremonyAdversary C E)

/-- One answer of the simulator of the ceremony costs the steps of the adversary and the overhead of
the claim, for each parameter and each list of outputs. -/
theorem ceremonyHybridSimulator_answer_bound (hsize : 0 < settings.batchSize) (step fuel : ℕ)
    (hanswer : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (hround : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (hfuel : ∀ parameter, hybridRounds circuits parameter (chunks settings.batchSize jobs) ≤ fuel)
    (s : (ceremonyHybridSimulator K circuits settings jobs D A).State) (l : PublicParameter × List (List Bit)) :
    IsQueryBoundP ((ceremonyHybridSimulator K circuits settings jobs D A).answer s l) Counted
      (fuel * step + hybridOverhead settings C jobs) := by
  have h := simBatches_bound K circuits settings.mode D (batchAdversary A) l.1 (knownSeed s.2) step
    hanswer hround (chunks settings.batchSize jobs) l.2 (fun _ => some []) s.1
  rw [chunks_flatten _ hsize] at h
  refine (isQueryBoundP_bind h fun r _ => isQueryBoundP_pure Counted _ 0).mono ?_
  have := Nat.mul_le_mul_right step (hfuel l.1)
  unfold hybridOverhead
  omega

end SimulatorBound

/-! ## The outputs of the simulator -/

section Outputs

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (mode : ReshareMode) (D : C.Coalition)
  (A : MainAdversary C E) (parameter : PublicParameter) (seed : C.Term → HashOutput)

/-- The simulator reads the outputs so far only at the honest operators. -/
theorem simBatches_congr (bs : List (List Job)) (outputs : List (List Bit))
    (pre pre' : C.Party → Option (List (List Bit))) (st : A.State) (h : ∀ i, i ∉ D.1 → pre i = pre' i) :
    simBatches K circuits mode D A parameter seed bs outputs pre st =
      simBatches K circuits mode D A parameter seed bs outputs pre' st := by
  induction bs generalizing outputs pre pre' st with
  | nil =>
    simp only [simBatches]
    congr 2
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, h i]
  | cons batch rest ih =>
    have hc : (∀ i, i ∉ D.1 → (pre i).isSome) ↔ ∀ i, i ∉ D.1 → (pre' i).isSome :=
      forall_congr' fun i => imp_congr_right fun hi => by rw [h i hi]
    simp only [simBatches, hc]
    split_ifs
    · refine bind_congr fun known => bind_congr fun r => ih _ _ _ _ fun i hi => ?_
      simp only [nextOutputs, h i hi]
    · rfl

theorem lazyBatches_congr (seeds : C.Term → HashOutput) (bs : List (List Job))
    (pre pre' : C.Party → Option (List (List Bit))) (st : A.State) (h : ∀ i, i ∉ D.1 → pre i = pre' i) :
    lazyBatches K circuits mode D A parameter seed seeds bs pre st =
      lazyBatches K circuits mode D A parameter seed seeds bs pre' st := by
  induction bs generalizing pre pre' st with
  | nil =>
    simp only [lazyBatches]
    congr 2
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, h i]
  | cons batch rest ih =>
    have hc : (∀ i, i ∉ D.1 → (pre i).isSome) ↔ ∀ i, i ∉ D.1 → (pre' i).isSome :=
      forall_congr' fun i => imp_congr_right fun hi => by rw [h i hi]
    simp only [lazyBatches, hc]
    split_ifs
    · refine bind_congr fun outs => bind_congr fun known => bind_congr fun r => ih _ _ _ fun i hi => ?_
      simp only [nextOutputs, h i hi]
    · rfl

/-- A corrupt operator has no output of the simulator. An honest operator with an output has the
outputs of `F_ceremony` after its outputs so far, or two copy hashes collide (MPClan, App. B). Each
output of the functionality has the length of the outputs of its circuit. -/
theorem simBatches_inv (bs : List (List Job)) (outputs : List (List Bit))
    (pre : C.Party → Option (List (List Bit))) (st : A.State)
    (hlen : List.Forall₂ (fun (l : List Bit) (job : Job) => l.length = (circuits parameter job.kind).outputs.length)
      outputs bs.flatten) :
    MainRunInv prims (fun r s => (∀ i, i ∈ D.1 → r.2 i = none) ∧
        (¬ MainCopyCollision s → ∀ i, i ∉ D.1 → ∀ o, r.2 i = some o → ∃ o₀, pre i = some o₀ ∧ o = o₀ ++ outputs))
      (simBatches K circuits mode D A parameter seed bs outputs pre st) := by
  induction bs generalizing outputs pre st with
  | nil =>
    obtain rfl : outputs = [] := List.forall₂_nil_right_iff.1 hlen
    refine MainRunInv.pure _ fun _ => ⟨fun i hi => by simp [hi], fun _ i hi o ho => ⟨o, ?_, by simp⟩⟩
    simpa [hi] using ho
  | cons batch rest ih =>
    rw [List.flatten_cons] at hlen
    simp only [simBatches]
    refine MainRunInv.ite _ (fun _ => ?_) fun _ => MainRunInv.pure _ fun _ => ⟨fun _ _ => rfl, fun _ _ _ _ h => by cases h⟩
    intro s z hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p₁, -, hz⟩ := hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p₂, hp₂, hz⟩ := hz
    have htake := List.forall₂_take batch.length hlen
    have hdrop := List.forall₂_drop batch.length hlen
    rw [List.take_left] at htake
    rw [List.drop_left] at hdrop
    obtain ⟨hcorrupt, hhonest⟩ := ih _ _ _ hdrop p₂.2 z hz
    refine ⟨hcorrupt, fun hs i hi o ho => ?_⟩
    have hle := Grows.simulateQ (grows_localAnswer (C := C) prims) _ p₂.2 z hz
    have hgood := mainSimAnswerX_inv prims K D A mode _ _ _ p₁.2 p₂ hp₂
      fun hc => hs (by obtain ⟨a, b, u, hab, ha, hb⟩ := hc; exact ⟨a, b, u, hab, hle ha, hle hb⟩)
    obtain ⟨o₁, ho₁, rfl⟩ := hhonest hs i hi o ho
    unfold nextOutputs at ho₁
    rcases hpre : pre i with _ | o₀
    · simp [hpre] at ho₁
    rcases hv : p₂.1.2 i with _ | v
    · simp [hpre, hv] at ho₁
    simp only [hpre, hv, Option.bind_some, Option.map_some, Option.some.injEq] at ho₁
    have hassemble : assemble (batch.map (circuits parameter ·.kind)) v = outputs.take batch.length := by
      refine main_assemble_eq _ _ v (List.forall₂_map_right_iff.2 htake) fun g hg => ?_
      rw [← main_outputsOf_length] at hg
      exact hgood i hi v hv g hg
    refine ⟨o₀, rfl, ?_⟩
    rw [← ho₁, hassemble, List.append_assoc, List.take_append_drop]

end Outputs

/-! ## The inputs of a batch

The inputs of a batch are values of `H`. With `H` fixed, the inputs of the honest operators are valid
inputs of a batch, and the leak of `F_main` on them is the known input wires and the outputs of
`F_ceremony` for the batch. -/

section Inputs

variable (prims : Primitives) (circuits : Circuits) (D : C.Coalition) {x : C.Party → Keys C}
  {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairKeys : C.Pair → HashOutput}

/-- The leak of `F_main` reads only the inputs of the honest operators. -/
theorem mainIdealLeak_congr (jobs : List Circuit) (w w' : C.Party → MainInput C)
    (h : ∀ i, i ∉ D.1 → w i = w' i) : mainIdealLeak D jobs w = mainIdealLeak D jobs w' := by
  have hin : ∀ i, (if i ∈ D.1 then none else some (w i)) = if i ∈ D.1 then none else some (w' i) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, ↓reduceIte]
    · simp only [hi, ↓reduceIte, h i hi]
  unfold mainIdealLeak
  simp only [hin]

/-- `D_inputQuery` of `Proof/Tree.lean` for the context of the hybrid ceremony. -/
private theorem D_inputQuery_hybrid (h : Query C → HashOutput) (i : C.Party) (job : Job) (T : C.Term) :
    ThresholdLeanXmssSecurity.D prims h (inputQuery (hybridContext i (dealtKeys parameter seeds pairKeys i)) job) T =
      if i ∈ C.holders T then inputBits h seeds job T else [] := by
  unfold inputQuery
  simp only [D_bind, D_pure, D_mapM]
  rw [getD_terms_idxOf]
  by_cases hi : i ∈ C.holders T
  · simp only [hybridContext, hi, ↓reduceIte, D_flatMapM, prf, D_map, D_hashQuery, inputBits, dealtKeys]
  · simp [hybridContext, hi, D_pure]

/-- With `H` fixed, the inputs of the honest operators are `batchInputs` there. -/
private theorem D_honestInputQuery (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (h : Query C → HashOutput)
    (batch : List Job) (i : C.Party) (hi : i ∉ D.1) :
    ThresholdLeanXmssSecurity.D prims h (honestInputQuery D x batch) i = batchInputs h seeds batch i := by
  rw [honestInputQuery, D_sequenceFin]
  simp only [hi, ↓reduceIte, batchInputQuery, D_mapM, hx, batchInputs]
  refine List.map_congr_left fun job _ => ?_
  funext T
  rw [D_inputQuery_hybrid]

/-- `reconstruct` returns a value on which every holder with a view agrees, if one holder has a view. -/
private theorem reconstruct_of_some_agree {α : Type} [Inhabited α] (views : C.Party → Option (C.Term → α))
    (T : C.Term) (V : α) (hagree : ∀ i ∈ C.holders T, ∀ f, views i = some f → f T = V)
    (hsome : ∃ i ∈ C.holders T, (views i).isSome) : reconstruct views T = V := by
  unfold reconstruct
  rcases hl : (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) with _ | ⟨f, rest⟩
  · exfalso
    obtain ⟨i, hiT, hs⟩ := hsome
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hs
    have : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) :=
      List.mem_filterMap.2 ⟨i, List.mem_finRange i, by simp [hiT, hf]⟩
    rw [hl] at this
    simp at this
  · have : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) := by
      rw [hl]; exact List.mem_cons_self
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 this
    by_cases hiT : i ∈ C.holders T
    · simp only [hiT, ↓reduceIte] at hi
      simp [hagree i hiT f hi]
    · simp [hiT] at hi

/-- The known input wires of a job with `H` fixed. -/
private theorem D_knownInputQuery (h : Query C → HashOutput) (job : Job) (T : C.Term) :
    ThresholdLeanXmssSecurity.D prims h (knownInputQuery D (knownSeed (corruptInputs D x)) job) T =
      if KnownTo D.1 T then
        job.points.flatMap fun y => bitsOfDigest (truncateHash (h (.prf (knownSeed (corruptInputs D x) T) y)))
      else [] := by
  unfold knownInputQuery
  simp only [D_bind, D_pure, D_mapM]
  rw [getD_terms_idxOf]
  by_cases hT : KnownTo D.1 T
  · simp only [hT, ↓reduceIte, D_flatMapM, prf, D_map, D_hashQuery]
  · simp [hT, D_pure]

/-- The seed of a known term from the corrupt keys is the dealt seed. -/
private theorem knownSeed_corruptInputs (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (T : C.Term)
    (hT : KnownTo D.1 T) : knownSeed (corruptInputs D x) T = seeds T := by
  obtain ⟨j, hjD, hjT⟩ := hT
  unfold knownSeed
  rcases hs : C.parties.findSome? (fun j => if j ∈ C.holders T then (corruptInputs D x j).map (·.seed T) else none)
    with _ | s
  · rw [List.findSome?_eq_none_iff] at hs
    simpa [hjT, corruptInputs, hjD] using hs j (List.mem_finRange j)
  · obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some hs
    by_cases hkT : k ∈ C.holders T
    · by_cases hkD : k ∈ D.1
      · simp only [hkT, hkD, corruptInputs, ↓reduceIte, Option.map_some, Option.some.injEq] at hk
        rw [hs, Option.getD_some, ← hk, hx]
        simp [dealtKeys, hkT]
      · simp [hkT, hkD, corruptInputs] at hk
    · simp [hkT] at hk

/-- With `H` fixed, the inputs of the honest operators extend to valid inputs of a batch. Every holder
of a term computes it from the same seed. -/
theorem honestInputs_main (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (h : Query C → HashOutput)
    (batch : List Job) :
    ∃ w : C.Party → MainInput C, MainInputs (batch.map (circuits parameter ·.kind)) D w ∧
      ∀ i, i ∉ D.1 → w i = ThresholdLeanXmssSecurity.D prims h (honestInputQuery D x batch) i := by
  refine ⟨batchInputs h seeds batch, ?_, fun i hi => (D_honestInputQuery prims D hx h batch i hi).symm⟩
  obtain ⟨widths, hw, hh, hc⟩ := batchInputs_main h seeds circuits parameter batch
  exact ⟨widths, hw, fun i _ => hh i (by simp [noCoalition]), hc⟩

/-- With `H` fixed, the leak of `F_main` on the inputs of the honest operators is the view of the
known input wires and the outputs of the jobs in the clear. -/
theorem honestInputs_leak (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (h : Query C → HashOutput)
    (batch : List Job) :
    mainIdealLeak D (batch.map (circuits parameter ·.kind))
        (ThresholdLeanXmssSecurity.D prims h (honestInputQuery D x batch)) =
      (knownViews D (ThresholdLeanXmssSecurity.D prims h
          (batch.mapM (knownInputQuery D (knownSeed (corruptInputs D x))))),
        ThresholdLeanXmssSecurity.D prims h (batch.mapM (evalJob circuits parameter seeds))) := by
  have hW := D_honestInputQuery prims D hx h batch
  rw [D_mapM, D_mapM]
  unfold mainIdealLeak knownViews
  refine Prod.ext ?_ ?_
  · funext i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp only [hi, ↓reduceIte, Option.map_some, hW i hi, batchInputs, List.map_map]
      congr 1
      refine List.map_congr_left fun job _ => ?_
      funext T
      simp only [Function.comp_apply, D_knownInputQuery]
      by_cases hT : KnownTo D.1 T
      · by_cases hiT : i ∈ C.holders T <;> simp [hT, hiT, knownSeed_corruptInputs D hx T hT, inputBits]
      · by_cases hiT : i ∈ C.holders T <;> simp [hT, hiT]
  · dsimp only
    rw [← mainOutputs_batch prims h seeds circuits parameter batch]
    unfold mainOutputs
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨-, hk, -⟩ := List.mem_zipIdx hp
    simp only [List.length_map, zero_add] at hk
    congr 2
    funext T
    obtain ⟨j, hjT, hjD⟩ := main_exists_honest_holder D T
    rw [reconstruct_of_some_agree _ T (inputBits h seeds batch[p.2] T) _ ⟨j, hjT, by simp [hjD, hW j hjD, batchInputs, hk]⟩,
      reconstruct_of_some_agree _ T (inputBits h seeds batch[p.2] T) _ ⟨j, hjT, by simp [batchInputs, hk]⟩]
    · intro i hiT f hf
      simp [batchInputs, hk] at hf
      simp [← hf, hiT]
    · intro i hiT f hf
      by_cases hi : i ∈ D.1
      · simp [hi] at hf
      · simp [hi, hW i hi, batchInputs, hk] at hf
        simp [← hf, hiT]

end Inputs

end ThresholdLeanXmssSecurity
