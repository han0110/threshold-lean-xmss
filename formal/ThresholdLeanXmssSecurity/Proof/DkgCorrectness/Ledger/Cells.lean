import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Sound

/-!
# The honest cells of one ceremony by class

`NewWithin c start cache k` states that the cells of class `c` of `cache` that are not cells of
`start` lie in a set of at most `k` inputs. `phase_newWithin` is the count of one phase in
`streamWorld`. An adversary with `step` counted calls in a round and honest programs with the
budgets `budget` of class `c` add at most `fuel * step + ∑ j, budget j` new cells of class `c`.

`ceremonyProgram_bound` and `cutCeremony_bound` give the honest budgets of one ceremony and of its
prefix up to the check of batch `k`. `ledgerSplit` and `ledgerSalts` prove `LedgerSplit` and
`LedgerSalts`, and `prefixSplit`, `prefixSalts` and `prefixSound` are the ledgers at the end of the
prefix `ceremonyPrefix k`, with the fuel of the phase as a free parameter and the honest term of all
batches of the ceremony.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open FirstCounts DigestBudgets
open GameCount (CellIn)

attribute [local instance] Classical.propDecidable

/-! ## The new cells of a class -/

section NewCells

variable {C : Committee} (prims : Primitives)

/-- The cells of class `c` of `cache` that are not cells of `start` lie in a set of at most `k`
inputs. -/
def NewWithin (c : HashClass) (start cache : HashCache C) (k : ℕ) : Prop :=
  ∃ cells : Finset (Query C), cells.card ≤ k ∧ ∀ x, CellIn c x → cache x ≠ none → start x ≠ none ∨ x ∈ cells

theorem NewWithin.mono {c : HashClass} {start cache : HashCache C} {k l : ℕ} (h : NewWithin c start cache k)
    (hkl : k ≤ l) : NewWithin c start cache l := by
  obtain ⟨cells, hcard, hcover⟩ := h
  exact ⟨cells, hcard.trans hkl, hcover⟩

theorem newWithin_refl (c : HashClass) (cache : HashCache C) : NewWithin c cache cache 0 :=
  ⟨∅, le_rfl, fun _ _ h => Or.inl h⟩

/-- One call of `streamWorld` adds at most one new cell of class `c`, and only for a call of
`Adds c`. -/
theorem streamWorld_newWithin (c : HashClass) (D : C.Coalition) (t : (WorldSpec C).Domain) (start : HashCache C)
    (w : StreamState C) (k : ℕ) (hw : NewWithin c start w.1 k) :
    ∀ z ∈ support ((streamWorld prims D t).run w), NewWithin c start z.2.1 (k + if Adds c t then 1 else 0) := by
  intro z hz
  obtain ⟨key, hkey⟩ := streamWorld_cells prims c D t w z hz
  obtain ⟨cells, hcard, hcover⟩ := hw
  split_ifs with ht
  · refine ⟨insert key cells, (Finset.card_insert_le _ _).trans (by omega), fun x hx hzx => ?_⟩
    rcases hkey x hx hzx with h | ⟨_, rfl⟩
    · exact (hcover x hx h).imp_right Finset.mem_insert_of_mem
    · exact Or.inr (Finset.mem_insert_self _ _)
  · refine ⟨cells, by omega, fun x hx hzx => ?_⟩
    rcases hkey x hx hzx with h | ⟨h, _⟩
    · exact hcover x hx h
    · exact absurd h ht

/-- A computation of the world with at most `n` calls of `Adds c` adds at most `n` new cells of class
`c` under `streamWorld`. -/
theorem simulateQ_newWithin (c : HashClass) (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ n, IsQueryBoundP oa (Adds c) n → ∀ (start : HashCache C) w k, NewWithin c start w.1 k →
      ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run w), NewWithin c start z.2.1 (k + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ start w k hw z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw.mono (Nat.le_add_right _ _)
  | query_bind t f ih =>
    intro n hn start w k hw z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    refine (ih y.1 _ (hn.2 y.1) start y.2 _ (streamWorld_newWithin prims c D t start w k hw y hy) z hz).mono ?_
    split_ifs with ht
    · have := hn.1.resolve_left (not_not.2 ht)
      omega
    · omega

end NewCells

/-! ## The calls of a class in one phase -/

section Phase

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A phase on the real network makes at most `fuel * step` calls of the adversary and the sum of the
honest budgets of class `c` of calls of `Adds c`. -/
theorem executePhase_adds (c : HashClass) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step fuel : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step) (st : net.State)
    {α : Type} (program : C.Party → PartyM C E RealSpec α) (budget : C.Party → ℕ)
    (hp : ∀ j, j ∉ D.1 → ClassBound c (program j) (budget j)) :
    IsQueryBoundP (executePhase worldRoles D net noFunctionality fuel st program) (Adds c)
      (fuel * step + ∑ j, budget j) :=
  isQueryBoundP_add (fun _ h => adds_or c h) _ _ _
    (ownAdds_executePhase c D net step (fun s m => (hround s m).of_imp fun _ h => counted_of_inClass h) fuel st
      program)
    (executePhase_bound c D net fuel st program budget hp)

/-- The count of one phase. From each world, a phase in `streamWorld` adds at most `fuel * step` cells
of the adversary and the sum of the honest budgets of new cells of class `c`. -/
theorem phase_newWithin (c : HashClass) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step fuel : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step) (st : net.State)
    {α : Type} (program : C.Party → PartyM C E RealSpec α) (budget : C.Party → ℕ)
    (hp : ∀ j, j ∉ D.1 → ClassBound c (program j) (budget j)) (w : StreamState C) :
    ∀ r ∈ support ((simulateQ (streamWorld prims D)
        (executePhase worldRoles D net noFunctionality fuel st program)).run w),
      NewWithin c w.1 r.2.1 (fuel * step + ∑ j, budget j) := by
  intro r hr
  have h := simulateQ_newWithin prims c D _ _ (executePhase_adds c D net step fuel hround st program budget hp)
    w.1 w 0 (newWithin_refl c w.1) r hr
  rwa [Nat.zero_add] at h

end Phase

/-! ## The honest budgets of one ceremony and of its prefix -/

section Budgets

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings) {c : HashClass}

attribute [local instance] inhabitedField

/-- The class `c` is not a class of the PRSS randomness, of the coins, of the PRF or of the setup. -/
def BatchClass (c : HashClass) : Prop := c ≠ .stream ∧ c ≠ .challenge ∧ c ≠ .signing ∧ c ≠ .prssSetup

omit [Fintype E] [DecidableEq E] in
/-- The program of one ceremony makes the calls of its batches. -/
theorem ceremonyProgram_bound (hc : BatchClass c) (i : C.Party) {σ : Type} (s : CeremonyStart C σ) :
    ClassBound c (ceremonyProgram K circuits settings i s)
      ((chunks settings.batchSize s.jobs).length * (digestCost C c + copyCost C c)) := by
  unfold ceremonyProgram
  rcases s.keys i with _ | keys
  · exact ClassBound.failure.mono (Nat.zero_le _)
  · refine (ClassBound.bind (m := 0)
      (ceremonyRun_bound K circuits settings hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 i keys s.jobs s.counters)
      fun p => ?_).mono (Nat.add_zero _).le
    rcases p with ⟨_ | outputs, st⟩
    · exact ClassBound.failure
    · exact ClassBound.pure _

/-- A program that stops at a check makes at most `n` local calls in class `c` before its stop or end. -/
def PausedBound {α : Type} (x : Paused K α) (n : ℕ) : Prop := ClassBound c x.run n

/-- A program on the counters that stops at a check makes at most `n` local calls in class `c` from
each counter pair. -/
def CutBound {α : Type} (x : CutM K α) (n : ℕ) : Prop := ∀ st, PausedBound K (c := c) (x.run st) n

variable {K}

omit [Fintype E] [DecidableEq E] in
theorem PausedBound.bind {α β : Type} {x : Paused K α} {f : α → Paused K β} {n m : ℕ}
    (hx : PausedBound K (c := c) x n) (hf : ∀ a, PausedBound K (c := c) (f a) m) :
    PausedBound K (c := c) (x >>= f) (n + m) := by
  unfold PausedBound
  rw [Paused.run_bind]
  refine ClassBound.bind hx fun o => ?_
  rcases o with a | ⟨point, rest⟩
  · exact hf a
  · exact (ClassBound.pure _).mono (Nat.zero_le _)

omit [Fintype E] [DecidableEq E] in
theorem CutBound.mono {α : Type} {x : CutM K α} {n m : ℕ} (h : CutBound K (c := c) x n) (hnm : n ≤ m) :
    CutBound K (c := c) x m := fun st => ClassBound.mono (h st) hnm

omit [Fintype E] [DecidableEq E] in
theorem CutBound.pure {α : Type} (a : α) : CutBound K (c := c) (pure a : CutM K α) 0 := fun _ =>
  ClassBound.pure _

omit [Fintype E] [DecidableEq E] in
theorem CutBound.bind {α β : Type} {x : CutM K α} {f : α → CutM K β} {n m : ℕ} (hx : CutBound K (c := c) x n)
    (hf : ∀ a, CutBound K (c := c) (f a) m) : CutBound K (c := c) (x >>= f) (n + m) := fun st => by
  rw [StateT.run_bind]
  exact PausedBound.bind (hx st) fun a => hf a.1 a.2

omit [Fintype E] [DecidableEq E] in
theorem CutBound.zero_bind {α β : Type} {x : CutM K α} {f : α → CutM K β} {n : ℕ} (hx : CutBound K (c := c) x 0)
    (hf : ∀ a, CutBound K (c := c) (f a) n) : CutBound K (c := c) (x >>= f) n :=
  (CutBound.bind hx hf).mono (Nat.zero_add _).le

omit [Fintype E] [DecidableEq E] in
theorem CutBound.bind_zero {α β : Type} {x : CutM K α} {f : α → CutM K β} {n : ℕ} (hx : CutBound K (c := c) x n)
    (hf : ∀ a, CutBound K (c := c) (f a) 0) : CutBound K (c := c) (x >>= f) n :=
  (CutBound.bind hx hf).mono (Nat.add_zero _).le

omit [Fintype E] [DecidableEq E] in
theorem CutBound.get : CutBound K (c := c) (get : CutM K (ℕ × ℕ)) 0 := fun _ => ClassBound.pure _

omit [Fintype E] [DecidableEq E] in
theorem CutBound.set (s : ℕ × ℕ) : CutBound K (c := c) (set s : CutM K PUnit) 0 := fun _ => ClassBound.pure _

omit [Fintype E] [DecidableEq E] in
theorem CutBound.lift {α : Type} {y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α} {n : ℕ} (h : StateBound c y n) :
    CutBound K (c := c) (CutM.lift y) n := fun st => by
  unfold PausedBound
  rw [CutM.lift_run]
  unfold Paused.lift ClassBound
  rw [OptionT.run_map]
  exact (isQueryBoundP_map_iff _ _ _).2 (h st)

omit [Fintype E] [DecidableEq E] in
theorem CutBound.stop (point : CheckPoint C) :
    CutBound K (c := c) (StateT.lift (Paused.stop point) : CutM K (RunState C)) 0 := fun st => by
  change PausedBound K (c := c) (Paused.stop point >>= fun a => (Pure.pure (a, st) : Paused K _)) (0 + 0)
  exact PausedBound.bind (ClassBound.pure _) fun a => ClassBound.pure _

omit [Fintype E] [DecidableEq E] in
theorem CutBound.mapM {α β : Type} (f : α → CutM K β) (n : ℕ) (hf : ∀ a, CutBound K (c := c) (f a) n) :
    ∀ xs : List α, CutBound K (c := c) (xs.mapM f) (xs.length * n)
  | [] => by simpa using CutBound.pure (K := K) (c := c) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (hf a).bind fun b => (CutBound.mapM f n hf xs).bind fun bs => CutBound.pure (K := K) (c := c) (b :: bs)

variable (K)

omit [Fintype E] [DecidableEq E] in
/-- A full real batch makes the digest calls of one comparison and the copy calls of one `OpenRep`. -/
theorem realBatch_bound (hc : BatchClass c) (ctx : Context C) (parameter : PublicParameter) (js : List Job) :
    StateBound c (realBatch K circuits settings.mode ctx parameter js) (digestCost C c + copyCost C c) := by
  unfold realBatch
  refine StateBound.zero_bind StateBound.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine StateBound.zero_bind (StateBound.lift_zero ((ClassBound.mapM _ 0
    (fun job => inputShares_bound _ hc.2.2.1 job) _).mono (by simp))) fun inputs => ?_
  refine StateBound.bind_zero' (StateBound.lift (runJobs_bound K _ hc.1 hc.2.1 _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact StateBound.bind_zero (StateBound.set _) fun _ => StateBound.pure _

omit [Fintype E] [DecidableEq E] in
/-- The cut batch makes no digest call, and at most the copy calls of one `OpenRep` after its stop. -/
theorem cutBatch_bound (hs : c ≠ .stream) (hsig : c ≠ .signing) (ctx : Context C) (parameter : PublicParameter)
    (js : List Job) :
    CutBound K (c := c) (cutBatch K circuits settings ctx parameter js) (digestCost C c + copyCost C c) := by
  unfold cutBatch
  refine CutBound.zero_bind CutBound.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine CutBound.zero_bind (CutBound.lift (StateBound.lift_zero ((ClassBound.mapM _ 0
    (fun job => inputShares_bound _ hsig job) _).mono (by simp)))) fun inputs => ?_
  refine CutBound.zero_bind (CutBound.lift (StateBound.lift_zero
    (runJobsHead_bound K ctx hs _ _ _ _))) fun head => ?_
  rcases head with ⟨head, state⟩
  refine CutBound.zero_bind (CutBound.stop _) fun after => ?_
  have hout : StateBound c ((realRunBuildingBlocks K ctx settings.mode).output head.2.1 head.2.2.1 :
      RunM C E RealSpec _) (copyCost C c) := StateBound.lift (openRep_bound K ctx _ _)
  refine ((CutBound.bind (CutBound.lift (StateBound.lift (σ := ℕ × ℕ) (hout after))) fun r =>
    CutBound.zero_bind (CutBound.set _) fun _ => CutBound.pure _).mono (n := copyCost C c + 0) (by omega))

omit [Fintype E] [DecidableEq E] in
/-- One ceremony that stops at the check of the batch with the tag `k` makes at most the calls of its
batches. -/
theorem cutRun_bound (hc : BatchClass c) (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    CutBound K (c := c) (cutRun K circuits settings k i keys jobs)
      ((chunks settings.batchSize jobs).length * (digestCost C c + copyCost C c)) := by
  unfold cutRun batched
  refine CutBound.zero_bind (CutBound.lift (StateBound.lift_zero (prssSetup_bound hc.2.2.2 i))) fun prss => ?_
  refine CutBound.bind_zero (CutBound.mapM _ _ (fun js => ?_) _) fun _ => CutBound.pure _
  refine CutBound.zero_bind CutBound.get fun p => ?_
  rcases p with ⟨_, tag⟩
  dsimp only
  split_ifs
  · exact cutBatch_bound K circuits settings hc.1 hc.2.2.1 _ _ _
  · exact CutBound.lift (realBatch_bound K circuits settings hc _ _ _)

omit [Fintype E] [DecidableEq E] in
/-- The program of one operator in the prefix of one ceremony up to the check of batch `k` makes at
most the calls of the batches of the ceremony. -/
theorem cutCeremony_bound (hc : BatchClass c) (k : ℕ) (i : C.Party) {σ : Type} (s : CeremonyStart C σ) :
    ClassBound c (cutCeremony K circuits settings k i s)
      ((chunks settings.batchSize s.jobs).length * (digestCost C c + copyCost C c)) := by
  unfold cutCeremony
  rcases s.keys i with _ | keys
  · exact ClassBound.failure.mono (Nat.zero_le _)
  · exact cutRun_bound K circuits settings hc _ i keys s.jobs s.counters

end Budgets

/-! ## The ledgers of the history, digest and salt cells -/

section Ledgers

variable {C : Committee}

/-- The class `digest` is a class of the batches. -/
theorem batchClass_digest : BatchClass .digest := ⟨nofun, nofun, nofun, nofun⟩

/-- The honest budget of the class `digest` of `batches` batches over all operators. -/
theorem sum_digestBudget (batches : ℕ) :
    ∑ _j : C.Party, batches * (digestCost C .digest + copyCost C .digest) = batches * termHashes C := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [digestCost, copyCost, ↓reduceIte, reduceCtorEq, Nat.add_zero, check_terms_length]
  unfold termHashes termCount
  ring

/-- The history and digest cells of a cache are its new cells of class `digest` and the cells of the
start. -/
theorem splitCacheBound_of_newWithin {start cache : HashCache C} {n m : ℕ}
    (h0 : SplitCacheBound (splitRegionCache SplitHashDomain start) n) (h : NewWithin .digest start cache m) :
    SplitCacheBound (splitRegionCache SplitHashDomain cache) (n + m) := by
  obtain ⟨S, hS, hcover⟩ := h0
  obtain ⟨cells, hcells, hnew⟩ := h
  refine ⟨S ∪ cells, (Finset.card_union_le _ _).trans (by omega), fun q hq => ?_⟩
  simp only [splitRegionCache, QueryCache.ofFn_apply] at hq
  split_ifs at hq with hP
  · have hcell : CellIn .digest q := by
      cases q <;> simp_all [SplitHashDomain, CellIn, queryClass]
    rcases hnew q hcell hq with h | h
    · exact Finset.mem_union_left _ (hcover q (by simp [splitRegionCache, hP, h]))
    · exact Finset.mem_union_right _ h
  · exact absurd rfl hq

/-- The salt of a digest input. -/
def saltOf : Query C → List Bit
  | .digest salt _ => salt
  | _ => []

/-- The digest salts of a cache are the salts of its new cells of class `digest` and the salts of the
start. -/
theorem digestSalts_of_newWithin {start cache : HashCache C} {salts : Finset (List Bit)} {m : ℕ}
    (h0 : DigestSaltsCovered start salts) (h : NewWithin .digest start cache m) :
    ∃ salts' : Finset (List Bit), DigestSaltsCovered cache salts' ∧ salts'.card ≤ salts.card + m := by
  obtain ⟨cells, hcells, hnew⟩ := h
  refine ⟨salts ∪ cells.image saltOf, fun salt d hd => ?_, (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_image_le.trans hcells) _)⟩
  rcases hnew (.digest salt d) rfl hd with h | h
  · exact Finset.mem_union_left _ (h0 salt d h)
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, rfl⟩)

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives)
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] in
/-- The new history and digest cells of one ceremony, `rounds * step` of the adversary and
`batches * termHashes C` of the honest operators. -/
theorem ceremony_newWithin (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step)
    (c : CeremonyStart C net.State) (world : StreamState C) :
    ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world),
      NewWithin .digest world.1 r.2.1 (rounds * step + (chunks settings.batchSize c.jobs).length * termHashes C) := by
  intro r hr
  have h := phase_newWithin prims .digest D net step rounds hround c.adversary _ _
    (fun j _ => ceremonyProgram_bound K circuits settings batchClass_digest j c) world r hr
  rwa [sum_digestBudget] at h

omit [Fintype E] [DecidableEq E] in
/-- The new history and digest cells of the prefix of one ceremony up to the check of batch `k`, in a
phase of `rounds` rounds. -/
theorem prefix_newWithin (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds k : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step)
    (c : CeremonyStart C net.State) (world : StreamState C) :
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world),
      NewWithin .digest world.1 z.2.1 (rounds * step + (chunks settings.batchSize c.jobs).length * termHashes C) := by
  intro z hz
  have h := phase_newWithin prims .digest D net step rounds hround c.adversary _ _
    (fun j _ => cutCeremony_bound K circuits settings batchClass_digest k j c) world z hz
  rwa [sum_digestBudget] at h

omit [Fintype E] [DecidableEq E] in
/-- `LedgerSplit`. -/
theorem ledgerSplit : LedgerSplit prims K circuits settings := by
  intro D net step rounds hround n c world hstart r hr
  rw [Nat.add_assoc]
  exact splitCacheBound_of_newWithin hstart (ceremony_newWithin prims K circuits settings D net step rounds hround
    c world r hr)

omit [Fintype E] [DecidableEq E] in
/-- `LedgerSalts`. -/
theorem ledgerSalts : LedgerSalts prims K circuits settings := by
  intro D net step rounds hround n c world ⟨salts, hcover, hcard⟩ r hr
  obtain ⟨salts', h, hcard'⟩ := digestSalts_of_newWithin hcover
    (ceremony_newWithin prims K circuits settings D net step rounds hround c world r hr)
  exact ⟨salts', h, hcard'.trans (by omega)⟩

omit [Fintype E] [DecidableEq E] in
/-- The ledger of the history and digest cells at the end of the prefix of one ceremony up to the check
of batch `k`, in a phase of `rounds` rounds. -/
theorem prefixSplit (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds k : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step) (n : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (hstart : SplitCacheBound (splitRegionCache SplitHashDomain world.1) n) :
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world),
      SplitCacheBound (splitRegionCache SplitHashDomain z.2.1)
        (n + rounds * step + (chunks settings.batchSize c.jobs).length * termHashes C) := by
  intro z hz
  rw [Nat.add_assoc]
  exact splitCacheBound_of_newWithin hstart (prefix_newWithin prims K circuits settings D net step rounds k hround
    c world z hz)

omit [Fintype E] [DecidableEq E] in
/-- The ledger of the digest salts at the end of the prefix of one ceremony up to the check of batch
`k`, in a phase of `rounds` rounds. -/
theorem prefixSalts (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds k : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step) (n : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (hstart : ∃ salts : Finset (List Bit), DigestSaltsCovered world.1 salts ∧ salts.card ≤ n) :
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world),
      ∃ salts : Finset (List Bit), DigestSaltsCovered z.2.1 salts ∧
        salts.card ≤ n + rounds * step + (chunks settings.batchSize c.jobs).length * termHashes C := by
  intro z hz
  obtain ⟨salts, hcover, hcard⟩ := hstart
  obtain ⟨salts', h, hcard'⟩ := digestSalts_of_newWithin hcover
    (prefix_newWithin prims K circuits settings D net step rounds k hround c world z hz)
  exact ⟨salts', h, hcard'.trans (by omega)⟩

end Ledgers

/-! ## The ledger of the coin keys at the end of a prefix -/

section PrefixSound

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

attribute [local instance] inhabitedField

/-- The flows of a program on the counters that stops at a check, from each counter pair. -/
def CutFlows {α : Type} (x : CutM K α) (n : ℕ) : Prop := ∀ st, Flows ((x.run st).run) n

variable {K}

omit [Fintype E] [DecidableEq E] in
theorem CutFlows.mono {α : Type} {x : CutM K α} {n m : ℕ} (h : CutFlows K x n) (hnm : n ≤ m) : CutFlows K x m :=
  fun st => (h st).mono hnm

omit [Fintype E] [DecidableEq E] in
theorem CutFlows.of_cutBound {α : Type} {x : CutM K α} (h : CutBound K (c := .challenge) x 0) : CutFlows K x 0 :=
  fun st => Flows.of_classBound (h st)

omit [Fintype E] [DecidableEq E] in
theorem CutFlows.bind {α β : Type} {x : CutM K α} {f : α → CutM K β} {n m : ℕ} (hx : CutFlows K x n)
    (hf : ∀ a, CutFlows K (f a) m) : CutFlows K (x >>= f) (n + m) := fun st => by
  rw [StateT.run_bind, Paused.run_bind]
  refine Flows.bind (hx st) fun o _ => ?_
  rcases o with a | ⟨point, rest⟩
  · exact hf a.1 a.2
  · exact (Flows.of_classBound (ClassBound.pure _)).mono (Nat.zero_le _)

omit [Fintype E] [DecidableEq E] in
theorem CutFlows.lift {α : Type} {y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α} {n : ℕ} (h : SFlows y n) :
    CutFlows K (CutM.lift y) n := fun st => by
  rw [CutM.lift_run]
  show Flows (Sum.inl <$> y.run st) n
  rw [map_eq_bind_pure_comp]
  exact (Flows.bind (m := 0) (h st) fun a _ => Flows.of_classBound (ClassBound.pure _)).mono (Nat.add_zero _).le

omit [Fintype E] [DecidableEq E] in
theorem CutFlows.mapM {α β : Type} (f : α → CutM K β) (n : ℕ) :
    ∀ xs : List α, (∀ a ∈ xs, CutFlows K (f a) n) → CutFlows K (xs.mapM f) (xs.length * n)
  | [], _ => by simpa using CutFlows.of_cutBound (CutBound.pure (K := K) (c := .challenge) ([] : List β))
  | a :: xs, hf => by
    rw [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (hf a (List.mem_cons_self ..)).bind fun b => (CutFlows.mapM f n xs fun a' ha' =>
        hf a' (List.mem_cons_of_mem _ ha')).bind fun bs =>
          CutFlows.of_cutBound (CutBound.pure (K := K) (c := .challenge) (b :: bs))

variable (K)

omit [Fintype E] [DecidableEq E] in
/-- One ceremony that stops at the check of the batch with the tag `k` makes at most `batchCoins`
coin calls for each batch. -/
theorem cutFlows_cutRun (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (hadm : AdmissibleJobs circuits settings jobs) :
    CutFlows K (cutRun K circuits settings k i keys jobs)
      ((chunks settings.batchSize jobs).length * batchCoins circuits settings) := by
  unfold cutRun batched
  refine (CutFlows.bind (n := 0) (CutFlows.of_cutBound (CutBound.lift (StateBound.lift_zero
    (prssSetup_bound (c := .challenge) nofun i)))) fun prss => ?_).mono (Nat.zero_add _).le
  refine (CutFlows.bind (m := 0) (CutFlows.mapM _ _ _ fun js hjs => ?_)
    fun _ => CutFlows.of_cutBound (CutBound.pure _)).mono (Nat.add_zero _).le
  refine (CutFlows.bind (n := 0) (CutFlows.of_cutBound CutBound.get) fun p => ?_).mono (Nat.zero_add _).le
  rcases p with ⟨_, tag⟩
  dsimp only
  split_ifs
  · exact (CutFlows.of_cutBound ((cutBatch_bound K circuits settings (c := .challenge) nofun nofun _ _ _).mono
      (by simp [digestCost, copyCost]))).mono (Nat.zero_le _)
  · exact CutFlows.lift (sflows_realBatch K circuits settings _ _ js _ (hadm keys.parameter js hjs).2)

omit [Fintype E] [DecidableEq E] in
/-- The coin calls of the program of one honest operator in the prefix of one ceremony up to the check
of batch `k`. -/
theorem flows_cutCeremony (k : ℕ) (i : C.Party) {σ : Type} (s : CeremonyStart C σ)
    (hadm : AdmissibleJobs circuits settings s.jobs) :
    Flows (cutCeremony K circuits settings k i s) ((chunks settings.batchSize s.jobs).length * batchCoins circuits settings) := by
  unfold cutCeremony
  rcases s.keys i with _ | keys
  · exact (Flows.of_classBound ClassBound.failure).mono (Nat.zero_le _)
  · exact cutFlows_cutRun K circuits settings _ i keys s.jobs hadm s.counters

omit [Fintype E] [DecidableEq E] in
/-- The ledger of the coin inputs and of the expansion keys at the end of the prefix of one ceremony
of admissible jobs up to the check of batch `k`, in a phase of `rounds` rounds. -/
theorem prefixSound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step rounds k : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step) (coins keys : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hadm : AdmissibleJobs circuits settings c.jobs)
    (hstart : ∃ (seen : Finset (Query C)) (expansionKeys : Finset HashOutput), SoundCache 0 world.1 seen expansionKeys ∧
      seen.card ≤ coins ∧ expansionKeys.card ≤ keys) :
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world),
      ∃ (seen : Finset (Query C)) (expansionKeys : Finset HashOutput), SoundCache 0 z.2.1 seen expansionKeys ∧
        seen.card ≤ coins + rounds * step + coinKeysOf circuits settings C (chunks settings.batchSize c.jobs).length ∧
        expansionKeys.card ≤ keys + coinKeysOf circuits settings C (chunks settings.batchSize c.jobs).length := by
  intro z hz
  obtain ⟨seen, ekeys, hs, hseen, hkeys⟩ := hstart
  obtain ⟨seen', keys', h', hc', hk'⟩ := phase_soundCache prims D net step rounds hround c.adversary _ _
    (fun j _ => flows_cutCeremony K circuits settings k j c hadm) world seen ekeys hs z hz
  rw [sum_batchCoins] at hc' hk'
  exact ⟨seen', keys', h', by omega, by omega⟩

end PrefixSound

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerSplit

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerSalts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerSalts

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.prefixSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.prefixSplit

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.prefixSalts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.prefixSalts

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.prefixSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.prefixSound
