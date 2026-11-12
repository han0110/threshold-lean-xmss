import ThresholdLeanXmssSecurity.Proof.TreeCheckCoinClock
import ThresholdLeanXmssSecurity.Proof.TreeCheckSigningDisc

/-! # Coin-label floors for audited callers

Audits preserve the inherited label floor through every supported result.
The first-run continuation keeps this floor under every public signing-head
choice. Quiet caller prefixes also have the higher floor at their next
check's label, using the local party's circuit parameter.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckCoinFloor
open TreeCheckCoinClock TreeCheckHonestDisc TreeCheckSigningDisc
open TreeCheckWalkRecipe TreeCheckWalkState TreeSimHashCount
attribute [local instance] Classical.propDecidable
attribute [local irreducible] treeLockstepPublicChoiceCode merkleNode merklePath Concrete.layerRoot tweakable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β : Type}

def RunFloor (p : RunM C E RealSpec α) : Prop :=
  ∀ st limit, limit ≤ st.label → CheckFloor limit (p.run st).run

theorem RunFloor.pure (a : α) : RunFloor (C := C) (E := E) (Pure.pure a) :=
  fun _ _ _ => CheckFloor.pure _ _

theorem RunFloor.of_quiet {p : RunM C E RealSpec α} (h : RunBudget CheckQuery p 0) :
    RunFloor p := fun st _ _ => CheckFloor.of_quiet (h st)

theorem RunFloor.bind {n : ℕ} {p : RunM C E RealSpec α} {f : α → RunM C E RealSpec β}
    (h : RunFloor p) (labels : LockstepLabels n p) (rest : ∀ a, RunFloor (f a)) :
    RunFloor (p >>= f) := by
  intro st limit le
  rw [StateT.run_bind]
  apply (h st limit le).party_bind
  rintro ⟨a, mid⟩ ha
  apply rest a mid limit
  rw [labels st a mid ha]
  omega

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

theorem runFloor_check (ctx : Context C) (tuples : List (Tuple C)) :
    RunFloor (check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples) := by
  intro st limit le
  have floor := (clocked_check K ctx tuples st).floor
    (fun _ _ h => Nat.add_le_add_left (checkClock_mono _ h) _)
  apply floor.mono
  simpa only [checkClock_zero, Nat.add_zero] using le

-- Port of TreeCheckWalkPointTransfer.openRep_quiet, using CheckQuery.
theorem openRep_checkQuiet (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    PartyBudget CheckQuery (openRep K ctx v count : PartyM C E RealSpec _) 0 := by
  have hc (f : C.Term → List Bit) : PartyBudget CheckQuery
      (oracleStep (C.terms.mapM fun T => hashQuery (.copy (f T))) : PartyM C E RealSpec _) 0 :=
    oracle_bound (by
      simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
        (fun T => hashQuery (.copy (f T))) 0 C.terms
        (fun _ _ => TreeCheckHonestDisc.hash_zero _ (by simp [CheckQuery])))
  unfold openRep
  simpa using (hc _).bind (fun ds =>
    (party_quiet_of_zero (PartyBound.exchange _)).bind (fun inbox =>
      (hc _).bind (fun copies =>
        (party_quiet_of_zero (PartyBound.require _)).bind
          (fun _ => PartyBudget.pure _))))

variable (circuits : Circuits) (settings : Settings)

/-- The output counter follows the accepted exact batch-label equation. -/
theorem audit_counter_eq (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (run : some a ∈ support ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial).run) :
    a.2.1 = initial.1 + batchLabels circuits ctx.keys.parameter jobs := by
  obtain ⟨_, _, _, _, counter⟩ :=
    lockstep_batchAudit circuits K settings ctx jobs initial a.1.1 a.1.2 a.2 run
  exact congrArg Prod.fst counter

theorem audit_counter (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (run : some a ∈ support ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial).run) :
    initial.1 ≤ a.2.1 := by
  rw [audit_counter_eq K circuits settings ctx jobs initial a run]
  omega

theorem audit_check_counter (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (run : some a ∈ support ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial).run) :
    initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1 ≤ a.2.1 := by
  rw [audit_counter_eq K circuits settings ctx jobs initial a run]
  unfold batchLabels
  omega

/-- The quiet batch prefix permits a floor at the first check's exact label. -/
theorem audit_check_floor (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    CheckFloor (initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1)
      ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial).run := by
  rw [treeSimCheckBatchAudit_run_prefix]
  apply (CheckFloor.of_quiet (batchPrefix_quiet K circuits settings ctx jobs initial)).party_bind
  intro data hdata
  obtain ⟨_, label, _, _, _⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs initial data hdata
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  simp only [bind_assoc, pure_bind]
  apply (runFloor_check K ctx data.2.1.2 data.2.2 _ (by omega)).party_bind
  intro checked _
  apply (CheckFloor.of_quiet (openRep_checkQuiet K ctx _ _)).party_bind
  intro opened _
  exact .pure _ _

theorem audit_floor (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (limit : ℕ) (le : limit ≤ initial.1) :
    CheckFloor limit ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial).run :=
  (audit_check_floor K circuits settings ctx jobs initial).mono (by omega)

theorem auditMap_counter (ctx : Context C) (chunks : List (List Job)) (initial : ℕ × ℕ)
    (a : (List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (run : some a ∈ support ((chunks.mapM
      (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial).run) :
    initial.1 ≤ a.2.1 := by
  induction chunks generalizing initial a with
  | nil =>
    have equal : a = (([], []), initial) := by
      simpa only [List.mapM_nil, WriterT.run_pure, StateT.run_pure, OptionT.run_pure,
        support_pure, Set.mem_singleton_iff, Option.some.injEq, List.empty_eq] using run
    rw [equal]
  | cons head tail ih =>
    rw [auditChunks_cons] at run
    obtain ⟨middle, hm, rest⟩ := treeSimCheck_some_bind _ _ _ run
    obtain ⟨last, hl, done⟩ := treeSimCheck_some_bind _ _ _ rest
    have equal : a = ((middle.1.1 :: last.1.1, middle.1.2 ++ last.1.2), last.2) := by
      simpa only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] using done
    rw [equal]
    exact le_trans (audit_counter K circuits settings ctx head initial middle hm) (ih middle.2 last hl)

theorem auditMap_floor (ctx : Context C) (chunks : List (List Job)) (initial : ℕ × ℕ)
    (limit : ℕ) (le : limit ≤ initial.1) :
    CheckFloor limit ((chunks.mapM
      (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial).run := by
  induction chunks generalizing initial with
  | nil => exact .pure _ _
  | cons head tail ih =>
    rw [auditChunks_cons]
    apply (audit_floor K circuits settings ctx head initial limit le).party_bind
    intro middle hm
    apply (ih middle.2 (le_trans le (audit_counter K circuits settings ctx head initial middle hm))).party_bind
    intro last _
    exact .pure _ _

theorem batched_floor (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (limit : ℕ) (le : limit ≤ initial.1) :
    CheckFloor limit ((batched settings.batchSize
      (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx) jobs).run.run initial).run := by
  rw [auditBatched_run]
  apply (auditMap_floor K circuits settings ctx _ initial limit le).party_bind
  intro _ _
  exact .pure _ _

theorem tweakable_party_quiet (code : OracleComp HashSpec α) :
    PartyBudget CheckQuery (oracleStep (tweakable code) : PartyM C E RealSpec α) 0 :=
  oracle_bound (tweakable_quiet code)

theorem topFinish_quiet (parameter : PublicParameter) (outputs : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) :
    PartyBudget CheckQuery (treeLockstepTopFinish (E := E) parameter outputs records) 0 := by
  unfold treeLockstepTopFinish
  exact (tweakable_party_quiet (C := C) (E := E) _).bind (m := 0) (fun _ => PartyBudget.pure _)

theorem bottomFinish_quiet (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (values : Option (List (List Bit)))
    (records : List (TreeSimCheckBatchRecord C)) :
    PartyBudget CheckQuery
      (treeLockstepBottomFinish (E := E) parameter top b outputs root randomness values records) 0 := by
  cases values with
  | none => exact party_quiet_of_zero PartyBound.failure
  | some values =>
    unfold treeLockstepBottomFinish
    dsimp only
    apply (tweakable_party_quiet (C := C) (E := E) _).bind (m := 0)
    intro path
    apply (tweakable_party_quiet (C := C) (E := E) _).bind (m := 0)
    intro root
    split_ifs
    · exact party_quiet_of_zero PartyBound.failure
    · exact PartyBudget.pure _

/-- Every supported public head continues from the inherited counter. -/
theorem firstRest_floor (ctx : Context C) (top : TopTree) (tree : Tree)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (limit : ℕ) (le : limit ≤ a.2.1) :
    CheckFloor limit (treeLockstepFirstRest K circuits settings ctx top tree a).run := by
  rcases a with ⟨⟨values, records⟩, counters⟩
  cases values with
  | none => exact .pure _ _
  | some outputs =>
    cases tree with
    | top => exact CheckFloor.of_quiet (topFinish_quiet ctx.keys.parameter outputs records)
    | bottom b =>
      unfold treeLockstepFirstRest
      dsimp only
      apply (CheckFloor.of_quiet (tweakable_party_quiet (C := C) (E := E) _)).party_bind
      intro chosen _
      cases chosen with
      | none => exact .pure _ _
      | some choice =>
        rcases choice with ⟨root, randomness, encoding⟩
        apply (batched_floor K circuits settings ctx _ counters limit le).party_bind
        intro result _
        exact CheckFloor.of_quiet (bottomFinish_quiet ctx.keys.parameter top b outputs root randomness _ _)

variable (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
variable (setup : C.Party → Option (PrssKeys C))

theorem callerCont_floor (j : ℕ) (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (limit : ℕ) (le : limit ≤ a.2.1) :
    CheckFloor limit (callerCont K circuits settings top tree x setup j caller i a).run := by
  unfold callerCont
  apply (auditMap_floor K circuits settings ⟨i, x i, setupKeys setup i⟩ _ a.2 limit le).party_bind
  intro result hresult
  have next := auditMap_counter K circuits settings ⟨i, x i, setupKeys setup i⟩ _ a.2 result hresult
  split_ifs
  · exact firstRest_floor K circuits settings _ top tree _ limit (le_trans le next)
  · cases tree with
    | top => exact firstRest_floor K circuits settings _ top .top _ limit (le_trans le next)
    | bottom b => exact CheckFloor.of_quiet (bottomFinish_quiet (x i).parameter top b _ _ _ _ _)

theorem callerProgram_floor (D : C.Coalition) (j : ℕ) (caller : Caller C) (i : C.Party)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) (limit : ℕ)
    (le : limit ≤ lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding tree) j) :
    CheckFloor limit (callerProgram K D circuits settings top tree x setup j caller i).run := by
  unfold callerProgram
  apply (CheckFloor.of_quiet (localPrelude_quiet (E := E) _ quiet)).party_bind
  intro _ _
  apply (audit_floor K circuits settings ⟨i, x i, setupKeys setup i⟩ _ _ limit le).party_bind
  intro result hresult
  apply callerCont_floor K circuits settings top tree x setup j caller i result limit
  exact le_trans le (audit_counter K circuits settings _ _ _ result hresult)

/-- The floor at the local check label also covers the preceding quiet work.
The local depth requires no equality with the reference party's parameter. -/
theorem callerProgram_check_floor (D : C.Coalition) (j : ℕ) (caller : Caller C) (i : C.Party)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckFloor (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding tree) j +
      depth (((lockstepChunks settings caller.encoding tree).getD j []).map
        (circuits (x i).parameter ·.kind)) + 1)
      (callerProgram K D circuits settings top tree x setup j caller i).run := by
  unfold callerProgram
  apply (CheckFloor.of_quiet (localPrelude_quiet (E := E) _ quiet)).party_bind
  intro _ _
  apply (audit_check_floor K circuits settings ⟨i, x i, setupKeys setup i⟩ _ _).party_bind
  intro result hresult
  apply callerCont_floor K circuits settings top tree x setup j caller i result
  exact audit_check_counter K circuits settings _ _ _ result hresult

-- Port of TreeCheckSigningChoice.signing_chunks_nonempty; no head-agreement
-- dependency is needed for this arithmetic property of the job list.
theorem signing_chunks_nonempty (b : Fin (2 ^ layerHeight))
    (positive : 0 < settings.batchSize) (encoding : Encoding) :
    ∃ head rest, chunks settings.batchSize (signJobs b encoding) = head :: rest := by
  apply List.exists_cons_of_ne_nil
  apply List.ne_nil_of_length_pos
  rw [length_chunks]
  have jobs : 0 < (signJobs b encoding).length := by
    simp only [signJobs, List.length_map]
    decide
  exact Nat.div_pos (by omega) positive

/-- After the last signing audit, the remaining program has no check queries. -/
theorem callerCont_sign_last_quiet (b : Fin (2 ^ layerHeight)) (j : ℕ)
    (last : j + 1 = treeBatches settings (.bottom b)) (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) :
    PartyBudget CheckQuery (callerCont K circuits settings top (.bottom b) x setup j caller i a) 0 := by
  have positive : 0 < settings.batchSize := by
    by_contra h
    have zero : settings.batchSize = 0 := by omega
    simp [treeBatches, chunks, zero] at last
  obtain ⟨head, tail, nonempty⟩ := signing_chunks_nonempty settings b positive caller.encoding
  have length := lockstepChunks_length settings caller.encoding (.bottom b)
  have signing : (firstChunks settings (.bottom b)).length ≤ j := by
    simp only [lockstepChunks, List.length_append, nonempty, List.length_cons,
      firstChunks, treeLockstepFirstJobs] at length ⊢
    omega
  have empty : (chunks settings.batchSize (signJobs b caller.encoding)).drop
      (j - (firstChunks settings (.bottom b)).length + 1) = [] := by
    apply List.drop_eq_nil_of_le
    simp only [lockstepChunks, List.length_append] at length
    change (chunks settings.batchSize (signJobs b caller.encoding)).length ≤
      j - (chunks settings.batchSize (bottomJobs b)).length + 1
    omega
  unfold callerCont
  simp only [phaseChunks, phaseIndex, if_neg (Nat.not_lt.mpr signing), empty,
    List.mapM_nil, WriterT.run_pure, StateT.run_pure, pure_bind]
  exact bottomFinish_quiet (x i).parameter top b _ _ _ _ _

end TreeCheckCoinFloor
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.runFloor_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.runFloor_check

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.openRep_checkQuiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.openRep_checkQuiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.audit_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.audit_counter

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.auditMap_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.auditMap_floor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.firstRest_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.firstRest_floor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerCont_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerCont_floor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerProgram_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerProgram_floor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerProgram_check_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerProgram_check_floor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerCont_sign_last_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinFloor.callerCont_sign_last_quiet
