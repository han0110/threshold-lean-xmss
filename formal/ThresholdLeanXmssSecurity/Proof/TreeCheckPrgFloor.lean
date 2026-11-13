import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgClock
import ThresholdLeanXmssSecurity.Proof.TreeCheckCoinFloor

/-! # PRG-label floors for audited callers

Every audit and caller preserves its inherited PRG label floor, including
aborting paths. Batch prefixes have their floor at the initial label.
Structural proofs port TreeCheckCoinFloor; counter and chunk arithmetic
reuse its existing lemmas.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckPrgFloor
open TreeCheckPrgClock TreeCheckPrgWindow TreeCheckPrgDisc
open TreeCheckWalkRecipe TreeCheckWalkState TreeSimHashCount
attribute [local instance] Classical.propDecidable
attribute [local irreducible] treeLockstepPublicChoiceCode merkleNode merklePath Concrete.layerRoot tweakable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β : Type}

def PrgRunFloor (p : RunM C E RealSpec α) : Prop :=
  ∀ st limit, limit ≤ st.label → PrgFloor limit (p.run st).run

theorem PrgRunFloor.pure (a : α) : PrgRunFloor (C := C) (E := E) (Pure.pure a) :=
  fun _ _ _ => PrgFloor.pure _ _

theorem PrgRunFloor.of_noPrg {p : RunM C E RealSpec α} (h : RunBudget (PrgFrom 0) p 0) :
    PrgRunFloor p := fun st _ _ => PrgFloor.of_noPrg (h st)

theorem PrgRunFloor.bind {n : ℕ} {p : RunM C E RealSpec α} {f : α → RunM C E RealSpec β}
    (h : PrgRunFloor p) (labels : LockstepLabels n p) (rest : ∀ a, PrgRunFloor (f a)) :
    PrgRunFloor (p >>= f) := by
  intro st limit le
  rw [StateT.run_bind]
  apply (h st limit le).party_bind
  rintro ⟨a, mid⟩ ha
  apply rest a mid limit
  rw [labels st a mid ha]
  omega

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

theorem prgRunFloor_check (ctx : Context C) (tuples : List (Tuple C)) :
    PrgRunFloor (check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples) := by
  intro st limit le
  have floor := (prgClocked_check K ctx tuples st).floor
    (fun _ _ h => Nat.add_le_add_left (prgCheckClock_mono _ h) _)
  apply floor.mono
  simpa only [prgCheckClock_zero, Nat.add_zero] using le

theorem openRep_noPrg (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    PartyBudget (PrgFrom 0) (openRep K ctx v count : PartyM C E RealSpec _) 0 :=
  openRep_zero K 0 ctx v count

variable (circuits : Circuits) (settings : Settings)

/-- The prefix reads at its initial label, so its floor starts there. -/
theorem batchPrefix_prgFloor (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (limit : ℕ) (le : limit ≤ initial.1) :
    PrgFloor limit (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run := by
  have clock := prgClocked_batchPrefix K circuits settings (pure (some ()))
    (isQueryBoundP_pure _ _ _) ctx jobs initial
  have floor := clock.floor (prefixClock_mono _ _)
  simp only [treeLockstepLocalPrelude, localStep, liftComp_pure, OptionT.lift_pure, pure_bind,
    prefixClock_zero _ _ (rounds_pos settings.mode)] at floor
  exact floor.mono le

theorem audit_prgFloor (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (limit : ℕ) (le : limit ≤ initial.1) :
    PrgFloor limit ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial).run := by
  rw [treeSimCheckBatchAudit_run_prefix]
  apply (batchPrefix_prgFloor K circuits settings ctx jobs initial limit le).party_bind
  intro data hdata
  obtain ⟨_, label, _, _, _⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs initial data hdata
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  simp only [bind_assoc, pure_bind]
  apply (prgRunFloor_check K ctx data.2.1.2 data.2.2 _ (by omega)).party_bind
  intro checked _
  apply (PrgFloor.of_noPrg (openRep_noPrg K ctx _ _)).party_bind
  intro opened _
  exact .pure _ _

theorem auditMap_prgFloor (ctx : Context C) (chunks : List (List Job)) (initial : ℕ × ℕ)
    (limit : ℕ) (le : limit ≤ initial.1) :
    PrgFloor limit ((chunks.mapM
      (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial).run := by
  induction chunks generalizing initial with
  | nil => exact .pure _ _
  | cons head tail ih =>
    rw [auditChunks_cons]
    apply (audit_prgFloor K circuits settings ctx head initial limit le).party_bind
    intro middle hm
    apply (ih middle.2 (le_trans le (TreeCheckCoinFloor.audit_counter K circuits settings ctx head initial middle hm))).party_bind
    intro last _
    exact .pure _ _

theorem batched_prgFloor (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (limit : ℕ) (le : limit ≤ initial.1) :
    PrgFloor limit ((batched settings.batchSize
      (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx) jobs).run.run initial).run := by
  rw [auditBatched_run]
  apply (auditMap_prgFloor K circuits settings ctx _ initial limit le).party_bind
  intro _ _
  exact .pure _ _

-- Port of TreeCheckSigningDisc.tweakable_quiet for all PRG labels.
theorem tweakable_noPrg (code : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable (C := C) code) (fun q => PrgFrom 0 (.inr q)) 0 := by
  induction code using OracleComp.inductionOn with
  | pure a =>
    simp only [tweakable, simulateQ_pure]
    exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    simpa using isQueryBoundP_bind (m := 0) (hash_zero 0 (.hash t)) (fun a _ => ih a)

-- Port of TreeCheckSigningDisc.head_quiet with the same arbitrary gate.
theorem head_noPrg (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (gate : OracleComp (LocalSpec C) (Option Unit))
    (noPrg : IsQueryBoundP gate (PrgFrom 0) 0) :
    IsQueryBoundP (signingHead parameter b outputs gate) (PrgFrom 0) 0 := by
  unfold signingHead
  refine isQueryBoundP_bind (n := 0) (m := 0) noPrg (fun a _ => ?_)
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some u =>
    apply IsQueryBoundP.liftComp_subSpec (p := fun q => PrgFrom 0 (.inr q)) (fun _ => Iff.rfl)
    exact tweakable_noPrg _

theorem tweakable_party_noPrg (code : OracleComp HashSpec α) :
    PartyBudget (PrgFrom 0) (oracleStep (tweakable code) : PartyM C E RealSpec α) 0 :=
  oracle_bound (tweakable_noPrg code)

theorem topFinish_noPrg (parameter : PublicParameter) (outputs : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) :
    PartyBudget (PrgFrom 0) (treeLockstepTopFinish (E := E) parameter outputs records) 0 := by
  unfold treeLockstepTopFinish
  exact (tweakable_party_noPrg (C := C) (E := E) _).bind (m := 0) (fun _ => PartyBudget.pure _)

theorem bottomFinish_noPrg (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (values : Option (List (List Bit)))
    (records : List (TreeSimCheckBatchRecord C)) :
    PartyBudget (PrgFrom 0)
      (treeLockstepBottomFinish (E := E) parameter top b outputs root randomness values records) 0 := by
  cases values with
  | none => exact party_quiet_of_zero 0 PartyBound.failure
  | some values =>
    unfold treeLockstepBottomFinish
    dsimp only
    apply (tweakable_party_noPrg (C := C) (E := E) _).bind (m := 0)
    intro path
    apply (tweakable_party_noPrg (C := C) (E := E) _).bind (m := 0)
    intro root
    split_ifs
    · exact party_quiet_of_zero 0 PartyBound.failure
    · exact PartyBudget.pure _

/-- Every supported public head continues from the inherited counter. -/
theorem firstRest_prgFloor (ctx : Context C) (top : TopTree) (tree : Tree)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (limit : ℕ) (le : limit ≤ a.2.1) :
    PrgFloor limit (treeLockstepFirstRest K circuits settings ctx top tree a).run := by
  rcases a with ⟨⟨values, records⟩, counters⟩
  cases values with
  | none => exact .pure _ _
  | some outputs =>
    cases tree with
    | top => exact PrgFloor.of_noPrg (topFinish_noPrg ctx.keys.parameter outputs records)
    | bottom b =>
      unfold treeLockstepFirstRest
      dsimp only
      apply (PrgFloor.of_noPrg (tweakable_party_noPrg (C := C) (E := E) _)).party_bind
      intro chosen _
      cases chosen with
      | none => exact .pure _ _
      | some choice =>
        rcases choice with ⟨root, randomness, encoding⟩
        apply (batched_prgFloor K circuits settings ctx _ counters limit le).party_bind
        intro result _
        exact PrgFloor.of_noPrg (bottomFinish_noPrg ctx.keys.parameter top b outputs root randomness _ _)

variable (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
variable (setup : C.Party → Option (PrssKeys C))

theorem callerCont_prgFloor (j : ℕ) (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (limit : ℕ) (le : limit ≤ a.2.1) :
    PrgFloor limit (callerCont K circuits settings top tree x setup j caller i a).run := by
  unfold callerCont
  apply (auditMap_prgFloor K circuits settings ⟨i, x i, setupKeys setup i⟩ _ a.2 limit le).party_bind
  intro result hresult
  have next := TreeCheckCoinFloor.auditMap_counter K circuits settings ⟨i, x i, setupKeys setup i⟩ _ a.2 result hresult
  split_ifs
  · exact firstRest_prgFloor K circuits settings _ top tree _ limit (le_trans le next)
  · cases tree with
    | top => exact firstRest_prgFloor K circuits settings _ top .top _ limit (le_trans le next)
    | bottom b => exact PrgFloor.of_noPrg (bottomFinish_noPrg (x i).parameter top b _ _ _ _ _)

theorem callerProgram_prgFloor (D : C.Coalition) (j : ℕ) (caller : Caller C) (i : C.Party)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom 0) 0) (limit : ℕ)
    (le : limit ≤ lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding tree) j) :
    PrgFloor limit (callerProgram K D circuits settings top tree x setup j caller i).run := by
  unfold callerProgram
  apply (PrgFloor.of_noPrg (localPrelude_prg (E := E) 0 _ quiet)).party_bind
  intro _ _
  apply (audit_prgFloor K circuits settings ⟨i, x i, setupKeys setup i⟩ _ _ limit le).party_bind
  intro result hresult
  apply callerCont_prgFloor K circuits settings top tree x setup j caller i result limit
  exact le_trans le (TreeCheckCoinFloor.audit_counter K circuits settings _ _ _ result hresult)

/-- After the last signing audit, the remaining program has no PRG queries. -/
theorem callerCont_sign_last_noPrg (b : Fin (2 ^ layerHeight)) (j : ℕ)
    (last : j + 1 = treeBatches settings (.bottom b)) (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) :
    PartyBudget (PrgFrom 0) (callerCont K circuits settings top (.bottom b) x setup j caller i a) 0 := by
  have positive : 0 < settings.batchSize := by
    by_contra h
    have zero : settings.batchSize = 0 := by omega
    simp [treeBatches, chunks, zero] at last
  obtain ⟨head, tail, nonempty⟩ := TreeCheckCoinFloor.signing_chunks_nonempty settings b positive caller.encoding
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
  exact bottomFinish_noPrg (x i).parameter top b _ _ _ _ _

end TreeCheckPrgFloor
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.PrgRunFloor.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.PrgRunFloor.bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.prgRunFloor_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.prgRunFloor_check

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.openRep_noPrg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.openRep_noPrg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.batchPrefix_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.batchPrefix_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.audit_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.audit_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.auditMap_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.auditMap_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.batched_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.batched_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.tweakable_noPrg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.tweakable_noPrg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.head_noPrg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.head_noPrg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.topFinish_noPrg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.topFinish_noPrg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.bottomFinish_noPrg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.bottomFinish_noPrg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.firstRest_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.firstRest_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.callerCont_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.callerCont_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.callerProgram_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.callerProgram_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFloor.callerCont_sign_last_noPrg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFloor.callerCont_sign_last_noPrg
