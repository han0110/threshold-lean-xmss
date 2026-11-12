import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkState

/-!
# Residual programs of the signing batches

For one party and one fixed encoding, the exchanges of each signing batch leave
its actual next audited caller, or a rejecting local tail. The accumulated
exchange count is `signRounds`; output and record lengths each increase once
per batch. This gives the original `WalkStateSigning` on the fixed caller.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckWalkSigning
open TreeCheckWalkRecipe TreeCheckWalkState TreeCheckWalkCoverage
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition) (circuits : Circuits) (settings : Settings)
variable (top : TopTree) (b : Fin (2 ^ layerHeight)) (x : C.Party → Keys C)
variable (setup : C.Party → Option (PrssKeys C))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem chunks_getD_sign (encoding : Encoding) (j : ℕ)
    (hj : (firstChunks settings (.bottom b)).length ≤ j) :
    (lockstepChunks settings encoding (.bottom b)).getD j [] =
      (chunks settings.batchSize (signJobs b encoding)).getD
        (j - (firstChunks settings (.bottom b)).length) [] := by
  simp only [lockstepChunks, firstChunks, treeLockstepFirstJobs,
    List.getD_eq_getElem?_getD] at hj ⊢
  rw [List.getElem?_append_right hj]

/-- The signing continuation runs the next batch at the actual accumulated state. -/
theorem callerCont_sign_step (j : ℕ)
    (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (next : j + 1 < treeBatches settings (.bottom b))
    (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (tail : OracleComp (LocalSpec C) (Option Unit)) :
    callerCont K circuits settings top (.bottom b) x setup j caller i a =
      (treeSimCheckBatchAudit K circuits settings ⟨i, x i, setupKeys setup i⟩
        ((lockstepChunks settings caller.encoding (.bottom b)).getD (j + 1) [])).run.run a.2 >>=
      callerCont K circuits settings top (.bottom b) x setup (j + 1)
        (stepCaller caller i a.1 tail) i := by
  have signing' : (firstChunks settings (.bottom b)).length ≤ j + 1 := by omega
  have length := lockstepChunks_length settings caller.encoding (.bottom b)
  have index : j - (firstChunks settings (.bottom b)).length + 1 <
      (chunks settings.batchSize (signJobs b caller.encoding)).length := by
    simp only [lockstepChunks, firstChunks, treeLockstepFirstJobs, List.length_append] at length signing ⊢
    omega
  have step : j + 1 - (firstChunks settings (.bottom b)).length =
      j - (firstChunks settings (.bottom b)).length + 1 := by omega
  have split := List.drop_eq_getElem_cons index
  rw [chunks_getD_sign settings b caller.encoding (j + 1) signing']
  unfold callerCont
  simp only [phaseChunks, phaseIndex, if_neg (Nat.not_lt.mpr signing),
    if_neg (Nat.not_lt.mpr signing'), stepCaller, step]
  rw [split, auditChunks_cons]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index, Option.getD_some,
    bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]

-- Generalizes TreeCheckWalkState.residual_batch to the signing phase; the
-- pinned and current leanVM libraries have no corresponding caller semantics.
set_option maxHeartbeats 1000000 in
/-- The exchanges of a signing batch retain its next caller or an abort. -/
theorem residual_sign_batch (j : ℕ) (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (next : j + 1 < treeBatches settings (.bottom b))
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding (.bottom b)).getD j [])) (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q) :
    Q = pure none ∨ ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      Q = (callerProgram K D circuits settings top (.bottom b) x setup (j + 1) caller' i).run := by
  have current : j < (lockstepChunks settings caller.encoding (.bottom b)).length := by
    rw [lockstepChunks_length]
    omega
  unfold callerProgram at h
  rw [treeSimCheckBatchAudit_run_prefix] at h
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (lockstepChunks settings caller.encoding (.bottom b)).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (lockstepChunks settings caller.encoding (.bottom b)) j
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  rw [show (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
      (treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j) >>=
        treeSimCheckBatchFinish K circuits ctx jobs (start, j)) >>=
          callerCont K circuits settings top (.bottom b) x setup j caller i) =
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
            callerCont K circuits settings top (.bottom b) x setup j caller i) by
    simp only [bind_assoc]] at h
  have prefixTimed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
  rw [parameter] at prefixTimed
  rw [show batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter jobs =
      (depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) +
        (checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) + 1) by
      unfold batchRounds
      omega] at h
  rcases Residual.party_bind prefixTimed h with none | ⟨data, hdata, h⟩
  · exact .inl none
  obtain ⟨-, -, hprefix⟩ := treeSimCheck_some_bind _ _ _ hdata
  obtain ⟨-, hlabel, -, -, -⟩ :=
    treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hprefix
  have hcount : (data.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
    unfold treeSimCheckBatchPrefix at hprefix
    obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ hprefix
    obtain ⟨q, hq, he⟩ := treeSimCheck_some_bind _ _ _ hrest
    have he' : data = (inputs, q) := by simpa only [OptionT.run_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] using he
    subst data
    exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs start j q.1 q.2 hq
  rw [parameter] at hcount hlabel
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify at h
  simp only [bind_assoc, pure_bind] at h
  have checkTimed := check_timed K ctx data.2.1.2 data.2.2
  rw [hcount] at checkTimed
  rcases Residual.party_bind checkTimed h with none | ⟨checked, hchecked, h⟩
  · exact .inl none
  have finalLabel := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 hchecked
  rw [hcount, hlabel] at finalLabel
  rcases residual_openRep K ctx _ _ _ h with none | ⟨inbox, rfl⟩
  · exact .inl none
  refine .inr ?_
  rw [callerCont_sign_step K circuits settings top b x setup j signing next caller i _ (openTail K ctx.self
      (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length data.2.1.1 inbox)]
  set count := (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length
  set value := assemble (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs) fun g =>
    ∑ T, treeSimOpenCopy K ctx.self count data.2.1.1 inbox T g
  refine ⟨stepCaller caller i (some value, [⟨ctx, jobs, (start, j), data.1, data.2.1.2, data.2.2, value,
    checked.2⟩]) (openTail K ctx.self count data.2.1.1 inbox), rfl, by simp [stepCaller],
    by simp [stepCaller], ?_⟩
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  unfold callerProgram
  simp only [stepCaller, labels]


/-- An abort is represented by a caller whose local tail rejects. -/
theorem sign_batch_step (j : ℕ) (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (next : j + 1 < treeBatches settings (.bottom b))
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding (.bottom b)).getD j [])) (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q) :
    ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      Q = (callerProgram K D circuits settings top (.bottom b) x setup (j + 1) caller' i).run := by
  rcases residual_sign_batch K D circuits settings top b x setup j signing next caller i same h with aborted | found
  · let record : TreeSimCheckBatchRecord C :=
      ⟨⟨i, x i, setupKeys setup i⟩, [], (0, 0), [], [], ⟨fun _ => [], 0, 0⟩, [], ⟨fun _ => [], 0, 0⟩⟩
    refine ⟨stepCaller caller i (none, [record]) (pure none), rfl, by simp [stepCaller],
      by simp [stepCaller], ?_⟩
    rw [aborted, callerProgram_abort K D circuits settings top (.bottom b) x setup (j + 1) _ i rfl]
  · exact found


/-- A suffix of a finite prefix gains exactly its next summand. -/
theorem take_drop_sum_succ {α : Type} (items : List α) (fallback : α) (f : α → ℕ)
    (start j : ℕ) (hs : start ≤ j) (hj : j < items.length) :
    (((items.take (j + 1)).drop start).map f).sum =
      (((items.take j).drop start).map f).sum + f (items.getD j fallback) := by
  have htake : start ≤ (items.take j).length := by
    rw [List.length_take]
    omega
  rw [List.take_add_one, List.drop_append_of_le_length htake]
  simp only [List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.toList_some, Option.getD_some,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem signRounds_succ (parameter : PublicParameter) (encoding : Encoding) (j : ℕ)
    (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (current : j < treeBatches settings (.bottom b)) :
    signRounds circuits settings parameter encoding (.bottom b) (j + 1) =
      signRounds circuits settings parameter encoding (.bottom b) j +
        batchRounds circuits settings.mode parameter
          ((lockstepChunks settings encoding (.bottom b)).getD j []) := by
  have hlen : j < (lockstepChunks settings encoding (.bottom b)).length := by
    rwa [lockstepChunks_length]
  exact take_drop_sum_succ _ [] (batchRounds circuits settings.mode parameter)
    (firstChunks settings (.bottom b)).length j signing hlen

/-- The original per-party signing invariant, with one fixed encoding. -/
theorem residual_signing (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter) :
    ∀ j, (firstChunks settings (.bottom b)).length ≤ j → j < treeBatches settings (.bottom b) →
    ∀ Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C))),
      Residual (signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding
          (.bottom b) j)
        (callerProgram K D circuits settings top (.bottom b) x setup
          (firstChunks settings (.bottom b)).length caller i).run Q →
      ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
        (caller'.records i).length + (firstChunks settings (.bottom b)).length =
          (caller.records i).length + j ∧
        (caller'.outputs i).length + (firstChunks settings (.bottom b)).length =
          (caller.outputs i).length + j ∧
        Q = (callerProgram K D circuits settings top (.bottom b) x setup j caller' i).run := by
  intro j signing
  induction j, signing using Nat.le_induction with
  | base =>
      intro _ Q h
      simp only [signRounds, List.drop_take_self, List.map_nil, List.sum_nil] at h
      exact ⟨caller, rfl, rfl, rfl, h.zero_inv⟩
  | succ j signing ih =>
      intro next Q h
      have current : j < treeBatches settings (.bottom b) := by omega
      rw [signRounds_succ circuits settings b _ _ j signing current] at h
      obtain ⟨M, first, second⟩ := h.split
      obtain ⟨middle, encoding, records, outputs, rfl⟩ := ih current M first
      rw [← encoding] at second
      obtain ⟨final, encoding', records', outputs', rfl⟩ :=
        sign_batch_step K D circuits settings top b x setup j signing next middle i same second
      exact ⟨final, encoding'.trans encoding, by omega, by omega, rfl⟩

/-- The fixed signing callers satisfy `WalkStateSigning`. -/
theorem walkStateSigning : WalkStateSigning K circuits settings := by
  intro D top b x setup caller i same
  exact residual_signing K D circuits settings top b x setup caller i same

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkSigning.callerCont_sign_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms callerCont_sign_step

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkSigning.residual_sign_batch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_sign_batch

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkSigning.residual_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_signing

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkSigning.walkStateSigning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkStateSigning

end ThresholdLeanXmssSecurity.TreeCheckWalkSigning
