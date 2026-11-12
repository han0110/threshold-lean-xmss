import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestDisc
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSigning
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkEntry

/-! # Coin-key discipline through the signing batches

The caller windows retain the literal quiet opening tails and the encoding
used by the signing job list. Exchanges reset the set of expansion keys.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckSigningDisc
open TreeCheckWalkRecipe TreeCheckWalkCoverage TreeCheckWalkState
open TreeCheckWalkEntry TreeCheckWalkSigning TreeCheckHonestDisc
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
attribute [local irreducible] treeLockstepPublicChoiceCode

variable (K : Constants C E) (D : C.Coalition)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

-- Port of TreeCheckWalkEntry.residual_batch_cont, retaining the actual tail.
set_option maxHeartbeats 1000000 in
theorem residual_batch_cont_quiet (j : ℕ) (current : j < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (value : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      IsQueryBoundP tail CheckQuery 0 ∧
      Q = (treeLockstepLocalPrelude tail >>= fun _ =>
        callerCont K circuits settings top tree x setup j caller i
          ((some value, [record]), (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
            (firstChunks settings tree) (j + 1), j + 1))).run := by
  unfold callerProgram at h
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j current,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ caller.encoding j current.le,
    treeSimCheckBatchAudit_run_prefix] at h
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (firstChunks settings tree).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  rw [show (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
      (treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j) >>=
        treeSimCheckBatchFinish K circuits ctx jobs (start, j)) >>=
          callerCont K circuits settings top tree x setup j caller i) =
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
            callerCont K circuits settings top tree x setup j caller i) by
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
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  rw [labels]
  exact ⟨_, _, _, openTail_quiet K ctx.self _ _ inbox, rfl⟩

-- Port of TreeCheckWalkEntry.residual_last with the literal quiet tail.
theorem residual_last_quiet (j : ℕ) (last : j + 1 = (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (opened : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      IsQueryBoundP tail CheckQuery 0 ∧
      Q = (treeLockstepLocalPrelude tail >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
          ((some opened, caller.records i ++ [record]),
            (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
              (firstChunks settings tree) (j + 1), j + 1))).run := by
  have current : j < (firstChunks settings tree).length := by omega
  rcases residual_batch_cont_quiet K D circuits settings top tree x setup j current caller i same h with
    none | ⟨value, record, tail, quiet, rfl⟩
  · exact .inl none
  obtain ⟨values, saved⟩ := outputs
  refine .inr ⟨values.flatten ++ value, record, tail, quiet, ?_⟩
  have empty : (firstChunks settings tree).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
  unfold callerCont
  simp only [phaseChunks, phaseIndex, if_pos current, empty, List.mapM_nil, saved]
  simp [foldlM_some]

variable (b : Fin (2 ^ layerHeight))

-- Port of TreeCheckWalkSigning.residual_sign_batch, retaining the literal tail.
set_option maxHeartbeats 1000000 in
theorem residual_sign_batch_quiet (j : ℕ) (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (next : j + 1 < treeBatches settings (.bottom b))
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding (.bottom b)).getD j [])) (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q) :
    Q = pure none ∨ ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      IsQueryBoundP (caller'.tail i) CheckQuery 0 ∧
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
    by simp [stepCaller], openTail_quiet K ctx.self count data.2.1.1 inbox, ?_⟩
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  unfold callerProgram
  simp only [stepCaller, labels]

-- Port of TreeCheckHonestDisc.caller_batch on the full encoded job list.
theorem sign_caller_batch (j limit : ℕ) (current : j < treeBatches settings (.bottom b))
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (bound : lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) ≤ limit) :
    CheckDisc limit (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding (.bottom b)).getD j [])) ∅
      (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run := by
  have current' : j < (lockstepChunks settings caller.encoding (.bottom b)).length := by
    rwa [lockstepChunks_length]
  unfold callerProgram
  rw [treeSimCheckBatchAudit_run_prefix]
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
            callerCont K circuits settings top (.bottom b) x setup j caller i) by simp only [bind_assoc]]
  have prefixTimed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
  have prefixQuiet := (localPrelude_quiet (E := E) _ quiet).bind
    (fun _ => batchPrefix_quiet K circuits settings ctx jobs (start, j))
  rw [parameter] at prefixTimed
  rw [show batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter jobs =
      (depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) +
        (checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) + 1) by
      unfold batchRounds; omega]
  apply CheckDisc.timed_party_bind prefixTimed (Disc.of_quiet prefixQuiet _)
  intro data hdata
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
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  simp only [bind_assoc, pure_bind]
  have checkTimed := check_timed K ctx data.2.1.2 data.2.2
  have checkDisc := runDisc_check K ctx data.2.1.2 data.2.2 limit (by
    rw [hcount, hlabel]
    rw [lockstepStart_succ circuits _ _ j current'] at bound
    unfold batchLabels at bound
    simpa only [start, jobs, Nat.add_assoc, Prod.fst] using bound)
  rw [hcount] at checkTimed
  apply CheckDisc.timed_party_bind checkTimed
  · simpa only [hcount] using checkDisc (checkLabels (data.2.1.2.map (·.count)).sum)
  · intro checked _
    exact openRep_first K ctx _ _ limit _

/-- The first pass of an encoded caller retains the preceding quiet tail. -/
theorem sign_caller_first (j limit : ℕ) (caller : Caller C) (i : C.Party)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckDisc limit 1 ∅
      (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run :=
  caller_first K D circuits settings top (.bottom b) x setup j limit caller i quiet

/-- Exchange counts increase with the checkpoint index of one encoding. -/
theorem signRounds_mono (parameter : PublicParameter) (encoding : Encoding)
    {j j' : ℕ} (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (le : j ≤ j') (last : j' < treeBatches settings (.bottom b)) :
    signRounds circuits settings parameter encoding (.bottom b) j ≤
      signRounds circuits settings parameter encoding (.bottom b) j' := by
  induction j', le using Nat.le_induction with
  | base => exact le_rfl
  | succ k le ih =>
    have current : k < treeBatches settings (.bottom b) := by omega
    rw [signRounds_succ circuits settings b parameter encoding k (by omega) current]
    exact le_trans (ih current) (Nat.le_add_right _ _)

/-- Earlier encoded batches followed by the first quiet pass of batch `j`. -/
theorem sign_caller_window (start j : ℕ)
    (signing : (firstChunks settings (.bottom b)).length ≤ start)
    (last : j < treeBatches settings (.bottom b)) (le : start ≤ j)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) j)
      (signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding (.bottom b) j -
        signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding (.bottom b) start + 1) ∅
      (callerProgram K D circuits settings top (.bottom b) x setup start caller i).run := by
  by_cases equal : start = j
  · subst start
    simpa only [Nat.sub_self, Nat.zero_add] using
      sign_caller_first K D circuits settings top x setup b j _ caller i quiet
  · have current : start < treeBatches settings (.bottom b) := by omega
    have next : start + 1 < treeBatches settings (.bottom b) := by omega
    have before : start + 1 ≤ j := by omega
    have disc := sign_caller_batch K D circuits settings top x setup b start _ current caller i same quiet
      (lockstepStart_mono circuits _ _ before)
    have order := signRounds_mono circuits settings b
      (x (refHolder D K.publicTerm)).parameter caller.encoding (by omega) before last
    have succ := signRounds_succ circuits settings b
      (x (refHolder D K.publicTerm)).parameter caller.encoding start signing current
    rw [show signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding (.bottom b) j -
        signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding (.bottom b) start + 1 =
      batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
        ((lockstepChunks settings caller.encoding (.bottom b)).getD start []) +
      (signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding (.bottom b) j -
        signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding (.bottom b) (start + 1) + 1) by omega]
    apply disc.of_residual
    intro Q run
    rcases residual_sign_batch_quiet K D circuits settings top x setup b start signing next caller i same run with
      aborted | ⟨caller', encoding, _, _, quiet', rfl⟩
    · rw [aborted]
      exact .pure _ _ _
    · simpa only [ite_self, encoding] using
        sign_caller_window (start + 1) j (by omega) last before caller' i same quiet'
termination_by j - start

/-- Public tweakable hashes cannot issue a check coin-key or expansion query. -/
theorem tweakable_quiet {α : Type} (code : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable (C := C) code) (fun q => CheckQuery (.inr q)) 0 := by
  induction code using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    simpa using isQueryBoundP_bind (m := 0) (hash_zero (.hash t) (by simp [CheckQuery]))
      (fun a _ => ih a)

/-- The public choice adds no check query to its preceding gate. -/
theorem head_quiet (parameter : PublicParameter) (outputs : List (List Bit))
    (gate : OracleComp (LocalSpec C) (Option Unit))
    (quiet : IsQueryBoundP gate CheckQuery 0) :
    IsQueryBoundP (signingHead parameter b outputs gate) CheckQuery 0 := by
  unfold signingHead
  refine isQueryBoundP_bind (n := 0) (m := 0) quiet (fun a _ => ?_)
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some u =>
    apply IsQueryBoundP.liftComp_subSpec (p := fun q => CheckQuery (.inr q)) (fun _ => Iff.rfl)
    exact tweakable_quiet _

/-- All complete first-run batches, at the cutoff of their final boundary. -/
theorem first_caller_complete (start : ℕ)
    (le : start ≤ (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) (firstChunks settings tree).length)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree).length -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter start) ∅
      (callerProgram K D circuits settings top tree x setup start caller i).run := by
  by_cases equal : start = (firstChunks settings tree).length
  · subst start
    simp only [Nat.sub_self]
    exact .zero _ _
  · have current : start < (firstChunks settings tree).length := by omega
    have before : start + 1 ≤ (firstChunks settings tree).length := by omega
    have disc := caller_batch K D circuits settings top tree x setup start _ current caller i same quiet
      (lockstepStart_mono circuits _ _ before)
    have order := batchStart_mono circuits settings tree (x (refHolder D K.publicTerm)).parameter before
    have succ := batchStart_succ circuits settings tree (x (refHolder D K.publicTerm)).parameter start current
    rw [show batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree).length -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter start =
      batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter ((firstChunks settings tree).getD start []) +
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree).length -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (start + 1)) by omega]
    apply disc.of_residual
    intro Q run
    by_cases last : start + 1 = (firstChunks settings tree).length
    · simp only [last, Nat.sub_self]
      exact .zero _ _
    · rcases residual_batch_quiet K D circuits settings top tree x setup start (by omega) caller i same run with
        aborted | ⟨caller', _, _, _, quiet', rfl⟩
      · rw [aborted]
        exact .pure _ _ _
      · simpa only [ite_self] using
          first_caller_complete (start + 1) before caller' i same quiet'
termination_by (firstChunks settings tree).length - start

-- Port of TreeCheckWalkEntry.residual_batch_some, keeping the literal quiet tail.
theorem residual_batch_some_quiet (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (value : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      IsQueryBoundP tail CheckQuery 0 ∧
      Q = (callerProgram K D circuits settings top tree x setup (j + 1)
        (stepCaller caller i (some value, [record]) tail) i).run := by
  rcases residual_batch_cont_quiet K D circuits settings top tree x setup j (by omega) caller i same h with
    none | ⟨value, record, tail, quiet, rfl⟩
  · exact .inl none
  refine .inr ⟨value, record, tail, quiet, ?_⟩
  rw [callerCont_step K circuits settings top tree x setup j next caller i _ tail]
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree _ (j + 1) next,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ _ (j + 1) next.le]
  simp only [stepCaller]

-- Port of TreeCheckWalkEntry.residual_first_some, keeping the literal quiet tail.
theorem residual_first_some_quiet (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some) :
    ∀ j, j < (firstChunks settings tree).length →
    ∀ {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))},
      Residual (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j)
        (callerProgram K D circuits settings top tree x setup 0 caller i).run Q →
      Q = pure none ∨ ∃ caller' : Caller C,
        (caller'.records i).length = (caller.records i).length + j ∧
        (∃ values : List (List (List Bit)), caller'.outputs i = values.map some) ∧
        IsQueryBoundP (caller'.tail i) CheckQuery 0 ∧
        Q = (callerProgram K D circuits settings top tree x setup j caller' i).run
  | 0, _, Q, h => .inr ⟨caller, rfl, outputs, quiet, h.zero_inv⟩
  | j + 1, next, Q, h => by
    have current : j < (firstChunks settings tree).length := by omega
    rw [show batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (j + 1) =
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j +
          batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
            ((firstChunks settings tree).getD j []) by
      simp only [batchStart, List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem current, Option.toList_some, Option.getD_some, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]] at h
    obtain ⟨M, first, second⟩ := h.split
    rcases residual_first_some_quiet caller i same quiet outputs j current first with rfl | ⟨middle, records, ⟨values, saved⟩, quietMiddle, rfl⟩
    · exact .inl second.pure_inv
    rcases residual_batch_some_quiet K D circuits settings top tree x setup j next middle i same second with
      none | ⟨value, record, tail, quietTail, rfl⟩
    · exact .inl none
    refine .inr ⟨_, ?_, ⟨values ++ [value], ?_⟩, quietTail, rfl⟩
    · simp only [stepCaller, List.length_append, List.length_singleton, records]
      omega
    · simp only [stepCaller, saved, List.map_append, List.map_singleton]

/-- The complete first run leaves the actual quiet opening tail at its entry. -/
theorem residual_first_entry_quiet (positive : 0 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (run : Residual (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree).length)
      (callerProgram K D circuits settings top tree x setup 0 caller i).run Q) :
    Q = pure none ∨ ∃ (opened : List (List Bit)) (records : List (TreeSimCheckBatchRecord C))
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      IsQueryBoundP tail CheckQuery 0 ∧
      Q = (treeLockstepLocalPrelude tail >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
          ((some opened, records),
            (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
              (firstChunks settings tree) (firstChunks settings tree).length,
              (firstChunks settings tree).length))).run := by
  obtain ⟨j, last⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (firstChunks settings tree).length ≠ 0)
  have last' : j + 1 = (firstChunks settings tree).length := last.symm
  rw [TreeCheckWalkEntry.batchStart_last circuits settings tree _ j last'] at run
  obtain ⟨M, first, second⟩ := run.split
  rcases residual_first_some_quiet K D circuits settings top tree x setup caller i same quiet outputs j
    (by omega) first with aborted | ⟨middle, records, outputs', quiet', rfl⟩
  · rw [aborted] at second
    exact .inl second.pure_inv
  · rcases residual_last_quiet K D circuits settings top tree x setup j last' middle i same outputs' second with
      aborted | ⟨opened, record, tail, quietTail, equal⟩
    · exact .inl aborted
    · exact .inr ⟨opened, middle.records i ++ [record], tail, quietTail, by simpa only [last'] using equal⟩

/-- The actual initial caller satisfies the full first-run discipline. -/
theorem initial_complete_checkDisc (dealt : DealtInputs D x) (i : C.Party) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) (firstChunks settings tree).length)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree).length) ∅
      (callerProgram K D circuits settings top tree x setup 0 (firstCaller setup) i).run := by
  have same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  simpa only [batchStart, List.take_zero, List.map_nil, List.sum_nil, Nat.sub_zero] using
    first_caller_complete K D circuits settings top tree x setup 0 (Nat.zero_le _) (firstCaller setup) i same
      (isQueryBoundP_pure _ _ _)

/-- The same complete window on the actual scheduler initial program. -/
theorem initial_program_complete_checkDisc
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (positive : 0 < (firstChunks settings tree).length)
    (dealt : DealtInputs D x) (i : C.Party) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) (firstChunks settings tree).length)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree).length) ∅
      ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run := by
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos positive)
  rw [initial_program K D A circuits settings top tree x start head rest chunked i, boundary_program]
  exact initial_complete_checkDisc K D circuits settings top tree x start.1.2 dealt i

end TreeCheckSigningDisc
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningDisc.residual_last_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningDisc.residual_last_quiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningDisc.residual_sign_batch_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningDisc.residual_sign_batch_quiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningDisc.sign_caller_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningDisc.sign_caller_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningDisc.head_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningDisc.head_quiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningDisc.residual_first_entry_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningDisc.residual_first_entry_quiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningDisc.initial_program_complete_checkDisc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningDisc.initial_program_complete_checkDisc
