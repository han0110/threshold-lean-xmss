import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgFloor
import ThresholdLeanXmssSecurity.Proof.TreeCheckSigningClock

/-! # Common PRG clocks for audited caller prefixes

The batch clock follows the ceiling of the circuit-prefix pass count and
then the check's PRG clock. Every cut bounds past PRG labels and gives a
floor on every future residual, including aborts and later signing choices.
The caller recursion ports TreeCheckSigningClock; literal opening tails
port TreeCheckSigningDisc and retain PRG quietness at every cutoff.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckPrgSigningClock
open TreeCheckPrgClock TreeCheckPrgFloor TreeCheckPrgDisc TreeCheckPrgWindow
open TreeCheckWalkRecipe TreeCheckWalkState TreeCheckWalkEntry TreeCheckWalkSigning TreeSimHashCount
open TreeCheckHonestDisc TreeCheckSigningClock TreeCheckWalkCoverage
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β : Type}
variable (circuits : Circuits) (settings : Settings)

def prgBatchClock (parameter : PublicParameter) (jobs : List Job) (start n : ℕ) : ℕ :=
  if n ≤ depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 then
    prefixClock settings.mode.rounds start n
  else start + depth (jobs.map (circuits parameter ·.kind)) + 1 +
    prgCheckClock (batchCount circuits parameter jobs)
      (n - (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1))

theorem prgBatchClock_prefix (parameter : PublicParameter) (jobs : List Job) (start n : ℕ)
    (le : n ≤ depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1) :
    prgBatchClock circuits settings parameter jobs start n = prefixClock settings.mode.rounds start n := by
  simp only [prgBatchClock, if_pos le]

theorem prgBatchClock_lower (parameter : PublicParameter) (jobs : List Job) (start n : ℕ) :
    start ≤ prgBatchClock circuits settings parameter jobs start n := by
  unfold prgBatchClock prefixClock
  split_ifs
  · exact Nat.le_add_right _ _
  · omega

theorem prgBatchClock_upper (parameter : PublicParameter) (jobs : List Job) (start n : ℕ) :
    prgBatchClock circuits settings parameter jobs start n ≤ start + batchLabels circuits parameter jobs := by
  unfold prgBatchClock
  split_ifs with early
  · have h := prefixClock_mono settings.mode.rounds start early
    rw [prefixClock_pre _ _ _ (rounds_pos settings.mode)] at h
    unfold batchLabels
    omega
  · have h := prgCheckClock_le (batchCount circuits parameter jobs)
      (n - (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1))
    unfold batchLabels
    omega

theorem prgBatchClock_mono (parameter : PublicParameter) (jobs : List Job) (start : ℕ) :
    Monotone (prgBatchClock circuits settings parameter jobs start) := by
  intro n n' le
  unfold prgBatchClock
  split_ifs with early early'
  · exact prefixClock_mono _ _ le
  · have h := prefixClock_mono settings.mode.rounds start early
    rw [prefixClock_pre _ _ _ (rounds_pos settings.mode)] at h
    omega
  · omega
  · exact Nat.add_le_add_left (prgCheckClock_mono _ (Nat.sub_le_sub_right le _)) _

theorem prgBatchClock_end (parameter : PublicParameter) (jobs : List Job) (start : ℕ) :
    prgBatchClock circuits settings parameter jobs start
      (batchRounds circuits settings.mode parameter jobs - 1) =
        start + batchLabels circuits parameter jobs := by
  unfold prgBatchClock batchRounds batchLabels
  split_ifs with early
  · have zero : checkLabels (batchCount circuits parameter jobs) = 0 := by omega
    rw [zero]
    simp only [Nat.add_zero, Nat.add_sub_cancel]
    rw [prefixClock_pre _ _ _ (rounds_pos settings.mode)]
    omega
  · rw [show (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 +
        checkLabels (batchCount circuits parameter jobs) + 1 - 1) -
        (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1) =
          checkLabels (batchCount circuits parameter jobs) by omega, prgCheckClock_end]
    omega

theorem prgBatchClock_one (parameter : PublicParameter) (jobs : List Job) (start : ℕ) :
    prgBatchClock circuits settings parameter jobs start 1 = start + 1 := by
  rw [prgBatchClock_prefix circuits settings parameter jobs start 1 (by omega)]
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
    (prefixClock_layer settings.mode.rounds start 0 (rounds_pos settings.mode)).2

-- Port of TreeCheckSigningClock's caller-clock recursion and order laws.
def prgCallerClock (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ) : ℕ :=
  if _h : b < chunks.length then
    if n < batchRounds circuits settings.mode parameter (chunks.getD b []) then
      prgBatchClock circuits settings parameter (chunks.getD b []) (lockstepStart circuits parameter chunks b) n
    else prgCallerClock parameter chunks (b + 1) (n - batchRounds circuits settings.mode parameter (chunks.getD b []))
  else lockstepStart circuits parameter chunks chunks.length
termination_by chunks.length - b

theorem prgCallerClock_done (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ)
    (last : chunks.length ≤ b) :
    prgCallerClock circuits settings parameter chunks b n = lockstepStart circuits parameter chunks chunks.length := by
  rw [prgCallerClock, dif_neg (Nat.not_lt.mpr last)]

theorem prgCallerClock_inside (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ)
    (current : b < chunks.length) (short : n < batchRounds circuits settings.mode parameter (chunks.getD b [])) :
    prgCallerClock circuits settings parameter chunks b n =
      prgBatchClock circuits settings parameter (chunks.getD b []) (lockstepStart circuits parameter chunks b) n := by
  rw [prgCallerClock, dif_pos current, if_pos short]

theorem prgCallerClock_next (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ)
    (current : b < chunks.length) (long : batchRounds circuits settings.mode parameter (chunks.getD b []) ≤ n) :
    prgCallerClock circuits settings parameter chunks b n =
      prgCallerClock circuits settings parameter chunks (b + 1)
        (n - batchRounds circuits settings.mode parameter (chunks.getD b [])) := by
  rw [prgCallerClock, dif_pos current, if_neg (Nat.not_lt.mpr long)]

theorem prgCallerClock_lower (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ) :
    lockstepStart circuits parameter chunks b ≤ prgCallerClock circuits settings parameter chunks b n := by
  rw [prgCallerClock]
  split_ifs with current short
  · exact prgBatchClock_lower circuits settings parameter _ _ _
  · exact le_trans (lockstepStart_mono circuits parameter chunks (Nat.le_succ b))
      (prgCallerClock_lower parameter chunks (b + 1) _)
  · simp only [lockstepStart, List.take_of_length_le (Nat.le_of_not_gt current), List.take_length]
    exact le_rfl
termination_by chunks.length - b

theorem prgCallerClock_upper (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ) :
    prgCallerClock circuits settings parameter chunks b n ≤ lockstepStart circuits parameter chunks chunks.length := by
  rw [prgCallerClock]
  split_ifs with current short
  · have bound := prgBatchClock_upper circuits settings parameter (chunks.getD b [])
      (lockstepStart circuits parameter chunks b) n
    rw [← lockstepStart_succ circuits parameter chunks b current] at bound
    exact le_trans bound (lockstepStart_mono circuits parameter chunks (by omega))
  · exact prgCallerClock_upper parameter chunks (b + 1) _
  · exact le_rfl
termination_by chunks.length - b

theorem prgCallerClock_mono (parameter : PublicParameter) (chunks : List (List Job)) (b : ℕ) :
    Monotone (prgCallerClock circuits settings parameter chunks b) := by
  intro n n' le
  by_cases current : b < chunks.length
  · by_cases short : n < batchRounds circuits settings.mode parameter (chunks.getD b [])
    · rw [prgCallerClock_inside circuits settings parameter chunks b n current short]
      by_cases short' : n' < batchRounds circuits settings.mode parameter (chunks.getD b [])
      · rw [prgCallerClock_inside circuits settings parameter chunks b n' current short']
        exact prgBatchClock_mono circuits settings parameter _ _ le
      · rw [prgCallerClock_next circuits settings parameter chunks b n' current (by omega)]
        have bound := prgBatchClock_upper circuits settings parameter (chunks.getD b [])
          (lockstepStart circuits parameter chunks b) n
        rw [← lockstepStart_succ circuits parameter chunks b current] at bound
        exact le_trans bound (prgCallerClock_lower circuits settings parameter chunks (b + 1) _)
    · rw [prgCallerClock_next circuits settings parameter chunks b n current (by omega),
        prgCallerClock_next circuits settings parameter chunks b n' current (by omega)]
      exact prgCallerClock_mono parameter chunks (b + 1) (Nat.sub_le_sub_right le _)
  · rw [prgCallerClock_done circuits settings parameter chunks b n (by omega),
      prgCallerClock_done circuits settings parameter chunks b n' (by omega)]
termination_by chunks.length - b

theorem prgCallerClock_one (parameter : PublicParameter) (chunks : List (List Job)) (b : ℕ)
    (current : b < chunks.length) :
    prgCallerClock circuits settings parameter chunks b 1 = lockstepStart circuits parameter chunks b + 1 := by
  rw [prgCallerClock_inside circuits settings parameter chunks b 1 current (by unfold batchRounds; omega),
    prgBatchClock_one]

/-- A floor at one cut remains valid at every later cut. -/
theorem prgFloor_after {limit cut n : ℕ}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (floor : ∀ Q, Residual cut P Q → PrgFloor limit Q) (le : cut ≤ n)
    {Q : OracleComp (PartySpec C E RealSpec) (Option α)} (run : Residual n P Q) :
    PrgFloor limit Q := by
  rw [show n = cut + (n - cut) by omega] at run
  obtain ⟨mid, first, last⟩ := run.split
  exact (floor mid first).residual last

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

theorem local_prg_mono {L L' : ℕ} {p : OracleComp (LocalSpec C) α}
    (le : L ≤ L') (quiet : IsQueryBoundP p (PrgFrom L) 0) :
    IsQueryBoundP p (PrgFrom L') 0 :=
  IsQueryBoundP.of_imp (fun _ h => prgFrom_antitone le h) quiet

-- Support-sensitive zero-budget bind, using VCVio's query-bound bind law.
theorem party_prg_bind {L : ℕ} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (quiet : PartyBudget (PrgFrom L) p 0)
    (rest : ∀ a, some a ∈ support p.run → PartyBudget (PrgFrom L) (f a) 0) :
    PartyBudget (PrgFrom L) (p >>= f) 0 := by
  unfold PartyBudget at *
  simp only [OptionT.run_bind, Option.elimM]
  apply isQueryBoundP_bind (m := 0) quiet
  intro a ha
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some a => exact rest a ha

set_option maxHeartbeats 1000000 in
/-- A cut through any encoded batch retains a floor on its entire continuation. -/
theorem caller_batch_prgClock (j n : ℕ) (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom 0) 0)
    (short : n < batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j [])) :
    PrgDisc (prgBatchClock circuits settings (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j [])
      (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding tree) j) n) n
      (callerProgram K D circuits settings top tree x setup j caller i).run ∧
    ∀ Q, Residual n (callerProgram K D circuits settings top tree x setup j caller i).run Q →
      PrgFloor (prgBatchClock circuits settings (x (refHolder D K.publicTerm)).parameter
        ((lockstepChunks settings caller.encoding tree).getD j [])
        (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
          (lockstepChunks settings caller.encoding tree) j) n) Q := by
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (lockstepChunks settings caller.encoding tree).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding tree) j
  set pre := depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  unfold callerProgram
  rw [treeSimCheckBatchAudit_run_prefix]
  rw [show (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
      (treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j) >>=
        treeSimCheckBatchFinish K circuits ctx jobs (start, j)) >>=
          callerCont K circuits settings top tree x setup j caller i) =
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
            callerCont K circuits settings top tree x setup j caller i) by simp only [bind_assoc]]
  by_cases early : n ≤ pre
  · rw [prgBatchClock_prefix circuits settings _ jobs start n early]
    apply prg_prefix_clock K circuits settings (caller.tail i) quiet ctx jobs (start, j)
    · intro data hd
      obtain ⟨_, _, hp⟩ := treeSimCheck_some_bind _ _ _ hd
      obtain ⟨_, label, _, _, _⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hp
      unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
      simp only [bind_assoc, pure_bind]
      apply (prgRunFloor_check K ctx data.2.1.2 data.2.2 _ (by simpa only [label] using le_rfl)).party_bind
      intro checked hchecked
      have final := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 hchecked
      apply (PrgFloor.of_noPrg (openRep_noPrg K ctx _ _)).party_bind
      intro opened _
      apply callerCont_prgFloor K circuits settings top tree x setup j caller i _
      dsimp only
      rw [final, label]
      omega
    · simpa only [parameter] using early
  · set cut := n - pre
    have split : n = pre + cut := by omega
    have countBound : cut ≤ checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) := by
      unfold batchRounds at short
      dsimp only [pre, cut]
      omega
    have timed := treeLockstep_localPrelude_timed (caller.tail i) _ _
      (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
    rw [parameter] at timed
    set limit := prgBatchClock circuits settings (x (refHolder D K.publicTerm)).parameter jobs start n
    have lower : start + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1 ≤ limit := by
      dsimp only [limit, prgBatchClock]
      rw [if_neg early, parameter]
      omega
    have hquiet := (party_prg_mono (Nat.zero_le limit) (localPrelude_prg (E := E) 0 _ quiet)).bind
      (fun _ => party_prg_mono lower (batchPrefix_window K circuits settings ctx jobs (start, j)))
    have suffix : ∀ data, some data ∈ support (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)).run →
        PrgDisc limit cut (treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
          callerCont K circuits settings top tree x setup j caller i).run ∧
        ∀ Q, Residual cut (treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
          callerCont K circuits settings top tree x setup j caller i).run Q → PrgFloor limit Q := by
      intro data hd
      obtain ⟨_, _, hp⟩ := treeSimCheck_some_bind _ _ _ hd
      obtain ⟨_, label, _, _, _⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hp
      have count := batchPrefix_count circuits settings K ctx jobs (start, j) data hp
      rw [parameter] at label count
      unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
      simp only [bind_assoc, pure_bind]
      have equal : limit = data.2.2.label + prgCheckClock (data.2.1.2.map (·.count)).sum cut := by
        dsimp only [limit, prgBatchClock]
        rw [if_neg early, label, count]
      rw [equal]
      apply prg_check_clock K ctx data.2.1.2 data.2.2
      · intro checked hchecked
        have final := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 hchecked
        apply (PrgFloor.of_noPrg (openRep_noPrg K ctx _ _)).party_bind
        intro opened _
        apply callerCont_prgFloor K circuits settings top tree x setup j caller i _
        simpa only [Prod.fst, final] using le_rfl
      · simpa only [count] using countBound
    refine ⟨?_, ?_⟩
    · rw [split]
      apply PrgDisc.timed_party_bind timed (PrgDisc.of_quiet hquiet _)
      intro data hd
      exact (suffix data hd).1
    · intro Q run
      rw [split] at run
      rcases Residual.party_bind timed run with aborted | ⟨data, hd, tail⟩
      · rw [aborted]; exact .pure _ _
      · exact (suffix data hd).2 Q tail

/-- The batch-end floor already holds before its final opening exchange. -/
theorem caller_batch_end_prgFloor (j n : ℕ) (caller : Caller C)
    (current : j < (lockstepChunks settings caller.encoding tree).length) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom 0) 0)
    (le : batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j []) - 1 ≤ n)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (run : Residual n (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    PrgFloor (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding tree) (j + 1)) Q := by
  have short : batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j []) - 1 <
      batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j []) := by unfold batchRounds; omega
  have floor := (caller_batch_prgClock circuits settings K D top tree x setup j _ caller i same quiet short).2
  rw [prgBatchClock_end, ← lockstepStart_succ circuits _ _ j current] at floor
  exact prgFloor_after floor le run

-- Port of TreeCheckSigningDisc.residual_batch_cont_quiet for every PRG cutoff.
set_option maxHeartbeats 1000000 in
theorem residual_batch_cont_prg (j : ℕ) (current : j < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (value : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      (∀ L, IsQueryBoundP tail (PrgFrom L) 0) ∧
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
  have hcount := batchPrefix_count circuits settings K ctx jobs (start, j) data hprefix
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
  exact ⟨_, _, _, openTail_prg K ctx.self _ _ inbox, rfl⟩

-- Port of TreeCheckSigningDisc.residual_last_quiet with the literal opening tail.
theorem residual_last_prg (j : ℕ) (last : j + 1 = (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (opened : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      (∀ L, IsQueryBoundP tail (PrgFrom L) 0) ∧
      Q = (treeLockstepLocalPrelude tail >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
          ((some opened, caller.records i ++ [record]),
            (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
              (firstChunks settings tree) (j + 1), j + 1))).run := by
  have current : j < (firstChunks settings tree).length := by omega
  rcases residual_batch_cont_prg circuits settings K D top tree x setup j current caller i same h with
    none | ⟨value, record, tail, quiet, rfl⟩
  · exact .inl none
  obtain ⟨values, saved⟩ := outputs
  refine .inr ⟨values.flatten ++ value, record, tail, quiet, ?_⟩
  have empty : (firstChunks settings tree).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
  unfold callerCont
  simp only [phaseChunks, phaseIndex, if_pos current, empty, List.mapM_nil, saved]
  simp [foldlM_some]

-- Port of TreeCheckSigningDisc.residual_sign_batch_quiet for every PRG cutoff.
set_option maxHeartbeats 1000000 in
theorem residual_sign_batch_prg (b : Fin (2 ^ layerHeight)) (j : ℕ) (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (next : j + 1 < treeBatches settings (.bottom b))
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding (.bottom b)).getD j [])) (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q) :
    Q = pure none ∨ ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      (∀ L, IsQueryBoundP (caller'.tail i) (PrgFrom L) 0) ∧
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
  have hcount := batchPrefix_count circuits settings K ctx jobs (start, j) data hprefix
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
    by simp [stepCaller], openTail_prg K ctx.self count data.2.1.1 inbox, ?_⟩
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  unfold callerProgram
  simp only [stepCaller, labels]

-- Port of TreeCheckPrgDisc.caller_batch_prg on the complete encoded job list.
/-- A complete signing batch only uses labels below the next batch start. -/
theorem sign_caller_batch_prg (b : Fin (2 ^ layerHeight)) (j limit : ℕ) (current : j < treeBatches settings (.bottom b))
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom limit) 0)
    (bound : lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) ≤ limit) :
    PrgDisc limit (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding (.bottom b)).getD j []))
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
  have prefixQuiet := (localPrelude_prg (E := E) limit _ quiet).bind
    (fun _ => party_prg_mono (by
      rw [lockstepStart_succ circuits _ _ j current'] at bound
      unfold batchLabels at bound
      simpa only [start, jobs, parameter, Prod.fst] using
        (show lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
          (lockstepChunks settings caller.encoding (.bottom b)) j +
          depth (((lockstepChunks settings caller.encoding (.bottom b)).getD j []).map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) + 1 ≤ limit by omega))
      (batchPrefix_window K circuits settings ctx jobs (start, j)))
  rw [parameter] at prefixTimed
  rw [show batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter jobs =
      (depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) +
        (checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) + 1) by
      unfold batchRounds; omega]
  apply PrgDisc.timed_party_bind prefixTimed (PrgDisc.of_quiet prefixQuiet _)
  intro data hdata
  obtain ⟨-, -, hprefix⟩ := treeSimCheck_some_bind _ _ _ hdata
  obtain ⟨-, hlabel, -, -, -⟩ :=
    treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hprefix
  have hcount := batchPrefix_count circuits settings K ctx jobs (start, j) data hprefix
  rw [parameter] at hcount hlabel
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  simp only [bind_assoc, pure_bind]
  have checkTimed := check_timed K ctx data.2.1.2 data.2.2
  have checkDisc := check_window K ctx data.2.1.2 data.2.2 limit (by
    rw [hcount, hlabel]
    rw [lockstepStart_succ circuits _ _ j current'] at bound
    unfold batchLabels at bound
    simpa only [start, jobs, Nat.add_assoc, Prod.fst] using bound)
  rw [hcount] at checkTimed
  apply PrgDisc.timed_party_bind checkTimed
  · simpa only [hcount] using PrgDisc.of_quiet checkDisc (checkLabels (data.2.1.2.map (·.count)).sum)
  · intro checked _
    exact openRep_first_prg K ctx _ _ limit _

/-- The final signing continuation is quiet, so its endpoint bounds every pass. -/
theorem sign_last_prgDisc (b : Fin (2 ^ layerHeight)) (j : ℕ)
    (last : j + 1 = treeBatches settings (.bottom b)) (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom 0) 0) :
    ∀ n, PrgDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) (j + 1)) n
      (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run := by
  intro n
  apply PrgDisc.of_quiet
  have current : j < (lockstepChunks settings caller.encoding (.bottom b)).length := by
    rw [lockstepChunks_length]
    omega
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (lockstepChunks settings caller.encoding (.bottom b)).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding (.bottom b)) j
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  unfold callerProgram
  apply party_prg_bind (party_prg_mono (Nat.zero_le _) (localPrelude_prg (E := E) 0 _ quiet))
  intro _ _
  rw [treeSimCheckBatchAudit_run_prefix]
  simp only [bind_assoc]
  apply party_prg_bind (party_prg_mono (show start + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1 ≤
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) from by
    rw [lockstepStart_succ circuits _ _ j current]
    unfold batchLabels
    rw [parameter]
    dsimp only [start, jobs]
    omega) (batchPrefix_window K circuits settings ctx jobs (start, j)))
  intro data hp
  obtain ⟨_, label, _, _, _⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hp
  have count := batchPrefix_count circuits settings K ctx jobs (start, j) data hp
  rw [parameter] at label count
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  simp only [bind_assoc, pure_bind]
  have bound : data.2.2.label + checkLabels (data.2.1.2.map (·.count)).sum ≤
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) := by
    rw [count, label, lockstepStart_succ circuits _ _ j current]
    unfold batchLabels
    dsimp only [start, jobs]
    omega
  apply party_prg_bind (check_window K ctx data.2.1.2 data.2.2 _ bound)
  intro checked _
  apply party_prg_bind (party_prg_mono (Nat.zero_le _) (openRep_noPrg K ctx _ _))
  intro opened _
  exact party_prg_mono (Nat.zero_le _) (callerCont_sign_last_noPrg K circuits settings top x setup b j last caller i _)

/-- One party's clock proof; the clock itself contains no party-dependent data. -/
theorem sign_caller_prgPoint (b : Fin (2 ^ layerHeight)) (j n : ℕ)
    (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (current : j < treeBatches settings (.bottom b)) (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom 0) 0) :
    PrgDisc (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) j n) n
      (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run ∧
    ∀ Q, Residual n (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q →
      PrgFloor (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) j n) Q := by
  have current' : j < (lockstepChunks settings caller.encoding (.bottom b)).length := by
    rwa [lockstepChunks_length]
  set rounds := batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
    ((lockstepChunks settings caller.encoding (.bottom b)).getD j [])
  by_cases short : n < rounds
  · rw [prgCallerClock_inside circuits settings _ _ j n current' short]
    exact caller_batch_prgClock circuits settings K D top (.bottom b) x setup j n caller i same quiet short
  · have long : rounds ≤ n := by omega
    rw [prgCallerClock_next circuits settings _ _ j n current' long]
    by_cases last : j + 1 = treeBatches settings (.bottom b)
    · rw [prgCallerClock_done circuits settings _ _ (j + 1) _ (by rw [lockstepChunks_length]; omega)]
      rw [lockstepChunks_length, ← last]
      refine ⟨sign_last_prgDisc circuits settings K D top x setup b j last caller i same quiet n, ?_⟩
      intro Q run
      exact caller_batch_end_prgFloor circuits settings K D top (.bottom b) x setup j n caller current' i same quiet
        (by dsimp only [rounds] at long; omega) run
    · have next : j + 1 < treeBatches settings (.bottom b) := by omega
      have bound := prgCallerClock_lower circuits settings (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) (n - rounds)
      refine ⟨?_, ?_⟩
      · suffices disc : PrgDisc (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
            (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) (n - rounds))
            (rounds + (n - rounds))
            (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run by
          convert disc using 1; omega
        apply (sign_caller_batch_prg circuits settings K D top x setup b j _ current caller i same (local_prg_mono (Nat.zero_le _) quiet) bound).of_residual
        intro Q run
        rcases residual_sign_batch_prg circuits settings K D top x setup b j signing next caller i same run with
          aborted | ⟨caller', encoding, _, _, quiet', rfl⟩
        · rw [aborted]; exact .pure _ _
        · simpa only [encoding, ite_self] using
            (sign_caller_prgPoint b (j + 1) (n - rounds) (by omega) next caller' i same (quiet' 0)).1
      · intro Q run
        rw [show n = rounds + (n - rounds) by omega] at run
        obtain ⟨mid, first, rest⟩ := run.split
        rcases residual_sign_batch_prg circuits settings K D top x setup b j signing next caller i same first with
          aborted | ⟨caller', encoding, _, _, quiet', rfl⟩
        · rw [aborted] at rest
          rw [rest.pure_inv]
          exact .pure _ _
        · have floor := (sign_caller_prgPoint b (j + 1) (n - rounds) (by omega) next caller' i same (quiet' 0)).2 Q rest
          simpa only [encoding] using floor
termination_by treeBatches settings (.bottom b) - j

/-- A common monotone clock, fixed before the party and all exchange answers. -/
theorem sign_caller_prgClock (b : Fin (2 ^ layerHeight)) (j n : ℕ)
    (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (current : j < treeBatches settings (.bottom b)) (caller : Caller C) :
    let limit := prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) j n
    lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) j ≤ limit ∧
    ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter →
      IsQueryBoundP (caller.tail i) (PrgFrom 0) 0 →
      PrgDisc limit n (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run ∧
      ∀ Q, Residual n (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q →
        PrgFloor limit Q := by
  exact ⟨prgCallerClock_lower circuits settings _ _ j n,
    fun i same quiet => sign_caller_prgPoint circuits settings K D top x setup b j n signing current caller i same quiet⟩

/-- First-run windows retain the whole future, including every later head choice. -/
theorem first_caller_prgPoint (j n : ℕ) (current : j < (firstChunks settings tree).length)
    (horizon : n ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree).length -
      batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom 0) 0) :
    PrgDisc (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) j n) n
      (callerProgram K D circuits settings top tree x setup j caller i).run ∧
    ∀ Q, Residual n (callerProgram K D circuits settings top tree x setup j caller i).run Q →
      PrgFloor (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) j n) Q := by
  have jobs := TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j current
  have start := TreeCheckWalkState.lockstepStart_first circuits settings tree
    (x (refHolder D K.publicTerm)).parameter caller.encoding j current.le
  have current' : j < (lockstepChunks settings caller.encoding tree).length := by
    cases tree <;> simp only [firstChunks, treeLockstepFirstJobs, lockstepChunks, List.length_append] at current ⊢ <;> omega
  set rounds := batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
    ((firstChunks settings tree).getD j [])
  by_cases short : n < rounds
  · rw [prgCallerClock_inside circuits settings _ _ j n current short]
    have h := caller_batch_prgClock circuits settings K D top tree x setup j n caller i same quiet (by rwa [jobs])
    simpa only [jobs, start] using h
  · have long : rounds ≤ n := by omega
    rw [prgCallerClock_next circuits settings _ _ j n current long]
    have step := batchStart_succ circuits settings tree (x (refHolder D K.publicTerm)).parameter j current
    by_cases last : j + 1 = (firstChunks settings tree).length
    · rw [prgCallerClock_done circuits settings _ _ (j + 1) _ last.ge]
      have equal : n = rounds := by rw [last] at step; dsimp only [rounds]; omega
      refine ⟨?_, ?_⟩
      · rw [equal]
        exact caller_batch_prg K D circuits settings top tree x setup j _ current caller i same (local_prg_mono (Nat.zero_le _) quiet)
          (lockstepStart_mono circuits _ _ last.le)
      · intro Q run
        have floor := caller_batch_end_prgFloor circuits settings K D top tree x setup j n caller current' i same quiet
          (by rw [jobs]; dsimp only [rounds] at long; omega) run
        rw [TreeCheckWalkState.lockstepStart_first circuits settings tree _ caller.encoding
          (j + 1) last.le, last] at floor
        exact floor
    · have next : j + 1 < (firstChunks settings tree).length := by omega
      have order := batchStart_mono circuits settings tree (x (refHolder D K.publicTerm)).parameter next.le
      have horizon' : n - rounds ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
          (firstChunks settings tree).length -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (j + 1) := by
        dsimp only [rounds]
        omega
      have bound := prgCallerClock_lower circuits settings (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) (j + 1) (n - rounds)
      refine ⟨?_, ?_⟩
      · suffices disc : PrgDisc (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
            (firstChunks settings tree) (j + 1) (n - rounds)) (rounds + (n - rounds))
            (callerProgram K D circuits settings top tree x setup j caller i).run by
          convert disc using 1; omega
        apply (caller_batch_prg K D circuits settings top tree x setup j _ current caller i same (local_prg_mono (Nat.zero_le _) quiet) bound).of_residual
        intro Q run
        rcases residual_batch_prg K D circuits settings top tree x setup j next caller i same run with
          aborted | ⟨caller', _, _, _, quiet', rfl⟩
        · rw [aborted]; exact .pure _ _
        · simpa only [ite_self] using
            (first_caller_prgPoint (j + 1) (n - rounds) next horizon' caller' i same (quiet' 0)).1
      · intro Q run
        rw [show n = rounds + (n - rounds) by omega] at run
        obtain ⟨mid, first, rest⟩ := run.split
        rcases residual_batch_prg K D circuits settings top tree x setup j next caller i same first with
          aborted | ⟨caller', _, _, _, quiet', rfl⟩
        · rw [aborted] at rest
          rw [rest.pure_inv]
          exact .pure _ _
        · exact (first_caller_prgPoint (j + 1) (n - rounds) next horizon' caller' i same (quiet' 0)).2 Q rest
termination_by (firstChunks settings tree).length - j

/-- The actual initial program has one common clock through the first-run boundary. -/
theorem initial_program_prgClock (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (positive : 0 < (firstChunks settings tree).length) (dealt : DealtInputs D x)
    (n : ℕ) (horizon : n ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree).length) :
    let limit := prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) 0 n
    limit ≤ lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) (firstChunks settings tree).length ∧
    (∀ i, PrgDisc limit n ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run) ∧
    ∀ i Q, Residual n ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run Q →
      PrgFloor limit Q := by
  obtain ⟨head, rest, chunks⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos positive)
  have point : ∀ i,
      PrgDisc (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) 0 n) n
        ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run ∧
      ∀ Q, Residual n ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run Q →
        PrgFloor (prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
          (firstChunks settings tree) 0 n) Q := by
    intro i
    rw [initial_program K D A circuits settings top tree x start head rest chunks i, boundary_program]
    have same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
      obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
      rw [hx i, hx (refHolder D K.publicTerm)]
      rfl
    apply first_caller_prgPoint circuits settings K D top tree x start.1.2 0 n positive _ (firstCaller start.1.2) i same
    · exact isQueryBoundP_pure _ _ _
    · simpa only [batchStart, List.take_zero, List.map_nil, List.sum_nil, Nat.sub_zero] using horizon
  exact ⟨prgCallerClock_upper circuits settings _ _ 0 n, fun i => (point i).1, fun i => (point i).2⟩

end TreeCheckPrgSigningClock
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.prgBatchClock_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.prgBatchClock_one

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.prgCallerClock_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.prgCallerClock_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.prgCallerClock_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.prgCallerClock_one

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.caller_batch_prgClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.caller_batch_prgClock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.caller_batch_end_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.caller_batch_end_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.residual_sign_batch_prg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.residual_sign_batch_prg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.residual_last_prg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.residual_last_prg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.sign_caller_batch_prg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.sign_caller_batch_prg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.sign_last_prgDisc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.sign_last_prgDisc

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.sign_caller_prgClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.sign_caller_prgClock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.initial_program_prgClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningClock.initial_program_prgClock
