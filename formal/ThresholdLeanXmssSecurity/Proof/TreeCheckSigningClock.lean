import ThresholdLeanXmssSecurity.Proof.TreeCheckCoinFloor
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSigning

/-! # Common clocks for audited caller prefixes

The clock depends on the common public parameter, encoded chunks and pass
count. Each local program has past check discipline and a floor on every
future residual. The initial-program clock covers the first run while its
future floor includes every supported signing-head choice.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckSigningClock
open TreeCheckCoinClock TreeCheckCoinFloor TreeCheckHonestDisc TreeCheckSigningDisc
open TreeCheckWalkRecipe TreeCheckWalkState TreeCheckWalkEntry TreeCheckWalkSigning TreeSimHashCount
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α : Type}
variable (circuits : Circuits) (settings : Settings)

def batchClock (parameter : PublicParameter) (jobs : List Job) (start n : ℕ) : ℕ :=
  start + depth (jobs.map (circuits parameter ·.kind)) + 1 +
    checkClock (batchCount circuits parameter jobs)
      (n - (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1))

theorem batchClock_prefix (parameter : PublicParameter) (jobs : List Job) (start n : ℕ)
    (le : n ≤ depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1) :
    batchClock circuits settings parameter jobs start n =
      start + depth (jobs.map (circuits parameter ·.kind)) + 1 := by
  simp only [batchClock, Nat.sub_eq_zero_of_le le, checkClock_zero, Nat.add_zero]

theorem batchClock_lower (parameter : PublicParameter) (jobs : List Job) (start n : ℕ) :
    start ≤ batchClock circuits settings parameter jobs start n := by unfold batchClock; omega

theorem batchClock_upper (parameter : PublicParameter) (jobs : List Job) (start n : ℕ) :
    batchClock circuits settings parameter jobs start n ≤ start + batchLabels circuits parameter jobs := by
  have h := checkClock_le (batchCount circuits parameter jobs)
    (n - (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1))
  unfold batchClock batchLabels
  omega

theorem batchClock_mono (parameter : PublicParameter) (jobs : List Job) (start : ℕ) :
    Monotone (batchClock circuits settings parameter jobs start) := by
  intro n n' le
  exact Nat.add_le_add_left (checkClock_mono _ (Nat.sub_le_sub_right le _)) _

theorem batchClock_end (parameter : PublicParameter) (jobs : List Job) (start : ℕ) :
    batchClock circuits settings parameter jobs start
      (batchRounds circuits settings.mode parameter jobs - 1) =
        start + batchLabels circuits parameter jobs := by
  unfold batchClock batchRounds batchLabels
  rw [show (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 +
      checkLabels (batchCount circuits parameter jobs) + 1 - 1) -
      (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1) =
        checkLabels (batchCount circuits parameter jobs) by omega, checkClock_end]
  omega

def callerClock (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ) : ℕ :=
  if _h : b < chunks.length then
    if n < batchRounds circuits settings.mode parameter (chunks.getD b []) then
      batchClock circuits settings parameter (chunks.getD b []) (lockstepStart circuits parameter chunks b) n
    else callerClock parameter chunks (b + 1) (n - batchRounds circuits settings.mode parameter (chunks.getD b []))
  else lockstepStart circuits parameter chunks chunks.length
termination_by chunks.length - b

theorem callerClock_done (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ)
    (last : chunks.length ≤ b) :
    callerClock circuits settings parameter chunks b n = lockstepStart circuits parameter chunks chunks.length := by
  rw [callerClock, dif_neg (Nat.not_lt.mpr last)]

theorem callerClock_inside (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ)
    (current : b < chunks.length) (short : n < batchRounds circuits settings.mode parameter (chunks.getD b [])) :
    callerClock circuits settings parameter chunks b n =
      batchClock circuits settings parameter (chunks.getD b []) (lockstepStart circuits parameter chunks b) n := by
  rw [callerClock, dif_pos current, if_pos short]

theorem callerClock_next (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ)
    (current : b < chunks.length) (long : batchRounds circuits settings.mode parameter (chunks.getD b []) ≤ n) :
    callerClock circuits settings parameter chunks b n =
      callerClock circuits settings parameter chunks (b + 1)
        (n - batchRounds circuits settings.mode parameter (chunks.getD b [])) := by
  rw [callerClock, dif_pos current, if_neg (Nat.not_lt.mpr long)]

theorem callerClock_lower (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ) :
    lockstepStart circuits parameter chunks b ≤ callerClock circuits settings parameter chunks b n := by
  rw [callerClock]
  split_ifs with current short
  · exact batchClock_lower circuits settings parameter _ _ _
  · exact le_trans (lockstepStart_mono circuits parameter chunks (Nat.le_succ b))
      (callerClock_lower parameter chunks (b + 1) _)
  · simp only [lockstepStart, List.take_of_length_le (Nat.le_of_not_gt current), List.take_length]
    exact le_rfl
termination_by chunks.length - b

theorem callerClock_upper (parameter : PublicParameter) (chunks : List (List Job)) (b n : ℕ) :
    callerClock circuits settings parameter chunks b n ≤ lockstepStart circuits parameter chunks chunks.length := by
  rw [callerClock]
  split_ifs with current short
  · have bound := batchClock_upper circuits settings parameter (chunks.getD b [])
      (lockstepStart circuits parameter chunks b) n
    rw [← lockstepStart_succ circuits parameter chunks b current] at bound
    exact le_trans bound (lockstepStart_mono circuits parameter chunks (by omega))
  · exact callerClock_upper parameter chunks (b + 1) _
  · exact le_rfl
termination_by chunks.length - b

theorem callerClock_mono (parameter : PublicParameter) (chunks : List (List Job)) (b : ℕ) :
    Monotone (callerClock circuits settings parameter chunks b) := by
  intro n n' le
  by_cases current : b < chunks.length
  · by_cases short : n < batchRounds circuits settings.mode parameter (chunks.getD b [])
    · rw [callerClock_inside circuits settings parameter chunks b n current short]
      by_cases short' : n' < batchRounds circuits settings.mode parameter (chunks.getD b [])
      · rw [callerClock_inside circuits settings parameter chunks b n' current short']
        exact batchClock_mono circuits settings parameter _ _ le
      · rw [callerClock_next circuits settings parameter chunks b n' current (by omega)]
        have bound := batchClock_upper circuits settings parameter (chunks.getD b [])
          (lockstepStart circuits parameter chunks b) n
        rw [← lockstepStart_succ circuits parameter chunks b current] at bound
        exact le_trans bound (callerClock_lower circuits settings parameter chunks (b + 1) _)
    · rw [callerClock_next circuits settings parameter chunks b n current (by omega),
        callerClock_next circuits settings parameter chunks b n' current (by omega)]
      exact callerClock_mono parameter chunks (b + 1) (Nat.sub_le_sub_right le _)
  · rw [callerClock_done circuits settings parameter chunks b n (by omega),
      callerClock_done circuits settings parameter chunks b n' (by omega)]
termination_by chunks.length - b

/-- A floor at one cut remains valid at every later cut. -/
theorem floor_after {limit cut n : ℕ}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (floor : ∀ Q, Residual cut P Q → CheckFloor limit Q) (le : cut ≤ n)
    {Q : OracleComp (PartySpec C E RealSpec) (Option α)} (run : Residual n P Q) :
    CheckFloor limit Q := by
  rw [show n = cut + (n - cut) by omega] at run
  obtain ⟨mid, first, last⟩ := run.split
  exact (floor mid first).residual last

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

-- Extracted from TreeCheckSigningDisc.sign_caller_batch's count calculation.
theorem batchPrefix_count (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (data : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (h : some data ∈ support (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run) :
    (data.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
  unfold treeSimCheckBatchPrefix at h
  obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨q, hq, he⟩ := treeSimCheck_some_bind _ _ _ hrest
  have equal : data = (inputs, q) := by simpa only [OptionT.run_pure, support_pure,
    Set.mem_singleton_iff, Option.some.injEq] using he
  subst data
  exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs initial.1 initial.2 q.1 q.2 hq

/-- Every pass of the circuit prefix is quiet for check queries. -/
theorem caller_prefix_disc (j limit n : ℕ) (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (le : n ≤ depth (((lockstepChunks settings caller.encoding tree).getD j []).map
      (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) :
    CheckDisc limit n ∅ (callerProgram K D circuits settings top tree x setup j caller i).run := by
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (lockstepChunks settings caller.encoding tree).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding tree) j
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
  have timed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
  have hquiet := (localPrelude_quiet (E := E) _ quiet).bind
    (fun _ => batchPrefix_quiet K circuits settings ctx jobs (start, j))
  rw [parameter] at timed
  have disc := CheckDisc.timed_party_bind (n := 0) (limit := limit) (keys := ∅)
    (f := fun data => treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
      callerCont K circuits settings top tree x setup j caller i) timed
    (Disc.of_quiet hquiet _) (fun _ _ => CheckDisc.zero _ _)
  exact (show CheckDisc limit _ ∅ _ from by simpa only [Nat.add_zero] using disc).antitone le

set_option maxHeartbeats 1000000 in
/-- A cut through any encoded batch retains a floor on its entire continuation. -/
theorem caller_batch_clock (j n : ℕ) (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (short : n < batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j [])) :
    CheckDisc (batchClock circuits settings (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j [])
      (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding tree) j) n) n ∅
      (callerProgram K D circuits settings top tree x setup j caller i).run ∧
    ∀ Q, Residual n (callerProgram K D circuits settings top tree x setup j caller i).run Q →
      CheckFloor (batchClock circuits settings (x (refHolder D K.publicTerm)).parameter
        ((lockstepChunks settings caller.encoding tree).getD j [])
        (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
          (lockstepChunks settings caller.encoding tree) j) n) Q := by
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (lockstepChunks settings caller.encoding tree).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding tree) j
  set pre := depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  by_cases early : n ≤ pre
  · rw [batchClock_prefix circuits settings _ jobs start n early]
    refine ⟨caller_prefix_disc circuits settings K D top tree x setup j _ n caller i same quiet early, ?_⟩
    intro Q run
    have floor := callerProgram_check_floor K circuits settings top tree x setup D j caller i quiet
    rw [same] at floor
    exact floor.residual run
  · set cut := n - pre
    have split : n = pre + cut := by omega
    have countBound : cut ≤ checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) := by
      unfold batchRounds at short
      dsimp only [pre, cut]
      omega
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
    have timed := treeLockstep_localPrelude_timed (caller.tail i) _ _
      (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
    rw [parameter] at timed
    have hquiet := (localPrelude_quiet (E := E) _ quiet).bind
      (fun _ => batchPrefix_quiet K circuits settings ctx jobs (start, j))
    set limit := batchClock circuits settings (x (refHolder D K.publicTerm)).parameter jobs start n
    have suffix : ∀ data, some data ∈ support (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)).run →
        CheckDisc limit cut ∅ (treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
          callerCont K circuits settings top tree x setup j caller i).run ∧
        ∀ Q, Residual cut (treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
          callerCont K circuits settings top tree x setup j caller i).run Q → CheckFloor limit Q := by
      intro data hd
      obtain ⟨_, _, hp⟩ := treeSimCheck_some_bind _ _ _ hd
      obtain ⟨_, label, _, _, _⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hp
      have count := batchPrefix_count circuits settings K ctx jobs (start, j) data hp
      rw [parameter] at label count
      unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
      simp only [bind_assoc, pure_bind]
      change CheckDisc (start + depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) + 1 +
          checkClock (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) cut) cut ∅ _ ∧ _
      have equal : limit = data.2.2.label + checkClock (data.2.1.2.map (·.count)).sum cut := by
        dsimp only [limit, batchClock, cut, pre]
        rw [label, count]
      rw [← label, ← count]
      change CheckDisc (data.2.2.label + checkClock (data.2.1.2.map (·.count)).sum cut) cut ∅ _ ∧
        ∀ Q, Residual cut _ Q → CheckFloor limit Q
      rw [equal]
      apply check_clock K ctx data.2.1.2 data.2.2
      · intro checked hchecked
        have final := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 hchecked
        apply (CheckFloor.of_quiet (openRep_checkQuiet K ctx _ _)).party_bind
        intro opened _
        apply callerCont_floor K circuits settings top tree x setup j caller i _
        simpa only [Prod.fst, final] using le_rfl
      · simpa only [count] using countBound
    refine ⟨?_, ?_⟩
    · rw [split]
      apply CheckDisc.timed_party_bind timed (Disc.of_quiet hquiet _)
      intro data hd
      exact (suffix data hd).1
    · intro Q run
      rw [split] at run
      rcases Residual.party_bind timed run with aborted | ⟨data, hd, tail⟩
      · rw [aborted]; exact .pure _ _
      · exact (suffix data hd).2 Q tail

/-- The batch-end floor already holds before its final opening exchange. -/
theorem caller_batch_end_floor (j n : ℕ) (caller : Caller C)
    (current : j < (lockstepChunks settings caller.encoding tree).length) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (le : batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j []) - 1 ≤ n)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (run : Residual n (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    CheckFloor (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding tree) (j + 1)) Q := by
  have short : batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j []) - 1 <
      batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((lockstepChunks settings caller.encoding tree).getD j []) := by unfold batchRounds; omega
  have floor := (caller_batch_clock circuits settings K D top tree x setup j _ caller i same quiet short).2
  rw [batchClock_end, ← lockstepStart_succ circuits _ _ j current] at floor
  exact floor_after floor le run

/-- The final signing continuation is quiet, so its endpoint bounds every pass. -/
theorem sign_last_disc (b : Fin (2 ^ layerHeight)) (j : ℕ)
    (last : j + 1 = treeBatches settings (.bottom b)) (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    Disc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) (j + 1)) ∅
      (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run := by
  have current : j < (lockstepChunks settings caller.encoding (.bottom b)).length := by
    rw [lockstepChunks_length]
    omega
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (lockstepChunks settings caller.encoding (.bottom b)).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding (.bottom b)) j
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  unfold callerProgram
  apply (Disc.of_quiet (localPrelude_quiet (E := E) _ quiet)).party_bind
  intro _ _
  rw [treeSimCheckBatchAudit_run_prefix]
  simp only [bind_assoc]
  apply (Disc.of_quiet (batchPrefix_quiet K circuits settings ctx jobs (start, j))).party_bind
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
  apply (runDisc_check K ctx data.2.1.2 data.2.2 _ bound).party_bind
  intro checked _
  apply (Disc.of_quiet (openRep_checkQuiet K ctx _ _)).party_bind
  intro opened _
  exact Disc.of_quiet (callerCont_sign_last_quiet K circuits settings top x setup b j last caller i _)

/-- One party's clock proof; the clock itself contains no party-dependent data. -/
theorem sign_caller_point (b : Fin (2 ^ layerHeight)) (j n : ℕ)
    (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (current : j < treeBatches settings (.bottom b)) (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckDisc (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) j n) n ∅
      (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run ∧
    ∀ Q, Residual n (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q →
      CheckFloor (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) j n) Q := by
  have current' : j < (lockstepChunks settings caller.encoding (.bottom b)).length := by
    rwa [lockstepChunks_length]
  set rounds := batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
    ((lockstepChunks settings caller.encoding (.bottom b)).getD j [])
  by_cases short : n < rounds
  · rw [callerClock_inside circuits settings _ _ j n current' short]
    exact caller_batch_clock circuits settings K D top (.bottom b) x setup j n caller i same quiet short
  · have long : rounds ≤ n := by omega
    rw [callerClock_next circuits settings _ _ j n current' long]
    by_cases last : j + 1 = treeBatches settings (.bottom b)
    · rw [callerClock_done circuits settings _ _ (j + 1) _ (by rw [lockstepChunks_length]; omega)]
      rw [lockstepChunks_length, ← last]
      refine ⟨sign_last_disc circuits settings K D top x setup b j last caller i same quiet n, ?_⟩
      intro Q run
      exact caller_batch_end_floor circuits settings K D top (.bottom b) x setup j n caller current' i same quiet
        (by dsimp only [rounds] at long; omega) run
    · have next : j + 1 < treeBatches settings (.bottom b) := by omega
      have bound := callerClock_lower circuits settings (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) (n - rounds)
      refine ⟨?_, ?_⟩
      · suffices disc : CheckDisc (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
            (lockstepChunks settings caller.encoding (.bottom b)) (j + 1) (n - rounds))
            (rounds + (n - rounds)) ∅
            (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run by
          convert disc using 1; omega
        apply (sign_caller_batch K D circuits settings top x setup b j _ current caller i same quiet bound).of_residual
        intro Q run
        rcases residual_sign_batch_quiet K D circuits settings top x setup b j signing next caller i same run with
          aborted | ⟨caller', encoding, _, _, quiet', rfl⟩
        · rw [aborted]; exact .pure _ _ _
        · simpa only [encoding, ite_self] using
            (sign_caller_point b (j + 1) (n - rounds) (by omega) next caller' i same quiet').1
      · intro Q run
        rw [show n = rounds + (n - rounds) by omega] at run
        obtain ⟨mid, first, rest⟩ := run.split
        rcases residual_sign_batch_quiet K D circuits settings top x setup b j signing next caller i same first with
          aborted | ⟨caller', encoding, _, _, quiet', rfl⟩
        · rw [aborted] at rest
          rw [rest.pure_inv]
          exact .pure _ _
        · have floor := (sign_caller_point b (j + 1) (n - rounds) (by omega) next caller' i same quiet').2 Q rest
          simpa only [encoding] using floor
termination_by treeBatches settings (.bottom b) - j

/-- A common monotone clock, fixed before the party and all exchange answers. -/
theorem sign_caller_clock (b : Fin (2 ^ layerHeight)) (j n : ℕ)
    (signing : (firstChunks settings (.bottom b)).length ≤ j)
    (current : j < treeBatches settings (.bottom b)) (caller : Caller C) :
    let limit := callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) j n
    lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) j ≤ limit ∧
    ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter →
      IsQueryBoundP (caller.tail i) CheckQuery 0 →
      CheckDisc limit n ∅ (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run ∧
      ∀ Q, Residual n (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run Q →
        CheckFloor limit Q := by
  exact ⟨callerClock_lower circuits settings _ _ j n,
    fun i same quiet => sign_caller_point circuits settings K D top x setup b j n signing current caller i same quiet⟩

/-- First-run windows retain the whole future, including every later head choice. -/
theorem first_caller_point (j n : ℕ) (current : j < (firstChunks settings tree).length)
    (horizon : n ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree).length -
      batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckDisc (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) j n) n ∅
      (callerProgram K D circuits settings top tree x setup j caller i).run ∧
    ∀ Q, Residual n (callerProgram K D circuits settings top tree x setup j caller i).run Q →
      CheckFloor (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) j n) Q := by
  have jobs := TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j current
  have start := TreeCheckWalkState.lockstepStart_first circuits settings tree
    (x (refHolder D K.publicTerm)).parameter caller.encoding j current.le
  have current' : j < (lockstepChunks settings caller.encoding tree).length := by
    cases tree <;> simp only [firstChunks, treeLockstepFirstJobs, lockstepChunks, List.length_append] at current ⊢ <;> omega
  set rounds := batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
    ((firstChunks settings tree).getD j [])
  by_cases short : n < rounds
  · rw [callerClock_inside circuits settings _ _ j n current short]
    have h := caller_batch_clock circuits settings K D top tree x setup j n caller i same quiet (by rwa [jobs])
    simpa only [jobs, start] using h
  · have long : rounds ≤ n := by omega
    rw [callerClock_next circuits settings _ _ j n current long]
    have step := batchStart_succ circuits settings tree (x (refHolder D K.publicTerm)).parameter j current
    by_cases last : j + 1 = (firstChunks settings tree).length
    · rw [callerClock_done circuits settings _ _ (j + 1) _ last.ge]
      have equal : n = rounds := by rw [last] at step; dsimp only [rounds]; omega
      refine ⟨?_, ?_⟩
      · rw [equal]
        exact caller_batch K D circuits settings top tree x setup j _ current caller i same quiet
          (lockstepStart_mono circuits _ _ last.le)
      · intro Q run
        have floor := caller_batch_end_floor circuits settings K D top tree x setup j n caller current' i same quiet
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
      have bound := callerClock_lower circuits settings (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) (j + 1) (n - rounds)
      refine ⟨?_, ?_⟩
      · suffices disc : CheckDisc (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
            (firstChunks settings tree) (j + 1) (n - rounds)) (rounds + (n - rounds)) ∅
            (callerProgram K D circuits settings top tree x setup j caller i).run by
          convert disc using 1; omega
        apply (caller_batch K D circuits settings top tree x setup j _ current caller i same quiet bound).of_residual
        intro Q run
        rcases residual_batch_quiet K D circuits settings top tree x setup j next caller i same run with
          aborted | ⟨caller', _, _, _, quiet', rfl⟩
        · rw [aborted]; exact .pure _ _ _
        · simpa only [ite_self] using
            (first_caller_point (j + 1) (n - rounds) next horizon' caller' i same quiet').1
      · intro Q run
        rw [show n = rounds + (n - rounds) by omega] at run
        obtain ⟨mid, first, rest⟩ := run.split
        rcases residual_batch_quiet K D circuits settings top tree x setup j next caller i same first with
          aborted | ⟨caller', _, _, _, quiet', rfl⟩
        · rw [aborted] at rest
          rw [rest.pure_inv]
          exact .pure _ _
        · exact (first_caller_point (j + 1) (n - rounds) next horizon' caller' i same quiet').2 Q rest
termination_by (firstChunks settings tree).length - j

/-- The actual initial program has one common clock through the first-run boundary. -/
theorem initial_program_clock (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (positive : 0 < (firstChunks settings tree).length) (dealt : DealtInputs D x)
    (n : ℕ) (horizon : n ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree).length) :
    let limit := callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) 0 n
    limit ≤ lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) (firstChunks settings tree).length ∧
    (∀ i, CheckDisc limit n ∅ ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run) ∧
    ∀ i Q, Residual n ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run Q →
      CheckFloor limit Q := by
  obtain ⟨head, rest, chunks⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos positive)
  have point : ∀ i,
      CheckDisc (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree) 0 n) n ∅
        ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run ∧
      ∀ Q, Residual n ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run Q →
        CheckFloor (callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
          (firstChunks settings tree) 0 n) Q := by
    intro i
    rw [initial_program K D A circuits settings top tree x start head rest chunks i, boundary_program]
    have same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
      obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
      rw [hx i, hx (refHolder D K.publicTerm)]
      rfl
    apply first_caller_point circuits settings K D top tree x start.1.2 0 n positive _ (firstCaller start.1.2) i same
    · exact isQueryBoundP_pure _ _ _
    · simpa only [batchStart, List.take_zero, List.map_nil, List.sum_nil, Nat.sub_zero] using horizon
  exact ⟨callerClock_upper circuits settings _ _ 0 n, fun i => (point i).1, fun i => (point i).2⟩

end TreeCheckSigningClock
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningClock.callerClock_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningClock.callerClock_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningClock.caller_batch_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningClock.caller_batch_clock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningClock.caller_batch_end_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningClock.caller_batch_end_floor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningClock.sign_last_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningClock.sign_last_disc

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningClock.sign_caller_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningClock.sign_caller_clock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningClock.initial_program_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningClock.initial_program_clock
