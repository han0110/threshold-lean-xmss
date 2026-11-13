import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestDisc
import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgWindow

/-!
# PRG labels before a first-run checkpoint

The local-pass discipline excludes PRG reads at or above the cutoff, on all
answer paths including aborts. Structural laws port `CheckDisc` with its key
accumulator removed. Timed prefix/check windows give the actual initial
program discipline through the first pass of a first-run batch.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckPrgDisc
open TreeCheckWalkState TreeCheckWalkRecipe TreeCheckPrgWindow TreeSimHashCount
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E α β : Type}

/-- Port of `CheckDisc`: PRG cutoff discipline for the first `n` local passes. -/
inductive PrgDisc (L : ℕ) : ℕ → OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | zero (P) : PrgDisc L 0 P
  | pure (n a) : PrgDisc L n (pure a)
  | queryLocal (n q k) (query : ¬ PrgFrom L q)
      (rest : ∀ r, PrgDisc L (n + 1) (k r)) :
      PrgDisc L (n + 1) (.roll (.inl (.inl q)) k)
  | round (n out k) (rest : ∀ inbox, PrgDisc L n (k inbox)) :
      PrgDisc L (n + 1) (.roll (.inl (.inr out)) k)

theorem prgFrom_antitone {L L' : ℕ} (le : L ≤ L') {q : (LocalSpec C).Domain}
    (h : PrgFrom L' q) : PrgFrom L q := by
  rcases q with noise | (hash | prg)
  · exact h.elim
  · exact h.elim
  · exact le.trans h

theorem party_prg_mono {L L' : ℕ} {p : PartyM C E RealSpec α}
    (le : L ≤ L') (h : PartyBudget (PrgFrom L) p 0) :
    PartyBudget (PrgFrom L') p 0 := by
  apply IsQueryBoundP.of_imp (fun t ht => ?_) h
  rcases t with (q | out) | impossible
  · exact prgFrom_antitone le ht
  · exact ht.elim
  · exact impossible.elim

theorem PrgDisc.mono {L L' n : ℕ}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : PrgDisc L n P)
    (le : L ≤ L') : PrgDisc L' n P := by
  induction h with
  | zero => exact .zero _
  | pure => exact .pure _ _
  | queryLocal n q k query rest ih =>
    exact .queryLocal n q k (fun h => query (prgFrom_antitone le h)) ih
  | round n out k rest ih => exact .round n out k ih

theorem PrgDisc.local_inv {L n : ℕ} {q : (LocalSpec C).Domain}
    {k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgDisc L (n + 1) (.roll (.inl (.inl q)) k)) :
    (¬ PrgFrom L q) ∧ ∀ r, PrgDisc L (n + 1) (k r) := by
  cases h with | queryLocal _ _ _ query rest => exact ⟨query, rest⟩

theorem PrgDisc.round_inv {L n : ℕ} {out : Mail C E}
    {k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgDisc L (n + 1) (.roll (.inl (.inr out)) k)) :
    ∀ inbox, PrgDisc L n (k inbox) := by
  cases h with | round _ _ _ rest => exact rest

/-- Port of `CheckDisc.residual_keys`, without a key accumulator. -/
theorem PrgDisc.residual {L n k : ℕ}
    {P Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgDisc L n P) (r : Residual k P Q) (le : k ≤ n) :
    PrgDisc L (n - k) Q := by
  induction r generalizing n with
  | refl P => simpa using h
  | queryLocal k q cont answer Q r ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ih (h.local_inv.2 answer) le
  | round k out cont inbox Q r ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [Nat.succ_sub_succ_eq_sub] using ih (h.round_inv inbox) (by omega : k ≤ n)
  | done k out => exact .pure _ _

theorem PrgDisc.timed_bind {L m n : ℕ}
    {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed m oa) (h : PrgDisc L m oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none)
    (rest : ∀ a, some a ∈ support oa → PrgDisc L n (f (some a))) :
    PrgDisc L (m + n) (oa >>= f) := by
  induction timed with
  | abort m => rw [pure_bind, abort]; exact .pure _ _
  | done a => rw [pure_bind, Nat.zero_add]; exact rest a (by simp)
  | queryLocal m q k hk ih =>
    rw [Nat.add_right_comm]
    refine .queryLocal _ _ _ h.local_inv.1 fun r => ?_
    rw [Nat.add_right_comm]
    apply ih r (h.local_inv.2 r)
    intro a ha
    apply rest a
    change some a ∈ support (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
    rw [mem_support_bind_iff]
    exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
  | round m out k hk ih =>
    rw [Nat.add_right_comm]
    refine .round _ _ _ fun inbox => ?_
    apply ih inbox (h.round_inv inbox)
    intro a ha
    apply rest a
    change some a ∈ support (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
    rw [mem_support_bind_iff]
    exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩

theorem PrgDisc.antitone {L m n : ℕ}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgDisc L n P) (le : m ≤ n) : PrgDisc L m P := by
  induction h generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact .zero _
  | pure => exact .pure _ _
  | queryLocal n q k query rest ih =>
    cases m with
    | zero => exact .zero _
    | succ m => exact .queryLocal _ _ _ query (fun r => ih r le)
  | round n out k rest ih =>
    cases m with
    | zero => exact .zero _
    | succ m => exact .round _ _ _ (fun r => ih r (by omega))

theorem PrgDisc.of_residual {L m n : ℕ}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : PrgDisc L m P)
    (rest : ∀ Q, Residual m P Q → PrgDisc L n Q) : PrgDisc L (m + n) P := by
  induction P generalizing m with
  | pure a => exact .pure _ _
  | queryBind t k ih =>
    cases m with
    | zero => simpa using rest _ (.refl _)
    | succ m =>
      rw [Nat.add_right_comm]
      rcases t with (q | out) | impossible
      · refine .queryLocal _ _ _ h.local_inv.1 fun r => ?_
        rw [Nat.add_right_comm]
        apply ih r (h.local_inv.2 r)
        intro Q run
        exact rest Q (.queryLocal m q k r Q run)
      · refine .round _ _ _ fun inbox => ?_
        apply ih inbox (h.round_inv inbox)
        intro Q run
        exact rest Q (.round m out k inbox Q run)
      · exact impossible.elim

theorem PrgDisc.timed_party_bind {L m n : ℕ}
    {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (timed : TreeSimCheckTimed m p.run) (h : PrgDisc L m p.run)
    (rest : ∀ a, some a ∈ support p.run → PrgDisc L n (f a).run) :
    PrgDisc L (m + n) (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  exact PrgDisc.timed_bind timed h _ rfl rest

/-- Port of `Disc.of_quiet`. A zero budget covers every answer and abort. -/
theorem PrgDisc.of_quiet {L : ℕ} {p : PartyM C E RealSpec α}
    (h : PartyBudget (PrgFrom L) p 0) : ∀ n, PrgDisc L n p.run := by
  intro n
  unfold PartyBudget at h
  generalize p.run = P at h ⊢
  induction P generalizing n with
  | pure a => exact .pure _ _
  | queryBind t k ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query t) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    have notQuery : ¬ PartyQuery (PrgFrom L) t := by
      intro ht
      simp [ht] at h
    have tail : ∀ r, IsQueryBoundP (k r) (PartyQuery (E := E) (G := RealSpec) (PrgFrom L)) 0 := by
      simpa [notQuery] using h.2
    cases n with
    | zero => exact .zero _
    | succ n =>
      rcases t with (q | out) | impossible
      · exact .queryLocal _ _ _ notQuery (fun r => ih r _ (tail r))
      · exact .round _ _ _ (fun r => ih r _ (tail r))
      · exact impossible.elim

section Gadgets
variable [Field E] [Algebra Bit E]
variable (K : Constants C E)

/-- Port of `CheckDisc.oracle_bind`, with the PRG query predicate. -/
theorem PrgDisc.oracle_bind {L n : ℕ} (p : OracleComp (RoSpec C) α)
    (quiet : IsQueryBoundP p (fun q => PrgFrom L (.inr q)) 0)
    (f : α → PartyM C E RealSpec β)
    (rest : ∀ a, PrgDisc L n (f a).run) :
    PrgDisc L n (oracleStep p >>= f).run := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [oracleStep_pure, pure_bind] using rest a
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have allowed : ¬ PrgFrom L (.inr q) := quiet.1.resolve_right (by omega)
    have tail : ∀ r, IsQueryBoundP (k r) (fun q => PrgFrom L (.inr q)) 0 := by
      simpa only [if_neg allowed] using quiet.2
    rw [oracleStep_bind, bind_assoc]
    cases n with
    | zero => exact .zero _
    | succ n =>
      rcases q with q | q
      all_goals exact .queryLocal n _ _ allowed (fun r => ih r (tail r))

theorem localPrelude_prg (L : ℕ) (gate : OracleComp (LocalSpec C) (Option Unit))
    (quiet : IsQueryBoundP gate (PrgFrom L) 0) :
    PartyBudget (PrgFrom L) (treeLockstepLocalPrelude (E := E) gate) 0 := by
  unfold treeLockstepLocalPrelude
  refine (localStep_bound (E := E) (G := RealSpec) quiet).bind (m := 0) fun out => ?_
  cases out with
  | none => exact party_quiet_of_zero L PartyBound.failure
  | some _ => exact .pure _

open TreeCheckWalkCoverage

theorem openTail_prg (i : C.Party) (count : ℕ) (v : Shares C Bit) (inbox : Mail C E) (L : ℕ) :
    IsQueryBoundP (openTail K i count v inbox) (PrgFrom L) 0 := by
  unfold openTail
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  apply IsQueryBoundP.liftComp_subSpec (p := fun t => PrgFrom (C := C) L (.inr t))
    (fun _ => Iff.rfl)
  unfold treeSimOpenCopyHashes
  simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t)) _ 0 C.terms
    (fun _ _ => hash_zero L _)

set_option backward.isDefEq.respectTransparency false in
-- Port of `CheckDisc.exchange_bind`.
theorem PrgDisc.exchange_bind (L n : ℕ) (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α) (hk : ∀ inbox, PrgDisc L n (k inbox).run) :
    PrgDisc L (n + 1) (exchange out >>= k).run := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>=
        exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk,
      pure_bind, Option.elimM]
    apply bind_congr
    intro inbox
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  apply PrgDisc.round
  intro inbox
  change PrgDisc L n (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact .pure _ _
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

theorem openRep_first_prg (ctx : Context C) (v : Shares C Bit) (count : ℕ)
    (L : ℕ) (k : (ℕ → Bit) → PartyM C E RealSpec α) :
    PrgDisc L 1 (openRep K ctx v count >>= k).run := by
  unfold openRep
  simp only [bind_assoc, pure_bind]
  refine PrgDisc.oracle_bind _ ?_ _ (fun _ => ?_)
  · simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t)) _ 0 C.terms
      (fun _ _ => hash_zero L _)
  · exact PrgDisc.exchange_bind L 0 _ _ (fun _ => .zero _)

end Gadgets

section Batch
open TreeCheckWalkCoverage
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

/-- The first-pass PRG cutoff, before the check starts. -/
def firstLimit (j : ℕ) : ℕ :=
  lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j +
    depth (((firstChunks settings tree).getD j []).map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) + 1

/-- Direct port of `caller_first`, using the first-run PRG prefix window. -/
theorem caller_first_prg (j L : ℕ) (first : j < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom L) 0)
    (bound : firstLimit K D circuits settings tree x j ≤ L) :
    PrgDisc L 1 (callerProgram K D circuits settings top tree x setup j caller i).run := by
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j first,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ caller.encoding j first.le,
    treeSimCheckBatchAudit_run_prefix]
  let ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  let jobs := (firstChunks settings tree).getD j []
  let initial := (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings tree) j, j)
  have timed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs initial)
  have prefixQuiet := batchPrefix_window K circuits settings ctx jobs initial
  have bound' : initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1 ≤ L := by
    simpa only [initial, jobs, ctx, same, firstLimit] using bound
  have firstPass : PrgDisc L 1
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs initial) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs initial data >>=
            callerCont K circuits settings top tree x setup j caller i).run :=
    (PrgDisc.timed_party_bind (n := 0) timed
    (PrgDisc.of_quiet ((localPrelude_prg (E := E) L _ quiet).bind
      (fun _ => by
        apply party_prg_mono bound'
        exact prefixQuiet)) _)
    (fun _ _ => .zero _)).antitone (m := 1) (by omega)
  simpa only [bind_assoc] using firstPass

/-- A complete earlier batch only uses labels below the next batch start. -/
theorem caller_batch_prg (j limit : ℕ) (current : j < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) (PrgFrom limit) 0)
    (bound : lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) (j + 1) ≤ limit) :
    PrgDisc limit (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j []))
      (callerProgram K D circuits settings top tree x setup j caller i).run := by
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j current,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ caller.encoding j current.le,
    treeSimCheckBatchAudit_run_prefix]
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
            callerCont K circuits settings top tree x setup j caller i) by simp only [bind_assoc]]
  have prefixTimed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
  have prefixQuiet := (localPrelude_prg (E := E) limit _ quiet).bind
    (fun _ => party_prg_mono (by
      rw [lockstepStart_succ circuits _ _ j current] at bound
      unfold batchLabels at bound
      simpa only [start, jobs, parameter, Prod.fst] using
        (show lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
          (firstChunks settings tree) j +
          depth (((firstChunks settings tree).getD j []).map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) + 1 ≤ limit by omega))
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
  have checkDisc := check_window K ctx data.2.1.2 data.2.2 limit (by
    rw [hcount, hlabel]
    rw [lockstepStart_succ circuits _ _ j current] at bound
    unfold batchLabels at bound
    simpa only [start, jobs, Nat.add_assoc, Prod.fst] using bound)
  rw [hcount] at checkTimed
  apply PrgDisc.timed_party_bind checkTimed
  · simpa only [hcount] using PrgDisc.of_quiet checkDisc (checkLabels (data.2.1.2.map (·.count)).sum)
  · intro checked _
    exact openRep_first_prg K ctx _ _ limit _


set_option maxHeartbeats 1000000 in
/-- Port of `residual_batch_quiet`: retain the literal opening tail and its
PRG quietness at every cutoff, including all abort disjuncts. -/
theorem residual_batch_prg (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      (∀ L, IsQueryBoundP (caller'.tail i) (PrgFrom L) 0) ∧
      Q = (callerProgram K D circuits settings top tree x setup (j + 1) caller' i).run := by
  have current : j < (firstChunks settings tree).length := by omega
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
  rw [callerCont_step K circuits settings top tree x setup j next caller i _ (openTail K ctx.self
      (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length data.2.1.1 inbox)]
  set count := (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length
  set value := assemble (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs) fun g =>
    ∑ T, treeSimOpenCopy K ctx.self count data.2.1.1 inbox T g
  refine ⟨stepCaller caller i (some value, [⟨ctx, jobs, (start, j), data.1, data.2.1.2, data.2.2, value,
    checked.2⟩]) (openTail K ctx.self count data.2.1.1 inbox), rfl, by simp [stepCaller],
    by simp [stepCaller], openTail_prg K ctx.self count data.2.1.1 inbox, ?_⟩
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree _ (j + 1) next,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ _ (j + 1) next.le]
  simp only [stepCaller, labels]


/-- Port of `caller_window`, using PRG windows through complete earlier
batches and the first pass of batch `j`. -/
theorem caller_window_prg (b j : ℕ) (first : j < (firstChunks settings tree).length) (le : b ≤ j)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : ∀ L, IsQueryBoundP (caller.tail i) (PrgFrom L) 0) :
    PrgDisc (firstLimit K D circuits settings tree x j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter b + 1)
      (callerProgram K D circuits settings top tree x setup b caller i).run := by
  by_cases equal : b = j
  · subst b
    simpa only [Nat.sub_self, Nat.zero_add] using
      caller_first_prg K D circuits settings top tree x setup j _ first caller i same (quiet _) le_rfl
  · have current : b < (firstChunks settings tree).length := by omega
    have next : b + 1 < (firstChunks settings tree).length := by omega
    have before : b + 1 ≤ j := by omega
    have disc := caller_batch_prg K D circuits settings top tree x setup b
      (firstLimit K D circuits settings tree x j) current caller i same (quiet _)
      ((lockstepStart_mono circuits _ _ before).trans (by unfold firstLimit; omega))
    have order := TreeCheckHonestDisc.batchStart_mono circuits settings tree
      (x (refHolder D K.publicTerm)).parameter before
    have succ := TreeCheckHonestDisc.batchStart_succ circuits settings tree (x (refHolder D K.publicTerm)).parameter b current
    rw [show batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter b + 1 =
      batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
        ((firstChunks settings tree).getD b []) +
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (b + 1) + 1) by omega]
    apply disc.of_residual
    intro Q run
    rcases residual_batch_prg K D circuits settings top tree x setup b next caller i same run with
      aborted | ⟨caller', _, _, _, quiet', rfl⟩
    · rw [aborted]
      exact .pure _ _
    · simpa only [ite_self] using
        caller_window_prg (b + 1) j first before caller' i same quiet'
termination_by j - b

/-- Initial-caller form, with the actual tail condition kept explicit. -/
theorem caller_initial_prgDisc (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : ∀ L, IsQueryBoundP (caller.tail i) (PrgFrom L) 0)
    (j : ℕ) (first : j < (firstChunks settings tree).length) :
    PrgDisc (firstLimit K D circuits settings tree x j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j + 1)
      (callerProgram K D circuits settings top tree x setup 0 caller i).run := by
  simpa only [batchStart, List.take_zero, List.map_nil, List.sum_nil, Nat.sub_zero] using
    caller_window_prg K D circuits settings top tree x setup 0 j first (Nat.zero_le _) caller i same quiet

/-- The actual first caller satisfies the discipline through the first pass
of every first-run checkpoint. Setup rejection remains in the literal tail. -/
theorem initial_prgDisc (dealt : DealtInputs D x) (i : C.Party)
    (j : ℕ) (first : j < (firstChunks settings tree).length) :
    PrgDisc (firstLimit K D circuits settings tree x j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j + 1)
      (callerProgram K D circuits settings top tree x setup 0 (firstCaller setup) i).run := by
  apply caller_initial_prgDisc K D circuits settings top tree x setup _ i _ _ j first
  · obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  · intro L
    exact isQueryBoundP_pure _ _ _

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- The same certificate on the scheduler's actual initial program. -/
theorem initial_program_prgDisc
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (i : C.Party) (j : ℕ)
    (first : j < (firstChunks settings tree).length) :
    PrgDisc (firstLimit K D circuits settings tree x j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j + 1)
      ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run := by
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos (by omega : 0 < (firstChunks settings tree).length))
  rw [initial_program K D A circuits settings top tree x start head rest chunked i, boundary_program]
  exact initial_prgDisc K D circuits settings top tree x start.1.2 dealt i j first

end Batch

end TreeCheckPrgDisc
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgDisc.PrgDisc.residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgDisc.PrgDisc.residual

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgDisc.caller_batch_prg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgDisc.caller_batch_prg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgDisc.residual_batch_prg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgDisc.residual_batch_prg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgDisc.initial_program_prgDisc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgDisc.initial_program_prgDisc
