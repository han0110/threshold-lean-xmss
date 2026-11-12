import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkEntry
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkOpenings
import ThresholdLeanXmssSecurity.Proof.TreeLockstepLateBottom
import ThresholdLeanXmssSecurity.Proof.TreeSetupKeys

/-!
# The first-run opening window

`firstRunOpening` proves `FirstRunOpening` for the unchanged source family.
Every honest copy-digest list is logged and every nonaborted program has the
literal pending `openTail` and inbox form. Only held-copy and earlier-output
agreement require the original clean/live guard.

The unconditional branch stops the existing residual proof before its last
opening exchange. The guarded branch retains the same joint snapshot and
uses `treeLockstep_batches_next` and `treeLockstep_batch_checked_held` on its
actual prefix data. Zero-count checks are pure. The final hash pass retains
the actual checked state, record constructor, and saved outputs; the pending
copy checks are never executed to establish this window.

Timing and abort-persistence ports come from `TreeCheckWalkEntry`,
`TreeCheckWalkState`, `TreeSimCheck`, and `TreeLockstepOpenedFinal`. The
snapshot equations come from `TreeLockstepLateBottom`. No residual premise
is added to the original invariant.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkFirstOpening
open TreeCheckWalkRecipe TreeCheckWalkCoverage TreeCheckWalkState TreeCheckWalkEntry
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

set_option maxHeartbeats 1000000 in
/-- The port of `residual_batch_cont` stopping before the opening exchange. -/
theorem residual_batch_send (j : ℕ) (current : j < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual
      ((depth (((firstChunks settings tree).getD j []).map
        (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) +
        checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter
          ((firstChunks settings tree).getD j [])))
      (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (v : Shares C Bit)
      (record : (ℕ → Bit) → TreeSimCheckBatchRecord C),
      Q = (openRep K ⟨i, x i, setupKeys setup i⟩ v
        (outputsOf (((firstChunks settings tree).getD j []).map
          (circuits (x (refHolder D K.publicTerm)).parameter ·.kind))).length >>= fun out =>
        callerCont K circuits settings top tree x setup j caller i
          ((some (assemble (((firstChunks settings tree).getD j []).map
            (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) out), [record out]),
            (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
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
  rcases Residual.party_bind (N := 0) checkTimed (by simpa only [Nat.add_zero] using h) with none | ⟨checked, hchecked, h⟩
  · exact .inl none
  have finalLabel := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 hchecked
  rw [hcount, hlabel] at finalLabel
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  have program := h.zero_inv
  rw [labels] at program
  refine .inr ⟨data.2.1.1, ?_, ?_⟩
  · exact fun out => ⟨ctx, jobs, (start, j), data.1, data.2.1.2,
      data.2.2, assemble (jobs.map (circuits ctx.keys.parameter ·.kind)) out, checked.2⟩
  · simpa only [parameter] using program

def sendRounds (parameter : PublicParameter) (jobs : List Job) : ℕ :=
  depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 +
    checkLabels (batchCount circuits parameter jobs)

def sendCont (j : ℕ) (i : C.Party) (W : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) (record : (ℕ → Bit) → TreeSimCheckBatchRecord C)
    (out : ℕ → Bit) : PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)) :=
  treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
    ((some (W ++ assemble (((firstChunks settings tree).getD j []).map
      (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) out), records ++ [record out]),
      signingInitial K D circuits settings tree x)

/-- Last-batch specialization retaining the actual record constructor. -/
theorem residual_last_send (j : ℕ) (last : j + 1 = (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (sendRounds circuits settings (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j []))
      (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (v : Shares C Bit) (W : List (List Bit))
      (record : (ℕ → Bit) → TreeSimCheckBatchRecord C),
      Q = (openRep K ⟨i, x i, setupKeys setup i⟩ v
        (outputsOf (((firstChunks settings tree).getD j []).map
          (circuits (x (refHolder D K.publicTerm)).parameter ·.kind))).length >>=
          sendCont K D circuits settings top tree x setup j i W (caller.records i) record).run := by
  have current : j < (firstChunks settings tree).length := by omega
  rcases residual_batch_send K D circuits settings top tree x setup j current caller i same h with
    none | ⟨v, record, program⟩
  · exact .inl none
  obtain ⟨values, saved⟩ := outputs
  refine .inr ⟨v, values.flatten, record, ?_⟩
  rw [program]
  congr 1
  apply bind_congr
  intro out
  have empty : (firstChunks settings tree).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
  unfold callerCont sendCont
  simp only [phaseChunks, phaseIndex, if_pos current, empty, List.mapM_nil, saved]
  simp [foldlM_some, signingInitial, last]

/-- Every honest raw program before the last opening is dead or is the
opening itself, with its own saved outputs and records. -/
theorem pending_send (prims : Primitives) (positive : 0 < settings.batchSize)
    (b : Fin (2 ^ layerHeight)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (same : ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (j : ℕ) (last : j + 1 = (firstChunks settings (.bottom b)).length)
    (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter j +
        sendRounds circuits settings (x (refHolder D K.publicTerm)).parameter
          ((firstChunks settings (.bottom b)).getD j [])) q)
    (i : C.Party) (hi : i ∉ D.1) :
    (q.program i).run = pure none ∨ ∃ (v : Shares C Bit) (W : List (List Bit))
      (records : List (TreeSimCheckBatchRecord C))
      (record : (ℕ → Bit) → TreeSimCheckBatchRecord C),
      records.length = j ∧
      q.program i = (openRep K ⟨i, x i, setupKeys p.1.2 i⟩ v
        (outputsOf (((firstChunks settings (.bottom b)).getD j []).map
          (circuits (x (refHolder D K.publicTerm)).parameter ·.kind))).length >>=
          sendCont K D circuits settings top (.bottom b) x p.1.2 j i W records record) := by
  have pos := firstChunks_bottom_pos settings positive b
  have current : j < (firstChunks settings (.bottom b)).length := by omega
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos pos)
  have residual := reached.residual prims D Z i hi
  rw [initial_program K D A circuits settings top (.bottom b) x p head rest chunked i,
    boundary_program] at residual
  obtain ⟨M, first, second⟩ := residual.split
  rcases residual_first_some K D circuits settings top (.bottom b) x p.1.2 (firstCaller p.1.2) i (same i)
      ⟨[], rfl⟩ j current first with rfl | ⟨middle, records, outputs, rfl⟩
  · exact .inl second.pure_inv
  rcases residual_last_send K D circuits settings top (.bottom b) x p.1.2 j last middle i
      (same i) outputs second with none | ⟨v, W, record, program⟩
  · exact .inl none
  refine .inr ⟨v, W, middle.records i, record, ?_, OptionT.ext program⟩
  simpa only [firstCaller, List.length_nil, Nat.zero_add] using records

/-- The original three clauses: only held shares and earlier-output
agreement have the clean/live guard. -/
def OpeningWindow (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (q : TreeCheckWalkDef.Pending A) : Prop :=
  ∃ (count : ℕ) (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (inbox : C.Party → Mail C E) (W : C.Party → List (List Bit))
    (recs : C.Party → List (TreeSimCheckBatchRecord C)),
    (∀ h, h ∉ D.1 → (ds h).length = C.terms.length ∧
      ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer q.world.2 (.copy (vector count (v h T))) u) ∧
    (∀ i, i ∉ D.1 → (recs i).length = (firstChunks settings (.bottom b)).length ∧
      ((q.program i).run = pure none ∨
        anyAbort (inbox i) = false ∧
        (∀ h, h ∉ D.1 → inbox i h = repOutbox K h (v h) count (ds h) i) ∧
        q.program i = treeLockstepLocalPrelude (openTail K i count (v i) (inbox i)) >>= fun _ =>
          treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top (.bottom b)
            ((some (W i ++ assemble
              (((firstChunks settings (.bottom b)).getD ((firstChunks settings (.bottom b)).length - 1) []).map
                (circuits (x (refHolder D K.publicTerm)).parameter ·.kind))
              (fun g => ∑ T, treeSimOpenCopy K i count (v i) (inbox i) T g)), recs i),
              signingInitial K D circuits settings (.bottom b) x))) ∧
    ((¬ TreeSimHashBudgetCollision q.world.2 ∧
        ∃ i, i ∉ D.1 ∧ (q.program i).run ≠ pure none) →
      (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < count →
        v i T g = v (refHolder D T) T g) ∧
      ∀ i k, i ∉ D.1 → k ∉ D.1 → (q.program i).run ≠ pure none →
        (q.program k).run ≠ pure none → W i = W k)

def FirstRunOpening (prims : Primitives) : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput),
      DealtInputs D x → ∀ p ∈ support (treeSaltSetup prims D A x z),
      ∀ q, Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
        (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
          (firstChunks settings (.bottom b)).length) q →
        OpeningWindow K D circuits settings top x p.1.2 A b q

/-- The initial hash pass with both abort flags and retained continuations.
Port of `treeLockstep_open_start` and `treeLockstep_open_start_cont`. -/
theorem open_start_live {α : Type} (live : C.Party → Bool) (count : ℕ)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (v : C.Party → Shares C Bit) (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α) :
    startSteps worldRoles D (fun i => if live i then openRep K (ctx i) (v i) count >>= k i else failure) =
      (do let ds ← free (treeLockstepOpenHashes D live count v)
          pure (treeSimOpenPartial K D live count v ds k)) := by
  unfold startSteps treeLockstepOpenHashes
  rw [free_sequenceFin]
  have one : ∀ i : C.Party,
      (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest
        (advance ((if live i then openRep K (ctx i) (v i) count >>= k i else failure).run))) =
      (do let ds ← free (if i ∉ D.1 ∧ live i = true then
            liftComp (treeSimOpenCopyHashes count (v i)) (LocalSpec C) else pure [])
          pure (if i ∈ D.1 then .done none else if live i then
            treeSimOpenStep K i count (v i) ds (k i) else .done none)) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_true, not_true_eq_false, false_and, if_false, free_pure, pure_bind]
    · by_cases hl : live i = true
      · simp only [hi, hl, if_false, if_true, not_false_eq_true, true_and]
        simpa only [self i, map_eq_bind_pure_comp, Function.comp_def] using
          treeSim_open_entry K (ctx i) count (v i) (k i)
      · simp only [hi, hl, if_false, not_false_eq_true, true_and]
        simp [worldRoles, advance_pure, free_pure]
  simp_rw [one]
  rw [sequenceFin_bind_pure]
  rfl

/-- Raw delivery preserves the pending opening tail and forces all honest
senders live whenever the recipient does not immediately abort. -/
theorem resume_open (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)))
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) :
    let resumed := TreeCheckWalkDef.resume D (treeSimOpenPartial K D live count v ds k) sent i
    let inbox := treeSimOpenInbox K D live count v ds sent i
    resumed.run = pure none ∨
      (∀ h, h ∉ D.1 → live h = true) ∧ anyAbort inbox = false ∧
      (∀ h, h ∉ D.1 → inbox h = repOutbox K h (v h) count (ds h) i) ∧
      resumed = treeLockstepLocalPrelude (openTail K i count (v i) inbox) >>= fun _ =>
        k i (fun g => ∑ T, treeSimOpenCopy K i count (v i) inbox T g) := by
  dsimp only
  have inbox : (fun j => if j ∈ D.1 then sent j i else
      (treeSimOpenPartial K D live count v ds k j).delivered i) =
      treeSimOpenInbox K D live count v ds sent i := by
    funext j
    by_cases hj : j ∈ D.1 <;> by_cases hl : live j = true <;>
      simp [treeSimOpenPartial, treeSimOpenStep, treeSimOpenInbox, Step.delivered, hj, hl]
  by_cases hl : live i = true
  · have raw : TreeCheckWalkDef.resume D (treeSimOpenPartial K D live count v ds k) sent i =
        OptionT.mk (exchangeResume (fun inbox => do
          let copy := treeSimOpenCopy K i count (v i) inbox
          let hashes ← oracleStep (treeSimOpenCopyHashes count copy)
          require (TreeSimOpenValid K i inbox hashes)
          k i (fun g => ∑ T, copy T g)) (treeSimOpenInbox K D live count v ds sent i)) := by
      unfold TreeCheckWalkDef.resume
      rw [show treeSimOpenPartial K D live count v ds k i = treeSimOpenStep K i count (v i) (ds i) (k i) by
        simp [treeSimOpenPartial, hi, hl]]
      simp only [treeSimOpenStep, if_neg hi, inbox]
    rw [raw]
    by_cases ha : anyAbort (treeSimOpenInbox K D live count v ds sent i) = true
    · exact .inl (by
        change (C.parties.any fun h => Msg.isAbort (treeSimOpenInbox K D live count v ds sent i h)) = true at ha
        simp only [OptionT.run_mk, exchangeResume, ha, if_true])
    · have all : ∀ h, h ∉ D.1 → live h = true := by
        intro h hh
        by_contra hn
        apply ha
        apply List.any_eq_true.mpr
        exact ⟨h, List.mem_finRange h, by simp [treeSimOpenInbox, hh, hn, Msg.isAbort]⟩
      refine .inr ⟨all, Bool.eq_false_iff.mpr ha, ?_, ?_⟩
      · intro h hh
        simp [treeSimOpenInbox, hh, all h hh, repOutbox, treeSimOpenOut]
      · apply OptionT.ext
        simp only [OptionT.run_mk, exchangeResume, show
          (C.parties.any fun h => Msg.isAbort (treeSimOpenInbox K D live count v ds sent i h)) = false
            from Bool.eq_false_iff.mpr ha, Bool.false_eq_true, if_false]
        exact congrArg OptionT.run (openResume_tail K i count (v i) _ (k i))
  · exact .inl (by simp [TreeCheckWalkDef.resume, treeSimOpenPartial, hi, hl])

/-- Invert the actual final round, retaining its local pass and reply. -/
theorem reached_last (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (initial : TreeCheckWalkDef.Pending A)
    (n : ℕ) (q : TreeCheckWalkDef.Pending A) (h : Reached prims D Z initial (n + 1) q) :
    ∃ (p : TreeCheckWalkDef.Pending A) (fuel : ℕ)
      (started : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
      (reply : (A.State × (C.Party → Mail C E)) × TreeSimState C),
      Reached prims D Z initial n p ∧ p.fuel = fuel + 1 ∧
      started ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D p.program)).run p.world) ∧
      (¬ ∀ i, i ∉ D.1 → (started.1 i).isDone) ∧
      reply ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (A.round p.state fun c i =>
          if c ∈ D.1 ∧ i ∉ D.1 then (started.1 i).outbox c else none))).run started.2) ∧
      q = ⟨reply.1.1, TreeCheckWalkDef.resume D started.1 reply.1.2, fuel, reply.2⟩ ∧
      started.2.2 <+: q.world.2 := by
  cases h with
  | next reached fuelLeft run =>
    unfold TreeCheckWalkDef.next at run
    simp only [mem_support_bind_iff] at run
    obtain ⟨started, hs, run⟩ := run
    split_ifs at run with stopped
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at run
      obtain ⟨observed, _, impossible⟩ := run
      cases impossible
    · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at run
      obtain ⟨reply, hr, rfl⟩ := run
      exact ⟨_, _, started, reply, reached, fuelLeft, hs, stopped, hr, rfl,
        treeSimLoggedWorld_prefix prims D _ _ _ hr⟩

/-- Equality of the honest starting programs is enough for the driver. -/
theorem start_congr {α : Type} (p q : C.Party → PartyM C E RealSpec α)
    (same : ∀ i, i ∉ D.1 → p i = q i) :
    startSteps worldRoles D p = startSteps worldRoles D q := by
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
  · simp only [if_neg hi, same i hi]

/-- The actual last-batch pre-opening programs have one common output width. -/
def width (j : ℕ) : ℕ := (outputsOf (((firstChunks settings tree).getD j []).map
  (circuits (x (refHolder D K.publicTerm)).parameter ·.kind))).length

/-- The fields retained in an opening continuation. -/
structure SendFields (C : Committee) where
  shares : C.Party → Shares C Bit
  saved : C.Party → List (List Bit)
  records : C.Party → List (TreeSimCheckBatchRecord C)
  record : C.Party → (ℕ → Bit) → TreeSimCheckBatchRecord C

def fieldsCont (j : ℕ) (f : SendFields C) :
    C.Party → (ℕ → Bit) → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)) :=
  fun i => sendCont K D circuits settings top tree x setup j i (f.saved i) (f.records i) (f.record i)

/-- Reassemble the separate residuals only for their literal local programs;
this makes no agreement assertion. -/
theorem pending_fields (prims : Primitives) (positive : 0 < settings.batchSize)
    (b : Fin (2 ^ layerHeight)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (same : ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (j : ℕ) (last : j + 1 = (firstChunks settings (.bottom b)).length)
    (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter j +
        sendRounds circuits settings (x (refHolder D K.publicTerm)).parameter
          ((firstChunks settings (.bottom b)).getD j [])) q) :
    ∃ (live : C.Party → Bool) (f : SendFields C),
      (∀ i, (f.records i).length = j) ∧
      ∀ i, i ∉ D.1 → q.program i =
        if live i then openRep K ⟨i, x i, setupKeys p.1.2 i⟩ (f.shares i)
          (width K D circuits settings (.bottom b) x j) >>=
            fieldsCont K D circuits settings top (.bottom b) x p.1.2 j f i else failure := by
  let dummy (i : C.Party) : TreeSimCheckBatchRecord C :=
    ⟨⟨i, x i, setupKeys p.1.2 i⟩, [], (0, 0), [], [], ⟨fun _ => [], 0, 0⟩, [], ⟨fun _ => [], 0, 0⟩⟩
  have each (i) : ∃ (live : Bool) (v : Shares C Bit) (W : List (List Bit))
      (rs : List (TreeSimCheckBatchRecord C)) (rec : (ℕ → Bit) → TreeSimCheckBatchRecord C),
      rs.length = j ∧ (i ∉ D.1 → q.program i = if live then
        openRep K ⟨i, x i, setupKeys p.1.2 i⟩ v (width K D circuits settings (.bottom b) x j) >>=
          sendCont K D circuits settings top (.bottom b) x p.1.2 j i W rs rec else failure) := by
    by_cases hi : i ∈ D.1
    · exact ⟨false, fun _ _ => 0, [], List.replicate j (dummy i), fun _ => dummy i,
        List.length_replicate, fun h => (h hi).elim⟩
    rcases pending_send K D circuits settings top x prims positive b A Z p same j last q reached i hi with
      none | ⟨v, W, rs, rec, len, eq⟩
    · refine ⟨false, fun _ _ => 0, [], List.replicate j (dummy i), fun _ => dummy i,
        List.length_replicate, fun _ => ?_⟩
      exact OptionT.ext none
    · exact ⟨true, v, W, rs, rec, len, fun _ => eq⟩
  choose live v W rs rec len eq using each
  exact ⟨live, ⟨v, W, rs, rec⟩, len, eq⟩

def Guard (A : Adversary C E (Keys C) PEmpty PEmpty) (q : TreeCheckWalkDef.Pending A) : Prop :=
  ¬ TreeSimHashBudgetCollision q.world.2 ∧ ∃ i, i ∉ D.1 ∧ (q.program i).run ≠ pure none

/-- Assemble the original window from a retained send and the actual reply.
Dead honest rows reuse a live sender's party-independent copy queries. -/
theorem window_of_send (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (j : ℕ) (last : j + 1 = (firstChunks settings (.bottom b)).length)
    (q : TreeCheckWalkDef.Pending A) (live : C.Party → Bool) (f : SendFields C)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (program : q.program = TreeCheckWalkDef.resume D
      (treeSimOpenPartial K D live (width K D circuits settings (.bottom b) x j) f.shares ds
        (fieldsCont K D circuits settings top (.bottom b) x setup j f)) sent)
    (existsLive : ∃ i, i ∉ D.1 ∧ live i = true)
    (lengths : ∀ i, (f.records i).length = j)
    (logged : ∀ i, i ∉ D.1 → live i = true → (ds i).length = C.terms.length ∧
      ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧ TreeSimHashAnswer q.world.2
        (.copy (vector (width K D circuits settings (.bottom b) x j) (f.shares i T))) u)
    (agreement : Guard D A q →
      (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < width K D circuits settings (.bottom b) x j →
        f.shares i T g = f.shares (refHolder D T) T g) ∧
      ∀ i k, i ∉ D.1 → k ∉ D.1 → (q.program i).run ≠ pure none →
        (q.program k).run ≠ pure none → f.saved i = f.saved k) :
    OpeningWindow K D circuits settings top x setup A b q := by
  obtain ⟨i₀, honest₀, live₀⟩ := existsLive
  let count := width K D circuits settings (.bottom b) x j
  let v := fun i => if i ∉ D.1 ∧ live i ≠ true then f.shares i₀ else f.shares i
  let hashes := fun i => if i ∉ D.1 ∧ live i ≠ true then ds i₀ else ds i
  let inbox := fun i => treeSimOpenInbox K D (fun _ => true) count v hashes sent i
  let out := fun i g => ∑ T, treeSimOpenCopy K i count (v i) (inbox i) T g
  let records := fun i => f.records i ++ [f.record i (out i)]
  have filled (all : ∀ i, i ∉ D.1 → live i = true) : v = f.shares ∧ hashes = ds := by
    constructor <;> funext i <;> dsimp only [v, hashes] <;>
      rw [if_neg (fun h => h.2 (all i h.1))]
  have mail (all : ∀ i, i ∉ D.1 → live i = true) (i) :
      inbox i = treeSimOpenInbox K D live count f.shares ds sent i := by
    rw [show inbox i = treeSimOpenInbox K D (fun _ => true) count v hashes sent i from rfl,
      (filled all).1, (filled all).2]
    funext h
    by_cases hh : h ∈ D.1
    · simp [treeSimOpenInbox, hh]
    · simp [treeSimOpenInbox, hh, all h hh]
  have resume (i) (hi : i ∉ D.1) := resume_open K D live count f.shares ds
    (fieldsCont K D circuits settings top (.bottom b) x setup j f) sent i hi
  have all_of_live (hg : Guard D A q) : ∀ i, i ∉ D.1 → live i = true := by
    obtain ⟨i, hi, hn⟩ := hg.2
    rcases resume i hi with dead | ⟨all, rest⟩
    · exact False.elim (hn (by simpa only [program] using dead))
    · exact all
  refine ⟨count, v, hashes, inbox, f.saved, records, ?_, ?_, ?_⟩
  · intro h hh
    by_cases hl : live h = true
    · simpa only [hashes, v, hl, ne_eq, not_true_eq_false, and_false, if_false] using logged h hh hl
    · simpa only [hashes, v, if_pos (And.intro hh hl)] using logged i₀ honest₀ live₀
  · intro i hi
    refine ⟨by simp only [records, List.length_append, List.length_singleton, lengths, last], ?_⟩
    rcases resume i hi with dead | ⟨all, noabort, honest, shape⟩
    · exact .inl (by simpa only [program] using dead)
    · refine .inr ⟨?_, ?_, ?_⟩
      · simpa only [mail all i] using noabort
      · intro h hh
        rw [mail all i, (filled all).1, (filled all).2]
        exact honest h hh
      · rw [program, shape]
        have jj : j = (firstChunks settings (.bottom b)).length - 1 := by omega
        simp only [mail all i, (filled all).1, fieldsCont, sendCont, records, out, jj]
  · intro hg
    obtain ⟨held, common⟩ := agreement hg
    have all := all_of_live hg
    rw [(filled all).1]
    exact ⟨held, common⟩

/-- Exact exchange timing supplies the snapshot segment premise. -/
theorem segment_of_timed {α : Type} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSimCheckTimed n p) (j : ℕ) :
    TreeSegmentRun (fun _ _ _ _ => True) j (j + n) p := by
  induction h generalizing j with
  | abort n => exact .abort _ _
  | done a => simpa using TreeSegmentRun.done (S := fun _ _ _ _ => True) j a
  | queryLocal n q k h ih => exact .queryLocal _ _ _ _ (by intros; unfold SaltRead; intros; trivial) (fun r => ih r j)
  | round n out k h ih =>
    apply TreeSegmentRun.round
    intro r
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih r (j + 1)

/-- Timed prefixes move through snapshots without changing local query order. -/
theorem snapshot_timed {α β : Type} {n : ℕ} {p : PartyM C E RealSpec α}
    (h : TreeSimCheckTimed n p.run) (fuel : ℕ) (k : α → PartyM C E RealSpec β) :
    treeLateSnapshot (n + fuel) (p >>= k) = p >>= fun a => treeLateSnapshot fuel (k a) :=
  treeLateSnapshot_bind (TreeTwinWithin.of_timed h) 0 (by simpa using segment_of_timed h 0) fuel k

-- The following persistence ports are from TreeSimCheck.lean:846–881.
private theorem step_done {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (r : A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E))
    (h : r ∈ support (stepRound worldRoles D A noFunctionality state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : r.2.1 i = .done a := by
  rw [stepRound_real] at h
  simp only [mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨p, _, next, hn, rfl⟩ := h
  have hh := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hn) i
  simpa only [roundLocal, hi, support_pure, Set.mem_singleton_iff] using hh

private theorem rounds_done {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (out : A.State × (C.Party → Option α))
    (h : out ∈ support (executeRounds worldRoles D A noFunctionality fuel state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : out.2 i = a := by
  induction fuel generalizing state steps out with
  | zero =>
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at h
    subst out
    exact congrArg Step.output hi
  | succ fuel ih =>
    simp only [executeRounds] at h
    split_ifs at h with hd
    · cases h
      exact congrArg Step.output hi
    · simp only [mem_support_bind_iff] at h
      obtain ⟨r, hr, ho⟩ := h
      exact ih r.1 r.2.1 out ho (step_done D A state steps r hr i a hi)

private theorem batch_resume {α β : Type}
    (k : C.Party → β → PartyM C E RealSpec α) (out : C.Party → Option β) (data : C.Party → β)
    (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (honest : ∀ i, i ∉ D.1 → out i = some (data i)) :
    free (Concrete.sequenceFin fun i => continueStep (k i) (.done (out i))) =
      startSteps worldRoles D (fun i => k i (data i)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, continueStep, free_pure]
  · simp [hi, honest i hi, continueStep, worldRoles]

/-- A joint split selected by all retained nonempty outputs, without an
extra exchange premise on the continuation. -/
theorem timed_boundary_live (prims : Primitives) {α β : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec β) (k : C.Party → β → PartyM C E RealSpec α) (fallback : β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (n + 1 + fuel) state (fun i => p i >>= k i))).run s))
    (live : ∀ i, i ∉ D.1 → (r.1.2 i).isSome) :
    ∃ (pref : (A.State × (C.Party → Option β)) × TreeSimState C) (data : C.Party → β),
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (n + 1) state p)).run s) ∧
      (∀ i, i ∉ D.1 → pref.1.2 i = some (data i)) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel pref.1.1 (fun i => k i (data i)))).run pref.2) := by
  rw [treeSimCheckTimed_phase_split D A n fuel state p k timed] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨pref, hpref, next, hnext, htail⟩ := run
  have hn := treeCheck_logged_support prims D _ _ hnext
  have ht := treeCheck_logged_support prims D _ _ htail
  have present (i) (hi : i ∉ D.1) : (pref.1.2 i).isSome := by
    cases he : pref.1.2 i with
    | some a => rfl
    | none =>
      have one := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hn) i
      have dead : next.1 i = .done none := by
        simpa only [he, continueStep, support_pure, Set.mem_singleton_iff] using one
      have final := rounds_done D A fuel pref.1.1 next.1 r.1 ht i none dead
      have hl := live i hi
      simp only [final, Option.isSome_none, Bool.false_eq_true] at hl
  let data := fun i => (pref.1.2 i).getD fallback
  have selected (i : C.Party) (hi : i ∉ D.1) : pref.1.2 i = some (data i) := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (present i hi)
    simp only [data, hv, Option.getD_some]
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A _ state p s pref
    (by simpa only [simulateQ_executePhase] using hpref)
  refine ⟨pref, data, hpref, selected, ?_⟩
  unfold executePhase
  rw [← batch_resume D k pref.1.2 data corrupt selected]
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨next, hnext, htail⟩

abbrev BatchData (C : Committee) := List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C
abbrev AuditOut (C : Committee) := (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)

/-- The count and label facts are restricted to supported prefix data. -/
theorem prefix_facts (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) (data : BatchData C)
    (h : some data ∈ support (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run) :
    (data.2.1.2.map (·.count)).sum = tupleCount (jobs.map (circuits ctx.keys.parameter ·.kind)) ∧
    data.2.2.label = initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1 := by
  have label := (treeSimCheckBatchPrefix_state K circuits settings ctx jobs initial data h).2.1
  refine ⟨?_, label⟩
  unfold treeSimCheckBatchPrefix at h
  obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨q, hq, he⟩ := treeSimCheck_some_bind _ _ _ hrest
  have eq : data = (inputs, q) := by
    simpa only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] using he
  subst data
  exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs initial.1 initial.2 q.1 q.2 hq

/-- Support-aware congruence for option-valued party programs. -/
theorem party_bind_congr {α β : Type} (p : PartyM C E RealSpec α)
    (f g : α → PartyM C E RealSpec β)
    (h : ∀ a, some a ∈ support p.run → f a = g a) : p >>= f = p >>= g := by
  apply OptionT.ext
  simp only [OptionT.run_bind, Option.elimM]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro a ha
  cases a with
  | none => rfl
  | some a => exact congrArg OptionT.run (h a ha)

/-- Snapshot the last audit precisely at its opening send. -/
theorem snapshot_audit_send {α : Type} (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (k : AuditOut C → PartyM C E RealSpec α) :
    treeLateSnapshot (sendRounds circuits settings ctx.keys.parameter jobs)
      ((treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial >>= k) =
    treeSimCheckBatchPrefix K circuits settings ctx jobs initial >>= fun data =>
      (check K ctx (realCheckGadgets K ctx) data.2.1.2).run data.2.2 >>= fun checked =>
        treeLateSnapshot 0 (treeLockstepBatchCheckCont K circuits ctx jobs initial data k checked) := by
  rw [treeSimCheckBatchAudit_run_prefix, bind_assoc]
  rw [show sendRounds circuits settings ctx.keys.parameter jobs =
    (depth (jobs.map (circuits ctx.keys.parameter ·.kind)) * settings.mode.rounds + 1) +
      checkLabels (tupleCount (jobs.map (circuits ctx.keys.parameter ·.kind))) from rfl,
    snapshot_timed (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs initial)]
  apply party_bind_congr
  intro data hd
  rw [treeLockstep_batchFinish_check]
  have count := (prefix_facts K circuits settings ctx jobs initial data hd).1
  have timed := check_timed K ctx data.2.1.2 data.2.2
  rw [count] at timed
  simpa only [Nat.add_zero] using snapshot_timed timed 0
    (treeLockstepBatchCheckCont K circuits ctx jobs initial data k)

/-- A zero-exchange snapshot of the opening performs exactly its own-copy
hash pass and retains the waiting step, including its continuation. -/
theorem opening_snapshot_phase {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality 0 state
      (fun i => treeLateSnapshot 0 (openRep K (ctx i) (v i) count >>= k i)) = (do
        let ds ← free (treeLockstepOpenHashes D (fun _ => true) count v)
        pure (state, fun i => if i ∈ D.1 then none else
          some (treeSimOpenStep K i count (v i) (ds i) (k i)))) := by
  rw [treeLateSnapshot_phase, treeLockstep_open_start_cont K D ctx self]
  simp only [bind_assoc, pure_bind, executeSteps, map_bind, map_pure]
  apply bind_congr
  intro ds
  congr 2
  funext i
  by_cases hi : i ∈ D.1 <;>
    simp [treeSimOpenPartial, hi, treeLateSnapshotOut, treeSimOpenStep]

/-- Split the actual check from the final opening hash pass, retaining its
successful local results and the log of the same final snapshot. -/
theorem check_send (prims : Primitives) {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (st : C.Party → RunState C) (tupleCount : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = tupleCount)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → Unit × RunState C → (ℕ → Bit) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (Step C E RealSpec α))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels tupleCount) state
        (fun i => (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= fun checked =>
          treeLateSnapshot 0 (openRep K (ctx i) (v i) count >>= k i checked)))).run s))
    (live : ∀ i, i ∉ D.1 → (r.1.2 i).isSome) :
    ∃ (checked : C.Party → Unit × RunState C) (ds : C.Party → List HashOutput),
      (∀ i, i ∉ D.1 → some (checked i) ∈ support
        ((check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)).run) ∧
      (∀ i, i ∉ D.1 → r.1.2 i = some (treeSimOpenStep K i count (v i) (ds i) (k i (checked i)))) ∧
      (∀ i, i ∉ D.1 → (ds i).length = C.terms.length ∧
        ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧
          TreeSimHashAnswer r.2.2 (.copy (vector count (v i T))) u) := by
  have finish (checked : C.Party → Unit × RunState C) (state' : A.State) (s' : TreeSimState C)
      (hsupport : ∀ i, i ∉ D.1 → some (checked i) ∈ support
        ((check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)).run)
      (suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality 0 state'
          (fun i => treeLateSnapshot 0 (openRep K (ctx i) (v i) count >>= k i (checked i))))).run s')) :
      ∃ (ds : C.Party → List HashOutput), (∀ i, i ∉ D.1 → r.1.2 i = some (treeSimOpenStep K i count (v i) (ds i) (k i (checked i)))) ∧
        (∀ i, i ∉ D.1 → (ds i).length = C.terms.length ∧
          ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧
            TreeSimHashAnswer r.2.2 (.copy (vector count (v i T))) u) := by
    rw [opening_snapshot_phase K D A state' ctx self] at suffix
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at suffix
    obtain ⟨⟨ds, cache⟩, hashes, rfl⟩ := suffix
    refine ⟨ds, fun i hi => by simp [hi], ?_⟩
    exact fun i hi => treeLockstep_open_hashes_logged prims D (fun _ => true) count v s' (ds, cache)
      hashes i hi rfl
  by_cases zero : tupleCount = 0
  · have empty (i) : (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) =
        pure ((), st i) := by simp only [check, counts i, zero]; rfl
    simp only [empty, pure_bind, zero, checkLabels, if_true] at run
    have supported (i) (_ : i ∉ D.1) : some ((), st i) ∈ support
        ((check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)).run := by
      simp only [empty, OptionT.run_pure, mem_support_pure_iff]
    obtain ⟨ds, shapes, logs⟩ := finish (fun i => ((), st i)) state s supported run
    exact ⟨_, ds, supported, shapes, logs⟩
  · have positive : 0 < checkLabels tupleCount := by simp [checkLabels, zero]
    let n := checkLabels tupleCount - 1
    have time : n + 1 = checkLabels tupleCount := by dsimp only [n]; omega
    let p := fun i => (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
    let cont := fun i checked => treeLateSnapshot 0 (openRep K (ctx i) (v i) count >>= k i checked)
    have timed (i) : TreeSimCheckTimed (n + 1) (p i).run := by
      rw [time, ← counts i]
      exact check_timed K (ctx i) (tuples i) (st i)
    obtain ⟨pref, checked, hprefix, selected, suffix⟩ := timed_boundary_live D prims A n 0 state p cont
      ((), ⟨fun _ => [], 0, 0⟩) timed s r (by simpa only [time, Nat.add_zero] using run) live
    have supported (i) (hi : i ∉ D.1) : some (checked i) ∈ support (p i).run := by
      have replay := treeSimCheck_phase_replay D A noFunctionality _ _ state p pref.1
        (treeLockstep_logged_run_allowed prims D _ s pref hprefix) i hi _ (selected i hi)
      exact replay.choose_spec.1.mem_support
    obtain ⟨ds, shapes, logs⟩ := finish checked pref.1.1 pref.2 supported suffix
    exact ⟨checked, ds, supported, shapes, logs⟩

/-- The exact audited continuation after the opening value is fixed. -/
def auditedSendCont {α : Type} (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (data : BatchData C) (k : AuditOut C → PartyM C E RealSpec α)
    (checked : Unit × RunState C) (out : ℕ → Bit) : PartyM C E RealSpec α :=
  k ((some (assemble (jobs.map (circuits ctx.keys.parameter ·.kind)) out),
      [⟨ctx, jobs, initial, data.1, data.2.1.2, data.2.2,
        assemble (jobs.map (circuits ctx.keys.parameter ·.kind)) out, checked.2⟩]),
    (checked.2.label, initial.2 + 1))

/-- The last-batch window on one retained joint snapshot. Earlier audit
outputs are parameters of k; no independently replayed data replace them. -/
theorem batch_send (prims : Primitives) {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (jobs : List Job) (initial : ℕ × ℕ) (k : C.Party → AuditOut C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (Step C E RealSpec α))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (sendRounds circuits settings parameter jobs) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeLateSnapshot (sendRounds circuits settings parameter jobs)
            ((treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i)))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (live : ∀ i, i ∉ D.1 → (r.1.2 i).isSome) :
    ∃ (data : C.Party → BatchData C) (checked : C.Party → Unit × RunState C)
      (ds : C.Party → List HashOutput),
      (∀ i, i ∉ D.1 → some (data i) ∈ support
        (treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial).run) ∧
      (∀ i, i ∉ D.1 → some (checked i) ∈ support
        ((check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (data i).2.1.2).run (data i).2.2).run) ∧
      (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf (jobs.map (circuits parameter ·.kind))).length →
        (data i).2.1.1 T g = (data (refHolder D T)).2.1.1 T g) ∧
      (∀ i, i ∉ D.1 → r.1.2 i = some (treeSimOpenStep K i
        (outputsOf (jobs.map (circuits parameter ·.kind))).length (data i).2.1.1 (ds i)
        (auditedSendCont circuits (ctx i) jobs initial (data i) (k i) (checked i)))) ∧
      (∀ i, i ∉ D.1 → (ds i).length = C.terms.length ∧
        ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧ TreeSimHashAnswer r.2.2
          (.copy (vector (outputsOf (jobs.map (circuits parameter ·.kind))).length ((data i).2.1.1 T))) u) := by
  let js := jobs.map (circuits parameter ·.kind)
  let p := fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial
  let next := fun i data =>
    (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) data.2.1.2).run data.2.2 >>= fun checked =>
      treeLateSnapshot 0 (treeLockstepBatchCheckCont K circuits (ctx i) jobs initial data (k i) checked)
  have timed (i) : TreeSimCheckTimed (depth js * settings.mode.rounds + 1) (p i).run := by
    have h := treeLockstep_localPrelude_timed (gate i) _ _
      (treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial)
    simpa only [parameters] using h
  have run' : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (depth js * settings.mode.rounds + 1 + checkLabels (tupleCount js)) state
        (fun i => p i >>= next i))).run s) := by
    have eq (i) := snapshot_audit_send K circuits settings (ctx i) jobs initial (k i)
    simp only [parameters] at eq
    simp only [eq] at run
    simpa only [p, next, sendRounds, batchCount, js, bind_assoc] using run
  obtain ⟨pref, raw, hpref, selectedRaw, suffixRaw⟩ := timed_boundary_live D prims A
    (depth js * settings.mode.rounds) (checkLabels (tupleCount js)) state p next
    ([], (0, []), ⟨fun _ => [], initial.1, initial.2⟩) timed s r run' live
  let honest := fun i : C.Party => if i ∉ D.1 then i else refHolder D K.publicTerm
  have hh (i) : honest i ∉ D.1 := by
    by_cases hi : i ∉ D.1
    · simpa only [honest, if_pos hi] using hi
    · simpa only [honest, if_neg hi] using (refHolder_spec D K.publicTerm).2
  have keep (i) (hi : i ∉ D.1) : honest i = i := if_pos hi
  let data := fun i => raw (honest i)
  have selected (i) (hi : i ∉ D.1) : pref.1.2 i = some (data i) := by
    simpa only [data, keep i hi] using selectedRaw i hi
  have supported (i) : some (data i) ∈ support
      (treeSimCheckBatchPrefix K circuits settings (ctx (honest i)) jobs initial).run := by
    have party := treeSimCheck_phase_replay D A noFunctionality _ _ state p pref.1
      (treeLockstep_logged_run_allowed prims D _ s pref hpref) (honest i) (hh i) _ (selectedRaw _ (hh i))
    obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
    exact party.choose_spec.1.mem_support
  have counts (i) : ((data i).2.1.2.map (·.count)).sum = tupleCount js := by
    simpa only [parameters] using (prefix_facts K circuits settings _ jobs initial (data i) (supported i)).1
  have suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels (tupleCount js)) pref.1.1
        (fun i => next i (data i)))).run pref.2) := by
    unfold executePhase at suffixRaw ⊢
    rw [start_congr D (fun i => next i (data i)) (fun i => next i (raw i))
      (fun i hi => by rw [show data i = raw i from congrArg raw (keep i hi)])]
    exact suffixRaw
  have accepted : ∃ i value, r.1.2 i = some value := by
    obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp (live (refHolder D K.publicTerm) (refHolder_spec D K.publicTerm).2)
    exact ⟨_, value, hv⟩
  have held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf js).length →
      (data i).2.1.1 T g = (data (refHolder D T)).2.1.1 T g := by
    by_cases zero : tupleCount js = 0
    · have widthZero : (outputsOf js).length = 0 := by rw [tupleCount_eq] at zero; omega
      intro i T g hi hT hg
      omega
    · have time : checkLabels (tupleCount js) =
          2 * sliceBits + 2 * (halvings (tupleCount js) - sliceBits) + 2 + (2 + 1) := by
        have hs : sliceBits ≤ halvings (tupleCount js) := by unfold halvings; omega
        simp only [checkLabels, if_neg zero]
        omega
      apply treeLockstep_batch_checked_held prims K circuits settings D A _ 2 state ctx self
        parameter parameters keys jobs initial (fun i => treeLockstepLocalPrelude (gate i))
        s pref data selected hpref
        (fun i checked => treeLateSnapshot 0
          (treeLockstepBatchCheckCont K circuits (ctx i) jobs initial (data i) (k i) checked)) r
      · simpa only [next, time] using suffix
      · exact good
      · exact accepted
  obtain ⟨checked, ds, checkSupport, shapes, logs⟩ := check_send K D prims A pref.1.1 ctx self
    (fun i => (data i).2.1.2) (fun i => (data i).2.2) (tupleCount js) counts
    (outputsOf js).length (fun i => (data i).2.1.1)
    (fun i => auditedSendCont circuits (ctx i) jobs initial (data i) (k i)) pref.2 r
    (by
      have eq (i) (checked : Unit × RunState C) :
          treeLockstepBatchCheckCont K circuits (ctx i) jobs initial (data i) (k i) checked =
            openRep K (ctx i) (data i).2.1.1 (outputsOf js).length >>=
              auditedSendCont circuits (ctx i) jobs initial (data i) (k i) checked := by
        unfold treeLockstepBatchCheckCont
        rw [parameters i]
        apply bind_congr
        intro out
        simp only [auditedSendCont, parameters i]
      simpa only [next, eq] using suffix) live
  exact ⟨data, checked, ds, fun i hi => by simpa only [keep i hi] using supported i,
    checkSupport, held, shapes, logs⟩


/-- Reachability embeds the actual final local pass in the original driver. -/
theorem reached_pending (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (initial p : TreeCheckWalkDef.Pending A) (n : ℕ)
    (h : Reached prims D Z initial n p) (m : ℕ)
    (out : (A.State × (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C)))) × TreeSimState C)
    (run : out ∈ support (pendingSteps prims D A m p)) :
    out ∈ support (pendingSteps prims D A (n + m) initial) := by
  induction h generalizing m with
  | start => simpa only [Nat.zero_add] using run
  | next reached fuelLeft step ih =>
    have rest := next_steps_support prims D A Z _ m _ _ step out run
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using ih (m + 1) rest

/-- The raw writer/state append law, retaining both records and counters. -/
theorem audits_append (ctx : Context C) (xs ys : List (List Job)) (initial : ℕ × ℕ) :
    (((xs ++ ys).mapM (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial) =
      (do let a ← ((xs.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial)
          let b ← ((ys.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run a.2)
          pure ((a.1.1 ++ b.1.1, a.1.2 ++ b.1.2), b.2)) := by
  simp [List.mapM_append, WriterT.run_bind, WriterT.run_map, StateT.run_bind, StateT.run_map]

/-- Extract the preceding batches on this same snapshot, with the actual
record lists and common output list. -/
theorem prior_batches (prims : Primitives) {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (batches : List (List Job)) (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (Step C E RealSpec α))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        ((batches.map (batchRounds circuits settings.mode parameter)).sum + sendRounds circuits settings parameter jobs) state
        (fun i => treeLateSnapshot
          ((batches.map (batchRounds circuits settings.mode parameter)).sum + sendRounds circuits settings parameter jobs)
          ((((batches ++ [jobs]).mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run initial) >>= k i)))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (values : List (List (List Bit))) (records : C.Party → List (TreeSimCheckBatchRecord C))
      (state' : A.State) (cache : TreeSimState C) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      values.length = batches.length ∧ (∀ i, (records i).map (·.outputs) = values) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (sendRounds circuits settings parameter jobs) state'
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
            treeLateSnapshot (sendRounds circuits settings parameter jobs)
              ((treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run
                (initial.1 + (batches.map (batchLabels circuits parameter)).sum, initial.2 + batches.length) >>= fun a =>
                k i ((values.map some ++ [a.1.1], records i ++ a.1.2), a.2))))).run cache) := by
  let cont := fun i (a : (List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) =>
    treeLateSnapshot (sendRounds circuits settings parameter jobs)
      ((treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run a.2 >>= fun b =>
        k i ((a.1.1 ++ [b.1.1], a.1.2 ++ b.1.2), b.2))
  have programs (i) : treeLateSnapshot
      ((batches.map (batchRounds circuits settings.mode parameter)).sum + sendRounds circuits settings parameter jobs)
      ((((batches ++ [jobs]).mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run initial) >>= k i) =
      ((batches.mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run initial) >>= cont i := by
    rw [audits_append]
    simp only [List.mapM_cons, List.mapM_nil, WriterT.run_bind, WriterT.run_pure,
      StateT.run_bind, StateT.run_pure, map_pure, pure_bind, bind_assoc]
    have eq := treeLateSnapshot_batches_bind K circuits settings (ctx i) batches initial
      (sendRounds circuits settings parameter jobs)
      (fun a => (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run a.2 >>= fun b =>
        k i ((a.1.1 ++ [b.1.1], a.1.2 ++ b.1.2), b.2))
    simpa [parameters, cont] using eq
  simp only [programs] at run
  apply treeLockstep_batches_next prims K circuits settings D A _ state ctx self parameter parameters keys
    (fun _ => pure (some ())) batches initial cont s r _ good accepted
  simpa only [localPrelude_some, pure_bind] using run

/-- Expose the initial audited list with a symbolic list argument, avoiding
normalization of the concrete bottom-job list in the kernel. -/
theorem initial_list_program (A : Adversary C E (Keys C) PEmpty PEmpty)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (batches : List (List Job)) (eq : firstChunks settings tree = batches)
    (i : C.Party) (present : (p.1.2 i).isSome) :
    (TreeCheckWalkDef.initial K circuits settings top tree x p).program i =
      ((batches.mapM (treeSimCheckBatchAudit K circuits settings ⟨i, x i, setupKeys p.1.2 i⟩)).run.run (0, 0)) >>=
        fun a => treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys p.1.2 i⟩ top tree
          ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2) := by
  obtain ⟨ki, row⟩ := Option.isSome_iff_exists.mp present
  simp only [TreeCheckWalkDef.initial, row, Option.elim_some, setupKeys_some p.1.2 i ki row]
  rw [treeLockstep_afterSetup_first, auditBatched_run]
  change chunks settings.batchSize (treeLockstepFirstJobs tree) = batches at eq
  rw [eq]
  simp only [bind_assoc, pure_bind]

/-- The final check label from the actual supported prefix and check outputs. -/
theorem checked_label (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (data : BatchData C) (checked : Unit × RunState C)
    (pref : some data ∈ support (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run)
    (chk : some checked ∈ support
      ((check (G := RealSpec) K ctx (realCheckGadgets K ctx) data.2.1.2).run data.2.2).run) :
    checked.2.label = initial.1 + batchLabels circuits ctx.keys.parameter jobs := by
  obtain ⟨count, label⟩ := prefix_facts K circuits settings ctx jobs initial data pref
  have fin := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 chk
  rw [count, label] at fin
  simpa only [batchLabels, batchCount, Nat.add_assoc] using fin

attribute [local irreducible] treeLockstepFirstRest treeLockstepPublicChoiceCode

set_option maxHeartbeats 1500000 in
/-- Reconstruct all guarded fields from the one actual send snapshot. -/
theorem guarded_fields (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : p ∈ support (treeSaltSetup prims D A x z))
    (same : ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (j : ℕ) (last : j + 1 = (firstChunks settings (.bottom b)).length)
    (out : (A.State × (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C)))) × TreeSimState C)
    (run : out ∈ support (pendingSteps prims D A
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter j +
        sendRounds circuits settings (x (refHolder D K.publicTerm)).parameter
          ((firstChunks settings (.bottom b)).getD j []))
      (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)))
    (good : ¬ TreeSimHashBudgetCollision out.2.2)
    (live : ∀ i, i ∉ D.1 → out.1.2 i ≠ .done none) :
    ∃ (f : SendFields C) (ds : C.Party → List HashOutput),
      (∀ i, (f.records i).length = j) ∧
      (∀ i, i ∉ D.1 → out.1.2 i = treeSimOpenStep K i
        (width K D circuits settings (.bottom b) x j) (f.shares i) (ds i)
        (fieldsCont K D circuits settings top (.bottom b) x p.1.2 j f i)) ∧
      (∀ i, i ∉ D.1 → (ds i).length = C.terms.length ∧
        ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧ TreeSimHashAnswer out.2.2
          (.copy (vector (width K D circuits settings (.bottom b) x j) (f.shares i T))) u) ∧
      (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < width K D circuits settings (.bottom b) x j →
        f.shares i T g = f.shares (refHolder D T) T g) ∧
      (∀ i k, f.saved i = f.saved k) := by
  let parameter := (x (refHolder D K.publicTerm)).parameter
  let allJobs := firstChunks settings (.bottom b)
  let batches := allJobs.take j
  let jobs := allJobs.getD j []
  let n := batchStart circuits settings (.bottom b) parameter j + sendRounds circuits settings parameter jobs
  let initial := TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p
  let r := ((out.1.1, fun i => treeLateSnapshotOut (out.1.2 i)), out.2)
  have captured : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality n p.1.1
        (fun i => treeLateSnapshot n (initial.program i)))).run p.2) := by
    as_aux_lemma =>
      rw [treeLateSnapshot_phase, simulateQ_map, StateT.run_map, support_map]
      exact ⟨out, run, rfl⟩
  have selected (i) (hi : i ∉ D.1) : r.1.2 i = some (out.1.2 i) :=
    treeLateSnapshotOut_some _ (live i hi)
  have present (i) (hi : i ∉ D.1) : (p.1.2 i).isSome := by
    as_aux_lemma =>
      cases row : p.1.2 i with
      | some keys => rfl
      | none =>
        have replay := treeSimCheck_phase_replay D A noFunctionality _ n p.1.1
          (fun i => treeLateSnapshot n (initial.program i)) r.1
          (treeLockstep_logged_run_allowed prims D _ p.2 r captured) i hi _ (selected i hi)
        have hs := replay.choose_spec.1.mem_support
        simp only [initial, TreeCheckWalkDef.initial, row, Option.elim_none] at hs
        change some (out.1.2 i) ∈ support (treeLateSnapshot n (OptionT.mk (pure none))).run at hs
        simp only [treeLateSnapshot_pure, Option.map_none, mem_support_pure_iff, reduceCtorEq] at hs
  let ctx := fun i => (⟨i, x i, setupKeys p.1.2 i⟩ : Context C)
  have self (i) : (ctx i).self = i := rfl
  have parameters (i) : (ctx i).keys.parameter = parameter := same i
  have prefixLog : p.2.2 <+: out.2.2 := treeSimLoggedWorld_prefix prims D _ _ _ run
  have setupGood : ¬ TreeSimHashBudgetCollision p.2.2 :=
    fun h => good (treeSimHashBudgetCollision_mono prefixLog h)
  have keys : Consistent D (fun i T => (ctx i).prss.term T) := by
    as_aux_lemma =>
      intro T i hiT k hkT hi hk
      obtain ⟨ki, rowI⟩ := Option.isSome_iff_exists.mp (present i hi)
      obtain ⟨kk, rowK⟩ := Option.isSome_iff_exists.mp (present k hk)
      exact (by
        simpa only [ctx, setupKeys_some p.1.2 i ki rowI, setupKeys_some p.1.2 k kk rowK] using
          treeAgreementSetupKeys prims D A x z p setupRun setupGood i k ki kk rowI rowK T hiT hkT)
  have current : j < allJobs.length := by dsimp only [allJobs]; omega
  have len : batches.length = j := by simp only [batches, List.length_take, Nat.min_eq_left current.le]
  have split : allJobs = batches ++ [jobs] := by
    as_aux_lemma =>
      calc
        allJobs = allJobs.take (j + 1) := by rw [last]; exact List.take_length.symm
        _ = batches ++ [jobs] := by
          as_aux_lemma =>
            simp only [List.take_add_one, Option.toList_some,
            batches, jobs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem current, Option.getD_some]
  let whole := fun i (a : (List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) =>
    treeLockstepFirstRest K circuits settings (ctx i) top (.bottom b)
      ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)
  have programs (i) (hi : i ∉ D.1) : initial.program i =
      (((batches ++ [jobs]).mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run (0, 0)) >>= whole i :=
    initial_list_program K circuits settings top (.bottom b) x A p (batches ++ [jobs]) split i (present i hi)
  have live' (i) (hi : i ∉ D.1) : (r.1.2 i).isSome := by rw [selected i hi]; rfl
  have accepted : ∃ i value, r.1.2 i = some value :=
    ⟨refHolder D K.publicTerm, _, selected _ (refHolder_spec D K.publicTerm).2⟩
  have captured' : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        ((batches.map (batchRounds circuits settings.mode parameter)).sum + sendRounds circuits settings parameter jobs)
        p.1.1 (fun i => treeLateSnapshot n
          ((((batches ++ [jobs]).mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run (0, 0)) >>= whole i)))).run p.2) := by
    as_aux_lemma =>
      unfold executePhase at captured ⊢
      rw [← start_congr D (fun i => treeLateSnapshot n (initial.program i)) _
        (fun i hi => congrArg (treeLateSnapshot n) (programs i hi))]
      exact captured
  obtain ⟨values, records, state', cache, gate, vlen, saved, suffix⟩ := prior_batches K D circuits settings prims A
    p.1.1 ctx self parameter parameters keys batches jobs (0, 0) whole p.2 r captured' good accepted
  let initialBatch := ((batches.map (batchLabels circuits parameter)).sum, j)
  let cont := fun i (a : AuditOut C) => whole i ((values.map some ++ [a.1.1], records i ++ a.1.2), a.2)
  obtain ⟨data, checked, ds, supported, checkSupport, held, shapes, logs⟩ := batch_send K D circuits settings prims A
    state' ctx self parameter parameters keys gate jobs initialBatch cont cache r
    (by simpa only [Nat.zero_add, len] using suffix) good live'
  let recordOf := fun i out => (⟨ctx i, jobs, initialBatch, (data i).1, (data i).2.1.2, (data i).2.2,
    assemble (jobs.map (circuits parameter ·.kind)) out, (checked i).2⟩ : TreeSimCheckBatchRecord C)
  let f : SendFields C := ⟨fun i => (data i).2.1.1, fun _ => values.flatten, records, recordOf⟩
  have finishLabel (i) (hi : i ∉ D.1) :
      (checked i).2.label = (signingInitial K D circuits settings (.bottom b) x).1 := by
    as_aux_lemma =>
      have fin := checked_label K circuits settings (ctx i) jobs initialBatch (data i) (checked i)
        (supported i hi) (checkSupport i hi)
      simp only [parameters] at fin
      change (checked i).2.label = lockstepStart circuits parameter allJobs allJobs.length
      rw [← last, lockstepStart_succ circuits parameter allJobs j current]
      exact fin
  have continuation (i) (hi : i ∉ D.1) :
      auditedSendCont circuits (ctx i) jobs initialBatch (data i) (cont i) (checked i) =
        fieldsCont K D circuits settings top (.bottom b) x p.1.2 j f i := by
    as_aux_lemma =>
      funext out
      unfold auditedSendCont cont whole fieldsCont sendCont
      simp only [parameters, finishLabel i hi]
      simp [f, recordOf, initialBatch, foldlM_some, List.foldlM_append, signingInitial, last]
      rfl
  refine ⟨f, ds, ?_, ?_, logs, held, fun _ _ => rfl⟩
  · intro i
    have h := congrArg List.length (saved i)
    simpa only [List.length_map, vlen, len] using h
  · intro i hi
    have h := shapes i hi
    rw [selected i hi, continuation i hi] at h
    exact Option.some.inj h

set_option maxHeartbeats 1500000 in
/-- The original first-run opening invariant, without residual premises. -/
theorem firstRunOpening (prims : Primitives) : FirstRunOpening K circuits settings prims := by
  intro positive top b D A x z Z dealt p setupRun q reached
  have same (i) : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    as_aux_lemma =>
      obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
      rw [hx i, hx (refHolder D K.publicTerm)]
      rfl
  have pos := firstChunks_bottom_pos settings positive b
  obtain ⟨j, last⟩ : ∃ j, j + 1 = (firstChunks settings (.bottom b)).length :=
    ⟨(firstChunks settings (.bottom b)).length - 1, by omega⟩
  let n := batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter j +
    sendRounds circuits settings (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings (.bottom b)).getD j [])
  have rounds : batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings (.bottom b)).length = n + 1 := by
    as_aux_lemma =>
      rw [batchStart_last circuits settings (.bottom b) _ j last]
      simp only [n, batchRounds, sendRounds, Nat.add_assoc]
  rw [rounds] at reached
  obtain ⟨prev, fuel, started, reply, before, fuelLeft, startRun, nonterminal, replyRun, qeq, logPrefix⟩ :=
    reached_last D prims A Z _ n q reached
  obtain ⟨live, f, lengths, programs⟩ := pending_fields K D circuits settings top x prims positive b A Z p
    same j last prev before
  let count := width K D circuits settings (.bottom b) x j
  let k := fieldsCont K D circuits settings top (.bottom b) x p.1.2 j f
  have starts : startSteps worldRoles D prev.program = (do
      let ds ← free (treeLockstepOpenHashes D live count f.shares)
      pure (treeSimOpenPartial K D live count f.shares ds k)) :=
    (start_congr D _ _ programs).trans (open_start_live K D live count
      (fun i => ⟨i, x i, setupKeys p.1.2 i⟩) (fun _ => rfl) f.shares k)
  have actualStart := startRun
  rw [starts] at startRun
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at startRun
  obtain ⟨⟨ds, cache⟩, hashes, rfl⟩ := startRun
  have program : q.program = TreeCheckWalkDef.resume D
      (treeSimOpenPartial K D live count f.shares ds k) reply.1.2 := congrArg TreeCheckWalkDef.Pending.program qeq
  have existsLive : ∃ i, i ∉ D.1 ∧ live i = true := by
    as_aux_lemma =>
      by_contra hn
      push Not at hn
      apply nonterminal
      intro i hi
      simp [treeSimOpenPartial, hi, hn i hi, Step.isDone]
  have logs := treeLockstep_open_hashes_logged prims D live count f.shares prev.world (ds, cache) hashes
  have logged (i) (hi : i ∉ D.1) (hl : live i = true) : (ds i).length = C.terms.length ∧
      ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer q.world.2 (.copy (vector count (f.shares i T))) u := by
    as_aux_lemma =>
      obtain ⟨len, hs⟩ := logs i hi hl
      refine ⟨len, fun T => ?_⟩
      obtain ⟨u, hu, hit⟩ := hs T
      exact ⟨u, hu, hit.imp (fun h => logPrefix.subset h) (fun h => logPrefix.subset h)⟩
  by_cases guard : Guard D A q
  swap
  · exact window_of_send K D circuits settings top x p.1.2 A b j last q live f ds reply.1.2
      program existsLive lengths logged (fun h => (guard h).elim)
  have allLive : ∀ i, i ∉ D.1 → live i = true := by
    as_aux_lemma =>
      obtain ⟨i, hi, hn⟩ := guard.2
      rcases resume_open K D live count f.shares ds k reply.1.2 i hi with dead | ⟨all, _⟩
      · exact False.elim (hn (by simpa only [program] using dead))
      · exact all
  let out := ((prev.state, treeSimOpenPartial K D live count f.shares ds k), cache)
  have pending : out ∈ support (pendingSteps prims D A n
      (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)) := by
    as_aux_lemma =>
      have zero : out ∈ support (pendingSteps prims D A 0 prev) := by
        as_aux_lemma =>
          simp only [pendingSteps, executeSteps, simulateQ_bind, simulateQ_pure, StateT.run_bind,
            StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff]
          exact ⟨_, actualStart, rfl⟩
      simpa only [Nat.add_zero] using reached_pending D prims A Z _ prev n before 0 out zero
  have good : ¬ TreeSimHashBudgetCollision cache.2 :=
    fun h => guard.1 (treeSimHashBudgetCollision_mono logPrefix h)
  have stepLive (i) (hi : i ∉ D.1) : out.1.2 i ≠ .done none := by
    as_aux_lemma =>
      simp [out, treeSimOpenPartial, hi, allLive i hi, treeSimOpenStep]
  obtain ⟨f', ds', lengths', shapes, logs', held, common⟩ := guarded_fields K D circuits settings top x prims A b z
    p setupRun same j last out pending good stepLive
  have steps : treeSimOpenPartial K D live count f.shares ds k =
      treeSimOpenPartial K D (fun _ => true) count f'.shares ds'
        (fieldsCont K D circuits settings top (.bottom b) x p.1.2 j f') := by
    as_aux_lemma =>
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimOpenPartial, hi]
      · simpa only [out, treeSimOpenPartial, if_neg hi, if_true] using shapes i hi
  rw [steps] at program
  apply window_of_send K D circuits settings top x p.1.2 A b j last q (fun _ => true) f' ds' reply.1.2
    program ⟨refHolder D K.publicTerm, (refHolder_spec D K.publicTerm).2, rfl⟩ lengths'
  · intro i hi _
    obtain ⟨len, hs⟩ := logs' i hi
    refine ⟨len, fun T => ?_⟩
    obtain ⟨u, hu, hit⟩ := hs T
    exact ⟨u, hu, hit.imp (fun h => logPrefix.subset h) (fun h => logPrefix.subset h)⟩
  · intro _
    exact ⟨held, fun i k _ _ _ _ => common i k⟩

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.residual_batch_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_batch_send

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.pending_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pending_send

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.resume_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resume_open

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.window_of_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_of_send

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.timed_boundary_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms timed_boundary_live

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.batch_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_send

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.guarded_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guarded_fields

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkFirstOpening.firstRunOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstRunOpening

end TreeCheckWalkFirstOpening
end ThresholdLeanXmssSecurity
