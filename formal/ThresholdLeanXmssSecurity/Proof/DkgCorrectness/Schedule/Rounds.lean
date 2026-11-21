import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutWalk
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.OpeningReach

/-!
# The round count of a prefix of one ceremony

`prefixRounds` is the number of rounds of one ceremony up to the start of the check of its batch
`k`. It counts the PRSS setup, the full batches before batch `k`, and the AND layers and `Rerand`
of batch `k`. For `k` at least the number of the batches, it is the whole ceremony
(`prefixRounds_of_le`). `timed_cutCeremony` states that the program of an operator that stops at
the check of batch `k` takes exactly `prefixRounds` rounds on each path with no abort.

The recorded ceremony is its recorded prefix up to the start of the check of batch `k`
(`recPrefix`), then the record of the start and the check (`recCheck`), then the rest (`finRest`)
(`recCeremony_eq`, `recFinish_eq`). The recorded prefix takes `prefixRounds` rounds
(`timedLog_recPrefix`), each of its leaves holds at most `k` starts (`leafStarts_recPrefix`), and with
its records dropped it stops at the starts of the checks of the cut program
(`cutStop_cutCeremony`, `recPrefix_pointAt`). With its record dropped, the check part is the program
of the pilot (`dropRec_recCheck`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## Timed programs with a premise on the support -/

section Timed

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

theorem mem_support_liftBind_of {α : Type} (t : (PartySpec C E G).Domain)
    (f : (PartySpec C E G).Range t → OracleComp (PartySpec C E G) α) (r : (PartySpec C E G).Range t) (a : α)
    (h : a ∈ support (f r)) : a ∈ support (PFunctor.FreeM.liftBind t f : OracleComp (PartySpec C E G) α) := by
  change a ∈ support (OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) t) >>= f)
  rw [mem_support_bind_iff]
  exact ⟨r, by simp, h⟩

/-- `Timed.bind` with a premise on the continuation only for the outputs in the support. -/
theorem _root_.ThresholdLeanXmssSecurity.Timed.bind_of_support {α β : Type} {m n : ℕ} {p : PartyM C E G α} {k : α → PartyM C E G β}
    (hp : Timed m p.run) (hk : ∀ a, some a ∈ support p.run → Timed n (k a).run) : Timed (m + n) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change Timed (m + n) (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run))
  generalize p.run = oa at hp hk ⊢
  induction hp with
  | abort m => simpa only [pure_bind, Option.elim_none] using Timed.abort (α := β) (m + n)
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hk a (by simp)
  | queryLocal m q f _ ih =>
    exact Timed.queryLocal (m + n) q _ fun r => ih r fun a ha => hk a (mem_support_liftBind_of (.inl (.inl q)) f r _ ha)
  | round m out f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Timed.round (m + n) out _ fun r => ih r fun a ha => hk a (mem_support_liftBind_of (.inl (.inr out)) f r _ ha)
  | call m input f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Timed.call (m + n) input _ fun r => ih r fun a ha => hk a (mem_support_liftBind_of (.inr input) f r _ ha)

theorem _root_.ThresholdLeanXmssSecurity.Timed.of_eq {α : Type} {m n : ℕ} {p : OracleComp (PartySpec C E G) (Option α)} (h : Timed m p)
    (hmn : m = n) : Timed n p := hmn ▸ h

end Timed

/-! ## The rounds of a prefix -/

section Rounds

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The rounds of the head of a batch of the circuits `cs`, namely its AND layers and `Rerand`. -/
def headRounds (mode : ReshareMode) (cs : List Circuit) : ℕ := depth cs * mode.rounds + 1

/-- The rounds of the batches `l` up to the start of the check of batch `j`. For `j` at least the
length of `l`, it is the rounds of all the batches. -/
def stopRounds (parameter : PublicParameter) (l : List (List Job)) (j : ℕ) : ℕ :=
  ((l.take j).map fun batch => CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum +
    match l[j]? with
    | some batch => headRounds settings.mode (batch.map (circuits parameter ·.kind))
    | none => 0

/-- The rounds of one ceremony of `jobs` under `parameter` up to the start of the check of batch `k`.
For `k` at least the number of the batches, it is the whole ceremony. -/
def prefixRounds (parameter : PublicParameter) (jobs : List Job) (k : ℕ) : ℕ :=
  setupRounds + stopRounds circuits settings parameter (chunks settings.batchSize jobs) k

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem stopRounds_cons_zero (parameter : PublicParameter) (b : List Job) (l : List (List Job)) :
    stopRounds circuits settings parameter (b :: l) 0 =
      headRounds settings.mode (b.map (circuits parameter ·.kind)) := by
  simp [stopRounds]

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem stopRounds_cons_succ (parameter : PublicParameter) (b : List Job) (l : List (List Job)) (j : ℕ) :
    stopRounds circuits settings parameter (b :: l) (j + 1) =
      CheckTiming.exactBatchRounds settings.mode (b.map (circuits parameter ·.kind)) +
        stopRounds circuits settings parameter l j := by
  simp only [stopRounds, List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem?_cons_succ]
  omega

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem stopRounds_nil (parameter : PublicParameter) (j : ℕ) : stopRounds circuits settings parameter [] j = 0 := by
  simp [stopRounds]

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- The whole ceremony is the last case of a prefix. -/
theorem prefixRounds_of_le (parameter : PublicParameter) (jobs : List Job) (k : ℕ)
    (hk : (chunks settings.batchSize jobs).length ≤ k) :
    prefixRounds circuits settings parameter jobs k = CheckTiming.ceremonyRounds circuits settings parameter jobs := by
  unfold prefixRounds stopRounds CheckTiming.ceremonyRounds
  rw [List.take_of_length_le hk, List.getElem?_eq_none hk, Nat.add_zero]

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem headRounds_le (mode : ReshareMode) (cs : List Circuit) :
    headRounds mode cs ≤ CheckTiming.exactBatchRounds mode cs := by
  unfold headRounds CheckTiming.exactBatchRounds
  omega

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem stopRounds_le (parameter : PublicParameter) :
    ∀ (l : List (List Job)) (j : ℕ), stopRounds circuits settings parameter l j ≤
      (l.map fun batch => CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum
  | [], j => by simp [stopRounds_nil]
  | b :: l, 0 => by
    rw [stopRounds_cons_zero, List.map_cons, List.sum_cons]
    exact (headRounds_le _ _).trans (Nat.le_add_right _ _)
  | b :: l, j + 1 => by
    rw [stopRounds_cons_succ, List.map_cons, List.sum_cons]
    exact Nat.add_le_add_left (stopRounds_le parameter l j) _

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- A prefix has at most the rounds of the whole ceremony. -/
theorem prefixRounds_le (parameter : PublicParameter) (jobs : List Job) (k : ℕ) :
    prefixRounds circuits settings parameter jobs k ≤ CheckTiming.ceremonyRounds circuits settings parameter jobs :=
  Nat.add_le_add_left (stopRounds_le circuits settings parameter _ k) _

end Rounds

/-! ## The timing of the program that stops at a check -/

section Cut

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- The head of a batch takes its AND layers and `Rerand`. -/
theorem runTimed_runJobsHead (ctx : Context C) (mode : ReshareMode) (cs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    RunTimed (headRounds mode cs) (runJobsHead K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs) := by
  rw [runJobsHead_eq, headRounds]
  have hlayer : ∀ p l, RunTimed mode.rounds (layerBody K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs p l) :=
    fun p l => by
      rw [layerBody_apply]
      exact (RunTimed.bind (runTimed_realMult K ctx mode _ _ _) fun _ => runTimed_pure _).of_eq (Nat.add_zero _)
  have hfold := RunTimed.foldlM _ hlayer (List.range (depth cs)) (inputs, [])
  rw [List.length_range] at hfold
  exact hfold.bind fun p => (RunTimed.bind (runTimed_realRerand K ctx mode _ _) fun _ => runTimed_pure _).of_eq
    (Nat.add_zero _)

omit [Fintype E] [DecidableEq E] in
/-- The batch that stops takes its head, and then it stops. -/
theorem timed_cutBatch (ctx : Context C) (parameter : PublicParameter) (js : List Job) (st : ℕ × ℕ) :
    Timed (headRounds settings.mode (js.map (circuits parameter ·.kind)))
      ((cutBatch K circuits settings ctx parameter js).run st).run.run := by
  unfold cutBatch
  simp only [StateT.run_bind, StateT.run_get, CutM.lift_run, StateT.run_lift, Paused.run_bind,
    Paused.lift, Paused.stop, map_bind, map_pure, pure_bind, bind_assoc]
  exact ((timed_inputShares ctx js).bind fun inputs => ((runTimed_runJobsHead K ctx settings.mode _ inputs _).bind
    fun _ => timed_pure _).of_eq (Nat.add_zero _)).of_eq (Nat.zero_add _)

omit [Fintype E] [DecidableEq E] in
/-- The rounds of a sequence of programs that stop at a check. A stop of the first program ends the
sequence at once, so the second program must take no round after a stop in the support. -/
theorem timed_cutM_bind {α β : Type} {x : CutM K α} {f : α → CutM K β} {st : ℕ × ℕ} {m n : ℕ}
    (hx : Timed m (x.run st).run.run)
    (hf : ∀ a, some (.inl a) ∈ support (x.run st).run.run → Timed n ((f a.1).run a.2).run.run)
    (hstop : ∀ point rest, some (.inr (point, rest)) ∈ support (x.run st).run.run → n = 0) :
    Timed (m + n) ((x >>= f).run st).run.run := by
  rw [StateT.run_bind, Paused.run_bind]
  refine Timed.bind_of_support hx fun o ho => ?_
  rcases o with a | ⟨point, rest⟩
  · exact hf a ho
  · rw [hstop point rest ho]
    exact timed_pure _

omit [Fintype E] [DecidableEq E] in
theorem timed_cutM_pure {α : Type} (a : α) (st : ℕ × ℕ) : Timed 0 ((pure a : CutM K α).run st).run.run :=
  timed_pure _

/-- The batches of a ceremony that stops at the tag `k`, from the tag `st.2 ≤ k`, take the rounds up
to the start of the check of the batch at the tag `k`. -/
theorem timed_cutBatches_mapM (k : ℕ) (i : C.Party) (keys : Keys C) (prss : PrssKeys C) :
    ∀ (l : List (List Job)) (st : ℕ × ℕ), st.2 ≤ k →
      Timed (stopRounds circuits settings keys.parameter l (k - st.2))
        ((l.mapM fun js => (do
          let (_, tag) ← get
          if tag = k then cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter js
          else CutM.lift (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter js) : CutM K _)).run st).run.run
  | [], st, _ => by
    rw [stopRounds_nil, List.mapM_nil]
    exact timed_cutM_pure K _ st
  | b :: l, st, hk => by
    rw [List.mapM_cons]
    by_cases ht : st.2 = k
    · subst ht
      have hb : ((do
          let (_, tag) ← get
          if tag = st.2 then cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter b
          else CutM.lift (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter b) : CutM K _).run st) =
          (cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter b).run st := by
        simp only [StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
      rw [Nat.sub_self, stopRounds_cons_zero, ← Nat.add_zero (headRounds _ _)]
      refine timed_cutM_bind K ?_ (fun a ha => ?_) fun _ _ _ => rfl
      · rw [hb]
        exact timed_cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter b st
      · rw [hb] at ha
        exact absurd ((cutWalk_cutBatch K circuits settings i keys prss b st _ ha).1 a rfl) id
    · have hlt : st.2 < k := lt_of_le_of_ne hk ht
      have hb : ((do
          let (_, tag) ← get
          if tag = k then cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter b
          else CutM.lift (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter b) : CutM K _).run st) =
          (CutM.lift (K := K) (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter b)).run st := by
        simp only [StateT.run_bind, StateT.run_get, pure_bind, ht, ↓reduceIte]
      have hw := cutWalk_lift (K := K) (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter b)
        (fun _ _ => False)
      rw [show k - st.2 = (k - (st.2 + 1)) + 1 by omega, stopRounds_cons_succ]
      refine timed_cutM_bind K ?_ (fun a ha => ?_) fun point rest ho => ?_
      · rw [hb, CutM.lift_run]
        exact Timed.map _ (CheckTiming.runTimed_realBatch_exact K circuits settings.mode _ keys.parameter b st)
      · rw [hb] at ha
        have hr := realBatch_support K circuits settings _ keys.parameter b st a ((hw st _ ha).1 a rfl)
        rw [← Nat.add_zero (stopRounds _ _ _ _ _)]
        refine timed_cutM_bind K ?_ (fun xs _ => timed_cutM_pure K _ _) fun _ _ _ => rfl
        have h := timed_cutBatches_mapM k i keys prss l a.2 (by rw [hr]; exact hlt)
        rw [hr] at h ⊢
        exact h
      · rw [hb] at ho
        exact ((hw st _ ho).2 point rest rfl).elim

/-- One ceremony that stops at the tag `k`, from the tag `st.2 ≤ k`, takes its PRSS setup and the
rounds of its batches up to the start of the check of the batch at the tag `k`. -/
theorem timed_cutRun (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) (st : ℕ × ℕ) (hk : st.2 ≤ k) :
    Timed (setupRounds + stopRounds circuits settings keys.parameter (chunks settings.batchSize jobs) (k - st.2))
      ((cutRun K circuits settings k i keys jobs).run st).run.run := by
  rw [SetupCut.cutRun_eq]
  have hw := cutWalk_lift (K := K) (StateT.lift (prssSetup (E := E) (G := RealSpec) i) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (PrssKeys C)) (fun _ _ => False)
  refine timed_cutM_bind K ?_ (fun a ha => ?_) fun point rest ho => ((hw st _ ho).2 point rest rfl).elim
  · rw [CutM.lift_run]
    exact Timed.map _ (RunTimed.lift (timed_prssSetup i) st)
  · have hst := lift_counters (prssSetup i) st a ((hw st _ ha).1 a rfl)
    unfold SetupCut.cutBatches batched
    rw [← Nat.add_zero (stopRounds _ _ _ _ _), hst]
    exact timed_cutM_bind K (timed_cutBatches_mapM K circuits settings k i keys a.1 _ st hk)
      (fun _ _ => timed_cutM_pure K _ _) fun _ _ _ => rfl

/-- The round count of a prefix. The program of an operator that stops at the check of batch `k` of
one ceremony takes exactly `prefixRounds` rounds under the parameter `parameter` of its keys, on each
path with no abort. For `k` at least the number of the batches, it is the whole ceremony
(`prefixRounds_of_le`). -/
theorem timed_cutCeremony (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (parameter : PublicParameter)
    (hparameter : ∀ keys, c.keys i = some keys → keys.parameter = parameter) :
    Timed (prefixRounds circuits settings parameter c.jobs k) (cutCeremony K circuits settings k i c).run := by
  unfold cutCeremony
  cases hkeys : c.keys i with
  | none => exact timed_failure _
  | some keys =>
    have h := timed_cutRun K circuits settings (c.counters.2 + k) i keys c.jobs c.counters (Nat.le_add_right _ _)
    rw [Nat.add_sub_cancel_left, hparameter keys hkeys] at h
    exact h

end Cut

/-! ## The recorded ceremony as a prefix and a rest -/

section Recorded

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The head of a recorded batch, namely its input sharings, its AND layers and `Rerand`. It gives the
start of the check of the batch and the tag of its counters. The code is the code of `recBatch`. -/
def recHead (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    StateT (ℕ × ℕ) (RecM C E) (BatchStart C × ℕ) := do
  let (label, k) ← get
  let cs := jobs.map (circuits parameter ·.kind)
  let B := realRunBuildingBlocks (G := RealSpec) K ctx settings.mode
  let inputs ← RecM.liftS (StateT.lift (jobs.mapM (inputShares ctx)))
  let (zs, s1) ← RecM.liftS (StateT.lift ((recLayers K B cs inputs (depth cs)).run ⟨fun _ => [], label, k⟩))
  let (v', s2) ← RecM.liftS (StateT.lift ((B.rerand (outputShares K cs
    (layerPrefix K B.mode cs inputs zs (depth cs)).1) (outputsOf cs).length).run s1))
  pure (⟨B.mode, jobs, parameter, cs, inputs, zs, v', ctx, s2⟩, k)

omit [Fintype E] [DecidableEq E] in
theorem recBatch_eq_head (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    recBatch K circuits settings ctx parameter jobs =
      recHead K circuits settings ctx parameter jobs >>= fun h => recCheckOpen K h.1 h.2 := by
  unfold recBatch recHead
  simp only [bind_assoc, pure_bind]

/-- The recorded ceremony up to the start of the check of batch `k`. It gives the outputs of the
batches before `k` and the start of the check of batch `k` with its tag. -/
def recPrefix (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    StateT (ℕ × ℕ) (RecM C E) (PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) := do
  let prss ← RecM.liftS (StateT.lift (prssSetup i))
  let outs ← ((chunks settings.batchSize jobs).take k).mapM
    (recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter)
  let head ← recHead K circuits settings ⟨i, keys, prss⟩ keys.parameter ((chunks settings.batchSize jobs).getD k [])
  pure (prss, outs, head)

/-- The rest of the recorded ceremony after the start of the check of batch `k`. -/
def recRest (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (d : PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let x ← recCheckOpen K d.2.2.1 d.2.2.2
  let xs ← ((chunks settings.batchSize jobs).drop (k + 1)).mapM
    (recBatch K circuits settings ⟨i, keys, d.1⟩ keys.parameter)
  pure ((d.2.1 ++ x :: xs).foldlM (fun acc batch => batch.map (acc ++ ·)) [])

omit [Fintype E] [DecidableEq E] in
/-- The recorded ceremony is its prefix up to the start of the check of batch `k` and then its rest. -/
theorem recRun_eq_prefix (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (hk : k < (chunks settings.batchSize jobs).length) :
    recRun K circuits settings i keys jobs =
      recPrefix K circuits settings k i keys jobs >>= recRest K circuits settings k i keys jobs := by
  have hsplit : chunks settings.batchSize jobs = (chunks settings.batchSize jobs).take k ++
      (chunks settings.batchSize jobs).getD k [] :: (chunks settings.batchSize jobs).drop (k + 1) := by
    rw [List.getD_eq_getElem _ _ hk, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  unfold recRun recPrefix recRest batched
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun prss => ?_
  conv_lhs => rw [hsplit]
  rw [List.mapM_append, List.mapM_cons]
  simp only [bind_assoc, pure_bind, recBatch_eq_head]

end Recorded

/-! ## The starts in the leaves of a recorded program -/

section Starts

open RecordedOpening

variable {C : Committee} {E : Type} {α β : Type}

/-- Each leaf of a recorded program holds at most `n` starts in its record. -/
def LeafStarts (n : ℕ) (p : OracleComp (PartySpec C E RealSpec) (Option α × Record C E)) : Prop :=
  ∀ x ∈ support p, (startsOf x.2).length ≤ n

theorem leafStarts_recBind {m n : ℕ} {x : RecM C E α} {f : α → RecM C E β} (hx : LeafStarts m x.run.run)
    (hf : ∀ a, LeafStarts n (f a).run.run) : LeafStarts (m + n) (x >>= f).run.run := by
  intro z hz
  rw [run_recBind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  rcases y with ⟨_ | a, w⟩
  · simp only [recCont, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (hx _ hy).trans (Nat.le_add_right _ _)
  · simp only [recCont, support_map, Set.mem_image] at hz
    obtain ⟨y', hy', rfl⟩ := hz
    rw [length_startsOf_append]
    exact Nat.add_le_add (hx _ hy) (hf a _ hy')

theorem leafStarts_lift (p : PartyM C E RealSpec α) : LeafStarts 0 (RecM.lift p).run.run := by
  intro z hz
  rw [run_recLift, support_map] at hz
  obtain ⟨o, -, rfl⟩ := hz
  simp [startsOf]

theorem leafStarts_pure (a : α) : LeafStarts 0 (pure a : RecM C E α).run.run := by
  intro z hz
  rw [run_recPure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp [startsOf]

theorem leafStarts_record (events : List (RecEvent C E)) :
    LeafStarts (startsOf events).length (RecM.record events).run.run := by
  intro z hz
  have h : (RecM.record events >>= fun u => (pure u : RecM C E PUnit)).run.run =
      (fun y => (y.1, events ++ y.2)) <$> (pure PUnit.unit : RecM C E PUnit).run.run :=
    run_recRecord_bind events pure
  rw [bind_pure] at h
  rw [h, run_recPure, map_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp [startsOf]

theorem LeafStarts.mono {m n : ℕ} {p : OracleComp (PartySpec C E RealSpec) (Option α × Record C E)}
    (h : LeafStarts m p) (hmn : m ≤ n) : LeafStarts n p := fun x hx => (h x hx).trans hmn

variable {S : Type}

theorem leafStarts_stateBind {m n : ℕ} {x : StateT S (RecM C E) α} {f : α → StateT S (RecM C E) β}
    (hx : ∀ st, LeafStarts m (x.run st).run.run) (hf : ∀ a st, LeafStarts n ((f a).run st).run.run) :
    ∀ st, LeafStarts (m + n) ((x >>= f).run st).run.run := fun st => by
  rw [StateT.run_bind]
  exact leafStarts_recBind (hx st) fun p => hf p.1 p.2

theorem leafStarts_statePure (a : α) : ∀ st : S, LeafStarts 0 ((pure a : StateT S (RecM C E) α).run st).run.run :=
  fun st => by
    rw [StateT.run_pure]
    exact leafStarts_pure _

theorem leafStarts_liftS (y : StateT S (PartyM C E RealSpec) α) :
    ∀ st, LeafStarts 0 ((RecM.liftS y).run st).run.run := fun _ => leafStarts_lift _

theorem leafStarts_stateLift {n : ℕ} (x : RecM C E α) (hx : LeafStarts n x.run.run) :
    ∀ st : S, LeafStarts n ((StateT.lift x : StateT S (RecM C E) α).run st).run.run := fun st => by
  rw [StateT.run_lift, ← Nat.add_zero n]
  exact leafStarts_recBind hx fun a => leafStarts_pure _

theorem leafStarts_get : ∀ st : S, LeafStarts 0 ((get : StateT S (RecM C E) S).run st).run.run := fun st => by
  rw [StateT.run_get]
  exact leafStarts_pure _

theorem leafStarts_set (t : S) : ∀ st : S, LeafStarts 0 ((set t : StateT S (RecM C E) PUnit).run st).run.run :=
  fun st => by
    rw [StateT.run_set]
    exact leafStarts_pure _

theorem leafStarts_mapM {γ : Type} {n : ℕ} (f : γ → StateT S (RecM C E) α) (hf : ∀ a st, LeafStarts n ((f a).run st).run.run) :
    ∀ (l : List γ) (st : S), LeafStarts (l.length * n) ((l.mapM f).run st).run.run
  | [], st => by
    rw [List.mapM_nil, List.length_nil, Nat.zero_mul]
    exact leafStarts_statePure _ st
  | a :: l, st => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm (l.length * n), ← Nat.add_zero (n + _),
      ← Nat.add_zero (l.length * n)]
    exact leafStarts_stateBind (hf a) (fun b => leafStarts_stateBind (leafStarts_mapM f hf l)
      fun bs => leafStarts_statePure _) st

end Starts

section StartsBatch

open RecordedOpening

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
theorem leafStarts_recCheckOpen (b : BatchStart C) (k : ℕ) :
    ∀ st, LeafStarts 1 ((recCheckOpen K b k).run st).run.run := by
  have hz : ∀ {γ δ : Type} {x : StateT (ℕ × ℕ) (RecM C E) γ} {f : γ → StateT (ℕ × ℕ) (RecM C E) δ} {n : ℕ},
      (∀ st, LeafStarts 0 (x.run st).run.run) → (∀ a st, LeafStarts n ((f a).run st).run.run) →
      ∀ st, LeafStarts n ((x >>= f).run st).run.run := fun hx hf st => by
    simpa only [Nat.zero_add] using leafStarts_stateBind hx hf st
  have hrec : ∀ e : RecEvent C E, (∀ b, e ≠ .start b) →
      ∀ st, LeafStarts 0 ((StateT.lift (RecM.record [e]) : StateT (ℕ × ℕ) (RecM C E) PUnit).run st).run.run := by
    intro e he st
    have h := leafStarts_stateLift (S := ℕ × ℕ) _ (leafStarts_record (C := C) (E := E) [e]) st
    cases e with
    | start b' => exact absurd rfl (he b')
    | opened v inbox => simpa [startsOf] using h
    | output o => simpa [startsOf] using h
  have h1 := leafStarts_stateLift (S := ℕ × ℕ) _ (leafStarts_record (C := C) (E := E) [.start b])
  simp only [startsOf, List.filterMap_cons, List.filterMap_nil, List.length_singleton] at h1
  unfold recCheckOpen
  rw [← Nat.add_zero 1]
  refine leafStarts_stateBind h1 fun _ => ?_
  refine hz (leafStarts_liftS _) fun _ => ?_
  refine hz (leafStarts_liftS _) fun _ => ?_
  refine hz (leafStarts_liftS _) fun _ => ?_
  refine hz (hrec _ fun _ h => by cases h) fun _ => ?_
  refine hz (leafStarts_liftS _) fun _ => ?_
  refine hz (hrec _ fun _ h => by cases h) fun _ => ?_
  exact hz (leafStarts_set _) fun _ => leafStarts_statePure _

omit [Fintype E] [DecidableEq E] in
theorem leafStarts_recHead (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    ∀ st, LeafStarts 0 ((recHead K circuits settings ctx parameter jobs).run st).run.run := by
  have hz : ∀ {γ δ : Type} {x : StateT (ℕ × ℕ) (RecM C E) γ} {f : γ → StateT (ℕ × ℕ) (RecM C E) δ},
      (∀ st, LeafStarts 0 (x.run st).run.run) → (∀ a st, LeafStarts 0 ((f a).run st).run.run) →
      ∀ st, LeafStarts 0 ((x >>= f).run st).run.run := fun hx hf st => leafStarts_stateBind hx hf st
  unfold recHead
  refine hz leafStarts_get fun _ => ?_
  refine hz (leafStarts_liftS _) fun _ => ?_
  refine hz (leafStarts_liftS _) fun _ => ?_
  exact hz (leafStarts_liftS _) fun _ => leafStarts_statePure _

omit [Fintype E] [DecidableEq E] in
theorem leafStarts_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    ∀ st, LeafStarts 1 ((recBatch K circuits settings ctx parameter jobs).run st).run.run := by
  rw [recBatch_eq_head]
  intro st
  simpa only [Nat.zero_add] using leafStarts_stateBind (leafStarts_recHead K circuits settings ctx parameter jobs)
    (fun h => leafStarts_recCheckOpen K h.1 h.2) st

omit [Fintype E] [DecidableEq E] in
/-- Each leaf of the recorded prefix up to the start of the check of batch `k` holds at most `k` starts. -/
theorem leafStarts_recPrefix (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) (st : ℕ × ℕ) :
    LeafStarts k ((recPrefix K circuits settings k i keys jobs).run st).run.run := by
  unfold recPrefix
  refine LeafStarts.mono (m := 0 + (k + 0)) ?_ (by omega)
  refine leafStarts_stateBind (leafStarts_liftS _) (fun prss => ?_) st
  refine leafStarts_stateBind (fun st' => ?_) (fun outs => ?_)
  · refine (leafStarts_mapM _ (leafStarts_recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter) _ st').mono ?_
    rw [List.length_take, Nat.mul_one]
    exact Nat.min_le_left _ _
  · intro st'
    simpa only [Nat.zero_add] using leafStarts_stateBind (leafStarts_recHead K circuits settings _ _ _)
      (fun h => leafStarts_statePure _) st'

omit [Fintype E] [DecidableEq E] in
/-- The head of a recorded batch takes its AND layers and `Rerand`, and it records nothing. -/
theorem timedLog_recHead {γ : Type} (ctx : Context C) (parameter : PublicParameter) (jobs : List Job)
    (f : BatchStart C × ℕ → γ) (st : ℕ × ℕ) :
    TimedLog (Stop 0) (Full 0 0) (headRounds settings.mode (jobs.map (circuits parameter ·.kind)))
      ((recHead K circuits settings ctx parameter jobs >>= fun h => pure (f h)).run st).run.run := by
  obtain ⟨label, k⟩ := st
  simp only [recHead, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, RecM.liftS, StateT.run_mk,
    bind_assoc, StateT.run_pure]
  rw [headRounds, ← Nat.zero_add (_ * _ + 1), ← Nat.add_zero (_ * _ + 1)]
  refine timedLog_lift_bind (timed_pair (timed_inputShares ctx jobs) _) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  rw [Nat.add_assoc]
  refine timedLog_lift_bind (timed_pair (runTimed_recLayers K ctx settings.mode _ _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₁ => ?_
  rw [← Nat.add_zero 1]
  refine timedLog_lift_bind (timed_pair (runTimed_realRerand K ctx settings.mode _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₂ => ?_
  rw [run_recPure]
  exact TimedLog.done _ ⟨rfl, rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The recorded prefix up to the start of the check of batch `k` takes `prefixRounds` rounds. An abort
keeps at most `k` openings, and a result has `k` starts and `k` openings. -/
theorem timedLog_recPrefix (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (hk : k < (chunks settings.batchSize jobs).length) (st : ℕ × ℕ) :
    TimedLog (Stop k) (Full k k) (prefixRounds circuits settings keys.parameter jobs k)
      ((recPrefix K circuits settings k i keys jobs).run st).run.run := by
  have hlen : ((chunks settings.batchSize jobs).take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk.le]
  simp only [recPrefix, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
  unfold prefixRounds stopRounds
  rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  refine timedLog_lift_bind (timed_pair (timed_prssSetup i) st) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  have hb := timedLog_recBatches K circuits settings ⟨i, keys, p.1⟩ keys.parameter
    ((chunks settings.batchSize jobs).take k) p.2
  rw [hlen] at hb
  refine timedLog_recBind (a₂ := 0) (s₂ := 0) (o₂ := 0) hb (fun c => ?_) le_rfl (by omega) (by omega) (by omega)
  have h := timedLog_recHead K circuits settings ⟨i, keys, p.1⟩ keys.parameter ((chunks settings.batchSize jobs)[k])
    (fun h => (p.1, c.1, h)) c.2
  rw [StateT.run_bind] at h
  exact h

end StartsBatch

/-! ## The recorded prefix and the cut -/

section PrefixCut

open RecordedOpening

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The start of the check at which an outcome of a program stops, with `some none` for an end with
no stop and `none` for an abort. -/
def cutStop {α : Type} (o : Option (CutOf C E α)) : Option (Option (CheckPoint C)) :=
  o.map fun r => r.elim (fun _ => none) fun pr => some pr.1

/-- The start of the check of a recorded start. -/
def pointOf (b : BatchStart C) : CheckPoint C :=
  ⟨b.ctx, batchTuples K b.mode b.circuits b.inputs b.zs b.v', b.state⟩

omit [Fintype E] [DecidableEq E] in
theorem cutStop_bind {α β : Type} (x : Paused K α) (f : α → Paused K β) :
    cutStop <$> (x >>= f).run.run = x.run.run >>= fun o => match o with
      | none => pure none
      | some (.inl a) => cutStop <$> (f a).run.run
      | some (.inr pr) => pure (some (some pr.1)) := by
  rw [Paused.run_bind, OptionT.run_bind, Option.elimM, map_bind]
  refine bind_congr fun o => ?_
  rcases o with _ | a | pr
  · simp [cutStop]
  · rfl
  · simp [cutStop]

omit [Fintype E] [DecidableEq E] in
theorem cutStop_lift {α : Type} (p : PartyM C E RealSpec α) :
    (Paused.lift (K := K) p).run.run = Option.map Sum.inl <$> p.run := by
  rw [Paused.lift, OptionT.run_map]

omit [Fintype E] [DecidableEq E] in
/-- The batch that stops stops at the start of the check of the recorded head. -/
theorem cutStop_cutBatch {β : Type} (ctx : Context C) (parameter : PublicParameter) (jobs : List Job)
    (f : Option (List (List Bit)) → CutM K β) (st : ℕ × ℕ) :
    cutStop <$> ((cutBatch K circuits settings ctx parameter jobs >>= f).run st).run.run =
      Option.map (fun h => some (pointOf K h.1.1)) <$>
        ((dropRecS (recHead K circuits settings ctx parameter jobs)).run st).run := by
  unfold cutBatch recHead
  simp only [bind_assoc, MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_get, dropRecS_liftS]
  obtain ⟨label, k⟩ := st
  simp only [StateT.run_bind, StateT.run_get, pure_bind, CutM.lift_run, StateT.run_lift, Paused.run_bind,
    Paused.lift, Paused.stop, map_bind, map_pure, bind_assoc, StateT.run_pure, OptionT.run_bind,
    OptionT.run_pure, Option.elimM]
  refine bind_congr fun inputs => ?_
  rcases inputs with _ | inputs
  · simp [cutStop]
  simp only [Option.elim]
  rw [runJobsHead_eq, StateT.run_bind, foldlM_layerBody_eq, StateT.run_map]
  simp only [OptionT.run_bind, Option.elimM, map_bind, bind_map_left, bind_assoc]
  refine bind_congr fun z => ?_
  rcases z with _ | z
  · simp [cutStop]
  simp only [Option.elim, StateT.run_bind, StateT.run_pure, OptionT.run_bind, Option.elimM, bind_assoc, map_bind]
  refine bind_congr fun y => ?_
  rcases y with _ | y
  · simp [cutStop]
  · simp [cutStop, pointOf, batchTuples]

omit [Fintype E] [DecidableEq E] in
/-- The batches of a ceremony that stops at the tag `k'`, from the tag `k' - pre.length`, stop at the
start of the check of the recorded head of the batch after `pre`. -/
theorem cutStop_batches {β : Type} (k' : ℕ) (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (js : List Job)
    (suf : List (List Job)) :
    ∀ (pre : List (List Job)) (st : ℕ × ℕ) (g : List (Option (List (List Bit))) → CutM K β), st.2 + pre.length = k' →
      cutStop <$> (((pre ++ js :: suf).mapM (fun js => (do
          let (_, tag) ← get
          if tag = k' then cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter js
          else CutM.lift (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter js) : CutM K _)) >>= g).run
          st).run.run =
        Option.map (fun x => some (pointOf K x.1.2.1)) <$> ((pre.mapM (realBatch K circuits settings.mode ⟨i, keys, prss⟩
          keys.parameter) >>= fun outs => dropRecS (recHead K circuits settings ⟨i, keys, prss⟩ keys.parameter js) >>=
            fun h => pure (outs, h)).run st).run
  | [], ⟨label, t⟩, g, hk => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    rw [List.nil_append, List.mapM_cons]
    simp only [bind_assoc]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    rw [ite_eq_left rfl, cutStop_cutBatch, List.mapM_nil, pure_bind, StateT.run_bind, OptionT.run_bind, Option.elimM,
      map_bind, map_eq_bind_pure_comp]
    refine bind_congr fun o => ?_
    rcases o with _ | o <;> rfl
  | b :: pre, ⟨label, t⟩, g, hk => by
    simp only [List.length_cons] at hk
    rw [List.cons_append, List.mapM_cons, List.mapM_cons]
    simp only [bind_assoc]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    rw [ite_eq_right (by omega : t ≠ k'), StateT.run_bind, StateT.run_bind, CutM.lift_run, realBatch_run,
      cutStop_bind, cutStop_lift, bind_map_left]
    simp only [OptionT.run_bind, Option.elimM, bind_assoc, map_bind, OptionT.run_pure, pure_bind]
    refine bind_congr fun o => ?_
    rcases o with _ | inputs
    · rfl
    simp only [Option.elim, bind_assoc, map_bind]
    refine bind_congr fun o => ?_
    rcases o with _ | r
    · rfl
    have ih := cutStop_batches k' i keys prss js suf pre (r.2.label, t + 1)
      (fun x => g (some r.1 :: x)) (by simp only; omega)
    refine Eq.trans ?_ (ih.trans ?_)
    · rw [pure_bind]
      rfl
    have hmap : ∀ {δ : Type} (M : StateT (ℕ × ℕ) (PartyM C E RealSpec) (List (Option (List (List Bit)))))
        (R : StateT (ℕ × ℕ) (PartyM C E RealSpec) δ) (a : Option (List (List Bit))),
        (do let x ← M; let h ← R; pure (a :: x, h)) =
          (fun y => (a :: y.1, y.2)) <$> (do let x ← M; let h ← R; pure (x, h)) := by
      intro δ M R a
      simp only [map_bind, map_pure]
    dsimp only
    rw [hmap, StateT.run_map, OptionT.run_map, Functor.map_map]
    congr 1
    funext a
    cases a <;> rfl

/-- The cut of one ceremony at check `k` stops at the start of the check of the recorded prefix. With
the records dropped and the rest of the cut program dropped, the two programs have the same stops. -/
theorem cutStop_cutCeremony (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hkeys : c.keys i = some keys) (hk : k < (chunks settings.batchSize c.jobs).length) :
    cutStop <$> (cutCeremony K circuits settings k i c).run =
      Option.map (fun x => some (pointOf K x.1.2.2.1)) <$>
        ((dropRecS (recPrefix K circuits settings k i keys c.jobs)).run c.counters).run := by
  have hsplit : chunks settings.batchSize c.jobs = (chunks settings.batchSize c.jobs).take k ++
      (chunks settings.batchSize c.jobs).getD k [] :: (chunks settings.batchSize c.jobs).drop (k + 1) := by
    rw [List.getD_eq_getElem _ _ hk, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : ((chunks settings.batchSize c.jobs).take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk.le]
  simp only [cutCeremony, hkeys]
  rw [SetupCut.cutRun_eq, StateT.run_bind, CutM.lift_run, cutStop_bind, cutStop_lift, bind_map_left]
  unfold recPrefix
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_liftS, monadHom_list_mapM, dropRecS_recBatch]
  rw [StateT.run_bind, StateT.run_lift]
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, map_bind, OptionT.run_pure, pure_bind]
  refine bind_congr fun o => ?_
  rcases o with _ | prss
  · simp
  simp only [Option.elim]
  unfold SetupCut.cutBatches batched
  rw [hsplit]
  have h := cutStop_batches K circuits settings (c.counters.2 + k) i keys prss
    ((chunks settings.batchSize c.jobs).getD k []) ((chunks settings.batchSize c.jobs).drop (k + 1))
    ((chunks settings.batchSize c.jobs).take k) c.counters
    (fun outs => pure ((outs.foldlM (fun acc batch => batch.map (acc ++ ·)) []))) (by rw [hlen])
  refine h.trans ?_
  have hmap : ∀ {δ : Type} (M : StateT (ℕ × ℕ) (PartyM C E RealSpec) (List (Option (List (List Bit)))))
      (R : StateT (ℕ × ℕ) (PartyM C E RealSpec) δ),
      (do let x ← M; let h ← R; pure (prss, x, h)) =
        (fun y => (prss, y.1, y.2)) <$> (do let x ← M; let h ← R; pure (x, h)) := by
    intro δ M R
    simp only [map_bind, map_pure]
  rw [← hsplit, hmap, StateT.run_map, OptionT.run_map, Functor.map_map]
  congr 1
  funext a
  cases a <;> rfl

/-- The rest of the recorded ceremony after its prefix, with the end of `recCeremony`. -/
def recFinish (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (p : (PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) × (ℕ × ℕ)) :
    RecM C E CeremonyResult :=
  (recRest K circuits settings k i keys jobs p.1).run p.2 >>= fun q => q.1.elim failure fun outputs => pure (outputs, q.2)

omit [Fintype E] [DecidableEq E] in
/-- The recorded program of one ceremony is its recorded prefix up to the start of the check of
batch `k`, and then its rest. -/
theorem recCeremony_eq (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hkeys : c.keys i = some keys) (hk : k < (chunks settings.batchSize c.jobs).length) :
    (recCeremony K circuits settings i c).run.run =
      ((recPrefix K circuits settings k i keys c.jobs).run c.counters).run.run >>=
        RecordedOpening.recCont (recFinish K circuits settings k i keys c.jobs) := by
  simp only [recCeremony, hkeys]
  rw [recRun_eq_prefix K circuits settings k i keys c.jobs hk, StateT.run_bind, bind_assoc,
    RecordedOpening.run_recBind]
  rfl

/-- On each result of the recorded prefix, the start of the check of batch `k` is a start of the cut
program at check `k`. Its context is that of the operator with the PRSS keys of the prefix, its tuples
have the counts of the head of batch `k`, and its run state holds the filled history of its tuples at
the label of the batches before `k` and the tag of batch `k`. -/
theorem recPrefix_pointAt (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hkeys : c.keys i = some keys) (hk : k < (chunks settings.batchSize c.jobs).length)
    (x : Option ((PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) × (ℕ × ℕ)) × Record C E)
    (hx : x ∈ support ((recPrefix K circuits settings k i keys c.jobs).run c.counters).run.run)
    (d : (PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) × (ℕ × ℕ)) (hd : x.1 = some d) :
    ∃ prss, PointAt K i ⟨i, keys, prss⟩
      (headCounts (((chunks settings.batchSize c.jobs).getD k []).map (circuits keys.parameter ·.kind)))
      (c.counters.1 + (((chunks settings.batchSize c.jobs).take k).map (jobLabel circuits keys.parameter)).sum)
      (c.counters.2 + k) (pointOf K d.1.2.2.1) := by
  have h1 : some d ∈ support ((dropRecS (recPrefix K circuits settings k i keys c.jobs)).run c.counters).run := by
    rw [← hd]
    change x.1 ∈ support (Prod.fst <$> ((recPrefix K circuits settings k i keys c.jobs).run c.counters).run.run)
    rw [support_map]
    exact ⟨x, hx, rfl⟩
  have h2 : some (some (pointOf K d.1.2.2.1)) ∈ support (cutStop <$> (cutCeremony K circuits settings k i c).run) := by
    rw [cutStop_cutCeremony K circuits settings k i c keys hkeys hk, support_map]
    exact ⟨some d, h1, rfl⟩
  rw [support_map] at h2
  obtain ⟨o, ho, hstop⟩ := h2
  simp only [cutCeremony, hkeys] at ho
  rcases o with _ | ⟨r⟩ | ⟨point, rest⟩
  · cases hstop
  · cases hstop
  · simp only [cutStop, Option.map_some, Sum.elim_inr, Option.some.injEq] at hstop
    obtain ⟨prss, pre, js, suf, hsplit, hlen, hpoint⟩ :=
      (cutWalk_cutRun K circuits settings (c.counters.2 + k) i keys c.jobs c.counters _ ho).2 point rest rfl
    have hpre : pre.length = k := by omega
    have htake : (chunks settings.batchSize c.jobs).take k = pre := by
      rw [hsplit, ← hpre, List.take_left]
    have hget : (chunks settings.batchSize c.jobs).getD k [] = js := by
      rw [hsplit, ← hpre, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp
    rw [htake, hget, ← hstop]
    exact ⟨prss, hpoint⟩

/-- The record of the start of the check of `b` and the check, as `recCheckOpen` runs them, with the
counters `st` kept. -/
def recCheck (b : BatchStart C) (st : ℕ × ℕ) : RecM C E ((Unit × RunState C) × (ℕ × ℕ)) :=
  RecM.record [.start b] >>= fun _ => RecM.lift (do
    let a ← ((realRunBuildingBlocks (G := RealSpec) K b.ctx b.mode).verify
      (batchTuples K b.mode b.circuits b.inputs b.zs b.v')).run b.state
    pure (a, st))

/-- The rest of the recorded ceremony after the check of batch `k`. It is the code of `recCheckOpen`
after the check, then the later batches, then the end of `recCeremony`. -/
def finRest (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (p : (PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) × (ℕ × ℕ))
    (x : (Unit × RunState C) × (ℕ × ℕ)) : RecM C E CeremonyResult := do
  let x₁ ← RecM.lift (do
    let a ← oracleStep (C.terms.mapM fun T =>
      hashQuery (.copy (vector (outputsOf p.1.2.2.1.circuits).length (p.1.2.2.1.v' T))))
    pure (a, x.2))
  let x₂ ← RecM.lift (do
    let a ← exchange (repOutbox K p.1.2.2.1.ctx.self p.1.2.2.1.v' (outputsOf p.1.2.2.1.circuits).length x₁.1)
    pure (a, x₁.2))
  RecM.record [.opened p.1.2.2.1.v' x₂.1]
  let x₄ ← RecM.lift (do
    let a ← repRest K p.1.2.2.1.ctx.self p.1.2.2.1.v' (outputsOf p.1.2.2.1.circuits).length x₂.1
    pure (a, x₂.2))
  RecM.record [.output (ThresholdLeanXmssSecurity.assemble p.1.2.2.1.circuits x₄.1)]
  let y ← (set (x.1.2.label, p.1.2.2.2 + 1) : StateT (ℕ × ℕ) (RecM C E) PUnit).run x₄.2
  let z ← (((chunks settings.batchSize jobs).drop (k + 1)).mapM
    (recBatch K circuits settings ⟨i, keys, p.1.1⟩ keys.parameter)).run y.2
  let q ← (pure ((p.1.2.1 ++ some (ThresholdLeanXmssSecurity.assemble p.1.2.2.1.circuits x₄.1) :: z.1).foldlM
    (fun acc batch => batch.map (acc ++ ·)) []) : StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit)))).run z.2
  q.1.elim failure fun outputs => pure (outputs, q.2)

omit [Fintype E] [DecidableEq E] in
/-- The rest after the prefix is the record of the start and the check, and then the rest after the
check. -/
theorem recFinish_eq (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (p : (PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) × (ℕ × ℕ)) :
    recFinish K circuits settings k i keys jobs p =
      recCheck K p.1.2.2.1 p.2 >>= finRest K circuits settings k i keys jobs p := by
  unfold recFinish recRest recCheckOpen recCheck finRest
  simp only [StateT.run_bind, StateT.run_lift, RecM.liftS, StateT.run_mk, bind_assoc, pure_bind]

omit [Fintype E] [DecidableEq E] in
/-- The record of the start and the check take the check rounds. Each leaf holds the record of the
start only. -/
theorem timedLog_recCheck (b : BatchStart C) (st : ℕ × ℕ) :
    TimedLog (fun x : Option ((Unit × RunState C) × (ℕ × ℕ)) × Record C E => x.1 = none ∧ x.2 = [.start b])
      (fun x => x.1.isSome ∧ x.2 = [.start b]) (checkLabels (tupleCount b.circuits)) (recCheck K b st).run.run := by
  have hcheck := runTimed_realCheck (G := RealSpec) K b.ctx (batchTuples K b.mode b.circuits b.inputs b.zs b.v')
    b.state
  rw [RecordedOpening.sum_batchTuples] at hcheck
  have h := timedLog_lift_bind (A := fun x : Option ((Unit × RunState C) × (ℕ × ℕ)) × Record C E =>
      x.1 = none ∧ x.2 = []) (B := fun x => x.1.isSome ∧ x.2 = []) (n := 0)
    (f := fun a => (pure a : RecM C E ((Unit × RunState C) × (ℕ × ℕ)))) (timed_pair hcheck st) ⟨rfl, rfl⟩
    (fun a => by rw [run_recPure]; exact TimedLog.done _ ⟨rfl, rfl⟩)
  rw [bind_pure] at h
  unfold recCheck
  rw [run_recRecord_bind]
  exact h.map _ (fun x hx => ⟨hx.1, by rw [hx.2]; rfl⟩) fun x hx => ⟨hx.1, by rw [hx.2]; rfl⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A record before the rest of a recorded bind moves into the rest. -/
theorem map_prepend_recCont {α β : Type} (w : Record C E) (A : OracleComp (PartySpec C E RealSpec) (Option α × Record C E))
    (f : α → RecM C E β) :
    (fun y => (y.1, w ++ y.2)) <$> (A >>= recCont f) = ((fun y => (y.1, w ++ y.2)) <$> A) >>= recCont f := by
  rw [map_bind, bind_map_left]
  refine bind_congr fun y => ?_
  rcases y with ⟨_ | a, w'⟩
  · simp [recCont]
  · simp only [recCont, Functor.map_map, List.append_assoc]

omit [Fintype E] [DecidableEq E] in
/-- With its record dropped and its result forgotten, the check part of a recorded start is the
program of the pilot at that start. -/
theorem dropRec_recCheck (b : BatchStart C) (st : ℕ × ℕ) (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C)
    (i : C.Party) (x : List (Tuple C)) (L tg : ℕ) (hctx : b.ctx = pilotContext keys prss i)
    (hx : batchTuples K b.mode b.circuits b.inputs b.zs b.v' = x) (hstate : b.state = ⟨filledHistory K i x, L, tg⟩) :
    (fun _ => ()) <$> dropRec (recCheck K b st) =
      (check K (pilotContext keys prss i) (realCheckBuildingBlocks K (pilotContext keys prss i)) x).run'
        ⟨filledHistory K i x, L, tg⟩ := by
  unfold recCheck
  rw [MonadHom.mmap_bind, dropRec_record, pure_bind, dropRec_lift, StateT.run'_eq, map_bind]
  simp only [map_pure]
  rw [← hstate, ← hx, ← hctx, map_eq_bind_pure_comp]
  rfl

end PrefixCut

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.timed_cutCeremony' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.timed_cutCeremony
