import ThresholdLeanXmssSecurity.Proof.LifetimeRunBoundary
import ThresholdLeanXmssSecurity.Proof.LifetimeKeysApartPath
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The setup boundary of a lifetime run

The concrete setup adversary runs the lifetime prefix once and keeps its private stream table.
Its state type omits suspended honest programs, so selected-run private parts cannot be stored
there. Exact program equalities reconstruct the source suspension across intervening requests.

For every row/cache event false on empty rows, the original selected setup is dominated by this
external setup. Its complete counted prefix has budget `Q + n²` under the original lifetime
query-bound premise. The resulting separation and setup-hit estimates are the S1 and S2 terms.

The module reuses the actual `runTo`/setup split, VCVio support and probability bind laws,
`continuationOracle_simulate`, the setup path counts, and the exact hybrid budget. No lifetime
scheduler analogue was found in leanVM.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace ThresholdLeanXmssSecurity.LifetimeSetupBridge

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Replace suspended programs, retaining the running tree and its fuel. -/
def replaceSteps (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) : LifetimeState C E :=
  { st with running := st.running.map fun r => (r.1, r.2.1, steps) }

@[simp] theorem replaceSteps_sign (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) : (replaceSteps steps st).sign = st.sign := rfl

@[simp] theorem replaceSteps_top (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) : (replaceSteps steps st).top = st.top := rfl

@[simp] theorem replaceSteps_bottom (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) : (replaceSteps steps st).bottom = st.bottom := rfl

@[simp] theorem replaceSteps_running_tree (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) : (replaceSteps steps st).running.map Prod.fst =
      st.running.map Prod.fst := by
  simp [replaceSteps, Option.map_map, Function.comp_def]

@[simp] theorem replaceSteps_running_none (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) : (replaceSteps steps st).running = none ↔ st.running = none := by
  simp [replaceSteps]

@[simp] theorem replaceSteps_blockedSign (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) (i : C.Party) (e : KeyIndex) :
    LifetimeProof.blockedSign (replaceSteps steps st) i e = LifetimeProof.blockedSign st i e := by
  simp [LifetimeProof.blockedSign]

section Requests

variable {ι : Type} {spec : OracleSpec ι}
variable (base : Roles C (OracleComp spec)) (keys : C.Party → Keys C)
variable (value : Point → OracleComp spec Digest)

/-- The signing dealer reads no suspended ceremony program. -/
theorem signerDealt_replaceSteps (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) (i : C.Party) :
    ThresholdLeanXmss.signerDealt (fun oa => base.honest (liftComp oa _)) keys value (replaceSteps steps st) i =
      ThresholdLeanXmss.signerDealt (fun oa => base.honest (liftComp oa _)) keys value st i := rfl

/-- Signing commutes with replacing the suspended ceremony programs. -/
theorem signAs_replaceSteps (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) (i : C.Party) (q : TsigQuery C) :
    LifetimeProof.signAs base keys value i q (replaceSteps steps st) =
      (fun r => (r.1, replaceSteps steps r.2)) <$> LifetimeProof.signAs base keys value i q st := by
  unfold LifetimeProof.signAs
  rw [signerDealt_replaceSteps, replaceSteps_sign, map_bind]
  apply bind_congr
  intro r
  simp only [map_pure]
  rfl

variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (Ro : ℕ → Roles C (OracleComp spec)) (D : C.Coalition) (h : C.Party)

/-- A non-round request while a ceremony runs commutes with replacing its suspended programs.
In particular, another start is denied on both sides. -/
theorem request_replaceSteps (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) (hrun : st.running ≠ none) (q : LifetimeQuery C E)
    (hq : ∀ sent, q ≠ .round sent) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run
        (replaceSteps steps st) =
      (fun r => (r.1, replaceSteps steps r.2)) <$>
        (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st := by
  cases q with
  | sign q =>
    cases q with
    | corrupt i => simp [lifetimeOraclesWith, StateT.run_pure]
    | tree b => exact signAs_replaceSteps base keys value steps st h (.tree b)
    | round1 i J e message =>
      rw [LifetimeProof.run_round1, LifetimeProof.run_round1, replaceSteps_blockedSign]
      split
      · simp only [map_pure]
      · exact signAs_replaceSteps base keys value steps
          { st with signed := insert (treeOf e) st.signed } i (.round1 i J e message)
    | round2 i J e message parts =>
      rw [LifetimeProof.run_round2, LifetimeProof.run_round2, replaceSteps_blockedSign]
      split
      · simp only [map_pure]
      · exact signAs_replaceSteps base keys value steps
          { st with signed := insert (treeOf e) st.signed } i (.round2 i J e message parts)
  | publicKey => simp [lifetimeOraclesWith, StateT.run_get, LifetimeState.publicKey]
  | start tree =>
    have hs : ¬ LifetimeProof.canStart attempts D st tree := fun h => hrun h.1
    have hs' : ¬ LifetimeProof.canStart attempts D (replaceSteps steps st) tree :=
      fun h => hrun ((replaceSteps_running_none steps st).mp h.1)
    rw [LifetimeProof.run_start, LifetimeProof.run_start, if_pos hs', if_pos hs, map_pure]
  | round sent => exact False.elim (hq sent rfl)

end Requests


section Pauses

open LifetimeRunBoundary LifetimePrfTransportProof LifetimeHybridOrder

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (keys : C.Party → Keys C) (h : C.Party)

/-- Before the next round, a running ceremony remains suspended. -/
theorem nonround_running (st : LifetimeState C E) (hrun : st.running ≠ none)
    (t : (LocalSpec C + LifetimeSpec C E).Domain)
    (ht : ∀ sent, t ≠ .inr (.round sent))
    (r : _ × LifetimeState C E)
    (hr : r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run st)) :
    r.2.running = st.running := by
  rcases t with t | q
  · change r ∈ support ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) at hr
    rw [StateT.run_lift] at hr
    obtain ⟨a, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    change r = (a, st) at hr
    rw [hr]
  · by_cases hs : ∃ tree, q = .start tree
    · obtain ⟨tree, rfl⟩ := hs
      rw [oracles4_inr, LifetimeProof.run_start, if_pos (fun hc => hrun hc.1)] at hr
      change r = (none, st) at hr
      rw [hr]
    · exact lifetime_running_eq D n K circuits settings attempts keys h q
        (fun tree he => hs ⟨tree, he⟩) (fun sent he => ht sent (congrArg Sum.inr he)) st r hr


/-- Between rounds, both the run counter and the complete suspension remain unchanged. -/
theorem runTo_frame (prog : Program C E) (st : LifetimeState C E) (hrun : st.running ≠ none)
    (r : Pause C E × LifetimeState C E)
    (hr : r ∈ support ((runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st)) :
    r.2.runCount = st.runCount ∧ r.2.running = st.running := by
  have inv := runTo_quietP (P := fun _ => False)
    (oracles4 K circuits settings attempts D n keys h) RoundStop
    (fun s => s.runCount = st.runCount ∧ s.running = st.running) ?_ prog st ⟨rfl, rfl⟩
  · exact (inv.2 r hr).1
  · intro t s hs ht
    refine ⟨?_, fun out hout => ?_⟩
    · convert isQueryBoundP_false ((oracles4 K circuits settings attempts D n keys h t).run s) 0 using 1
    · have hne : s.running ≠ none := by rw [hs.2]; exact hrun
      have hc := oracles4_runCount K circuits settings attempts D n keys h t s out hout
      refine ⟨?_, (nonround_running K circuits settings attempts D n keys h s hne t
        (fun sent he => ht (.round sent) he trivial) out hout).trans hs.2⟩
      rcases hc with hc | ⟨tree, _, hopen, _⟩
      · exact hc.trans hs.1
      · exact False.elim (hne hopen.1)

/-- The complete segment between rounds commutes with erasing the selected run's programs. -/
theorem runTo_replaceSteps (steps : C.Party → Step C E RealSpec TreeOutput)
    (prog : Program C E) (st : LifetimeState C E) (hrun : st.running ≠ none) :
    (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run
        (replaceSteps steps st) =
      (fun r => (r.1, replaceSteps steps r.2)) <$>
        (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st := by
  induction prog using OracleComp.recOn generalizing st with
  | pure f => simp [runTo, StateT.run_pure]
  | queryBind t k ih =>
    rcases t with t | q
    · simp only [runTo, StateT.run_bind]
      have hh : ∀ s : LifetimeState C E,
          (oracles4 K circuits settings attempts D n keys h (.inl t)).run s =
            (advCopy4 (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, s)) :=
        fun s => rfl
      simp only [hh, bind_assoc, pure_bind, map_bind]
      exact bind_congr fun a => ih a st hrun
    · by_cases hq : ∃ sent, q = .round sent
      · obtain ⟨sent, rfl⟩ := hq
        simp [runTo, RoundStop, StateT.run_pure]
      · have hs : ∀ s : LifetimeState C E, ¬ RoundStop s q := by
          intro s
          cases q <;> simp_all [RoundStop]
        simp only [runTo, StateT.run_bind, StateT.run_get, pure_bind, if_neg (hs _)]
        rw [oracles4_inr, request_replaceSteps base4 keys (value4 D keys) K circuits settings
          attempts (roles4 n) D h steps st hrun q (fun sent he => hq ⟨sent, he⟩)]
        rw [map_bind, bind_map_left]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro r hr
        exact ih r.1 r.2 (by
          rw [nonround_running K circuits settings attempts D n keys h st hrun (.inr q)
            (fun sent he => hq ⟨sent, Sum.inr.inj he⟩) r hr]
          exact hrun)

/-- A running selected reveal cannot fail the segment check after intervening non-round queries. -/
theorem revealSegment_running (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (prog : Program C E) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (hc : CountIs (n + 1) st)
    (hs : st.running = some (tree, fuel, fun i => suspendStep (k i)
      (prssRevealStep D active parts committed i))) :
    revealSegment K circuits settings attempts D n keys h k active parts committed prog st =
      ((runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st >>= fun r =>
        r.1.atRound (pure ((none, r.1.rest), r.2)) fun sent next => do
          let rows ← targetCopy4 (prssRevealRows D active parts committed sent)
          let steps := fun i => suspendStep (k i) (prssFinishStep i (rows i))
          pure ((some rows, next (some (toCoalition D steps))),
            ({ r.2 with running := some (tree, fuel - 1, steps) }).settle D)) := by
  unfold revealSegment
  apply OracleComp.bind_congr_of_forall_mem_support
  intro r hr
  have hf := runTo_frame K circuits settings attempts D n keys h prog st (by rw [hs]; simp) r hr
  have hrunning := hf.2.trans hs
  have hcount : CountIs (n + 1) r.2 := hf.1.trans hc
  cases r.1 with
  | done f => rfl
  | wait q next =>
    cases q <;> try rfl
    simp only [Pause.atRound, hrunning, hcount, and_self, if_true]


/-- Suspending the selected continuation preserves the actual commit inbox to the coalition. -/
theorem initial_visible (data : C.Party → Parts C × List HashOutput)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    toCoalition D (fun i => suspendStep (k i) (prssInitialSteps D data i)) = prssCommitVisible D data := by
  unfold toCoalition
  simp only [suspendStep_outbox]
  exact prssInitialSteps_outbox D data

/-- The actual reveal inbox likewise carries no extra suspended-state information. -/
theorem reveal_visible (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    toCoalition D (fun i => suspendStep (k i) (prssRevealStep D active parts committed i)) =
      prssRevealVisible D active parts := by
  unfold toCoalition
  simp only [suspendStep_outbox]
  exact prssRevealStep_outbox D active parts committed

/-- The same exact check at the selected commit. -/
theorem commitSegment_running (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (data : C.Party → Parts C × List HashOutput) (prog : Program C E)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (hc : CountIs (n + 1) st)
    (hs : st.running = some (tree, fuel, fun i => suspendStep (k i) (prssInitialSteps D data i))) :
    commitSegment K circuits settings attempts D n keys h k data prog st =
      (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st >>= fun r =>
        r.1.atRound (pure ((none, r.1.rest), r.2)) fun sent next =>
          let committed := prssCommitInbox D data sent
          let active := fun i => (C.parties.any fun j => Msg.isAbort (committed i j)) = false
          let steps := fun i => suspendStep (k i)
            (prssRevealStep D active (fun j => (data j).1) committed i)
          revealSegment K circuits settings attempts D n keys h k active (fun j => (data j).1)
            committed (next (some (toCoalition D steps)))
            (({ r.2 with running := some (tree, fuel - 1, steps) }).settle D) := by
  unfold commitSegment
  apply OracleComp.bind_congr_of_forall_mem_support
  intro r hr
  have hf := runTo_frame K circuits settings attempts D n keys h prog st (by rw [hs]; simp) r hr
  have hrunning := hf.2.trans hs
  have hcount : CountIs (n + 1) r.2 := hf.1.trans hc
  cases r.1 with
  | done f => rfl
  | wait q next =>
    cases q <;> try rfl
    simp only [Pause.atRound, hrunning, hcount, and_self, if_true]


/-- Run `n` has ended, and every subsequent running ceremony has a larger run counter. -/
def PastSelected (st : LifetimeState C E) : Prop :=
  n + 1 ≤ st.runCount ∧ (st.runCount = n + 1 → st.running = none)


/-- An all-inactive commit settles the selected run before the reveal segment begins. -/
theorem inactive_pastSelected (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (hc : CountIs (n + 1) st) (ha : ∀ i, i ∉ D.1 → ¬ active i) :
    PastSelected n (({ st with running := some (tree, fuel,
      fun i => suspendStep (k i) (prssRevealStep D active parts committed i)) }).settle D) := by
  have hall : ∀ i, i ∉ D.1 → (suspendStep (k i) (prssRevealStep D active parts committed i)).isDone := by
    simpa only [suspendStep_isDone, prssRevealStep_all_done] using ha
  refine ⟨?_, fun _ => ?_⟩
  · rw [LifetimeProof.settle_runCount]
    change n + 1 ≤ st.runCount
    exact Nat.le_of_eq hc.symm
  · cases tree <;> simp only [LifetimeState.settle, if_pos (Or.inr hall)]

/-- Non-round interleavings cannot resurrect a settled selected run. -/
theorem runTo_pastSelected (prog : Program C E) (st : LifetimeState C E) (hs : PastSelected n st)
    (r : Pause C E × LifetimeState C E)
    (hr : r ∈ support ((runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st)) :
    PastSelected n r.2 := by
  have inv := runTo_quietP (P := fun _ => False)
    (oracles4 K circuits settings attempts D n keys h) RoundStop (PastSelected n) ?_ prog st hs
  · exact (inv.2 r hr).1
  · intro t s hs ht
    refine ⟨?_, fun out hout => ?_⟩
    · convert isQueryBoundP_false ((oracles4 K circuits settings attempts D n keys h t).run s) 0 using 1
    · have hc := oracles4_frame D n K circuits settings attempts keys h t
        (fun sent he => ht (.round sent) he trivial) s out hout
      rcases hc with ⟨hc, hr⟩ | hc
      · exact ⟨by rw [hc]; exact hs.1, fun he => hr.trans (hs.2 (hc.symm.trans he))⟩
      · have hle := hs.1
        exact ⟨by omega, fun he => by omega⟩

/-- Once the selected run has settled, the reveal segment has no selected reveal rows,
even if its intervening program starts later runs. -/
theorem revealSegment_pastSelected (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (prog : Program C E) (st : LifetimeState C E) (hs : PastSelected n st)
    (out : (Option (RevealRows C) × Program C E) × LifetimeState C E)
    (hout : out ∈ support (revealSegment K circuits settings attempts D n keys h k active
      parts committed prog st)) : out.1.1 = none := by
  unfold revealSegment at hout
  obtain ⟨r, hr, hout⟩ := (mem_support_bind_iff _ _ _).mp hout
  have hafter := runTo_pastSelected K circuits settings attempts D n keys h prog st hs r hr
  cases hp : r.1 with
  | done f =>
    simp only [hp, Pause.atRound] at hout
    change out = ((none, _), _) at hout
    rw [hout]
  | wait q next =>
    cases q <;> simp only [hp, Pause.atRound] at hout
    all_goals try { change out = ((none, _), _) at hout; rw [hout] }
    cases hrun : r.2.running with
    | none =>
      simp only [hrun] at hout
      change out = ((none, _), _) at hout
      rw [hout]
    | some running =>
      obtain ⟨tree, fuel, steps⟩ := running
      have hc : ¬ CountIs (n + 1) r.2 := fun hc =>
        Option.some_ne_none _ (hrun.symm.trans (hafter.2 hc))
      simp only [hrun, hc, false_and, if_false] at hout
      change out = ((none, _), _) at hout
      rw [hout]


end Pauses


section Driver

open LifetimeRunBoundary LifetimePrfTransportProof LifetimeHybridOrder

/-- Lifetime state with no suspended honest program. -/
structure VisibleState (C : Committee) where
  sign : TsigState C
  top : C.Party → Option TopTree
  bottom : C.Party → Fin (2 ^ layerHeight) → Option BottomTree
  topRuns : ℕ
  bottomRuns : Fin (2 ^ layerHeight) → ℕ
  signed : Finset (Fin (2 ^ layerHeight))
  running : Option (ThresholdLeanXmss.Tree × ℕ)

/-- Forget the suspended programs, retaining all other lifetime state. -/
def visibleState (st : LifetimeState C E) : VisibleState C :=
  ⟨st.sign, st.top, st.bottom, st.topRuns, st.bottomRuns, st.signed,
    st.running.map fun r => (r.1, r.2.1)⟩

/-- Restore only inert placeholders. No round is evaluated on these placeholders. -/
def VisibleState.restore (st : VisibleState C) : LifetimeState C E :=
  ⟨st.sign, st.top, st.bottom, st.topRuns, st.bottomRuns, st.signed,
    st.running.map fun r => (r.1, r.2, fun _ => .done none)⟩

theorem restore_visibleState (st : LifetimeState C E) :
    (visibleState st).restore = replaceSteps (fun _ => .done none) st := by
  cases st
  simp [visibleState, VisibleState.restore, replaceSteps, Option.map_map, Function.comp_def]


@[simp] theorem visible_replaceSteps (steps : C.Party → Step C E RealSpec TreeOutput)
    (st : LifetimeState C E) : visibleState (replaceSteps steps st) = visibleState st := by
  cases st
  simp [visibleState, replaceSteps, Option.map_map, Function.comp_def]


/-- Restoring the known suspension after visible erasure recovers the complete state. -/
theorem replace_restore (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput) (hs : st.running = some (tree, fuel, steps)) :
    replaceSteps steps (visibleState st).restore = st := by
  cases st
  simp only [visibleState, VisibleState.restore, replaceSteps]
  simp_all


/-- Advancing the fuel after a public send agrees with erasing the actual next suspension. -/
theorem visible_advance (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (old next : C.Party → Step C E RealSpec TreeOutput)
    (hs : st.running = some (tree, fuel, fun _ => .done none)) :
    visibleState ({ replaceSteps old st with running := some (tree, fuel - 1, next) } : LifetimeState C E) =
      { visibleState st with running := st.running.map fun r => (r.1, r.2.1 - 1) } := by
  cases st
  simp_all [visibleState, replaceSteps]

/-- The pending lifetime query, with only its public continuation and visible state retained. -/
structure Held (C : Committee) (E : Type) where
  keys : C.Party → Keys C
  h : C.Party
  continuation : Option (Sent C E) → Program C E
  state : VisibleState C

/-- Fold the two local copies onto one local oracle. The generated hybrid makes no programming
call; the definition gives such a call the inert answer used by `worldTo4`. -/
abbrev foldWorld : QueryImpl (WorldSpec C) (OracleComp (LocalSpec C)) :=
  LifetimeKeygenHopProof.continuationOracle

/-- The hybrid interpreter, retaining its stream table and erasing only its observation log. -/
def localHybrid (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) : OracleComp (LocalSpec C) (α × StreamCache C) :=
  simulateQ foldWorld ((treeSimErase (simulateQ (hybridImpl D) p)).run table)



theorem localHybrid_pure (D : C.Coalition) {α : Type} (a : α) (table : StreamCache C) :
    localHybrid D (pure a) table = pure (a, table) := by
  simp [localHybrid, treeSimErase_pure]

theorem localHybrid_bind (D : C.Coalition) {α β : Type} (p : OracleComp (Spec4 C) α)
    (k : α → OracleComp (Spec4 C) β) (table : StreamCache C) :
    localHybrid D (p >>= k) table =
      localHybrid D p table >>= fun r => localHybrid D (k r.1) r.2 := by
  simp only [localHybrid, simulateQ_bind, treeSimErase_bind, StateT.run_bind]

theorem foldWorld_free {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (foldWorld (C := C)) (free p) = p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [free_bind, simulateQ_bind]
    have hq : simulateQ (foldWorld (C := C)) (free (OracleComp.lift (OracleSpec.query t))) =
        (OracleComp.lift (OracleSpec.query t) : OracleComp (LocalSpec C) _) :=
      simulateQ_spec_query (foldWorld (C := C)) (Sum.inr t)
    rw [hq]
    exact bind_congr ih

/-- The selected run's honest computations use the same ordinary oracle and leave the retained
stream table untouched. -/
theorem localHybrid_target (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α)
    (table : StreamCache C) :
    localHybrid D (targetCopy4 p) table = (fun a => (a, table)) <$> p := by
  unfold localHybrid
  rw [impl4_targetCopy_free, LifetimeKeygenHopProof.erase_base_honest]
  change simulateQ foldWorld (free p >>= fun a => pure (a, table)) = _
  rw [simulateQ_bind, foldWorld_free]
  simp only [simulateQ_pure, bind_pure_comp]



theorem localHybrid_map (D : C.Coalition) {α β : Type} (f : α → β)
    (p : OracleComp (Spec4 C) α) (table : StreamCache C) :
    localHybrid D (f <$> p) table = (fun r => (f r.1, r.2)) <$> localHybrid D p table := by
  rw [show f <$> p = p >>= fun a => pure (f a) from (bind_pure_comp _ _).symm,
    localHybrid_bind]
  simp only [localHybrid_pure, bind_pure_comp]

/-- Every result of the retained-table local interpretation is a result of the source program. -/
theorem localHybrid_support (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) (r : α × StreamCache C) (hr : r ∈ support (localHybrid D p table)) :
    r.1 ∈ support p := by
  have hr' := support_simulateQ_subset foldWorld _ hr
  change r ∈ support (Prod.fst <$> ((simulateQ (hybridImpl D) p).run table).run) at hr'
  rw [support_map, Set.mem_image] at hr'
  obtain ⟨out, hout, he⟩ := hr'
  exact he ▸ support_emulation (hybridImpl D) p table out hout

/-- Erasing the hybrid log does not create a programming query. -/
theorem hybrid_noProgram (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) :
    IsQueryBoundP ((treeSimErase (simulateQ (hybridImpl D) p)).run table)
      AimedProgramCall 0 := by
  have hlift : ∀ {β : Type} (w : OracleComp (WorldSpec C) β) (table : StreamCache C),
      IsQueryBoundP w AimedProgramCall 0 →
      IsQueryBoundP ((treeSimErase (StateT.lift (liftM w) : EmulationM C β)).run table)
        AimedProgramCall 0 := by
    intro β w table hw
    rw [treeSimErase_lift, StateT.run_lift]
    exact qb0_bind hw (fun _ => isQueryBoundP_pure _ _ 0)
  have hstep : ∀ t : (Spec4 C).Domain, ∀ table : StreamCache C,
      IsQueryBoundP ((treeSimErase (hybridImpl D t)).run table)
        AimedProgramCall 0 := by
    intro t table
    rcases t with ((t | t) | t) | t
    · change IsQueryBoundP ((treeSimErase ((emulatedRoles D).adversary
        (OracleComp.lift (OracleSpec.query t)))).run table) _ 0
      rw [show treeSimErase ((emulatedRoles D).adversary (OracleComp.lift (OracleSpec.query t))) =
          StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) from
        treeSimErase_adversary D _, StateT.run_lift]
      exact qb0_bind (aimed_noProgram_adversary _) (fun _ => isQueryBoundP_pure _ _ 0)
    · change IsQueryBoundP ((treeSimErase ((emulatedRoles D).honest
        (OracleComp.lift (OracleSpec.query t)))).run table) _ 0
      by_cases ht : ∃ x, t = .inr (.inr x) ∧ Hidden D x.1
      · obtain ⟨x, rfl, hx⟩ := ht
        rw [emul_honest_hidden D x hx]
        simpa [treeSimErase, keygenEraseLog, WriterT.run_liftM, Functor.map_map]
          using aimed_noProgram_free
            (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run table) (LocalSpec C))
      · rw [emul_honest_other D t (fun x he hx => ht ⟨x, he, hx⟩)]
        exact hlift _ table (aimed_noProgram_free _)
    · change IsQueryBoundP ((treeSimErase ((lifetimeHybridRoles D 0 0).honest
        (OracleComp.lift (OracleSpec.query t)))).run table) _ 0
      rw [LifetimeKeygenHopProof.erase_base_honest]
      change IsQueryBoundP (free (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, table)) _ 0
      exact qb0_bind (aimed_noProgram_free _) (fun _ => isQueryBoundP_pure _ _ 0)
    · change IsQueryBoundP ((treeSimErase ((lifetimeHybridRoles D 0 0).honest
        (OracleComp.lift (OracleSpec.query t)))).run table) _ 0
      rw [LifetimeKeygenHopProof.erase_base_honest]
      change IsQueryBoundP (free (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, table)) _ 0
      exact qb0_bind (aimed_noProgram_free _) (fun _ => isQueryBoundP_pure _ _ 0)
  induction p using OracleComp.inductionOn generalizing table with
  | pure a => simp only [simulateQ_pure, treeSimErase_pure, StateT.run_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, treeSimErase_bind, StateT.run_bind]
    exact qb0_bind (hstep t table) (fun r => ih r.1 r.2)

/-- Both local copies share exactly the original hash cache after folding, while the stream table
is still returned. -/
theorem localHybrid_evaluate (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (Spec4 C) α) (table : StreamCache C) :
    simulateQ (localAnswer prims) (localHybrid D p table) =
      simulateQ (worldAnswer prims) ((treeSimErase (simulateQ (hybridImpl D) p)).run table) :=
  LifetimeKeygenHopProof.continuationOracle_simulate prims _ (by
    have he : LifetimeKeygenHopProof.Programming (C := C) = AimedProgramCall := by
      funext t
      rcases t with (t | t) | t <;> rfl
    rw [he]
    exact hybrid_noProgram D p table)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E)


/-- The exact visible output of a between-round segment is independent of the stored programs. -/
theorem runTo_visible (keys : C.Party → Keys C) (h : C.Party)
    (prog : Program C E) (st : LifetimeState C E) (hrun : st.running ≠ none) :
    (fun r => (r.1, visibleState r.2)) <$>
        (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run
          (visibleState st).restore =
      (fun r => (r.1, visibleState r.2)) <$>
        (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st := by
  rw [restore_visibleState, runTo_replaceSteps K circuits settings attempts D n keys h _ prog st hrun,
    Functor.map_map]
  simp only [visible_replaceSteps]


/-- The actual suspension can be reconstructed after the whole public segment. This is an exact
program equality, retaining the result and every other lifetime state field. -/
theorem runTo_reconstruct (keys : C.Party → Keys C) (h : C.Party)
    (prog : Program C E) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput) (hs : st.running = some (tree, fuel, steps)) :
    (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st =
      (fun r => (r.1, replaceSteps steps r.2)) <$>
        (runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run
          (visibleState st).restore := by
  have hh := runTo_replaceSteps K circuits settings attempts D n keys h steps prog
    (visibleState st).restore (by simp [VisibleState.restore, visibleState, hs])
  rwa [replace_restore st tree fuel steps hs] at hh


/-- Erasing the final adversary continuation exposes the reveal as the public segment followed
by the actual honest derivation. This equality still retains every oracle query. -/
theorem revealRows_running (keys : C.Party → Keys C) (h : C.Party)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (prog : Program C E) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (hc : CountIs (n + 1) st)
    (hs : st.running = some (tree, fuel, fun i => suspendStep (k i)
      (prssRevealStep D active parts committed i))) :
    (fun r => r.1.1) <$> revealSegment K circuits settings attempts D n keys h k active parts committed prog st =
      ((runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run
          (visibleState st).restore >>= fun r =>
        r.1.atRound (pure none) fun sent _ =>
          some <$> targetCopy4 (prssRevealRows D active parts committed sent)) := by
  rw [revealSegment_running K circuits settings attempts D n keys h k active parts committed prog st tree fuel hc hs,
    runTo_reconstruct K circuits settings attempts D n keys h prog st tree fuel _ hs, map_bind, bind_map_left]
  apply bind_congr
  intro r
  cases hp : r.1 with
  | done f => simp only [Pause.atRound, map_pure]
  | wait q next =>
    cases q <;> simp only [Pause.atRound, map_pure]
    erw [Functor.map_map]

/-- The initial setup suspension cannot be settled before its first round. -/
theorem settle_initial (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (data : C.Party → Parts C × List HashOutput)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    ({ st with running := some (tree, ceremonyFuel circuits settings,
      fun i => suspendStep (k i) (prssInitialSteps D data i)) } : LifetimeState C E).settle D =
      { st with running := some (tree, ceremonyFuel circuits settings,
        fun i => suspendStep (k i) (prssInitialSteps D data i)) } := by
  have hf : ceremonyFuel circuits settings ≠ 0 := by unfold ceremonyFuel setupRounds; omega
  simp only [LifetimeState.settle, hf, false_or, suspendStep_isDone,
    if_neg (prssInitialSteps_not_done D data)]

/-- When at least one honest operator remains active, the commit round cannot settle the run. -/
theorem settle_commit_active (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (data : C.Party → Parts C × List HashOutput) (sent : Sent C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (ha : ¬ ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i) :
    ({ st with running := some (tree, ceremonyFuel circuits settings - 1,
      fun i => suspendStep (k i) (prssRevealStep D (prssCommitActive D sent)
        (fun j => (data j).1) (prssCommitInbox D data sent) i)) } : LifetimeState C E).settle D =
      { st with running := some (tree, ceremonyFuel circuits settings - 1,
        fun i => suspendStep (k i) (prssRevealStep D (prssCommitActive D sent)
          (fun j => (data j).1) (prssCommitInbox D data sent) i)) } := by
  have hf : ceremonyFuel circuits settings - 1 ≠ 0 := by unfold ceremonyFuel setupRounds; omega
  simp only [LifetimeState.settle, hf, false_or, suspendStep_isDone, prssRevealStep_all_done,
    if_neg ha]


/-- Internal result before testing the selected start. This value stays inside the prefix. -/
structure BeforeStart (C : Committee) (E : Type) where
  keys : C.Party → Keys C
  h : C.Party
  pause : Pause C E
  state : LifetimeState C E

/-- The common actual computation before the selected start decision. -/
def beforeStart4 : OracleComp (Spec4 C) (Option (BeforeStart C E)) := do
  let state ← (base4 (C := C)).adversary (A.keygen.start (corruptInputs D fun _ => ()) [])
  let (state, outputs) ← executePhase base4 D A.keygen noFunctionality setupRounds state
    fun i => (keygen i : PartyM C E RealSpec (Keys C))
  let some h := C.parties.find? (· ∉ D.1) | pure none
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure none else do
  let keys := fun i => (outputs i).getD default
  let (pause, st) ← (runTo (oracles4 K circuits settings attempts D n keys h)
    (StartStop attempts D n) (A.run state (keys h).parameter)).run (LifetimeProof.initial D)
  pure (some ⟨keys, h, pause, st⟩)

/-- The admitted start becomes a driver state without sampling or retaining any selected parts. -/
def holdStart : Option (BeforeStart C E) → Option (Held C E)
  | none => none
  | some before => before.pause.atStart none fun tree k =>
      if LifetimeProof.canStart attempts D before.state tree ∧ CountIs n before.state then
        some ⟨before.keys, before.h, k, visibleState (E := E)
          { LifetimeProof.increment before.state tree with
            running := some (tree, ceremonyFuel circuits settings, fun _ => .done none) }⟩
      else none

/-- Keygen and the lifetime prefix, stopped before the selected run samples its setup parts. -/
def prefix4 : OracleComp (Spec4 C) (Option (Held C E)) := do
  let state ← (base4 (C := C)).adversary (A.keygen.start (corruptInputs D fun _ => ()) [])
  let (state, outputs) ← executePhase base4 D A.keygen noFunctionality setupRounds state
    fun i => (keygen i : PartyM C E RealSpec (Keys C))
  let some h := C.parties.find? (· ∉ D.1) | pure none
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure none else do
  let keys := fun i => (outputs i).getD default
  let (pause, st) ← (runTo (oracles4 K circuits settings attempts D n keys h)
    (StartStop attempts D n) (A.run state (keys h).parameter)).run (LifetimeProof.initial D)
  pause.atStart (pure none) fun tree k =>
    if LifetimeProof.canStart attempts D st tree ∧ CountIs n st then
      pure (some ⟨keys, h, k, visibleState (E := E)
        { LifetimeProof.increment st tree with
          running := some (tree, ceremonyFuel circuits settings, fun _ => .done none) }⟩)
    else pure none


/-- The external driver selects its state from the one actual prefix run. -/
theorem prefix4_eq : prefix4 K circuits settings attempts D n A =
    holdStart circuits settings attempts D n <$> beforeStart4 K circuits settings attempts D n A := by
  unfold prefix4 beforeStart4
  simp only [map_bind]
  apply bind_congr
  intro state
  apply bind_congr
  intro r
  cases hf : C.parties.find? (fun i => i ∉ D.1) with
  | none => simp only [map_pure]; rfl
  | some h =>
    by_cases hout : ¬ ∀ i, i ∉ D.1 → (r.2 i).isSome
    · simp only [if_pos hout, map_pure]; rfl
    · simp only [if_neg hout, map_bind]
      apply bind_congr
      intro r
      rw [map_pure]
      cases r.1 with
      | done f => rfl
      | wait q k =>
        cases q <;> try rfl
        simp only [Pause.atStart, holdStart]
        split <;> rfl

/-- The source resumes its exact selected setup from the same internal prefix result. -/
def setupAfterStart4 : Option (BeforeStart C E) → OracleComp (Spec4 C) (Option (Boundary C E))
  | none => pure none
  | some before => do
      let r ← before.pause.atStart (pure ((none, before.pause.rest), before.state)) fun tree k' =>
        if LifetimeProof.canStart attempts D before.state tree ∧ CountIs n before.state then do
          let data ← targetCopy4 (prssInitialData D)
          let k := cont K circuits settings before.keys before.state tree
          let next := fun i => suspendStep (k i) (prssInitialSteps D data i)
          commitSegment K circuits settings attempts D n before.keys before.h k data
            (k' (some (toCoalition D next)))
            (({ LifetimeProof.increment before.state tree with
              running := some (tree, ceremonyFuel circuits settings, next) }).settle D)
        else pure ((none, before.pause.rest), before.state)
      pure (some ⟨before.keys, before.h, r.1.1, r.1.2, r.2⟩)

/-- Exact source factorization before any selected setup data is sampled. -/
theorem setup4_beforeStart : setup4 K circuits settings attempts D n A =
    beforeStart4 K circuits settings attempts D n A >>= setupAfterStart4 K circuits settings attempts D n := by
  unfold setup4 beforeStart4
  simp only [bind_assoc]
  apply bind_congr
  intro state
  apply bind_congr
  intro r
  cases hf : C.parties.find? (fun i => i ∉ D.1) with
  | none => simp only [pure_bind]; rfl
  | some h =>
    by_cases hout : ¬ ∀ i, i ∉ D.1 → (r.2 i).isSome
    · simp only [if_pos hout, pure_bind]; rfl
    · simp only [if_neg hout, startSegment, bind_assoc, pure_bind, setupAfterStart4]

/-- Resume one pending lifetime answer and run through signing and local queries to the next
round. The returned continuation has already reserved that round's unit of fuel. -/
def resume4 (held : Held C E) (inbox : Sent C E) :
    OracleComp (Spec4 C) (Option (Held C E) × Sent C E) := do
  let (pause, st) ← (runTo (oracles4 K circuits settings attempts D n held.keys held.h)
    RoundStop (held.continuation (some inbox))).run held.state.restore
  pause.atRound (pure (none, fun _ _ => none)) fun sent k =>
    pure (some ⟨held.keys, held.h, k,
      { (visibleState st) with running := st.running.map fun r => (r.1, r.2.1 - 1) }⟩, sent)


/-- Deterministic driver bookkeeping after a public segment. -/
def resumed (held : Held C E) (r : Pause C E × LifetimeState C E) : Option (Held C E) × Sent C E :=
  r.1.atRound (none, fun _ _ => none) fun sent k =>
    (some ⟨held.keys, held.h, k,
      { (visibleState r.2) with running := r.2.running.map fun r => (r.1, r.2.1 - 1) }⟩, sent)

theorem resume4_map (held : Held C E) (inbox : Sent C E) :
    resume4 K circuits settings attempts D n held inbox = resumed held <$>
      (runTo (oracles4 K circuits settings attempts D n held.keys held.h)
        RoundStop (held.continuation (some inbox))).run held.state.restore := by
  unfold resume4
  rw [← bind_pure_comp]
  apply bind_congr
  rintro ⟨pause, state⟩
  cases pause with
  | done f => rfl
  | wait q k => cases q <;> rfl

/-- The external setup runs the selected honest programs. Its adversary runs the lifetime prefix
once, and between its rounds runs exactly the pending lifetime continuation. -/
def boundaryAdv : Adversary C E (Keys C) PEmpty PEmpty where
  State := Option (Held C E) × StreamCache C
  start _ _ := localHybrid D (prefix4 K circuits settings attempts D n A) ∅
  round state inbox := match state.1 with
    | none => pure (state, fun _ _ => none)
    | some held => do
      let ((next, sent), table) ← localHybrid D (resume4 K circuits settings attempts D n held inbox) state.2
      pure ((next, table), sent)
  answer _ l := l.elim

/-- A dead driver makes no further query. -/
def round4 (state : Option (Held C E)) (inbox : Sent C E) :
    OracleComp (Spec4 C) (Option (Held C E) × Sent C E) :=
  match state with
  | none => pure (none, fun _ _ => none)
  | some held => resume4 K circuits settings attempts D n held inbox

/-- The two external setup views, fed to the actual lifetime continuation. -/
def earlyRounds4 (state : Option (Held C E)) (data : C.Party → Parts C × List HashOutput) :
    OracleComp (Spec4 C) (Option (Held C E) × Sent C E × Option (Sent C E)) := do
  let (state', sent) ← round4 K circuits settings attempts D n state (prssCommitVisible D data)
  if ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i then pure (state', sent, none) else do
  let (state'', sent') ← round4 K circuits settings attempts D n state'
    (prssRevealVisible D (prssCommitActive D sent) (fun i => (data i).1))
  pure (state'', sent, some sent')

/-- The concrete external setup prefix, before its honest key-derivation calls. -/
def early4 : OracleComp (Spec4 C)
    ((C.Party → Parts C × List HashOutput) × Option (Held C E) × Sent C E × Option (Sent C E)) := do
  let state ← prefix4 K circuits settings attempts D n A
  let data ← targetCopy4 (prssInitialData D)
  let r ← earlyRounds4 K circuits settings attempts D n state data
  pure (data, r)

theorem boundary_round (state : Option (Held C E)) (table : StreamCache C) (inbox : Sent C E) :
    (boundaryAdv K circuits settings attempts D n A).round (state, table) inbox =
      (fun r => ((r.1.1, r.2), r.1.2)) <$>
        localHybrid D (round4 K circuits settings attempts D n state inbox) table := by
  cases state with
  | none => simp [boundaryAdv, round4, localHybrid_pure]
  | some held => rfl

theorem boundary_earlyRounds (state : Option (Held C E)) (table : StreamCache C)
    (data : C.Party → Parts C × List HashOutput) :
    prssEarlyDataRounds D (boundaryAdv K circuits settings attempts D n A) (state, table) data =
      (fun r => ((r.1.1, r.2), r.1.2)) <$>
        localHybrid D (earlyRounds4 K circuits settings attempts D n state data) table := by
  unfold prssEarlyDataRounds earlyRounds4
  rw [boundary_round, localHybrid_bind]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro r
  split
  · rw [localHybrid_pure, map_pure]
  · rw [localHybrid_bind, boundary_round]
    simp only [bind_map_left, map_bind, pure_bind]
    apply bind_congr
    intro r
    rw [localHybrid_pure, map_pure]

/-- The actual setup adversary, including both possible round calls, is the local interpretation
of the fixed four-copy prefix `early4`. The same retained table is threaded through both calls. -/
theorem boundary_setupEarly (x : C.Party → Keys C) (z : Aux) :
    setupEarly D (boundaryAdv K circuits settings attempts D n A)
      ((boundaryAdv K circuits settings attempts D n A).start (corruptInputs D x) z) =
      (fun r => (r.1.1, ((r.1.2.1, r.2), r.1.2.2))) <$>
        localHybrid D (early4 K circuits settings attempts D n A) ∅ := by
  unfold setupEarly early4
  change (localHybrid D (prefix4 K circuits settings attempts D n A) ∅ >>= _) = _
  rw [localHybrid_bind, map_bind]
  apply bind_congr
  intro r
  rw [localHybrid_bind, localHybrid_target]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro data
  rw [boundary_earlyRounds, localHybrid_bind]
  simp only [bind_map_left, map_bind, localHybrid_pure, map_pure]




/-- Reveal rows returned by the concrete external setup after the fixed driver prefix. -/
def driverRows4 : OracleComp (Spec4 C) (Option (RevealRows C)) := do
  let (data, _, sent, revealed) ← early4 K circuits settings attempts D n A
  match revealed with
  | none => pure none
  | some sent' =>
      some <$> targetCopy4 (prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
        (prssCommitInbox D data sent) sent')

/-- A program equality for the actual external setup's rows. All oracle effects, including the
hash cache seen after key derivation, remain in this equality. -/
theorem boundary_rows_local (x : C.Party → Keys C) (z : Aux) :
    Prod.snd <$> (setupEarly D (boundaryAdv K circuits settings attempts D n A)
      ((boundaryAdv K circuits settings attempts D n A).start (corruptInputs D x) z) >>= setupReveal D) =
      Prod.fst <$> localHybrid D (driverRows4 K circuits settings attempts D n A) ∅ := by
  rw [boundary_setupEarly, driverRows4, localHybrid_bind]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro r
  rcases r with ⟨⟨data, state, sent, revealed⟩, table⟩
  cases revealed with
  | none => simp only [setupReveal, localHybrid_pure, map_pure]
  | some sent' =>
    rw [localHybrid_map, localHybrid_target]
    simp only [setupReveal, bind_pure_comp, Functor.map_map]


/-- Interpret a four-copy program with the retained stream table and the actual shared hash cache. -/
def eval4 (prims : Primitives) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) (cache : HashCache C) : ProbComp ((α × StreamCache C) × HashCache C) :=
  (simulateQ (localAnswer prims) (localHybrid D p table)).run cache


theorem eval4_pure (prims : Primitives) {α : Type} (a : α)
    (table : StreamCache C) (cache : HashCache C) :
    eval4 D prims (pure a) table cache = pure ((a, table), cache) := by
  simp only [eval4, localHybrid_pure, simulateQ_pure, StateT.run_pure]

theorem eval4_bind (prims : Primitives) {α β : Type} (p : OracleComp (Spec4 C) α)
    (k : α → OracleComp (Spec4 C) β) (table : StreamCache C) (cache : HashCache C) :
    eval4 D prims (p >>= k) table cache =
      eval4 D prims p table cache >>= fun r => eval4 D prims (k r.1.1) r.1.2 r.2 := by
  simp only [eval4, localHybrid_bind, simulateQ_bind, StateT.run_bind]

theorem eval4_map (prims : Primitives) {α β : Type} (f : α → β)
    (p : OracleComp (Spec4 C) α) (table : StreamCache C) (cache : HashCache C) :
    eval4 D prims (f <$> p) table cache =
      (fun r => ((f r.1.1, r.1.2), r.2)) <$> eval4 D prims p table cache := by
  simp only [eval4, localHybrid_map, simulateQ_map, StateT.run_map]

theorem eval4_support (prims : Primitives) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) (cache : HashCache C) (r : (α × StreamCache C) × HashCache C)
    (hr : r ∈ support (eval4 D prims p table cache)) : r.1.1 ∈ support p := by
  apply localHybrid_support D p table r.1
  apply support_simulateQ_run'_subset (localAnswer prims) (localHybrid D p table) cache
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ hr

/-- The original source event, including its complete hash cache, under the local interpreter. -/
theorem source_event_eq (prims : Primitives) (P : RevealRows C → HashCache C → Prop) :
    Pr[fun r => P (rowsAt r.1) r.2 | worldRun prims (worldSetup K circuits settings attempts D n A)] =
      Pr[fun r => P (rowsOf (r.1.1.bind Boundary.rows)) r.2 |
        eval4 D prims (setup4 K circuits settings attempts D n A) ∅ ∅] := by
  rw [eval4, localHybrid_evaluate]
  simp only [treeSimErase, StateT.run_mk, keygenEraseLog, simulateQ_map, StateT.run_map, probEvent_map]
  rfl

/-- The concrete external setup event has exactly the fixed driver's row and cache marginal. -/
theorem boundary_event_eq (prims : Primitives) (x : C.Party → Keys C) (z : Aux)
    (P : RevealRows C → HashCache C → Prop) :
    Pr[fun r => P (rowsOf r.1.2) r.2 |
      worldRun prims (setupPrefix D (boundaryAdv K circuits settings attempts D n A) x z)] =
      Pr[fun r => P (rowsOf r.1.1) r.2 | eval4 D prims (driverRows4 K circuits settings attempts D n A) ∅ ∅] := by
  have he := congrArg (fun p => (simulateQ (localAnswer prims) p).run (∅ : HashCache C))
    (boundary_rows_local K circuits settings attempts D n A x z)
  simp only [simulateQ_map, StateT.run_map] at he
  have hp := congrArg (fun p => Pr[fun r => P (rowsOf r.1) r.2 | p]) he
  simpa only [probEvent_map, worldRun_setupPrefix, eval4, Function.comp_def] using hp


/-- The final external setup round followed by the honest derivation. -/
def revealDriver4 (held : Held C E) (inbox : Sent C E) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (Spec4 C) (Option (RevealRows C)) := do
  let (_, sent) ← resume4 K circuits settings attempts D n held inbox
  some <$> targetCopy4 (prssRevealRows D active parts committed sent)

/-- At a live reveal, the external driver has exactly the source rows and cache. If the lifetime
ends before sending its next round, its source event is empty. -/
theorem reveal_event_le (prims : Primitives) (P : RevealRows C → HashCache C → Prop)
    (hP : ∀ cache, ¬ P (rowsOf none) cache)
    (held : Held C E) (inbox : Sent C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hs : st.running = some (tree, fuel, fun i => suspendStep (k i)
      (prssRevealStep D active parts committed i)))
    (table : StreamCache C) (cache : HashCache C) :
    Pr[fun r => P (rowsOf r.1.1) r.2 | eval4 D prims
      ((fun r => r.1.1) <$> revealSegment K circuits settings attempts D n held.keys held.h k
        active parts committed (held.continuation (some inbox)) st) table cache] ≤
      Pr[fun r => P (rowsOf r.1.1) r.2 | eval4 D prims
        (revealDriver4 K circuits settings attempts D n held inbox active parts committed) table cache] := by
  rw [revealRows_running K circuits settings attempts D n held.keys held.h k active parts committed
    (held.continuation (some inbox)) st tree fuel hc hs, hv]
  unfold revealDriver4 resume4
  rw [bind_assoc, eval4_bind, eval4_bind]
  apply probEvent_bind_mono
  intro r _
  cases hp : r.1.1.1 with
  | done f =>
    simp only [hp, Pause.atRound, eval4_pure, probEvent_pure, hP, if_false, zero_le]
  | wait q next =>
    cases q <;> simp only [hp, Pause.atRound, pure_bind]
    all_goals try { simp only [eval4_pure, probEvent_pure, hP, if_false, zero_le] }
    exact le_rfl


/-- Complete setup rows after feeding the external commit view to a live driver. -/
def commitDriver4 (held : Held C E) (data : C.Party → Parts C × List HashOutput) :
    OracleComp (Spec4 C) (Option (RevealRows C)) := do
  let (state, sent) ← resume4 K circuits settings attempts D n held (prssCommitVisible D data)
  if ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i then pure none else do
  let (_, sent') ← round4 K circuits settings attempts D n state
    (prssRevealVisible D (prssCommitActive D sent) (fun i => (data i).1))
  some <$> targetCopy4 (prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
    (prssCommitInbox D data sent) sent')


/-- Finish the actual external setup after its first sampled data. -/
def finishDriver4 (state : Option (Held C E)) (data : C.Party → Parts C × List HashOutput) :
    OracleComp (Spec4 C) (Option (RevealRows C)) := do
  let (_, sent, revealed) ← earlyRounds4 K circuits settings attempts D n state data
  match revealed with
  | none => pure none
  | some sent' =>
      some <$> targetCopy4 (prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
        (prssCommitInbox D data sent) sent')

theorem driverRows4_factor : driverRows4 K circuits settings attempts D n A =
    prefix4 K circuits settings attempts D n A >>= fun state =>
      targetCopy4 (prssInitialData D) >>= finishDriver4 K circuits settings attempts D n state := by
  simp only [driverRows4, early4, bind_assoc, pure_bind]
  rfl

theorem finishDriver4_some (held : Held C E) (data : C.Party → Parts C × List HashOutput) :
    finishDriver4 K circuits settings attempts D n (some held) data =
      commitDriver4 K circuits settings attempts D n held data := by
  unfold finishDriver4 earlyRounds4 commitDriver4
  simp only [round4, bind_assoc]
  apply bind_congr
  intro r
  split
  · rw [pure_bind]
  · simp only [bind_assoc, pure_bind]

/-- An empty source row on every answer path has zero event probability, including the complete
cache left by any intervening work. -/
theorem eval4_empty_event (prims : Primitives) (P : RevealRows C → HashCache C → Prop)
    (hP : ∀ cache, ¬ P (rowsOf none) cache) (p : OracleComp (Spec4 C) (Option (RevealRows C)))
    (hp : ∀ r ∈ support p, r = none) (table : StreamCache C) (cache : HashCache C) :
    Pr[fun r => P (rowsOf r.1.1) r.2 | eval4 D prims p table cache] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro r hr
  rw [hp _ (eval4_support D prims p table cache r hr)]
  exact hP _

/-- At the selected commit, both honest views are fed to the actual stored continuation. -/
theorem commit_event_le (prims : Primitives) (P : RevealRows C → HashCache C → Prop)
    (hP : ∀ cache, ¬ P (rowsOf none) cache)
    (held : Held C E) (data : C.Party → Parts C × List HashOutput)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hs : st.running = some (tree, ceremonyFuel circuits settings,
      fun i => suspendStep (k i) (prssInitialSteps D data i)))
    (table : StreamCache C) (cache : HashCache C) :
    Pr[fun r => P (rowsOf r.1.1) r.2 | eval4 D prims
      ((fun r => r.1.1) <$> commitSegment K circuits settings attempts D n held.keys held.h k data
        (held.continuation (some (prssCommitVisible D data))) st) table cache] ≤
      Pr[fun r => P (rowsOf r.1.1) r.2 | eval4 D prims
        (commitDriver4 K circuits settings attempts D n held data) table cache] := by
  rw [commitSegment_running K circuits settings attempts D n held.keys held.h k data
    (held.continuation (some (prssCommitVisible D data))) st tree _ hc hs,
    runTo_reconstruct K circuits settings attempts D n held.keys held.h
      (held.continuation (some (prssCommitVisible D data))) st tree _ _ hs, hv]
  simp only [map_bind, bind_map_left]
  unfold commitDriver4 resume4
  rw [bind_assoc, eval4_bind, eval4_bind]
  apply probEvent_bind_mono
  intro r hr
  have hr' := eval4_support D prims _ table cache r hr
  have hrun : (held.state.restore : LifetimeState C E).running =
      some (tree, ceremonyFuel circuits settings, fun _ => .done none) := by
    rw [← hv]
    simp [VisibleState.restore, visibleState, hs]
  have hframe := runTo_frame K circuits settings attempts D n held.keys held.h
    (held.continuation (some (prssCommitVisible D data))) held.state.restore
    (by rw [hrun]; simp) r.1.1 hr'
  have hcount : CountIs (n + 1) r.1.1.2 := by
    change r.1.1.2.runCount = n + 1
    rw [hframe.1, ← hv]
    exact hc
  have hrunning := hframe.2.trans hrun
  cases hp : r.1.1.1 with
  | done f =>
    simp only [hp, Pause.atRound, map_pure, eval4_pure, probEvent_pure, hP, if_false, zero_le]
  | wait q next =>
    cases q <;> simp only [hp, Pause.atRound, map_pure, pure_bind]
    all_goals try { simp only [eval4_pure, probEvent_pure, hP, if_false, zero_le] }
    rename_i sent
    have ha : (fun i => (C.parties.any fun j =>
        Msg.isAbort (prssCommitInbox D data sent i j)) = false) = prssCommitActive D sent :=
      funext (prssCommitInbox_active D data sent)
    rw [ha]
    by_cases hall : ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i
    · rw [if_pos hall]
      have hsource := inactive_pastSelected D n
        (replaceSteps (fun i => suspendStep (k i) (prssInitialSteps D data i)) r.1.1.2)
        tree (ceremonyFuel circuits settings - 1) (prssCommitActive D sent) (fun i => (data i).1)
        (prssCommitInbox D data sent) k hcount hall
      rw [eval4_empty_event D prims P hP _ (fun row hrow => ?_) r.1.2 r.2]
      · exact bot_le
      · rw [support_map, Set.mem_image] at hrow
        obtain ⟨out, hout, rfl⟩ := hrow
        exact revealSegment_pastSelected K circuits settings attempts D n held.keys held.h k _ _ _ _ _ hsource out hout
    · rw [if_neg hall, round4]
      rw [settle_commit_active circuits settings D _ tree data sent k hall]
      rw [reveal_visible D]
      exact reveal_event_le K circuits settings attempts D n prims P hP
        ⟨held.keys, held.h, next,
          { visibleState r.1.1.2 with running := r.1.1.2.running.map fun r => (r.1, r.2.1 - 1) }⟩
        _ k (prssCommitActive D sent) (fun i => (data i).1) (prssCommitInbox D data sent)
        ({ replaceSteps (fun i => suspendStep (k i) (prssInitialSteps D data i)) r.1.1.2 with
          running := some (tree, ceremonyFuel circuits settings - 1,
            fun i => suspendStep (k i) (prssRevealStep D (prssCommitActive D sent)
              (fun j => (data j).1) (prssCommitInbox D data sent) i)) } : LifetimeState C E)
        tree (ceremonyFuel circuits settings - 1) hcount
        (visible_advance r.1.1.2 tree _ _ _ hrunning) rfl r.1.2 r.2


set_option maxHeartbeats 800000 in
/-- Event domination for the actual lifetime setup and the once-only external setup adversary. -/
theorem setup_event_le (prims : Primitives) (x : C.Party → Keys C) (z : Aux)
    (P : RevealRows C → HashCache C → Prop) (hP : ∀ cache, ¬ P (rowsOf none) cache) :
    Pr[fun r => P (rowsAt r.1) r.2 | worldRun prims (worldSetup K circuits settings attempts D n A)] ≤
      Pr[fun r => P (rowsOf r.1.2) r.2 |
        worldRun prims (setupPrefix D (boundaryAdv K circuits settings attempts D n A) x z)] := by
  rw [source_event_eq, boundary_event_eq]
  have htarget : Pr[fun r => P (rowsOf r.1.1) r.2 | eval4 D prims
      ((fun b : Option (Boundary C E) => b.bind Boundary.rows) <$>
        setup4 K circuits settings attempts D n A) ∅ ∅] ≤
      Pr[fun r => P (rowsOf r.1.1) r.2 |
        eval4 D prims (driverRows4 K circuits settings attempts D n A) ∅ ∅] := by
    rw [setup4_beforeStart, driverRows4_factor, prefix4_eq]
    simp only [map_bind, bind_map_left]
    rw [eval4_bind, eval4_bind]
    apply probEvent_bind_mono
    intro r _
    rcases r with ⟨⟨before, table⟩, cache⟩
    cases before with
    | none =>
      simp only [setupAfterStart4, map_pure, Option.bind_none, eval4_pure,
        probEvent_pure, hP, if_false, zero_le]
    | some before =>
      unfold setupAfterStart4 holdStart
      cases hp : before.pause with
      | done f =>
        simp only [hp, Pause.atStart, pure_bind, map_pure, Option.bind_some, eval4_pure,
          probEvent_pure, hP, if_false, zero_le]
      | wait q next =>
        cases q <;> simp only [hp, Pause.atStart]
        all_goals try { simp only [pure_bind, map_pure, Option.bind_some, eval4_pure,
          probEvent_pure, hP, if_false, zero_le] }
        rename_i tree
        by_cases hstart : LifetimeProof.canStart attempts D before.state tree ∧ CountIs n before.state
        · simp only [if_pos hstart, map_bind, bind_assoc]
          rw [eval4_bind, eval4_bind]
          apply probEvent_bind_mono
          intro data _
          simp only [map_pure, Option.bind_some]
          rw [settle_initial circuits settings D]
          rw [initial_visible D]
          have hc : CountIs (n + 1)
              ({ LifetimeProof.increment before.state tree with
                running := some (tree, ceremonyFuel circuits settings,
                  fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                    (prssInitialSteps D data.1.1 i)) } : LifetimeState C E) := by
            change (LifetimeProof.increment before.state tree).runCount = n + 1
            rw [LifetimeProof.increment_runCount]
            exact congrArg (fun x => x + 1) hstart.2
          rw [finishDriver4_some]
          exact commit_event_le K circuits settings attempts D n prims P hP
            ⟨before.keys, before.h, next, visibleState (E := E)
              { LifetimeProof.increment before.state tree with
                running := some (tree, ceremonyFuel circuits settings, fun _ => .done none) }⟩
            data.1.1 (cont K circuits settings before.keys before.state tree)
            ({ LifetimeProof.increment before.state tree with
              running := some (tree, ceremonyFuel circuits settings,
                fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                  (prssInitialSteps D data.1.1 i)) } : LifetimeState C E)
            tree hc rfl rfl data.1.2 data.2
        · simp only [if_neg hstart, pure_bind, map_pure, Option.bind_some, eval4_pure,
            probEvent_pure, hP, if_false, zero_le]
  simpa only [eval4_map, probEvent_map, Function.comp_def] using htarget

/-- The external setup's initial commitment pass costs at most `n²`, including when the
selected lifetime run was never admitted. Ported from `treeHashBudget_setup_initial_count`
(`TreeHashBudgetFinal.lean`) with the actual local `Counted` predicate. -/
theorem initialData_bound : IsQueryBoundP (prssInitialData D) Counted (C.n ^ 2) := by
  unfold prssInitialData
  have hpass : ∀ qs : C.Party → Query C,
      IsQueryBoundP (liftComp (C.parties.mapM fun j => hashQuery (qs j)) (LocalSpec C)) Counted C.n := by
    intro qs
    rw [keygen_liftComp_mapM]
    have h := main_bound_mapM (fun j => liftComp (hashQuery (qs j)) (LocalSpec C)) 1
      (fun j => by
        change IsQueryBoundP (OracleComp.lift (OracleSpec.query
          (spec := LocalSpec C) (.inr (.inl (qs j))))) Counted 1
        rw [isQueryBoundP_query_iff]
        intro _
        omega) C.parties
    simpa only [Committee.parties, List.length_finRange, Nat.mul_one] using h
  have hb := main_bound_sequenceFin C.n
    (fun i : C.Party => if i ∈ D.1 then pure (⟨0, fun _ => 0, fun _ => 0⟩, []) else do
      let own ← liftComp (sampleParts : ProbComp (Parts C)) (LocalSpec C)
      let commitments ← liftComp (C.parties.mapM fun j =>
        hashQuery (.commit .prss i j (revealTo .prss own i j))) (LocalSpec C)
      pure (own, commitments)) (fun i => by
        split
        · exact isQueryBoundP_pure _ _ _
        · refine (isQueryBoundP_bind (main_bound_sample _) (m := C.n) fun own _ => ?_).mono (by omega)
          exact (isQueryBoundP_bind (hpass _) (m := 0)
            (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega))
  simpa only [pow_two] using hb

/-- Predicate version of VCVio's `IsTotalQueryBound.of_bind_left`:
removing a continuation cannot increase any filtered query count. -/
theorem bound_bind_left {ι α β : Type} {spec : OracleSpec ι} {P : ι → Prop} [DecidablePred P]
    {p : OracleComp spec α} {k : α → OracleComp spec β} {Q : ℕ}
    (hQ : IsQueryBoundP (p >>= k) P Q) : IsQueryBoundP p P Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure _ => trivial
  | query_bind t k ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at hQ
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨hQ.1, fun a => ih a (hQ.2 a)⟩


/-- Replace a continuation after a shared prefix, charging the same one-time additive allowance
on every answer path. This retains the prefix's residual budget instead of paying it twice. -/
theorem bound_replace_tail {ι α β γ : Type} {spec : OracleSpec ι} {P : ι → Prop} [DecidablePred P]
    (p : OracleComp spec α) (left : α → OracleComp spec β) (right : α → OracleComp spec γ)
    (extra : ℕ)
    (hstep : ∀ a ∈ support p, ∀ q, IsQueryBoundP (left a) P q → IsQueryBoundP (right a) P (q + extra))
    (Q : ℕ) (hQ : IsQueryBoundP (p >>= left) P Q) : IsQueryBoundP (p >>= right) P (Q + extra) := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a =>
    rw [pure_bind] at hQ ⊢
    exact hstep a (by simp) Q hQ
  | query_bind t k ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at hQ ⊢
    refine ⟨hQ.1.imp id (fun h => by omega), fun a => ?_⟩
    have hh := ih a (fun b hb => hstep b ((mem_support_bind_iff _ _ _).mpr
      ⟨a, mem_support_query t a, hb⟩)) _ (hQ.2 a)
    refine hh.mono ?_
    by_cases ht : P t
    · have hp : 0 < Q := hQ.1.resolve_left (not_not.mpr ht)
      simp only [if_pos ht]
      omega
    · simp only [if_neg ht]
      omega


/-- The driver's second send consumes only the prefix of the actual selected reveal computation. -/
theorem reveal_early_bound (held : Held C E) (inbox : Sent C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hs : st.running = some (tree, fuel, fun i => suspendStep (k i)
      (prssRevealStep D active parts committed i)))
    (table : StreamCache C) (Q : ℕ)
    (hQ : IsQueryBoundP (localHybrid D ((fun r => r.1.1) <$>
      revealSegment K circuits settings attempts D n held.keys held.h k active parts committed
        (held.continuation (some inbox)) st) table) Counted Q) :
    IsQueryBoundP (localHybrid D (resume4 K circuits settings attempts D n held inbox) table) Counted Q := by
  rw [revealRows_running K circuits settings attempts D n held.keys held.h k active parts committed
    (held.continuation (some inbox)) st tree fuel hc hs, hv, localHybrid_bind] at hQ
  rw [resume4_map, localHybrid_map, isQueryBoundP_map_iff]
  exact bound_bind_left hQ


set_option maxHeartbeats 800000 in
/-- The two actual driver sends consume only a prefix of the selected setup computation. -/
theorem commit_early_bound (held : Held C E) (data : C.Party → Parts C × List HashOutput)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hs : st.running = some (tree, ceremonyFuel circuits settings,
      fun i => suspendStep (k i) (prssInitialSteps D data i)))
    (table : StreamCache C) (Q : ℕ)
    (hQ : IsQueryBoundP (localHybrid D ((fun r => r.1.1) <$>
      commitSegment K circuits settings attempts D n held.keys held.h k data
        (held.continuation (some (prssCommitVisible D data))) st) table) Counted Q) :
    IsQueryBoundP (localHybrid D (earlyRounds4 K circuits settings attempts D n (some held) data) table)
      Counted Q := by
  rw [commitSegment_running K circuits settings attempts D n held.keys held.h k data
    (held.continuation (some (prssCommitVisible D data))) st tree _ hc hs,
    runTo_reconstruct K circuits settings attempts D n held.keys held.h
      (held.continuation (some (prssCommitVisible D data))) st tree _ _ hs, hv] at hQ
  simp only [map_bind, bind_map_left] at hQ
  rw [localHybrid_bind] at hQ
  unfold earlyRounds4
  rw [round4, resume4_map, bind_map_left, localHybrid_bind]
  refine bound_replace_tail _ _ _ 0 ?_ Q hQ
  intro r hr q hq
  have hr' := localHybrid_support D _ table r hr
  have hrun : (held.state.restore : LifetimeState C E).running =
      some (tree, ceremonyFuel circuits settings, fun _ => .done none) := by
    rw [← hv]
    simp [VisibleState.restore, visibleState, hs]
  have hframe := runTo_frame K circuits settings attempts D n held.keys held.h
    (held.continuation (some (prssCommitVisible D data))) held.state.restore
    (by rw [hrun]; simp) r.1 hr'
  have hcount : CountIs (n + 1) r.1.2 := by
    change r.1.2.runCount = n + 1
    rw [hframe.1, ← hv]
    exact hc
  have hrunning := hframe.2.trans hrun
  cases hp : r.1.1 with
  | done f =>
    simp only [resumed, hp, Pause.atRound]
    split <;> simp only [round4, pure_bind, localHybrid_pure] <;> exact isQueryBoundP_pure _ _ _
  | wait query next =>
    cases query <;> simp only [resumed, hp, Pause.atRound]
    all_goals try { split <;> simp only [round4, pure_bind, localHybrid_pure] <;> exact isQueryBoundP_pure _ _ _ }
    rename_i sent
    simp only [hp, Pause.atRound] at hq
    have ha : (fun i => (C.parties.any fun j =>
        Msg.isAbort (prssCommitInbox D data sent i j)) = false) = prssCommitActive D sent :=
      funext (prssCommitInbox_active D data sent)
    rw [ha] at hq
    by_cases hall : ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i
    · rw [if_pos hall, localHybrid_pure]
      exact isQueryBoundP_pure _ _ _
    · rw [if_neg hall, round4]
      erw [bind_pure_comp, localHybrid_map, isQueryBoundP_map_iff]
      rw [settle_commit_active circuits settings D _ tree data sent k hall, reveal_visible D] at hq
      exact reveal_early_bound K circuits settings attempts D n
        ⟨held.keys, held.h, next,
          { visibleState r.1.2 with running := r.1.2.running.map fun r => (r.1, r.2.1 - 1) }⟩
        _ k (prssCommitActive D sent) (fun i => (data i).1) (prssCommitInbox D data sent)
        ({ replaceSteps (fun i => suspendStep (k i) (prssInitialSteps D data i)) r.1.2 with
          running := some (tree, ceremonyFuel circuits settings - 1,
            fun i => suspendStep (k i) (prssRevealStep D (prssCommitActive D sent)
              (fun j => (data j).1) (prssCommitInbox D data sent) i)) } : LifetimeState C E)
        tree (ceremonyFuel circuits settings - 1) hcount
        (visible_advance r.1.2 tree _ _ _ hrunning) rfl r.2 q hq


/-- A dead driver's two externally scheduled calls make no query. -/
theorem earlyRounds4_none_bound (data : C.Party → Parts C × List HashOutput) (table : StreamCache C) :
    IsQueryBoundP (localHybrid D (earlyRounds4 K circuits settings attempts D n none data) table) Counted 0 := by
  unfold earlyRounds4
  simp only [round4, pure_bind]
  split <;> simp only [localHybrid_pure] <;> exact isQueryBoundP_pure _ _ _

/-- The external setup always samples initial data, including after an unreached selected start. -/
def earlyAfterStart4 (before : Option (BeforeStart C E)) : OracleComp (Spec4 C)
    ((C.Party → Parts C × List HashOutput) × Option (Held C E) × Sent C E × Option (Sent C E)) := do
  let data ← targetCopy4 (prssInitialData D)
  let r ← earlyRounds4 K circuits settings attempts D n (holdStart circuits settings attempts D n before) data
  pure (data, r)

theorem early4_beforeStart : early4 K circuits settings attempts D n A =
    beforeStart4 K circuits settings attempts D n A >>= earlyAfterStart4 K circuits settings attempts D n := by
  rw [early4, prefix4_eq, bind_map_left]
  rfl

theorem dead_early_bound (before : Option (BeforeStart C E))
    (hdead : holdStart circuits settings attempts D n before = none) (table : StreamCache C) :
    IsQueryBoundP (localHybrid D (earlyAfterStart4 K circuits settings attempts D n before) table)
      Counted (C.n ^ 2) := by
  rw [earlyAfterStart4, hdead, localHybrid_bind, localHybrid_target, bind_map_left]
  refine (isQueryBoundP_bind (initialData_bound D) (m := 0) fun data _ => ?_).mono (by omega)
  rw [bind_pure_comp, localHybrid_map, isQueryBoundP_map_iff]
  exact earlyRounds4_none_bound K circuits settings attempts D n data table

set_option maxHeartbeats 800000 in
/-- The selected setup reuses its source budget. Only the dead-prefix branch needs the extra
external commitment pass. -/
theorem afterStart_early_bound (before : Option (BeforeStart C E)) (table : StreamCache C) (Q : ℕ)
    (hQ : IsQueryBoundP (localHybrid D (setupAfterStart4 K circuits settings attempts D n before) table) Counted Q) :
    IsQueryBoundP (localHybrid D (earlyAfterStart4 K circuits settings attempts D n before) table)
      Counted (Q + C.n ^ 2) := by
  by_cases hdead : holdStart circuits settings attempts D n before = none
  · exact (dead_early_bound K circuits settings attempts D n before hdead table).mono (by omega)
  · cases before with
    | none => exact False.elim (hdead rfl)
    | some before =>
      cases hp : before.pause with
      | done f => exact False.elim (hdead (by simp [holdStart, hp, Pause.atStart]))
      | wait query next =>
        cases query <;> simp only [holdStart, hp, Pause.atStart] at hdead
        all_goals try { exact False.elim (hdead trivial) }
        rename_i tree
        by_cases hstart : LifetimeProof.canStart attempts D before.state tree ∧ CountIs n before.state
        · have hbase : IsQueryBoundP
              (localHybrid D (earlyAfterStart4 K circuits settings attempts D n (some before)) table) Counted Q := by
            unfold setupAfterStart4 at hQ
            simp only [hp, Pause.atStart, if_pos hstart, bind_assoc] at hQ
            rw [localHybrid_bind] at hQ
            unfold earlyAfterStart4
            simp only [holdStart, hp, Pause.atStart, if_pos hstart]
            rw [localHybrid_bind]
            refine bound_replace_tail _ _ _ 0 ?_ Q hQ
            intro data _ q hq
            rw [bind_pure_comp, localHybrid_map, isQueryBoundP_map_iff]
            rw [bind_pure_comp, localHybrid_map, isQueryBoundP_map_iff] at hq
            rw [settle_initial circuits settings D, initial_visible D] at hq
            have hc : CountIs (n + 1)
                ({ LifetimeProof.increment before.state tree with
                  running := some (tree, ceremonyFuel circuits settings,
                    fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                      (prssInitialSteps D data.1 i)) } : LifetimeState C E) := by
              change (LifetimeProof.increment before.state tree).runCount = n + 1
              rw [LifetimeProof.increment_runCount]
              exact congrArg (fun x => x + 1) hstart.2
            apply commit_early_bound K circuits settings attempts D n
              ⟨before.keys, before.h, next, visibleState (E := E)
                { LifetimeProof.increment before.state tree with
                  running := some (tree, ceremonyFuel circuits settings, fun _ => .done none) }⟩
              data.1 (cont K circuits settings before.keys before.state tree)
              ({ LifetimeProof.increment before.state tree with
                running := some (tree, ceremonyFuel circuits settings,
                  fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                    (prssInitialSteps D data.1 i)) } : LifetimeState C E)
              tree hc rfl rfl data.2 q
            rw [localHybrid_map, isQueryBoundP_map_iff]
            exact hq
          exact hbase.mono (Nat.le_add_right _ _)
        · exact False.elim (hdead (by simp [if_neg hstart]))

/-- Folding the copies never increases the counted local charge. -/
theorem foldWorld_bound {α : Type} (p : OracleComp (WorldSpec C) α) (Q : ℕ)
    (hQ : IsQueryBoundP p LifetimeCounted Q) :
    IsQueryBoundP (simulateQ foldWorld p) Counted Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with (t | t) | t
    · change IsQueryBoundP ((OracleComp.lift (OracleSpec.query t) : OracleComp (LocalSpec C) _) >>=
        fun a => simulateQ foldWorld (k a)) Counted Q
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun a => (ih a _ (hQ.2 a)).mono ?_⟩
      · by_cases ht : Counted t
        · right
          have hh : LifetimeCounted (Sum.inl (Sum.inl t)) := by
            rcases t with t | t <;> simp_all [Counted, LifetimeCounted]
          exact hQ.1.resolve_left (not_not.mpr hh)
        · exact Or.inl ht
      · by_cases ht : Counted t
        · have hh : LifetimeCounted (Sum.inl (Sum.inl t)) := by
            rcases t with t | t <;> simp_all [Counted, LifetimeCounted]
          simp [ht, hh]
        · simp only [if_neg ht]
          split <;> omega
    · change IsQueryBoundP ((pure false : OracleComp (LocalSpec C) Bool) >>= _) Counted Q
      rw [pure_bind]
      exact (ih false _ (hQ.2 false)).mono (by simp [LifetimeCounted])
    · change IsQueryBoundP ((OracleComp.lift (OracleSpec.query t) : OracleComp (LocalSpec C) _) >>=
        fun a => simulateQ foldWorld (k a)) Counted Q
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun a => (ih a _ (hQ.2 a)).mono ?_⟩
      · by_cases ht : Counted t
        · right
          have hh : LifetimeCounted (Sum.inr t) := by
            rcases t with t | t <;> simp_all [Counted, LifetimeCounted]
          exact hQ.1.resolve_left (not_not.mpr hh)
        · exact Or.inl ht
      · by_cases ht : Counted t
        · have hh : LifetimeCounted (Sum.inr t) := by
            rcases t with t | t <;> simp_all [Counted, LifetimeCounted]
          simp [ht, hh]
        · simp only [if_neg ht]
          split <;> omega

/-- The entire actual setup boundary inherits the all-party source budget before any projection
or erasure. -/
theorem worldSetup_bound (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q) :
    IsQueryBoundP (worldSetup K circuits settings attempts D n A) LifetimeCounted Q := by
  rw [hybrid_split K circuits settings attempts D n A] at hQ
  exact bound_bind_left hQ

/-- The once-only source setup, folded onto local oracles, keeps the original all-answer bound. -/
theorem sourceSetup_bound (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q) :
    IsQueryBoundP (localHybrid D (setup4 K circuits settings attempts D n A) ∅) Counted Q := by
  apply foldWorld_bound
  change IsQueryBoundP (Prod.fst <$> worldSetup K circuits settings attempts D n A) LifetimeCounted Q
  rw [isQueryBoundP_map_iff]
  exact worldSetup_bound K circuits settings attempts D n A Q hQ


/-- The actual external setup has the source's shared path budget plus one extra initial pass
on branches where run `n` was never admitted. -/
theorem boundary_setupEarly_bound_of_hybrid (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q)
    (x : C.Party → Keys C) (z : Aux) :
    IsQueryBoundP (setupEarly D (boundaryAdv K circuits settings attempts D n A)
      ((boundaryAdv K circuits settings attempts D n A).start (corruptInputs D x) z)) Counted (Q + C.n ^ 2) := by
  rw [boundary_setupEarly, isQueryBoundP_map_iff, early4_beforeStart, localHybrid_bind]
  have hs := sourceSetup_bound K circuits settings attempts D n A Q hQ
  rw [setup4_beforeStart, localHybrid_bind] at hs
  exact bound_replace_tail _ _ _ (C.n ^ 2)
    (fun r _ q hq => afterStart_early_bound K circuits settings attempts D n r.1 r.2 q hq) Q hs

/-- S1: the actual selected setup's keys fail separation with the original setup path estimate. -/
theorem setup_keysApart_le_of_hybrid (prims : Primitives) (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q) :
    Pr[fun r => ¬ KeysApart D (rowsAt r.1) |
      worldRun prims (worldSetup K circuits settings attempts D n A)] ≤
      ((Q + C.n ^ 2 : ℕ) : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 +
        ((Fintype.card (C.Party × C.Party × C.Term × C.Term) +
          Fintype.card (C.Party × C.Party × C.Party × C.Party) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (revealPairs C : ℝ≥0∞) / 2 ^ 256 := by
  refine (setup_event_le K circuits settings attempts D n A prims (fun _ => default) []
    (fun rows _ => ¬ KeysApart D rows) (by simp [KeysApart, RowKey, rowsOf])).trans ?_
  exact LifetimeKeysApartPath.prob_notKeysApart_le prims D (boundaryAdv K circuits settings attempts D n A)
    (fun _ => default) [] (Q + C.n ^ 2)
    (boundary_setupEarly_bound_of_hybrid K circuits settings attempts D n A Q hQ _ _)

/-- S2: a hidden key of the actual selected setup occurs in its boundary cache only at the
standard setup-hit rate with the same complete path budget. -/
theorem setup_keyHit_le_of_hybrid (prims : Primitives) (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q) :
    Pr[fun r => KeyHit D (rowsAt r.1) r.2 |
      worldRun prims (worldSetup K circuits settings attempts D n A)] ≤
      ((2 * (Q + C.n ^ 2) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (setup_event_le K circuits settings attempts D n A prims (fun _ => default) []
    (KeyHit D) (by simp [KeyHit, RowKey, rowsOf])).trans ?_
  exact LifetimePathCount.setupHit_le prims D (boundaryAdv K circuits settings attempts D n A)
    (fun _ => default) [] (Q + C.n ^ 2)
    (boundary_setupEarly_bound_of_hybrid K circuits settings attempts D n A Q hQ _ _)


end Driver

section SourceBudget

open LifetimeRunBoundary

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (circuitsOf : (HashInput → HashOutput) → Circuits) (D : C.Coalition) (A : LifetimeAdversary C E)
variable (Q : ℕ) (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
include hQ

/-- The concrete setup bridge's complete counted budget, from the original lifetime premise. -/
theorem boundary_setupEarly_bound (n : ℕ) (values : MpcDomain → HashOutput)
    (x : C.Party → Keys C) (z : Aux) :
    let B := boundaryAdv K (circuitsOf (thOf values)) settings attempts D n A
    IsQueryBoundP (setupEarly D B (B.start (corruptInputs D x) z)) Counted (Q + C.n ^ 2) :=
  boundary_setupEarly_bound_of_hybrid K _ settings attempts D n A Q
    (LifetimeRealBad.hybridBudget K settings attempts circuitsOf D A Q hQ n values) x z

/-- S1 for the exact selected lifetime boundary under `HasLifetimeQueryBoundAll`. -/
theorem setup_keysApart_le (aes : Aes) (n : ℕ) (values : MpcDomain → HashOutput) :
    Pr[fun r => ¬ KeysApart D (rowsAt r.1) |
      worldRun ⟨thOf values, aes⟩ (worldSetup K (circuitsOf (thOf values)) settings attempts D n A)] ≤
      ((Q + C.n ^ 2 : ℕ) : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 +
        ((Fintype.card (C.Party × C.Party × C.Term × C.Term) +
          Fintype.card (C.Party × C.Party × C.Party × C.Party) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (revealPairs C : ℝ≥0∞) / 2 ^ 256 :=
  setup_keysApart_le_of_hybrid K _ settings attempts D n A ⟨thOf values, aes⟩ Q
    (LifetimeRealBad.hybridBudget K settings attempts circuitsOf D A Q hQ n values)

/-- S2 for the exact selected lifetime boundary under `HasLifetimeQueryBoundAll`. -/
theorem setup_keyHit_le (aes : Aes) (n : ℕ) (values : MpcDomain → HashOutput) :
    Pr[fun r => KeyHit D (rowsAt r.1) r.2 |
      worldRun ⟨thOf values, aes⟩ (worldSetup K (circuitsOf (thOf values)) settings attempts D n A)] ≤
      ((2 * (Q + C.n ^ 2) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  setup_keyHit_le_of_hybrid K _ settings attempts D n A ⟨thOf values, aes⟩ Q
    (LifetimeRealBad.hybridBudget K settings attempts circuitsOf D A Q hQ n values)

end SourceBudget


/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.request_replaceSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms request_replaceSteps

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.runTo_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runTo_reconstruct

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.setup4_beforeStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setup4_beforeStart

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.boundary_setupEarly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_setupEarly

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.setup_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setup_event_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.boundary_setupEarly_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_setupEarly_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.setup_keysApart_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setup_keysApart_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSetupBridge.setup_keyHit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setup_keyHit_le


end ThresholdLeanXmssSecurity.LifetimeSetupBridge
