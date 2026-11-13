import ThresholdLeanXmssSecurity.Proof.LifetimeLemmas
import ThresholdLeanXmssSecurity.Proof.SeedHit

/-!
# Ceremony indices of the lifetime scheduler

The lifetime scheduler increments one tree counter on each accepted start. Settling a
ceremony, advancing its rounds, and serving signing requests preserve these counters.
The counters bound every active ceremony index by `lifetimeRuns attempts`.
-/

open OracleComp OracleSpec

noncomputable section

set_option maxRecDepth 100000
set_option pp.deepTerms false

namespace ThresholdLeanXmssSecurity
namespace LifetimeProof

open LeanXmss ThresholdLeanXmss

attribute [local instance] Classical.propDecidable
local instance : DecidableEq ThresholdLeanXmss.Tree := Classical.decEq _

variable {C : Committee} {E : Type}

/-- Each tree has at most the prescribed number of attempts; an active run has been counted. -/
def RunInvariant (attempts : ℕ) (st : LifetimeState C E) : Prop :=
  st.topRuns ≤ attempts ∧ (∀ b, st.bottomRuns b ≤ attempts) ∧
    (st.running ≠ none → 0 < st.runCount)

@[simp] theorem settle_topRuns (D : C.Coalition) (st : LifetimeState C E) :
    (st.settle D).topRuns = st.topRuns := by
  unfold LifetimeState.settle
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

@[simp] theorem settle_bottomRuns (D : C.Coalition) (st : LifetimeState C E) :
    (st.settle D).bottomRuns = st.bottomRuns := by
  unfold LifetimeState.settle
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

@[simp] theorem settle_runCount (D : C.Coalition) (st : LifetimeState C E) :
    (st.settle D).runCount = st.runCount := by
  simp [LifetimeState.runCount]

theorem settle_running (D : C.Coalition) (st : LifetimeState C E)
    (h : (st.settle D).running ≠ none) : (st.settle D).running = st.running := by
  cases hr : st.running with
  | none => simp [LifetimeState.settle, hr]
  | some r =>
    rcases r with ⟨tree, fuel, steps⟩
    by_cases hd : fuel = 0 ∨ ∀ i, i ∉ D.1 → (steps i).isDone
    · cases tree <;> simp [LifetimeState.settle, hr, hd] at h
    · simp only [LifetimeState.settle, hr, if_neg hd]

theorem RunInvariant.settle {attempts : ℕ} {st : LifetimeState C E}
    (h : RunInvariant attempts st) (D : C.Coalition) : RunInvariant attempts (st.settle D) := by
  refine ⟨by simpa using h.1, by simpa using h.2.1, fun hr => ?_⟩
  rw [settle_runCount]
  exact h.2.2 (by rw [← settle_running D st hr]; exact hr)

theorem RunInvariant.runCount_le {attempts : ℕ} {st : LifetimeState C E}
    (h : RunInvariant attempts st) : st.runCount ≤ lifetimeRuns attempts := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun b _ => h.2.1 b
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  unfold LifetimeState.runCount lifetimeRuns
  nlinarith [h.1]

theorem RunInvariant.round_index {attempts : ℕ} {st : LifetimeState C E}
    (h : RunInvariant attempts st) (hr : st.running ≠ none) :
    st.runCount - 1 < lifetimeRuns attempts := by
  have hp := h.2.2 hr
  have hb := h.runCount_le
  omega

/-- The counter of the chosen tree. -/
def runsAt (st : LifetimeState C E) : ThresholdLeanXmss.Tree → ℕ
  | .top => st.topRuns
  | .bottom b => st.bottomRuns b

/-- The counter update made by an admitted start. -/
def increment (st : LifetimeState C E) : ThresholdLeanXmss.Tree → LifetimeState C E
  | .top => { st with topRuns := st.topRuns + 1 }
  | .bottom b => { st with bottomRuns := Function.update st.bottomRuns b (st.bottomRuns b + 1) }

theorem increment_runCount (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) :
    (increment st tree).runCount = st.runCount + 1 := by
  cases tree with
  | top => simp [increment, LifetimeState.runCount, Nat.add_right_comm]
  | bottom b =>
    simp only [increment, LifetimeState.runCount]
    rw [Finset.sum_update_of_mem (Finset.mem_univ b)]
    have hs := Finset.sum_erase_add Finset.univ st.bottomRuns (Finset.mem_univ b)
    rw [Finset.sdiff_singleton_eq_erase]
    omega

theorem increment_runsAt (st : LifetimeState C E) (tree other : ThresholdLeanXmss.Tree) :
    runsAt (increment st tree) other = runsAt st other + if tree = other then 1 else 0 := by
  cases tree <;> cases other <;> simp [increment, runsAt, Function.update_apply]
  split_ifs <;> simp_all

theorem RunInvariant.started {attempts : ℕ} {st : LifetimeState C E}
    (h : RunInvariant attempts st) (tree : ThresholdLeanXmss.Tree)
    (hlt : runsAt st tree < attempts) (D : C.Coalition) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput) :
    RunInvariant attempts (({ increment st tree with running := some (tree, fuel, steps) }).settle D) := by
  apply RunInvariant.settle
  have hp : 0 < (increment st tree).runCount := by rw [increment_runCount]; omega
  refine ⟨?_, ?_, fun _ => hp⟩
  · have ht := h.1
    cases tree <;> simp only [increment, runsAt] at * <;> omega
  · intro b
    cases tree with
    | top => exact h.2.1 b
    | bottom a =>
      change Function.update st.bottomRuns a (st.bottomRuns a + 1) b ≤ attempts
      by_cases heq : b = a
      · subst b
        simpa [runsAt] using Nat.succ_le_of_lt hlt
      · simpa [Function.update_of_ne heq] using h.2.1 b

section Scheduler

variable [Field E] [Algebra Bit E]
variable {ι : Type} {spec : OracleSpec ι}
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (Ro : ℕ → Roles C (OracleComp spec)) (base : Roles C (OracleComp spec))
variable (D : C.Coalition) (keys : C.Party → Keys C) (value : Point → OracleComp spec Digest) (h : C.Party)

/-- A successful start response records precisely one newly started tree. -/
def newRun (q : (LifetimeSpec C E).Domain) : (LifetimeSpec C E).Range q → Option ThresholdLeanXmss.Tree :=
  match q with
  | .start tree => fun response => response.map fun _ => tree
  | _ => fun _ => none

/-- The signing branch, with the lifetime's per-operator dealer and cleared tree memo. -/
def signAs (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E) :
    OracleComp spec ((TsigSpec C).Range q × LifetimeState C E) := do
  let (answer, sign) ← (tsigOracles
    (fun oa => base.honest (liftComp oa _))
    (signerDealt (fun oa => base.honest (liftComp oa _)) keys value st i) q).run st.sign
  pure (answer, { st with sign := { sign with trees := fun _ => none } })

omit [Field E] [Algebra Bit E] in
theorem signAs_frame (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E) r
    (hr : r ∈ support (signAs base keys value i q st)) :
    (∀ tree, runsAt r.2 tree = runsAt st tree) ∧ r.2.running = st.running := by
  unfold signAs at hr
  obtain ⟨⟨answer, sign⟩, _, hr⟩ := (mem_support_bind_iff (m := OracleComp spec) _ _ _).mp hr
  change r = (answer, { st with sign := { sign with trees := fun _ => none } }) at hr
  subst r
  exact ⟨fun tree => by cases tree <;> rfl, rfl⟩

def blockedSign (st : LifetimeState C E) (i : C.Party) (e : KeyIndex) : Prop :=
  st.running.map (·.1) = some (.bottom (treeOf e)) ∨ st.bottom i (treeOf e) = none

def canStart (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) : Prop :=
  st.running = none ∧ match tree with
  | .top => st.topRuns < attempts ∧ ∃ i, i ∉ D.1 ∧ st.top i = none
  | .bottom b => st.bottomRuns b < attempts ∧ b ∉ st.signed ∧
      (∀ i, i ∉ D.1 → (st.top i).isSome) ∧ ∃ i, i ∉ D.1 ∧ st.bottom i b = none

omit [Field E] [Algebra Bit E] in
theorem canStart_lt {st : LifetimeState C E} {tree : ThresholdLeanXmss.Tree}
    (hc : canStart attempts D st tree) : runsAt st tree < attempts := by
  cases tree <;> exact hc.2.1

theorem run_sign_tree (b : Fin (2 ^ layerHeight)) (st : LifetimeState C E) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.sign (.tree b))).run st =
      signAs base keys value h (.tree b) st := rfl

theorem run_round1 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (st : LifetimeState C E) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h
      (.sign (.round1 i J e message))).run st =
      if blockedSign st i e then pure (none, st) else
        signAs base keys value i (.round1 i J e message) { st with signed := insert (treeOf e) st.signed } := by
  simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp only [blockedSign, *, StateT.run_bind, StateT.run_pure, pure_bind,
    StateT.run_set, Bool.false_eq_true, if_false, if_true] <;> rfl

theorem run_round2 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (st : LifetimeState C E) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h
      (.sign (.round2 i J e message parts))).run st =
      if blockedSign st i e then pure (none, st) else
        signAs base keys value i (.round2 i J e message parts)
          { st with signed := insert (treeOf e) st.signed } := by
  simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp only [blockedSign, *, StateT.run_bind, StateT.run_pure, pure_bind,
    StateT.run_set, Bool.false_eq_true, if_false, if_true] <;> rfl

theorem run_start (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.start tree)).run st =
      if ¬canStart attempts D st tree then pure (none, st) else (do
        let steps ← startSteps (Ro st.runCount) D fun i =>
          (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree :
            PartyM C E RealSpec TreeOutput)
        pure (some (toCoalition D steps),
          ({ increment st tree with running := some (tree, ceremonyFuel circuits settings, steps) }).settle D)) := by
  cases tree <;>
    simp only [lifetimeOraclesWith, canStart, increment, StateT.run_bind, StateT.run_get, pure_bind] <;>
    split <;>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc] <;> rfl

theorem run_round (sent : C.Party → C.Party → Option (Msg E)) (st : LifetimeState C E) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.round sent)).run st =
      (match st.running with
      | none => pure (none, st)
      | some (tree, fuel, steps) => do
        let (_, next, _) ← stepRound (Ro (st.runCount - 1)) D (roundAdversary (I := PEmpty) sent)
          noFunctionality () steps
        pure (some (toCoalition D next), ({ st with running := some (tree, fuel - 1, next) }).settle D)) := by
  cases hr : st.running with
  | none => simp [lifetimeOraclesWith, hr, StateT.run_bind, StateT.run_get, StateT.run_pure]
  | some r =>
    rcases r with ⟨tree, fuel, steps⟩
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind, hr,
      StateT.run_lift, StateT.run_set, StateT.run_pure, bind_assoc]

/-- The observable scheduler transition, independent of the oracle answers. -/
def RunStep (st : LifetimeState C E) (q : (LifetimeSpec C E).Domain)
    (r : (LifetimeSpec C E).Range q × LifetimeState C E) : Prop :=
  (∀ tree, runsAt r.2 tree = runsAt st tree + if newRun q r.1 = some tree then 1 else 0) ∧
    match newRun q r.1 with
    | some tree => runsAt st tree < attempts
    | none => r.2.running ≠ none → st.running ≠ none

omit [Field E] [Algebra Bit E] in
theorem runStep_noStart {q : (LifetimeSpec C E).Domain} {st : LifetimeState C E}
    {r : (LifetimeSpec C E).Range q × LifetimeState C E}
    (hnew : newRun q r.1 = none) (hc : ∀ tree, runsAt r.2 tree = runsAt st tree)
    (hrun : r.2.running ≠ none → st.running ≠ none) : RunStep attempts st q r := by
  exact ⟨by simpa [hnew] using hc, by simpa [hnew] using hrun⟩

theorem step_corrupt (i : C.Party) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range (.sign (.corrupt i)) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.sign (.corrupt i))).run st)) :
    RunStep attempts st (.sign (.corrupt i)) r := by
  have heq : r = (none, st) := hr
  subst r
  exact runStep_noStart attempts rfl (fun _ => rfl) id

theorem step_tree (b : Fin (2 ^ layerHeight)) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range (.sign (.tree b)) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.sign (.tree b))).run st)) :
    RunStep attempts st (.sign (.tree b)) r := by
  rw [run_sign_tree] at hr
  have hf := signAs_frame base keys value h (.tree b) st r hr
  exact runStep_noStart attempts rfl hf.1 (hf.2 ▸ id)

theorem step_round1 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range (.sign (.round1 i J e message)) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.sign (.round1 i J e message))).run st)) :
    RunStep attempts st (.sign (.round1 i J e message)) r := by
  rw [run_round1] at hr
  split at hr
  · have heq : r = (none, st) := hr
    subst r
    exact runStep_noStart attempts rfl (fun _ => rfl) id
  · have hf := signAs_frame base keys value i (.round1 i J e message) _ r hr
    exact runStep_noStart attempts rfl hf.1 (hf.2 ▸ id)

theorem step_round2 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range (.sign (.round2 i J e message parts)) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.sign (.round2 i J e message parts))).run st)) :
    RunStep attempts st (.sign (.round2 i J e message parts)) r := by
  rw [run_round2] at hr
  split at hr
  · have heq : r = (none, st) := hr
    subst r
    exact runStep_noStart attempts rfl (fun _ => rfl) id
  · have hf := signAs_frame base keys value i (.round2 i J e message parts) _ r hr
    exact runStep_noStart attempts rfl hf.1 (hf.2 ▸ id)

theorem step_publicKey  (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range (.publicKey) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.publicKey)).run st)) :
    RunStep attempts st (.publicKey) r := by
  have heq : r = (st.publicKey (keys h).parameter h, st) := hr
  subst r
  exact runStep_noStart attempts rfl (fun _ => rfl) id

omit [Field E] [Algebra Bit E] in
theorem RunStep.start (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E)
    (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput) (hlt : runsAt st tree < attempts) :
    RunStep attempts st (.start tree) (some (toCoalition D steps),
      ({ increment st tree with running := some (tree, fuel, steps) }).settle D) := by
  refine ⟨?_, hlt⟩
  intro other
  cases other with
  | top => simpa only [runsAt, settle_topRuns, newRun, Option.map_some,
      Option.some.injEq] using increment_runsAt st tree .top
  | bottom b => simpa only [runsAt, settle_bottomRuns, newRun, Option.map_some,
      Option.some.injEq] using increment_runsAt st tree (.bottom b)

theorem step_start (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range (.start tree) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.start tree)).run st)) :
    RunStep attempts st (.start tree) r := by
  rw [run_start] at hr
  split at hr
  · have heq : r = (none, st) := hr
    subst r
    exact runStep_noStart attempts rfl (fun _ => rfl) id
  · rename_i hcan
    obtain ⟨steps, _, hr⟩ := (mem_support_bind_iff (m := OracleComp spec)
      (startSteps (Ro st.runCount) D fun i =>
        (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree :
          PartyM C E RealSpec TreeOutput))
      (fun steps => pure (some (toCoalition D steps),
        ({ increment st tree with running := some (tree, ceremonyFuel circuits settings, steps) }).settle D)) r).mp hr
    change r = _ at hr
    subst r
    exact RunStep.start attempts D tree st (ceremonyFuel circuits settings) steps
      (canStart_lt attempts D (not_not.mp hcan))

theorem step_round (sent : C.Party → C.Party → Option (Msg E)) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range (.round sent) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.round sent)).run st)) :
    RunStep attempts st (.round sent) r := by
  rw [run_round] at hr
  cases hrun : st.running with
  | none =>
    rw [hrun] at hr
    have heq : r = (none, st) := hr
    subst r
    exact runStep_noStart attempts rfl (fun _ => rfl) id
  | some out =>
    rcases out with ⟨tree, fuel, steps⟩
    rw [hrun] at hr
    obtain ⟨⟨_, next, _⟩, _, hr⟩ := (mem_support_bind_iff (m := OracleComp spec)
      (stepRound (Ro (st.runCount - 1)) D (roundAdversary (I := PEmpty) sent) noFunctionality () steps)
      (fun out => pure (some (toCoalition D out.2.1),
        ({ st with running := some (tree, fuel - 1, out.2.1) }).settle D)) r).mp hr
    change r = _ at hr
    subst r
    exact runStep_noStart attempts rfl
      (fun tree => by cases tree <;> simp [runsAt]) (fun _ => by simp [hrun])

theorem lifetimeOracles_step (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range q × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st)) :
    RunStep attempts st q r := by
  cases q with
  | sign q =>
    cases q with
    | corrupt i => exact step_corrupt K circuits settings attempts Ro base D keys value h i st r hr
    | tree b => exact step_tree K circuits settings attempts Ro base D keys value h b st r hr
    | round1 i J e message => exact step_round1 K circuits settings attempts Ro base D keys value h i J e message st r hr
    | round2 i J e message parts => exact step_round2 K circuits settings attempts Ro base D keys value h i J e message parts st r hr
  | publicKey => exact step_publicKey K circuits settings attempts Ro base D keys value h st r hr
  | start tree => exact step_start K circuits settings attempts Ro base D keys value h tree st r hr
  | round sent => exact step_round K circuits settings attempts Ro base D keys value h sent st r hr

theorem lifetimeOracles_runs (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range q × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st)) :
    ∀ tree, runsAt r.2 tree = runsAt st tree + if newRun q r.1 = some tree then 1 else 0 :=
  (lifetimeOracles_step K circuits settings attempts Ro base D keys value h q st r hr).1

theorem lifetimeOracles_control (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range q × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st)) :
    match newRun q r.1 with
    | some tree => runsAt st tree < attempts
    | none => r.2.running ≠ none → st.running ≠ none :=
  (lifetimeOracles_step K circuits settings attempts Ro base D keys value h q st r hr).2

end Scheduler

theorem runCount_eq_of_runsAt {left right : LifetimeState C E}
    (heq : ∀ tree, runsAt left tree = runsAt right tree) : left.runCount = right.runCount := by
  unfold LifetimeState.runCount
  have htop : left.topRuns = right.topRuns := heq .top
  exact congrArg₂ Nat.add htop (Finset.sum_congr rfl fun b _ => heq (.bottom b))

section Invariant

variable [Field E] [Algebra Bit E]
variable {ι : Type} {spec : OracleSpec ι}
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (Ro : ℕ → Roles C (OracleComp spec)) (base : Roles C (OracleComp spec))
variable (D : C.Coalition) (keys : C.Party → Keys C) (value : Point → OracleComp spec Digest) (h : C.Party)

theorem lifetimeOracles_runCount (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (r : (LifetimeSpec C E).Range q × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st)) :
    r.2.runCount = st.runCount + (newRun q r.1).toList.length := by
  have hc := lifetimeOracles_runs K circuits settings attempts Ro base D keys value h q st r hr
  cases hn : newRun q r.1 with
  | none =>
    simp only [Option.toList_none, List.length_nil, Nat.add_zero]
    exact runCount_eq_of_runsAt (by simpa [hn] using hc)
  | some tree =>
    simp only [Option.toList_some, List.length_singleton]
    rw [← increment_runCount st tree]
    apply runCount_eq_of_runsAt
    intro other
    rw [hc, hn, increment_runsAt]
    simp

/-- The concrete lifetime oracle preserves the scheduler invariant on every answer branch. -/
theorem lifetimeOracles_invariant (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (hs : RunInvariant attempts st) (r : (LifetimeSpec C E).Range q × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st)) :
    RunInvariant attempts r.2 := by
  have hc := lifetimeOracles_runs K circuits settings attempts Ro base D keys value h q st r hr
  have hcontrol := lifetimeOracles_control K circuits settings attempts Ro base D keys value h q st r hr
  have hn := lifetimeOracles_runCount K circuits settings attempts Ro base D keys value h q st r hr
  have hb : ∀ tree, runsAt st tree ≤ attempts := by
    intro tree
    cases tree with
    | top => exact hs.1
    | bottom b => exact hs.2.1 b
  have hbound : ∀ tree, runsAt r.2 tree ≤ attempts := by
    intro tree
    rw [hc]
    by_cases heq : newRun q r.1 = some tree
    · simp only [heq] at hcontrol
      simp only [heq, if_true]
      omega
    · simpa [heq] using hb tree
  refine ⟨hbound .top, fun b => hbound (.bottom b), fun hrunning => ?_⟩
  cases heq : newRun q r.1 with
  | none =>
    simp only [heq] at hcontrol
    have hp := hs.2.2 (hcontrol hrunning)
    simp only [heq, Option.toList_none, List.length_nil, Nat.add_zero] at hn
    omega
  | some tree =>
    simp only [heq, Option.toList_some, List.length_singleton] at hn
    omega

/-- The local adversary interface used between lifetime requests. -/
def lifetimeSourceOracles : QueryImpl (LocalSpec C + LifetimeSpec C E)
    (StateT (LifetimeState C E) (OracleComp spec)) :=
  (fun t => StateT.lift (base.adversary (OracleComp.lift (OracleSpec.query t)))) +
    lifetimeOraclesWith K circuits settings attempts Ro base D keys value h

theorem lifetimeSource_step_invariant (q : (LocalSpec C + LifetimeSpec C E).Domain)
    (s : LifetimeState C E) (hstate : RunInvariant attempts s)
    (z : (LocalSpec C + LifetimeSpec C E).Range q × LifetimeState C E)
    (hz : z ∈ support ((lifetimeSourceOracles K circuits settings attempts Ro base D keys value h q).run s)) :
    RunInvariant attempts z.2 := by
  cases q with
  | inl q =>
    change z ∈ support ((StateT.lift (base.adversary (OracleComp.lift (OracleSpec.query q))) :
      StateT (LifetimeState C E) (OracleComp spec) _).run s) at hz
    rw [StateT.run_lift] at hz
    obtain ⟨a, _, hz⟩ := (mem_support_bind_iff (m := OracleComp spec) _ _ _).mp hz
    change z = (a, s) at hz
    subst z
    exact hstate
  | inr q =>
    exact lifetimeOracles_invariant K circuits settings attempts Ro base D keys value h q s hstate z hz


theorem lifetimeSource_invariant {α : Type} (source : OracleComp (LocalSpec C + LifetimeSpec C E) α)
    (st : LifetimeState C E) (hs : RunInvariant attempts st)
    (r : α × LifetimeState C E)
    (hr : r ∈ support ((simulateQ
      (lifetimeSourceOracles K circuits settings attempts Ro base D keys value h) source).run st)) :
    RunInvariant attempts r.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (RunInvariant attempts)
    (lifetimeSource_step_invariant K circuits settings attempts Ro base D keys value h) source st hs r hr

/-- The initial scheduler state after the key generation stage of `lifetimeGameWith`. -/
def initial (D : C.Coalition) : LifetimeState C E :=
  ⟨⟨D.1, fun _ => none, [], fun _ => none⟩, fun _ => none, fun _ _ => none,
    0, fun _ => 0, ∅, none⟩

omit [Field E] [Algebra Bit E] in
theorem initial_invariant : RunInvariant attempts (initial (E := E) D) := by
  simp [RunInvariant, initial]

/-- Every actual scheduler prefix has the advertised total number of runs and a valid active index. -/
theorem lifetimeSource_run_bound {α : Type}
    (source : OracleComp (LocalSpec C + LifetimeSpec C E) α)
    (r : α × LifetimeState C E)
    (hr : r ∈ support ((simulateQ
      (lifetimeSourceOracles K circuits settings attempts Ro base D keys value h) source).run (initial D))) :
    r.2.topRuns ≤ attempts ∧ (∀ b, r.2.bottomRuns b ≤ attempts) ∧
      r.2.runCount ≤ lifetimeRuns attempts ∧
        (r.2.running ≠ none → r.2.runCount - 1 < lifetimeRuns attempts) := by
  have hi := lifetimeSource_invariant K circuits settings attempts Ro base D keys value h source
    (initial D) (initial_invariant attempts D) r hr
  exact ⟨hi.1, hi.2.1, hi.runCount_le, hi.round_index⟩

omit [Field E] [Algebra Bit E] in
theorem RunInvariant.start_index {st : LifetimeState C E} (hi : RunInvariant attempts st)
    {tree : ThresholdLeanXmss.Tree} (hc : canStart attempts D st tree) :
    st.runCount < lifetimeRuns attempts := by
  have hb := (hi.started tree (canStart_lt attempts D hc) D 0 (fun _ => .done none)).runCount_le
  rw [settle_runCount] at hb
  change (increment st tree).runCount ≤ lifetimeRuns attempts at hb
  rw [increment_runCount] at hb
  omega

/-- Every role lookup made by an admitted start is within the fixed hybrid index set. -/
theorem lifetimeOracles_start_index (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E)
    (hi : RunInvariant attempts st)
    (r : (LifetimeSpec C E).Range (.start tree) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.start tree)).run st))
    (hsome : r.1 ≠ none) : st.runCount < lifetimeRuns attempts := by
  have hc := lifetimeOracles_control K circuits settings attempts Ro base D keys value h (.start tree) st r hr
  have hb := (lifetimeOracles_invariant K circuits settings attempts Ro base D keys value h (.start tree) st hi r hr).runCount_le
  have hn := lifetimeOracles_runCount K circuits settings attempts Ro base D keys value h (.start tree) st r hr
  cases heq : r.1 with
  | none => exact (hsome heq).elim
  | some messages =>
    simp only [newRun, heq, Option.map_some, Option.toList_some, List.length_singleton] at hn
    omega

/-- Roles outside the finite ceremony index set do not affect a scheduler request. -/
theorem lifetimeOracles_roles_congr (Ro' : ℕ → Roles C (OracleComp spec))
    (heq : ∀ n < lifetimeRuns attempts, Ro n = Ro' n)
    (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E) (hi : RunInvariant attempts st) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st =
      (lifetimeOraclesWith K circuits settings attempts Ro' base D keys value h q).run st := by
  cases q with
  | sign q => cases q <;> rfl
  | publicKey => rfl
  | start tree =>
    simp only [run_start]
    split
    · rfl
    · rename_i hc
      rw [heq st.runCount (hi.start_index attempts D (not_not.mp hc))]
  | round sent =>
    simp only [run_round]
    cases hr : st.running with
    | none => rfl
    | some running =>
      rcases running with ⟨tree, fuel, steps⟩
      rw [heq (st.runCount - 1) (hi.round_index (by simp [hr]))]

/-- The complete adaptive source has the same syntax under roles agreeing on every possible run index. -/
theorem lifetimeSource_roles_congr (Ro' : ℕ → Roles C (OracleComp spec))
    (heq : ∀ n < lifetimeRuns attempts, Ro n = Ro' n)
    {α : Type} (source : OracleComp (LocalSpec C + LifetimeSpec C E) α)
    (st : LifetimeState C E) (hi : RunInvariant attempts st) :
    (simulateQ (lifetimeSourceOracles K circuits settings attempts Ro base D keys value h) source).run st =
      (simulateQ (lifetimeSourceOracles K circuits settings attempts Ro' base D keys value h) source).run st := by
  have hstep : ∀ q s, RunInvariant attempts s →
      (lifetimeSourceOracles K circuits settings attempts Ro base D keys value h q).run s =
        (lifetimeSourceOracles K circuits settings attempts Ro' base D keys value h q).run s := by
    intro q s hs
    cases q with
    | inl q => rfl
    | inr q => exact lifetimeOracles_roles_congr K circuits settings attempts Ro base D keys value h Ro' heq q s hs
  induction source using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [← hstep q st hi]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro middle hm
    apply ih middle.1 middle.2
    exact lifetimeSource_step_invariant K circuits settings attempts Ro base D keys value h q st hi middle hm


end Invariant

section Game

variable [Field E] [Algebra Bit E]
variable {ι : Type} {spec : OracleSpec ι}

/-- Ceremony roles beyond the fixed run budget are irrelevant to the entire lifetime program. -/
theorem lifetimeGame_roles_congr (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (attempts : ℕ) (Ro Ro' : ℕ → Roles C (OracleComp spec))
    (base : Roles C (OracleComp spec)) (D : C.Coalition) (A : LifetimeAdversary C E)
    (heq : ∀ n < lifetimeRuns attempts, Ro n = Ro' n) :
    lifetimeGameWith K circuits settings attempts Ro base D A =
      lifetimeGameWith K circuits settings attempts Ro' base D A := by
  unfold lifetimeGameWith
  apply bind_congr
  intro state
  apply bind_congr
  rintro ⟨state, outputs⟩
  dsimp only
  split
  · rename_i h hfound
    split
    · rfl
    · let keys := fun i => (outputs i).getD default
      let value := fun point => base.honest (liftComp (prfValue (honestSeeds D keys) point) _)
      have hc := lifetimeSource_roles_congr K circuits settings attempts Ro base D keys value h Ro' heq
        (A.run state (keys h).parameter) (initial D) (initial_invariant attempts D)
      change (simulateQ (lifetimeSourceOracles K circuits settings attempts Ro base D keys value h)
        (A.run state (keys h).parameter)).run (initial D) >>= _ =
          (simulateQ (lifetimeSourceOracles K circuits settings attempts Ro' base D keys value h)
            (A.run state (keys h).parameter)).run (initial D) >>= _
      rw [hc]
  · rfl

end Game

end LifetimeProof
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.LifetimeProof.lifetimeOracles_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeProof.lifetimeOracles_step

/-- info: 'ThresholdLeanXmssSecurity.LifetimeProof.lifetimeSource_run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeProof.lifetimeSource_run_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeProof.lifetimeOracles_start_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeProof.lifetimeOracles_start_index

/-- info: 'ThresholdLeanXmssSecurity.LifetimeProof.lifetimeGame_roles_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeProof.lifetimeGame_roles_congr
