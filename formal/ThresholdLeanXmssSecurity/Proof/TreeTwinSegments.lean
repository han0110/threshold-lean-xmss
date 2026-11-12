import ThresholdLeanXmssSecurity.Proof.TreeTwinLinked2
import ThresholdLeanXmssSecurity.Proof.TreeAssembly

/-! Segment coupling of the actual ceremony runs. Reachability and fuel are retained
through the segment induction; observation uses the existing swap-cache relation. -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeTwinSegment

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

section Generic

variable {σ₁ σ₂ Ia₁ Ia₂ I₁ I₂ O₁ O₂ L₁ L₂ R₁ R₂ α₁ α₂ : Type}
  (Ro₁ : Roles C (StateT σ₁ ProbComp)) (Ro₂ : Roles C (StateT σ₂ ProbComp))
  (D₁ D₂ : C.Coalition) (A₁ : Adversary C E Ia₁ L₁ R₁) (A₂ : Adversary C E Ia₂ L₂ R₂)
  (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂)

-- Ported from .claude/design/TwinSeg_Seg1.lean; uses the existing executeRounds_add.
/-- Lockstep up to bad with steps of several rounds. `R n` holds at the round count `n`,
and `total` is the round budget. -/
theorem relTriple_executeRounds_segments (Bad : σ₁ → Prop)
    (R : ℕ → (A₁.State × (C.Party → Step C E (CallSpec I₁ O₁) α₁)) × σ₁ →
      (A₂.State × (C.Party → Step C E (CallSpec I₂ O₂) α₂)) × σ₂ → Prop)
    (Q : (A₁.State × (C.Party → Option α₁)) × σ₁ → (A₂.State × (C.Party → Option α₂)) × σ₂ → Prop)
    (total : ℕ)
    (hsticky : ∀ st (steps : C.Party → Step C E (CallSpec I₁ O₁) α₁) s, Bad s →
      ∀ x ∈ support ((stepRound Ro₁ D₁ A₁ F₁ st steps).run s), Bad x.2)
    (hdone : ∀ n c₁ c₂, R n c₁ c₂ → ¬ Bad c₁.2 → (AllDone D₁ c₁.1.2 ↔ AllDone D₂ c₂.1.2))
    (hout : ∀ n c₁ c₂, R n c₁ c₂ → ¬ Bad c₁.2 →
      Q ((c₁.1.1, fun i => (c₁.1.2 i).output), c₁.2) ((c₂.1.1, fun i => (c₂.1.2 i).output), c₂.2))
    (hstep : ∀ n c₁ c₂, n < total → R n c₁ c₂ → ¬ Bad c₁.2 → ¬ AllDone D₁ c₁.1.2 →
      ∃ k, 0 < k ∧ n + k ≤ total ∧
        RelTriple ((executeSteps Ro₁ D₁ A₁ F₁ k c₁.1.1 c₁.1.2).run c₁.2)
          ((executeSteps Ro₂ D₂ A₂ F₂ k c₂.1.1 c₂.1.2).run c₂.2)
          fun x y => Bad x.2 ∨ R (n + k) x y) :
    ∀ m n, total - n = m → n ≤ total → ∀ c₁ c₂, Bad c₁.2 ∨ R n c₁ c₂ →
      RelTriple ((executeRounds Ro₁ D₁ A₁ F₁ (total - n) c₁.1.1 c₁.1.2).run c₁.2)
        ((executeRounds Ro₂ D₂ A₂ F₂ (total - n) c₂.1.1 c₂.1.2).run c₂.2)
        fun x y => Bad x.2 ∨ Q x y := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hm hn c₁ c₂ hc
    by_cases hb : Bad c₁.2
    · exact relTriple_of_support_left fun x hx _ =>
        Or.inl (executeRounds_sticky Ro₁ D₁ A₁ F₁ Bad hsticky _ _ _ _ hb x hx)
    have hR := hc.resolve_left hb
    by_cases hd : AllDone D₁ c₁.1.2
    · have hd₂ := (hdone n c₁ c₂ hR hb).1 hd
      have e₁ : executeRounds Ro₁ D₁ A₁ F₁ (total - n) c₁.1.1 c₁.1.2 =
          pure (c₁.1.1, fun i => (c₁.1.2 i).output) := by
        cases total - n with
        | zero => simp [executeRounds]
        | succ f => rw [executeRounds_succ, if_pos hd]
      have e₂ : executeRounds Ro₂ D₂ A₂ F₂ (total - n) c₂.1.1 c₂.1.2 =
          pure (c₂.1.1, fun i => (c₂.1.2 i).output) := by
        cases total - n with
        | zero => simp [executeRounds]
        | succ f => rw [executeRounds_succ, if_pos hd₂]
      rw [e₁, e₂]
      simp only [StateT.run_pure]
      exact relTriple_pure_pure (Or.inr (hout n c₁ c₂ hR hb))
    · by_cases hlt : n < total
      · obtain ⟨k, hk, hle, step⟩ := hstep n c₁ c₂ hlt hR hb hd
        have split : total - n = k + (total - (n + k)) := by omega
        rw [split, executeRounds_add, executeRounds_add, StateT.run_bind, StateT.run_bind]
        refine relTriple_bind step fun x y hxy => ?_
        exact ih (total - (n + k)) (by omega) (n + k) rfl hle x y hxy
      · have z : total - n = 0 := by omega
        rw [z]
        simp only [executeRounds, StateT.run_pure]
        exact relTriple_pure_pure (Or.inr (hout n c₁ c₂ hR hb))

end Generic

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

-- Ported from .claude/design/TwinSeg_Seg2.lean, using the original ceremony coupling.
/-- `treeSimulationHop` from the ceremony coupling, with no stage structure. -/
theorem treeSimulationHop_of_ceremony (events : TreeSimEvents C E)
    (ceremony : TreeSimCeremonyCoupling prims K circuits settings events)
    (hashBound : TreeSimHashBound circuits settings (treeSimTrace prims K circuits settings events))
    (checkBound : TreeSimCheckBound circuits settings (treeSimTrace prims K circuits settings events)) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  have coupling := treeSim_ghost_coupling prims K circuits settings events
    (treeSim_ceremony_coupling prims K circuits settings events ceremony)
  intro hb top tree D A x z Z q hx hq
  by_cases hsmall : q < 2 ^ 128
  · obtain ⟨parameter, seeds, pairs, hx⟩ := hx
    have heq : x = dealtKeys parameter seeds pairs := funext hx
    subst x
    have hm := congrArg (fun d => d true)
      (treeSim_trace_marginal prims K circuits settings events top tree D A
        (dealtKeys parameter seeds pairs) z Z)
    have hm' : Pr[fun r => r.1 = true | treeSimTrace prims K circuits settings events top tree D A
        (dealtKeys parameter seeds pairs) z Z] =
        Pr[= true | (simulateQ (streamWorld prims D)
          (treeRealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z)).run' (∅, ∅)] := by
      simpa only [← probOutput_def, probOutput_map] using hm
    have hi := congrArg (fun p => Pr[= true | p])
      (treeSim_streamIdeal_eq prims K circuits settings top tree D A parameter seeds pairs z Z)
    simp only [probOutput_map] at hi
    rw [← hm', accepts_eq_worldRun, hi]
    have hc := treeSim_badUnion _ _ (fun r : Bool × Bool × Bool => r.2.1 = true) (fun r => r.2.2 = true)
      (fun r => r.1 = true) (fun b => b = true)
      (coupling hb top tree D A parameter seeds pairs z Z q hq hsmall)
    have dealt : DealtInputs D (dealtKeys parameter seeds pairs) := ⟨parameter, seeds, pairs, fun _ => rfl⟩
    have hh := (hashBound hb top tree D A _ z Z q dealt hq hsmall).trans
      (treeSim_hashBudget circuits settings tree q)
    have hcheck := checkBound hb top tree D A _ z Z q dealt hq hsmall
    simpa only [probEvent_eq_eq_probOutput, add_comm] using hc.trans (add_le_add hh hcheck)
  · exact treeSim_large prims K circuits settings top tree D A x z Z q (Nat.le_of_not_gt hsmall)

/-- The ceremony coupling for `treeSimEvents3`. -/
def TreeSimCeremonyGoal3 : Prop :=
  TreeSimCeremonyCoupling prims K circuits settings (treeSimEvents3 prims K circuits settings)

/-- The sibling of `treeSimulationHop_of_pairs3` above `TreeSimStagesGoal3`. -/
theorem treeSimulationHop_of_pairs3_ceremony
    (ceremony : TreeSimCeremonyGoal3 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_ceremony prims K circuits settings (treeSimEvents3 prims K circuits settings) ceremony
    (treeSimHashBoundGoal3_of_guarded prims K circuits settings honest salt
      (treeSimSaltReuseGuarded_of_pairs splits pairBounds))
    (treeSimCheckBoundGoal3_of_setupBranches3 prims K circuits settings branches)

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop)

/-- The relation of the stages on the actual real state, as `TreeStagesTwinRelation3.R`. -/
def twinR (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ swaps δ, (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) ∧ Req n δ (a.1, treeStagesTwin swaps a.2) b

/-- A step of `k` rounds from the actual real state. -/
def SegStepAt (k n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  n + k + 3 ≤ ceremonyFuel circuits settings ∧
  RelTriple
    ((executeSteps (treeSimRealRoles prims D) D A noFunctionality k a.1.1 a.1.2).run a.2)
    ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality k b.1.1 b.1.2).run b.2)
    (fun u v => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
      twinR D A Req (n + k) u v)

/-- The field `next` of `TreeStagesRelation3` with steps of several rounds. -/
def TreeTwinSegStep : Prop :=
  ∀ n (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → twinR D A Req n a b →
    ∃ k, 0 < k ∧ SegStepAt prims K circuits settings top tree D A parameter seeds pairs z Req k n a b

-- The swap transfer is the next-field proof of treeStages_relation_of_twin3.
/-- One twin round gives one round from the actual real state. Both runners must be active:
`stepRound` itself does not apply the stopping test of `executeSteps`. The fixed twin relation
supplies this agreement in `treeTwinSegStep_of_rounds`. -/
theorem segStepAt_of_round
    (drawn : TreeTwinDigestDrawnGoal3 prims K circuits settings top tree D A parameter seeds pairs z p r)
    (n : ℕ) (δ : HiddenAddress C → Bit) (swaps : List (List Bit × HashOutput × HashOutput))
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (reach : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a)
    (bound : n + 3 ≤ ceremonyFuel circuits settings)
    (good : ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2)
    (active : ¬ AllDone D a.1.2)
    (activeIdeal : ¬ AllDone D b.1.2)
    (salts : ∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1)
    (round : RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
      (fun v w => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
        ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
        Req (n + 1) δ' ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2))) :
    SegStepAt prims K circuits settings top tree D A parameter seeds pairs z Req 1 n a b := by
  refine ⟨treeTwin_progress prims K circuits settings top tree D A _ _ _ n a reach active, ?_⟩
  have real := treeSim_relTriple_support
    (treeStages_round_twin prims D A swaps a.1.1 a.1.2 a.2 salts)
  have real' := relTriple_post_mono real (R' := fun u v =>
      TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
      (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)) (by
    rintro u v ⟨(guess | hit) | good', hu, _⟩
    · exact Or.inl (treeSimBad3_of_bad2 prims K circuits settings top tree D A _ z _
        (Or.inl (Or.inl (Or.inr guess))))
    · exact Or.inl (treeTwin_freeHit3 prims K circuits settings top tree D A parameter seeds pairs z p r
        (fun _ _ _ _ => True) drawn n δ swaps a b reach good salts trivial u hu hit)
    · exact Or.inr good')
  have coupled := treeSim_relTriple_support (treeStages_twin_transfer swaps _ _ real' round)
  simp only [executeSteps, show ¬ (∀ i, i ∉ D.1 → (a.1.2 i).isDone) from active,
    show ¬ (∀ i, i ∉ D.1 → (b.1.2 i).isDone) from activeIdeal,
    if_false, StateT.run_bind, StateT.run_pure]
  apply relTriple_bind coupled
  rintro u w ⟨(bad | bad | ⟨extra, δ', salts', req'⟩), hu, _⟩
  · exact relTriple_pure_pure (Or.inl bad)
  · exact relTriple_pure_pure (Or.inl bad)
  · apply relTriple_pure_pure
    have hpref : a.2.2 <+: u.2.2 := by
      apply treeSimLoggedWorld_prefix prims D (stepRound worldRoles D A noFunctionality a.1.1 a.1.2) a.2 u
      simpa only [simulateQ_stepRound, treeSimRealRoles] using hu
    refine Or.inr ⟨extra ++ swaps, δ', ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact salts' x hx
      · exact treeStages_hiddenSalt_mono D x.1 hpref (salts x hx)
    · rw [← treeStagesTwin_append]
      exact req'


/-- The fixed twin relation supplies the stopping agreement required by the adapter. -/
theorem treeTwinSegStep_of_rounds
    (Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (drawn : TreeTwinDigestDrawnGoal3 prims K circuits settings top tree D A parameter seeds pairs z p r)
    (next : TreeTwinNext3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D Stage)) :
    TreeTwinSegStep prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D Stage) := by
  rintro n a b reach bound good active ⟨swaps, δ, salts, req⟩
  refine ⟨1, by omega, ?_⟩
  exact segStepAt_of_round prims K circuits settings top tree D A parameter seeds pairs z p r
    (treeTwinReq D Stage) drawn n δ swaps a b reach bound good active
    (fun h => active (req.2.2.1.mpr h)) salts
    (next n δ swaps a b reach bound good active salts req)

/-- A supported segment extends the actual retained trace by its full length. -/
theorem treeStages_reach_segment (n k : ℕ) (a u : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a)
    (hu : u ∈ support ((executeSteps (treeSimRealRoles prims D) D A noFunctionality
      k a.1.1 a.1.2).run a.2)) :
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) (n + k) u := by
  unfold TreeStagesReach at reach ⊢
  rw [treeStages_trace_add]
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion]
  exact ⟨a, reach, hu⟩

set_option backward.isDefEq.respectTransparency false in
/-- Assemble the full padded suffix from positive bounded segments of the actual runs. -/
theorem treeSimFinish_of_segments
    (Z : Distinguisher C A.State TreeOutput)
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (entry : TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D Stage))
    (next : TreeTwinSegStep prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D Stage)) :
    RelTriple (treeSimRealFinish prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) Z p.2.1 ((r.2, p.2.2.1.2), p.2.2.2))
      ((treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z p.2.1 p.1).run' r.2)
      (fun a b =>
        let flags := treeSimEvents3 prims K circuits settings top tree D A
          (dealtKeys parameter seeds pairs) z Z a.2
        (flags.1 = true ∨ flags.2 = true) ∨ (a.1 = true ↔ b = true)) := by
  let Bad : TreeSimState C → Prop := fun s =>
    TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z s.2
  let R : ℕ → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop := fun n a b =>
    n + 3 ≤ ceremonyFuel circuits settings ∧
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a ∧ twinR D A (treeTwinReq D Stage) n a b
  have sticky : ∀ st steps s, Bad s →
      ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality st steps).run s),
      Bad u.2 :=
    treeSim_round_bad prims D A Bad (fun _ _ h =>
      treeSimBad3_mono prims K circuits settings top tree D A _ z h)
  have done : ∀ n a b, R n a b → ¬ Bad a.2 → (AllDone D a.1.2 ↔ AllDone D b.1.2) := by
    rintro n a b ⟨_, _, swaps, δ, salts, req⟩ _
    exact req.2.2.1
  have output : ∀ n a b, R n a b → ¬ Bad a.2 →
      TreeStagesSwapFinal D A p.1.1
        ((a.1.1, fun i => (a.1.2 i).output), a.2)
        ((b.1.1, fun i => (b.1.2 i).output), b.2) := by
    rintro n a b ⟨bound, reach, swaps, δ, salts, req⟩ good
    refine ⟨req.2.1, ?_, Or.inr ⟨swaps, δ, salts, req.1.1.symm, req.1.2⟩⟩
    exact treeStages_outputs_of_replay prims K circuits settings top tree D A parameter seeds pairs z p.1
      ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
      (treeStages_reach_outputWitness prims K circuits settings top tree D A parameter seeds pairs z
        p hp padding r hr n bound a reach)
      (fun h => good (treeSimBad3_of_bad prims K circuits settings top tree D A _ z _ h))
      (treeStages_reach_corrupt prims K circuits settings top tree D A _ _ _ n a reach) req.2.2.2.1
  have segment : ∀ n a b, n < ceremonyFuel circuits settings - 3 → R n a b →
      ¬ Bad a.2 → ¬ AllDone D a.1.2 → ∃ k, 0 < k ∧ n + k ≤ ceremonyFuel circuits settings - 3 ∧
      RelTriple
        ((executeSteps (treeSimRealRoles prims D) D A noFunctionality k a.1.1 a.1.2).run a.2)
        ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality k b.1.1 b.1.2).run b.2)
        (fun u v => Bad u.2 ∨ R (n + k) u v) := by
    rintro n a b _ ⟨bound, reach, req⟩ good active
    obtain ⟨k, positive, margin, step⟩ := next n a b reach bound good active req
    refine ⟨k, positive, by omega, ?_⟩
    apply relTriple_post_mono (treeSim_relTriple_support step)
    rintro u v ⟨bad | rel, hu, hv⟩
    · exact Or.inl bad
    · exact Or.inr ⟨margin,
        treeStages_reach_segment prims K circuits settings top tree D A parameter seeds pairs p r
          n k a u reach hu, rel⟩
  rw [treeSimRealFinish_rounds, treeSimIdealFinish_rounds]
  apply relTriple_bind (R := fun a b => Bad a.2 ∨ TreeStagesSwapFinal D A p.1.1 a b)
  · have real : (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree) =
        (fun i => prssSetup i >>= treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs) i) :=
      funext (treeSim_real_cont K circuits settings top tree (dealtKeys parameter seeds pairs))
    have ideal : treeSimProgram K circuits settings D parameter
        (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2 top tree =
        (fun i => prssSetup i >>= treeSimIdealCont K circuits settings top tree D parameter
          (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2 i) :=
      funext (treeSim_ideal_cont K circuits settings top tree D parameter
        (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2)
    have hidden := treeSimCommonPrefix_hidden prims circuits settings top tree D A parameter seeds pairs z p hp
    have fuel : ceremonyFuel circuits settings = (ceremonyFuel circuits settings - 3) + 3 := by
      unfold ceremonyFuel setupRounds
      omega
    rw [real, ideal, ← hidden, fuel]
    apply treeSim_prssSetup_continuations prims D A p.2.1 _ _ _ _
      (fun a b => Bad a.2 ∨ R 0 a b)
    · intro u hu
      apply relTriple_post_mono (treeSim_relTriple_support (entry u hu))
      rintro a b ⟨bad | ⟨δ, req⟩, ha, hb⟩
      · exact Or.inl bad
      · refine Or.inr ⟨?_, ?_, [], δ, fun x hx => by simp at hx, req⟩
        · unfold ceremonyFuel setupRounds
          omega
        · exact treeStages_reach_entry prims K circuits settings top tree D A _ _ _ u hu a ha
    · intro a b hab
      simpa only [Nat.sub_zero] using
        relTriple_executeRounds_segments (treeSimRealRoles prims D) (treeSimIdealRoles prims D)
          D D A A noFunctionality noFunctionality Bad R (TreeStagesSwapFinal D A p.1.1)
          (ceremonyFuel circuits settings - 3) sticky done output segment
          (ceremonyFuel circuits settings - 3) 0 (Nat.sub_zero _) (Nat.zero_le _) a b hab
  · intro a b hab
    rcases hab with bad | rel
    · apply relTriple_of_support_left
      intro x hx _
      apply Or.inl
      apply (treeSimEvents3_bad prims K circuits settings top tree D A _ z Z x.2).mpr
      exact treeSimBad3_mono prims K circuits settings top tree D A _ z
        (treeSim_observe_prefix prims D A Z a x hx) bad
    · apply relTriple_post_mono (treeStages_observe_swapFinal prims D A Z p.1.1 a b rel)
      rintro x y (bad | eq)
      · exact Or.inl (Or.inl (by simp [treeSimEvents3, TreeSimHashBad3, TreeSimHashBad2, bad]))
      · exact Or.inr (by rw [eq])

end Fields

/-- `TreeTwinStageCoreGoal3` with steps of several rounds from the actual real state. -/
def TreeTwinSegCoreGoal3 : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop,
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage) ∧
    TreeTwinSegStep prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage)


/-- The original full-ceremony coupling follows from the segment core. -/
theorem treeSimCeremonyGoal3_of_segments
    (core : TreeTwinSegCoreGoal3 prims K circuits settings) :
    TreeSimCeremonyGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  by_cases bad : TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2
  · exact treeSimRoundStages_run prims K circuits settings (treeSimEvents3 prims K circuits settings)
      top tree D A parameter seeds pairs z Z p.1 p.2.1 p.2.2
      (treeSimCommonPrefix_hidden prims circuits settings top tree D A parameter seeds pairs z p hp)
      (treeSimRoundCore_stages3 prims K circuits settings top tree D A parameter seeds pairs z Z
        p.1 p.2.1 p.2.2
        (treeStages_badCore3 prims K circuits settings top tree D A parameter seeds pairs z p.1 p.2.1 p.2.2 bad))
  · obtain ⟨padding, hpadding⟩ := core hb top tree D A parameter seeds pairs z Z q hq hsmall p hp bad
    apply relTriple_of_evalDist_eq_left
      (treeSimRealFinish_padding prims K circuits settings top tree D A
        (dealtKeys parameter seeds pairs) Z p.2.1 p.2.2 padding).symm
    apply relTriple_of_evalDist_eq_right
      (treeSimIdealFinish_padding prims K circuits settings top tree D A parameter seeds Z p.2.1 p.1 p.2.2.1.1 padding)
    apply relTriple_bind (treeSim_relTriple_support (relTriple_refl _))
    rintro r _ ⟨rfl, hr, _⟩
    obtain ⟨Stage, entry, next⟩ := hpadding r hr
    exact treeSimFinish_of_segments prims K circuits settings top tree D A parameter seeds pairs z p r
      Z hp padding hr Stage entry next

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.relTriple_executeRounds_segments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms relTriple_executeRounds_segments

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeSimulationHop_of_ceremony' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimulationHop_of_ceremony

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeSimulationHop_of_pairs3_ceremony' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimulationHop_of_pairs3_ceremony

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.segStepAt_of_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms segStepAt_of_round

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeTwinSegStep_of_rounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeTwinSegStep_of_rounds

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeStages_reach_segment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_reach_segment

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeSimFinish_of_segments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimFinish_of_segments

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeSimCeremonyGoal3_of_segments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCeremonyGoal3_of_segments

end TreeTwinSegment
end ThresholdLeanXmssSecurity
