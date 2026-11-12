import ThresholdLeanXmssSecurity.Proof.TreeTwinNext

/-!
# The stages of the twins after the collector layers

`TreeTwinNext.lean` reduces `TreeTwinStageCoreGoal3` to `TreeTwinOtherGoal`. This file shows that
the stage must also carry the saved shares of each run, restates the goal with them, and proves
the reduction and the digest swap step.

## The stage must carry the saved shares

`TreeTwinOtherGoal` is not false, because `Allowed := fun _ => False` turns it back into
`TreeTwinStageCoreGoal3`. But with an `Allowed` that holds the actual code, the collector stage of
`TreeTwinNext.lean` cannot be used. This is a deduction from the frozen definitions.

* `Allowed` reads only `TreeTwinCode`. The code has no saved shares `p₁` and `p₂`.
* `TreeStagesCollectorSchedule`, `TreeStagesCollectorTail` and `TreeStagesRerandTail` relate
  `p₁` and `p₂` in no field. So `TreeTwinRerandEntry` holds for any two share lists.
* `TreeTwinOtherRerand` puts every such entry into `Other`, and `TreeTwinOtherNext` must then hold
  at it. Its reach premise reads only the real side.
* The check and the final opening read the tuples of `p₁` and `p₂`.
  `treeStages_finalMask_simBatch_finish` needs the Shamir, residual and internal share equations
  between the two runs. With an ideal tuple list that has a nonzero residual, an honest ideal
  operator rejects the check while the real one accepts, so no coupling has equal adversary states.

`TreeTwinRunData` carries the saved-share invariant. It is the GS20 translation that the collector exits
produce (`TreeSimCollectorResultRel`, `treeTwin_schedule_next`).

* Each saved sharing of the ideal run is the real one with a shift at the held `T₀` only
  (`TreeSimHistoryRel`). The shift is common to all honest operators.
* Each saved tuple has the same count and mode. Its `x` and `y` have a common held shift, and its
  `z` has the shift of the honest local products, as `treeSim_collector_transcript_exit` gives it.
  This shift makes the residual `z - x y` equal in the two runs.

## The restated goal

* `TreeTwinDataCollectorStage` and `TreeTwinDataRerandEntry` are the stages of `TreeTwinNext.lean`
  with `TreeTwinRunData` added. `treeTwinDataStage` is the stage relation with them.
* `TreeTwinScheduleData` and `TreeTwinTailData` are `treeTwin_schedule_round` and
  `treeTwin_tail_round` with the invariant kept. The frozen lemmas hide the successor shares, so
  these two are named `Prop`s. Their proof copies `treeTwin_schedule_next` and
  `treeTwin_tail_next` with one more conjunct. It must also show that `layerX` and `layerY` keep
  the held shift, also at gate indices past the count.
* `treeTwin_dataCollector_round` proves the field `next` at the data collector stage from them.
* `Other` is a list of round kinds. `TreeTwinKindNext Kind` is the field `next` at one kind. The
  additional kinds are the peer reshare, Rerand, Coin, ExtendMult, the check, the digest round,
  both openings, the output and the batch transitions.
* `TreeTwinDataGoal` asks for `Allowed` and the kinds with the field `entry`, the data Rerand entry
  and `TreeTwinKindNext` at each kind. `treeTwinStageCoreGoal3_of_data` gives
  `TreeTwinStageCoreGoal3` from it and the two data rounds.

## The digest swap

`treeTwin_hiddenDigest_twin` is `treeStages_hiddenDigest_fresh` in the twin form of `next`. It
starts at the twin state and ends in `TreeSimBad3` or in the stream relation of the twin with one
more swap. Two points fix the form of the digest round of a later kind.

* Live honest holders of `T₀` may hold different real histories at `T₀` if the adversary chooses
  some of their messages. If such distinct histories occur, each distinct history needs its own swap
  with the same salt, and the round adds a list of swaps without repeats. A repeated swap undoes
  itself in `treeStagesSwapAll`.
* `treeStages_hiddenDigest_fresh` needs the hash of the ideal history in the real cache (`inner'`),
  and fresh digest addresses. The real run never hashes the ideal history, so the padding or the
  stage must supply this entry.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The GS20 translation of the saved shares of the two runs. The saved sharings differ by a
common shift at the held `T₀`. The saved tuples differ by common shifts at `T₀`, and the shift of
`z` is the sum of the honest local product differences. -/
def TreeTwinRunData (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)) : Prop :=
  (∀ i, i ∉ D.1 → (p₂ i).1.length = (p₁ i).1.length ∧ (p₂ i).2.length = (p₁ i).2.length) ∧
  (∀ k : ℕ, ∃ difference : List Bit, ∀ i, i ∉ D.1 → ∀ w₁ w₂, (p₁ i).1[k]? = some w₁ →
    (p₂ i).1[k]? = some w₂ → TreeSimHistoryRel D i difference w₁ w₂) ∧
  (∀ k : ℕ, ∃ dx dy : ℕ → Bit, ∀ i, i ∉ D.1 → ∀ t₁ t₂ : Tuple C, (p₁ i).2[k]? = some t₁ →
    (p₂ i).2[k]? = some t₂ →
    t₂.count = t₁.count ∧ t₂.mode = t₁.mode ∧
    t₂.x = treeSimHeldShift D i t₁.count dx t₁.x ∧ t₂.y = treeSimHeldShift D i t₁.count dy t₁.y ∧
    t₂.z = treeSimHeldShift D i t₁.count (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1),
      (((p₁ j).2[k]?.map fun t : Tuple C => mulRep K (ctx₁ j) t.x t.y g).getD 0 -
        ((p₂ j).2[k]?.map fun t : Tuple C => mulRep K (ctx₂ j) t.x t.y g).getD 0)) t₁.z)

section Stages

variable {A : Adversary C E (Keys C) PEmpty PEmpty}

/-- `TreeTwinCollectorStage` with the saved shares in `TreeTwinRunData`. -/
def TreeTwinDataCollectorStage (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop)
    (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ d : TreeSimCollectorData K D, ∃ s : TreeStagesCollectorSchedule K D d,
    Allowed (treeTwinScheduleCode K D s) ∧ δ = d.δ ∧ TreeSimFutureEmpty (s.ρ + 1) a.2.1.2 ∧
    TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂ ∧
    ((∃ live, a.1.2 = treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        b.1.2 = treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) ∨
      ∃ sent, a.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent ∧
        b.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)

/-- `TreeTwinRerandEntry` with the saved shares in `TreeTwinRunData`. -/
def TreeTwinDataRerandEntry (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop)
    (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next) (live : C.Party → Bool),
    Allowed (treeTwinRerandCode K D rest) ∧ δ = next.δ ∧ TreeSimFutureEmpty (rest.ρ + 1) a.2.1.2 ∧
    TreeSimFutureEmpty (rest.ρ + 1) b.2.2 ∧ TreeSimFutureZero (rest.ρ + 1) next.δ ∧
    TreeTwinRunData K D next.ctx₁ next.ctx₂ rest.p₁ rest.p₂ ∧
    a.1.2 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
    b.1.2 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂

/-- The stage relation: the done stage, the data collector stage, or one of the round kinds. -/
def treeTwinDataStage (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)) :
    ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop :=
  fun _ δ a b => TreeTwinDoneStage a b ∨ TreeTwinDataCollectorStage K D Allowed δ a b ∨
    ∃ Kind ∈ kinds, Kind δ a b

end Stages

/-- `treeTwin_schedule_round` with the saved shares kept in `TreeTwinRunData`. -/
def TreeTwinScheduleData : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (s : TreeStagesCollectorSchedule K D d)
    (nextLayer : ℕ) (remaining : List ℕ), s.rest = nextLayer :: remaining →
    ∀ (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C),
    TreeSimStreamRel d.δ a b → TreeSimFutureEmpty (s.ρ + 1) a.1.2 →
    TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂ →
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimCollectorData K D) (successor : TreeStagesCollectorSchedule K D next)
          (live : C.Party → Bool),
          successor.ρ = s.ρ + 1 ∧ successor.circs = s.circs ∧ successor.layer = nextLayer ∧
          successor.rest = remaining ∧
          treeTwinScheduleCode K D successor = treeTwinScheduleCode K D s ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (successor.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (successor.ρ + 1) z.2.2 ∧
          TreeTwinRunData K D successor.ctx₁ successor.ctx₂ successor.p₁ successor.p₂ ∧
          u.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₂ next.v₂ next.st₂ next.k₂)

/-- `treeTwin_tail_round` with the saved shares kept in `TreeTwinRunData`. -/
def TreeTwinTailData : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C),
    TreeSimStreamRel d.δ a b → TreeSimFutureEmpty (tail.ρ + 1) a.1.2 →
    TreeTwinRunData K D tail.ctx₁ tail.ctx₂ tail.p₁ tail.p₂ →
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next) (live : C.Party → Bool),
          rest.ρ = tail.ρ + 1 ∧ rest.circs = tail.circs ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (rest.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (rest.ρ + 1) z.2.2 ∧
          TreeSimFutureZero (rest.ρ + 1) next.δ ∧
          TreeTwinRunData K D next.ctx₁ next.ctx₂ rest.p₁ rest.p₂ ∧
          u.1.2.1 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂ ∧
          treeTwinRerandCode K D rest = treeTwinTailCode K D tail)

/-- One round from the data collector stage. It is `treeTwin_collector_round` with the saved
shares. The first exchange keeps the schedule, and the forwarding exchange uses the two data
rounds. -/
theorem treeTwin_dataCollector_round (scheduleData : TreeTwinScheduleData prims K)
    (tailData : TreeTwinTailData prims K) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Allowed : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (rerand : ∀ δ a b, TreeTwinDataRerandEntry K D Allowed δ a b → ∃ Kind ∈ kinds, Kind δ a b)
    (n : ℕ) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (state : a.1.1 = b.1.1) (related : TreeSimStreamRel δ a.2 b.2)
    (stage : TreeTwinDataCollectorStage K D Allowed δ a b) :
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => ∃ δ', treeTwinReq D (treeTwinDataStage K D Allowed kinds) n δ'
      ((v.1.1, v.1.2.1), v.2) ((w.1.1, w.1.2.1), w.2)) := by
  obtain ⟨d, s, allowed, rfl, fresh, data, ⟨live, h₁, h₂⟩ | ⟨sent, h₁, h₂⟩⟩ := stage
  · have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).1
    simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    rw [h₁, h₂, ← state]
    by_cases stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true
    · apply relTriple_post_mono (treeSim_collector_partial_mixed prims K D A a.1.1 live stopped d.δ
        d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a.2 b.2 related)
      rintro u z ⟨hs, -, hu, hz, hc, -, -⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i _ => Or.inl
        ⟨congrFun hu i, congrFun hz i⟩)
      exact ⟨d.δ, hc, hs, done, flags, Or.inl ⟨hu, hz⟩⟩
    · have all : ∀ j, j ∉ D.1 → live j = true := fun j hj => by
        by_contra h
        exact stopped ⟨j, hj, h⟩
      rw [treeTwin_collectorPartial_live K D live all, treeTwin_collectorPartial_live K D live all]
      apply relTriple_post_mono (treeSim_collector_first_mixed prims K D A a.1.1 d.δ
        d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a.2 b.2 related)
      rintro u z ⟨hs, -, hu, hz, hc, hl, -⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_collectorAfterFirst K D _ _ _ _ _ _ _ _ _ _ i hi)
      refine ⟨d.δ, hc, hs, done, flags,
        Or.inr (Or.inl ⟨d, s, allowed, rfl, ?_, data, Or.inr ⟨u.1.2.2, hu, hz⟩⟩)⟩
      change TreeSimFutureEmpty (s.ρ + 1) u.2.1.2
      rw [hl]
      exact fresh
  · rw [h₁, h₂, ← state]
    cases hrest : s.rest with
    | cons nextLayer remaining =>
      apply relTriple_post_mono (scheduleData D A a.1.1 d s nextLayer remaining hrest sent a.2 b.2
        related fresh data)
      rintro u z ⟨hs, -, next, successor, live, -, -, -, -, code, hc, f₁, -, data', hu, hz⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_collectorPartial K D _ _ _ _ _ _ _ _ _ _ i hi)
      exact ⟨next.δ, hc, hs, done, flags,
        Or.inr (Or.inl ⟨next, successor, code ▸ allowed, rfl, f₁, data', Or.inl ⟨live, hu, hz⟩⟩)⟩
    | nil =>
      apply relTriple_post_mono (tailData D A a.1.1 d (s.last K D d hrest) sent a.2 b.2 related
        fresh data)
      rintro u z ⟨hs, -, next, rest, live, -, -, hc, f₁, f₂, zero, data', hu, hz, code⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_peerPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
      exact ⟨next.δ, hc, hs, done, flags,
        Or.inr (Or.inr (rerand _ _ _ ⟨next, rest, live, code ▸ allowed, rfl, f₁, f₂, zero, data', hu, hz⟩))⟩

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Allowed : TreeTwinCode C E → Prop)
  (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop))

/-- The data Rerand entry after the last collector layer is a stage of one of the kinds. -/
def TreeTwinDataRerand : Prop :=
  ∀ δ (a : TreeSimConfig A (TreeSimState C)) b, TreeTwinDataRerandEntry K D Allowed δ a b →
    ∃ Kind ∈ kinds, Kind δ a b

/-- The field `next` of `TreeTwinNext3` at the stages of one round kind `Kind`. -/
def TreeTwinKindNext (Kind : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop) : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    treeTwinReq D (treeTwinDataStage K D Allowed kinds) n δ (a.1, treeStagesTwin swaps a.2) b →
    Kind δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
    ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
    treeTwinReq D (treeTwinDataStage K D Allowed kinds) (n + 1) δ'
      ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2))

/-- The field `next` of `treeTwinDataStage`. The done stage has no round, the data collector
stage uses `treeTwin_dataCollector_round` with no swap, and each kind uses its own field. -/
theorem treeTwinNext3_of_data (scheduleData : TreeTwinScheduleData prims K)
    (tailData : TreeTwinTailData prims K)
    (rerand : TreeTwinDataRerand K D A Allowed kinds)
    (next : ∀ Kind ∈ kinds, TreeTwinKindNext prims K circuits settings top tree D A parameter seeds
      pairs z p r Allowed kinds Kind) :
    TreeTwinNext3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D (treeTwinDataStage K D Allowed kinds)) := by
  intro n δ swaps a b reach bound good active salts req
  obtain ⟨related, state, _, _, stage⟩ := req
  rcases stage with done | collector | ⟨Kind, mem, rest⟩
  · exact (active fun i _ => by rw [done.1]; trivial).elim
  · apply relTriple_post_mono (treeTwin_dataCollector_round prims K scheduleData tailData D A Allowed
      kinds rerand (n + 1) δ (a.1, treeStagesTwin swaps a.2) b state related collector)
    rintro v w ⟨δ', req'⟩
    exact Or.inr ⟨[], δ', fun x hx => by simp at hx, req'⟩
  · exact next Kind mem n δ swaps a b reach bound good active salts
      ⟨related, state, ‹_›, ‹_›, Or.inr (Or.inr ⟨Kind, mem, rest⟩)⟩ rest

end Fields

/-- `TreeTwinOtherGoal` with the saved shares. It asks for `Allowed` and the round kinds with the
field `entry`, the data Rerand entry and the field `next` at each kind. -/
def TreeTwinDataGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ (Allowed : TreeTwinCode C E → Prop)
      (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
        TreeSimConfig A (HashCache C × HiddenCache C) → Prop)),
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D (treeTwinDataStage K D Allowed kinds)) ∧
    TreeTwinDataRerand K D A Allowed kinds ∧
    ∀ Kind ∈ kinds, TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r
      Allowed kinds Kind

/-- `TreeTwinStageCoreGoal3` from the two data rounds and `TreeTwinDataGoal`. -/
theorem treeTwinStageCoreGoal3_of_data (scheduleData : TreeTwinScheduleData prims K)
    (tailData : TreeTwinTailData prims K) (goal : TreeTwinDataGoal prims K circuits settings) :
    TreeTwinStageCoreGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := goal hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Allowed, kinds, entry, rerand, next⟩ := hpadding r hr
  exact ⟨treeTwinDataStage K D Allowed kinds, entry,
    treeTwinNext3_of_data prims K circuits settings top tree D A parameter seeds pairs z p r Allowed
      kinds scheduleData tailData rerand next⟩

/-- `TreeSimStagesGoal3` from the lockstep goals, the two data rounds and `TreeTwinDataGoal`. -/
theorem treeSimStagesGoal3_of_data
    (lockstep : TreeLockstepStagesGoal circuits prims K settings)
    (draws : TreeTwinDigestDrawsGoal circuits prims K settings)
    (scheduleData : TreeTwinScheduleData prims K) (tailData : TreeTwinTailData prims K)
    (goal : TreeTwinDataGoal prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStagesGoal3_of_lockstep prims K circuits settings lockstep draws
    (treeTwinStageCoreGoal3_of_data prims K circuits settings scheduleData tailData goal)

/-- A salt guess is a `TreeSimBad3` event. -/
theorem treeSimBad3_of_saltGuess (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) (log : TreeSimLog C)
    (guess : TreeSimSaltGuess D log) :
    TreeSimBad3 prims K circuits settings top tree D A x z log :=
  Or.inl (Or.inl (Or.inl (Or.inr guess)))

/-- The digest transport is the stream relation of the twin with one swap. -/
theorem treeTwin_digestRel_iff (salt : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) :
    TreeStagesDigestRel salt h h' δ a b ↔ TreeSimStreamRel δ (treeStagesTwin [(salt, h, h')] a) b := by
  simp only [TreeStagesDigestRel, TreeSimStreamRel, treeStagesTwin, treeStagesSwapAll, List.foldr_cons,
    List.foldr_nil]
  exact ⟨fun hr => ⟨hr.1.symm, hr.2⟩, fun hr => ⟨hr.1.symm, hr.2⟩⟩

/-- `treeStages_hiddenDigest_fresh` in the twin form of the field `next`. The real side starts at
any state, for example the twin state of earlier swaps. It ends in `TreeSimBad3`, or with equal
results and the stream relation of the twin with the swap `(salt, h, h')`. -/
theorem treeTwin_hiddenDigest_twin {α : Type} (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (salt history history' : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (k : HashOutput → OracleComp (LocalSpec C) α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (inner : a.1.1 (.history history) = some h)
    (inner' : a.1.1 (.history history') = some h')
    (fresh : a.1.1 (.digest salt h) = none) (fresh' : a.1.1 (.digest salt h') = none)
    (hidden : TreeSimHiddenSalt D a.2 salt) (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)) >>= fun d =>
          worldRoles.adversary (k d))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history') (LocalSpec C)) >>= fun d =>
          worldRoles.adversary (k d))).run b)
      (fun u w => TreeSimBad3 prims K circuits settings top tree D A x z u.2.2 ∨
        (u.1 = w.1 ∧ TreeSimStreamRel δ (treeStagesTwin [(salt, h, h')] u.2) w.2 ∧
          u.2.1.2 = a.1.2 ∧ w.2.2 = b.2)) := by
  apply relTriple_post_mono (treeStages_hiddenDigest_fresh prims D salt history history' h h' δ k a b
    inner inner' fresh fresh' hidden related)
  rintro u w (guess | ⟨same, digest, private₁, private₂⟩)
  · exact Or.inl (treeSimBad3_of_saltGuess prims K circuits settings top tree D A x z u.2.2 guess)
  · exact Or.inr ⟨same, (treeTwin_digestRel_iff salt h h' δ u.2 w.2).1 digest, private₁, private₂⟩

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_dataCollector_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_dataCollector_round

/-- info: 'ThresholdLeanXmssSecurity.treeTwinStageCoreGoal3_of_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinStageCoreGoal3_of_data

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_data

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_hiddenDigest_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_hiddenDigest_twin

end ThresholdLeanXmssSecurity
