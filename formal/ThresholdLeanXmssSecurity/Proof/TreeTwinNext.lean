import ThresholdLeanXmssSecurity.Proof.TreeTwin3

/-!
# The stage relation of the twins

`TreeTwin3.lean` reduces `TreeSimStagesGoal3` to `TreeTwinStageCoreGoal3`. That goal asks for a
stage relation `Stage` with the fields `entry` and `next`. This file builds the part of `Stage`
covered by the equal-cache transitions, with other kinds as parameters.

* `treeTwinStage Allowed Other` is the stage relation. It is the disjunction of three stages.
  * `TreeTwinDoneStage` holds when every operator stopped with no output on both sides.
  * `TreeTwinCollectorStage` holds at a collector layer of the saved schedule
    `TreeStagesCollectorSchedule`, at its first exchange (`treeSimCollectorPartial`) or at its
    forwarding exchange (`treeSimCollectorAfterFirst`). The code of the schedule satisfies
    `Allowed`.
  * `Other` is the stage relation of all other round kinds.
* `Allowed` fixes the code of a schedule: the contexts, the gadgets, the circuits and the suffix
  after the layers. Without it the ideal suffix of a collector stage is free, and no `Other` can
  hold every Rerand entry with a free ideal suffix.
* `treeTwin_schedule_next`, `treeTwin_schedule_round`, `treeTwin_tail_next` and
  `treeTwin_tail_round` are copies of the `TreeSimStages.lean` lemmas
  `TreeStagesCollectorSchedule.next` and `.round` and `TreeStagesCollectorTail.next` and `.round`.
  Their results also state that the successor keeps the code.
* `treeTwin_collector_round` proves the field `next` at the collector stage. It uses
  `treeSim_collector_partial_mixed`, `treeSim_collector_first_mixed` and the two copied rounds.
  These lemmas need no reach premise, and their freshness premise reads only the private cache,
  which the twin keeps. So they apply to the twin state, and the swap list of the result is empty.
* The abort tests on `colInbox` agree on the real and the ideal side, because an honest operator
  sends no abort frame (`treeTwin_anyAbort_colInbox`).
* After the last collector layer, the round goes to the peer Rerand entry `TreeTwinRerandEntry`.
  The named `Prop` `TreeTwinOtherRerand` puts this entry into `Other`.
* `TreeTwinOtherGoal` asks for `Allowed` and `Other` with the field `entry`, the Rerand entry, and
  the field `next` at the stages of `Other` (`TreeTwinOtherNext`).
  `treeTwinStageCoreGoal3_of_other` gives `TreeTwinStageCoreGoal3` from it.
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

/-- Two steps of an honest operator have the same kind: both stopped with no output, or both
wait for an exchange. -/
def TreeTwinSameKind {α : Type} (x y : Step C E RealSpec α) : Prop :=
  (x = .done none ∧ y = .done none) ∨ (∃ o₁ k₁ o₂ k₂, x = .wait o₁ k₁ ∧ y = .wait o₂ k₂)

/-- Steps of the same kind have the same stop flags and the same output flags. -/
theorem treeTwin_flags_of_sameKind {α : Type} (D : C.Coalition) (s₁ s₂ : C.Party → Step C E RealSpec α)
    (same : ∀ i, i ∉ D.1 → TreeTwinSameKind (s₁ i) (s₂ i)) :
    (AllDone D s₁ ↔ AllDone D s₂) ∧ (∀ i, i ∉ D.1 → (s₁ i).output.isSome = (s₂ i).output.isSome) := by
  refine ⟨⟨fun h i hi => ?_, fun h i hi => ?_⟩, fun i hi => ?_⟩
  · rcases same i hi with ⟨_, e⟩ | ⟨_, _, _, _, e₁, _⟩
    · rw [e]; trivial
    · have := h i hi; rw [e₁] at this; exact this.elim
  · rcases same i hi with ⟨e, _⟩ | ⟨_, _, _, _, _, e₂⟩
    · rw [e]; trivial
    · have := h i hi; rw [e₂] at this; exact this.elim
  · rcases same i hi with ⟨e₁, e₂⟩ | ⟨_, _, _, _, e₁, e₂⟩
    · rw [e₁, e₂]
    · rw [e₁, e₂]; rfl

/-- An honest operator sends no abort frame in the first collector exchange. So the abort test
reads only the corrupt messages. -/
theorem treeTwin_anyAbort_colInbox (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (sent : C.Party → Mail C E)
    (i : C.Party) :
    anyAbort (colInbox K D count rnd v sent i) = C.parties.any fun j => j ∈ D.1 ∧ Msg.isAbort (sent j i) := by
  unfold anyAbort colInbox
  congr 1
  funext j
  by_cases hj : j ∈ D.1
  · simp [hj]
  · simp only [hj, if_false, false_and, decide_false, colOut1]
    split_ifs <;> rfl

theorem treeTwin_sameKind_collectorPartial {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (count : ℕ) (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) (i : C.Party) (hi : i ∉ D.1) :
    TreeTwinSameKind (treeSimCollectorPartial K D live count rnd₁ v₁ st₁ k₁ i)
      (treeSimCollectorPartial K D live count rnd₂ v₂ st₂ k₂ i) := by
  by_cases hl : live i = true
  · exact Or.inr ⟨_, _, _, _, by
      simp only [treeSimCollectorPartial, hl, if_true, treeSimCollectorWaiting, hi, if_false,
        treeSimCollectorStep]; rfl, by
      simp only [treeSimCollectorPartial, hl, if_true, treeSimCollectorWaiting, hi, if_false,
        treeSimCollectorStep]; rfl⟩
  · exact Or.inl ⟨by simp [treeSimCollectorPartial, hl], by simp [treeSimCollectorPartial, hl]⟩

theorem treeTwin_sameKind_collectorAfterFirst {α : Type} (D : C.Coalition)
    (count : ℕ) (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) (sent : C.Party → Mail C E)
    (i : C.Party) (hi : i ∉ D.1) :
    TreeTwinSameKind (treeSimCollectorAfterFirst K D count rnd₁ v₁ st₁ k₁ sent i)
      (treeSimCollectorAfterFirst K D count rnd₂ v₂ st₂ k₂ sent i) := by
  have e := (treeTwin_anyAbort_colInbox K D count rnd₁ v₁ sent i).trans
    (treeTwin_anyAbort_colInbox K D count rnd₂ v₂ sent i).symm
  by_cases ha : anyAbort (colInbox K D count rnd₁ v₁ sent i) = true
  · have hb : anyAbort (colInbox K D count rnd₂ v₂ sent i) = true := e ▸ ha
    exact Or.inl ⟨by simp [treeSimCollectorAfterFirst, ha], by simp [treeSimCollectorAfterFirst, hb]⟩
  · have hb : ¬ anyAbort (colInbox K D count rnd₂ v₂ sent i) = true := e ▸ ha
    exact Or.inr ⟨_, _, _, _, (if_neg (by simp [hi, ha]) : _ = _),
      (if_neg (by simp [hi, hb]) : _ = _)⟩

theorem treeTwin_sameKind_peerPartial {α : Type} (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (live : C.Party → Bool) (count : ℕ) (rnd₁ rnd₂ : C.Party → PrssOutput C Bit)
    (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) (i : C.Party) (hi : i ∉ D.1) :
    TreeTwinSameKind (treeSimPeerPartial K D ctx₁ live count rnd₁ v₁ st₁ k₁ i)
      (treeSimPeerPartial K D ctx₂ live count rnd₂ v₂ st₂ k₂ i) := by
  by_cases hl : live i = true
  · exact Or.inr ⟨_, _, _, _, by
      simp only [treeSimPeerPartial, hl, if_true, treeSimPeerWaiting, hi, if_false, treeSimPeerStep]; rfl, by
      simp only [treeSimPeerPartial, hl, if_true, treeSimPeerWaiting, hi, if_false, treeSimPeerStep]; rfl⟩
  · exact Or.inl ⟨by simp [treeSimPeerPartial, hl], by simp [treeSimPeerPartial, hl]⟩

/-- A partial collector entry with every honest operator live is the full entry. -/
theorem treeTwin_collectorPartial_live {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (all : ∀ j, j ∉ D.1 → live j = true) (count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    treeSimCollectorPartial K D live count rnd v st k = treeSimCollectorWaiting K D count rnd v st k := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
  · simp [treeSimCollectorPartial, all i hi]


/-- The code of a collector layer: the contexts, the gadgets, the circuits and the suffix after
the layers, on the real and the ideal side. -/
abbrev TreeTwinCode (C : Committee) (E : Type) [Field E] [Algebra Bit E] : Type :=
  (C.Party → Context C) × (C.Party → Context C) ×
    (C.Party → RunGadgets C E RealSpec) × (C.Party → RunGadgets C E RealSpec) × List Circuit ×
    (C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) ×
    (C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)

/-- The code of a layer schedule. -/
def treeTwinScheduleCode (D : C.Coalition) {d : TreeSimCollectorData K D}
    (s : TreeStagesCollectorSchedule K D d) : TreeTwinCode C E :=
  (s.ctx₁, s.ctx₂, s.gadgets₁, s.gadgets₂, s.circs, s.finish₁, s.finish₂)

/-- The code of the last collector layer. -/
def treeTwinTailCode (D : C.Coalition) {d : TreeSimCollectorData K D}
    (tail : TreeStagesCollectorTail K D d) : TreeTwinCode C E :=
  (tail.ctx₁, tail.ctx₂, tail.gadgets₁, tail.gadgets₂, tail.circs, tail.finish₁, tail.finish₂)

/-- The code of a Rerand recipe. -/
def treeTwinRerandCode (D : C.Coalition) {d : TreeSimPeerData K D}
    (rest : TreeStagesRerandTail K D d) : TreeTwinCode C E :=
  (d.ctx₁, d.ctx₂, rest.gadgets₁, rest.gadgets₂, rest.circs, rest.finish₁, rest.finish₂)

/-- `TreeStagesCollectorSchedule.next` of `TreeSimStages.lean`, copied. The result also states
that the successor keeps the code of the schedule. -/
theorem treeTwin_schedule_next (D : C.Coalition) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (nextLayer : ℕ) (remaining : List ℕ)
    (rest_eq : s.rest = nextLayer :: remaining) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (s.ρ + 1) initial) (sent sent' : C.Party → Mail C E) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeSimCollectorNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = s.ρ + 1 ∧ n.idx = 0 ∧ n.count = (gatesAt s.circs nextLayer).length ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesCollectorSchedule K D (n.data K rnd₁ rnd₂ masks),
          successor.ρ = n.ρ ∧ successor.circs = s.circs ∧ successor.layer = nextLayer ∧
          successor.rest = remaining ∧
          treeTwinScheduleCode K D successor = treeTwinScheduleCode K D s := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  let nextP₁ := fun i => (appendLayer s.circs s.layer (s.p₁ i).1 (x₁ i).1,
    (s.p₁ i).2 ++ [⟨layerX K s.circs s.layer (s.p₁ i).1, layerY K s.circs s.layer (s.p₁ i).1,
      (x₁ i).1, (gatesAt s.circs s.layer).length, (s.gadgets₁ i).mode⟩])
  let nextP₂ := fun i => (appendLayer s.circs s.layer (s.p₂ i).1 (x₂ i).1,
    (s.p₂ i).2 ++ [⟨layerX K s.circs s.layer (s.p₂ i).1, layerY K s.circs s.layer (s.p₂ i).1,
      (x₂ i).1, (gatesAt s.circs s.layer).length, (s.gadgets₂ i).mode⟩])
  refine ⟨{
    T₀ := d.T₀, lacked := d.lacked, ctx₁ := s.ctx₁, ctx₂ := s.ctx₂
    self₁ := s.self₁, self₂ := s.self₂, keys := s.keys
    ρ := s.ρ + 1, idx := 0, count := (gatesAt s.circs nextLayer).length
    v₁ := fun i => mulRep K (s.ctx₁ i) (layerX K s.circs nextLayer (nextP₁ i).1) (layerY K s.circs nextLayer (nextP₁ i).1)
    v₂ := fun i => mulRep K (s.ctx₂ i) (layerX K s.circs nextLayer (nextP₂ i).1) (layerY K s.circs nextLayer (nextP₂ i).1)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (s.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (s.labels i hi)))
    next₁ := fun i => treeStagesAfterLayer K (s.gadgets₁ i) s.circs nextLayer remaining (nextP₁ i) (s.finish₁ i)
    next₂ := fun i => treeStagesAfterLayer K (s.gadgets₂ i) s.circs nextLayer remaining (nextP₂ i) (s.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppendMode K .collector d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).1.2
    visible := s.visible, futureZero := s.zero, futureEmpty := fresh
  }, rfl, rfl, rfl, ?_⟩
  · intro i hi _
    rw [s.program₁ i hi, rest_eq]
    exact treeStages_layers_collector K (s.ctx₁ i) (s.gadgets₁ i) (s.mult₁ i hi)
      s.circs nextLayer remaining (nextP₁ i) (x₁ i).2 (s.finish₁ i)
  · intro i hi _
    rw [s.program₂ i hi, rest_eq]
    exact treeStages_layers_collector K (s.ctx₂ i) (s.gadgets₂ i) (s.mult₂ i hi)
      s.circs nextLayer remaining (nextP₂ i) (x₂ i).2 (s.finish₂ i)

  · intro rnd₁ rnd₂ masks zeroNext
    refine ⟨{
      ctx₁ := s.ctx₁, ctx₂ := s.ctx₂, self₁ := s.self₁, self₂ := s.self₂, keys := s.keys
      gadgets₁ := s.gadgets₁, gadgets₂ := s.gadgets₂, mult₁ := s.mult₁, mult₂ := s.mult₂
      circs := s.circs, layer := nextLayer, rest := remaining
      p₁ := nextP₁, p₂ := nextP₂, finish₁ := s.finish₁, finish₂ := s.finish₂
      program₁ := by intros; rfl
      program₂ := by intros; rfl
      ρ := s.ρ + 1
      labels := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (s.labels i hi))
      visible := ?_, zero := zeroNext
      rerand₁ := s.rerand₁, rerand₂ := s.rerand₂, verify₁ := s.verify₁, verify₂ := s.verify₂
    }, rfl, rfl, rfl, rfl, rfl⟩
    intro x hx
    change (d.δ + treeSimCollectorShift K D d.T₀ (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _) x = 0
    simp only [Pi.add_apply, s.visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _ _ x hx, add_zero]

/-- `TreeStagesCollectorSchedule.round` of `TreeSimStages.lean`, copied. The result also states
that the successor keeps the code of the schedule. -/
theorem treeTwin_schedule_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (s : TreeStagesCollectorSchedule K D d)
    (nextLayer : ℕ) (remaining : List ℕ) (rest_eq : s.rest = nextLayer :: remaining)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2) :
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
          u.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₂ next.v₂ next.st₂ next.k₂) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, _, _, after⟩ := treeTwin_schedule_next K D d s nextLayer remaining rest_eq a.1.2 fresh sent u.1.2
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D A u.1.1 d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨_, _, empty₁, empty₂, zero, rnd₁, rnd₂, masks, steps₁, steps₂, boundary⟩ := h'
  obtain ⟨successor, nextLabel, info⟩ := after rnd₁ rnd₂ masks zero
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, successor, n.live, nextLabel.trans label,
    info.1, info.2.1, info.2.2.1, info.2.2.2, boundary.2.1, ?_, ?_, steps₁, steps₂⟩
  · simpa only [nextLabel] using empty₁
  · simpa only [nextLabel] using empty₂

/-- `TreeStagesCollectorTail.next` of `TreeSimStages.lean`, copied. The result also states that
the Rerand recipe keeps the code of the tail. -/
theorem treeTwin_tail_next (D : C.Coalition) (d : TreeSimCollectorData K D)
    (tail : TreeStagesCollectorTail K D d) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (tail.ρ + 1) initial) (sent sent' : C.Party → Mail C E) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeStagesPeerNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = tail.ρ + 1 ∧ n.count = (outputsOf tail.circs).length ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        ∃ rest : TreeStagesRerandTail K D (n.data K rnd₁ rnd₂ masks), rest.ρ = n.ρ ∧ rest.circs = tail.circs ∧
          treeTwinRerandCode K D rest = treeTwinTailCode K D tail := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let nextP₁ := fun i => (appendLayer tail.circs tail.layer (tail.p₁ i).1 (x₁ i).1,
    (tail.p₁ i).2 ++ [⟨layerX K tail.circs tail.layer (tail.p₁ i).1, layerY K tail.circs tail.layer (tail.p₁ i).1,
      (x₁ i).1, (gatesAt tail.circs tail.layer).length, (tail.gadgets₁ i).mode⟩])
  let nextP₂ := fun i => (appendLayer tail.circs tail.layer (tail.p₂ i).1 (x₂ i).1,
    (tail.p₂ i).2 ++ [⟨layerX K tail.circs tail.layer (tail.p₂ i).1, layerY K tail.circs tail.layer (tail.p₂ i).1,
      (x₂ i).1, (gatesAt tail.circs tail.layer).length, (tail.gadgets₂ i).mode⟩])
  refine ⟨{
    T₀ := T₀, pivotParty := pivotParty, pivot := pivot
    ctx₁ := tail.ctx₁, ctx₂ := tail.ctx₂, self₁ := tail.self₁, self₂ := tail.self₂, keys := tail.keys
    ρ := tail.ρ + 1, count := (outputsOf tail.circs).length
    v₁ := fun i => ownerSum K (tail.ctx₁ i) (outputShares K tail.circs (nextP₁ i).1)
    v₂ := fun i => ownerSum K (tail.ctx₂ i) (outputShares K tail.circs (nextP₂ i).1)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (tail.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (tail.labels i hi)))
    next₁ := fun i => treeStagesAfterRerand K (tail.gadgets₁ i) tail.circs (nextP₁ i) (tail.finish₁ i)
    next₂ := fun i => treeStagesAfterRerand K (tail.gadgets₂ i) tail.circs (nextP₂ i) (tail.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppendMode K .collector d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).1.2
    visible := tail.visible, futureZero := tail.zero, futureEmpty := fresh
  }, rfl, rfl, ?_⟩
  · intro i hi _
    rw [tail.program₁ i hi]
    exact treeStages_layers_rerand K (tail.ctx₁ i) (tail.gadgets₁ i) (tail.rerand₁ i hi)
      tail.circs (nextP₁ i) (x₁ i).2 (tail.finish₁ i)
  · intro i hi _
    rw [tail.program₂ i hi]
    exact treeStages_layers_rerand K (tail.ctx₂ i) (tail.gadgets₂ i) (tail.rerand₂ i hi)
      tail.circs (nextP₂ i) (x₂ i).2 (tail.finish₂ i)
  · intro rnd₁ rnd₂ masks
    refine ⟨⟨tail.gadgets₁, tail.gadgets₂, tail.circs, rfl, nextP₁, nextP₂, tail.finish₁, tail.finish₂,
      (by intros; rfl), (by intros; rfl), tail.ρ + 1,
      (fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (tail.labels i hi))),
      tail.keys, tail.verify₁, tail.verify₂, ?_⟩, rfl, rfl, rfl⟩
    intro x hx
    simp only [TreeStagesPeerNext.data, TreeStagesPeerNext.δ, Pi.add_apply, tail.visible x hx,
      treeSimPeerShift, treeSim_blockShift_visible D (tail.ρ + 1) 0 _ _ _ x hx, add_zero]

/-- `TreeStagesCollectorTail.round` of `TreeSimStages.lean`, copied. The result also states that
the Rerand recipe keeps the code of the tail. -/
theorem treeTwin_tail_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
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
          u.1.2.1 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂ ∧
          treeTwinRerandCode K D rest = treeTwinTailCode K D tail) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, _, after⟩ := treeTwin_tail_next K D d tail a.1.2 fresh sent u.1.2
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨caches, empty₁, empty₂, zero, rnd₁, rnd₂, masks, next₁, next₂⟩ := h'
  obtain ⟨rest, restLabel, restCircs, restCode⟩ := after rnd₁ rnd₂ masks
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, rest, n.live, restLabel.trans label, restCircs, caches, ?_, ?_, ?_, next₁, next₂, restCode⟩
  · simpa only [restLabel] using empty₁
  · simpa only [restLabel] using empty₂
  · simpa only [restLabel, TreeStagesPeerNext.data] using zero

section Stages

variable {A : Adversary C E (Keys C) PEmpty PEmpty}

/-- Every operator stopped with no output, on both sides. -/
def TreeTwinDoneStage (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  a.1.2 = (fun _ => .done none) ∧ b.1.2 = (fun _ => .done none)

/-- A collector layer of the saved schedule, at its first exchange or at its forwarding exchange.
The future labels of the private cache are empty. -/
def TreeTwinCollectorStage (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ d : TreeSimCollectorData K D, ∃ s : TreeStagesCollectorSchedule K D d,
    Allowed (treeTwinScheduleCode K D s) ∧ δ = d.δ ∧ TreeSimFutureEmpty (s.ρ + 1) a.2.1.2 ∧
    ((∃ live, a.1.2 = treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        b.1.2 = treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) ∨
      ∃ sent, a.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent ∧
        b.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)

/-- The peer Rerand entry after the last collector layer, as `TreeStagesCollectorTail.round`
gives it. -/
def TreeTwinRerandEntry (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next) (live : C.Party → Bool),
    Allowed (treeTwinRerandCode K D rest) ∧ δ = next.δ ∧ TreeSimFutureEmpty (rest.ρ + 1) a.2.1.2 ∧ TreeSimFutureEmpty (rest.ρ + 1) b.2.2 ∧
    TreeSimFutureZero (rest.ρ + 1) next.δ ∧
    a.1.2 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
    b.1.2 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂

/-- The stage relation: the done stage, the collector stage, or a stage `Other` of the other
round kinds. It does not read the round index. -/
def treeTwinStage (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop)
    (Other : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop) :
    ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop :=
  fun _ δ a b => TreeTwinDoneStage a b ∨ TreeTwinCollectorStage K D Allowed δ a b ∨ Other δ a b

end Stages

/-- One round from the collector stage, on any real state. The result is again a stage of
`treeTwinStage Other`, with equal adversary states, equal flags and the stream relation. After the
last layer it is the Rerand entry, which `rerand` puts into `Other`. -/
theorem treeTwin_collector_round (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Allowed : TreeTwinCode C E → Prop) (Other : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (rerand : ∀ δ a b, TreeTwinRerandEntry K D Allowed δ a b → Other δ a b)
    (n : ℕ) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (state : a.1.1 = b.1.1) (related : TreeSimStreamRel δ a.2 b.2)
    (stage : TreeTwinCollectorStage K D Allowed δ a b) :
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => ∃ δ', treeTwinReq D (treeTwinStage K D Allowed Other) n δ'
      ((v.1.1, v.1.2.1), v.2) ((w.1.1, w.1.2.1), w.2)) := by
  obtain ⟨d, s, allowed, rfl, fresh, ⟨live, h₁, h₂⟩ | ⟨sent, h₁, h₂⟩⟩ := stage
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
      refine ⟨d.δ, hc, hs, done, flags, Or.inr (Or.inl ⟨d, s, allowed, rfl, ?_, Or.inr ⟨u.1.2.2, hu, hz⟩⟩)⟩
      change TreeSimFutureEmpty (s.ρ + 1) u.2.1.2
      rw [hl]
      exact fresh
  · rw [h₁, h₂, ← state]
    cases hrest : s.rest with
    | cons nextLayer remaining =>
      apply relTriple_post_mono (treeTwin_schedule_round prims K D A a.1.1 d s nextLayer
        remaining hrest sent a.2 b.2 related fresh)
      rintro u z ⟨hs, -, next, successor, live, -, -, -, -, code, hc, f₁, -, hu, hz⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_collectorPartial K D _ _ _ _ _ _ _ _ _ _ i hi)
      exact ⟨next.δ, hc, hs, done, flags,
        Or.inr (Or.inl ⟨next, successor, code ▸ allowed, rfl, f₁, Or.inl ⟨live, hu, hz⟩⟩)⟩
    | nil =>
      apply relTriple_post_mono (treeTwin_tail_round prims K D A a.1.1 d
        (s.last K D d hrest) sent a.2 b.2 related fresh)
      rintro u z ⟨hs, -, next, rest, live, -, -, hc, f₁, f₂, zero, hu, hz, code⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_peerPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
      exact ⟨next.δ, hc, hs, done, flags,
        Or.inr (Or.inr (rerand _ _ _ ⟨next, rest, live, code ▸ allowed, rfl, f₁, f₂, zero, hu, hz⟩))⟩

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Allowed : TreeTwinCode C E → Prop)
  (Other : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop)

/-- The Rerand entry after the last collector layer is a stage of `Other`. -/
def TreeTwinOtherRerand : Prop :=
  ∀ δ (a : TreeSimConfig A (TreeSimState C)) b, TreeTwinRerandEntry K D Allowed δ a b → Other δ a b

/-- The field `next` of `TreeTwinNext3` at the stages of `Other`. -/
def TreeTwinOtherNext : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    treeTwinReq D (treeTwinStage K D Allowed Other) n δ (a.1, treeStagesTwin swaps a.2) b →
    Other δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
    ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
    treeTwinReq D (treeTwinStage K D Allowed Other) (n + 1) δ'
      ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2))

/-- The field `next` of `treeTwinStage Other`. The done stage has no round, the collector stage
uses `treeTwin_collector_round` with no swap, and `Other` uses `TreeTwinOtherNext`. -/
theorem treeTwinNext3_of_other
    (rerand : TreeTwinOtherRerand K D A Allowed Other)
    (other : TreeTwinOtherNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed Other) :
    TreeTwinNext3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D (treeTwinStage K D Allowed Other)) := by
  intro n δ swaps a b reach bound good active salts req
  obtain ⟨related, state, _, _, stage⟩ := req
  rcases stage with done | collector | rest
  · exact (active fun i _ => by rw [done.1]; trivial).elim
  · apply relTriple_post_mono (treeTwin_collector_round prims K D A Allowed Other rerand (n + 1) δ
      (a.1, treeStagesTwin swaps a.2) b state related collector)
    rintro v w ⟨δ', req'⟩
    exact Or.inr ⟨[], δ', fun x hx => by simp at hx, req'⟩
  · exact other n δ swaps a b reach bound good active salts
      ⟨related, state, ‹_›, ‹_›, Or.inr (Or.inr rest)⟩ rest

end Fields

/-- `TreeTwinStageCoreGoal3` with the stage relation `treeTwinStage Other`. It asks for `Other`
with the field `entry`, the Rerand entry and the field `next` at the stages of `Other`. -/
def TreeTwinOtherGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ (Allowed : TreeTwinCode C E → Prop) (Other : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop),
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D (treeTwinStage K D Allowed Other)) ∧
    TreeTwinOtherRerand K D A Allowed Other ∧
    TreeTwinOtherNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed Other

/-- The target of this file. -/
theorem treeTwinStageCoreGoal3_of_other (goal : TreeTwinOtherGoal prims K circuits settings) :
    TreeTwinStageCoreGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := goal hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Allowed, Other, entry, rerand, other⟩ := hpadding r hr
  exact ⟨treeTwinStage K D Allowed Other, entry,
    treeTwinNext3_of_other prims K circuits settings top tree D A parameter seeds pairs z p r Allowed
      Other rerand other⟩

/-- `TreeSimStagesGoal3` from the lockstep goals and `TreeTwinOtherGoal`. -/
theorem treeSimStagesGoal3_of_other
    (lockstep : TreeLockstepStagesGoal circuits prims K settings)
    (draws : TreeTwinDigestDrawsGoal circuits prims K settings)
    (goal : TreeTwinOtherGoal prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStagesGoal3_of_lockstep prims K circuits settings lockstep draws
    (treeTwinStageCoreGoal3_of_other prims K circuits settings goal)

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_collector_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_collector_round

/-- info: 'ThresholdLeanXmssSecurity.treeTwinStageCoreGoal3_of_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinStageCoreGoal3_of_other

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_other

end ThresholdLeanXmssSecurity
