import ThresholdLeanXmssSecurity.Proof.TreeTwinBatchReplay
import ThresholdLeanXmssSecurity.Proof.TreeTwinCollectorReplay

/-!
# Round transitions retaining their recorded values

The collector and peer rounds retain both recorded exits, the next states and
saved shares, and coherence of the same next real masks at the final actual cache.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinRoundReplay
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

-- Port of TreeTwinKinds.treeTwin_scheduleLinked_next; retains the original witnesses.
theorem scheduleLinked_next_at (D : C.Coalition) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (nextLayer : ℕ) (remaining : List ℕ)
    (rest_eq : s.rest = nextLayer :: remaining) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (s.ρ + 1) initial) (sent sent' : C.Party → Mail C E)
    (data : TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂) (link : TreeTwinScheduleLink K D s) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeSimCollectorNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = s.ρ + 1 ∧ n.idx = 0 ∧ n.count = (gatesAt s.circs nextLayer).length ∧
      n.ctx₁ = s.ctx₁ ∧ n.ctx₂ = s.ctx₂ ∧
      n.st₁ = (fun i => (n.x₁ i).2) ∧ n.st₂ = (fun i => (n.x₂ i).2) ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesCollectorSchedule K D (n.data K rnd₁ rnd₂ masks),
          successor.ρ = n.ρ ∧ successor.circs = s.circs ∧ successor.layer = nextLayer ∧
          successor.rest = remaining ∧
          treeTwinScheduleCode K D successor = treeTwinScheduleCode K D s ∧
          TreeTwinRunData K D successor.ctx₁ successor.ctx₂ successor.p₁ successor.p₂ ∧
          TreeTwinScheduleLink K D successor ∧
          successor.p₁ = (fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₁ i).mode (s.p₁ i) (n.x₁ i).1) ∧
          successor.p₂ = (fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₂ i).mode (s.p₂ i) (n.x₂ i).1) := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  let nextP₁ := fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₁ i).mode (s.p₁ i) (x₁ i).1
  let nextP₂ := fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₂ i).mode (s.p₂ i) (x₂ i).1
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
  }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
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
    }, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · intro x hx
      change (d.δ + treeSimCollectorShift K D d.T₀ (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _) x = 0
      simp only [Pi.add_apply, s.visible x hx, treeSimCollectorShift,
        treeSim_blockShift_visible D (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _ _ x hx, add_zero]
    · exact treeTwinRunData_exit K D d s.ctx₁ s.ctx₂ s.gadgets₁ s.gadgets₂ s.circs s.layer s.p₁ s.p₂
        data link x₁ x₂ fun i hi => (exits i hi).1.1
    · obtain ⟨_, _, _, modes, wires, tuples⟩ := link
      refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, modes, fun i j hi hj => ?_, fun i j hi hj => ?_⟩
      · simpa [nextP₁, treeTwinLayerShares, treeTwin_appendLayer_length] using wires i j hi hj
      · simpa [nextP₁, treeTwinLayerShares] using tuples i j hi hj

-- Port of TreeTwinKinds.treeTwin_tailLinked_next; retains the original witnesses.
theorem tailLinked_next_at (D : C.Coalition) (d : TreeSimCollectorData K D)
    (tail : TreeStagesCollectorTail K D d) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (tail.ρ + 1) initial) (sent sent' : C.Party → Mail C E)
    (data : TreeTwinRunData K D tail.ctx₁ tail.ctx₂ tail.p₁ tail.p₂) (link : TreeTwinTailLink K D tail) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeStagesPeerNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = tail.ρ + 1 ∧ n.count = (outputsOf tail.circs).length ∧
      n.ctx₁ = tail.ctx₁ ∧ n.ctx₂ = tail.ctx₂ ∧
      n.st₁ = (fun i => (n.x₁ i).2) ∧ n.st₂ = (fun i => (n.x₂ i).2) ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        ∃ rest : TreeStagesRerandTail K D (n.data K rnd₁ rnd₂ masks), rest.ρ = n.ρ ∧ rest.circs = tail.circs ∧
          treeTwinRerandCode K D rest = treeTwinTailCode K D tail ∧
          TreeTwinRunData K D (n.data K rnd₁ rnd₂ masks).ctx₁ (n.data K rnd₁ rnd₂ masks).ctx₂ rest.p₁ rest.p₂ ∧
          TreeTwinRerandLink K D rest ∧
          rest.p₁ = (fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₁ i).mode (tail.p₁ i) (n.x₁ i).1) ∧
          rest.p₂ = (fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₂ i).mode (tail.p₂ i) (n.x₂ i).1) := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let nextP₁ := fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₁ i).mode (tail.p₁ i) (x₁ i).1
  let nextP₂ := fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₂ i).mode (tail.p₂ i) (x₂ i).1
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
  }, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
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
      tail.keys, tail.verify₁, tail.verify₂, ?_⟩, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · intro x hx
      simp only [TreeStagesPeerNext.data, TreeStagesPeerNext.δ, Pi.add_apply, tail.visible x hx,
        treeSimPeerShift, treeSim_blockShift_visible D (tail.ρ + 1) 0 _ _ _ x hx, add_zero]
    · exact treeTwinRunData_exit K D d tail.ctx₁ tail.ctx₂ tail.gadgets₁ tail.gadgets₂ tail.circs tail.layer
        tail.p₁ tail.p₂ data link x₁ x₂ fun i hi => (exits i hi).1.1
    · obtain ⟨_, _, _, modes, wires, tuples⟩ := link
      refine ⟨fun _ _ => rfl, fun _ _ => rfl, modes, fun i j hi hj => ?_, fun i j hi hj => ?_⟩
      · simpa [nextP₁, treeTwinLayerShares, treeTwin_appendLayer_length] using wires i j hi hj
      · simpa [nextP₁, treeTwinLayerShares] using tuples i j hi hj

-- Port of TreeSimStages.TreeStagesPeerSchedule.next; retains the original witnesses.
theorem peerSchedule_next_at (D : C.Coalition) (d : TreeSimPeerData K D)
    (layer : ℕ) (rest : List ℕ) (s : TreeStagesPeerSchedule K D d (layer :: rest))
    (initial : HiddenCache C) (fresh : TreeSimFutureEmpty (s.ρ + 1) initial)
    (sent : C.Party → Mail C E) :
    let out₁ := treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent
    let out₂ := treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent
    ∃ n : TreeStagesPeerNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = s.ρ + 1 ∧
      n.ctx₁ = d.ctx₁ ∧ n.ctx₂ = d.ctx₂ ∧
      n.st₁ = (fun i => (n.x₁ i).2) ∧ n.st₂ = (fun i => (n.x₂ i).2) ∧
      n.count = treeStagesPeerLayerCount s.circs rest ∧
      (∀ i, i ∉ D.1 → TreeSimPeerExitRel K D d i (n.x₁ i) (n.x₂ i)) ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesPeerSchedule K D (n.data K rnd₁ rnd₂ masks) rest,
          successor.ρ = n.ρ ∧ successor.circs = s.circs ∧
          successor.p₁ = (fun i => treeTwinLayerShares K s.circs layer (s.gadgets₁ i).mode (s.p₁ i) (n.x₁ i).1) ∧
          successor.p₂ = (fun i => treeTwinLayerShares K s.circs layer (s.gadgets₂ i).mode (s.p₂ i) (n.x₂ i).1) := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_peer_exit_values K D d sent
  let nextP₁ := fun i => (appendLayer s.circs layer (s.p₁ i).1 (x₁ i).1,
    (s.p₁ i).2 ++ [⟨layerX K s.circs layer (s.p₁ i).1, layerY K s.circs layer (s.p₁ i).1,
      (x₁ i).1, (gatesAt s.circs layer).length, (s.gadgets₁ i).mode⟩])
  let nextP₂ := fun i => (appendLayer s.circs layer (s.p₂ i).1 (x₂ i).1,
    (s.p₂ i).2 ++ [⟨layerX K s.circs layer (s.p₂ i).1, layerY K s.circs layer (s.p₂ i).1,
      (x₂ i).1, (gatesAt s.circs layer).length, (s.gadgets₂ i).mode⟩])
  refine ⟨{
    T₀ := d.T₀, pivotParty := d.pivotParty, pivot := d.pivot
    ctx₁ := d.ctx₁, ctx₂ := d.ctx₂, self₁ := d.self₁, self₂ := d.self₂, keys := s.keys
    ρ := s.ρ + 1, count := treeStagesPeerLayerCount s.circs rest
    v₁ := fun i => treeStagesPeerLayerValue K (d.ctx₁ i) s.circs rest (nextP₁ i)
    v₂ := fun i => treeStagesPeerLayerValue K (d.ctx₂ i) s.circs rest (nextP₂ i)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.2.1.trans (congrArg (· + 1) (s.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (s.labels i hi)))
    next₁ := fun i => treeStagesPeerLayerCont K (s.gadgets₁ i) s.circs rest (nextP₁ i) (s.finish₁ i)
    next₂ := fun i => treeStagesPeerLayerCont K (s.gadgets₂ i) s.circs rest (nextP₂ i) (s.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppend K d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).2.1
    visible := s.visible, futureZero := s.zero, futureEmpty := fresh
  }, rfl, rfl, rfl, rfl, rfl, rfl, exits, ?_⟩
  · intro i hi _
    rw [s.program₁ i hi]
    exact treeStages_layers_peer K (d.ctx₁ i) (s.gadgets₁ i) (s.mult₁ i hi) (s.rerand₁ i hi)
      s.circs rest (nextP₁ i) (x₁ i).2 (s.finish₁ i)
  · intro i hi _
    rw [s.program₂ i hi]
    exact treeStages_layers_peer K (d.ctx₂ i) (s.gadgets₂ i) (s.mult₂ i hi) (s.rerand₂ i hi)
      s.circs rest (nextP₂ i) (x₂ i).2 (s.finish₂ i)
  · intro rnd₁ rnd₂ masks zeroNext
    refine ⟨{
      gadgets₁ := s.gadgets₁, gadgets₂ := s.gadgets₂, mult₁ := s.mult₁, mult₂ := s.mult₂
      rerand₁ := s.rerand₁, rerand₂ := s.rerand₂, verify₁ := s.verify₁, verify₂ := s.verify₂, keys := s.keys
      circs := s.circs, count := rfl, p₁ := nextP₁, p₂ := nextP₂, finish₁ := s.finish₁, finish₂ := s.finish₂
      program₁ := by intros; rfl
      program₂ := by intros; rfl
      checked₁ := by
        intro i hi
        have h := s.checked₁ i hi
        simpa only [nextP₁, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using h
      checked₂ := by
        intro i hi
        have h := s.checked₂ i hi
        simpa only [nextP₂, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using h
      ρ := s.ρ + 1
      labels := fun i hi => (exits i hi).2.2.1.trans (congrArg (· + 1) (s.labels i hi))
      visible := ?_, zero := zeroNext
    }, rfl, rfl, rfl, rfl⟩
    intro x hx
    change (d.δ + treeSimPeerShift K D d.T₀ d.pivotParty (s.ρ + 1) 0 (treeStagesPeerLayerCount s.circs rest) _ 0) x = 0
    simp only [Pi.add_apply, s.visible x hx, treeSimPeerShift,
      treeSim_blockShift_visible D (s.ρ + 1) 0 (treeStagesPeerLayerCount s.circs rest) _ _ x hx, add_zero]

-- Port of TreeTwinKinds.treeTwin_scheduleLinked_round; retains the original witnesses.
theorem scheduleLinked_round_at (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (s : TreeStagesCollectorSchedule K D d)
    (nextLayer : ℕ) (remaining : List ℕ) (rest_eq : s.rest = nextLayer :: remaining)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2)
    (data : TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂) (link : TreeTwinScheduleLink K D s) :
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
          TreeTwinScheduleLink K D successor ∧
          u.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₂ next.v₂ next.st₂ next.k₂ ∧
          ∃ (sent' : C.Party → Mail C E) (x₁ x₂ : C.Party → Shares C Bit × RunState C),
            (∀ i, i ∉ D.1 → live i = true →
              treeSimCollectorRecorded K d.count d.st₁ i
                (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i) = some (x₁ i) ∧
              treeSimCollectorRecorded K d.count d.st₂ i
                (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i) = some (x₂ i)) ∧
            next.st₁ = (fun i => (x₁ i).2) ∧ next.st₂ = (fun i => (x₂ i).2) ∧
            successor.p₁ = (fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₁ i).mode (s.p₁ i) (x₁ i).1) ∧
            successor.p₂ = (fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₂ i).mode (s.p₂ i) (x₂ i).1) ∧
            TreeTwinHolderKeys.DrawCoherent prims D (fun i => live i = true)
              u.2.1 s.ctx₁ (s.ρ + 1) next.count next.rnd₁) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, index, _, ctx₁, ctx₂, st₁, st₂, after⟩ := scheduleLinked_next_at K D d s nextLayer remaining rest_eq a.1.2 fresh sent u.1.2 data link
  rw [← h.1]
  apply relTriple_bind (TreeTwinCollectorReplay.collectorNext_coupling_at prims K D A u.1.1 d.δ a.1.2 d.k₁ d.k₂ _ _ n u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨_, _, empty₁, empty₂, zero, rnd₁, rnd₂, masks, steps₁, steps₂, boundary, answered⟩ := h'
  obtain ⟨successor, nextLabel, circs, layer, rest, code, runData, link, p₁, p₂⟩ := after rnd₁ rnd₂ masks zero
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, successor, n.live, nextLabel.trans label,
    circs, layer, rest, code, boundary.2.1, ?_, ?_, runData, link, steps₁, steps₂,
    u.1.2, n.x₁, n.x₂, ?_, st₁, st₂, p₁, p₂, ?_⟩
  · simpa only [nextLabel] using empty₁
  · simpa only [nextLabel] using empty₂
  · intro i hi hl
    exact ⟨by simpa only [if_neg hi, hl, if_true] using n.shape₁ i,
      by simpa only [if_neg hi, hl, if_true] using n.shape₂ i⟩
  · have coherent := TreeTwinDrawReplay.drawCoherent_of_answered prims D
      (fun i => n.live i = true) u'.2.1 n.ctx₁ n.ρ n.count rnd₁
      (fun i hi _ => n.self₁ i hi) (by simpa only [index] using answered)
    simpa only [TreeSimCollectorNext.data, ctx₁, label] using coherent

-- Port of TreeTwinKinds.treeTwin_tailLinked_round; retains the original witnesses.
theorem tailLinked_round_at (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2)
    (data : TreeTwinRunData K D tail.ctx₁ tail.ctx₂ tail.p₁ tail.p₂) (link : TreeTwinTailLink K D tail) :
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
          TreeTwinRunData K D next.ctx₁ next.ctx₂ rest.p₁ rest.p₂ ∧ TreeTwinRerandLink K D rest ∧
          u.1.2.1 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂ ∧
          treeTwinRerandCode K D rest = treeTwinTailCode K D tail ∧
          ∃ (sent' : C.Party → Mail C E) (x₁ x₂ : C.Party → Shares C Bit × RunState C),
            (∀ i, i ∉ D.1 → live i = true →
              treeSimCollectorRecorded K d.count d.st₁ i
                (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i) = some (x₁ i) ∧
              treeSimCollectorRecorded K d.count d.st₂ i
                (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i) = some (x₂ i)) ∧
            next.st₁ = (fun i => (x₁ i).2) ∧ next.st₂ = (fun i => (x₂ i).2) ∧
            rest.p₁ = (fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₁ i).mode (tail.p₁ i) (x₁ i).1) ∧
            rest.p₂ = (fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₂ i).mode (tail.p₂ i) (x₂ i).1) ∧
            next.ctx₁ = tail.ctx₁ ∧ next.ctx₂ = tail.ctx₂ ∧
            TreeTwinHolderKeys.DrawCoherent prims D (fun i => live i = true)
              u.2.1 tail.ctx₁ (tail.ρ + 1) next.count next.rnd₁) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, _, ctx₁, ctx₂, st₁, st₂, after⟩ := tailLinked_next_at K D d tail a.1.2 fresh sent u.1.2 data link
  rw [← h.1]
  apply relTriple_bind (TreeTwinBatchReplay.peerNext_coupling_at prims K D d.δ a.1.2 d.k₁ d.k₂ _ _ n u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨caches, empty₁, empty₂, zero, rnd₁, rnd₂, masks, next₁, next₂, coherent⟩ := h'
  obtain ⟨rest, restLabel, restCircs, restCode, restData, restLink, p₁, p₂⟩ := after rnd₁ rnd₂ masks
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, rest, n.live, restLabel.trans label,
    restCircs, caches, ?_, ?_, ?_, restData, restLink, next₁, next₂, restCode,
    u.1.2, n.x₁, n.x₂, ?_, st₁, st₂, p₁, p₂, ctx₁, ctx₂, ?_⟩
  · simpa only [restLabel] using empty₁
  · simpa only [restLabel] using empty₂
  · simpa only [restLabel, TreeStagesPeerNext.data] using zero
  · intro i hi hl
    exact ⟨by simpa only [if_neg hi, hl, if_true] using n.shape₁ i,
      by simpa only [if_neg hi, hl, if_true] using n.shape₂ i⟩
  · simpa only [TreeStagesPeerNext.data, ctx₁, label] using coherent

-- Port of TreeSimStages.TreeStagesPeerSchedule.round; retains the original witnesses.
theorem peerSchedule_round_at (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (d : TreeSimPeerData K D)
    (layer : ℕ) (rest : List ℕ) (s : TreeStagesPeerSchedule K D d (layer :: rest))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimPeerData K D) (successor : TreeStagesPeerSchedule K D next rest)
          (live : C.Party → Bool),
          successor.ρ = s.ρ + 1 ∧ successor.circs = s.circs ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (successor.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (successor.ρ + 1) z.2.2 ∧
          u.1.2.1 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂ ∧
          ∃ (sent : C.Party → Mail C E) (x₁ x₂ : C.Party → Shares C Bit × RunState C),
            (∀ i, i ∉ D.1 → live i = true →
              treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i = some (x₁ i) ∧
              treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i = some (x₂ i)) ∧
            (∀ i, i ∉ D.1 → TreeSimPeerExitRel K D d i (x₁ i) (x₂ i)) ∧
            next.st₁ = (fun i => (x₁ i).2) ∧ next.st₂ = (fun i => (x₂ i).2) ∧
            successor.p₁ = (fun i => treeTwinLayerShares K s.circs layer (s.gadgets₁ i).mode (s.p₁ i) (x₁ i).1) ∧
            successor.p₂ = (fun i => treeTwinLayerShares K s.circs layer (s.gadgets₂ i).mode (s.p₂ i) (x₂ i).1) ∧
            next.ctx₁ = d.ctx₁ ∧ next.ctx₂ = d.ctx₂ ∧
            next.count = treeStagesPeerLayerCount s.circs rest ∧
            TreeTwinHolderKeys.DrawCoherent prims D (fun i => live i = true)
              u.2.1 d.ctx₁ (s.ρ + 1) next.count next.rnd₁) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_peer_resume_factor, treeSim_peer_resume_factor, d.view K D]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, ctx₁, ctx₂, st₁, st₂, count, exits, after⟩ := peerSchedule_next_at K D d layer rest s a.1.2 fresh u.1.2
  rw [← h.1]
  apply relTriple_bind (TreeTwinBatchReplay.peerNext_coupling_at prims K D d.δ a.1.2 d.k₁ d.k₂ _ _ n u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨caches, empty₁, empty₂, zeroNext, rnd₁, rnd₂, masks, steps₁, steps₂, coherent⟩ := h'
  obtain ⟨successor, nextLabel, circs, p₁, p₂⟩ := after rnd₁ rnd₂ masks zeroNext
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, successor, n.live,
    nextLabel.trans label, circs, caches, ?_, ?_, steps₁, steps₂,
    u.1.2, n.x₁, n.x₂, ?_, exits, st₁, st₂, p₁, p₂, ctx₁, ctx₂, count, ?_⟩
  · simpa only [nextLabel] using empty₁
  · simpa only [nextLabel] using empty₂
  · intro i hi hl
    exact ⟨by simpa only [if_neg hi, hl, if_true] using n.shape₁ i,
      by simpa only [if_neg hi, hl, if_true] using n.shape₂ i⟩
  · simpa only [TreeStagesPeerNext.data, ctx₁, label] using coherent

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinRoundReplay.scheduleLinked_next_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scheduleLinked_next_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinRoundReplay.tailLinked_next_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tailLinked_next_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinRoundReplay.peerSchedule_next_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms peerSchedule_next_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinRoundReplay.scheduleLinked_round_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scheduleLinked_round_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinRoundReplay.tailLinked_round_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tailLinked_round_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinRoundReplay.peerSchedule_round_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms peerSchedule_round_at

end ThresholdLeanXmssSecurity.TreeTwinRoundReplay
