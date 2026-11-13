import ThresholdLeanXmssSecurity.Proof.TreeTwinDrawReplay

/-!
# Collector draws retained at their final actual cache

Generic-index collector couplings retain the answers for the same real masks
used by their boundary equations, including selectively aborted resumptions.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open ThresholdLeanXmssSecurity.TreeTwinDrawReplay
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinCollectorReplay
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

-- Port of TreeSim.treeSim_collector_draws_mixed; retains actual draw answers.
theorem collector_draws_mixed_at (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimCollectorDraws (E := E) D ctx₁ idx count st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimCollectorDraws (E := E) D ctx₂ idx count st₂)).run b)
      (fun u z => TreeSimCollectorMasksRel D δ ctx₁ idx count st₁ u.1 z.1 ∧
        (∀ i, i ∉ D.1 → DrawAnswered prims D u.2.1 (ctx₁ i) (st₁ i).label idx count (u.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2) := by
  unfold treeSimCollectorDraws
  rw [simulateQ_sequenceFin, simulateQ_sequenceFin]
  apply relTriple_post_mono (sequenceFin_rel_stable _ _ (TreeSimStreamRel δ)
    (fun i (x y : PrssOutput C Bit) (s : TreeSimState C) => i ∉ D.1 →
      (y.1 = x.1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).1 ∧
       y.2 = x.2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).2) ∧
      DrawAnswered prims D s.1 (ctx₁ i) (st₁ i).label idx count x) ?_ ?_ a b hs)
  · intro u z h
    exact ⟨fun i hi => (h.1 i hi).1, (fun i hi => (h.1 i hi).2), h.2⟩
  · intro i x y s j t h ht hi
    have grows := logged_caches_grow prims D _ s t ht
    exact ⟨(h hi).1, drawAnswered_mono prims D grows.1 grows.2 (h hi).2⟩
  · intro i s₁ s₂ hstate
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨fun h => (h hi).elim, hstate⟩
    · simp only [if_neg hi]
      rw [← treeSim_prssDraw_context (ctx₁ i) (ctx₂ i) (self i hi) (keys i hi), ← lab i hi]
      apply relTriple_post_mono (relTriple_with_left_support
        (treeSim_prssBits_mixed prims D δ hδ (ctx₁ i) (st₁ i).label idx count s₁ s₂ hstate)
        (fun u hu => drawAnswered_of_logged prims D (ctx₁ i) (st₁ i).label idx count s₁ u hu))
      intro u z h
      exact ⟨fun _ => ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, h.1.2.2⟩

-- Port of TreeSim.treeSim_collector_start_mixed; retains actual draw answers.
theorem collector_start_mixed_at {α : Type} (D : C.Coalition)
    (δ : HiddenAddress C → Bit) (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= k₂ i))).run b)
      (fun u z => (∃ rnd₁ rnd₂, TreeSimCollectorMasksRel D δ ctx₁ idx count st₁ rnd₁ rnd₂ ∧
        u.1 = treeSimCollectorWaiting K D count rnd₁ v₁ st₁ k₁ ∧
        z.1 = treeSimCollectorWaiting K D count rnd₂ v₂ st₂ k₂ ∧
        (∀ i, i ∉ D.1 → DrawAnswered prims D u.2.1 (ctx₁ i) (st₁ i).label idx count (rnd₁ i))) ∧ TreeSimStreamRel δ u.2 z.2) := by
  rw [treeSim_collector_start_factor K D ctx₁ self₁, treeSim_collector_start_factor K D ctx₂ self₂]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (collector_draws_mixed_at prims D δ hδ ctx₁ ctx₂
    (fun i hi => (self₁ i hi).trans (self₂ i hi).symm) keys idx count st₁ st₂ lab a b hs)
  intro u z h
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨⟨u.1, z.1, h.1, rfl, rfl, h.2.1⟩, h.2.2⟩

-- Port of TreeSim.treeSim_collector_start_next; retains actual draw answers.
theorem collector_start_next_at {α : Type} (D : C.Coalition)
    (T₀ : C.Term) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂) x = 0) :
    let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= k₂ i))).run b)
      (fun u z => (∃ rnd₁ rnd₂,
        (∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
          (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i) ∧
        u.1 = treeSimCollectorWaiting K D count rnd₁ v₁ st₁ k₁ ∧
        z.1 = treeSimCollectorWaiting K D count rnd₂ v₂ st₂ k₂ ∧
        (∀ i, i ∉ D.1 → DrawAnswered prims D u.2.1 (ctx₁ i) ρ idx count (rnd₁ i))) ∧ TreeSimStreamRel δ u.2 z.2) := by
  intro δ
  have hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  apply relTriple_post_mono (collector_start_mixed_at prims K D δ hδ ctx₁ ctx₂ self₁ self₂ keys
    idx count v₁ v₂ st₁ st₂ (fun i hi => (lab₁ i hi).trans (lab₂ i hi).symm) k₁ k₂ a b
    ⟨hs.1, treeSim_hiddenRel_extend past _ hs.2 fresh⟩)
  intro u z h
  obtain ⟨rnd₁, rnd₂, hm, hu, hz, answered⟩ := h.1
  refine ⟨⟨rnd₁, rnd₂, ?_, hu, hz, ?_⟩, h.2⟩
  rotate_left
  · intro i hi
    simpa only [lab₁ i hi] using answered i hi
  intro i hi
  have hshift : treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count =
      frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
        (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i := by
    rw [lab₁ i hi]
    dsimp only [δ]
    rw [treeSim_prssShift_add, treeSim_prssShift_zero past (ctx₁ i) ρ idx count block, zero_add]
    unfold treeSimCollectorShift
    rw [treeSim_prssShift_block D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
  have hm' := hm i hi
  rw [hshift] at hm'
  exact Prod.ext hm'.1 hm'.2

-- Port of TreeSim.treeSim_collector_start_boundary; retains actual draw answers.
theorem collector_start_boundary_at (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (T₀ : C.Term) (lacked : lackedTerm D.1 = some T₀) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂) x = 0) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= k₂ i))).run b)
      (fun u z => ∃ rnd₁ rnd₂, ∃ masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i +
        frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
          (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i,
        TreeSimCollectorBoundary K D A
          ⟨count, T₀, lacked, past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂),
            rnd₁, rnd₂, v₁, v₂, st₁, st₂, k₁, k₂, history, masks, states⟩
          ((state, u.1), u.2) ((state, z.1), z.2) ∧
        (∀ i, i ∉ D.1 → DrawAnswered prims D u.2.1 (ctx₁ i) ρ idx count (rnd₁ i))) := by
  apply relTriple_post_mono (collector_start_next_at prims K D T₀ ctx₁ ctx₂ self₁ self₂ keys
    ρ idx count v₁ v₂ st₁ st₂ lab₁ lab₂ k₁ k₂ past visible block a b hs fresh)
  intro u z h
  obtain ⟨⟨rnd₁, rnd₂, masks, hu, hz, answered⟩, hc⟩ := h
  exact ⟨rnd₁, rnd₂, masks, ⟨rfl, hc, Or.inl ⟨hu, hz⟩⟩, answered⟩

-- Port of TreeSim.treeSim_collector_resume_boundary using A204 stable sequence.
theorem collector_resume_boundary_at (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (T₀ : C.Term) (lacked : lackedTerm D.1 = some T₀) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (next₁ next₂ k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (x₁ x₂ : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none)
    (shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none)
    (program₁ : ∀ i, i ∉ D.1 → live i = true →
      k₁ i (x₁ i) = treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= next₁ i)
    (program₂ : ∀ i, i ∉ D.1 → live i = true →
      k₂ i (x₂ i) = treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= next₂ i)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂) x = 0) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => ∃ rnd₁ rnd₂, ∃ masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i +
        frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
          (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i,
        u.1 = treeSimCollectorPartial K D live count rnd₁ v₁ st₁ next₁ ∧
        z.1 = treeSimCollectorPartial K D live count rnd₂ v₂ st₂ next₂ ∧
        TreeSimCollectorBoundary K D A
          ⟨count, T₀, lacked, past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂),
            rnd₁, rnd₂, v₁, v₂, st₁, st₂, next₁, next₂, history, masks, states⟩
          ((state, u.1), u.2) ((state, z.1), z.2) ∧
        (∀ i, i ∉ D.1 → live i = true →
          DrawAnswered prims D u.2.1 (ctx₁ i) ρ idx count (rnd₁ i))) := by
  let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
  let dt := frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
    (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0))
  have hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  have hshift : ∀ i, i ∉ D.1 → treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count = dt i := by
    intro i hi
    rw [lab₁ i hi]
    dsimp only [δ]
    rw [treeSim_prssShift_add, treeSim_prssShift_zero past (ctx₁ i) ρ idx count block, zero_add]
    unfold treeSimCollectorShift
    rw [treeSim_prssShift_block D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
  let Q := fun i (s₁ s₂ : Step C E RealSpec TreeOutput) (cache : TreeSimState C) => ∃ r₁ r₂ : PrssOutput C Bit,
    (i ∉ D.1 → r₂ = r₁ + dt i) ∧
    s₁ = treeSimCollectorPartial K D live count (fun _ => r₁) v₁ st₁ next₁ i ∧
    s₂ = treeSimCollectorPartial K D live count (fun _ => r₂) v₂ st₂ next₂ i ∧
    (i ∉ D.1 → live i = true → DrawAnswered prims D cache.1 (ctx₁ i) ρ idx count r₁)
  have step : ∀ i a' b', TreeSimStreamRel δ a' b' →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (treeSimResume (k₁ i) (out₁ i)))).run a')
        ((simulateQ (streamWorld prims D) (free (treeSimResume (k₂ i) (out₂ i)))).run b')
        (fun u z => Q i u.1 z.1 u.2 ∧ TreeSimStreamRel δ u.2 z.2) := by
    intro i a' b' hc
    rw [shape₁ i, shape₂ i]
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨⟨0, 0, fun h => (h hi).elim, ?_, ?_, fun h => (h hi).elim⟩, hc⟩ <;>
        simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume, program₁ i hi hl, program₂ i hi hl]
        apply relTriple_post_mono (collector_entry_mixed_at prims K D δ hδ (ctx₁ i) (ctx₂ i)
          ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi) idx count (v₁ i) (v₂ i)
          (st₁ i) (st₂ i) ((lab₁ i hi).trans (lab₂ i hi).symm) (next₁ i) (next₂ i) a' b' hc)
        intro u z h
        obtain ⟨⟨r₁, r₂, ht, hp, hu, hz, answered⟩, hc'⟩ := h
        rw [hshift i hi] at ht hp
        refine ⟨⟨r₁, r₂, fun _ => Prod.ext ht hp, ?_, ?_, ?_⟩, hc'⟩
        · simpa only [treeSimCollectorPartial, hl, if_true, treeSimCollectorWaiting, if_neg hi,
            treeSimCollectorStep, self₁ i hi, localContext] using hu
        · simpa only [treeSimCollectorPartial, hl, if_true, treeSimCollectorWaiting, if_neg hi,
            treeSimCollectorStep, self₂ i hi, localContext] using hz
        · intro _ _
          simpa only [lab₁ i hi] using answered
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        apply relTriple_pure_pure
        exact ⟨⟨0, 0 + dt i, fun _ => rfl, by simp [treeSimCollectorPartial, hl],
          by simp [treeSimCollectorPartial, hl], fun _ h => (hl h).elim⟩, hc⟩
  unfold treeSimResumeAll
  rw [free_sequenceFin, free_sequenceFin, simulateQ_sequenceFin, simulateQ_sequenceFin]
  have stable : ∀ i x y s j t, Q i x y s →
      t ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (treeSimResume (k₁ j) (out₁ j)))).run s) → Q i x y t.2 := by
    intro i x y s j t h ht
    obtain ⟨r₁, r₂, hm, hu, hz, answered⟩ := h
    have grows := logged_caches_grow prims D _ s t ht
    exact ⟨r₁, r₂, hm, hu, hz, fun hi hl =>
      drawAnswered_mono prims D grows.1 grows.2 (answered hi hl)⟩
  apply relTriple_post_mono (sequenceFin_rel_stable _ _ (TreeSimStreamRel δ) Q
    stable step a b ⟨hs.1, treeSim_hiddenRel_extend past _ hs.2 fresh⟩)
  intro u z h
  choose rnd₁ rnd₂ masks hu hz answered using h.1
  have hu' : u.1 = treeSimCollectorPartial K D live count rnd₁ v₁ st₁ next₁ := funext hu
  have hz' : z.1 = treeSimCollectorPartial K D live count rnd₂ v₂ st₂ next₂ := funext hz
  refine ⟨rnd₁, rnd₂, masks, hu', hz', ⟨rfl, h.2, ?_⟩, answered⟩
  by_cases stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true
  · exact Or.inr (Or.inr ⟨live, stopped, hu', hz'⟩)
  · left
    have allLive : ∀ i, i ∉ D.1 → live i = true := by
      intro i hi
      by_contra hl
      exact stopped ⟨i, hi, hl⟩
    constructor
    · rw [hu']
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
      · simp [treeSimCollectorPartial, allLive i hi]
    · rw [hz']
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
      · simp [treeSimCollectorPartial, allLive i hi]

-- Port of TreeSim.TreeSimCollectorNext.coupling with the same mask witnesses.
theorem collectorNext_coupling_at (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (past : HiddenAddress C → Bit) (initial : HiddenCache C) (k₁ k₂) (out₁ out₂)
    (n : TreeSimCollectorNext K D past initial k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (ha : a.1.2 = initial) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeSimCacheFrame n.ρ a.1.2 u.2.1.2 ∧ TreeSimCacheFrame n.ρ b.2 z.2.2 ∧
        TreeSimFutureEmpty (n.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (n.ρ + 1) z.2.2 ∧
        TreeSimFutureZero (n.ρ + 1)
          (past + treeSimCollectorShift K D n.T₀ n.ρ n.idx n.count (n.v₁ - n.v₂)) ∧
        ∃ rnd₁ rnd₂, ∃ masks : n.Masks K rnd₁ rnd₂,
        u.1 = treeSimCollectorPartial K D n.live n.count rnd₁ n.v₁ n.st₁ n.next₁ ∧
        z.1 = treeSimCollectorPartial K D n.live n.count rnd₂ n.v₂ n.st₂ n.next₂ ∧
        TreeSimCollectorBoundary K D A (n.data K rnd₁ rnd₂ masks)
          ((state, u.1), u.2) ((state, z.1), z.2) ∧
        (∀ i, i ∉ D.1 → n.live i = true →
          DrawAnswered prims D u.2.1 (n.ctx₁ i) n.ρ n.idx n.count (rnd₁ i))) := by
  apply relTriple_post_mono (treeSim_relTriple_support (collector_resume_boundary_at prims K D A state n.T₀ n.lacked n.ctx₁ n.ctx₂
    n.self₁ n.self₂ n.keys n.ρ n.idx n.count n.v₁ n.v₂ n.st₁ n.st₂ n.lab₁ n.lab₂
    n.next₁ n.next₂ k₁ k₂ out₁ out₂ n.x₁ n.x₂ n.live n.shape₁ n.shape₂ n.program₁ n.program₂
    n.history n.states past n.visible (n.block K) a b hs (by simpa only [ha] using n.fresh K)))
  intro u z h
  have f₁ := treeSim_collector_resume_logged_frame prims K D n.ctx₁ n.ρ n.idx n.count n.v₁ n.st₁
    k₁ n.next₁ out₁ n.x₁ n.live (fun i hi _ => n.lab₁ i hi) n.shape₁ n.program₁ a u h.2.1
  have f₂ := treeSim_collector_resume_frame prims K D n.ctx₂ n.ρ n.idx n.count n.v₂ n.st₂
    k₂ n.next₂ out₂ n.x₂ n.live (fun i hi _ => n.lab₂ i hi) n.shape₂ n.program₂ b z h.2.2
  have he : TreeSimFutureEmpty n.ρ a.1.2 := by simpa only [ha] using n.futureEmpty
  refine ⟨f₁, f₂, treeSim_futureEmpty_after he f₁,
    treeSim_futureEmpty_after (treeSim_futureEmpty_related he hs.2) f₂, ?_, h.1⟩
  exact treeSim_futureZero_extend D n.ρ n.idx n.count _ _ past n.futureZero

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorReplay.collector_draws_mixed_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collector_draws_mixed_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorReplay.collector_start_mixed_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collector_start_mixed_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorReplay.collector_start_next_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collector_start_next_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorReplay.collector_start_boundary_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collector_start_boundary_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorReplay.collector_resume_boundary_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collector_resume_boundary_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorReplay.collectorNext_coupling_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collectorNext_coupling_at

end ThresholdLeanXmssSecurity.TreeTwinCollectorReplay
