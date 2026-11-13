import ThresholdLeanXmssSecurity.Proof.TreeTwinHolderKeys
import ThresholdLeanXmssSecurity.Proof.TreeTwinLaterKinds

/-!
# Stream answers retained by the actual peer and collector draws

The coupling retains the real PRSS masks together with their answers in the
final real cache. Sequential resumptions preserve those answers as the shared
cache grows. Digest relabeling preserves the stream-key entries.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinDrawReplay
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem logged_caches_grow {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    s.1.1 ≤ r.2.1.1 ∧ s.1.2 ≤ r.2.1.2 := by
  rw [treeSimLoggedWorld_run, support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  have h := treeLockstep_logged_streams prims D p s.1 u.1.1 u.1.2 u.2 hu
  exact ⟨h.1, h.2.1⟩

def DrawAnswered (prims : Primitives) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C) (ctx : Context C)
    (label idx count : ℕ) (rnd : PrssOutput C Bit) : Prop :=
  ∀ T, ctx.self ∈ C.holders T → ∀ g < count,
    TreeLockstepStreamAnswer prims D cache (.term T, ctx.prss.term T, label, idx, g) (rnd.1 T g)

theorem drawCoherent_of_answered (prims : Primitives) (D : C.Coalition)
    (live : C.Party → Prop) (cache : HashCache C × HiddenCache C)
    (ctx : C.Party → Context C) (label count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (self : ∀ i, i ∉ D.1 → live i → (ctx i).self = i)
    (h : ∀ i, i ∉ D.1 → live i → DrawAnswered prims D cache (ctx i) label 0 count (rnd i)) :
    TreeTwinHolderKeys.DrawCoherent prims D live cache ctx label count rnd := by
  intro i hi li T held g hg
  exact h i hi li T (by rw [self i hi li]; exact held) g hg

theorem drawAnswered_mono (prims : Primitives) (D : C.Coalition)
    {cache cache' : HashCache C × HiddenCache C} (hash : cache.1 ≤ cache'.1)
    (hidden : cache.2 ≤ cache'.2) {ctx : Context C} {label idx count : ℕ} {rnd : PrssOutput C Bit}
    (h : DrawAnswered prims D cache ctx label idx count rnd) :
    DrawAnswered prims D cache' ctx label idx count rnd := by
  intro T held g hg
  exact treeLockstep_streamAnswer_mono prims D hash hidden (h T held g hg)

theorem drawCoherent_mono (prims : Primitives) (D : C.Coalition)
    {cache cache' : HashCache C × HiddenCache C} (hash : cache.1 ≤ cache'.1)
    (hidden : cache.2 ≤ cache'.2) {live : C.Party → Prop} {ctx : C.Party → Context C}
    {label count : ℕ} {rnd : C.Party → PrssOutput C Bit}
    (h : TreeTwinHolderKeys.DrawCoherent prims D live cache ctx label count rnd) :
    TreeTwinHolderKeys.DrawCoherent prims D live cache' ctx label count rnd := by
  intro i hi li T held g hg
  exact treeLockstep_streamAnswer_mono prims D hash hidden (h i hi li T held g hg)

theorem streamAnswer_swapAll (prims : Primitives) (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (cache : HashCache C × HiddenCache C)
    (x : PrgInput C) (u : Bit) :
    TreeLockstepStreamAnswer prims D (treeStagesSwapAll swaps cache.1, cache.2) x u ↔
      TreeLockstepStreamAnswer prims D cache x u := by
  simp only [TreeLockstepStreamAnswer]
  rw [treeTwin_swapAll_read swaps cache.1 (.streamKey x.2.1)
    (fun y _ => digestSwap_streamKey y.1 y.2.1 y.2.2 x.2.1)]

theorem drawAnswered_swapAll (prims : Primitives) (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (cache : HashCache C × HiddenCache C)
    (ctx : Context C) (label idx count : ℕ) (rnd : PrssOutput C Bit) :
    DrawAnswered prims D (treeStagesSwapAll swaps cache.1, cache.2) ctx label idx count rnd ↔
      DrawAnswered prims D cache ctx label idx count rnd := by
  simp only [DrawAnswered, streamAnswer_swapAll]

theorem drawCoherent_swapAll (prims : Primitives) (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (cache : HashCache C × HiddenCache C)
    (live : C.Party → Prop) (ctx : C.Party → Context C) (label count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) :
    TreeTwinHolderKeys.DrawCoherent prims D live (treeStagesSwapAll swaps cache.1, cache.2) ctx label count rnd ↔
      TreeTwinHolderKeys.DrawCoherent prims D live cache ctx label count rnd := by
  simp only [TreeTwinHolderKeys.DrawCoherent, streamAnswer_swapAll]

theorem drawCoherent_antitone (prims : Primitives) (D : C.Coalition)
    {live live' : C.Party → Prop} {cache : HashCache C × HiddenCache C} {ctx : C.Party → Context C}
    {label count : ℕ} {rnd : C.Party → PrssOutput C Bit}
    (h : TreeTwinHolderKeys.DrawCoherent prims D live cache ctx label count rnd)
    (sub : ∀ i, live' i → live i) :
    TreeTwinHolderKeys.DrawCoherent prims D live' cache ctx label count rnd :=
  fun i hi li => h i hi (sub i li)

-- Verbatim port of LifetimeSlotCoupling.relTriple_with_left_support.
-- Pinned/current leanVM CacheAgreement has the analogous two-sided strengthening.
theorem relTriple_with_left_support {α β : Type} {p : ProbComp α} {q : ProbComp β}
    {R : α → β → Prop} {P : α → Prop} (h : RelTriple p q R)
    (hp : ∀ a ∈ support p, P a) : RelTriple p q (fun a b => R a b ∧ P a) := by
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => ⟨hc z hz, hp z.1 ?_⟩⟩
  have hz' : z.1 ∈ support 𝒟[p] := by
    rw [← c.2.map_fst, support_map]
    exact ⟨z, hz, rfl⟩
  exact (mem_support_iff_evalDist_apply_ne_zero p z.1).2 hz'

/-- Support preservation through the same sequential state computation. -/
theorem sequenceFin_preserves {α σ : Type} {n : ℕ}
    (f : Fin n → StateT σ ProbComp α) (P : σ → Prop)
    (step : ∀ i s r, P s → r ∈ support ((f i).run s) → P r.2)
    (s : σ) (hs : P s) (r : (Fin n → α) × σ)
    (run : r ∈ support ((Concrete.sequenceFin f).run s)) : P r.2 := by
  induction n generalizing s with
  | zero =>
    simp only [Concrete.sequenceFin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at run
    subst r
    exact hs
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure,
      support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at run
    obtain ⟨u, hu, v, hv, rfl⟩ := run
    exact ih (fun i => f i.succ) (fun i => step i.succ) u.2 (step 0 s u hs hu) v hv

-- State-aware port of private TreeSim.treeSim_sequenceFin_rel (TreeSim:3504).
theorem sequenceFin_rel_stable {α β σ₁ σ₂ : Type} {n : ℕ}
    (f₁ : Fin n → StateT σ₁ ProbComp α) (f₂ : Fin n → StateT σ₂ ProbComp β)
    (I : σ₁ → σ₂ → Prop) (R : Fin n → α → β → σ₁ → Prop)
    (stable : ∀ i a b s j t, R i a b s → t ∈ support ((f₁ j).run s) → R i a b t.2)
    (step : ∀ i s₁ s₂, I s₁ s₂ →
      RelTriple ((f₁ i).run s₁) ((f₂ i).run s₂) (fun u v => R i u.1 v.1 u.2 ∧ I u.2 v.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : I s₁ s₂) :
    RelTriple ((Concrete.sequenceFin f₁).run s₁) ((Concrete.sequenceFin f₂).run s₂)
      (fun u v => (∀ i, R i (u.1 i) (v.1 i) u.2) ∧ I u.2 v.2) := by
  induction n generalizing s₁ s₂ with
  | zero =>
    simp only [Concrete.sequenceFin, StateT.run_pure]
    exact relTriple_pure_pure ⟨fun i => Fin.elim0 i, hs⟩
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (step 0 s₁ s₂ hs)
    intro u v huv
    apply relTriple_bind (relTriple_with_left_support
      (ih (fun i => f₁ i.succ) (fun i => f₂ i.succ) (fun i => R i.succ)
        (fun i a b s j t => stable i.succ a b s j.succ t)
        (fun i => step i.succ) u.2 v.2 huv.2)
      (fun us hus => sequenceFin_preserves (fun i : Fin n => f₁ i.succ) (R 0 u.1 v.1)
        (fun j s t => stable 0 u.1 v.1 s j.succ t) u.2 huv.1 us hus))
    intro us vs hus
    apply relTriple_pure_pure
    refine ⟨?_, hus.1.2⟩
    intro i
    cases i using Fin.cases with
    | zero => exact hus.2
    | succ i => exact hus.1.1 i

section Field
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

theorem stepRound_caches_grow {Ia α : Type} (D : C.Coalition)
    (A : Adversary C E Ia PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (s : TreeSimState C)
    (u : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (run : u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality state steps).run s)) :
    s.1.1 ≤ u.2.1.1 ∧ s.1.2 ≤ u.2.1.2 := by
  simp only [treeSimRealRoles, ← simulateQ_stepRound] at run
  exact logged_caches_grow prims D _ s u run

/-- Replay the actual draw result against its actual final cache. -/
theorem drawAnswered_of_logged (D : C.Coalition) (ctx : Context C) (ρ idx count : ℕ)
    (a : TreeSimState C) (u : PrssOutput C Bit × TreeSimState C)
    (run : u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run a)) :
    DrawAnswered prims D u.2.1 ctx ρ idx count u.1 := by
  have localRun := TreeCheckMaskExtraction.allowed_free _ _ _
    (treeLockstep_logged_run_allowed prims D _ a u run)
  -- Lift removal is the A202 drawCoherent_of_replay port, retaining arbitrary idx.
  have ro : TreeSimCheckAllowed
      (fun t v => TreeLockstepWorldStreams prims D u.2.1 (.inr (.inr t)) v)
      (prssDraw ctx (bitCodec (E := E)) ρ idx count) u.1 :=
    TreeSimCheckAllowed.simulate_inv
      (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (Sum.inr t)))
      (fun t v => TreeLockstepWorldStreams prims D u.2.1 (.inr t) v) _
      (fun t v hv => TreeSimCheckAllowed.query_inv
        (allowed := fun t v => TreeLockstepWorldStreams prims D u.2.1 (.inr t) v)
        (Sum.inr t) v hv) _ _ localRun
  exact TreeCheckWalkTranscript.term_mask prims D u.2.1 _ (fun _ _ h => h) ctx ρ idx count u.1 ro

-- Same witnesses as TreeSimPeerRel, with the real draw answer retained.
def TreeSimPeerRelAt {α : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : Context C) (idx count : ℕ) (v₁ v₂ : ℕ → Bit)
    (st₁ st₂ : RunState C) (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s₁ s₂ : Step C E RealSpec α) : Prop :=
  ∃ r₁ r₂ : PrssOutput C Bit,
    r₂.1 = r₁.1 + (treeSimPrssShift δ ctx₁ st₁.label idx count).1 ∧
    r₂.2 = r₁.2 + (treeSimPrssShift δ ctx₁ st₁.label idx count).2 ∧
    s₁ = treeSimPeerStep K ctx₁ (bitCodec (E := E)) r₁ v₁ count st₁ k₁ ∧
    s₂ = treeSimPeerStep K ctx₂ (bitCodec (E := E)) r₂ v₂ count st₂ k₂ ∧
    DrawAnswered prims D cache ctx₁ st₁.label idx count r₁

theorem TreeSimPeerRelAt_rel {α : Type} {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C} {idx count : ℕ} {v₁ v₂ : ℕ → Bit}
    {st₁ st₂ : RunState C} {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α}
    {s₁ s₂ : Step C E RealSpec α}
    (h : TreeSimPeerRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂) : TreeSimPeerRel K δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ := by
  obtain ⟨r₁, r₂, h₁, h₂, hs₁, hs₂, _⟩ := h
  exact ⟨r₁, r₂, h₁, h₂, hs₁, hs₂⟩

theorem TreeSimPeerRelAt_mono {α : Type} {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C} {idx count : ℕ} {v₁ v₂ : ℕ → Bit}
    {st₁ st₂ : RunState C} {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α}
    {s₁ s₂ : Step C E RealSpec α} {cache' : HashCache C × HiddenCache C}
    (hash : cache.1 ≤ cache'.1) (hidden : cache.2 ≤ cache'.2)
    (h : TreeSimPeerRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂) : TreeSimPeerRelAt prims K D cache' δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ := by
  obtain ⟨r₁, r₂, h₁, h₂, hs₁, hs₂, answered⟩ := h
  exact ⟨r₁, r₂, h₁, h₂, hs₁, hs₂, drawAnswered_mono prims D hash hidden answered⟩

theorem TreeSimPeerRelAt_swapAll {α : Type} {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C} {idx count : ℕ} {v₁ v₂ : ℕ → Bit}
    {st₁ st₂ : RunState C} {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α}
    {s₁ s₂ : Step C E RealSpec α}
    (swaps : List (List Bit × HashOutput × HashOutput)) :
    TreeSimPeerRelAt prims K D (treeStagesSwapAll swaps cache.1, cache.2) δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ ↔
      TreeSimPeerRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ := by
  simp only [TreeSimPeerRelAt, drawAnswered_swapAll]

-- Port of treeSim_peer_start_mixed: support strengthening precedes the same draw map.
theorem peer_start_mixed_at {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C) (lab : st₁.label = st₂.label)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((((prssRandomness ctx₁ (bitCodec (E := E)) idx count >>= fun o =>
          reshare K ctx₁ (bitCodec (E := E)) o v₁ count).run st₁) >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((((prssRandomness ctx₂ (bitCodec (E := E)) idx count >>= fun o =>
          reshare K ctx₂ (bitCodec (E := E)) o v₂ count).run st₂) >>= k₂).run)))).run b)
      (fun u v => TreeSimPeerRelAt prims K D u.2.1 δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1 v.1 ∧
        TreeSimStreamRel δ u.2 v.2) := by
  rw [treeSim_peer_entry, treeSim_peer_entry]
  rw [← lab, ← treeSim_prssDraw_context ctx₁ ctx₂ self keys]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_left_support
    (treeSim_prssBits_mixed prims D δ hδ ctx₁ st₁.label idx count a b hs)
    (fun u hu => drawAnswered_of_logged prims D ctx₁ st₁.label idx count a u hu))
  intro u v h
  exact ⟨⟨u.1, v.1, h.1.1, h.1.2.1, rfl, rfl, h.2⟩, h.1.2.2⟩

-- Same witnesses as TreeSimCollectorEntryRel, with the real draw answer retained.
def TreeSimCollectorEntryRelAt {α : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : Context C) (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s₁ s₂ : Step C E RealSpec α) : Prop :=
  ∃ rnd₁ rnd₂ : PrssOutput C Bit,
    rnd₂.1 = rnd₁.1 + (treeSimPrssShift δ ctx₁ st₁.label idx count).1 ∧
    rnd₂.2 = rnd₁.2 + (treeSimPrssShift δ ctx₁ st₁.label idx count).2 ∧
    s₁ = treeSimCollectorStep K ctx₁ rnd₁ v₁ count st₁ k₁ ∧
    s₂ = treeSimCollectorStep K ctx₂ rnd₂ v₂ count st₂ k₂ ∧
    DrawAnswered prims D cache ctx₁ st₁.label idx count rnd₁

theorem TreeSimCollectorEntryRelAt_rel {α : Type} {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C} {idx count : ℕ} {v₁ v₂ : ℕ → Bit}
    {st₁ st₂ : RunState C} {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α}
    {s₁ s₂ : Step C E RealSpec α}
    (h : TreeSimCollectorEntryRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂) : TreeSimCollectorEntryRel K δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ := by
  obtain ⟨r₁, r₂, h₁, h₂, hs₁, hs₂, _⟩ := h
  exact ⟨r₁, r₂, h₁, h₂, hs₁, hs₂⟩

theorem TreeSimCollectorEntryRelAt_mono {α : Type} {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C} {idx count : ℕ} {v₁ v₂ : ℕ → Bit}
    {st₁ st₂ : RunState C} {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α}
    {s₁ s₂ : Step C E RealSpec α} {cache' : HashCache C × HiddenCache C}
    (hash : cache.1 ≤ cache'.1) (hidden : cache.2 ≤ cache'.2)
    (h : TreeSimCollectorEntryRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂) : TreeSimCollectorEntryRelAt prims K D cache' δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ := by
  obtain ⟨r₁, r₂, h₁, h₂, hs₁, hs₂, answered⟩ := h
  exact ⟨r₁, r₂, h₁, h₂, hs₁, hs₂, drawAnswered_mono prims D hash hidden answered⟩

theorem TreeSimCollectorEntryRelAt_swapAll {α : Type} {D : C.Coalition} {cache : HashCache C × HiddenCache C}
    {δ : HiddenAddress C → Bit} {ctx₁ ctx₂ : Context C} {idx count : ℕ} {v₁ v₂ : ℕ → Bit}
    {st₁ st₂ : RunState C} {k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α}
    {s₁ s₂ : Step C E RealSpec α}
    (swaps : List (List Bit × HashOutput × HashOutput)) :
    TreeSimCollectorEntryRelAt prims K D (treeStagesSwapAll swaps cache.1, cache.2) δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ ↔
      TreeSimCollectorEntryRelAt prims K D cache δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂ := by
  simp only [TreeSimCollectorEntryRelAt, drawAnswered_swapAll]

-- Port of treeSim_collector_entry_mixed: support strengthening precedes the same draw map.
theorem collector_entry_mixed_at {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C) (lab : st₁.label = st₂.label)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((treeSimCollectorProgram K ctx₁ idx count v₁ st₁ >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((treeSimCollectorProgram K ctx₂ idx count v₂ st₂ >>= k₂).run)))).run b)
      (fun u z => TreeSimCollectorEntryRelAt prims K D u.2.1 δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  unfold treeSimCollectorProgram
  rw [treeSim_collector_entry, treeSim_collector_entry]
  rw [← lab, ← treeSim_prssDraw_context ctx₁ ctx₂ self keys]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_left_support
    (treeSim_prssBits_mixed prims D δ hδ ctx₁ st₁.label idx count a b hs)
    (fun u hu => drawAnswered_of_logged prims D ctx₁ st₁.label idx count a u hu))
  intro u v h
  exact ⟨⟨u.1, v.1, h.1.1, h.1.2.1, rfl, rfl, h.2⟩, h.1.2.2⟩

def TreeStagesPeerResumeRelAt (prims : Primitives) (K : Constants C E) (cache : HashCache C × HiddenCache C) (D : C.Coalition) (live : C.Party → Bool) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (x y : C.Party → Step C E RealSpec TreeOutput) : Prop :=
  ∀ i, if i ∈ D.1 then x i = .done none ∧ y i = .done none else
    if live i then TreeSimPeerRelAt prims K D cache δ (ctx₁ i) (ctx₂ i) idx count (v₁ i) (v₂ i) (st₁ i) (st₂ i) (k₁ i) (k₂ i) (x i) (y i)
    else x i = .done none ∧ y i = .done none


-- Port of TreeSimStages.treeStages_peer_resume_entry using the stable sequence.
theorem peer_resume_entry_at (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (live : C.Party → Bool)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (label : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (k₁ k₂ next₁ next₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (x₁ x₂ : C.Party → Shares C Bit × RunState C)
    (shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none)
    (shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none)
    (program₁ : ∀ i, i ∉ D.1 → live i = true → k₁ i (x₁ i) =
      treeSimPeerProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) (next₁ i))
    (program₂ : ∀ i, i ∉ D.1 → live i = true → k₂ i (x₂ i) =
      treeSimPeerProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) (next₂ i))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (related : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeStagesPeerResumeRelAt prims K u.2.1 D live δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ next₁ next₂ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  unfold treeSimResumeAll
  rw [free_sequenceFin, free_sequenceFin, simulateQ_sequenceFin, simulateQ_sequenceFin]
  apply sequenceFin_rel_stable _ _ (TreeSimStreamRel δ)
    (fun i u z s => if i ∈ D.1 then u = .done none ∧ z = .done none else
      if live i then TreeSimPeerRelAt prims K D s.1 δ (ctx₁ i) (ctx₂ i) idx count (v₁ i) (v₂ i)
        (st₁ i) (st₂ i) (next₁ i) (next₂ i) u z else u = .done none ∧ z = .done none)
  · intro i u z s j t h ht
    by_cases hi : i ∈ D.1
    · simpa only [if_pos hi] using h
    · simp only [if_neg hi] at h ⊢
      by_cases hl : live i = true
      · simp only [if_pos hl] at h ⊢
        have grows := logged_caches_grow prims D _ s t ht
        exact TreeSimPeerRelAt_mono prims K grows.1 grows.2 h
      · simpa only [if_neg hl] using h
  · intro i a b h
    rw [shape₁ i, shape₂ i]
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨rfl, rfl⟩, h⟩
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume, program₁ i hi hl, program₂ i hi hl]
        exact peer_start_mixed_at prims K D δ visible (ctx₁ i) (ctx₂ i) (self i hi) (keys i hi)
          idx count (v₁ i) (v₂ i) (st₁ i) (st₂ i) (label i hi) (next₁ i) (next₂ i) a b h
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨rfl, rfl⟩, h⟩
  · exact related

-- Port of TreeSimStages.treeStages_peer_resume_masks; choose retains the answer.
theorem peer_resume_masks_at (D : C.Coalition) (cache : HashCache C × HiddenCache C) (ρ : ℕ) (live : C.Party → Bool) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (x y : C.Party → Step C E RealSpec TreeOutput)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st₁ i).label = ρ)
    (related : TreeStagesPeerResumeRelAt prims K cache D live δ ctx₁ ctx₂ 0 count v₁ v₂ st₁ st₂ k₁ k₂ x y) :
    ∃ rnd₁ rnd₂ : C.Party → PrssOutput C Bit,
      (∀ i, i ∉ D.1 →
        (rnd₂ i).1 = (rnd₁ i).1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).1 ∧
        (rnd₂ i).2 = (rnd₁ i).2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).2) ∧
      x = treeSimPeerPartial K D ctx₁ live count rnd₁ v₁ st₁ k₁ ∧
      y = treeSimPeerPartial K D ctx₂ live count rnd₂ v₂ st₂ k₂ ∧
      TreeTwinHolderKeys.DrawCoherent prims D (fun i => live i = true) cache ctx₁ ρ count rnd₁ := by
  have witnesses : ∀ i, ∃ r₁ r₂ : PrssOutput C Bit,
      (i ∉ D.1 → r₂.1 = r₁.1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).1 ∧
        r₂.2 = r₁.2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).2) ∧
      x i = (if live i then if i ∈ D.1 then .done none else treeSimPeerStep K (ctx₁ i) bitCodec r₁ (v₁ i) count (st₁ i) (k₁ i) else .done none) ∧
      y i = (if live i then if i ∈ D.1 then .done none else treeSimPeerStep K (ctx₂ i) bitCodec r₂ (v₂ i) count (st₂ i) (k₂ i) else .done none) ∧
      (i ∉ D.1 → live i = true → DrawAnswered prims D cache (ctx₁ i) ρ 0 count r₁) := by
    intro i
    have h := related i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi] at h ⊢
      exact ⟨0, 0, fun hn => (hn hi).elim, (by simpa using h.1), (by simpa using h.2), fun hn => (hn hi).elim⟩
    · simp only [if_neg hi] at h ⊢
      by_cases hl : live i = true
      · simp only [if_pos hl] at h ⊢
        obtain ⟨r₁, r₂, hm₁, hm₂, hx, hy, answered⟩ := h
        exact ⟨r₁, r₂, fun _ => ⟨hm₁, hm₂⟩, hx, hy, fun _ _ => by simpa only [lab i hi hl] using answered⟩
      · simp only [if_neg hl] at h ⊢
        exact ⟨0, treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count,
          fun _ => ⟨by simp, by simp⟩, h.1, h.2, fun _ liveTrue => (hl liveTrue).elim⟩
  choose rnd₁ rnd₂ masks hx hy answered using witnesses
  exact ⟨rnd₁, rnd₂, masks, funext hx, funext hy,
    drawCoherent_of_answered prims D _ cache ctx₁ ρ count rnd₁ (fun i hi _ => self₁ i hi) answered⟩


end Field

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.logged_caches_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logged_caches_grow

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.stepRound_caches_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepRound_caches_grow

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.drawAnswered_of_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms drawAnswered_of_logged

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.sequenceFin_rel_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sequenceFin_rel_stable

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.peer_start_mixed_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms peer_start_mixed_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.collector_entry_mixed_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collector_entry_mixed_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.peer_resume_entry_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms peer_resume_entry_at

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinDrawReplay.peer_resume_masks_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms peer_resume_masks_at

end ThresholdLeanXmssSecurity.TreeTwinDrawReplay
