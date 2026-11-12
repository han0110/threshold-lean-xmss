import ThresholdLeanXmssSecurity.Proof.TreeTwinHashPrefill
import ThresholdLeanXmssSecurity.Proof.TreeStagesRelation

/-! # Joint prefilling before a read-complete pass
Whole hidden blocks are coupled by encoded field translation; public hash cells
use the same table. Both caches and the real query log are retained.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinPassPrefill
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} (prims : Primitives)

private theorem hidden_query_grows (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : HashCache C × HiddenCache C) (r : (WorldSpec C).Range t × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((streamWorld prims D t).run s)) : s.2 ≤ r.2.2 := by
  have onhash {α : Type} (m : StateT (HashCache C) ProbComp α)
      (z : α × (HashCache C × HiddenCache C)) (hz : z ∈ support ((onHash m).run s)) : s.2 ≤ z.2.2 := by
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact le_rfl
  rcases t with t | n | q | x
  · exact onhash _ r hr
  · exact onhash _ r hr
  · exact onhash _ r hr
  · by_cases hidden : Hidden D x.1
    · simp only [streamWorld, hidden, if_true, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      exact QueryImpl.withCaching_cache_le _ _ _ _ hu
    · simp only [streamWorld, hidden, if_false] at hr
      exact onhash _ r hr

/-- Hidden entries survive arbitrary stream-world programs. -/
theorem treeSim_hidden_grows {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (s : HashCache C × HiddenCache C) (r : α × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) p).run s)) : s.2 ≤ r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact le_rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      support_bind, Set.mem_iUnion] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact (hidden_query_grows prims D t s u hu).trans (ih u.1 u.2 r hr)

/-- Logging preserves the same monotone hidden cache. -/
theorem treeSim_hidden_grows_logged {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) : s.1.2 ≤ r.2.1.2 := by
  apply treeSim_hidden_grows prims D p s.1 (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D p s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- One selected step establishes a predicate that every later step preserves. -/
theorem sequenceFin_establish {σ α : Type} {n : ℕ} (f : Fin n → StateT σ ProbComp α)
    (Pre P : σ → Prop)
    (pre : ∀ i s u, u ∈ support ((f i).run s) → Pre s → Pre u.2)
    (persist : ∀ i s u, u ∈ support ((f i).run s) → P s → P u.2)
    (i₀ : Fin n) (establish : ∀ s u, u ∈ support ((f i₀).run s) → Pre s → P u.2) :
    ∀ s u, u ∈ support ((Concrete.sequenceFin f).run s) → Pre s → P u.2 := by
  induction n with
  | zero => exact Fin.elim0 i₀
  | succ n ih =>
    intro s u hu hs
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hu
    obtain ⟨v, hv, w, hw, rfl⟩ := hu
    cases i₀ using Fin.cases with
    | zero =>
      exact treeStages_sequenceFin_persist (fun i => f i.succ) P (fun i => persist i.succ)
        v.2 w hw (establish s v hv hs)
    | succ i =>
      exact ih (fun i => f i.succ) (fun i => pre i.succ) (fun i => persist i.succ)
        i establish v.2 w hw (pre 0 s v hv hs)

/-- The hidden-table prefill law with only the real log erased. -/
theorem treeSim_prefill_stream_table {α : Type} (D : C.Coalition) {n : ℕ}
    (addr : Fin n → HiddenAddress C) (inj : Function.Injective addr)
    (hidden : ∀ i, Hidden D (addr i).1.1) (p : OracleComp (WorldSpec C) α)
    (h : HashCache C) (c : HiddenCache C) (fresh : ∀ i, c (addr i) = none)
    (read : ∀ u ∈ support ((simulateQ (streamWorld prims D) p).run (h, c)),
      ∀ i, u.2.2 (addr i) ≠ none) :
    evalDist ((simulateQ (streamWorld prims D) p).run (h, c)) =
      evalDist (do
        let bits ← ($ᵗ (Fin n → Bit) : ProbComp (Fin n → Bit))
        (simulateQ (streamWorld prims D) p).run (h, cacheFin addr bits c)) := by
  have hr : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run ((h, c), [])),
      ∀ i, u.2.1.2 (addr i) ≠ none := by
    intro u hu
    apply read (u.1, u.2.1)
    rw [← treeSimLoggedWorld_erase prims D p (h, c) [], support_map]
    exact ⟨u, hu, rfl⟩
  have he := TreeTwinPrefill.treeSim_prefill_logged_table prims D addr inj hidden p h c [] fresh hr
  have hm := evalDist_map_eq_of_evalDist_eq he (fun r : α × TreeSimState C => (r.1, r.2.1))
  simpa only [map_bind, treeSimLoggedWorld_erase] using hm

private theorem supported_table {α β : Type} [SampleableType β] (p : ProbComp α)
    (k : β → ProbComp α) (he : evalDist p = evalDist (do let v ← ($ᵗ β); k v))
    (v : β) (u : α) (hu : u ∈ support (k v)) : u ∈ support p := by
  rw [mem_support_iff, probOutput_def, he, ← probOutput_def, ← mem_support_iff]
  exact (mem_support_bind_iff _ _ _).2 ⟨v, by simp, hu⟩

variable {E : Type} [Field E] [Algebra Bit E]
variable (K : Constants C E)

/-- Exact contents and frames of the selected hidden blocks and public cells. -/
structure Prefilled (D : C.Coalition) (label idx count : ℕ) (δ₀ : KeyName C → Fin count → E)
    (blockList : List (KeyName C × HashOutput)) (qs : List (Query C))
    (h₀ : HashCache C) (c₁₀ c₂₀ : HiddenCache C) (h : HashCache C) (c₁ c₂ : HiddenCache C) : Prop where
  blocks : ∀ x ∈ blockList, ∃ bits : Fin (count * elementBits) → Bit,
    (∀ g, c₁ (x, label, idx, g.val) = some (bits g)) ∧
    (∀ g, c₂ (x, label, idx, g.val) = some (treeStagesFieldShift K count (δ₀ x.1) bits g))
  frame₁ : ∀ y, (∀ x ∈ blockList, ∀ g : Fin (count * elementBits), y ≠ (x, label, idx, g.val)) → c₁ y = c₁₀ y
  frame₂ : ∀ y, (∀ x ∈ blockList, ∀ g : Fin (count * elementBits), y ≠ (x, label, idx, g.val)) → c₂ y = c₂₀ y
  hashes : ∀ q ∈ qs, h q ≠ none
  hashFrame : ∀ q', q' ∉ qs → h q' = h₀ q'

/-- Restore the head block to a tail prefill certificate. -/
private theorem prefilled_cons (D : C.Coalition) (label idx count : ℕ)
    (δ₀ : KeyName C → Fin count → E) (x : KeyName C × HashOutput)
    (xs : List (KeyName C × HashOutput)) (notmem : x ∉ xs) (qs : List (Query C))
    (h₀ h : HashCache C) (c₁₀ c₂₀ c₁ c₂ : HiddenCache C)
    (bits : Fin (count * elementBits) → Bit)
    (hc : Prefilled K D label idx count δ₀ xs qs h₀
      (cacheFin (fun g : Fin (count * elementBits) => (x, label, idx, g.val)) bits c₁₀)
      (cacheFin (fun g : Fin (count * elementBits) => (x, label, idx, g.val))
        (treeStagesFieldShift K count (δ₀ x.1) bits) c₂₀) h c₁ c₂) :
    Prefilled K D label idx count δ₀ (x :: xs) qs h₀ c₁₀ c₂₀ h c₁ c₂ := by
  let addr := fun g : Fin (count * elementBits) => (x, label, idx, g.val)
  have inj : Function.Injective addr := fun i j he => Fin.ext (congrArg (fun y => y.2.2.2) he)
  have miss (g : Fin (count * elementBits)) : ∀ y ∈ xs, ∀ j : Fin (count * elementBits),
      addr g ≠ (y, label, idx, j.val) := by
    intro y hy j he
    have hh : x = y := congrArg Prod.fst he
    exact notmem (hh.symm ▸ hy)
  refine ⟨?_, ?_, ?_, hc.hashes, hc.hashFrame⟩
  · intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨bits, fun g => (hc.frame₁ (addr g) (miss g)).trans (cacheFin_at addr inj bits c₁₀ g),
        fun g => (hc.frame₂ (addr g) (miss g)).trans (cacheFin_at addr inj _ c₂₀ g)⟩
    · exact hc.blocks y hy
  · intro y hy
    exact (hc.frame₁ y (fun z hz g => hy z (List.mem_cons_of_mem _ hz) g)).trans
      (cacheFin_of_not_mem addr bits c₁₀ y (fun g => hy x (List.mem_cons_self ..) g))
  · intro y hy
    exact (hc.frame₂ y (fun z hz g => hy z (List.mem_cons_of_mem _ hz) g)).trans
      (cacheFin_of_not_mem addr _ c₂₀ y (fun g => hy x (List.mem_cons_self ..) g))



/-- Couple the complete pass after filling precisely its mandatory-read cells. -/
theorem prefill_pass_coupling {α β : Type} (D : C.Coalition) (label idx count : ℕ)
    (δ₀ : KeyName C → Fin count → E) (blocks : List (KeyName C × HashOutput))
    (nodupB : blocks.Nodup) (hiddenB : ∀ x ∈ blocks, Hidden D x.1)
    (qs : List (Query C)) (nodupQ : qs.Nodup) (randomQ : ∀ q ∈ qs, ¬ IsFixed q)
    (p₁ : OracleComp (LocalSpec C) α) (p₂ : OracleComp (LocalSpec C) β)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (pub : a.1.1 = b.1)
    (fresh₁ : ∀ x ∈ blocks, ∀ g : Fin (count * elementBits), a.1.2 (x, label, idx, g.val) = none)
    (fresh₂ : ∀ x ∈ blocks, ∀ g : Fin (count * elementBits), b.2 (x, label, idx, g.val) = none)
    (freshQ : ∀ q ∈ qs, a.1.1 q = none)
    (read₁ : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p₁)).run a),
      (∀ x ∈ blocks, ∀ g : Fin (count * elementBits), u.2.1.2 (x, label, idx, g.val) ≠ none) ∧
        ∀ q ∈ qs, u.2.1.1 q ≠ none)
    (read₂ : ∀ u ∈ support ((simulateQ (streamWorld prims D) (free p₂)).run b),
      (∀ x ∈ blocks, ∀ g : Fin (count * elementBits), u.2.2 (x, label, idx, g.val) ≠ none) ∧
        ∀ q ∈ qs, u.2.1 q ≠ none)
    (R : (α × TreeSimState C) → (β × (HashCache C × HiddenCache C)) → Prop)
    (cont : ∀ h c₁ c₂, Prefilled K D label idx count δ₀ blocks qs a.1.1 a.1.2 b.2 h c₁ c₂ →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free p₁)).run ((h, c₁), a.2))
        ((simulateQ (streamWorld prims D) (free p₂)).run (h, c₂)) R) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free p₁)).run a)
      ((simulateQ (streamWorld prims D) (free p₂)).run b) R := by
  induction blocks generalizing a b with
  | nil =>
    rcases a with ⟨⟨h, c₁⟩, log⟩
    rcases b with ⟨h₂, c₂⟩
    dsimp only at pub
    subst h₂
    have he₁ := TreeTwinHashPrefill.prefillHash_sequence prims D qs nodupQ randomQ p₁
      ((h, c₁), log) freshQ (fun u hu => (read₁ u hu).2)
    have he₂ := TreeTwinHashPrefill.prefillHash_sequence_stream prims D qs nodupQ randomQ p₂
      (h, c₂) freshQ (fun u hu => (read₂ u hu).2)
    apply relTriple_of_evalDist_eq_left he₁
    apply relTriple_of_evalDist_eq_right he₂.symm
    apply relTriple_bind (relTriple_uniformSample_bij (Equiv.refl (Fin qs.length → HashOutput)).bijective
      Eq (fun _ => rfl))
    intro vals vals₂ he
    subst vals₂
    apply cont (cacheFin qs.get vals h) c₁ c₂
    refine ⟨by simp, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
    · intro q hq
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hq
      rw [cacheFin_at qs.get nodupQ.injective_get]
      exact Option.some_ne_none _
    · intro q hq
      exact cacheFin_of_not_mem qs.get vals h q (fun i he => hq (he.symm ▸ List.get_mem qs i))
  | cons x xs ih =>
    rcases a with ⟨⟨h, c₁⟩, log⟩
    rcases b with ⟨h₂, c₂⟩
    dsimp only at pub
    subst h₂
    have nd := List.nodup_cons.1 nodupB
    let addr := fun g : Fin (count * elementBits) => (x, label, idx, g.val)
    have inj : Function.Injective addr := fun i j he => Fin.ext (congrArg (fun y => y.2.2.2) he)
    have hidden : ∀ g, Hidden D (addr g).1.1 := fun _ => hiddenB x (List.mem_cons_self ..)
    have he₁ := TreeTwinPrefill.treeSim_prefill_logged_table prims D addr inj hidden (free p₁)
      h c₁ log (fresh₁ x (List.mem_cons_self ..))
      (fun u hu => (read₁ u hu).1 x (List.mem_cons_self ..))
    have he₂ := treeSim_prefill_stream_table prims D addr inj hidden (free p₂)
      h c₂ (fresh₂ x (List.mem_cons_self ..))
      (fun u hu => (read₂ u hu).1 x (List.mem_cons_self ..))
    apply relTriple_of_evalDist_eq_left he₁
    apply relTriple_of_evalDist_eq_right he₂.symm
    apply relTriple_bind (relTriple_uniformSample_bij (treeStagesFieldShift K count (δ₀ x.1)).bijective
      (fun bits bits₂ => bits₂ = treeStagesFieldShift K count (δ₀ x.1) bits) (fun _ => rfl))
    intro bits bits₂ he
    subst bits₂
    have miss (y : KeyName C × HashOutput) (hy : y ∈ xs) (g : Fin (count * elementBits)) :
        ∀ i, (y, label, idx, g.val) ≠ addr i := by
      intro i he
      have hh : y = x := congrArg Prod.fst he
      exact nd.1 (hh ▸ hy)
    apply ih nd.2 (fun y hy => hiddenB y (List.mem_cons_of_mem _ hy))
      ((h, cacheFin addr bits c₁), log)
      (h, cacheFin addr (treeStagesFieldShift K count (δ₀ x.1) bits) c₂) rfl
    · intro y hy g
      exact (cacheFin_of_not_mem addr bits c₁ _ (miss y hy g)).trans
        (fresh₁ y (List.mem_cons_of_mem _ hy) g)
    · intro y hy g
      exact (cacheFin_of_not_mem addr _ c₂ _ (miss y hy g)).trans
        (fresh₂ y (List.mem_cons_of_mem _ hy) g)
    · exact freshQ
    · intro u hu
      have hr := read₁ u (supported_table _ _ he₁ bits u hu)
      exact ⟨fun y hy => hr.1 y (List.mem_cons_of_mem _ hy), hr.2⟩
    · intro u hu
      have hr := read₂ u (supported_table _ _ he₂ (treeStagesFieldShift K count (δ₀ x.1) bits) u hu)
      exact ⟨fun y hy => hr.1 y (List.mem_cons_of_mem _ hy), hr.2⟩
    · intro h' c₁' c₂' hc
      exact cont h' c₁' c₂' (prefilled_cons K D label idx count δ₀ x xs nd.1 qs
        h h' c₁ c₂ c₁' c₂' bits hc)

end ThresholdLeanXmssSecurity.TreeTwinPassPrefill

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPassPrefill.treeSim_hidden_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPassPrefill.treeSim_hidden_grows

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPassPrefill.treeSim_hidden_grows_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPassPrefill.treeSim_hidden_grows_logged

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPassPrefill.sequenceFin_establish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPassPrefill.sequenceFin_establish

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPassPrefill.treeSim_prefill_stream_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPassPrefill.treeSim_prefill_stream_table

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPassPrefill.prefill_pass_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPassPrefill.prefill_pass_coupling
