import ThresholdLeanXmssSecurity.Proof.SigningOpening

/-!
# Two-sided stopping for the signing compiler coupling

Two stateful handlers preserve a relation and equal answers until either of two
sticky bad events. The phase rule composes separately coupled program phases.
Nested stateful simulations fuse after reassociating their output states.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

namespace ThresholdLeanXmssSecurity.SigningCompilerUntil

variable {ι σ₁ σ₂ α β : Type} {spec : OracleSpec ι}

/-- The two runs have stopped, or their outputs and continuing states agree. -/
def Until (Bad₁ : σ₁ → Prop) (Bad₂ : σ₂ → Prop) (Sync : σ₁ → σ₂ → Prop)
    (a : α × σ₁) (b : α × σ₂) : Prop :=
  Bad₁ a.2 ∨ Bad₂ b.2 ∨ (a.1 = b.1 ∧ Sync a.2 b.2)

/-- Port of `SigningOpeningProof.relTriple_simulateQ_until`: distinct handlers and
state spaces, with a sticky stopping event on either side. -/
theorem relTriple_simulateQ_until
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (Bad₁ : σ₁ → Prop) (Bad₂ : σ₂ → Prop) (Sync : σ₁ → σ₂ → Prop)
    (hsticky₁ : ∀ t s, Bad₁ s → ∀ a ∈ support ((impl₁ t).run s), Bad₁ a.2)
    (hsticky₂ : ∀ t s, Bad₂ s → ∀ b ∈ support ((impl₂ t).run s), Bad₂ b.2)
    (hstep : ∀ t s₁ s₂, Sync s₁ s₂ → ¬ Bad₁ s₁ → ¬ Bad₂ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂) (Until Bad₁ Bad₂ Sync))
    (oa : OracleComp spec α) :
    ∀ s₁ s₂, Bad₁ s₁ ∨ Bad₂ s₂ ∨ Sync s₁ s₂ →
      RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
        (Until Bad₁ Bad₂ Sync) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s₁ s₂ hs
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rcases hs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  | query_bind t k ih =>
    intro s₁ s₂ hs
    by_cases hb₁ : Bad₁ s₁
    · exact relTriple_of_support_left fun a ha _ => Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₁ Bad₁ hsticky₁ _ s₁ hb₁ a ha)
    by_cases hb₂ : Bad₂ s₂
    · exact SigningOpeningProof.relTriple_of_support_right fun b hb _ => Or.inr (Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₂ Bad₂ hsticky₂ _ s₂ hb₂ b hb))
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    refine relTriple_bind (hstep t s₁ s₂ ((hs.resolve_left hb₁).resolve_left hb₂) hb₁ hb₂)
      fun a b hab => ?_
    rcases hab with h | h | ⟨heq, h⟩
    · exact relTriple_of_support_left fun c hc _ => Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₁ Bad₁ hsticky₁ _ a.2 h c hc)
    · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ => Or.inr (Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₂ Bad₂ hsticky₂ _ b.2 h c hc))
    · rw [heq]
      exact ih b.1 a.2 b.2 (Or.inr (Or.inr h))

/-- Separately coupled phases compose while either stopping event persists. -/
theorem relTriple_bind_until
    (Bad₁ : σ₁ → Prop) (Bad₂ : σ₂ → Prop) (Sync : σ₁ → σ₂ → Prop)
    {oa : ProbComp (α × σ₁)} {ob : ProbComp (α × σ₂)}
    (k₁ : α → StateT σ₁ ProbComp β) (k₂ : α → StateT σ₂ ProbComp β)
    (hprefix : RelTriple oa ob (Until Bad₁ Bad₂ Sync))
    (hsticky₁ : ∀ x s, Bad₁ s → ∀ a ∈ support ((k₁ x).run s), Bad₁ a.2)
    (hsticky₂ : ∀ x s, Bad₂ s → ∀ b ∈ support ((k₂ x).run s), Bad₂ b.2)
    (hnext : ∀ x s₁ s₂, Sync s₁ s₂ → ¬ Bad₁ s₁ → ¬ Bad₂ s₂ →
      RelTriple ((k₁ x).run s₁) ((k₂ x).run s₂) (Until Bad₁ Bad₂ Sync)) :
    RelTriple (oa >>= fun a => (k₁ a.1).run a.2)
      (ob >>= fun b => (k₂ b.1).run b.2) (Until Bad₁ Bad₂ Sync) := by
  refine relTriple_bind hprefix fun a b hab => ?_
  by_cases hb₁ : Bad₁ a.2
  · exact relTriple_of_support_left fun c hc _ => Or.inl (hsticky₁ _ _ hb₁ c hc)
  by_cases hb₂ : Bad₂ b.2
  · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ =>
      Or.inr (Or.inl (hsticky₂ _ _ hb₂ c hc))
  obtain ⟨heq, hs⟩ := (hab.resolve_left hb₁).resolve_left hb₂
  rw [heq]
  exact hnext _ _ _ hs hb₁ hb₂

variable {κ : Type} {mid : OracleSpec κ}

/-- Combine an inner handler's state with the state of its implementing oracle. -/
def fuse (inner : QueryImpl spec (StateT σ₁ (OracleComp mid)))
    (outer : QueryImpl mid (StateT σ₂ ProbComp)) :
    QueryImpl spec (StateT (σ₁ × σ₂) ProbComp) :=
  fun t sc => (fun z => (z.1.1, (z.1.2, z.2))) <$>
    (simulateQ outer ((inner t).run sc.1)).run sc.2

/-- Exact fusion, retaining both final states in their product order. -/
theorem simulateQ_fuse
    (inner : QueryImpl spec (StateT σ₁ (OracleComp mid)))
    (outer : QueryImpl mid (StateT σ₂ ProbComp)) (oa : OracleComp spec α) :
    ∀ s c, (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ outer ((simulateQ inner oa).run s)).run c =
      (simulateQ (fuse inner outer) oa).run (s, c) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s c
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    intro s c
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    have hf : (fuse inner outer t).run (s, c) =
        (fun z => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ outer ((inner t).run s)).run c := rfl
    rw [hf, bind_map_left]
    congr 1
    funext z
    exact ih z.1.1 z.1.2 z.2

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerUntil.relTriple_simulateQ_until' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_simulateQ_until
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerUntil.relTriple_bind_until' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_bind_until
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerUntil.simulateQ_fuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_fuse

end ThresholdLeanXmssSecurity.SigningCompilerUntil
