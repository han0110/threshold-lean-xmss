import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.StepBase
import ThresholdLeanXmssSecurity.Proof.SigningCompilerCouplingUntil

/-!
# The step on the two worlds

`saltProvStep` proves `SaltProvStep`. The left side is `shiftedWorld`, which is `loggedWorld` under the
rewrite `provShift`. The right side is `provWorld`. `ProvSync` couples the two states. The queue, the
hidden table and the log are equal, and the hash cache of the left side is the hash cache of the right
side with the separate table merged over it through the shift (`shiftTable`).

`provStep` couples one call until `δ` is named. A private free digest call reads the cell `(salt, h)`
of the separate table on the right side and the cell `(salt + δ, h)` of the merged cache on the left
side. These cells agree, because the salt of a private entry is a full hidden salt and no ordinary
digest cell under a shifted full hidden salt has a value before `δ` is named. A call that meets a cell
of the shifted table from the ordinary cache writes that cell on the right side, and then `δ` is named.
Each other call runs as `loggedWorld` on both sides (`loggedWorld_merge`). At the end a counted call
under a shifted full hidden salt has its cell in the hash cache, so `δ` is named.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open OracleComp.ProgramLogic.Relational ThresholdLeanXmssSecurity.SigningCompilerUntil

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The coupling of the two states. The left state is the right state with the separate table merged
over the hash cache through the shift, and the right state has `ProvInv`. -/
def ProvSync (D : C.Coalition) (δ : Fin 256 → Bit) (s₁ : ProvQueue C × LogState C) (s₂ : ProvState C) : Prop :=
  s₁ = (s₂.2.1, mergeLog (shiftTable δ s₂.2.2) s₂.1) ∧ ProvInv D s₂

theorem provSync_start (D : C.Coalition) (δ : Fin 256 → Bit) :
    ProvSync D δ (([] : ProvQueue C), (((∅, ∅), []) : LogState C)) provStart := by
  refine ⟨?_, provInv_provStart D⟩
  simp only [provStart, mergeLog, shiftTable_empty, mergeCache_empty]

variable (prims : Primitives)

/-- A call of `loggedWorld` keeps `ProvInv` with an unchanged separate table, when the new queue has
`QueueInv`. -/
theorem provInv_frame (D : C.Coalition) (t : (WorldSpec C).Domain) (s₂ : ProvState C) (hI : ProvInv D s₂)
    (z : (WorldSpec C).Range t × LogState C) (hz : z ∈ support ((loggedWorld prims D t).run s₂.1))
    (queue : ProvQueue C) (hq : QueueInv D z.2.1.2 queue) : ProvInv D (z.2, queue, s₂.2.2) := by
  obtain ⟨-, hT, hL⟩ := hI
  obtain ⟨gm, gh⟩ := loggedWorld_grows prims D t s₂.1 z hz
  refine ⟨hq, fun salt history hne => fullHiddenSalts_mono D gh (hT salt history hne), fun salt history hmem => ?_⟩
  change Query.digest salt history ∈ z.2.2 at hmem
  rw [loggedWorld_log prims D t s₂.1 z hz, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hL salt history hmem)
    change z.2.1.1 _ ≠ none
    rw [gm _ v hv]
    simp
  · rcases t with ((u | q | x) | p) | (u | q | x)
    all_goals simp only [countedCells, List.not_mem_nil, List.mem_singleton] at hmem
    subst hmem
    rw [loggedWorld_countedHash, hashAnswer_digest] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (randomOracle_grows _ _ w hw).2

/-- A call that runs as `loggedWorld` on both sides, with no cell of the shifted table, keeps the
coupling. -/
theorem provStep_frame (D : C.Coalition) (δ : Fin 256 → Bit) (t : (WorldSpec C).Domain) (s₂ : ProvState C)
    (newQueue : (WorldSpec C).Range t → ProvQueue C)
    (hfree : ∀ q, mainCell t = some q → CellFree (shiftTable δ s₂.2.2) q)
    (hQ : ∀ z ∈ support ((loggedWorld prims D t).run s₂.1), QueueInv D z.2.1.2 (newQueue z.1))
    (hI : ProvInv D s₂)
    (hshift : (shiftedWorld prims D δ t).run (s₂.2.1, mergeLog (shiftTable δ s₂.2.2) s₂.1) =
      (fun z => (z.1, (newQueue z.1, z.2))) <$> (loggedWorld prims D t).run (mergeLog (shiftTable δ s₂.2.2) s₂.1))
    (hprov : (provWorld prims D t).run s₂ =
      (fun z => (z.1, (z.2, newQueue z.1, s₂.2.2))) <$> (loggedWorld prims D t).run s₂.1) :
    RelTriple ((shiftedWorld prims D δ t).run (s₂.2.1, mergeLog (shiftTable δ s₂.2.2) s₂.1))
      ((provWorld prims D t).run s₂) (Until (fun _ => False) (NamedBy D δ) (ProvSync D δ)) := by
  rw [hshift, loggedWorld_merge prims D _ t hfree, Functor.map_map, hprov]
  exact relTriple_map (relTriple_refl_of_mem_support _ fun z hz =>
    Or.inr (Or.inr ⟨rfl, rfl, provInv_frame prims D t s₂ hI z hz _ (hQ z hz)⟩))

/-- A call after which the hash cache of `provWorld` holds a digest cell under a shifted full hidden
salt names `δ`. -/
theorem provStep_diverge (D : C.Coalition) (δ : Fin 256 → Bit) (t : (WorldSpec C).Domain) {α : Type}
    (oa : ProbComp α) (s₂ : ProvState C) (salt : List Bit) (history : HashOutput)
    (hs : salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) s₂.1.1.2))
    (hset : ∀ z ∈ support ((provWorld prims D t).run s₂), z.2.1.1.1 (.digest salt history) ≠ none) :
    RelTriple oa ((provWorld prims D t).run s₂) (fun _ b => False ∨ NamedBy D δ b.2 ∨ False) :=
  SigningOpeningProof.relTriple_of_support_right fun b hb _ => Or.inr (Or.inl
    ⟨salt, history, hset b hb, fullHiddenSalts_mono D (provWorld_grows prims D t s₂ b hb).2.shiftCache hs⟩)

/-- The coupling of one call of the two worlds, until `δ` is named. -/
theorem provStep (D : C.Coalition) (δ : Fin 256 → Bit) (t : (WorldSpec C).Domain) (s₁ : ProvQueue C × LogState C)
    (s₂ : ProvState C) (hs : ProvSync D δ s₁ s₂) (hb : ¬ NamedBy D δ s₂) :
    RelTriple ((shiftedWorld prims D δ t).run s₁) ((provWorld prims D t).run s₂)
      (Until (fun _ => False) (NamedBy D δ) (ProvSync D δ)) := by
  obtain ⟨rfl, hI⟩ := hs
  obtain ⟨hQ, hT, hL⟩ := hI
  have hmain : ∀ salt history, salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) s₂.1.1.2) →
      s₂.1.1.1 (.digest salt history) = none := fun salt history h => by
    by_contra hc
    exact hb ⟨salt, history, hc, h⟩
  have hshT : ∀ salt history, shiftTable δ s₂.2.2 (salt, history) ≠ none →
      salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) s₂.1.1.2) := fun _ _ h => mem_of_shiftTable D δ hT h
  have div : ∀ salt history, shiftTable δ s₂.2.2 (salt, history) ≠ none →
      (∀ z ∈ support ((provWorld prims D t).run s₂), z.2.1.1.1 (.digest salt history) ≠ none) →
      RelTriple ((shiftedWorld prims D δ t).run (s₂.2.1, mergeLog (shiftTable δ s₂.2.2) s₂.1))
        ((provWorld prims D t).run s₂) (Until (fun _ => False) (NamedBy D δ) (ProvSync D δ)) :=
    fun salt history h hset =>
      relTriple_post_mono (provStep_diverge prims D δ t _ s₂ salt history (hshT _ _ h) hset) fun _ _ hab => by
        rcases hab with h | h | h
        · exact h.elim
        · exact Or.inr (Or.inl h)
        · exact h.elim
  by_cases h₁ : ∃ salt history, t = .inr (.inr (.inl (.digest salt history)))
  · obtain ⟨salt, history, rfl⟩ := h₁
    have plain : ∀ rest : ProvQueue C, QueueInv D s₂.1.1.2 rest →
        (shiftedWorld prims D δ (.inr (.inr (.inl (.digest salt history))))).run
            (s₂.2.1, mergeLog (shiftTable δ s₂.2.2) s₂.1) =
          (fun z => (z.1, (rest, z.2))) <$> (loggedWorld prims D (.inr (.inr (.inl (.digest salt history))))).run
            (mergeLog (shiftTable δ s₂.2.2) s₂.1) →
        (provWorld prims D (.inr (.inr (.inl (.digest salt history))))).run s₂ =
          (fun z => (z.1, (z.2, rest, s₂.2.2))) <$> (loggedWorld prims D (.inr (.inr (.inl (.digest salt history))))).run
            s₂.1 →
        RelTriple ((shiftedWorld prims D δ (.inr (.inr (.inl (.digest salt history))))).run
            (s₂.2.1, mergeLog (shiftTable δ s₂.2.2) s₂.1))
          ((provWorld prims D (.inr (.inr (.inl (.digest salt history))))).run s₂)
          (Until (fun _ => False) (NamedBy D δ) (ProvSync D δ)) := by
      intro rest hrest hshift hprov
      by_cases hf : shiftTable δ s₂.2.2 (salt, history) = none
      · exact provStep_frame prims D δ _ s₂ (fun _ => rest) (fun q hq salt' history' e => by
          cases hq
          cases e
          exact hf) (fun z hz => hrest.grows (loggedWorld_grows prims D _ _ z hz).2) ⟨hQ, hT, hL⟩ hshift hprov
      · refine div salt history hf fun z hz => ?_
        rw [hprov] at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [loggedWorld_freeHash, hashAnswer_digest] at hw
        simp only [support_map, Set.mem_image] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        exact (randomOracle_grows _ _ w' hw').2
    rcases hq : s₂.2.1 with _ | ⟨entry, rest⟩
    · rw [← hq]
      exact plain [] (queueInv_nil _ _) (by rw [hq]; exact shiftedWorld_digest_nil prims D δ salt history _)
        (provWorld_digest_nil prims D salt history s₂ hq)
    · rw [← hq]
      by_cases hp : Private D entry salt
      · have hfull : salt ∈ fullHiddenSalts D s₂.1.1.2 :=
          hQ.mem_of_private (by rw [hq]; exact List.mem_cons_self) hp
        have hlen := length_of_mem_fullHiddenSalts hfull
        have hm := hmain (addSalt δ salt) history (addSalt_mem_fullHiddenSalts D δ hfull)
        rw [hq, shiftedWorld_digest_cons, ite_eq_left hp, provWorld_digest_cons prims D salt history s₂ entry rest hq,
          ite_eq_left hp, loggedWorld_freeHash, hashAnswer_digest, randomOracle.run_eq, randomOracle.run_eq]
        have hcell : (mergeLog (shiftTable δ s₂.2.2) s₂.1).1.1 (.digest (addSalt δ salt) history) =
            s₂.2.2 (salt, history) := by
          change mergeCache s₂.1.1.1 (shiftTable δ s₂.2.2) (.digest (addSalt δ salt) history) = _
          cases hv : s₂.2.2 (salt, history) with
          | some v => exact mergeCache_digest _ _ _ _ v (by rw [shiftTable_addSalt δ _ _ _ hlen, hv])
          | none => simp [mergeCache, QueryCache.ofFn, shiftTable_addSalt δ _ _ _ hlen, hv, hm]
        rw [hcell]
        have hrest : QueueInv D s₂.1.1.2 rest := by
          rw [hq] at hQ
          exact hQ.tail
        cases hv : s₂.2.2 (salt, history) with
        | some v =>
          simp only [map_pure]
          exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, rfl, hrest, hT, hL⟩))
        | none =>
          simp only [map_bind, map_pure]
          refine relTriple_bind (relTriple_refl ($ᵗ HashOutput)) fun a b hab => ?_
          cases hab
          refine relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, ?_, hrest, ?_, hL⟩))
          · simp only [mergeLog, shiftTable_cacheQuery δ _ _ _ _ hlen, mergeCache_cacheTable]
          · intro salt' history' hne
            by_cases e : (salt', history') = (salt, history)
            · cases e
              exact hfull
            · rw [QueryCache.cacheQuery_of_ne _ _ e] at hne
              exact hT salt' history' hne
      · have hrest : QueueInv D s₂.1.1.2 rest := by
          rw [hq] at hQ
          exact hQ.tail
        exact plain rest hrest (by rw [hq, shiftedWorld_digest_cons, ite_eq_right hp])
          (by rw [provWorld_digest_cons prims D salt history s₂ entry rest hq, ite_eq_right hp])
  by_cases h₂ : ∃ x, t = .inr (.inr (.inr x))
  · obtain ⟨x, rfl⟩ := h₂
    refine provStep_frame prims D δ _ s₂ (fun b => pushRead x b s₂.2.1) (fun q hq => by cases hq)
      (fun z hz => hQ.push (loggedWorld_grows prims D _ _ z hz).2 x z.1 fun hx => ?_) ⟨hQ, hT, hL⟩
      (shiftedWorld_stream prims D δ x _ _) (provWorld_stream prims D x s₂)
    rw [loggedWorld_run_hidden prims D x hx] at hz
    cases hc : s₂.1.1.2 (streamCell x) with
    | some v =>
      rw [hc] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hc
    | none =>
      rw [hc] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨u, _, rfl⟩ := hz
      simp
  push Not at h₁ h₂
  have hshift := shiftedWorld_other prims D δ t (fun s h e => h₁ s h e) (fun x e => h₂ x e) s₂.2.1
    (mergeLog (shiftTable δ s₂.2.2) s₂.1)
  have hprov := provWorld_other prims D t (fun s h e => h₁ s h e) (fun x e => h₂ x e) s₂
  by_cases hfree : ∀ q, mainCell t = some q → CellFree (shiftTable δ s₂.2.2) q
  · exact provStep_frame prims D δ t s₂ (fun _ => s₂.2.1) hfree
      (fun z hz => hQ.grows (loggedWorld_grows prims D _ _ z hz).2) ⟨hQ, hT, hL⟩ hshift hprov
  push Not at hfree
  obtain ⟨q, hq, hnf⟩ := hfree
  simp only [CellFree, not_forall] at hnf
  obtain ⟨salt, history, rfl, hne⟩ := hnf
  have hm := hmain salt history (hshT salt history hne)
  refine div salt history hne fun z hz => ?_
  rw [hprov] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases t with ((u | q' | x) | p) | (u | q' | x)
  all_goals simp only [mainCell, reduceCtorEq, Option.some.injEq] at hq
  · subst hq
    rw [loggedWorld_countedHash, hashAnswer_digest] at hw
    simp only [support_map, Set.mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact (randomOracle_grows _ _ w' hw').2
  · simp only [loggedWorld, streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hw
    rw [localProgram_inr] at hw
    obtain ⟨w', ⟨w'', hw'', rfl⟩, rfl⟩ := hw
    rw [← hq] at hm ⊢
    exact (programAnswer_grows p _ w'' hw'').2 hm (fun ⟨input, e, _⟩ => by rw [hq] at e; cases e)
  · subst hq
    exact absurd rfl (h₁ salt history)

/-- The step on the world. In `loggedWorld` with the rewritten calls, a counted call under a shifted
full hidden salt has at most the probability that `provWorld` names the shift. The bound is a mean over
the run from the empty start. -/
theorem saltProvStep : SaltProvStep (C := C) prims := by
  intro D δ α oa
  have hleft : (simulateQ (loggedWorld prims D) ((simulateQ (provShift D δ) oa).run' [])).run ((∅, ∅), []) =
      (fun y => (y.1, y.2.2)) <$> (simulateQ (shiftedWorld prims D δ) oa).run ([], ((∅, ∅), [])) := by
    rw [shiftedWorld, ← simulateQ_fuse (provShift D δ) (loggedWorld prims D) oa [] ((∅, ∅), []), StateT.run'_eq,
      simulateQ_map, StateT.run_map, Functor.map_map]
  rw [hleft, prEvent_map]
  simp only [mem_named]
  have coupled := relTriple_simulateQ_until (shiftedWorld prims D δ) (provWorld prims D) (fun _ => False)
    (NamedBy D δ) (ProvSync D δ) (fun _ _ h => h.elim) (namedBy_sticky prims D δ)
    (fun t s₁ s₂ hs _ hb => provStep prims D δ t s₁ s₂ hs hb) oa ([], ((∅, ∅), [])) provStart
    (Or.inr (Or.inr (provSync_start D δ)))
  refine prEvent_le_of_relTriple coupled (p := fun y => ShiftHit D δ (y.1, y.2.2).2)
    (q := fun y => NamedBy D δ y.2) fun y₁ y₂ hR hhit => ?_
  rcases hR with hf | hb | ⟨-, hs, -, -, hL⟩
  · exact hf.elim
  · exact hb
  · obtain ⟨q, hq, salt, history, hsalt, rfl⟩ := hhit
    rw [hs] at hq hsalt
    exact ⟨salt, history, hL salt history hq, hsalt⟩

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.provStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.provStep

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.saltProvStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.saltProvStep
