import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndProvenance

/-!
# The stream cells at the end of the game with a table

The stream cells of the public cache grow by at most one for each call of `Adds .stream`
(`jointKeyWorld_within`). A walk of the game moves the potential `CellPot`, the cells and the cost of
the runs that remain. The seed generation, the signing oracles, the monitor and the win test add only
the calls of the adversary. In the network phase of a tree run, each honest operator keeps its own set
of stream cells (`KeyThen`, `executePhase_cells`). A ceremony draws only under the keys of its own
setup (`KeyCells.runJobs_k`), at most `termCount + n` keys (`card_keyCells`). So `cellsCount` proves
`CellsCount`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open DigestBudgets (ClassBound StateBound)
open Draws (NoBad NoBadS)
open UsedHit (Entry Table entryName tableFresh)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_sequenceFin)

attribute [local instance] Classical.propDecidable

attribute [local irreducible] wrongOutput

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The stream cells of the public cache -/

section CellsWorld

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

open FirstCounts (Within Adds)

/-- A hidden draw of the ideal joint world keeps the public cache. -/
theorem jointHidden_hash (x : KeyName C × HashOutput) (s : KeyJointState C) :
    ∀ r ∈ support ((jointHidden false x).run s), r.2.hash = s.hash := by
  intro r hr
  rcases hk : s.keys x with _ | v
  · simp only [jointHidden, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_mk, hk, support_map,
      Set.mem_image] at hr
    obtain ⟨v, -, rfl⟩ := hr
    rfl
  · simp only [jointHidden, StateT.run_mk, hk, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl

/-- A call of the ideal joint world adds at most one stream cell to the public cache, and only if it is
a call of `Adds .stream`. -/
theorem jointKeyWorld_cells (t : (WorldSpec C).Domain) (s : KeyJointState C) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), ∃ key, ∀ x, GameCount.CellIn .stream x →
      r.2.hash x ≠ none → s.hash x ≠ none ∨ (Adds .stream t ∧ x = key) := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  show ∃ key, ∀ x, GameCount.CellIn .stream x → p.2.hash x ≠ none → s.hash x ≠ none ∨ (Adds .stream t ∧ x = key)
  have hlocal : ∀ (u : (LocalSpec C).Domain) (p' : (LocalSpec C).Range u × KeyJointState C),
      (InClass .stream u → Adds .stream t) → p' ∈ support ((onJointHash (localAnswer prims u)).run s) →
        ∃ key, ∀ x, GameCount.CellIn .stream x → p'.2.hash x ≠ none → s.hash x ≠ none ∨ (Adds .stream t ∧ x = key) :=
      fun u p hu hp' => by
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    obtain ⟨key, hkey⟩ := FirstCounts.localAnswer_cells prims .stream u s.hash z hz
    exact ⟨key, fun x hx hzx => (hkey x hx hzx).imp_right fun h => ⟨hu h.1, h.2⟩⟩
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · exact hlocal (.inl u) p id (by rw [← jointLocal_false]; exact hp)
  · exact hlocal (.inr (.inl q)) p id (by rw [← jointLocal_false]; exact hp)
  · exact hlocal (.inr (.inr x)) p id (by rw [← jointLocal_false]; exact hp)
  · have hp' : p ∈ support ((onJointHash (programAnswer (q, v))).run s) := by
      rw [← jointProgram_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    exact ⟨q, fun x _ hx => (FirstCounts.programAnswer_cells (q, v) s.hash z hz x hx).imp_right fun h => ⟨trivial, h⟩⟩
  · exact hlocal (.inl u) p id (by rw [← jointLocal_false]; exact hp)
  · exact hlocal (.inr (.inl q)) p id (by rw [← jointLocal_false]; exact hp)
  · by_cases hh : Hidden D x.1
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = (do
          let h ← jointHidden false (x.1, x.2.1)
          pure (prims.aes.eval (truncateHash h) x.2.2)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
      rw [hc] at hp
      simp only [StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      obtain ⟨w, hw, rfl⟩ := hp
      refine ⟨.copy [], fun y _ hy => Or.inl ?_⟩
      rwa [← jointHidden_hash (x.1, x.2.1) s w hw]
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = jointLocal prims false (.inr (.inr x)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
      rw [hc] at hp
      exact hlocal (.inr (.inr x)) p id (by rw [← jointLocal_false]; exact hp)

/-- One call of the ideal joint world keeps the stream cells within one more cell for a call of
`Adds .stream`. -/
theorem jointKeyWorld_within (t : (WorldSpec C).Domain) (s : KeyJointState C) (k : ℕ)
    (hs : Within .stream s.hash k) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), Within .stream r.2.hash (k + if Adds .stream t then 1 else 0) := by
  intro r hr
  obtain ⟨key, hkey⟩ := jointKeyWorld_cells prims D t s r hr
  obtain ⟨cells, hcard, hcover⟩ := hs
  split_ifs with ht
  · refine ⟨insert key cells, (Finset.card_insert_le _ _).trans (by omega), fun x hx hzx => ?_⟩
    rcases hkey x hx hzx with h | ⟨_, rfl⟩
    · exact Finset.mem_insert_of_mem (hcover x hx h)
    · exact Finset.mem_insert_self _ _
  · refine ⟨cells, by omega, fun x hx hzx => ?_⟩
    rcases hkey x hx hzx with h | ⟨h, _⟩
    · exact hcover x hx h
    · exact absurd h ht

/-- A computation of the world with at most `n` calls of `Adds .stream` adds at most `n` stream cells
in the ideal joint world. -/
theorem simulateQ_jointWithin {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ n, IsQueryBoundP oa (Adds .stream) n → ∀ s k, Within .stream s.hash k →
      ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) oa).run s), Within .stream r.2.hash (k + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ s k hs r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact hs.mono (Nat.le_add_right _ _)
  | query_bind t f ih =>
    intro n hn s k hs r hr
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨y, hy, hr⟩ := hr
    refine (ih y.1 _ (hn.2 y.1) y.2 _ (jointKeyWorld_within prims D t s k hs y hy) r hr).mono ?_
    split_ifs with ht
    · have := hn.1.resolve_left (not_not.2 ht)
      omega
    · omega

/-- The stream cells of a cache within `k` inputs are at most `k`. -/
theorem streamCells_card_le (cache : HashCache C) (k : ℕ) (h : Within .stream cache k) :
    (UsedHit.streamCells cache).card ≤ k := by
  obtain ⟨cells, hcard, hcover⟩ := h
  refine le_trans ?_ hcard
  refine Finset.card_le_card_of_injOn (fun key => Query.streamKey key) (fun key hkey => ?_) (fun a _ b _ hab => ?_)
  · exact hcover _ rfl (by simpa [UsedHit.streamCells] using hkey)
  · exact Query.streamKey.inj hab

end CellsWorld

/-! ## The walk of the stream cells through the game -/

section CellsMoves

variable {C : Committee} (prims : Primitives) (D : C.Coalition) (runLimit : ℕ) (cost : Tree → ℕ)

open FirstCounts (Within Adds remaining)

/-- The potential of the walk. The stream cells lie within `k₀` inputs, and `k₀` with the cost of the
runs that remain is at most `k`. -/
def CellPot {σ : Type} (k : ℕ) (s : RealState C σ) (w : KeyJointState C) : Prop :=
  ∃ k₀, Within .stream w.hash k₀ ∧ k₀ + remaining runLimit cost s.runs ≤ k

/-- A computation of the game that moves the potential `CellPot k` to `CellPot (k + n)` in the ideal
joint world. -/
def JMoves {σ α : Type} (n : ℕ) (m : RealM C σ α) : Prop :=
  ∀ k s w, CellPot runLimit cost k s w →
    ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) (m.run s)).run w), CellPot runLimit cost (k + n) z.1.2 z.2

/-- A computation of the signing phase that moves the potential by `n` from each state of the signing
game. -/
def JMovesT {σ α : Type} (n : ℕ) (m : StateT (TsigState C) (RealM C σ) α) : Prop :=
  ∀ t, JMoves prims D runLimit cost n (m.run t)

variable {prims D runLimit cost}

theorem cellPot_mono {σ : Type} {k k' : ℕ} {s : RealState C σ} {w : KeyJointState C} (h : CellPot runLimit cost k s w)
    (hk : k ≤ k') : CellPot runLimit cost k' s w := by
  obtain ⟨k₀, hw, hle⟩ := h
  exact ⟨k₀, hw, by omega⟩

theorem jmoves_mono {σ α : Type} {n n' : ℕ} {m : RealM C σ α} (h : JMoves prims D runLimit cost n m) (hn : n ≤ n') :
    JMoves prims D runLimit cost n' m := fun k s w hs z hz =>
  cellPot_mono (h k s w hs z hz) (by omega)

theorem jmoves_pure {σ α : Type} (a : α) : JMoves prims D runLimit cost 0 (pure a : RealM C σ α) := by
  intro k s w hs z hz
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hs

theorem jmoves_bind {σ α β : Type} {n l : ℕ} {x : RealM C σ α} {f : α → RealM C σ β}
    (hx : JMoves prims D runLimit cost n x) (hf : ∀ a, JMoves prims D runLimit cost l (f a)) :
    JMoves prims D runLimit cost (n + l) (x >>= f) := by
  intro k s w hs z hz
  simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  have := hf y.1.1 (k + n) y.1.2 y.2 (hx k s w hs y hy) z hz
  rwa [Nat.add_assoc] at this

theorem jmoves_get_bind {σ β : Type} {n : ℕ} {f : RealState C σ → RealM C σ β}
    (hf : ∀ s, JMoves prims D runLimit cost n (f s)) : JMoves prims D runLimit cost n (get >>= f) := by
  intro k s w hs z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact hf s k s w hs z hz

theorem jmoves_lift {σ α : Type} {n : ℕ} {oa : OracleComp (WorldSpec C) α} (h : IsQueryBoundP oa (Adds .stream) n) :
    JMoves prims D runLimit cost n (StateT.lift oa : RealM C σ α) := by
  intro k s w hs z hz
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, mem_support_bind_iff,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨k₀, hw, hle⟩ := hs
  exact ⟨k₀ + n, simulateQ_jointWithin prims D oa n h w k₀ hw y hy, by dsimp only; omega⟩

theorem jmoves_modify {σ : Type} (f : RealState C σ → RealState C σ) (hf : ∀ s, (f s).runs = s.runs) :
    JMoves prims D runLimit cost 0 (modify f : RealM C σ Unit) := by
  intro k s w hs z hz
  simp only [StateT.run_modify, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨k₀, hw, hle⟩ := hs
  exact ⟨k₀, hw, by simpa only [hf, Nat.add_zero] using hle⟩

theorem jmoves_map {σ α β : Type} {n : ℕ} {x : RealM C σ α} (g : α → β) (hx : JMoves prims D runLimit cost n x) :
    JMoves prims D runLimit cost n (g <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact jmoves_mono (jmoves_bind hx fun _ => jmoves_pure _) (by omega)

theorem jmoves_get {σ : Type} : JMoves prims D runLimit cost 0 (get : RealM C σ _) := by
  have h := jmoves_get_bind (prims := prims) (D := D) (runLimit := runLimit) (cost := cost)
    (f := fun s : RealState C σ => (pure s : RealM C σ _)) fun _ => jmoves_pure _
  rwa [bind_pure] at h

theorem jmovesT_lift {σ α : Type} {n : ℕ} {x : RealM C σ α} (hx : JMoves prims D runLimit cost n x) :
    JMovesT prims D runLimit cost n (StateT.lift x : StateT (TsigState C) (RealM C σ) α) := by
  intro t
  rw [StateT.run_lift]
  exact jmoves_mono (jmoves_bind hx fun _ => jmoves_pure _) (by omega)

theorem jmovesT_simulateQ {σ ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT (TsigState C) (RealM C σ)))
    (p : ι → Prop) (h : ∀ q, JMovesT prims D runLimit cost (if p q then 1 else 0) (impl q)) {α : Type}
    (oa : OracleComp spec α) : ∀ n, IsQueryBoundP oa p n → JMovesT prims D runLimit cost n (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ t
    rw [simulateQ_pure, StateT.run_pure]
    exact jmoves_mono (jmoves_pure _) (Nat.zero_le _)
  | query_bind q k ih =>
    intro n hn t
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    refine jmoves_mono (jmoves_bind (h q t) fun y => ih y.1 _ (hn.2 y.1) y.2) ?_
    split_ifs with hq
    · have := hn.1.resolve_left (not_not.2 hq)
      omega
    · omega

end CellsMoves

/-! ## The stream cells of the honest operators on the network -/

section CellsNet

variable {C : Committee} {E : Type} (prims : Primitives) (D : C.Coalition)

open FirstCounts (Within Adds)

/-- The cell of class `stream` that a local call of an operator can add. -/
def honestCell : (LocalSpec C).Domain → Query C
  | .inl _ => .copy []
  | .inr (.inl q) => q
  | .inr (.inr x) => .streamKey x.2.1

/-- The stream cells of an operator after a call. -/
def cellAdd : (PartySpec C E RealSpec).Domain → Finset (Query C) → Finset (Query C)
  | .inl (.inl t), Q => if InClass .stream t then insert (honestCell t) Q else Q
  | _, Q => Q

/-- Each path of `oa` keeps the stream cells of its calls, with the cells `Q` at the start, in a set of
at most `b` cells. -/
def KeyThen (b : ℕ) {α : Type} (oa : OracleComp (PartySpec C E RealSpec) α) : Finset (Query C) → Prop :=
  OracleComp.construct (C := fun _ => Finset (Query C) → Prop) (fun _ Q => Q.card ≤ b)
    (fun t _ ih Q => Q.card ≤ b ∧ ∀ u, ih u (cellAdd t Q)) oa

theorem keyThen_query_bind (b : ℕ) {α : Type} (t : (PartySpec C E RealSpec).Domain)
    (k : (PartySpec C E RealSpec).Range t → OracleComp (PartySpec C E RealSpec) α) (Q : Finset (Query C)) :
    KeyThen b (liftM (OracleSpec.query t) >>= k) Q ↔ Q.card ≤ b ∧ ∀ u, KeyThen b (k u) (cellAdd t Q) := Iff.rfl

theorem keyThen_card (b : ℕ) {α : Type} (oa : OracleComp (PartySpec C E RealSpec) α) (Q : Finset (Query C))
    (h : KeyThen b oa Q) : Q.card ≤ b := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact h
  | query_bind t k _ => exact ((keyThen_query_bind b t k Q).1 h).1

theorem subset_cellAdd (t : (PartySpec C E RealSpec).Domain) (Q : Finset (Query C)) : Q ⊆ cellAdd t Q := by
  rcases t with (t | _) | _
  · show Q ⊆ (if InClass .stream t then insert (honestCell t) Q else Q)
    split_ifs
    · exact Finset.subset_insert _ _
    · exact subset_rfl
  · exact subset_rfl
  · exact subset_rfl

/-- An honest local call of the ideal joint world adds at most its own stream cell. -/
theorem jointKeyWorld_honestCell (q : (LocalSpec C).Domain) (s : KeyJointState C) :
    ∀ r ∈ support ((jointKeyWorld prims D false (.inr q)).run s), ∀ x, GameCount.CellIn .stream x →
      r.2.hash x ≠ none → s.hash x ≠ none ∨ (InClass .stream q ∧ x = honestCell q) := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  show ∀ x, GameCount.CellIn .stream x → p.2.hash x ≠ none → s.hash x ≠ none ∨ (InClass .stream q ∧ x = honestCell q)
  rcases q with u | q | x
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inl u))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    obtain ⟨key, hkey⟩ := FirstCounts.localAnswer_cells prims .stream (.inl u) s.hash z hz
    intro x hx hzx
    exact (hkey x hx hzx).imp_right fun h => h.1.elim
  · have hp' : p ∈ support ((onJointHash (hashAnswer prims q)).run s) := by
      rw [← jointHash_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    intro x hx hzx
    rcases FirstCounts.hashAnswer_cells prims q s.hash z hz x hzx with h | rfl
    · exact Or.inl h
    · refine Or.inr ⟨?_, rfl⟩
      cases x <;> simp_all [GameCount.CellIn, InClass]
  · by_cases hh : Hidden D x.1
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = (do
          let h ← jointHidden false (x.1, x.2.1)
          pure (prims.aes.eval (truncateHash h) x.2.2)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
      rw [hc] at hp
      simp only [StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      obtain ⟨w, hw, rfl⟩ := hp
      intro y _ hy
      left
      rwa [← jointHidden_hash (x.1, x.2.1) s w hw]
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = jointLocal prims false (.inr (.inr x)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
      rw [hc] at hp
      have hp' : p ∈ support ((onJointHash (localAnswer prims (.inr (.inr x)))).run s) := by
        rw [← jointLocal_false]; exact hp
      obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
      change z ∈ support ((prgAnswer prims x).run s.hash) at hz
      unfold prgAnswer at hz
      rw [StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨p', hp'', hz⟩ := hz
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      intro y _ hy
      rcases FirstCounts.hashAnswer_cells prims _ s.hash p' hp'' y hy with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, rfl⟩

/-- The stream cells of the world lie in `H`. -/
def CellsIn (H : Finset (Query C)) (w : KeyJointState C) : Prop :=
  ∀ x, GameCount.CellIn .stream x → w.hash x ≠ none → x ∈ H

/-- A computation of the world with at most `n` calls of `Adds .stream` adds at most `n` cells to a set
that holds the stream cells. -/
theorem simulateQ_cellsIn {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ n, IsQueryBoundP oa (Adds .stream) n → ∀ H w, CellsIn H w →
      ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) oa).run w),
        ∃ H', H ⊆ H' ∧ H'.card ≤ H.card + n ∧ CellsIn H' z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ H w hw z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨H, subset_rfl, by omega, hw⟩
  | query_bind t f ih =>
    intro n hn H w hw z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨key, hkey⟩ := jointKeyWorld_cells prims D t w y hy
    by_cases ht : Adds .stream t
    · have hn1 := hn.1.resolve_left (not_not.2 ht)
      have hk := hn.2 y.1
      simp only [ht, ↓reduceIte] at hk
      obtain ⟨H', hsub, hcard, hH'⟩ := ih y.1 _ hk (insert key H) y.2 (fun x hx hyx =>
        (hkey x hx hyx).elim (fun h => Finset.mem_insert_of_mem (hw x hx h)) fun h => h.2 ▸ Finset.mem_insert_self _ _) z hz
      refine ⟨H', (Finset.subset_insert _ _).trans hsub, ?_, hH'⟩
      have := Finset.card_insert_le key H
      omega
    · have hk := hn.2 y.1
      simp only [ht, ↓reduceIte] at hk
      exact ih y.1 _ hk H y.2 (fun x hx hyx =>
        (hkey x hx hyx).elim (fun h => hw x hx h) fun h => absurd h.1 ht) z hz

/-- The continuation of a stopped program keeps its stream cells in a set of at most `b` cells. -/
def StepKey (b : ℕ) (Q : Finset (Query C)) {α : Type} : Step C E RealSpec α → Prop
  | .wait _ resume => ∀ inbox, KeyThen b (resume inbox) Q
  | _ => True

/-- The local steps of an honest operator add only its own stream cells. -/
theorem advance_cells (b : ℕ) (H : Finset (Query C)) {α : Type} (oa : OracleComp (PartySpec C E RealSpec) (Option α)) :
    ∀ Q w, KeyThen b oa Q → (∀ x, GameCount.CellIn .stream x → w.hash x ≠ none → x ∈ H ∨ x ∈ Q) →
      ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) (free (advance oa))).run w),
        ∃ Q', Q ⊆ Q' ∧ Q'.card ≤ b ∧ (∀ x, GameCount.CellIn .stream x → z.2.hash x ≠ none → x ∈ H ∨ x ∈ Q') ∧
          StepKey b Q' z.1 := by
  induction oa using OracleComp.inductionOn with
  | pure out =>
    intro Q w h hw z hz
    simp only [advance_pure, free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨Q, subset_rfl, keyThen_card b _ Q h, hw, trivial⟩
  | query_bind t k ih =>
    intro Q w h hw z hz
    rw [keyThen_query_bind] at h
    rcases t with (q | outbox) | input
    · change z ∈ support ((simulateQ (jointKeyWorld prims D false) (free (OracleComp.lift
        (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)))).run w) at hz
      simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rw [simulateQ_HasQuery_query] at hy
      have hy' : ∀ x, GameCount.CellIn .stream x → y.2.hash x ≠ none → x ∈ H ∨ x ∈ cellAdd (E := E) (.inl (.inl q)) Q := by
        intro x hx hyx
        rcases jointKeyWorld_honestCell prims D q w y hy x hx hyx with h' | ⟨hq, rfl⟩
        · exact (hw x hx h').imp_right fun h'' => subset_cellAdd _ Q h''
        · right
          simp only [cellAdd, hq, ↓reduceIte]
          exact Finset.mem_insert_self _ _
      obtain ⟨Q', hQ', hcard, hz', hstep⟩ := ih y.1 _ y.2 (h.2 y.1) hy' z hz
      exact ⟨Q', (subset_cellAdd _ Q).trans hQ', hcard, hz', hstep⟩
    · change z ∈ support ((simulateQ (jointKeyWorld prims D false) (free (pure (Step.wait outbox k)))).run w) at hz
      simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Q, subset_rfl, h.1, hw, fun inbox => h.2 inbox⟩
    · exact input.elim

/-- A sequence of computations keeps an invariant on the world and a family `Qs`, when each computation
keeps it with a new member at its index. The member at an index is the start member until the
computation of that index. -/
theorem sequenceFin_inv {β X : Type} : ∀ {m : ℕ} (I : (Fin m → X) → KeyJointState C → Prop) (P : Fin m → β → X → Prop)
    (f : Fin m → OracleComp (WorldSpec C) β) (Q₀ : Fin m → X),
    (∀ j Qs w, I Qs w → Qs j = Q₀ j → ∀ y ∈ support ((simulateQ (jointKeyWorld prims D false) (f j)).run w),
      ∃ x, I (Function.update Qs j x) y.2 ∧ P j y.1 x) →
    ∀ w, I Q₀ w → ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) (OverPermutation.sequenceFin f)).run w),
      ∃ Qs', I Qs' z.2 ∧ ∀ j, P j (z.1 j) (Qs' j)
  | 0, I, P, f, Q₀, _, w, hw, z, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨Q₀, hw, fun j => j.elim0⟩
  | m + 1, I, P, f, Q₀, hf, w, hw, z, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, v, hv, rfl⟩ := hz
    obtain ⟨x₀, hI, hP⟩ := hf 0 Q₀ w hw rfl y hy
    have e : Function.update Q₀ 0 x₀ = Fin.cons (α := fun _ => X) x₀ (Fin.tail Q₀) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp
      · simp [Fin.tail]
    rw [e] at hI
    obtain ⟨Qt, hQt, hPt⟩ := sequenceFin_inv (fun Qt w => I (Fin.cons (α := fun _ => X) x₀ Qt) w)
      (fun i => P i.succ) (fun i => f i.succ) (Fin.tail Q₀) (fun i Qt w' hw' hi y' hy' => by
        obtain ⟨x, hx, hPx⟩ := hf i.succ _ w' hw' (by simpa [Fin.tail] using hi) y' hy'
        refine ⟨x, ?_, hPx⟩
        rwa [Fin.cons_update]) y.2 hI v hv
    refine ⟨Fin.cons (α := fun _ => X) x₀ Qt, hQt, fun j => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hP
    · simpa using hPt i

/-- The stream cells lie in `H`. The cells of each honest operator lie in `H` and are at most `b`, and `H`
has at most `c` cells beyond the cells of the honest operators. -/
def NetCells (b c : ℕ) (Qs : C.Party → Finset (Query C)) (w : KeyJointState C) : Prop :=
  ∃ H, CellsIn H w ∧ H.card ≤ c + ∑ j ∈ Finset.univ.filter (· ∉ D.1), (Qs j).card ∧
    ∀ j, j ∉ D.1 → Qs j ⊆ H ∧ (Qs j).card ≤ b

theorem netCells_mono {b c c' : ℕ} {Qs : C.Party → Finset (Query C)} {w : KeyJointState C}
    (h : NetCells D b c Qs w) (hc : c ≤ c') : NetCells D b c' Qs w := by
  obtain ⟨H, hH, hcard, hQ⟩ := h
  exact ⟨H, hH, by omega, hQ⟩

/-- An honest operator that adds its own cells keeps `NetCells`. -/
theorem netCells_update {b c : ℕ} {Qs : C.Party → Finset (Query C)} {w' : KeyJointState C} (j : C.Party)
    (hj : j ∉ D.1) (Q' : Finset (Query C)) (H : Finset (Query C))
    (hHcard : H.card ≤ c + ∑ j ∈ Finset.univ.filter (· ∉ D.1), (Qs j).card)
    (hQ : ∀ j, j ∉ D.1 → Qs j ⊆ H ∧ (Qs j).card ≤ b) (hQ' : Qs j ⊆ Q') (hcard : Q'.card ≤ b)
    (hcover : ∀ x, GameCount.CellIn .stream x → w'.hash x ≠ none → x ∈ H ∨ x ∈ Q') :
    NetCells D b c (Function.update Qs j Q') w' := by
  have hmem : j ∈ Finset.univ.filter (· ∉ D.1) := by simpa using hj
  have hsum : ∑ i ∈ Finset.univ.filter (· ∉ D.1), (Function.update Qs j Q' i).card =
      Q'.card + ∑ i ∈ (Finset.univ.filter (· ∉ D.1)).erase j, (Qs i).card := by
    rw [← Finset.add_sum_erase _ _ hmem, Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hsum' := Finset.add_sum_erase (Finset.univ.filter (· ∉ D.1)) (fun i => (Qs i).card) hmem
  have hunion : (H ∪ Q').card ≤ H.card + Q'.card - (Qs j).card := by
    have h1 := Finset.card_union_add_card_inter H Q'
    have h2 : (Qs j).card ≤ (H ∩ Q').card :=
      Finset.card_le_card fun x hx => Finset.mem_inter.2 ⟨(hQ j hj).1 hx, hQ' hx⟩
    omega
  refine ⟨H ∪ Q', fun x hx hwx => ?_, ?_, fun i hi => ?_⟩
  · rcases hcover x hx hwx with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  · have h3 := Finset.card_le_card hQ'
    rw [hsum]
    omega
  · by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact ⟨Finset.subset_union_right, hcard⟩
    · rw [Function.update_of_ne hij]
      exact ⟨(hQ i hi).1.trans Finset.subset_union_left, (hQ i hi).2⟩

/-- One round adds at most `step` cells of the adversary, and the honest operators add only their own
cells. -/
theorem stepRound_cells {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) (b c step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) (InClass .stream) step) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (Qs : C.Party → Finset (Query C)) (w : KeyJointState C)
    (hw : NetCells D b c Qs w) (hsteps : ∀ j, j ∉ D.1 → StepKey b (Qs j) (steps j))
    (y : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) × KeyJointState C)
    (hy : y ∈ support ((simulateQ (jointKeyWorld prims D false) (stepRound worldRoles D A noFunctionality st steps)).run w)) :
    ∃ Qs', NetCells D b (c + step) Qs' y.2 ∧ ∀ j, j ∉ D.1 → StepKey b (Qs' j) (y.1.2.1 j) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRound at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, ha, v, hv, rfl⟩ := hy
  have hadv : IsQueryBoundP (worldRoles.adversary (A.round st fun c i =>
      if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none)) (Adds .stream) (step + 0) :=
    FirstCounts.isQueryBoundP_add (fun _ => FirstCounts.adds_or .stream) _ _ _
      (FirstCounts.ownAdds_adversary .stream _ step (hround _ _)) (DigestBudgets.honestIn_adversary .stream _)
  obtain ⟨H, hH, hHcard, hQ⟩ := hw
  obtain ⟨H', hHH', hH'card, hH'⟩ := simulateQ_cellsIn prims D _ _ hadv H w hH a ha
  have ha' : NetCells D b (c + step) Qs a.2 :=
    ⟨H', hH', by omega, fun j hj => ⟨(hQ j hj).1.trans hHH', (hQ j hj).2⟩⟩
  refine sequenceFin_inv prims D (NetCells D b (c + step)) (fun j next Q => j ∉ D.1 → StepKey b Q next) _ Qs
    (fun j Qs' w' hw' hQs' u hu => ?_) a.2 ha' v hv
  have hkeep : ∀ (next : Step C E RealSpec α), (j ∉ D.1 → StepKey b (Qs' j) next) → u.2 = w' →
      ∃ x, NetCells D b (c + step) (Function.update Qs' j x) u.2 ∧ (j ∉ D.1 → StepKey b x next) :=
    fun next hnext hu2 => ⟨Qs' j, by rw [Function.update_eq_self, hu2]; exact hw', hnext⟩
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact hkeep _ (fun _ => trivial) rfl
  · by_cases hj : j ∈ D.1
    · simp only [hsj, hj, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact hkeep _ (fun h => absurd hj h) rfl
    · simp only [hsj, hj, ↓reduceIte] at hu
      have hres := hsteps j hj
      rw [hsj] at hres
      obtain ⟨H₁, hH₁, hH₁card, hQ₁⟩ := hw'
      obtain ⟨Q', hQ', hcard, hcover, hstep⟩ := advance_cells prims D b H₁ _ (Qs' j) w'
        (hQs' ▸ hres _) (fun x hx hwx => Or.inl (hH₁ x hx hwx)) u hu
      exact ⟨Q', netCells_update D j hj Q' H₁ hH₁card hQ₁ hQ' hcard hcover, fun _ => hstep⟩
  · exact input.elim

/-- The rounds add at most `step` cells of the adversary in each round. -/
theorem executeRounds_cells {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) (b step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) (InClass .stream) step) (fuel : ℕ) :
    ∀ (c : ℕ) (st : A.State) (steps : C.Party → Step C E RealSpec α) (Qs : C.Party → Finset (Query C))
      (w : KeyJointState C), NetCells D b c Qs w → (∀ j, j ∉ D.1 → StepKey b (Qs j) (steps j)) →
        ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false)
          (executeRounds worldRoles D A noFunctionality fuel st steps)).run w),
          ∃ Qs', NetCells D b (c + fuel * step) Qs' z.2 := by
  induction fuel with
  | zero =>
    intro c st steps Qs w hw _ z hz
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨Qs, netCells_mono D hw (by omega)⟩
  | succ fuel ih =>
    intro c st steps Qs w hw hsteps z hz
    unfold executeRounds at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Qs, netCells_mono D hw (by omega)⟩
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      obtain ⟨Qs', hQs', hsteps'⟩ := stepRound_cells prims D A b c step hround st steps Qs w hw hsteps y hy
      obtain ⟨Qs'', h⟩ := ih (c + step) y.1.1 y.1.2.1 Qs' y.2 hQs' hsteps' z hz
      exact ⟨Qs'', netCells_mono D h (by rw [Nat.succ_mul]; omega)⟩

/-- A phase on the network adds at most `step` cells of the adversary in each round and `b` cells of
each honest operator, when each honest program keeps its cells within `b`. -/
theorem executePhase_cells {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) (b step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) (InClass .stream) step) (fuel : ℕ) (st : A.State)
    (program : C.Party → PartyM C E RealSpec α) (hp : ∀ i, i ∉ D.1 → KeyThen b (program i).run ∅)
    (w : KeyJointState C) (k : ℕ) (hw : Within .stream w.hash k) :
    ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false)
      (executePhase worldRoles D A noFunctionality fuel st program)).run w),
      Within .stream z.2.hash (k + fuel * step + C.n * b) := by
  intro z hz
  unfold executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startSteps at hy
  obtain ⟨H, hcard, hH⟩ := hw
  have h0 : NetCells D b k (fun _ => ∅) w :=
    ⟨H, fun x hx hwx => hH x hx hwx, by simp [hcard], fun _ _ => ⟨Finset.empty_subset _, by simp⟩⟩
  have hf : ∀ (j : C.Party) (Qs : C.Party → Finset (Query C)) (w' : KeyJointState C), NetCells D b k Qs w' →
      Qs j = (fun _ => ∅) j → ∀ u ∈ support ((simulateQ (jointKeyWorld prims D false)
        (if j ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program j).run))).run w'),
        ∃ x, NetCells D b k (Function.update Qs j x) u.2 ∧ (j ∉ D.1 → StepKey b x u.1) := by
    intro j Qs w' hw' hQs' u hu
    by_cases hj : j ∈ D.1
    · simp only [hj, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨Qs j, by rw [Function.update_eq_self]; exact hw', fun h => absurd hj h⟩
    · simp only [hj, ↓reduceIte] at hu
      obtain ⟨H₁, hH₁, hH₁card, hQ₁⟩ := hw'
      obtain ⟨Q', hQ', hcard', hcover, hstep⟩ := advance_cells prims D b H₁ _ (Qs j) w'
        (hQs' ▸ hp j hj) (fun x hx hwx => Or.inl (hH₁ x hx hwx)) u hu
      exact ⟨Q', netCells_update D j hj Q' H₁ hH₁card hQ₁ hQ' hcard' hcover, fun _ => hstep⟩
  obtain ⟨Qs, hQs, hsteps⟩ := sequenceFin_inv prims D (NetCells D b k) (fun j next Q => j ∉ D.1 → StepKey b Q next)
    _ (fun _ => ∅) hf w h0 y hy
  obtain ⟨Qs', H', hH', hH'card, hQ'⟩ := executeRounds_cells prims D A b step hround fuel k st y.1 Qs y.2 hQs hsteps z hz
  refine ⟨H', ?_, hH'⟩
  have hsum : ∑ j ∈ Finset.univ.filter (· ∉ D.1), (Qs' j).card ≤ C.n * b := by
    refine (Finset.sum_le_card_nsmul _ _ b fun j hj => (hQ' j (by simpa using hj)).2).trans ?_
    rw [smul_eq_mul]
    refine Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans ?_)
    simp
  omega

end CellsNet


/-! ## The stream calls of a ceremony after its setup

The lemmas of the body are the case `LocalK` of `Draws.runJobs_pstate`. `RoK` constrains each name and
the calls of `H` in class `stream`. -/

namespace KeyCells

section Body

open DigestBudgets (ClassBound StateBound PartyIn RoIn)

variable {C : Committee} {E : Type}

/-- A call of `H` or `PRG` in class `stream` that is not a call of `PRG` with a key that `A` allows. -/
def RoK (A : KeyName C → HashOutput → Prop) : (RoSpec C).Domain → Prop
  | .inl q => InClass .stream (.inr (.inl q))
  | .inr x => ¬ A x.1 x.2.1

/-- A local call that is a call of `RoK A`. -/
def LocalK (A : KeyName C → HashOutput → Prop) : (LocalSpec C).Domain → Prop
  | .inr t => RoK A t
  | _ => False

/-- An operator program whose calls in class `stream` are calls of `PRG` with keys that `A` allows. -/
abbrev KOk {α : Type} (A : KeyName C → HashOutput → Prop) (p : PartyM C E RealSpec α) : Prop :=
  SetupBudgets.PBound (LocalK A) p 0

/-- A program on a state with `KOk A` from each state. -/
abbrev KOkS {σ α : Type} (A : KeyName C → HashOutput → Prop) (p : StateT σ (PartyM C E RealSpec) α) : Prop :=
  SetupBudgets.PState (LocalK A) p 0

theorem localK_stream {S : KeyName C → HashOutput → Prop} (t : (LocalSpec C).Domain) (h : LocalK S t) :
    InClass .stream t := by
  rcases t with _ | _ | _
  · exact h.elim
  · exact h
  · rfl

theorem KOk.of_class {α : Type} {S : KeyName C → HashOutput → Prop} {p : PartyM C E RealSpec α}
    (h : ClassBound (E := E) .stream p 0) : KOk S p :=
  SetupBudgets.PBound.of_class localK_stream h

theorem KOk.bind {α β : Type} {S : KeyName C → HashOutput → Prop} {p : PartyM C E RealSpec α}
    {f : α → PartyM C E RealSpec β} (h : KOk S p) (hf : ∀ a, KOk S (f a)) : KOk S (p >>= f) :=
  SetupBudgets.PBound.bind h hf

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

theorem runJobs_k (mode : ReshareMode) (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    KOkS (NameKey ctx.self ctx.prss) (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) :=
  Draws.runJobs_pstate K ctx localK_stream (fun _ h h' => h' h) mode jobs inputs

end Body

section Count

variable {C : Committee} {E : Type}

/-- `KeyThen` with an end condition `post` on the value and the cells. -/
def KeyThenP (b : ℕ) {α : Type} (post : α → Finset (Query C) → Prop) (oa : OracleComp (PartySpec C E RealSpec) α) :
    Finset (Query C) → Prop :=
  OracleComp.construct (C := fun _ => Finset (Query C) → Prop) post
    (fun t _ ih Q => Q.card ≤ b ∧ ∀ u, ih u (cellAdd t Q)) oa

theorem keyThenP_query_bind (b : ℕ) {α : Type} (post : α → Finset (Query C) → Prop) (t : (PartySpec C E RealSpec).Domain)
    (k : (PartySpec C E RealSpec).Range t → OracleComp (PartySpec C E RealSpec) α) (Q : Finset (Query C)) :
    KeyThenP b post (liftM (OracleSpec.query t) >>= k) Q ↔ Q.card ≤ b ∧ ∀ u, KeyThenP b post (k u) (cellAdd t Q) :=
  Iff.rfl

theorem keyThenP_bind (b : ℕ) {α β : Type} (post : β → Finset (Query C) → Prop)
    (oa : OracleComp (PartySpec C E RealSpec) α) (f : α → OracleComp (PartySpec C E RealSpec) β) :
    ∀ Q, KeyThenP b post (oa >>= f) Q ↔ KeyThenP b (fun a Q' => KeyThenP b post (f a) Q') oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro Q; rw [pure_bind]; exact Iff.rfl
  | query_bind t k ih =>
    intro Q
    rw [bind_assoc, keyThenP_query_bind, keyThenP_query_bind]
    exact and_congr_right fun _ => forall_congr' fun u => ih u _

theorem KeyThenP.imp (b : ℕ) {α : Type} {post post' : α → Finset (Query C) → Prop}
    (hpost : ∀ a Q, post a Q → post' a Q) (oa : OracleComp (PartySpec C E RealSpec) α) :
    ∀ {Q}, KeyThenP b post oa Q → KeyThenP b post' oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun h => hpost a _ h
  | query_bind t k ih =>
    intro Q h
    rw [keyThenP_query_bind] at h ⊢
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

/-- A program whose calls in class `stream` are calls of `PRG` with keys of `A` keeps its cells within the
cells `Q₀` and the stream cells `K` of the keys of `A`. -/
theorem keyThenP_of_kOk (b : ℕ) {A : KeyName C → HashOutput → Prop} {α : Type}
    (oa : OracleComp (PartySpec C E RealSpec) α) (h : IsQueryBoundP oa (SetupBudgets.PartyP (LocalK A)) 0) (K Q₀ : Finset (Query C))
    (hK : ∀ N k, A N k → Query.streamKey k ∈ K) (hb : (Q₀ ∪ K).card ≤ b) (post : α → Finset (Query C) → Prop)
    (hpost : ∀ a Q', Q' ⊆ Q₀ ∪ K → post a Q') : ∀ Q, Q ⊆ Q₀ ∪ K → KeyThenP b post oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun Q hQ => hpost a Q hQ
  | query_bind t k ih =>
    intro Q hQ
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ SetupBudgets.PartyP (LocalK A) t := h.1.resolve_right (lt_irrefl 0)
    rw [keyThenP_query_bind]
    refine ⟨(Finset.card_le_card hQ).trans hb, fun u => ih u (by simpa only [ht, ite_false] using h.2 u) _ ?_⟩
    rcases t with (t | _) | _
    · show (if InClass .stream t then insert (honestCell t) Q else Q) ⊆ Q₀ ∪ K
      split_ifs with hc
      · refine Finset.insert_subset_iff.2 ⟨?_, hQ⟩
        rcases t with _ | q | x
        · exact hc.elim
        · exact absurd hc ht
        · exact Finset.mem_union_right _ (hK _ _ (not_not.1 ht))
      · exact hQ
    · exact hQ
    · exact hQ

/-- A program that adds at most `d` cells from each start with room for them. -/
def KP (b : ℕ) {α : Type} (p : PartyM C E RealSpec α) (d : ℕ) : Prop :=
  ∀ Q : Finset (Query C), Q.card + d ≤ b → KeyThenP b (fun _ Q' => Q'.card ≤ Q.card + d) p.run Q

theorem KP.mono {b : ℕ} {α : Type} {p : PartyM C E RealSpec α} {d d' : ℕ} (h : KP b p d) (hd : d ≤ d') : KP b p d' :=
  fun Q hQ => KeyThenP.imp b (fun _ Q' h' => by omega) _ (h Q (by omega))

theorem KP.of_kOk {b : ℕ} {A : KeyName C → HashOutput → Prop} {α : Type} {p : PartyM C E RealSpec α} (h : KOk A p)
    (K : Finset (Query C)) (hK : ∀ N k, A N k → Query.streamKey k ∈ K) : KP b p K.card := fun Q hQ =>
  keyThenP_of_kOk b _ h K Q hK ((Finset.card_union_le _ _).trans hQ) _
    (fun _ _ hQ' => (Finset.card_le_card hQ').trans (Finset.card_union_le _ _)) Q Finset.subset_union_left

theorem KP.of_class {b : ℕ} {α : Type} {p : PartyM C E RealSpec α} (h : ClassBound (E := E) .stream p 0) :
    KP b p 0 := by
  simpa using KP.of_kOk (b := b) (KOk.of_class (S := fun _ _ => False) h) ∅ fun _ _ h => h.elim

theorem KP.pure {b : ℕ} {α : Type} (a : α) (d : ℕ) : KP b (Pure.pure a : PartyM C E RealSpec α) d :=
  fun Q _ => show Q.card ≤ Q.card + d by omega

theorem KP.failure {b : ℕ} {α : Type} (d : ℕ) : KP b (failure : PartyM C E RealSpec α) d :=
  fun Q _ => show Q.card ≤ Q.card + d by omega

theorem KP.bind {b : ℕ} {α β : Type} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} {d₁ d₂ : ℕ}
    (hp : KP b p d₁) (hf : ∀ a, KP b (f a) d₂) : KP b (p >>= f) (d₁ + d₂) := by
  intro Q hQ
  rw [OptionT.run_bind]
  unfold Option.elimM
  rw [keyThenP_bind]
  refine KeyThenP.imp b (fun o Q' (h' : Q'.card ≤ Q.card + d₁) => ?_) _ (hp Q (by omega))
  rcases o with _ | a
  · show Q'.card ≤ Q.card + (d₁ + d₂)
    omega
  · exact KeyThenP.imp b (fun _ Q'' h'' => by omega) _ (hf a Q' (by omega))

theorem KP.map {b : ℕ} {α β : Type} {p : PartyM C E RealSpec α} (g : α → β) {d : ℕ} (hp : KP b p d) :
    KP b (g <$> p) d := by
  simpa using KP.bind hp fun a => KP.pure (b := b) (g a) 0

end Count

section Counters

variable {C : Committee} {E : Type}

open DigestBudgets (ClassBound StateBound)

/-- A program on the counters with `KOk A` from each state. -/
def KOkAt {α : Type} (A : KeyName C → HashOutput → Prop) (x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) :
    Prop :=
  ∀ s n, KOk A ((x.run s).run n)

/-- A program on the counters that adds at most `d` cells from each state. -/
def KS (b : ℕ) {α : Type} (x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) (d : ℕ) : Prop :=
  ∀ s n, KP b ((x.run s).run n) d

variable {A : KeyName C → HashOutput → Prop} {b : ℕ}

theorem KOkAt.bind {α β : Type} {x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α}
    {f : α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β} (hx : KOkAt A x) (hf : ∀ a, KOkAt A (f a)) :
    KOkAt A (x >>= f) := fun s n => by
  rw [StateT.run_bind, StateT.run_bind]
  exact KOk.bind (hx s n) fun q => hf q.1.1 q.1.2 q.2

theorem KOkAt.pure {α : Type} (a : α) :
    KOkAt A (Pure.pure a : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) := fun _ _ =>
  isQueryBoundP_pure _ _ _

theorem KOk.map {α β : Type} {p : PartyM C E RealSpec α} (g : α → β) (h : KOk A p) : KOk A (g <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact KOk.bind h fun _ => isQueryBoundP_pure _ _ _

theorem KOkAt.lift {α : Type} {y : PartyM C E RealSpec α} (h : KOk A y) :
    KOkAt A (StateT.lift (StateT.lift y) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) := fun s n => by
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map]
  exact KOk.map _ (KOk.map _ h)

theorem KOkAt.get : KOkAt A (get : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) (ℕ × ℕ)) := fun _ _ =>
  isQueryBoundP_pure _ _ _

theorem KOkAt.set (s' : ℕ × ℕ) : KOkAt A (set s' : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) PUnit) :=
  fun _ _ => isQueryBoundP_pure _ _ _

theorem KOkAt.mapM {α β : Type} (f : α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β)
    (hf : ∀ a, KOkAt A (f a)) : ∀ xs : List α, KOkAt A (xs.mapM f)
  | [] => by simpa using KOkAt.pure (A := A) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (KOkAt.mapM f hf xs).bind fun _ => KOkAt.pure _

theorem KS.mono {α : Type} {x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α} {d d' : ℕ} (h : KS b x d)
    (hd : d ≤ d') : KS b x d' := fun s n => (h s n).mono hd

theorem KS.bind {α β : Type} {x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α}
    {f : α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β} {d₁ d₂ d : ℕ} (hx : KS b x d₁)
    (hf : ∀ a, KS b (f a) d₂) (hd : d₁ + d₂ ≤ d) : KS b (x >>= f) d := fun s n => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (KP.bind (hx s n) fun q => hf q.1.1 q.1.2 q.2).mono hd

theorem KS.pure {α : Type} (a : α) (d : ℕ) :
    KS b (Pure.pure a : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) d := fun _ _ => KP.pure _ _

theorem KS.lift {α : Type} {y : PartyM C E RealSpec α} {d : ℕ} (h : KP b y d) :
    KS b (StateT.lift (StateT.lift y) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) d := fun s n => by
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map]
  exact KP.map _ (KP.map _ h)

theorem KS.liftGet : KS b (StateT.lift (get : StateT ℕ (PartyM C E RealSpec) ℕ) :
    StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) ℕ) 0 := fun s n => by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure]
  exact KP.pure _ _

theorem KS.liftSet (m : ℕ) : KS b (StateT.lift (set m : StateT ℕ (PartyM C E RealSpec) PUnit) :
    StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) PUnit) 0 := fun s n => by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
  exact KP.pure _ _

theorem KS.of_kOkAt {α : Type} {x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α} (h : KOkAt A x)
    (K : Finset (Query C)) (hK : ∀ N k, A N k → Query.streamKey k ∈ K) : KS b x K.card := fun s n =>
  KP.of_kOk (h s n) K hK

/-- The stream cells of the keys of operator `i` under the PRSS keys `prss`. -/
def keyCells (i : C.Party) (prss : PrssKeys C) : Finset (Query C) :=
  (Finset.univ.filter fun T : C.Term => i ∈ C.holders T).image (fun T => Query.streamKey (prss.term T)) ∪
    (Finset.univ.filter fun j : C.Party => j ≠ i).image fun j => Query.streamKey (prss.pair j)

theorem mem_keyCells (i : C.Party) (prss : PrssKeys C) (N : KeyName C) (k : HashOutput) (h : NameKey i prss N k) :
    Query.streamKey k ∈ keyCells i prss := by
  rcases h with ⟨T, hT, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨T, by simpa using hT, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, by simpa using hj, rfl⟩)

theorem card_keyCells (i : C.Party) (prss : PrssKeys C) : (keyCells i prss).card ≤ termCount C + C.n := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
    rw [Finset.card_univ, ThresholdLeanXmssSecurity.card_term C, termCount]
  · refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
    simp

end Counters

section Slots

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) {b : ℕ}

open DigestBudgets (ClassBound StateBound)

attribute [local instance] inhabitedField

/-- A slot ceremony adds at most the cells of the keys of its own setup. -/
theorem slotCeremony_ks (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C)
    (jobs : List Job) : KS b (slotCeremony K circuits settings D fresh i keys jobs) (termCount C + C.n) := by
  unfold slotCeremony
  refine KS.bind KS.liftGet (d₂ := termCount C + C.n) (fun c => ?_) (by omega)
  refine KS.bind (KS.liftSet _) (d₂ := termCount C + C.n) (fun _ => ?_) (by omega)
  refine KS.bind (KS.lift (KP.of_class (DigestBudgets.prssSetup_bound (c := .stream) nofun i)))
    (d₂ := termCount C + C.n) (fun prss => ?_) (by omega)
  refine (KS.of_kOkAt (A := NameKey i (((fresh c).map (prssOverlay D i prss)).getD prss)) ?_ _
    (mem_keyCells i _)).mono (card_keyCells i _)
  unfold batched
  refine KOkAt.bind (KOkAt.mapM _ (fun js => ?_) _) fun _ => KOkAt.pure _
  refine KOkAt.bind KOkAt.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine KOkAt.bind (KOkAt.lift (KOk.of_class ((ClassBound.mapM _ 0
    (fun job => DigestBudgets.inputShares_bound (c := .stream) _ nofun job) _).mono (by simp)))) fun inputs => ?_
  refine KOkAt.bind (KOkAt.lift (runJobs_k (ctx := ⟨i, keys, ((fresh c).map (prssOverlay D i prss)).getD prss⟩)
    K _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact KOkAt.bind (KOkAt.set _) fun _ => KOkAt.pure _

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree add at most `treeSetups tree * d` cells when each ceremony adds at most `d`. -/
theorem ceremonyOutput_ks
    (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), KS b (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) (Option (List (List Bit)))) (top : TopTree)
    (tree : Tree) (d : ℕ) (hrun : ∀ jobs, KS b (run jobs) d) :
    KS b (ceremonyOutput lift parameter run top tree) (treeSetups tree * d) := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine KS.bind (hrun _) (d₂ := 0) (fun o => ?_) (by simp [treeSetups])
    rcases o with _ | outputs
    · exact KS.pure _ _
    · exact KS.bind (hlift _) (fun _ => KS.pure _ 0) (by omega)
  | bottom b' =>
    unfold ceremonyOutput
    refine KS.bind (hrun _) (d₂ := d) (fun o => ?_) (by simp [treeSetups]; omega)
    rcases o with _ | outputs
    · exact KS.pure _ _
    refine KS.bind (hlift _) (d₂ := d) (fun root => ?_) (by omega)
    refine KS.bind (hlift _) (d₂ := d) (fun base => ?_) (by omega)
    refine KS.bind (hlift _) (d₂ := d) (fun found => ?_) (by omega)
    rcases found with _ | ⟨randomness, encoding⟩
    · exact KS.pure _ _
    refine KS.bind (hrun _) (d₂ := 0) (fun out => ?_) (by omega)
    rcases out with _ | values
    · exact KS.pure _ _
    refine KS.bind (hlift _) (d₂ := 0) (fun path => ?_) (by omega)
    refine KS.bind (hlift _) (d₂ := 0) (fun topRoot => ?_) (by omega)
    split_ifs
    · exact KS.pure _ _
    · exact KS.pure _ _

/-- The program of an operator in a run of `tree` adds at most `treeSetups tree * (termCount + n)` cells. -/
theorem slotProgram_kp (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (operator : OperatorState C) (tree : Tree) :
    KP b (slotProgram K circuits settings D fresh i operator tree) (treeSetups tree * (termCount C + C.n)) := by
  have htree : ∀ keys top, KP b (slotTree K circuits settings D fresh i keys top tree)
      (treeSetups tree * (termCount C + C.n)) := by
    intro keys top
    have hX := ceremonyOutput_ks (b := b) (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa))))
      (fun oa => KS.lift (KP.of_class (DigestBudgets.ClassBound.oracleStep_zero
        (DigestBudgets.noCall_of_onlySign (c := .stream) nofun (GameCount.onlySign_tweakable oa)))))
      keys.parameter (slotCeremony K circuits settings D fresh i keys) top tree _
      (slotCeremony_ks K circuits settings D fresh i keys)
    unfold slotTree
    refine (KP.bind (d₁ := treeSetups tree * (termCount C + C.n)) (d₂ := 0) ?_ fun o => ?_).mono (by omega)
    · simp only [StateT.run'_eq, StateT.run_map]
      exact KP.map _ (KP.map _ (hX (0, 0) 0))
    · rcases o with _ | output
      · exact KP.failure _
      · exact KP.pure _ _
  cases tree with
  | top =>
    unfold slotProgram
    rcases operator.keys with _ | keys
    · exact KP.failure _
    · exact htree keys _
  | bottom b' =>
    unfold slotProgram
    rcases operator.keys with _ | keys <;> rcases operator.top with _ | top
    · exact KP.failure _
    · exact KP.failure _
    · exact KP.failure _
    · exact htree keys top

end Slots

end KeyCells

/-! ## The stream cells of the game with a table -/

section CellsGame

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

attribute [local instance] inhabitedField

open FirstCounts (Within Adds remaining)

/-- The stream cells of one run of `tree`. The adversary adds at most `step` in each of the `treeFuel`
rounds, and each operator adds at most one for each key of its names in each setup of the run. -/
def treeCells (step : ℕ) (C : Committee) (tree : Tree) : ℕ :=
  treeFuel circuits settings * step + treeSetups tree * C.n * (termCount C + C.n)

/-- The network phase of one allowed run of `tree` in the game with the table `F` adds at most
`treeCells` stream cells to the public cache of the ideal joint world. An honest operator draws only
with the keys of the setup of the ceremony. It holds one key for each term that it holds and one for each
other operator. -/
def TreeRunCells : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ state sent, IsQueryBoundP (net.round state sent) (InClass .stream) step) →
    ∀ (F : Table C (gameSetups runLimit)) (tree : Tree) (s : RealState C net.State), s.runs tree < runLimit →
      ∀ (w : KeyJointState C) (k : ℕ), Within .stream w.hash k →
        ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) (executePhase worldRoles D net noFunctionality
          (treeFuel circuits settings) s.adversary fun i => slotProgram K circuits settings D
            (fun c => (List.map (fun x => tableFresh F (setupsBefore s.runs + x))
              (List.range (treeSetups tree))).getD c none) i (s.operators i) tree)).run w),
          Within .stream z.2.hash (k + treeCells circuits settings step C tree)

/-- The program of an honest operator in an allowed run of `tree` of the game with the table `F` keeps
the stream cells of its calls within `treeSetups tree * (termCount + n)` cells. Each ceremony draws
under the keys of its own setup, one for each term that the operator holds and one for each other
operator. -/
def SlotKeys : Prop :=
  ∀ (D : C.Coalition) (F : Table C (gameSetups runLimit)) (tree : Tree) (runs : Tree → ℕ), runs tree < runLimit →
    ∀ (i : C.Party) (operator : OperatorState C), i ∉ D.1 →
      KeyThen (treeSetups tree * (termCount C + C.n)) (slotProgram K circuits settings D
        (fun c => (List.map (fun x => tableFresh F (setupsBefore runs + x))
          (List.range (treeSetups tree))).getD c none) i operator tree).run ∅

omit [Fintype E] [DecidableEq E] in
/-- `TreeRunCells` from the stream cells of the honest programs. -/
theorem treeRunCells_of_slotKeys (hkeys : SlotKeys K circuits settings runLimit) :
    TreeRunCells prims K circuits settings runLimit := by
  intro D net step hround F tree s hrun w k hw z hz
  refine (executePhase_cells prims D net _ step hround _ _ _ (fun i hi => hkeys D F tree s.runs hrun i _ hi)
    w k hw z hz).mono (le_of_eq ?_)
  unfold treeCells
  ring

variable {prims K circuits settings runLimit} {D : C.Coalition} {F : Table C (gameSetups runLimit)} {step : ℕ}

omit [Fintype E] [DecidableEq E] in
/-- An allowed run of `tree` keeps the potential. -/
theorem drawTreeRun_cells (hcells : TreeRunCells prims K circuits settings runLimit)
    (net : Adversary C E Unit PEmpty PEmpty) (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (InClass .stream) step)
    (tree : Tree) (k : ℕ) (s : RealState C net.State) (w : KeyJointState C)
    (hs : CellPot runLimit (fun tree => treeCells circuits settings step C tree + step) k s w) (hrun : s.runs tree < runLimit) :
    ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) ((UsedHit.drawTreeRun K circuits settings
      (fun slot => pure (tableFresh F slot)) (wrongOutput D) D net tree).run s)).run w),
        CellPot runLimit (fun tree => treeCells circuits settings step C tree + step) k z.1.2 z.2 := by
  intro z hz
  unfold UsedHit.drawTreeRun at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    List.mapM_pure, liftComp_pure, free_pure] at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, rfl⟩ := hz
  obtain ⟨k₀, hw, hle⟩ := hs
  have h₁ := hcells D net step hround F tree s hrun w k₀ hw y₁ hy₁
  have hmon : IsQueryBoundP (wrongOutput D (fun i => (s.operators i).keys) tree y₁.1.2) (Adds .stream) 0 :=
    (noCall_iff _ _).1 (GameCount.wrongOutput_noCall D _ (fun _ ht =>
      FirstCounts.monitorCall_not_adds (c := .stream) nofun ht) _ _ _)
  have h₂ := simulateQ_jointWithin prims D _ 0 hmon y₁.2 _ h₁ y₂ hy₂
  have h₃ := simulateQ_jointWithin prims D _ step (FirstCounts.voteRound_adds .stream (by decide) D net step hround
    y₁.1.1 _ fun j q hq => by
      obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.1 hq
      exact FirstCounts.queryClass_treeVote tree o) y₂.2 _ h₂ y₃ hy₃
  refine ⟨_, h₃, ?_⟩
  have e := FirstCounts.remaining_update runLimit (fun tree => treeCells circuits settings step C tree + step) s.runs tree hrun
  dsimp only
  omega

omit [Fintype E] [DecidableEq E] in
/-- The allowed runs of `tree` keep the potential. -/
theorem drawTreeRuns_cells (hcells : TreeRunCells prims K circuits settings runLimit)
    (net : Adversary C E Unit PEmpty PEmpty) (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (InClass .stream) step)
    (tree : Tree) : ∀ count, JMoves prims D runLimit (fun tree => treeCells circuits settings step C tree + step) 0
      (UsedHit.drawTreeRuns K circuits settings runLimit (fun slot => pure (tableFresh F slot)) (wrongOutput D) D net tree count)
  | 0 => jmoves_pure _
  | count + 1 => by
    intro k s w hs z hz
    simp only [UsedHit.drawTreeRuns, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz with hmay
    · simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      exact drawTreeRuns_cells hcells net hround tree count k y.1.2 y.2
        (drawTreeRun_cells hcells net hround tree k s w hs (FirstCounts.mayRun_lt runLimit hmay) y hy) z hz
    · exact jmoves_pure _ k s w hs z hz

omit [Fintype E] [DecidableEq E] in
theorem drawTreeRequest_cells (hcells : TreeRunCells prims K circuits settings runLimit)
    (net : Adversary C E Unit PEmpty PEmpty) (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (InClass .stream) step)
    (b : Fin (2 ^ layerHeight)) :
    JMoves prims D runLimit (fun tree => treeCells circuits settings step C tree + step) 0 (UsedHit.drawTreeRequest K circuits settings runLimit
      (fun slot => pure (tableFresh F slot)) (wrongOutput D) D net b) := by
  unfold UsedHit.drawTreeRequest
  refine jmoves_bind (n := 0) (l := 0) (drawTreeRuns_cells hcells net hround _ 1) fun _ => jmoves_get_bind fun s => ?_
  split
  · exact jmoves_bind (n := 0) (l := 0) (jmoves_lift (FirstCounts.free_noAdds (c := .stream) nofun
      (GameCount.onlySign_prfValue _ _))) fun _ => jmoves_pure _
  · exact jmoves_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The answer of an honest operator adds no stream cell. It is `tsigOracles` on the free copy. -/
theorem operatorAnswer_cells {σ : Type} {cost : Tree → ℕ} (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) (t : TsigState C) :
    JMoves prims D runLimit cost 0
      ((operatorAnswer (m := RealM C σ) realLift (gameValue D operators) operator e q).run t) := by
  have hom := hom_operatorAnswer (realHom σ) (fun oa => free (liftComp oa (LocalSpec C)))
    (fun x => free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))) operator e q t
  change JMoves prims D runLimit cost 0 ((operatorAnswer (fun oa => realHom σ (free (liftComp oa (LocalSpec C))))
    (fun x => realHom σ (free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))))
      operator e q).run t)
  rw [← hom]
  refine jmoves_lift ?_
  unfold operatorAnswer
  split
  · rename_i keys top _ _ _ _
    rw [ownAnswer_run]
    exact DigestBudgets.signQuiet (c := .stream) nofun D operators keys top q _
  · exact isQueryBoundP_pure _ _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem signRequest_cells {σ : Type} {cost : Tree → ℕ} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    JMovesT prims D runLimit cost 0 (signRequest D i e q : StateT (TsigState C) (RealM C σ) _) := by
  intro t
  unfold signRequest
  simp only [StateT.run_bind]
  exact jmoves_bind (n := 0) (l := 0) (jmovesT_lift (jmoves_modify (fun s : RealState C σ =>
    { s with closed := Function.update s.closed (treeOf e) true }) fun _ => rfl) t) fun y =>
      jmoves_bind (n := 0) (l := 0) (jmovesT_lift jmoves_get y.2) fun _ => operatorAnswer_cells _ _ _ _ _

omit [Fintype E] [DecidableEq E] in
/-- The signing phase moves the potential by the calls of class `stream` of the forger. -/
theorem drawSigning_cells (hcells : TreeRunCells prims K circuits settings runLimit) (A : DkgTsigAdversary C E)
    (hround : ∀ state sent, IsQueryBoundP (A.net.round state sent) (InClass .stream) step) (forge : ℕ)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .stream) forge) :
    JMoves prims D runLimit (fun tree => treeCells circuits settings step C tree + step) forge (UsedHit.drawSigning K circuits settings runLimit
      (fun slot => pure (tableFresh F slot)) (wrongOutput D) D A) := by
  have hP : ∀ q, ¬ ForgeInClass (C := C) (σ := A.net.State) .stream (.inr q) := fun _ => id
  unfold UsedHit.drawSigning
  refine jmoves_get_bind fun s => ?_
  split
  · refine jmoves_mono (jmoves_bind (l := 0) (jmovesT_simulateQ _ (ForgeInClass .stream) (fun q => ?_) _ forge
      (hforge _ _) _) fun p => ?_) (by omega)
    · rcases q with t | q | q
      · refine jmovesT_lift (jmoves_lift ?_)
        rw [ThresholdLeanXmssSecurity.adversary_query]
        change IsQueryBoundP (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _)
          (Adds .stream) _
        rw [isQueryBoundP_query_iff]
        split_ifs with ht
        · exact fun _ => Nat.one_pos
        · exact fun h => absurd h ht
      · simp only [hP, ↓reduceIte]
        rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · exact fun t => jmoves_pure _
        · exact jmovesT_lift (drawTreeRequest_cells hcells A.net hround b)
        · exact signRequest_cells _ _ _
        · exact signRequest_cells _ _ _
      · simp only [hP, ↓reduceIte]
        rcases q with _ | state
        · exact jmovesT_lift (jmoves_map _ jmoves_get)
        · exact jmovesT_lift (jmoves_modify (fun s : RealState C A.net.State => { s with adversary := state })
            fun _ => rfl)
    · obtain ⟨forgery, st⟩ := p
      refine jmoves_get_bind fun s' => ?_
      rw [forgeryWins_canonicalDealt]
      exact jmoves_lift ((noCall_iff _ _).1 (noCall_forgeryWins _ _ _ _ _))
  · exact jmoves_mono (jmoves_pure _) (Nat.zero_le _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The stream cells of `runLimit` runs of each tree are the rounds of the adversary in the runs and
their votes and `honestKnownKeys`. -/
theorem remaining_treeCells :
    remaining runLimit (fun tree => treeCells circuits settings step C tree + step) (fun _ => 0) =
      runLimit * (1 + 2 ^ layerHeight) * (treeFuel circuits settings + 1) * step + honestKnownKeys runLimit C := by
  simp only [remaining, Nat.sub_zero, treeCells, treeSetups, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, honestKnownKeys, gameSetups]
  ring

omit [Fintype E] [DecidableEq E] in
/-- The game with the table `F` keeps the stream cells within the budget of the adversary in class
`stream` and `honestKnownKeys`. -/
theorem tableGame_within (hcells : TreeRunCells prims K circuits settings runLimit) (A : DkgTsigAdversary C E)
    (start forge : ℕ) (hstart : ∀ x z, IsQueryBoundP (A.net.start x z) (InClass .stream) start)
    (hround : ∀ state sent, IsQueryBoundP (A.net.round state sent) (InClass .stream) step)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .stream) forge) :
    ∀ r ∈ support (UsedHit.jointRun prims D (UsedHit.tableGame K circuits settings runLimit F D A)),
      Within .stream r.2.hash (start + setupRounds * step + step +
        remaining runLimit (fun tree => treeCells circuits settings step C tree + step) (fun _ => 0) + forge) := by
  intro r hr
  unfold UsedHit.jointRun UsedHit.tableGame UsedHit.drawGame UsedHit.drawRun at hr
  rw [simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr'
  obtain ⟨⟨⟨state, keys⟩, w₁⟩, hy, hr'⟩ := hr'
  have hw₁ := simulateQ_jointWithin prims D _ _ (FirstCounts.isQueryBoundP_add (fun _ => FirstCounts.adds_or .stream)
    _ _ _ (FirstCounts.ownAdds_realExecution .stream D A.net start step hstart hround setupRounds _ _ _)
    ((GameCount.bound_iff _ _ _).1 (DigestBudgets.seedHonest (C := C) (E := E) (c := .stream) nofun D A.net)))
    keyJointInitial 0 (FirstCounts.within_empty .stream) _ hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr'
  obtain ⟨⟨⟨state, ok⟩, w₂⟩, hv, hr'⟩ := hr'
  have hw₂ := simulateQ_jointWithin prims D _ step (FirstCounts.voteRound_adds .stream (by decide) D A.net step hround
    _ _ fun j q hq => by
      obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.1 hq
      rfl) w₁ _ hw₁ _ hv
  obtain ⟨y, hy₂, rfl⟩ := hr'
  obtain ⟨x, hx, hy₂⟩ := hy₂
  have h₁ := drawTreeRuns_cells (D := D) (F := F) hcells A.net hround .top runLimit _ (seedState D state keys ok) w₂
    ⟨_, hw₂, le_rfl⟩ x hx
  obtain ⟨k₀, hw, hle⟩ := drawSigning_cells (D := D) (F := F) hcells A hround forge hforge _ x.1.2 x.2 h₁ y hy₂
  have hruns : (seedState D state keys ok).runs = fun _ => 0 := rfl
  rw [hruns] at hle
  generalize remaining runLimit (fun tree => treeCells circuits settings step C tree + step) (fun _ => 0) = R at hle ⊢
  generalize remaining runLimit (fun tree => treeCells circuits settings step C tree + step) y.1.2.runs = R' at hle
  generalize setupRounds * step = M at hle ⊢
  exact hw.mono (by omega)

omit [Fintype E] [DecidableEq E] in
/-- `CellsCount` from the stream cells of one network phase of a tree run. -/
theorem cellsCount_of_treeRunCells (hcells : TreeRunCells prims K circuits settings runLimit) :
    UsedHit.CellsCount K circuits settings runLimit prims := by
  intro D A q hq F r hr
  obtain ⟨start, step, forge, hsum, hstart, hround, hforge⟩ :=
    dkgTsigBounded_classBounded circuits settings runLimit hq .stream
  refine (streamCells_card_le _ _ (tableGame_within (step := step) hcells A start forge hstart hround hforge r hr)).trans ?_
  rw [remaining_treeCells]
  simp only [dkgTsigRounds] at hsum
  nlinarith

omit [Fintype E] [DecidableEq E] in
/-- `CellsCount` from the stream cells of the honest programs. -/
theorem cellsCount_of_slotKeys (hkeys : SlotKeys K circuits settings runLimit) :
    UsedHit.CellsCount K circuits settings runLimit prims :=
  cellsCount_of_treeRunCells (treeRunCells_of_slotKeys prims K circuits settings runLimit hkeys)

end CellsGame

section CellsEnd

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] in
/-- The program of each honest operator in an allowed run keeps its stream cells within
`treeSetups tree * (termCount + n)` cells. -/
theorem slotKeys : SlotKeys K circuits settings runLimit := by
  intro D F tree runs _ i operator _
  have h := KeyCells.slotProgram_kp (b := treeSetups tree * (termCount C + C.n)) K circuits settings D
    (fun c => (List.map (fun x => tableFresh F (setupsBefore runs + x)) (List.range (treeSetups tree))).getD c none)
    i operator tree ∅ (by simp)
  show KeyCells.KeyThenP _ (fun _ Q => Q.card ≤ treeSetups tree * (termCount C + C.n)) _ ∅
  exact KeyCells.KeyThenP.imp _ (fun _ Q' hQ' => by simpa using hQ') _ h

omit [Fintype E] [DecidableEq E] in
/-- The public cache at the end of the game with a table has at most `q + honestKnownKeys` stream cells. -/
theorem cellsCount : UsedHit.CellsCount K circuits settings runLimit prims :=
  cellsCount_of_slotKeys (slotKeys K circuits settings runLimit)

end CellsEnd

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cellsCount_of_treeRunCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cellsCount_of_treeRunCells

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cellsCount_of_slotKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cellsCount_of_slotKeys

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cellsCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cellsCount
