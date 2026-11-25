import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Represent
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Counts

/-!
# The cost of the program of the shared rest

`StCost`, `GameCost` and `GameCostT` are the cost calculus of `Cost.lean` (`TableCost`, `RedCost`)
for a state over the oracle computations of any spec. `peekCharge cW` charges a call of the world
with `cW` and a read with nothing.

`cost_sharedProgram_le` bounds the cost of `sharedProgram` for each charge `cW` of the calls of the
world. Each real run of a tree costs `R tree`, at most `runLimit` runs of each tree run, the calls of
`forge` cost `F`, and the dealer, its signing oracles and the win test cost nothing. The potential
of the runs is `FirstCounts.remaining`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

open PFunctor.FreeM (costWith cost costWith_mono costWith_le_cost_add)

/-! ## A cost calculus on a state over oracle computations -/

section Calculus

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (c : ι → ℕ∞) {X : Type}

/-- `m` costs at most `B` from every state, with the cost `k` of the result. -/
def StCost {α : Type} (m : StateT X (OracleComp spec) α) (k : α → ℕ∞) (B : ℕ∞) : Prop :=
  ∀ x, costWith c (m.run x) (fun p => k p.1) ≤ B

namespace StCost

variable {c} {α β : Type}

theorem mono {m : StateT X (OracleComp spec) α} {k k' : α → ℕ∞} {B B' : ℕ∞} (h : StCost c m k B)
    (hk : ∀ a, k' a ≤ k a) (hB : B ≤ B') : StCost c m k' B' := fun x =>
  (costWith_mono _ fun p : α × X => hk p.1).trans ((h x).trans hB)

theorem pure (a : α) (k : α → ℕ∞) : StCost c (Pure.pure a : StateT X (OracleComp spec) α) k (k a) := fun _ => le_rfl

theorem bind {m : StateT X (OracleComp spec) α} {f : α → StateT X (OracleComp spec) β} {K : α → ℕ∞}
    {k : β → ℕ∞} {B : ℕ∞} (h : StCost c m K B) (hf : ∀ a, StCost c (f a) k (K a)) : StCost c (m >>= f) k B :=
  fun x => by
  rw [StateT.run_bind, PFunctor.FreeM.costWith_bind']
  exact (costWith_mono _ fun p : α × X => hf p.1 p.2).trans (h x)

theorem frame {m : StateT X (OracleComp spec) α} {k : α → ℕ∞} {B : ℕ∞} (h : StCost c m k B) (r : ℕ∞) :
    StCost c m (fun a => k a + r) (B + r) := fun x =>
  (costWith_add_le _ _ _ r).trans (add_le_add (h x) le_rfl)

end StCost

/-- `m` costs at most `Φ s` from every game state `s`, with the cost `k` of the output and of
the new game state. -/
def GameCost {σ α : Type} (m : StateT (RealState C σ) (StateT X (OracleComp spec)) α)
    (k : α → RealState C σ → ℕ∞) (Φ : RealState C σ → ℕ∞) : Prop :=
  ∀ s, StCost c (m.run s) (fun p => k p.1 p.2) (Φ s)

/-- `GameCost` from every state of the signing game. -/
def GameCostT {σ α : Type} (m : StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) α)
    (k : α → RealState C σ → ℕ∞) (Φ : RealState C σ → ℕ∞) : Prop :=
  ∀ st, GameCost c (m.run st) (fun p s => k p.1 s) Φ

namespace GameCost

variable {c} {σ α β : Type}

theorem mono {m : StateT (RealState C σ) (StateT X (OracleComp spec)) α} {k k' : α → RealState C σ → ℕ∞}
    {Φ Φ' : RealState C σ → ℕ∞} (h : GameCost c m k Φ) (hk : ∀ a s, k' a s ≤ k a s) (hΦ : ∀ s, Φ s ≤ Φ' s) :
    GameCost c m k' Φ' := fun s =>
  (h s).mono (fun p : α × RealState C σ => hk p.1 p.2) (hΦ s)

theorem pure (a : α) (k : α → RealState C σ → ℕ∞) :
    GameCost c (Pure.pure a : StateT (RealState C σ) (StateT X (OracleComp spec)) α) k (k a) :=
  fun s => StCost.pure (a, s) _

theorem bind {m : StateT (RealState C σ) (StateT X (OracleComp spec)) α}
    {f : α → StateT (RealState C σ) (StateT X (OracleComp spec)) β} {K : α → RealState C σ → ℕ∞}
    {k : β → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞} (h : GameCost c m K Φ)
    (hf : ∀ a, GameCost c (f a) k (K a)) : GameCost c (m >>= f) k Φ := fun s => by
  rw [StateT.run_bind]
  exact StCost.bind (h s) fun p => hf p.1 p.2

theorem frame {m : StateT (RealState C σ) (StateT X (OracleComp spec)) α} {k : α → RealState C σ → ℕ∞}
    {Φ : RealState C σ → ℕ∞} (h : GameCost c m k Φ) (r : ℕ∞) :
    GameCost c m (fun a s => k a s + r) (fun s => Φ s + r) := fun s => (h s).frame r

theorem get_bind {f : RealState C σ → StateT (RealState C σ) (StateT X (OracleComp spec)) α}
    {k : α → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞}
    (h : ∀ s, StCost c ((f s).run s) (fun p => k p.1 p.2) (Φ s)) : GameCost c (get >>= f) k Φ := fun s => by
  rw [StateT.run_bind]
  exact h s

theorem set (t : RealState C σ) (k : PUnit → RealState C σ → ℕ∞) :
    GameCost c (MonadStateOf.set t : StateT (RealState C σ) (StateT X (OracleComp spec)) PUnit) k fun _ => k () t :=
  fun _ => StCost.pure (PUnit.unit, t) _

theorem modify (f : RealState C σ → RealState C σ) (k : PUnit → RealState C σ → ℕ∞) :
    GameCost c (modify f : StateT (RealState C σ) (StateT X (OracleComp spec)) PUnit) k (fun s => k () (f s)) :=
  fun s => StCost.pure (PUnit.unit, f s) _

theorem lift {m : StateT X (OracleComp spec) α} {k : α → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞}
    (h : ∀ s, StCost c m (fun a => k a s) (Φ s)) :
    GameCost c (StateT.lift m : StateT (RealState C σ) (StateT X (OracleComp spec)) α) k Φ := fun s => by
  rw [StateT.run_lift]
  exact StCost.bind (h s) fun a => StCost.pure (a, s) _

theorem of_eq {m m' : StateT (RealState C σ) (StateT X (OracleComp spec)) α} {k : α → RealState C σ → ℕ∞}
    {Φ : RealState C σ → ℕ∞} (h : GameCost c m k Φ) (e : m = m') : GameCost c m' k Φ := e ▸ h

theorem map_get (f : RealState C σ → α) (k : α → RealState C σ → ℕ∞) :
    GameCost c (f <$> (get : StateT (RealState C σ) (StateT X (OracleComp spec)) _)) k (fun s => k (f s) s) := by
  rw [map_eq_bind_pure_comp]
  exact get_bind fun _ => StCost.pure _ _

end GameCost

namespace GameCostT

variable {c} {σ α β : Type}

theorem mono {m : StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) α}
    {k k' : α → RealState C σ → ℕ∞} {Φ Φ' : RealState C σ → ℕ∞} (h : GameCostT c m k Φ)
    (hk : ∀ a s, k' a s ≤ k a s) (hΦ : ∀ s, Φ s ≤ Φ' s) : GameCostT c m k' Φ' := fun st =>
  (h st).mono (fun p s => hk p.1 s) hΦ

theorem pure (a : α) (k : α → RealState C σ → ℕ∞) :
    GameCostT c (Pure.pure a : StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) α) k
      (k a) := fun _ => GameCost.pure _ _

theorem bind {m : StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) α}
    {f : α → StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) β}
    {K : α → RealState C σ → ℕ∞} {k : β → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞}
    (h : GameCostT c m K Φ) (hf : ∀ a, GameCostT c (f a) k (K a)) : GameCostT c (m >>= f) k Φ := fun st => by
  rw [StateT.run_bind]
  exact GameCost.bind (h st) fun p => hf p.1 p.2

theorem frame {m : StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) α}
    {k : α → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞} (h : GameCostT c m k Φ) (r : ℕ∞) :
    GameCostT c m (fun a s => k a s + r) (fun s => Φ s + r) := fun st => (h st).frame r

theorem lift {m : StateT (RealState C σ) (StateT X (OracleComp spec)) α} {k : α → RealState C σ → ℕ∞}
    {Φ : RealState C σ → ℕ∞} (h : GameCost c m k Φ) :
    GameCostT c (StateT.lift m : StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) α)
      k Φ := fun _ => GameCost.bind h fun _ => GameCost.pure _ _

theorem get_bind {f : RealState C σ → StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec))) α}
    {k : α → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞}
    (h : ∀ s st, StCost c (((f s).run st).run s) (fun p => k p.1.1 p.2) (Φ s)) :
    GameCostT c (StateT.lift get >>= f) k Φ := fun st s => by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get]
  exact h s st

/-- A program through a stateful handler costs at most the charges `d` of its calls plus the
potential `Φ`, when each step costs at most its charge and the drop of `Φ`. -/
theorem simulateQ {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}
    (impl : QueryImpl spec' (StateT (TsigState C) (StateT (RealState C σ) (StateT X (OracleComp spec)))))
    (d : ι' → ℕ∞) (Φ : RealState C σ → ℕ∞)
    (hstep : ∀ t, GameCostT c (impl t) (fun _ s => Φ s) (fun s => d t + Φ s)) (oa : OracleComp spec' α) :
    GameCostT c (simulateQ impl oa) (fun _ s => Φ s) (fun s => cost d oa + Φ s) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [cost] using GameCostT.pure (c := c) a fun _ s => Φ s
  | query_bind t f ih =>
    rw [simulateQ_query_bind, cost, costWith_query_bind]
    refine bind (K := fun u s => cost d (f u) + Φ s) ?_ ih
    refine ((hstep t).frame (⨆ u, cost d (f u))).mono (fun u s => ?_) (fun s => ?_)
    · rw [add_comm (cost d (f u))]
      exact add_le_add le_rfl (le_iSup (fun u => cost d (f u)) u)
    · rw [add_assoc, add_comm (Φ s), ← add_assoc]
      rfl

end GameCostT

end Calculus

/-! ## Programs with reads -/

section Peek

/-- The charge of a call of the world with reads. A read costs nothing. -/
def peekCharge (cW : (WorldSpec C).Domain → ℕ∞) : (PeekSpec C).Domain → ℕ∞
  | .inl t => cW t
  | .inr _ => 0

variable (cW : (WorldSpec C).Domain → ℕ∞)

/-- A computation of the world as a computation with reads costs its calls of the world. -/
theorem stCost_simulateQ_peek {β : Type} (oa : OracleComp (WorldSpec C) β) (k : β → ℕ∞) :
    StCost (peekCharge cW) (simulateQ peekHandler oa) k (costWith cW oa k) := by
  induction oa using OracleComp.inductionOn with
  | pure b => intro v; simp
  | query_bind t f ih =>
    intro v
    rw [simulateQ_query_bind, StateT.run_bind, costWith_query_bind]
    simp only [peekHandler, liftM, monadLift_self, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_mk,
      bind_assoc, pure_bind]
    change costWith (peekCharge cW) (liftM ((PeekSpec C).query (.inl t)) >>= fun r =>
      liftM ((PeekSpec C).query (.inr ())) >>= fun w => (simulateQ peekHandler (f r)).run w) _ ≤ _
    simp only [costWith_query_bind, peekCharge, zero_add]
    gcongr with r
    exact iSup_le fun w => ih r w

variable {σ : Type}

/-- A computation of the world in the game costs its calls of the world. -/
theorem gameCost_inWorld {β : Type} (oa : OracleComp (WorldSpec C) β) {B : ℕ∞} (h : cost cW oa ≤ B)
    (Ψ : RealState C σ → ℕ∞) :
    GameCost (peekCharge cW) (inWorld peekHandler oa : SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β)
      (fun _ s => Ψ s) (fun s => B + Ψ s) :=
  GameCost.lift fun s => (stCost_simulateQ_peek cW oa fun _ => Ψ s).mono (fun _ => le_rfl)
    ((costWith_le_cost_add _ _).trans (add_le_add h (iSup_le fun _ => le_rfl)))

/-- A read of the stream state costs nothing. -/
theorem gameCost_read_bind {β : Type} {f : StreamState C → SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β}
    {k : β → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞} (h : ∀ u, GameCost (peekCharge cW) (f u) k Φ) :
    GameCost (peekCharge cW) (StateT.lift (id <$> get) >>= f) k Φ := fun s v => by
  have e := h v s v
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_get, map_pure, pure_bind, id,
    StateT.run_pure]
  exact e

end Peek

/-! ## The cost of the shared rest -/

section Walk

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (cW : (WorldSpec C).Domain → ℕ∞) (R : Tree → ℕ) (D : C.Coalition)

/-- The potential of the runs that remain, with the cost `R tree` for each run of `tree`. -/
def runsLeft {σ : Type} (s : RealState C σ) : ℕ∞ := (FirstCounts.remaining runLimit R s.runs : ℕ)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem queryClass_map_treeVote {tree : Tree} {output : Option TreeOutput} {q : Query C}
    (h : output.map (treeVote tree) = some q) : queryClass q = .vote := by
  cases output with
  | none => cases h
  | some output =>
    cases h
    exact FirstCounts.queryClass_treeVote tree output

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem queryClass_map_seedVote {keys : Option (Keys C)} {q : Query C} (h : keys.map seedVote = some q) :
    queryClass q = .vote := by
  cases keys with
  | none => cases h
  | some keys =>
    cases h
    rfl

omit [Fintype E] [DecidableEq E] in
/-- One real run of `tree` from a state with fewer than `runLimit` runs of `tree` costs its part of
the potential. -/
theorem stCost_sharedRun (net : Adversary C E Unit PEmpty PEmpty)
    (V : ℕ∞) (hvote : ∀ (state : net.State) (input : C.Party → Option (Query C)),
      (∀ j q, input j = some q → queryClass q = .vote) → cost cW (voteRound worldRoles D net state input) ≤ V)
    (hrun : ∀ (s : RealState C net.State) (tree : Tree),
      cost cW (executePhaseR worldRoles D net noFunctionality ([] : Record C E) (treeFuel circuits settings)
        s.adversary fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) + V ≤
          R tree)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) (s : RealState C net.State) (hs : s.runs tree < runLimit) :
    StCost (peekCharge cW) ((sharedRun K circuits settings peekHandler id Mode.real D net parameter seeds dealt emu
      tree).run s) (fun p => runsLeft runLimit R p.2) (runsLeft runLimit R s) := by
  unfold sharedRun
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  have hnot : ¬ s.runs tree < Mode.real.emulated tree := by simp [Mode.real]
  rw [ite_eq_right hnot]
  unfold sharedRunWith
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  have hpot : (R tree : ℕ∞) + ((FirstCounts.remaining runLimit R (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞) =
      runsLeft runLimit R s := by
    rw [runsLeft, ← FirstCounts.remaining_update runLimit R s.runs tree hs, Nat.cast_add, add_comm]
  refine (?_ : GameCost (peekCharge cW) _ (fun _ s => runsLeft runLimit R s) fun _ => runsLeft runLimit R s) s
  refine gameCost_read_bind cW fun before => ?_
  refine GameCost.bind (K := fun _ _ =>
    V + ((FirstCounts.remaining runLimit R (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((gameCost_inWorld cW _ le_rfl _).mono (fun _ _ => le_rfl) fun _ => by
      rw [← add_assoc, ← hpot]
      exact add_le_add (hrun s tree) le_rfl) fun r => ?_
  refine gameCost_read_bind cW fun after => ?_
  refine GameCost.bind (K := fun _ _ =>
    ((FirstCounts.remaining runLimit R (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((gameCost_inWorld cW _ (hvote _ _ fun _ _ => queryClass_map_treeVote) _).mono (fun _ _ => le_rfl)
      fun _ => le_rfl) fun v => ?_
  exact (GameCost.set _ _).mono (fun _ _ => le_rfl) fun _ => le_rfl

omit [Fintype E] [DecidableEq E] in
/-- The runs of `tree` cost the drop of the potential. -/
theorem gameCost_sharedRuns (net : Adversary C E Unit PEmpty PEmpty)
    (V : ℕ∞) (hvote : ∀ (state : net.State) (input : C.Party → Option (Query C)),
      (∀ j q, input j = some q → queryClass q = .vote) → cost cW (voteRound worldRoles D net state input) ≤ V)
    (hrun : ∀ (s : RealState C net.State) (tree : Tree),
      cost cW (executePhaseR worldRoles D net noFunctionality ([] : Record C E) (treeFuel circuits settings)
        s.adversary fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) + V ≤
          R tree)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, GameCost (peekCharge cW)
      (sharedRuns K circuits settings runLimit peekHandler id Mode.real D net parameter seeds dealt emu tree count)
      (fun _ s => runsLeft runLimit R s) (runsLeft runLimit R)
  | 0 => GameCost.pure _ _
  | count + 1 => by
    have rest := gameCost_sharedRuns net V hvote hrun parameter seeds dealt emu tree count
    unfold sharedRuns
    refine GameCost.get_bind fun s => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h, StateT.run_bind]
      exact StCost.bind (stCost_sharedRun K circuits settings runLimit cW R D net V hvote hrun parameter seeds dealt emu tree s
        (FirstCounts.mayRun_lt runLimit h)) fun p => rest p.2
    · rw [ite_eq_right h]
      exact StCost.pure _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The signing oracles of a dealer on the computations of the world. -/
theorem gameCostT_tsig {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C)
    (htsig : ∀ st, cost cW ((tsigOracles (fun oa => free (liftComp oa _)) d q).run st) ≤ 0)
    (Ψ : RealState C σ → ℕ∞) :
    GameCostT (peekCharge cW)
      (tsigOracles (sharedLift (σ := σ) peekHandler) (SeedHitProof.Dealt.hmap (worldHomOver peekHandler σ) d) q)
      (fun _ s => Ψ s) (fun s => 0 + Ψ s) := fun st =>
  (gameCost_inWorld cW _ (htsig st) Ψ).of_eq
    (SeedHitProof.hom_tsigOracles (worldHomOver peekHandler σ) (fun oa => free (liftComp oa _)) d q st)

omit [Fintype E] [DecidableEq E] in
theorem gameCostT_dealerOracles (A : DkgTsigAdversary C E)
    (V : ℕ∞) (hvote : ∀ (state : A.net.State) (input : C.Party → Option (Query C)),
      (∀ j q, input j = some q → queryClass q = .vote) → cost cW (voteRound worldRoles D A.net state input) ≤ V)
    (hrun : ∀ (s : RealState C A.net.State) (tree : Tree),
      cost cW (executePhaseR worldRoles D A.net noFunctionality ([] : Record C E) (treeFuel circuits settings)
        s.adversary fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) + V ≤
          R tree)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (d : Dealt C (OracleComp (WorldSpec C)))
    (htsig : ∀ q st, cost cW ((tsigOracles (fun oa => free (liftComp oa _)) d q).run st) ≤ 0) (q : TsigQuery C) :
    GameCostT (peekCharge cW)
      (sharedDealerOracles K circuits settings runLimit peekHandler id Mode.real D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (worldHomOver peekHandler A.net.State) d) q)
      (fun _ s => runsLeft runLimit R s) (fun s => 0 + runsLeft runLimit R s) := by
  unfold sharedDealerOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact (GameCostT.pure _ _).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm
  · dsimp only
    refine GameCostT.bind (K := fun _ s => runsLeft runLimit R s)
      ((gameCostT_tsig cW d _ (htsig _) _).mono (fun _ _ => le_rfl) fun _ => le_rfl) fun answer => ?_
    have tail : GameCostT (peekCharge cW) (StateT.lift get >>= fun s : RealState C A.net.State =>
        match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => pure (some (tree, ρ))
        | _, _ => pure none : StateT (TsigState C) (SharedM C (OracleComp (PeekSpec C)) (StreamState C) A.net.State) _)
        (fun _ s => runsLeft runLimit R s) (fun s => runsLeft runLimit R s) := by
      refine GameCostT.get_bind fun s st => ?_
      split <;> exact StCost.pure _ _
    by_cases hc : Mode.real.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      exact GameCostT.bind (GameCostT.lift (gameCost_sharedRuns K circuits settings runLimit cW R D A.net V hvote hrun
        parameter seeds dealt emu _ 1)) fun _ => tail
    · simp only [hc, ↓reduceIte]
      exact tail
  all_goals
    dsimp only
    refine GameCostT.bind (K := fun _ s => runsLeft runLimit R s)
      ((GameCostT.lift (GameCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm) fun _ => ?_
    refine GameCostT.get_bind fun s st => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first
        | exact (gameCostT_tsig cW d _ (htsig _) _ st s).mono (fun _ => le_rfl) (le_of_eq (zero_add _))
        | exact StCost.pure _ _

/-- The charge of a call of `forge`. A call of the local oracles costs `fc`, and a call of the
signing oracles or of the state costs nothing, because the runs pay from the potential. -/
def forgeCharge {σ : Type} (fc : (LocalSpec C).Domain → ℕ∞) : (LocalSpec C + (TsigSpec C + StateSpec σ)).Domain → ℕ∞
  | .inl t => fc t
  | .inr _ => 0

omit [Fintype E] [DecidableEq E] in
theorem gameCost_dealerSigning (A : DkgTsigAdversary C E)
    (V : ℕ∞) (hvote : ∀ (state : A.net.State) (input : C.Party → Option (Query C)),
      (∀ j q, input j = some q → queryClass q = .vote) → cost cW (voteRound worldRoles D A.net state input) ≤ V)
    (hrun : ∀ (s : RealState C A.net.State) (tree : Tree),
      cost cW (executePhaseR worldRoles D A.net noFunctionality ([] : Record C E) (treeFuel circuits settings)
        s.adversary fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) + V ≤
          R tree)
    (fc : (LocalSpec C).Domain → ℕ∞)
    (hforger : ∀ t, cost cW (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤ fc t)
    (F : ℕ∞) (hforge : ∀ pk top, cost (forgeCharge fc) (A.forge pk top) ≤ F)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C))
    (hdealer : cost cW (referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) _))
      (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) ≤ 0)
    (htsig : ∀ top q st, cost cW ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0)
    (hwins : ∀ top st forgery, cost cW (forgeryWins (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) st forgery) ≤ 0) :
    GameCost (peekCharge cW)
      (sharedSigning K circuits settings runLimit peekHandler id false Mode.real D A parameter seeds dealt emu)
      (fun _ _ => 0) (fun s => F + runsLeft runLimit R s) := by
  unfold sharedSigning
  refine GameCost.get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact (StCost.pure _ _).mono (fun _ => le_rfl) zero_le
  | some kt =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold sharedDealer
    simp only [bind_assoc, pure_bind]
    have e₂ : referenceTree (fun oa => sharedLift (σ := A.net.State) peekHandler (tweakable oa))
        (fun x => sharedLift (σ := A.net.State) peekHandler (prfValue seeds x)) parameter emptyTop .top =
        worldHomOver peekHandler A.net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (worldHomOver peekHandler A.net.State)
        (fun oa => free (liftComp (tweakable oa) _)) (fun x => free (liftComp (prfValue seeds x) _)) parameter
        emptyTop .top).symm
    rw [e₂]
    refine (?_ : GameCost (peekCharge cW) _ (fun _ _ => 0) fun s => F + runsLeft runLimit R s) s
    refine GameCost.bind (K := fun _ s => F + runsLeft runLimit R s)
      ((gameCost_inWorld cW _ hdealer _).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _)) fun out => ?_
    have d₂ : dealtWith (sharedLift (σ := A.net.State) peekHandler) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) (fun x => sharedLift (σ := A.net.State) peekHandler (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (worldHomOver peekHandler A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (worldHomOver peekHandler A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₂]
    refine GameCost.bind (K := fun _ s => runsLeft runLimit R s)
      (((GameCostT.simulateQ (c := peekCharge cW) _ (forgeCharge fc) (runsLeft runLimit R) (fun t => ?_) _) _).mono
        (fun _ _ => le_rfl) fun s => add_le_add (hforge _ _) le_rfl) fun p => ?_
    · rcases t with t | q | q
      · exact GameCostT.lift (gameCost_inWorld cW _ (hforger t) _)
      · exact gameCostT_dealerOracles K circuits settings runLimit cW R D A V hvote hrun parameter seeds dealt emu _
          (htsig _) q
      · rcases q with _ | state
        · exact (GameCostT.lift (GameCost.map_get _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
        · exact (GameCostT.lift (GameCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
    · rcases p with ⟨forgery, st⟩
      exact ((gameCost_inWorld cW _ (hwins _ st forgery) fun _ => 0).of_eq
        (hom_forgeryWins (worldHomOver peekHandler A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)).mono
          (fun _ _ => le_rfl) fun _ => by simp

omit [Fintype E] [DecidableEq E] in
/-- The cost of the shared rest with reads. -/
theorem stCost_sharedRestOf (A : DkgTsigAdversary C E)
    (V : ℕ∞) (hvote : ∀ (state : A.net.State) (input : C.Party → Option (Query C)),
      (∀ j q, input j = some q → queryClass q = .vote) → cost cW (voteRound worldRoles D A.net state input) ≤ V)
    (hrun : ∀ (s : RealState C A.net.State) (tree : Tree),
      cost cW (executePhaseR worldRoles D A.net noFunctionality ([] : Record C E) (treeFuel circuits settings)
        s.adversary fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) + V ≤
          R tree)
    (fc : (LocalSpec C).Domain → ℕ∞)
    (hforger : ∀ t, cost cW (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤ fc t)
    (F : ℕ∞) (hforge : ∀ pk top, cost (forgeCharge fc) (A.forge pk top) ≤ F)
    (hdealer : ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput), cost cW (referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) _))
      (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) ≤ 0)
    (htsig : ∀ parameter seeds dealt top q st, cost cW ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0)
    (hwins : ∀ parameter seeds dealt top st forgery, cost cW (forgeryWins (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) st forgery) ≤ 0)
    (state : A.net.State) (keys : C.Party → Option (Keys C)) :
    StCost (peekCharge cW) (sharedRestOf K circuits settings runLimit peekHandler id false D A state keys)
      (fun _ => 0) (V + (F + runsLeft runLimit R (startState D state keys))) := by
  unfold sharedRestOf sharedRest
  refine StCost.bind (K := fun _ => (0 : ℕ∞)) ?_ fun p => by
    rcases p with ⟨win, s⟩
    exact StCost.pure _ _
  refine GameCost.get_bind (k := fun _ _ => (0 : ℕ∞)) (Φ := fun s => V + (F + runsLeft runLimit R s)) (fun s => ?_)
    (startState D state keys)
  refine GameCost.bind (K := fun _ _ => F + runsLeft runLimit R s) (k := fun _ _ => (0 : ℕ∞))
    (gameCost_inWorld cW (voteRound worldRoles D A.net s.adversary fun i => ((s.operators i).keys).map seedVote)
      (hvote _ _ fun _ _ => queryClass_map_seedVote) fun _ => F + runsLeft runLimit R s) (fun v => ?_) s
  obtain ⟨state', ok⟩ := v
  refine GameCost.bind ((GameCost.set _ (fun _ s => F + runsLeft runLimit R s)).mono (fun _ _ => le_rfl)
    fun _ => le_rfl) fun _ => ?_
  exact GameCost.bind (K := fun _ s => F + runsLeft runLimit R s)
    ((gameCost_sharedRuns K circuits settings runLimit cW R D A.net V hvote hrun (gameParameter D keys)
      (gameSeeds D keys) (fun i => (keys i).getD noKeys) (committed ok fun _ => none) .top runLimit).frame F |>.mono
        (fun _ s => le_of_eq (add_comm _ _)) fun s => le_of_eq (add_comm _ _))
    fun _ => gameCost_dealerSigning K circuits settings runLimit cW R D A V hvote hrun fc hforger F hforge
      (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (committed ok fun _ => none)
      (hdealer _ _) (htsig _ _ _) (hwins _ _ _)

omit [Fintype E] [DecidableEq E] in
/-- The cost of the program of the shared rest. The vote of the seed generation costs at most `V`, the
runs with their votes cost `R tree` each, at most `runLimit` runs of each tree, and `forge` costs at
most `F`. The dealer and the win test cost nothing. -/
theorem cost_sharedProgram_le (A : DkgTsigAdversary C E)
    (V : ℕ∞) (hvote : ∀ (state : A.net.State) (input : C.Party → Option (Query C)),
      (∀ j q, input j = some q → queryClass q = .vote) → cost cW (voteRound worldRoles D A.net state input) ≤ V)
    (hrun : ∀ (s : RealState C A.net.State) (tree : Tree),
      cost cW (executePhaseR worldRoles D A.net noFunctionality ([] : Record C E) (treeFuel circuits settings)
        s.adversary fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run) + V ≤
          R tree)
    (fc : (LocalSpec C).Domain → ℕ∞)
    (hforger : ∀ t, cost cW (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤ fc t)
    (F : ℕ∞) (hforge : ∀ pk top, cost (forgeCharge fc) (A.forge pk top) ≤ F)
    (hdealer : ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput),
      cost cW (referenceTree (fun oa => free (liftComp (tweakable (C := C) oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) ≤ 0)
    (htsig : ∀ parameter seeds dealt top q st, cost cW ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0)
    (hwins : ∀ parameter seeds dealt top st forgery, cost cW (forgeryWins (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) st forgery) ≤ 0)
    (state : A.net.State) (keys : C.Party → Option (Keys C)) :
    cost (peekCharge cW) (sharedProgram K circuits settings runLimit D A state keys) ≤
      V + (F + (FirstCounts.remaining runLimit R (fun _ => 0) : ℕ)) := by
  have h := stCost_sharedRestOf K circuits settings runLimit cW R D A V hvote hrun fc hforger F hforge hdealer htsig hwins
    state keys
  unfold sharedProgram programOf
  change costWith (peekCharge cW) (liftM ((PeekSpec C).query (.inr ())) >>= fun w =>
    (sharedRestOf K circuits settings runLimit peekHandler id false D A state keys).run' w) (fun _ => 0) ≤ _
  rw [costWith_query_bind]
  simp only [peekCharge, zero_add]
  refine iSup_le fun w => ?_
  rw [StateT.run'_eq]
  exact (le_of_eq (PFunctor.FreeM.costWith_map' _ _ _)).trans (h w)

end Walk

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.cost_sharedProgram_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.cost_sharedProgram_le
