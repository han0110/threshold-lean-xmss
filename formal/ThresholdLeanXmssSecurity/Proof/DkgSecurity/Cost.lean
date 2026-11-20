import ThresholdLeanXmss.Statement.Dkg
import ThresholdLeanXmss.Statement.DkgReduction
import ThresholdLeanXmssSecurity.Proof.Execution
import PolyFun.PFunctor.Free.Cost.Value


/-!
# The cost calculus of the forger of the setup

The cost of a program of the forger is the worst-case charge of `adversaryCost` on its path
(`PFunctor.FreeM.costWith`), in `ℕ∞`. The leaf cost of `costWith` is the potential that the rest of
the program may still spend, so a sequence of programs composes by `costWith_bind'`.

* `TableCost m k B` says that `m` on the own table of the forger costs at most `B` from every table
  state, with the leaf cost `k`. `RedCost` is the same for the state of the game.
* `TableCost.simulateQ` and `RedCost.simulateQ` carry a cost through a stateful handler.
* `executePhase_cost` bounds a phase on the network by `fuel` rounds of the adversary and the costs
  of the honest programs, for roles in `TableM` whose steps cost at most `ownCost` and `honestCost`.
* `queryCostAtMost_iff_cost_le` reads `QueryCostAtMost` as a bound on the worst-case cost.
-/


set_option autoImplicit false

open OracleComp OracleSpec ThresholdLeanXmss HashSig LeanXmss
open PFunctor.FreeM (costWith cost costWith_mono costWith_le_cost_add)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## Worst-case costs -/

section Generic

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

theorem costWith_query_bind {α : Type} (c : ι → ℕ∞) (t : ι) (f : spec t → OracleComp spec α)
    (k : α → ℕ∞) :
    costWith c (liftM (spec.query t) >>= f) k = c t + ⨆ u, costWith c (f u) k :=
  rfl

/-- A constant added to the leaf cost adds at most that constant. -/
theorem costWith_add_le {α : Type} (c : ι → ℕ∞) (x : OracleComp spec α) (k : α → ℕ∞) (r : ℕ∞) :
    costWith c x (fun a => k a + r) ≤ costWith c x k + r := by
  induction x using OracleComp.inductionOn with
  | pure a => exact le_rfl
  | query_bind t f ih =>
    rw [costWith_query_bind, costWith_query_bind, add_assoc]
    gcongr
    exact iSup_le fun u => (ih u).trans (add_le_add (le_iSup (fun u => costWith c (f u) k) u) le_rfl)

theorem cost_bind_le_add {α β : Type} {c : ι → ℕ∞} {x : OracleComp spec α} {f : α → OracleComp spec β}
    {n m : ℕ∞} (hx : cost c x ≤ n) (hf : ∀ a, cost c (f a) ≤ m) : cost c (x >>= f) ≤ n + m := by
  rw [cost, PFunctor.FreeM.costWith_bind']
  exact (costWith_le_cost_add x _).trans (add_le_add hx (iSup_le hf))

theorem cost_pure_le {α : Type} (c : ι → ℕ∞) (a : α) (n : ℕ∞) : cost c (pure a : OracleComp spec α) ≤ n := by
  simp [cost]

theorem cost_map_le {α β : Type} {c : ι → ℕ∞} {x : OracleComp spec α} (f : α → β) {n : ℕ∞}
    (hx : cost c x ≤ n) : cost c (f <$> x) ≤ n := by
  rw [map_eq_bind_pure_comp]
  refine (cost_bind_le_add (m := 0) hx fun a => cost_pure_le c (f a) 0).trans ?_
  simp

theorem cost_query_le {c : ι → ℕ∞} (t : ι) : cost c (liftM (spec.query t) : OracleComp spec _) ≤ c t := by
  have h := costWith_query_bind (spec := spec) c t Pure.pure fun _ => 0
  simp only [bind_pure] at h
  rw [cost, h]
  simp

theorem cost_mapM_le {α β : Type} {c : ι → ℕ∞} (f : α → OracleComp spec β) (n : α → ℕ∞)
    (hf : ∀ a, cost c (f a) ≤ n a) : ∀ xs : List α, cost c (xs.mapM f) ≤ (xs.map n).sum
  | [] => cost_pure_le c _ _
  | a :: xs => by
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (cost_bind_le_add (hf a) fun _ => (cost_bind_le_add (cost_mapM_le f n hf xs) fun _ =>
      cost_pure_le c _ 0)).trans (by simp)

theorem cost_sequenceFin_sum {ι α : Type} {spec : OracleSpec.{0, 0} ι} {c : ι → ℕ∞} :
    ∀ {N : ℕ} (f : Fin N → OracleComp spec α) (n : Fin N → ℕ∞), (∀ i, cost c (f i) ≤ n i) →
      cost c (HashSig.OverPermutation.sequenceFin f) ≤ ∑ i, n i
  | 0, f, _, _ => cost_pure_le c _ _
  | N + 1, f, n, hf => by
    rw [HashSig.OverPermutation.sequenceFin, Fin.sum_univ_succ]
    exact (cost_bind_le_add (hf 0) fun _ => cost_bind_le_add (cost_sequenceFin_sum (fun i => f i.succ)
      (fun i => n i.succ) fun i => hf i.succ) fun _ => cost_pure_le c _ 0).trans (by simp)

end Generic

/-- `QueryCostAtMost` is a bound on the worst-case cost. -/
theorem queryCostAtMost_iff_cost_le {ι α : Type} {spec : OracleSpec.{0, 0} ι} (x : OracleComp spec α)
    (w : ι → ℕ) (n : ℕ) : QueryCostAtMost x w n ↔ cost (fun t => (w t : ℕ∞)) x ≤ n :=
  (PFunctor.FreeM.isChargeBound_iff_isRollBound_nat x w n).symm.trans
    PFunctor.FreeM.isChargeBound_iff_cost_natCast_le

/-! ## Programs on the own table -/

/-- The charge of a call of the forger to `tsigGame`, `adversaryCost` in `ℕ∞`. -/
def charge (t : (LocalSpec C + TsigSpec C).Domain) : ℕ∞ := adversaryCost t

/-- `m` costs at most `B` from every state of the own table, with the leaf cost `k`. -/
def TableCost {α : Type} (m : TableM C α) (k : α → ℕ∞) (B : ℕ∞) : Prop :=
  ∀ ts, costWith charge (m.run ts) (fun p => k p.1) ≤ B

namespace TableCost

variable {α β : Type}

theorem mono {m : TableM C α} {k k' : α → ℕ∞} {B B' : ℕ∞} (h : TableCost m k B) (hk : ∀ a, k' a ≤ k a)
    (hB : B ≤ B') : TableCost m k' B' := fun ts =>
  (costWith_mono _ fun p : α × TableState C => hk p.1).trans ((h ts).trans hB)

theorem pure (a : α) (k : α → ℕ∞) : TableCost (Pure.pure a : TableM C α) k (k a) := fun _ => le_rfl

theorem bind {m : TableM C α} {f : α → TableM C β} {K : α → ℕ∞} {k : β → ℕ∞} {B : ℕ∞}
    (h : TableCost m K B) (hf : ∀ a, TableCost (f a) k (K a)) : TableCost (m >>= f) k B := fun ts => by
  rw [StateT.run_bind, PFunctor.FreeM.costWith_bind']
  exact (costWith_mono _ fun p : α × TableState C => hf p.1 p.2).trans (h ts)

theorem frame {m : TableM C α} {k : α → ℕ∞} {B : ℕ∞} (h : TableCost m k B) (r : ℕ∞) :
    TableCost m (fun a => k a + r) (B + r) := fun ts =>
  (costWith_add_le _ _ _ r).trans (add_le_add (h ts) le_rfl)

theorem lift {x : OracleComp (LocalSpec C + TsigSpec C) α} {k : α → ℕ∞} {B : ℕ∞}
    (h : costWith charge x k ≤ B) : TableCost (liftM x : TableM C α) k B := fun ts => by
  change costWith charge (x >>= fun a => Pure.pure (a, ts)) _ ≤ B
  rw [PFunctor.FreeM.costWith_bind']
  exact h

theorem get (k : TableState C → ℕ∞) (B : ℕ∞) (h : ∀ s, k s ≤ B) : TableCost (MonadState.get : TableM C _) k B :=
  fun ts => h ts

/-- A program on the table through a stateful handler costs at most the charges `d` of its calls,
when each step costs at most its charge. -/
theorem simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec (TableM C)) (d : ι → ℕ∞)
    (hstep : ∀ t, TableCost (impl t) (fun _ => 0) (d t)) (k : α → ℕ∞) (oa : OracleComp spec α) :
    TableCost (simulateQ impl oa) k (costWith d oa k) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using TableCost.pure (C := C) a k
  | query_bind t f ih =>
    rw [simulateQ_query_bind, costWith_query_bind]
    change TableCost (impl t >>= fun u => _root_.simulateQ impl (f u)) k _
    refine bind (K := fun u => costWith d (f u) k) ?_ ih
    refine ((hstep t).frame (⨆ u, costWith d (f u) k)).mono (fun u => ?_) le_rfl
    simpa using le_iSup (fun u => costWith d (f u) k) u

end TableCost

/-! ## Programs on the state of the game -/

/-- `m` costs at most `Φ s` from every game state `s`, with the leaf cost `k` of the output and of
the new game state. -/
def RedCost {σ α : Type} (m : RedM C σ α) (k : α → RealState C σ → ℕ∞) (Φ : RealState C σ → ℕ∞) : Prop :=
  ∀ s, TableCost (m.run s) (fun p => k p.1 p.2) (Φ s)

namespace RedCost

variable {σ α β : Type}

theorem mono {m : RedM C σ α} {k k' : α → RealState C σ → ℕ∞} {Φ Φ' : RealState C σ → ℕ∞}
    (h : RedCost m k Φ) (hk : ∀ a s, k' a s ≤ k a s) (hΦ : ∀ s, Φ s ≤ Φ' s) : RedCost m k' Φ' := fun s =>
  (h s).mono (fun p : α × RealState C σ => hk p.1 p.2) (hΦ s)

theorem pure (a : α) (k : α → RealState C σ → ℕ∞) : RedCost (Pure.pure a : RedM C σ α) k (k a) :=
  fun s => TableCost.pure (a, s) _

theorem bind {m : RedM C σ α} {f : α → RedM C σ β} {K : α → RealState C σ → ℕ∞}
    {k : β → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞} (h : RedCost m K Φ) (hf : ∀ a, RedCost (f a) k (K a)) :
    RedCost (m >>= f) k Φ := fun s => by
  rw [StateT.run_bind]
  exact TableCost.bind (h s) fun p => hf p.1 p.2

theorem frame {m : RedM C σ α} {k : α → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞} (h : RedCost m k Φ)
    (r : ℕ∞) : RedCost m (fun a s => k a s + r) (fun s => Φ s + r) := fun s =>
  (h s).frame r

theorem lift {m : TableM C α} {k : α → RealState C σ → ℕ∞} {Φ : RealState C σ → ℕ∞}
    (h : ∀ s, TableCost m (fun a => k a s) (Φ s)) : RedCost (StateT.lift m) k Φ := fun s => by
  change TableCost (m >>= fun a => Pure.pure (a, s)) _ _
  exact TableCost.bind (h s) fun a => TableCost.pure (a, s) _

/-- A program on the game state through a stateful handler costs at most the charges `d` of its
calls plus the potential `Φ`, when each step costs at most its charge and the drop of `Φ`. -/
theorem simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec (RedM C σ)) (d : ι → ℕ∞)
    (Φ : RealState C σ → ℕ∞) (hstep : ∀ t, RedCost (impl t) (fun _ s => Φ s) (fun s => d t + Φ s))
    (oa : OracleComp spec α) :
    RedCost (simulateQ impl oa) (fun _ s => Φ s) (fun s => cost d oa + Φ s) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [cost] using RedCost.pure (C := C) a fun _ s => Φ s
  | query_bind t f ih =>
    rw [simulateQ_query_bind, cost, costWith_query_bind]
    change RedCost (impl t >>= fun u => _root_.simulateQ impl (f u)) _ _
    refine bind (K := fun u s => cost d (f u) + Φ s) ?_ ih
    refine ((hstep t).frame (⨆ u, cost d (f u))).mono (fun u s => ?_) (fun s => ?_)
    · rw [add_comm (cost d (f u))]
      exact add_le_add le_rfl (le_iSup (fun u => cost d (f u)) u)
    · rw [add_assoc, add_comm (Φ s), ← add_assoc]
      rfl

end RedCost

/-! ## The roles of the forger -/

/-- The charge of a local call of an emulated honest operator, a call of `H` outside the setup
domains, which the forger forwards to `tsigGame`. -/
def honestCost : (LocalSpec C).Domain → ℕ
  | .inr (.inl q) => if isSetupQuery q then 0 else 1
  | _ => 0

/-- Private sampling of the forger costs nothing. -/
theorem cost_liftComp_prob {α : Type} (p : ProbComp α) :
    cost charge (liftComp p (LocalSpec C + TsigSpec C)) ≤ 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact cost_pure_le _ _ _
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C + TsigSpec C) =
        (liftM ((LocalSpec C + TsigSpec C).query (.inl (.inl t))) : OracleComp (LocalSpec C + TsigSpec C) _) >>=
          fun u => liftComp (k u) (LocalSpec C + TsigSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    simpa [charge, adversaryCost] using cost_bind_le_add (n := 0) (m := 0) (cost_query_le (c := charge) _) ih

theorem tableCost_forward (t : (LocalSpec C + TsigSpec C).Domain) :
    TableCost (forward t) (fun _ => 0) (adversaryCost t) :=
  TableCost.lift (cost_query_le (c := charge) (spec := LocalSpec C + TsigSpec C) t)

theorem tableCost_tableCall (aes : Aes) (x : (RoSpec C).Domain) :
    TableCost (tableCall aes x) (fun _ => 0) 0 := fun ts => by
  unfold tableCall
  change costWith charge (liftComp ((privateStep aes x).run ts.table) _ >>= fun p => Pure.pure (p.1, _)) _ ≤ 0
  rw [PFunctor.FreeM.costWith_bind']
  simpa [cost] using cost_liftComp_prob ((privateStep aes x).run ts.table)

/-- A step of `adversaryCall` costs at most `ownCost`. -/
theorem tableCost_adversaryCall (aes : Aes) (t : (LocalSpec C).Domain) :
    TableCost (adversaryCall aes t) (fun _ => 0) (ownCost t) := by
  rcases t with n | q | x
  · exact tableCost_forward _
  · unfold adversaryCall
    dsimp only
    split_ifs
    · refine TableCost.bind (K := fun _ => 0) ((tableCost_tableCall aes _).mono (fun _ => le_rfl) zero_le)
        fun y => ?_
      refine TableCost.bind (K := fun _ => 0) (fun ts => ?_) fun _ => TableCost.pure _ _
      exact le_rfl
    · exact (tableCost_forward _).mono (fun _ => le_rfl) (by simp [adversaryCost, ownCost])
  · exact (tableCost_tableCall aes _).mono (fun _ => le_rfl) (zero_le)

/-- A step of `honestCall` costs at most `honestCost`. -/
theorem tableCost_honestCall (aes : Aes) (D : C.Coalition) (t : (LocalSpec C).Domain) :
    TableCost (honestCall aes D t) (fun _ => 0) (honestCost t) := by
  rcases t with n | q | x
  · exact tableCost_forward _
  · unfold honestCall
    dsimp only
    split_ifs with hq
    · exact (tableCost_tableCall aes _).mono (fun _ => le_rfl) (zero_le)
    · exact (tableCost_forward _).mono (fun _ => le_rfl) (by simp [adversaryCost, honestCost, hq])
  · unfold honestCall
    dsimp only
    split_ifs
    · intro ts
      change costWith charge (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run ts.streams) _ >>=
        fun p => Pure.pure (p.1, _)) _ ≤ _
      rw [PFunctor.FreeM.costWith_bind']
      simpa [cost] using (cost_liftComp_prob _).trans (zero_le)
    · exact (tableCost_tableCall aes _).mono (fun _ => le_rfl) (zero_le)

/-- The adversary of the forger costs at most the calls of `ownCost`. -/
theorem tableCost_adversary (aes : Aes) (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β)
    (k : β → ℕ∞) :
    TableCost ((reductionRoles aes D).adversary oa) k (costWith (fun t => (ownCost t : ℕ∞)) oa k) :=
  TableCost.simulateQ _ _ (tableCost_adversaryCall aes) k oa

/-- The emulated honest operators cost at most the calls of `honestCost`. -/
theorem tableCost_honest (aes : Aes) (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β)
    (k : β → ℕ∞) :
    TableCost ((reductionRoles aes D).honest oa) k (costWith (fun t => (honestCost t : ℕ∞)) oa k) :=
  TableCost.simulateQ _ _ (tableCost_honestCall aes D) k oa

/-- A private sample of an emulated operator costs nothing. -/
theorem cost_liftComp_local {α : Type} (p : ProbComp α) :
    cost (fun t => (honestCost (C := C) t : ℕ∞)) (liftComp p (LocalSpec C)) ≤ 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact cost_pure_le _ _ _
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inl t)) : OracleComp (LocalSpec C) _) >>= fun u => liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    simpa [honestCost] using cost_bind_le_add (n := 0) (m := 0) (cost_query_le (c := fun t => (honestCost (C := C) t : ℕ∞)) _) ih

/-! ## The phases on the network -/

section Network

variable {E : Type}

/-- The charge of a call of an operator program. A round costs nothing. -/
def partyCost : (PartySpec C E RealSpec).Domain → ℕ
  | .inl (.inl t) => honestCost t
  | _ => 0

/-- The cost of an operator program. -/
abbrev partyCharge (t : (PartySpec C E RealSpec).Domain) : ℕ∞ := partyCost t

/-- The most that the rest of a stopped program can cost. -/
def rest {α : Type} : Step C E RealSpec α → ℕ∞
  | .wait _ k => ⨆ inbox, cost partyCharge (k inbox)
  | _ => 0

/-- Advancing a program to its next round costs the local calls on the way, and leaves the rest. -/
theorem costWith_advance {α : Type} (p : OracleComp (PartySpec C E RealSpec) (Option α)) :
    costWith (fun t => (honestCost t : ℕ∞)) (advance p) rest ≤ cost partyCharge p := by
  induction p using OracleComp.inductionOn with
  | pure out => exact zero_le
  | query_bind t f ih =>
    rcases t with (q | outbox) | input
    · change costWith _ (liftM ((LocalSpec C).query q) >>= fun r => advance (f r)) rest ≤
        cost partyCharge (liftM ((PartySpec C E RealSpec).query (.inl (.inl q))) >>= f)
      rw [costWith_query_bind, cost, costWith_query_bind]
      exact add_le_add le_rfl (iSup_mono ih)
    · change rest (Step.wait outbox f) ≤ cost partyCharge (liftM ((PartySpec C E RealSpec).query (.inl (.inr outbox))) >>= f)
      rw [cost, costWith_query_bind]
      simp [rest, cost]
    · exact input.elim

variable {Ro : Roles C (TableM C)}
  (hadv : ∀ {β : Type} (oa : OracleComp (LocalSpec C) β) (k : β → ℕ∞),
    TableCost (Ro.adversary oa) k (costWith (fun t => (ownCost t : ℕ∞)) oa k))
  (hhon : ∀ {β : Type} (oa : OracleComp (LocalSpec C) β) (k : β → ℕ∞),
    TableCost (Ro.honest oa) k (costWith (fun t => (honestCost t : ℕ∞)) oa k))

include hhon in
theorem tableCost_honest_advance {α : Type} (p : OracleComp (PartySpec C E RealSpec) (Option α)) :
    TableCost (Ro.honest (advance p)) rest (cost partyCharge p) :=
  (hhon _ _).mono (fun _ => le_rfl) (costWith_advance p)

/-- The steps of `sequenceFin` add their costs. -/
theorem TableCost.sequenceFin {β : Type} (R : β → ℕ∞) :
    ∀ {N : ℕ} (g : Fin N → TableM C β) (B : Fin N → ℕ∞), (∀ i, TableCost (g i) R (B i)) →
      TableCost (HashSig.OverPermutation.sequenceFin g) (fun st => ∑ i, R (st i)) (∑ i, B i)
  | 0, g, B, _ => by
    rw [HashSig.OverPermutation.sequenceFin]
    simpa using TableCost.pure (C := C) (Fin.elim0 : Fin 0 → β) (fun st => ∑ i, R (st i))
  | N + 1, g, B, h => by
    rw [HashSig.OverPermutation.sequenceFin, Fin.sum_univ_succ]
    refine TableCost.bind (K := fun a => R a + ∑ i : Fin N, B i.succ) ?_ fun a => ?_
    · exact (h 0).frame _
    · refine TableCost.bind (K := fun tail => ∑ i : Fin N, R (tail i) + R a)
        (((TableCost.sequenceFin R (fun i => g i.succ) (fun i => B i.succ) fun i => h i.succ).frame (R a)).mono
          (fun _ => le_rfl) (le_of_eq (add_comm _ _))) fun tail => ?_
      refine (TableCost.pure _ _).mono (fun _ => le_rfl) (le_of_eq ?_)
      rw [Fin.sum_univ_succ, add_comm]
      rfl

variable {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
  (hround : ∀ state sent, cost (fun t => (ownCost t : ℕ∞)) (A.round state sent) ≤ step)

include hadv hhon hround in
/-- One round costs one round of the adversary and spends the rests of the honest programs. -/
theorem stepRound_cost {α : Type} (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    TableCost (stepRound Ro D A noFunctionality state steps) (fun r => ∑ j, rest (r.2.1 j))
      (step + ∑ j, rest (steps j)) := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [callInput_real])
  refine TableCost.bind (K := fun _ => ∑ j, rest (steps j)) ((hadv _ _).mono (fun _ => le_rfl)
    ((costWith_le_cost_add _ _).trans (add_le_add (hround _ _) iSup_const_le))) fun r => ?_
  obtain ⟨state', sent⟩ := r
  dsimp only
  refine TableCost.bind (K := fun st => ∑ j, rest (st j)) (TableCost.sequenceFin rest _ _ fun j => ?_)
    fun st => TableCost.pure _ _
  cases hs : steps j with
  | done out => exact TableCost.pure _ _
  | call input k => exact input.elim
  | wait outbox k =>
    dsimp only
    split_ifs
    · exact (TableCost.pure _ _).mono (fun _ => le_rfl) zero_le
    · exact (tableCost_honest_advance hhon _).mono (fun _ => le_rfl) (le_iSup (fun inbox => cost partyCharge (k inbox)) _)

include hadv hhon hround in
/-- At most `fuel` rounds cost `fuel` rounds of the adversary and the rests of the honest programs. -/
theorem executeRounds_cost {α : Type} :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      TableCost (executeRounds Ro D A noFunctionality fuel state steps) (fun _ => 0)
        (fuel * step + ∑ j, rest (steps j))
  | 0, state, steps => (TableCost.pure _ _).mono (fun _ => le_rfl) zero_le
  | fuel + 1, state, steps => by
    unfold executeRounds
    split_ifs
    · exact (TableCost.pure _ _).mono (fun _ => le_rfl) zero_le
    refine TableCost.bind (K := fun r => ∑ j, rest (r.2.1 j) + fuel * step)
      (((stepRound_cost hadv hhon D A step hround state steps).frame _).mono (fun _ => le_rfl) (le_of_eq ?_))
      fun r => ?_
    · push_cast
      ring
    obtain ⟨state', steps', sent⟩ := r
    exact (executeRounds_cost fuel state' steps').mono (fun _ => le_rfl) (le_of_eq (add_comm _ _))

include hhon in
/-- The first steps of the honest programs cost the programs up to their first rounds. -/
theorem startSteps_cost {α : Type} (program : C.Party → PartyM C E RealSpec α) :
    TableCost (startSteps Ro D program) (fun st => ∑ j, rest (st j))
      (∑ j, if j ∈ D.1 then 0 else cost partyCharge (program j).run) := by
  unfold startSteps
  refine TableCost.sequenceFin rest _ _ fun j => ?_
  split_ifs
  · exact TableCost.pure _ _
  · exact tableCost_honest_advance hhon _

include hadv hhon hround in
/-- A phase costs `fuel` rounds of the adversary and the costs of the honest programs. -/
theorem executePhase_cost {α : Type} (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec α)
    (B : C.Party → ℕ∞) (hB : ∀ j, j ∉ D.1 → cost partyCharge (program j).run ≤ B j) :
    TableCost (executePhase Ro D A noFunctionality fuel state program) (fun _ => 0) (fuel * step + ∑ j, B j) := by
  unfold executePhase
  refine TableCost.bind (K := fun st => fuel * step + ∑ j, rest (st j))
    (((startSteps_cost hhon D program).frame (fuel * step)).mono (fun _ => le_of_eq (add_comm _ _)) ?_)
    fun st => executeRounds_cost hadv hhon D A step hround fuel state st
  rw [add_comm]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
  split_ifs with hj
  · exact zero_le
  · exact hB j hj

end Network

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.executePhase_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.executePhase_cost
