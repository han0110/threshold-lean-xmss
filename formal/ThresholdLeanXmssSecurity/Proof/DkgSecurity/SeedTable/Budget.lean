import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.IdealCoupling
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Cost
import ThresholdLeanXmssSecurity.Proof.SigningStronglyUnforgeable

/-!
# The budget of the table adversary

Only a call of the class of the seed generation and the private sampling of `tableNet` and of a rest
on `tableWorld` reach the outer oracles. A private sample is no counted call.

* `cost_tableLocal` bounds the counted calls of a computation under the private table by its
  `ownCost`.
* `cost_tableWorld` bounds the counted calls of a rest with reads on `tableWorld` by its calls of
  the class (`classCharge`), on both copies.
* `isQueryBounded_table` gives the budget of `tableNet` with a distinguisher from the budget of the
  adversary and a bound on the counted calls of the distinguisher.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open PFunctor.FreeM (costWith cost costWith_mono costWith_le_cost_add)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

open SeedPartition SeedEmulation
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.Partitioned (isPrivate)

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- A counted call costs one. -/
def countedCharge (t : (LocalSpec C).Domain) : ℕ∞ := ((if Counted t then 1 else 0 : ℕ) : ℕ∞)

theorem isQueryBoundP_of_cost {α : Type} {oa : OracleComp (LocalSpec C) α} {n : ℕ}
    (h : cost countedCharge oa ≤ n) : IsQueryBoundP oa Counted n :=
  (SigningStronglyUnforgeable.isQueryBoundP_iff_queryCostAtMost oa Counted n).2 ((queryCostAtMost_iff_cost_le _ _ _).2 h)

/-- Private sampling is no counted call. -/
theorem cost_liftComp_counted {α : Type} (p : ProbComp α) :
    cost (countedCharge (C := C)) (liftComp p (LocalSpec C)) ≤ 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact cost_pure_le _ _ _
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inl t)) : OracleComp (LocalSpec C) _) >>= fun u => liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    refine (cost_bind_le_add (n := 0) (m := 0) ((cost_query_le (c := countedCharge (C := C)) (.inl t)).trans
      (by simp [countedCharge, Counted])) ih).trans (by simp)

theorem countedCharge_le_ownCost (t : (LocalSpec C).Domain) : countedCharge t ≤ (ownCost t : ℕ∞) := by
  rcases t with n | q | x
  · simp [countedCharge, ownCost, Counted]
  · unfold countedCharge ownCost
    split_ifs <;> simp
  · unfold countedCharge ownCost
    split_ifs <;> simp

variable (prims : Primitives)

/-- The counted calls of a computation under the private table are at most its own calls. -/
theorem cost_tableLocal {α : Type} (oa : OracleComp (LocalSpec C) α) (T : HashCache C) :
    cost countedCharge ((simulateQ (Partitioned.tableLocal seedGenOutside prims) oa).run T) ≤
      cost (fun t => (ownCost t : ℕ∞)) oa := by
  induction oa using OracleComp.inductionOn generalizing T with
  | pure a => exact cost_pure_le _ _ _
  | query_bind t k ih =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    have hk : cost (fun t => (ownCost t : ℕ∞)) (liftM (OracleSpec.query t) >>= k) =
        (ownCost t : ℕ∞) + ⨆ u, cost (fun t => (ownCost t : ℕ∞)) (k u) := by
      rw [cost, costWith_query_bind]
      rfl
    rw [hk]
    refine cost_bind_le_add ?_ fun a => (ih a.1 a.2).trans (le_iSup (fun u => cost _ (k u)) a.1)
    by_cases hp : isPrivate seedGenOutside t = true
    · have e : (Partitioned.tableLocal seedGenOutside prims t).run T =
          liftComp ((localAnswer prims t).run T) (LocalSpec C) := by
        simp [Partitioned.tableLocal, hp]
      rw [e]
      exact (cost_liftComp_counted _).trans bot_le
    · have hf : isPrivate seedGenOutside t = false := by simpa using hp
      have e : (Partitioned.tableLocal seedGenOutside prims t).run T =
          (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _) >>= fun a => pure (a, T) := by
        simp only [Partitioned.tableLocal, hf, Bool.false_eq_true, ite_false]
        rw [StateT.run_monadLift, monadLift_self]
      rw [e]
      refine (cost_bind_le_add (m := 0) (cost_query_le _) fun _ => cost_pure_le _ _ _).trans ?_
      simpa using countedCharge_le_ownCost t

/-- A call of `H` in the class of the seed generation, on either copy, costs one. Every other query
of a rest with reads costs nothing. -/
def classCharge : (PeekSpec C).Domain → ℕ∞
  | .inl (.inl (.inl (.inr (.inl q)))) => if isSeedGenQuery q then 1 else 0
  | .inl (.inr (.inr (.inl q))) => if isSeedGenQuery q then 1 else 0
  | _ => 0

/-- The counted calls of one local call under the private table. -/
def localClass : (LocalSpec C).Domain → ℕ∞
  | .inr (.inl q) => if isSeedGenQuery q then 1 else 0
  | _ => 0

theorem cost_tableLocal_step (u : (LocalSpec C).Domain) (T : HashCache C) :
    cost countedCharge ((Partitioned.tableLocal seedGenOutside prims u).run T) ≤ localClass u := by
  by_cases hp : isPrivate seedGenOutside u = true
  · have e : (Partitioned.tableLocal seedGenOutside prims u).run T =
        liftComp ((localAnswer prims u).run T) (LocalSpec C) := by
      simp [Partitioned.tableLocal, hp]
    rw [e]
    exact (cost_liftComp_counted _).trans bot_le
  · have hf : isPrivate seedGenOutside u = false := by simpa using hp
    have e : (Partitioned.tableLocal seedGenOutside prims u).run T =
        (liftM ((LocalSpec C).query u) : OracleComp (LocalSpec C) _) >>= fun a => pure (a, T) := by
      simp only [Partitioned.tableLocal, hf, Bool.false_eq_true, ite_false]
      rw [StateT.run_monadLift, monadLift_self]
    rw [e]
    refine (cost_bind_le_add (m := 0) (cost_query_le _) fun _ => cost_pure_le _ _ _).trans ?_
    rcases u with n | q | x
    · simp [countedCharge, Counted]
    · have hq : isSeedGenQuery q = true := by simpa [isPrivate, seedGenOutside] using hf
      cases q <;> simp_all [countedCharge, Counted, localClass, isSeedGenQuery]
    · simp [isPrivate, seedGenOutside, isSeedGenQuery] at hf

/-- The counted calls of a rest with reads on `tableWorld` are its calls of the class. -/
theorem cost_tableWorld (D : C.Coalition) {α : Type} (P : OracleComp (PeekSpec C) α) (w : StreamState C) :
    cost countedCharge ((simulateQ (withPeek (tableWorld prims D) id) P).run w) ≤ cost classCharge P := by
  have local_le : ∀ (u : (LocalSpec C).Domain) (T : HashCache C) (H : HiddenCache C) (c : ℕ∞),
      localClass u ≤ c → cost countedCharge ((fun r => (r.1, (r.2, H))) <$>
        (DkgSecurityProof.tableLocal prims u).run T) ≤ c := fun u T H c hc => by
    rw [tableLocal_eq]
    exact cost_map_le _ ((cost_tableLocal_step prims u T).trans hc)
  induction P using OracleComp.inductionOn generalizing w with
  | pure a => exact cost_pure_le _ _ _
  | query_bind t k ih =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    have hk : cost classCharge (liftM (OracleSpec.query t) >>= k) =
        classCharge t + ⨆ u, cost classCharge (k u) := by
      rw [cost, costWith_query_bind]
      rfl
    rw [hk]
    refine cost_bind_le_add ?_ fun a => (ih a.1 a.2).trans (le_iSup (fun u => cost _ (k u)) a.1)
    obtain ⟨T, H⟩ := w
    rcases t with ((((n | q | x) | p) | (n | q | x)) | u)
    · exact local_le (.inl n) T H _ (by simp [localClass])
    · exact local_le (.inr (.inl q)) T H _ (by simp [localClass, classCharge])
    · exact local_le (.inr (.inr x)) T H _ (by simp [localClass])
    · exact cost_pure_le _ _ _
    · exact local_le (.inl n) T H _ (by simp [localClass])
    · exact local_le (.inr (.inl q)) T H _ (by simp [localClass, classCharge])
    · change cost countedCharge ((tableWorld prims D (.inr (.inr (.inr x)))).run (T, H)) ≤ _
      simp only [tableWorld]
      split_ifs
      · exact cost_map_le _ ((cost_liftComp_counted _).trans bot_le)
      · exact local_le (.inr (.inr x)) T H _ (by simp [localClass])
    · change cost countedCharge (((fun w => blind (id w)) <$> get : StateT (StreamState C)
        (OracleComp (LocalSpec C)) _).run (T, H)) ≤ _
      simp only [StateT.run_map, StateT.run_get]
      exact cost_map_le _ (cost_pure_le _ _ _)

/-- The budget of `tableNet` with a distinguisher, from the budget of the start and the rounds of the
adversary and a count of the counted calls of the distinguisher. -/
theorem isQueryBounded_table (net : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C (tableNet prims net).State (Keys C)) (start step final q : ℕ)
    (hq : start + setupRounds * step + final ≤ q)
    (hstart : ∀ x z, QueryCostAtMost (net.start x z) ownCost start)
    (hround : ∀ state sent, QueryCostAtMost (net.round state sent) ownCost step)
    (hZ : ∀ r, IsQueryBoundP (Z r) Counted final) :
    IsQueryBounded (tableNet prims net) Z setupRounds q := by
  refine ⟨start, step, final, hq, fun x z => ?_, fun st sent => ?_, fun _ l => l.elim, hZ⟩
  · have h := isQueryBoundP_of_cost ((cost_tableLocal prims (net.start x z) ∅).trans
      ((queryCostAtMost_iff_cost_le _ _ _).1 (hstart x z)))
    rw [← tableNet_start] at h
    exact h
  · have h := isQueryBoundP_of_cost (cost_map_le (fun r => ((r.1.1, r.2), r.1.2))
      ((cost_tableLocal prims (net.round st.1 sent) st.2).trans
        ((queryCostAtMost_iff_cost_le _ _ _).1 (hround st.1 sent))))
    rw [tableNet_round prims net st sent]
    exact h

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.isQueryBounded_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.isQueryBounded_table

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.cost_tableWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.cost_tableWorld
