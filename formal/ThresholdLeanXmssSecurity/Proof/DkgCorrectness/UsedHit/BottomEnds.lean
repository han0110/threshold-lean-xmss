import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Bottom
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopCosts

/-!
# The end points of the two numberings

Each run that `mayRun` allows starts with at most `runLimit` runs of each tree, so each of its slots is
below `gameSetups runLimit` in both numberings (`slots_lt_gameSetups`). At the end point both hybrids
draw fresh keys for each such slot, so a run is the same program in both (`fixedTreeRun_eq_hybrid`).
The bound of the runs holds through the whole game, and `endPointsAgree` proves `EndPointsAgree`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

/-- Two handlers that agree from each state with an invariant, and the first keeps the invariant. Then
the two simulations agree from each such state. -/
theorem simulateQ_run_congr_inv {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {τ σ α : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT τ (StateT σ (OracleComp spec')))) (Inv : σ → Prop)
    (hagree : ∀ t st s, Inv s → ((impl₁ t).run st).run s = ((impl₂ t).run st).run s)
    (hinv : ∀ t st s, Inv s → ∀ r ∈ support (((impl₁ t).run st).run s), Inv r.2)
    (oa : OracleComp spec α) :
    ∀ st s, Inv s → ((simulateQ impl₁ oa).run st).run s = ((simulateQ impl₂ oa).run st).run s := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st s _; simp
  | query_bind t k ih =>
    intro st s hs
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind, StateT.run_bind,
      StateT.run_bind]
    calc ((impl₁ t).run st).run s >>= (fun p => ((simulateQ impl₁ (k p.1.1)).run p.1.2).run p.2)
        = ((impl₁ t).run st).run s >>= (fun p => ((simulateQ impl₂ (k p.1.1)).run p.1.2).run p.2) :=
          bind_congr_of_forall_mem_support _ fun p hp => ih p.1.1 p.1.2 p.2 (hinv t st s hs p hp)
      _ = ((impl₂ t).run st).run s >>= (fun p => ((simulateQ impl₂ (k p.1.1)).run p.1.2).run p.2) := by
          rw [hagree t st s hs]

theorem lift_run_congr {τ σ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (x y : StateT σ m α)
    (st : τ) (s : σ) (h : x.run s = y.run s) :
    ((StateT.lift x : StateT τ (StateT σ m) α).run st).run s = ((StateT.lift y : StateT τ (StateT σ m) α).run st).run s := by
  simp only [StateT.run_lift, StateT.run_bind, h]

theorem stateT_run_bind_congr {σ α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (x y : StateT σ m α)
    (k : α → StateT σ m β) (s : σ) (h : x.run s = y.run s) : (x >>= k).run s = (y >>= k).run s := by
  rw [StateT.run_bind, StateT.run_bind, h]

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- Each tree has at most `runLimit` runs. -/
def RunsBounded {σ : Type} (s : RealState C σ) : Prop := ∀ t, s.runs t ≤ runLimit

/-- Each slot of a run that starts with fewer than `runLimit` runs of its tree, and with at most
`runLimit` runs of each tree, is below `gameSetups` in both numberings. -/
theorem slots_lt_gameSetups (runs : Tree → ℕ) (hle : ∀ t, runs t ≤ runLimit) (tree : Tree)
    (hlt : runs tree < runLimit) (c : ℕ) (hc : c < treeSetups tree) :
    fixedSlot runLimit runs tree + c < gameSetups runLimit ∧ setupsBefore runs + c < gameSetups runLimit := by
  have hsum : ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) * treeSetups (.bottom b) =
      2 * ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) := by
    simp only [treeSetups, Finset.mul_sum, Nat.mul_comm]
  have hall : ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) ≤ runLimit * 2 ^ layerHeight := by
    calc ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) ≤ ∑ _b : Fin (2 ^ layerHeight), runLimit :=
          Finset.sum_le_sum fun b _ => hle _
      _ = runLimit * 2 ^ layerHeight := by simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
  simp only [fixedSlot, setupsBefore, gameSetups, hsum] at hc ⊢
  cases tree with
  | top =>
    simp only [treeSetups] at hc ⊢
    generalize ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) = T at hall ⊢
    generalize 2 ^ layerHeight = B at hall ⊢
    constructor <;> nlinarith
  | bottom b =>
    have hone : ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) + 1 ≤ runLimit * 2 ^ layerHeight := by
      have := Finset.sum_lt_sum (s := Finset.univ) (f := fun b' : Fin (2 ^ layerHeight) => runs (.bottom b'))
        (g := fun _ => runLimit) (fun b' _ => hle _) ⟨b, Finset.mem_univ _, hlt⟩
      simpa [Finset.sum_const, Finset.card_univ, Nat.mul_comm] using this
    simp only [treeSetups] at hc ⊢
    have htop := hle .top
    generalize ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) = T at hone ⊢
    generalize 2 ^ layerHeight = B at hone ⊢
    constructor <;> nlinarith

theorem sampleSlot_gameSetups (x : ℕ) (hx : x < gameSetups runLimit) :
    sampleSlot (C := C) (gameSetups runLimit) x = some <$> sampleFresh := by
  simp only [sampleSlot, hx, ite_true]

/-- At the end point a run that `mayRun` allows is the same program in both numberings. -/
theorem fixedTreeRun_eq_hybrid (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (hs : RunsBounded runLimit s) (hlt : s.runs tree < runLimit) :
    (fixedTreeRun K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree).run s =
      (hybridTreeRun K circuits settings (gameSetups runLimit) (wrongOutput D) D net tree).run s := by
  have e : (List.range (treeSetups tree)).mapM
        (fun c => sampleSlot (C := C) (gameSetups runLimit) (fixedSlot runLimit s.runs tree + c)) =
      (List.range (treeSetups tree)).mapM
        (fun c => sampleSlot (C := C) (gameSetups runLimit) (setupsBefore s.runs + c)) := by
    refine TprfSecurityProof.mapM_congr_mem fun c hc => ?_
    have h := slots_lt_gameSetups runLimit s.runs hs tree hlt c (List.mem_range.1 hc)
    rw [sampleSlot_gameSetups runLimit _ h.1, sampleSlot_gameSetups runLimit _ h.2]
  simp only [fixedTreeRun, hybridTreeRun, StateT.run_bind, StateT.run_get, pure_bind, e]

/-- A run adds one to the runs of its tree, so a run that `mayRun` allows keeps the bound. -/
theorem fixedTreeRun_bounded (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (hs : RunsBounded runLimit s) (hlt : s.runs tree < runLimit) :
    ∀ r ∈ support ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net tree).run s),
      RunsBounded runLimit r.2 := by
  intro r hr t
  rw [fixedTreeRun_runs K circuits settings runLimit j D net tree s r hr]
  by_cases ht : t = tree
  · subst ht
    simp only [Function.update_self]
    omega
  · rw [Function.update_of_ne ht]
    exact hs t

/-- At the end point the runs of a tree are the same program in both numberings, and keep the bound. -/
theorem fixedTreeRuns_eq_hybrid (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ (count : ℕ) (s : RealState C net.State), RunsBounded runLimit s →
      (fixedTreeRuns K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree count).run s =
        (hybridTreeRuns K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree count).run s ∧
      ∀ r ∈ support ((fixedTreeRuns K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree
        count).run s), RunsBounded runLimit r.2
  | 0, s, hs => by
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [fixedTreeRuns, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact hs
  | count + 1, s, hs => by
    simp only [fixedTreeRuns, hybridTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hm
    · have hlt := FirstCounts.mayRun_lt runLimit hm
      rw [StateT.run_bind, StateT.run_bind]
      refine ⟨?_, fun r hr => ?_⟩
      · calc (fixedTreeRun K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree).run s >>=
              (fun p => (fixedTreeRuns K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree
                count).run p.2)
            = (fixedTreeRun K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree).run s >>=
              (fun p => (hybridTreeRuns K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net tree
                count).run p.2) :=
              bind_congr_of_forall_mem_support _ fun p hp => (fixedTreeRuns_eq_hybrid D net tree count p.2
                (fixedTreeRun_bounded K circuits settings runLimit _ D net tree s hs hlt p hp)).1
          _ = _ := by rw [fixedTreeRun_eq_hybrid K circuits settings runLimit D net tree s hs hlt]
      · rw [mem_support_bind_iff] at hr
        obtain ⟨p, hp, hr⟩ := hr
        exact (fixedTreeRuns_eq_hybrid D net tree count p.2
          (fixedTreeRun_bounded K circuits settings runLimit _ D net tree s hs hlt p hp)).2 r hr
    · refine ⟨rfl, fun r hr => ?_⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
      exact hs

/-- At the end point a request of a bottom tree is the same program in both numberings, and keeps the
bound. -/
theorem fixedTreeRequest_eq_hybrid (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (s : RealState C net.State) (hs : RunsBounded runLimit s) :
    (fixedTreeRequest K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net b).run s =
        (hybridTreeRequest K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net b).run s ∧
      ∀ r ∈ support ((fixedTreeRequest K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D net
        b).run s), RunsBounded runLimit r.2 := by
  obtain ⟨heq, hbd⟩ := fixedTreeRuns_eq_hybrid K circuits settings runLimit D net (.bottom b) 1 s hs
  unfold fixedTreeRequest hybridTreeRequest
  rw [StateT.run_bind, StateT.run_bind, heq]
  refine ⟨rfl, fun r hr => ?_⟩
  rw [← heq, mem_support_bind_iff] at hr
  obtain ⟨p, hp, hr⟩ := hr
  rw [(requestRest_adds D b p.2).2 r hr]
  exact hbd p hp

/-- At the end point the signing phase is the same program in both numberings from each state with the
bound. -/
theorem fixedSigning_eq_hybrid (D : C.Coalition) (A : DkgTsigAdversary C E) (s : RealState C A.net.State)
    (hs : RunsBounded runLimit s) :
    (fixedSigning K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A).run s =
      (hybridSigning K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A).run s := by
  unfold fixedSigning hybridSigning
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases topHolder D s.operators with _ | ⟨keys, top⟩
  · rfl
  · refine stateT_run_bind_congr _ _ _ s ?_
    refine simulateQ_run_congr_inv _ _ (RunsBounded runLimit) (fun t st s' hs' => ?_) (fun t st s' hs' r hr => ?_)
      _ _ _ hs
    · rcases t with t | q | q
      · change ((StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) :
          StateT (TsigState C) (RealM C A.net.State) _).run st).run s' =
          ((StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) :
          StateT (TsigState C) (RealM C A.net.State) _).run st).run s'
        rfl
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · change ((pure (noAnswer (.corrupt i)) : StateT (TsigState C) (RealM C A.net.State) _).run st).run s' =
            ((pure (noAnswer (.corrupt i)) : StateT (TsigState C) (RealM C A.net.State) _).run st).run s'
          rfl
        · exact lift_run_congr _ _ st s' (fixedTreeRequest_eq_hybrid K circuits settings runLimit D A.net b s' hs').1
        · change ((signRequest D i e (.round1 i J e message)).run st).run s' =
            ((signRequest D i e (.round1 i J e message)).run st).run s'
          rfl
        · change ((signRequest D i e (.round2 i J e message parts)).run st).run s' =
            ((signRequest D i e (.round2 i J e message parts)).run st).run s'
          rfl
      · rcases q with _ | state
        · change ((StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _)) :
            StateT (TsigState C) (RealM C A.net.State) _).run st).run s' =
            ((StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _)) :
            StateT (TsigState C) (RealM C A.net.State) _).run st).run s'
          rfl
        · change ((StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state }) :
            StateT (TsigState C) (RealM C A.net.State) _).run st).run s' =
            ((StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state }) :
            StateT (TsigState C) (RealM C A.net.State) _).run st).run s'
          rfl
    · rcases t with t | q | q
      · change r ∈ support (((StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift
          (OracleSpec.query t)))) : StateT (TsigState C) (RealM C A.net.State) _).run st).run s') at hr
        rw [run_lift_tsig, StateT.run_lift, support_map] at hr
        obtain ⟨p, hp, rfl⟩ := hr
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨_, _, rfl⟩ := hp
        exact hs'
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · change r ∈ support (((pure (noAnswer (.corrupt i)) : StateT (TsigState C) (RealM C A.net.State) _).run
            st).run s') at hr
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact hs'
        · change r ∈ support (((StateT.lift (fixedTreeRequest K circuits settings runLimit (gameSetups runLimit)
            (wrongOutput D) D A.net b) : StateT (TsigState C) (RealM C A.net.State) _).run st).run s') at hr
          rw [run_lift_tsig, support_map] at hr
          obtain ⟨p, hp, rfl⟩ := hr
          exact (fixedTreeRequest_eq_hybrid K circuits settings runLimit D A.net b s' hs').2 p hp
        · change r ∈ support (((signRequest D i e (.round1 i J e message)).run st).run s') at hr
          intro t'
          rw [(signRequest_quiet D i e (.round1 i J e message) st s').2 r hr]
          exact hs' t'
        · change r ∈ support (((signRequest D i e (.round2 i J e message parts)).run st).run s') at hr
          intro t'
          rw [(signRequest_quiet D i e (.round2 i J e message parts) st s').2 r hr]
          exact hs' t'
      · rcases q with _ | state
        · change r ∈ support (((StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _)) :
            StateT (TsigState C) (RealM C A.net.State) _).run st).run s') at hr
          rw [run_lift_tsig, support_map] at hr
          obtain ⟨p, hp, rfl⟩ := hr
          change p ∈ support (pure (s'.adversary, s') : OracleComp (WorldSpec C) _) at hp
          obtain rfl : p = (s'.adversary, s') := hp
          exact hs'
        · change r ∈ support (((StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state }) :
            StateT (TsigState C) (RealM C A.net.State) _).run st).run s') at hr
          rw [run_lift_tsig, support_map] at hr
          obtain ⟨p, hp, rfl⟩ := hr
          change p ∈ support (pure (PUnit.unit, { s' with adversary := state }) : OracleComp (WorldSpec C) _) at hp
          obtain rfl : p = (PUnit.unit, { s' with adversary := state }) := hp
          exact hs'

/-- `EndPointsAgree`. The end points of the fixed and of the old numbering have one probability. -/
theorem endPointsAgree (prims : Primitives) : EndPointsAgree K circuits settings runLimit prims := by
  intro D A
  have hrun : fixedRun K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A =
      hybridRun K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A := by
    unfold fixedRun hybridRun
    refine bind_congr fun p => ?_
    obtain ⟨state, keys⟩ := p
    dsimp only
    refine bind_congr fun v => ?_
    obtain ⟨state, ok⟩ := v
    dsimp only
    have hs : RunsBounded runLimit (seedState D state keys ok) := fun _ => Nat.zero_le _
    obtain ⟨heq, hbd⟩ := fixedTreeRuns_eq_hybrid K circuits settings runLimit D A.net .top runLimit _ hs
    rw [StateT.run_bind, StateT.run_bind]
    congr 1
    calc (fixedTreeRuns K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A.net .top
            runLimit).run (seedState D state keys ok) >>=
          (fun p => (fixedSigning K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A).run p.2)
        = (fixedTreeRuns K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A.net .top
            runLimit).run (seedState D state keys ok) >>=
          (fun p => (hybridSigning K circuits settings runLimit (gameSetups runLimit) (wrongOutput D) D A).run p.2) :=
          bind_congr_of_forall_mem_support _ fun p hp =>
            fixedSigning_eq_hybrid K circuits settings runLimit D A p.2 (hbd p hp)
      _ = _ := by rw [heq]
  unfold fixedProb hybridProb fixedGame hybridGame
  rw [hrun]

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.endPointsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.endPointsAgree
