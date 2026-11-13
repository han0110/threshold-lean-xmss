import ThresholdLeanXmssSecurity.Proof.LifetimeForgerReplay
import ThresholdLeanXmssSecurity.Proof.LifetimeJointLink
import ThresholdLeanXmssSecurity.Proof.LifetimeIdealBad

/-! # Restricted commutation for dealer precomputation -/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimePrecomputeSwap
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Query restrictions suffice for commutation of the complete adaptive programs.
Port of `Execution.commutes_simulateQ` with the two zero-query predicates. -/
theorem commutes_simulateQ_restrict {κ σ : Type} {spec : OracleSpec κ}
    (I : QueryImpl spec (StateT σ ProbComp)) (P Q : κ → Prop)
    (hI : ∀ t t', P t → Q t' → Commutes (I t) (I t'))
    {α β : Type} (oa : OracleComp spec α) (ob : OracleComp spec β)
    (hoa : IsQueryBoundP oa (fun t => ¬ P t) 0)
    (hob : IsQueryBoundP ob (fun t => ¬ Q t) 0) :
    Commutes (simulateQ I oa) (simulateQ I ob) := by
  have hquery : ∀ t, P t → ∀ {γ : Type} (oc : OracleComp spec γ),
      IsQueryBoundP oc (fun t => ¬ Q t) 0 → Commutes (I t) (simulateQ I oc) := by
    intro t ht γ oc hc
    induction oc using OracleComp.inductionOn with
    | pure b => rw [simulateQ_pure]; exact commutes_pure (I t) b
    | query_bind t' k ih =>
      rw [isQueryBoundP_query_bind_iff] at hc
      have ht' : Q t' := by simpa using hc.1
      rw [simulateQ_bind, simulateQ_query]
      exact ((hI t t' ht ht').map_right _).bind_right fun b => ih b (by simpa using hc.2 b)
  induction oa using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact (commutes_pure (simulateQ I ob) a).symm
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : P t := by simpa using hoa.1
    rw [simulateQ_bind, simulateQ_query]
    exact ((hquery t ht ob hob).map_left _).bind_left fun a => ih a (by simpa using hoa.2 a)

/-- A read and a programming attempt at different addresses commute. -/
theorem commutes_randomOracle_programAnswer (q : Query C) (x : Query C × HashOutput)
    (hne : q ≠ x.1) :
    Commutes ((Query C →ₒ HashOutput).randomOracle q) (programAnswer x) := by
  intro s
  simp only [randomOracle.apply_eq, programAnswer, StateT.run_bind, StateT.run_pure,
    StateT.run_get, pure_bind, bind_assoc]
  by_cases fixed : ∃ input, x.1 = .hash input ∧ MpcInput input
  · simp [fixed]
  · rcases hs : s q with _ | u <;> rcases hx : s x.1 with _ | v <;>
      simp [fixed, hs, hx, StateT.run_bind, StateT.run_modifyGet, StateT.run_set,
        StateT.run_pure, QueryCache.cacheQuery_of_ne _ _ hne,
        QueryCache.cacheQuery_of_ne _ _ hne.symm]
    simp only [show ∀ a, (s.cacheQuery q a).cacheQuery x.1 x.2 =
        (s.cacheQuery x.1 x.2).cacheQuery q a from
      fun a => Function.update_comm hne _ _ _]

/-- Dealer calls are free local calls outside the keygen derivation domain. -/
def DealerQuery : (WorldSpec C).Domain → Prop
  | .inr (.inl _) => True
  | .inr (.inr (.inl q)) => ¬ KeygenPoint q
  | .inr (.inr (.inr _)) => True
  | _ => False

/-- Fixed hash answers and reads away from the programmed point commute with programming. -/
theorem commutes_hashAnswer_programAnswer (prims : Primitives)
    (q : Query C) (x : Query C × HashOutput) (hne : q ≠ x.1) :
    Commutes (hashAnswer prims q) (programAnswer x) := by
  by_cases h : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := h
    rw [hashAnswer_of_isFixed prims hm]
    exact (commutes_pure _ _).symm
  · rw [hashAnswer_of_not_isFixed prims h]
    exact commutes_randomOracle_programAnswer q x hne

/-- A dealer call commutes with local calls and keygen-only programming. -/
theorem commutes_dealer_world (prims : Primitives) {t t' : (WorldSpec C).Domain}
    (ht : DealerQuery t) (ht' : ¬ LifetimeJointLink.OtherProgram t') :
    Commutes (worldAnswer prims t) (worldAnswer prims t') := by
  rcases t with (t | x) | t
  · simp [DealerQuery] at ht
  · simp [DealerQuery] at ht
  · rcases t' with (t' | x) | t'
    · exact commutes_of_isAtom (isAtom_localAnswer prims t) (isAtom_localAnswer prims t')
    · have hx : KeygenPoint x.1 := by simpa [LifetimeJointLink.OtherProgram] using ht'
      rcases t with n | q | y
      · exact commutes_private_stateT _ _
      · exact commutes_hashAnswer_programAnswer prims q x (fun he => ht (he ▸ hx))
      · have hne : Query.streamKey y.2.1 ≠ x.1 := by
          intro he
          have := he ▸ (show ¬ KeygenPoint (Query.streamKey (C := C) y.2.1) by simp [KeygenPoint])
          exact this hx
        change Commutes (prgAnswer prims y) (programAnswer x)
        simpa [prgAnswer, map_eq_bind_pure_comp] using
          (commutes_hashAnswer_programAnswer prims (.streamKey y.2.1) x hne).map_left
            (fun d => prims.aes.eval (truncateHash d) y.2.2)
    · exact commutes_of_isAtom (isAtom_localAnswer prims t) (isAtom_localAnswer prims t')

/-- A discarded dealer computation can be moved after the observed world output. -/
theorem evalDist_world_ghost (prims : Primitives) {α β : Type}
    (G : OracleComp (WorldSpec C) α) (R : OracleComp (WorldSpec C) β)
    (hG : IsQueryBoundP G (fun t => ¬ DealerQuery t) 0)
    (hR : IsQueryBoundP R LifetimeJointLink.OtherProgram 0) (c : HashCache C) :
    𝒟[(simulateQ (worldAnswer prims) (G >>= fun _ => R)).run' c] =
      𝒟[(simulateQ (worldAnswer prims) R).run' c] := by
  have h := commutes_simulateQ_restrict (worldAnswer prims) DealerQuery
    (fun t => ¬ LifetimeJointLink.OtherProgram t)
    (fun _ _ => commutes_dealer_world prims) G R hG (by simpa using hR)
  have he := (h.bind (fun _ b => pure b)) c
  have he' := congrArg (fun d : SPMF (β × HashCache C) => Prod.fst <$> d) he
  simp only [← evalDist_map, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure] at he'
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]
  refine he'.trans ?_
  apply evalDist_bind_congr
  intro r hr
  exact SwapPort.evalDist_bind_ignore _ _


open LifetimeIdealBad

/-- Keygen derivation calls in the dealer's oracle interface. -/
def RoKeygen : (RoSpec C).Domain → Prop
  | .inl q => KeygenPoint q
  | .inr _ => False

section Writer
variable {ι ω : Type} {spec : OracleSpec ι} [EmptyCollection ω] [Append ω] (P : ι → Prop)

/-- A writer computation makes no query selected by P. -/
def WriterQuiet {α : Type} (p : WriterT ω (OracleComp spec) α) : Prop :=
  IsQueryBoundP p.run P 0

private theorem w_pure {α : Type} (a : α) :
    WriterQuiet (spec := spec) (ω := ω) P (pure a) := isQueryBoundP_pure _ _ _

private theorem w_bind {α β : Type} {p : WriterT ω (OracleComp spec) α}
    {f : α → WriterT ω (OracleComp spec) β}
    (hp : WriterQuiet P p) (hf : ∀ a, WriterQuiet P (f a)) :
    WriterQuiet P (p >>= f) := by
  unfold WriterQuiet at *
  rw [WriterT.run_bind]
  apply zero_bind P hp
  intro a ha
  exact (isQueryBoundP_map_iff _ _ _).2 (hf a.1)

omit [Append ω] in
private theorem w_lift {α : Type} (p : OracleComp spec α)
    (hp : IsQueryBoundP p P 0) : WriterQuiet (spec := spec) (ω := ω) P (liftM p) := by
  exact (isQueryBoundP_map_iff _ _ _).2 hp

private theorem w_mapM [LawfulMonad (WriterT ω (OracleComp spec))] {α β : Type} (xs : List α) (f : α → WriterT ω (OracleComp spec) β)
    (hf : ∀ a, WriterQuiet P (f a)) : WriterQuiet P (xs.mapM f) := by
  induction xs with
  | nil => exact w_pure P _
  | cons a xs ih =>
    rw [List.mapM_cons]
    exact w_bind P (hf a) fun _ => w_bind P ih fun _ => w_pure P _

/-- Writer port of LifetimeIdealBad.ceremonyOutput_quiet, retaining its output log. -/
theorem ceremonyOutput_writer_quiet
    (hashLift : ∀ {α : Type}, OracleComp HashSpec α → WriterT ω (OracleComp spec) α)
    (hhash : ∀ {α : Type} (p : OracleComp HashSpec α), WriterQuiet P (hashLift p))
    (run : List Job → WriterT ω (OracleComp spec) (Option (List (List Bit))))
    (hrun : ∀ jobs, WriterQuiet P (run jobs))
    (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    WriterQuiet P (ceremonyOutput hashLift parameter run top tree) := by
  unfold ceremonyOutput
  cases tree with
  | top =>
    apply w_bind P (hrun topJobs)
    rintro (_ | outputs)
    · exact w_pure P _
    exact w_bind P (hhash _) fun _ => w_pure P _
  | bottom b =>
    apply w_bind P (hrun (bottomJobs b))
    rintro (_ | outputs)
    · exact w_pure P _
    apply w_bind P (hhash _)
    intro root
    apply w_bind P (hhash _)
    intro base
    apply w_bind P (hhash _)
    rintro (_ | ⟨randomness, encoding⟩)
    · exact w_pure P _
    apply w_bind P (hrun _)
    rintro (_ | values)
    · exact w_pure P _
    apply w_bind P (hhash _)
    intro path
    apply w_bind P (hhash _)
    intro topRoot
    split <;> exact w_pure P _
end Writer

/-- HashSpec calls use only the structured hash domain, never keygen derivation. -/
theorem tweakable_noKeygen {α : Type} (p : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable (C := C) p) RoKeygen 0 := by
  apply LifetimeKeygenPrograms.qb0_simulateQ
  intro t
  exact (isQueryBoundP_query_iff _ _ _).2 (by simp [RoKeygen, KeygenPoint])

/-- Evaluating cleartext jobs uses PRF calls, not keygen derivation calls. -/
theorem evalJob_noKeygen (circuits : Circuits) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (job : Job) :
    IsQueryBoundP (evalJob circuits parameter seeds job) RoKeygen 0 := by
  unfold evalJob
  apply zero_bind RoKeygen (zero_mapM _ _ _ fun x => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  unfold prfValue
  apply zero_bind RoKeygen (zero_mapM _ _ _ fun T => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  apply (isQueryBoundP_map_iff _ _ _).2
  exact (isQueryBoundP_query_iff _ _ _).2 (by simp [RoKeygen, KeygenPoint])

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- The full dealer, including the writer log of openings, never derives keygen keys. -/
theorem dealerCeremony_noKeygen (circuits : Circuits) (settings : Settings)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    IsQueryBoundP (dealerCeremony circuits settings parameter seeds top tree) RoKeygen 0 := by
  refine ceremonyOutput_writer_quiet (spec := RoSpec C)
    (ω := List (List (List Bit))) RoKeygen
    (fun oa => liftM (tweakable (C := C) oa)) ?_
    (batched settings.batchSize fun jobs => do
      let outputs ← liftM (jobs.mapM (evalJob circuits parameter seeds))
      tell [outputs]
      pure (some outputs)) ?_ parameter top tree
  · intro α p
    exact w_lift RoKeygen _ (tweakable_noKeygen p)
  intro jobs
  unfold batched
  apply w_bind RoKeygen (w_mapM _ _ _ fun js => ?_) fun _ => w_pure RoKeygen _
  apply w_bind RoKeygen (w_lift _ _ (zero_mapM _ _ _ (evalJob_noKeygen circuits parameter seeds)))
  intro outputs
  apply w_bind RoKeygen
  · exact isQueryBoundP_pure _ _ _
  intro _
  exact w_pure RoKeygen _

/-- Lifting a separated dealer computation into the world preserves its query restriction. -/
theorem free_ro_dealerQuery {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoKeygen 0) :
    IsQueryBoundP (free (liftComp p (LocalSpec C))) (fun t => ¬ DealerQuery t) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ RoKeygen t := hp.1.resolve_right (by omega)
    rw [liftComp_bind, free_bind]
    rcases t with q | y
    · change IsQueryBoundP ((OracleComp.lift (OracleSpec.query
        (spec := WorldSpec C) (.inr (.inr (.inl q))))) >>= _) (fun t => ¬ DealerQuery t) 0
      apply (isQueryBoundP_query_bind_iff _ _ _ _).2
      refine ⟨Or.inl (by simpa [DealerQuery, RoKeygen] using ht), fun u => ?_⟩
      simpa [RoKeygen, ht] using ih u (by simpa [ht] using hp.2 u)
    · change IsQueryBoundP ((OracleComp.lift (OracleSpec.query
        (spec := WorldSpec C) (.inr (.inr (.inr y))))) >>= _) (fun t => ¬ DealerQuery t) 0
      apply (isQueryBoundP_query_bind_iff _ _ _ _).2
      refine ⟨Or.inl (by simp [DealerQuery]), fun u => ?_⟩
      simpa [RoKeygen] using ih u (by simpa [ht] using hp.2 u)

set_option maxRecDepth 4000 in
/-- Every call in the complete precomputed table is a separated dealer call. -/
theorem free_dealerTables_dealerQuery (circuits : Circuits) (settings : Settings)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    IsQueryBoundP (free (liftComp
      (LifetimeForgerReplay.dealerTables circuits settings parameter seeds) (LocalSpec C)))
      (fun t => ¬ DealerQuery t) 0 := by
  apply free_ro_dealerQuery
  unfold LifetimeForgerReplay.dealerTables
  apply zero_bind RoKeygen (dealerCeremony_noKeygen circuits settings parameter seeds emptyTop .top) 
  intro top ht
  have hmap (bs : List (Fin (2 ^ layerHeight))) : IsQueryBoundP
      (bs.mapM fun b => dealerCeremony circuits settings parameter seeds
        ((TreeOutput.topTree top.1).getD emptyTop) (.bottom b)) RoKeygen 0 :=
    zero_mapM RoKeygen bs
    (fun b => dealerCeremony circuits settings parameter seeds
      ((TreeOutput.topTree top.1).getD emptyTop) (.bottom b))
    (fun b => dealerCeremony_noKeygen circuits settings parameter seeds
      ((TreeOutput.topTree top.1).getD emptyTop) (.bottom b))
  generalize List.finRange (2 ^ layerHeight) = bs
  exact zero_bind RoKeygen (hmap bs) fun bottoms hb => isQueryBoundP_pure _ _ _

end ThresholdLeanXmssSecurity.LifetimePrecomputeSwap

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_simulateQ_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_simulateQ_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_randomOracle_programAnswer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_randomOracle_programAnswer

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_hashAnswer_programAnswer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_hashAnswer_programAnswer

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_dealer_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.commutes_dealer_world

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.evalDist_world_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.evalDist_world_ghost

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.ceremonyOutput_writer_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.ceremonyOutput_writer_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.tweakable_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.tweakable_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.evalJob_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.evalJob_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.dealerCeremony_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.dealerCeremony_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.free_ro_dealerQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.free_ro_dealerQuery

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.free_dealerTables_dealerQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimePrecomputeSwap.free_dealerTables_dealerQuery

