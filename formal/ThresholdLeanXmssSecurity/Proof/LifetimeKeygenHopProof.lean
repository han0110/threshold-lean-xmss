import ThresholdLeanXmssSecurity.Proof.LifetimeHybridOrder
import ThresholdLeanXmssSecurity.Proof.KeygenAlias
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The lifetime keygen continuation

The all-emulated lifetime factors at the actual keygen output into its keygen
prefix and `afterKeygen`. A fixed local continuation forwards both ordinary
world copies to the same local oracle. It retains the lifetime's shared stream
table throughout the continuation. Capping this continuation and the keygen
adversary gives the D18 component budget `(setupRounds + 2) * Q`.

The real and dealer endpoints factor through the same concrete tail. Its
ordinary world copies are forwarded into the cache left by keygen; initializing
a fresh private keygen table at that boundary would not preserve this cache.
Two bounded tests stop with false or true on the first excess query. They
bracket the uncapped ideal test on every cache, while real reached-tail bounds
make both agree with the real test. Each direction costs one component error.

An ideal-tail cap-quiet premise is inappropriate: the keygen simulator ignores
failed programming, so its echoed parameter can disagree with the functionality's
returned parameter on that event. The lifetime adversary can branch on this
disagreement. The stopping-test sandwich needs no budget on such ideal outputs.
`KeygenCapQuiet` concerns only the keygen adversary, before this tail starts.

The pinned and current leanVM proof sources were searched for continuation
compilers and capped hybrids. The threshold scheduler and its keygen simulator
use the local component interfaces from `LifetimeJointLink`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeKeygenHopProof

open LifetimeHybridOrder LifetimeJointLink

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The real keygen prefix with exactly the base roles used by `afterKeygen`. -/
def keygenPrefix : EmulationM C (A.keygen.State × (C.Party → Option (Keys C))) := do
  let base := lifetimeHybridRoles D 0 0
  let state ← base.adversary (A.keygen.start (corruptInputs D fun _ => ()) [])
  executePhase base D A.keygen noFunctionality setupRounds state
    fun i => (keygen i : PartyM C E RealSpec (Keys C))

/-- The tail is the literal scheduler tail, including aborts and the forgery test. -/
theorem allEmulated_factor (circuits : Circuits) :
    lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D A =
      keygenPrefix D A >>= fun r => afterKeygen K settings attempts D A circuits r.1 r.2 := by
  simp only [lifetimeGameWith, keygenPrefix, afterKeygen, bind_assoc]
  apply bind_congr
  intro state
  apply bind_congr
  rintro ⟨state, outputs⟩
  rfl

/-- An ordinary world prefix shares its hash cache with the emulation tail;
the private stream table is initialized only when the tail starts. -/
theorem emulationGame_lift_bind {α : Type} (p : OracleComp (WorldSpec C) α)
    (f : α → EmulationM C Bool) :
    emulationGame (StateT.lift (liftM p) >>= f) =
      p >>= fun a => emulationGame (f a) := by
  simp [emulationGame, StateT.run_bind, StateT.run_lift, WriterT.run_bind,
    WriterT.run_liftM, map_bind, bind_map_left]

/-- The dealer endpoint uses the actual keygen simulator followed by the
literal continuation, without resetting the shared hash cache. -/
theorem dealerKeygenGame_factor (circuits : Circuits) :
    dealerKeygenGame K settings attempts D A circuits =
      idealExecution (fun p => p) D Fkeygen (keygenSimulator D A.keygen)
        (fun _ => ()) [] >>= fun r =>
        emulationGame (afterKeygen K settings attempts D A circuits r.1 r.2) := by
  exact emulationGame_lift_bind _ _

/-- Lift the ordinary world without observing it or changing the stream table. -/
def plainRoles : Roles C (StateT (StreamCache C) (OracleComp (WorldSpec C))) where
  adversary p := StateT.lift (worldRoles.adversary p)
  honest p := StateT.lift (worldRoles.honest p)

theorem erase_base_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    treeSimErase ((lifetimeHybridRoles D 0 0).adversary p) =
      (plainRoles (C := C)).adversary p := by
  exact treeSimErase_adversary D p

theorem erase_base_honest {α : Type} (p : OracleComp (LocalSpec C) α) :
    treeSimErase ((lifetimeHybridRoles D 0 0).honest p) =
      (plainRoles (C := C)).honest p := by
  simpa only [lifetimeHybridRoles, Nat.lt_irrefl, if_false, if_true, plainRoles, worldRoles]
    using treeSimErase_lift (free p)

/-- Erasing the prefix's observation log gives the real keygen and leaves the
stream table untouched, for every output and every ordinary oracle answer. -/
theorem keygenPrefix_erased :
    treeSimErase (keygenPrefix D A) = StateT.lift
      (realExecution D A.keygen noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []) := by
  have hlift {α β : Type} (p : OracleComp (WorldSpec C) α)
      (f : α → OracleComp (WorldSpec C) β) :
      (StateT.lift (p >>= f) : StateT (StreamCache C) (OracleComp (WorldSpec C)) β) =
        StateT.lift p >>= fun a => StateT.lift (f a) := by
    apply StateT.ext
    intro s
    simp [StateT.run_lift, StateT.run_bind, map_bind, bind_map_left]
  have hpure {α : Type} (a : α) :
      (StateT.lift (pure a) : StateT (StreamCache C) (OracleComp (WorldSpec C)) α) = pure a := by
    apply StateT.ext
    intro s
    simp [StateT.run_lift]
  simp only [keygenPrefix, treeSimErase_bind, erase_base_adversary, realExecution, hlift]
  apply bind_congr
  intro state
  rw [treeSim_hom_phase (fun p => treeSimErase p) (fun a => treeSimErase_pure a)
    (fun p f => treeSimErase_bind p f) (lifetimeHybridRoles D 0 0) plainRoles
    (fun p => erase_base_adversary D p) (fun p => erase_base_honest D p)]
  exact (treeSim_hom_phase (fun p => StateT.lift p) (fun a => hpure a)
    (fun p f => hlift p f) worldRoles plainRoles (fun _ => rfl) (fun _ => rfl)
    D A.keygen setupRounds state (fun i => (keygen i : PartyM C E RealSpec (Keys C)))).symm

theorem emulationGame_erased (p : EmulationM C Bool) :
    emulationGame p = (treeSimErase p).run' ∅ := by
  simp [emulationGame, treeSimErase, keygenEraseLog, StateT.run'_eq, Functor.map_map]

/-- The real-keygen all-emulated endpoint has the same explicit world prefix
as the component claim, followed by the actual lifetime continuation. -/
theorem allEmulated_real_factor (circuits : Circuits) :
    emulationGame (lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D A) =
      realExecution D A.keygen noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [] >>=
        fun r => emulationGame (afterKeygen K settings attempts D A circuits r.1 r.2) := by
  rw [allEmulated_factor, emulationGame_erased, treeSimErase_bind, keygenPrefix_erased]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, map_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro r
  exact (emulationGame_erased _).symm

/-- Forward ordinary queries from either world copy to the same local oracle.
The continuation has no programming interface; a programming request is rejected. -/
def continuationOracle : QueryImpl (WorldSpec C) (OracleComp (LocalSpec C))
  | .inl (.inl q) => OracleComp.lift (OracleSpec.query q)
  | .inl (.inr _) => pure false
  | .inr q => OracleComp.lift (OracleSpec.query q)

/-- One concrete local distinguisher, with the actual post-keygen lifetime code. -/
def continuation (circuits : Circuits) : Distinguisher C A.keygen.State (Keys C) := fun r =>
  simulateQ continuationOracle
    (emulationGame (afterKeygen K settings attempts D A circuits r.1 r.2))

/-- The programming branch of the world interface. -/
def Programming : (WorldSpec C).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- Forwarding both ordinary copies preserves their shared cache, including
keygen derivations already queried by the prefix. -/
theorem continuationOracle_simulate (prims : Primitives) {α : Type}
    (p : OracleComp (WorldSpec C) α) (h : IsQueryBoundP p Programming 0) :
    simulateQ (localAnswer prims) (simulateQ continuationOracle p) =
      simulateQ (worldAnswer prims) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ Programming t := by simpa using h.1
    have hq : simulateQ (localAnswer prims) (continuationOracle t) =
        worldAnswer prims t := by
      rcases t with (q | x) | q
      · change simulateQ (localAnswer prims) (OracleComp.lift (OracleSpec.query q)) =
          localAnswer prims q
        simp
      · exact (ht trivial).elim
      · change simulateQ (localAnswer prims) (OracleComp.lift (OracleSpec.query q)) =
          localAnswer prims q
        simp
    simp only [simulateQ_bind, simulateQ_spec_query, hq]
    exact bind_congr fun a => ih a (by simpa using h.2 a)

/-- A local query costs no more than its all-party lifetime charge. -/
theorem continuationOracle_queryBound (t : (WorldSpec C).Domain) :
    IsQueryBoundP (continuationOracle t) Counted
      (if LifetimeCounted t then 1 else 0) := by
  have local_bound (q : (LocalSpec C).Domain) :
      IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q)) Counted
        (if LifetimeCounted (.inr q) then 1 else 0) := by
    apply (isQueryBoundP_query_iff _ _ _).2
    intro hq
    rcases q with u | q | x
    · exact (hq.elim)
    · simp [LifetimeCounted]
    · simp [LifetimeCounted]
  rcases t with (q | x) | q
  · rcases q with u | q | x
    · exact local_bound (.inl u)
    · exact local_bound (.inr (.inl q))
    · exact local_bound (.inr (.inr x))
  · simp [continuationOracle]
  · exact local_bound q

/-- The fixed compiler preserves the all-answer lifetime allowance. -/
theorem continuationOracle_bound {α : Type} (p : OracleComp (WorldSpec C) α)
    (Q : ℕ) (h : IsQueryBoundP p LifetimeCounted Q) :
    IsQueryBoundP (simulateQ continuationOracle p) Counted Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query]
    apply (isQueryBoundP_bind (continuationOracle_queryBound t)
      (fun a _ => ih a _ (h.2 a))).mono
    by_cases ht : LifetimeCounted t
    · have hpos := h.1.resolve_left (not_not.mpr ht)
      simp only [ht, if_true]
      omega
    · simp [ht]

/-- A tail with its inherited lifetime budget is unchanged by the local cap. -/
theorem continuation_cap_eq (circuits : Circuits) (Q : ℕ)
    (r : A.keygen.State × (C.Party → Option (Keys C)))
    (h : IsQueryBoundP
      (emulationGame (afterKeygen K settings attempts D A circuits r.1 r.2))
      LifetimeCounted Q) :
    cap Q (continuation K settings attempts D A circuits r) =
      continuation K settings attempts D A circuits r :=
  cap_eq _ Q (continuationOracle_bound _ Q h)

/-- Stop before the first counted query exceeding the allowance. The two
Boolean return values give lower and upper tests for the uncapped continuation. -/
def stopCap (fallback : Bool) : OracleComp (LocalSpec C) Bool → ℕ → OracleComp (LocalSpec C) Bool
  | .pure b, _ => pure b
  | .queryBind t k, Q =>
    if Counted t then
      if Q = 0 then pure fallback else
        OracleComp.lift (OracleSpec.query t) >>= fun u => stopCap fallback (k u) (Q - 1)
    else OracleComp.lift (OracleSpec.query t) >>= fun u => stopCap fallback (k u) Q

theorem stopCap_bound (fallback : Bool) (p : OracleComp (LocalSpec C) Bool) (Q : ℕ) :
    IsQueryBoundP (stopCap fallback p Q) Counted Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure b => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    change IsQueryBoundP (stopCap fallback (.queryBind t k) Q) Counted Q
    simp only [stopCap]
    split
    · rename_i ht
      split
      · simp
      · rename_i hQ
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr (Nat.pos_of_ne_zero hQ), fun u => by simpa [ht] using ih u (Q - 1)⟩
    · rename_i ht
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl ht, fun u => by simpa [ht] using ih u Q⟩

/-- On a pathwise bounded source, either stopping value gives the original code. -/
theorem stopCap_eq (fallback : Bool) (p : OracleComp (LocalSpec C) Bool) (Q : ℕ)
    (h : IsQueryBoundP p Counted Q) : stopCap fallback p Q = p := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure b => rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    change stopCap fallback (.queryBind t k) Q = _
    simp only [stopCap]
    split
    · rename_i ht
      have hpos := h.1.resolve_left (not_not.mpr ht)
      rw [if_neg (Nat.ne_of_gt hpos)]
      exact bind_congr fun u => ih u _ (by simpa [ht] using h.2 u)
    · rename_i ht
      exact bind_congr fun u => ih u _ (by simpa [ht] using h.2 u)

/-- The stopping tests bracket the original test from every shared cache.
No ideal-output budget or reachability assumption is used. -/
theorem stopCap_bracket (prims : Primitives) (p : OracleComp (LocalSpec C) Bool)
    (Q : ℕ) (g : HashCache C) :
    Pr[fun r => r.1 = true | (simulateQ (localAnswer prims) (stopCap false p Q)).run g] ≤
      Pr[fun r => r.1 = true | (simulateQ (localAnswer prims) p).run g] ∧
    Pr[fun r => r.1 = true | (simulateQ (localAnswer prims) p).run g] ≤
      Pr[fun r => r.1 = true | (simulateQ (localAnswer prims) (stopCap true p Q)).run g] := by
  induction p using OracleComp.inductionOn generalizing Q g with
  | pure b => exact ⟨le_rfl, le_rfl⟩
  | query_bind t k ih =>
    change (Pr[fun r => r.1 = true |
        (simulateQ (localAnswer prims) (stopCap false (.queryBind t k) Q)).run g] ≤
      Pr[fun r => r.1 = true | (simulateQ (localAnswer prims) (.queryBind t k)).run g]) ∧
      (Pr[fun r => r.1 = true | (simulateQ (localAnswer prims) (.queryBind t k)).run g] ≤
      Pr[fun r => r.1 = true |
        (simulateQ (localAnswer prims) (stopCap true (.queryBind t k) Q)).run g])
    by_cases ht : Counted t
    · by_cases hQ : Q = 0
      · simp only [stopCap, ht, if_true, hQ, simulateQ_pure, StateT.run_pure,
          probEvent_pure, Bool.false_eq_true, if_false]
        exact ⟨zero_le, probEvent_le_one⟩
      · simp only [stopCap, ht, if_true, hQ, if_false, simulateQ_bind,
          simulateQ_spec_query, StateT.run_bind]
        exact ⟨probEvent_bind_mono (mx := (localAnswer prims t).run g)
            (fun r _ => (ih r.1 (Q - 1) r.2).1),
          probEvent_bind_mono (mx := (localAnswer prims t).run g)
            (fun r _ => (ih r.1 (Q - 1) r.2).2)⟩
    · simp only [stopCap, ht, if_false, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact ⟨probEvent_bind_mono (mx := (localAnswer prims t).run g)
          (fun r _ => (ih r.1 Q r.2).1),
        probEvent_bind_mono (mx := (localAnswer prims t).run g)
          (fun r _ => (ih r.1 Q r.2).2)⟩

/-- The exact real or ideal keygen prefix of the component claim. -/
def phase (B : Adversary C E Unit PEmpty PEmpty) (ideal : Bool) :
    OracleComp (WorldSpec C) (B.State × (C.Party → Option (Keys C))) :=
  if ideal then
    idealExecution (fun p => p) D Fkeygen (keygenSimulator D B) (fun _ => ()) []
  else realExecution D B noFunctionality setupRounds
    (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []

/-- One fixed bounded component test for each stopping value. -/
def componentGame (circuits : Circuits) (Q : ℕ) (fallback ideal : Bool) :
    OracleComp (WorldSpec C) Bool :=
  distinguish (phase D (capAdversary Q A.keygen) ideal)
    (fun r => stopCap fallback (continuation K settings attempts D A circuits r) Q)

/-- The actual continuation after the capped keygen adversary. -/
def middleGame (circuits : Circuits) (Q : ℕ) (ideal : Bool) :
    OracleComp (WorldSpec C) Bool :=
  distinguish (phase D (capAdversary Q A.keygen) ideal)
    (continuation K settings attempts D A circuits)

/-- The same local continuation after the original keygen adversary. -/
def uncappedGame (circuits : Circuits) (ideal : Bool) : OracleComp (WorldSpec C) Bool :=
  distinguish (phase D A.keygen ideal) (continuation K settings attempts D A circuits)

/-- The real endpoint and the local component adapter agree with their entire
hash cache, provided the actual tail has no programming query. -/
theorem allEmulated_uncapped (prims : Primitives) (circuits : Circuits)
    (hfree : ∀ r : A.keygen.State × (C.Party → Option (Keys C)),
      IsQueryBoundP (emulationGame (afterKeygen K settings attempts D A circuits r.1 r.2))
        Programming 0) :
    simulateQ (worldAnswer prims)
      (emulationGame (lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D A)) =
      simulateQ (worldAnswer prims) (uncappedGame K settings attempts D A circuits false) := by
  rw [allEmulated_real_factor]
  simp only [uncappedGame, phase, Bool.false_eq_true, if_false, distinguish, simulateQ_bind]
  apply bind_congr
  intro r
  rw [simulateQ_world_adversary']
  exact (continuationOracle_simulate prims _ (hfree r)).symm

/-- The dealer endpoint has the same local continuation and the actual
programmed keygen cache; no private-table reset is introduced. -/
theorem dealerKeygenGame_uncapped (prims : Primitives) (circuits : Circuits)
    (hfree : ∀ r : A.keygen.State × (C.Party → Option (Keys C)),
      IsQueryBoundP (emulationGame (afterKeygen K settings attempts D A circuits r.1 r.2))
        Programming 0) :
    simulateQ (worldAnswer prims) (dealerKeygenGame K settings attempts D A circuits) =
      simulateQ (worldAnswer prims) (uncappedGame K settings attempts D A circuits true) := by
  rw [dealerKeygenGame_factor]
  simp only [uncappedGame, phase, if_true, distinguish, simulateQ_bind]
  apply bind_congr
  intro r
  rw [simulateQ_world_adversary']
  exact (continuationOracle_simulate prims _ (hfree r)).symm

/-- Finite-role pruning on the concrete chronological endpoint. -/
def ChronologicalRoles (circuits : Circuits) : Prop :=
  chronologicalGame K settings attempts D A circuits (lifetimeRuns attempts) =
    emulationGame (lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
      (lifetimeHybridRoles D 0 0) D A)

/-- Programming is absent from the actual tail, on every possible keygen output. -/
def TailProgramFree (circuits : Circuits) : Prop :=
  ∀ r : A.keygen.State × (C.Party → Option (Keys C)),
    IsQueryBoundP (emulationGame (afterKeygen K settings attempts D A circuits r.1 r.2)) Programming 0

/-- Capping the keygen adversary preserves the phase's full joint output/cache
law. This predicate concerns only the three keygen rounds, before the tail. -/
def KeygenCapQuiet (prims : Primitives) (Q : ℕ) : Prop :=
  ∀ ideal : Bool,
    (simulateQ (worldAnswer prims) (phase D (capAdversary Q A.keygen) ideal)).run ∅ =
      (simulateQ (worldAnswer prims) (phase D A.keygen ideal)).run ∅

/-- The continuation's allowance only at actually reached real keygen outputs.
There is deliberately no corresponding requirement on ideal outputs. -/
def RealTailBound (prims : Primitives) (circuits : Circuits) (Q : ℕ) : Prop :=
  ∀ r ∈ support ((simulateQ (worldAnswer prims)
    (phase D (capAdversary Q A.keygen) false)).run ∅),
    IsQueryBoundP (continuation K settings attempts D A circuits r.1) Counted Q

/-- A whole-program all-answer bound also bounds every reached continuation.
The predicate domain need not be finite. -/
theorem continuation_bound_of_support {ι α β : Type} {spec : OracleSpec ι}
    (p : OracleComp spec α) (f : α → OracleComp spec β) (charged : ι → Prop)
    [DecidablePred charged] (Q : ℕ) (hQ : IsQueryBoundP (p >>= f) charged Q)
    (a : α) (ha : a ∈ support p) : IsQueryBoundP (f a) charged Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure b =>
    simp only [support_pure, Set.mem_singleton_iff] at ha
    subst a
    simpa only [pure_bind] using hQ
  | query_bind t k ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at hQ
    rcases (mem_support_bind_iff _ _ _).mp ha with ⟨u, _, hu⟩
    exact (ih u _ (hQ.2 u) hu).mono (by split <;> omega)

/-- The actual all-emulated source budget supplies the real tail allowance
after a quiet keygen cap. Only the real prefix's support is used. -/
theorem realTailBound_of_sourceBound (prims : Primitives) (circuits : Circuits) (Q : ℕ)
    (hcap : KeygenCapQuiet D A prims Q)
    (hbudget : IsQueryBoundP
      (emulationGame (lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D A)) LifetimeCounted Q) :
    RealTailBound K settings attempts D A prims circuits Q := by
  rw [allEmulated_real_factor] at hbudget
  intro r hr
  rw [hcap false] at hr
  have hs : r.1 ∈ support (phase D A.keygen false) := by
    apply support_simulateQ_run'_subset (worldAnswer prims) (phase D A.keygen false) ∅
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ hr
  exact continuationOracle_bound _ Q
    (continuation_bound_of_support _ _ LifetimeCounted Q hbudget r.1 hs)

/-- Both stopping choices meet the exact D18 component budget. -/
theorem component_queryBound (circuits : Circuits) (Q : ℕ) (fallback : Bool) :
    IsQueryBounded (capAdversary Q A.keygen)
      (fun r => stopCap fallback (continuation K settings attempts D A circuits r) Q)
      setupRounds ((setupRounds + 2) * Q) := by
  refine ⟨Q, Q, Q, ?_, fun _ _ => cap_bound _ Q, fun _ _ => cap_bound _ Q,
    fun _ _ => cap_bound _ Q, fun _ => stopCap_bound _ _ Q⟩
  rw [Nat.add_mul]
  omega

theorem component_gap (prims : Primitives) (circuits : Circuits) (Q : ℕ) (fallback : Bool) :
    |accepts prims (componentGame K settings attempts D A circuits Q fallback false) -
      accepts prims (componentGame K settings attempts D A circuits Q fallback true)| ≤
      keygenHashError C ((setupRounds + 2) * Q) := by
  exact (keygenSecurityClosed prims D (capAdversary Q A.keygen) (fun _ => ()) []
    (fun r => stopCap fallback (continuation K settings attempts D A circuits r) Q)
    ((setupRounds + 2) * Q) trivial
    (component_queryBound K settings attempts D A circuits Q fallback)).2

private theorem accepts_run (prims : Primitives) (p : OracleComp (WorldSpec C) Bool) :
    accepts prims p =
      (Pr[fun r => r.1 = true | (simulateQ (worldAnswer prims) p).run ∅]).toReal := by
  unfold accepts
  rw [probEvent_runWorld_fst prims p (fun b => b = true)]
  simp only [StateT.run'_eq, probEvent_map, Function.comp_def]

/-- At a reached bounded real tail, neither stopping choice changes any output
or hash-cache entry. -/
theorem component_real_eq (prims : Primitives) (circuits : Circuits) (Q : ℕ) (fallback : Bool)
    (hbound : RealTailBound K settings attempts D A prims circuits Q) :
    (simulateQ (worldAnswer prims) (componentGame K settings attempts D A circuits Q fallback false)).run ∅ =
      (simulateQ (worldAnswer prims) (middleGame K settings attempts D A circuits Q false)).run ∅ := by
  simp only [componentGame, middleGame, distinguish, simulateQ_bind, StateT.run_bind,
    simulateQ_world_adversary']
  apply OracleComp.bind_congr_of_forall_mem_support
  intro r hr
  rw [stopCap_eq _ _ _ (hbound r hr)]

/-- The uncapped ideal acceptance lies between the two bounded stopping tests,
including ideal outputs that no real lifetime reaches. -/
theorem component_ideal_bracket (prims : Primitives) (circuits : Circuits) (Q : ℕ) :
    accepts prims (componentGame K settings attempts D A circuits Q false true) ≤
      accepts prims (middleGame K settings attempts D A circuits Q true) ∧
    accepts prims (middleGame K settings attempts D A circuits Q true) ≤
      accepts prims (componentGame K settings attempts D A circuits Q true true) := by
  simp only [accepts_run, componentGame, middleGame, distinguish, simulateQ_bind,
    StateT.run_bind, simulateQ_world_adversary']
  constructor
  · apply ENNReal.toReal_mono probEvent_ne_top
    exact probEvent_bind_mono (fun r _ =>
      (stopCap_bracket prims (continuation K settings attempts D A circuits r.1) Q r.2).1)
  · apply ENNReal.toReal_mono probEvent_ne_top
    exact probEvent_bind_mono (fun r _ =>
      (stopCap_bracket prims (continuation K settings attempts D A circuits r.1) Q r.2).2)

/-- Each direction uses one component bound, so the absolute distance costs
one keygen error, not the sum of two errors. -/
theorem middle_gap (prims : Primitives) (circuits : Circuits) (Q : ℕ)
    (hbound : RealTailBound K settings attempts D A prims circuits Q) :
    |accepts prims (middleGame K settings attempts D A circuits Q false) -
      accepts prims (middleGame K settings attempts D A circuits Q true)| ≤
      keygenHashError C ((setupRounds + 2) * Q) := by
  have hlo := component_gap K settings attempts D A prims circuits Q false
  have hhi := component_gap K settings attempts D A prims circuits Q true
  have hb := component_ideal_bracket K settings attempts D A prims circuits Q
  have he (b : Bool) :
      accepts prims (componentGame K settings attempts D A circuits Q b false) =
      accepts prims (middleGame K settings attempts D A circuits Q false) := by
    simp only [accepts_run, component_real_eq K settings attempts D A prims circuits Q b hbound]
  rw [he false] at hlo
  rw [he true] at hhi
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hhi).1], by linarith [(abs_le.mp hlo).2]⟩

/-- Quiet keygen caps transport the entire continuation, not just its acceptance. -/
theorem middle_eq_uncapped (prims : Primitives) (circuits : Circuits) (Q : ℕ)
    (hcap : KeygenCapQuiet D A prims Q) (ideal : Bool) :
    (simulateQ (worldAnswer prims) (middleGame K settings attempts D A circuits Q ideal)).run ∅ =
      (simulateQ (worldAnswer prims) (uncappedGame K settings attempts D A circuits ideal)).run ∅ := by
  simp only [middleGame, uncappedGame, distinguish, simulateQ_bind, StateT.run_bind]
  rw [hcap ideal]
  rfl

/-- The exact fixed-`Th` lifetime endpoints inherit the single component error. -/
theorem endpoint_gap (prims : Primitives) (circuits : Circuits) (Q : ℕ)
    (hroles : ChronologicalRoles K settings attempts D A circuits)
    (hfree : TailProgramFree K settings attempts D A circuits)
    (hcap : KeygenCapQuiet D A prims Q)
    (hbound : RealTailBound K settings attempts D A prims circuits Q) :
    |accepts prims (chronologicalGame K settings attempts D A circuits (lifetimeRuns attempts)) -
      accepts prims (dealerKeygenGame K settings attempts D A circuits)| ≤
      keygenHashError C ((setupRounds + 2) * Q) := by
  have h := middle_gap K settings attempts D A prims circuits Q hbound
  unfold ChronologicalRoles at hroles
  simp only [accepts_run, middle_eq_uncapped K settings attempts D A prims circuits Q hcap] at h
  simp only [accepts_run, hroles, allEmulated_uncapped K settings attempts D A prims circuits hfree,
    dealerKeygenGame_uncapped K settings attempts D A prims circuits hfree]
  exact h

/-- The lifetime counter does not affect the sampled Boolean output. -/
theorem lifetimeRun_output (game : (HashInput → HashOutput) → OracleComp (WorldSpec C) Bool) :
    Prod.fst <$> lifetimeRunSampled aes game = (do
      let values ← $ᵗ (MpcDomain → HashOutput)
      (simulateQ (worldAnswer ⟨thOf values, aes⟩) (game (thOf values))).run' ∅) := by
  simp only [lifetimeRunSampled, map_bind]
  apply bind_congr
  intro values
  exact fst_map_run_withAddCost _ _ _ _

/-- Concrete role pruning, tail classification, keygen-only cap quietness and
real reached-tail bounds imply the original lifetime keygen hop. -/
theorem lifetimeKeygenHop_of_programs (Q : ℕ)
    (hroles : ∀ values : MpcDomain → HashOutput,
      ChronologicalRoles K settings attempts D A (circuitsOf (thOf values)))
    (hfree : ∀ values : MpcDomain → HashOutput,
      TailProgramFree K settings attempts D A (circuitsOf (thOf values)))
    (hcap : ∀ values : MpcDomain → HashOutput,
      KeygenCapQuiet D A ⟨thOf values, aes⟩ Q)
    (hbound : ∀ values : MpcDomain → HashOutput,
      RealTailBound K settings attempts D A ⟨thOf values, aes⟩ (circuitsOf (thOf values)) Q) :
    LifetimeKeygenHop K settings attempts aes circuitsOf D A Q := by
  let realGame := fun Th => chronologicalGame K settings attempts D A (circuitsOf Th) (lifetimeRuns attempts)
  let idealGame := fun Th => dealerKeygenGame K settings attempts D A (circuitsOf Th)
  have hpoint (values : MpcDomain → HashOutput) :
      |(Pr[fun b => b = true | (simulateQ (worldAnswer ⟨thOf values, aes⟩)
        (realGame (thOf values))).run' ∅]).toReal -
      (Pr[fun b => b = true | (simulateQ (worldAnswer ⟨thOf values, aes⟩)
        (idealGame (thOf values))).run' ∅]).toReal| ≤ keygenHashError C ((setupRounds + 2) * Q) := by
    simpa only [accepts_eq_probOutput, probEvent_eq_eq_probOutput] using
      endpoint_gap K settings attempts D A ⟨thOf values, aes⟩ (circuitsOf (thOf values)) Q
        (hroles values) (hfree values) (hcap values) (hbound values)
  have havg := (abs_probEvent_bind_sub_le_sum ($ᵗ (MpcDomain → HashOutput))
    (fun values => (simulateQ (worldAnswer ⟨thOf values, aes⟩) (realGame (thOf values))).run' ∅)
    (fun values => (simulateQ (worldAnswer ⟨thOf values, aes⟩) (idealGame (thOf values))).run' ∅)
    (fun b => b = true) (fun _ => keygenHashError C ((setupRounds + 2) * Q)) hpoint).trans
    (sum_probOutput_mul_const_le _ (by unfold keygenHashError; positivity))
  rw [← lifetimeRun_output aes realGame, ← lifetimeRun_output aes idealGame] at havg
  simpa only [LifetimeKeygenHop, chronologicalProbability, dealerKeygenProbability,
    realGame, idealGame, probEvent_map, Function.comp_def] using havg

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.realTailBound_of_sourceBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realTailBound_of_sourceBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.allEmulated_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allEmulated_factor

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.dealerKeygenGame_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerKeygenGame_factor

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.keygenPrefix_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenPrefix_erased

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.allEmulated_real_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allEmulated_real_factor

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.continuationOracle_simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuationOracle_simulate

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.continuationOracle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuationOracle_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.stopCap_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stopCap_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.stopCap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stopCap_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.stopCap_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stopCap_bracket

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.allEmulated_uncapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allEmulated_uncapped

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.dealerKeygenGame_uncapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerKeygenGame_uncapped

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.component_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms component_gap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.component_real_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms component_real_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.component_ideal_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms component_ideal_bracket

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.middle_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms middle_gap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.endpoint_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpoint_gap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeygenHopProof.lifetimeKeygenHop_of_programs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeKeygenHop_of_programs

end ThresholdLeanXmssSecurity.LifetimeKeygenHopProof
