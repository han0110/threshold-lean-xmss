import ThresholdLeanXmssSecurity.Proof.LifetimePathCount

/-!
# Query budgets for the selected PRSS reference execution

The query bound ranges over every oracle answer, including the honest hash answers. Thus a
reference setup can be realized by choosing the actual setup's uncounted answers. The choice
preserves the adversary's observations and the continuation keys. Honest echo answers may be
chosen separately at each occurrence: this argument is about paths of the oracle program,
not about a consistent random-oracle table or a probability coupling.

The pinned and current leanVM query-bound modules were searched. The support continuation
lemma from `XmssSecurity.Proof.QueryBoundSupport` supplies the budget after a chosen free
computation; the threshold setup and role-support lemmas supply its concrete instances.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeReferenceBudget

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} {E : Type}

/-- Replacing a continuation by one with no greater path cost preserves the cost of its prefix. -/
theorem bound_bind_mono {ι α β γ : Type} {spec : OracleSpec ι}
    (charged : spec.Domain → Prop) (p : OracleComp spec α)
    (f : α → OracleComp spec β) (g : α → OracleComp spec γ)
    (h : ∀ a Q, IsQueryBoundP (g a) charged Q → IsQueryBoundP (f a) charged Q) :
    ∀ Q, IsQueryBoundP (p >>= g) charged Q → IsQueryBoundP (p >>= f) charged Q := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a
  | query_bind t k ih =>
      intro Q hp
      simp only [bind_assoc, isQueryBoundP_query_bind_iff] at hp ⊢
      exact ⟨hp.1, fun u => ih u _ (hp.2 u)⟩

/-- Fixing any supported output of an honest computation costs no additional adversary queries. -/
theorem bound_after_free {α β : Type} (p : OracleComp (LocalSpec C) α)
    (k : α → OracleComp (WorldSpec C) β) (a : α) (ha : a ∈ support p) (Q : ℕ)
    (h : IsQueryBoundP (free p >>= k) WorldCounted Q) :
    IsQueryBoundP (k a) WorldCounted Q := by
  apply IsQueryBoundP.continuation_mono_of_mem_support WorldCounted _ _ Q h a
  rwa [LifetimeKeygenCapQuiet.support_free]

/-- A list of unconstrained query answers can be chosen independently at each occurrence. -/
theorem mapM_support_of_each {ι α β : Type} {spec : OracleSpec ι}
    (f : α → OracleComp spec β) (v : α → β) :
    ∀ xs : List α, (∀ a ∈ xs, v a ∈ support (f a)) →
      xs.map v ∈ support (xs.mapM f) := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons a xs ih =>
      intro h
      simp only [List.mapM_cons, List.map_cons, support_bind, Set.mem_iUnion,
        support_pure, Set.mem_singleton_iff]
      exact ⟨v a, h a (by simp), xs.map v, ih (fun b hb => h b (by simp [hb])), rfl⟩

/-- Every prescribed local parts value lies in the support of the actual sampler. -/
theorem sampleParts_supported (p : Parts C) : p ∈ support (sampleParts (C := C)) := by
  rcases p with ⟨parameter, term, pair⟩
  simp [sampleParts]

/-- The actual PRSS initialization permits the reference commitments and parts. Corrupt rows
have exactly the default value of the actual program. -/
theorem initialData_supported (D : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) :
    prssDataMask D (prssDataAt h parts) ∈ support (prssInitialData D) := by
  unfold prssInitialData
  apply LifetimeKeygenCapQuiet.mem_support_sequenceFin_of
  intro i
  by_cases hi : i ∈ D.1
  · simp [hi, prssDataMask]
  · simp only [if_neg hi, prssDataMask, prssDataAt, support_bind, Set.mem_iUnion,
      support_liftComp, support_pure, Set.mem_singleton_iff]
    refine ⟨parts i, sampleParts_supported _, ?_⟩
    refine ⟨C.parties.map (fun j => h (.commit .prss i j (revealTo .prss (parts i) i j))), ?_, rfl⟩
    apply mapM_support_of_each
    intro j _
    exact mem_support_query _ _

/-- The all-answer support of derivation contains every key assignment with the required zero
coordinates, even if two derivation queries have the same input. -/
theorem deriveKeys_supported (i : C.Party) (view : C.Party → Parts C) (keys : PrssKeys C)
    (ht : ∀ T, i ∉ C.holders T → keys.term T = 0) (hp : keys.pair i = 0) :
    (0, keys.term, keys.pair) ∈ support (deriveKeys .prss i view) := by
  simp only [deriveKeys, reduceCtorEq, ↓reduceIte, pure_bind,
    support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  refine ⟨C.terms.map keys.term, ?_, C.parties.map keys.pair, ?_, ?_⟩
  · apply mapM_support_of_each
    intro T _
    by_cases hi : i ∈ C.holders T
    · simp only [if_pos hi]
      exact mem_support_query _ _
    · simp [hi, ht T hi]
  · apply mapM_support_of_each
    intro j _
    by_cases hj : j = i
    · simp [hj, hp]
    · simp only [dif_neg hj]
      exact mem_support_query _ _
  · simp only [getD_terms_idxOf, getD_parties]

section Echo

/-- Agreement of the exposed shared keys at one honest pair. -/
def ExposedAgree (D : C.Coalition) (keys : C.Party → C.Term → HashOutput) (i j : C.Party) : Prop :=
  ∀ T, KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → keys i T = keys j T

theorem exposedAgree_symm (D : C.Coalition) (keys : C.Party → C.Term → HashOutput)
    (i j : C.Party) : ExposedAgree D keys i j ↔ ExposedAgree D keys j i := by
  constructor <;> intro h T hT hi hj <;> exact (h T hT hj hi).symm

/-- Chosen honest hash answers encode the reference's echo decision. Hashes visible to a
corrupt receiver retain their original values. -/
def echoValue (D : C.Coalition) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i j : C.Party) : HashOutput :=
  if i ∉ D.1 ∧ j ∉ D.1 ∧ KeygenShareHidden D i j then
    if ExposedAgree D keys i j ∨ i < j then 0 else 1
  else prssEcho h keys i j

theorem echoValue_corrupt (D : C.Coalition) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i j : C.Party) (hj : j ∈ D.1) :
    echoValue D h keys i j = prssEcho h keys i j := by
  simp [echoValue, hj]

theorem echoValue_hidden (D : C.Coalition) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i j : C.Party)
    (hi : i ∉ D.1) (hj : j ∉ D.1) (hne : i ≠ j) (hs : KeygenShareHidden D i j) :
    echoValue D h keys i j = echoValue D h keys j i ↔ ExposedAgree D keys i j := by
  have h01 : (0 : HashOutput) ≠ 1 := by
    intro he
    have hn : (0 : ℕ) = 1 := congrArg BitVec.toNat he
    exact Nat.zero_ne_one hn
  have hs' : KeygenShareHidden D j i := by
    simpa only [KeygenShareHidden, and_comm] using hs
  simp only [echoValue, hi, hj, hs, hs', not_false_eq_true, and_self, ite_true]
  rw [← exposedAgree_symm D keys i j]
  by_cases ha : ExposedAgree D keys i j
  · simp [ha]
  · simp only [ha, false_or, iff_false]
    rcases lt_or_gt_of_ne hne with hij | hji
    · simpa only [if_pos hij, if_neg (not_lt.mpr (le_of_lt hij))] using h01
    · simpa only [if_pos hji, if_neg (not_lt.mpr (le_of_lt hji))] using h01.symm

theorem echoValue_exposed (D : C.Coalition) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i j : C.Party)
    (hs : ¬ KeygenShareHidden D i j) :
    echoValue D h keys i j = prssEcho h keys i j := by
  simp [echoValue, hs]

def echoInbox (D : C.Coalition) (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (values : C.Party → C.Party → HashOutput) (i : C.Party) : Mail C E := fun j =>
  if j ∈ D.1 then sent j i else if active j then
    if i = j then none else some (.hashes [values j i]) else some .abort

theorem echoInbox_abort (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (values : C.Party → C.Party → HashOutput) (i j : C.Party) :
    Msg.isAbort (echoInbox D active sent values i j) =
      Msg.isAbort (prssEchoInbox D active sent (fun _ => 0) (fun _ _ => 0) i j) := by
  unfold echoInbox prssEchoInbox
  split_ifs <;> rfl

/-- The actual equality test on the chosen echo answers is exactly the reference test,
including its stronger comparison on hidden honest pairs. -/
theorem echoCheck_iff (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i : C.Party) (hi : i ∉ D.1) :
    (∀ j, j ≠ i → Msg.hashesOf (echoInbox D active sent (echoValue D h keys) i j) =
      [echoValue D h keys i j]) ↔ AimedEchoCheck D active sent h keys i := by
  unfold AimedEchoCheck
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hji
  by_cases hj : j ∈ D.1
  · simp only [echoInbox, if_pos hj, echoValue_corrupt D h keys i j hj]
  · simp only [echoInbox, if_neg hj]
    by_cases ha : active j
    · simp only [if_pos ha, if_neg hji.symm, Msg.hashesOf, List.cons.injEq, and_true]
      by_cases hs : KeygenShareHidden D i j
      · rw [if_pos hs, eq_comm, echoValue_hidden D h keys i j hi hj hji.symm hs]
        rfl
      · have hs' : ¬ KeygenShareHidden D j i := by
          simpa only [KeygenShareHidden, and_comm] using hs
        rw [if_neg hs, echoValue_exposed D h keys i j hs, echoValue_exposed D h keys j i hs']
        exact eq_comm
    · simp [ha, Msg.hashesOf]

def echoSteps {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (values : C.Party → C.Party → HashOutput) (next : C.Party → PartyM C E RealSpec α)
    (i : C.Party) : Step C E RealSpec α :=
  if i ∈ D.1 then .done none else if active i then
    .wait (fun j => if j = i then none else some (.hashes [values i j]))
      (exchangeResume fun received => do
        require (∀ j, j ≠ i → Msg.hashesOf (received j) = [values i j])
        next i)
  else .done none

theorem echoSteps_callInput {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (values : C.Party → C.Party → HashOutput) (next : C.Party → PartyM C E RealSpec α)
    (i : C.Party) : (echoSteps D active values next i).callInput = none := by
  unfold echoSteps
  split_ifs <;> rfl

theorem echoSteps_inbox {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (values : C.Party → C.Party → HashOutput) (next : C.Party → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    (fun j => if j ∈ D.1 then sent j i else (echoSteps D active values next j).delivered i) =
      echoInbox D active sent values i := by
  funext j
  by_cases hj : j ∈ D.1 <;> by_cases ha : active j <;>
    simp [echoSteps, echoInbox, Step.delivered, hj, ha]

theorem echoSteps_visible {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (next : C.Party → PartyM C E RealSpec α) :
    (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      (echoSteps D active (echoValue D h keys) next i).outbox c else none) =
      prssEchoVisible D active h keys := by
  funext c i
  by_cases hc : c ∈ D.1 <;> by_cases hi : i ∈ D.1 <;> by_cases ha : active i <;>
    simp [echoSteps, Step.outbox, prssEchoVisible, prssEchoOutbox, hc, hi, ha,
      echoValue_corrupt]

/-- One actual echo round, with the chosen free answers, has the reference adversary call,
the reference abort decisions and the original continuation programs. -/
theorem echoSteps_round {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (next : C.Party → PartyM C E RealSpec α) (state : A.State) :
    stepRound worldRoles D A noFunctionality state
      (echoSteps D active (echoValue D h keys) next) = (do
        let (state', sent) ← worldRoles.adversary (A.round state (prssEchoVisible D active h keys))
        let steps ← Concrete.sequenceFin fun i => free
          (if AimedEchoAccepted D active sent h keys i then advance (next i).run else pure (.done none))
        pure (state', steps, sent)) := by
  simp only [stepRound, echoSteps_callInput, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, ↓reduceIte, echoSteps_visible]
  apply bind_congr
  rintro ⟨state', sent⟩
  congr 1
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [echoSteps, hi, AimedEchoAccepted, free_pure]
  · by_cases ha : active i
    · have hstep : echoSteps D active (echoValue D h keys) next i =
          .wait (fun j => if j = i then none else some (.hashes [echoValue D h keys i j]))
            (exchangeResume fun received => do
              require (∀ j, j ≠ i → Msg.hashesOf (received j) = [echoValue D h keys i j])
              next i) := by simp only [echoSteps, if_neg hi, if_pos ha]
      simp only [hstep, if_neg hi]
      rw [show (fun j => if j ∈ D.1 then sent j i else
          (echoSteps D active (echoValue D h keys) next j).delivered i) =
          echoInbox D active sent (echoValue D h keys) i from echoSteps_inbox _ _ _ _ _ _]
      have hb : (fun j => Msg.isAbort (echoInbox D active sent (echoValue D h keys) i j)) =
          (fun j => Msg.isAbort (prssEchoInbox D active sent (fun _ => 0) (fun _ _ => 0) i j)) :=
        funext (echoInbox_abort D active sent (echoValue D h keys) i)
      simp only [exchangeResume]
      rw [hb]
      by_cases hab : C.parties.any (fun j => Msg.isAbort
          (prssEchoInbox D active sent (fun _ => 0) (fun _ _ => 0) i j)) = true
      · simp only [AimedEchoAccepted, hab, not_true_eq_false, and_false,
          false_and, ↓reduceIte]
        rfl
      · rw [if_neg hab, advance_require_bind]
        rw [echoCheck_iff D active sent h keys i hi]
        simp only [AimedEchoAccepted, hi, ha, hab, not_false_eq_true, true_and]
        split_ifs <;> simp_all [worldRoles]
    · simp [echoSteps, hi, ha, AimedEchoAccepted, free_pure]

end Echo

theorem suspend_echo_row {α : Type} (i : C.Party) (keys : PrssKeys C)
    (values : C.Party → HashOutput) (next : PrssKeys C → PartyM C E RealSpec α) :
    suspendStep next (prssFinishStep i (some (keys, C.parties.map values))) =
      .wait (fun j => if j = i then none else some (.hashes [values j]))
        (exchangeResume fun received => do
          require (∀ j, j ≠ i → Msg.hashesOf (received j) = [values j])
          next keys) := by
  simp only [prssFinishStep, suspendStep, getD_parties]
  congr 1
  funext received
  simp only [exchangeResume]
  split_ifs
  · rfl
  · simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, bind_assoc]
    unfold require
    split_ifs <;> rfl

section Rows

theorem postReveal_supported (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (h : Query C → HashOutput) (keys : PrssKeys C) (values : C.Party → HashOutput)
    (ht : ∀ T, i ∉ C.holders T → keys.term T = 0) (hp : keys.pair i = 0) :
    (if prssOpenCheck i own committed revealed
        (C.parties.map fun j => h (.commit .prss j i (Msg.hashesOf (revealed j))))
      then some (keys, C.parties.map values) else none) ∈
      support (prssPostRevealData i own committed revealed) := by
  unfold prssPostRevealData
  rw [mem_support_bind_iff]
  refine ⟨C.parties.map (fun j => h (.commit .prss j i (Msg.hashesOf (revealed j)))), ?_, ?_⟩
  · rw [support_liftComp]
    exact mapM_support_of_each _ _ _ (fun _ _ => mem_support_query _ _)
  · split_ifs with hc
    · rw [mem_support_bind_iff]
      refine ⟨(0, keys.term, keys.pair), ?_, ?_⟩
      · rw [support_liftComp]
        exact deriveKeys_supported i _ keys ht hp
      · rw [mem_support_bind_iff]
        refine ⟨C.parties.map values, ?_, ?_⟩
        · rw [support_liftComp]
          exact mapM_support_of_each _ _ _ (fun _ _ => mem_support_query _ _)
        · cases keys
          simp
    · simp

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives)

/-- The actual reveal rows with freely chosen derivations and echo answers. -/
def referenceRows (D : C.Coalition) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent revealed : C.Party → Mail C E) : RevealRows C := fun i =>
  if AimedReferenceActive D h active sent revealed i then
    some (aimedReferenceKeys prims D h normal parts (fun i j => revealed j i) i,
      C.parties.map (echoValue D h
        (fun j => (aimedReferenceKeys prims D h (fun _ => 0) parts (fun i j => revealed j i) j).term) i))
  else none

theorem referenceRows_supported (D : C.Coalition) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent revealed : C.Party → Mail C E) :
    referenceRows prims D h normal active parts sent revealed ∈
      support (prssRevealRows D active parts (prssCommitInbox D (prssDataAt h parts) sent) revealed) := by
  unfold prssRevealRows
  apply LifetimeKeygenCapQuiet.mem_support_sequenceFin_of
  intro i
  by_cases hi : i ∈ D.1
  · simp [hi, referenceRows, AimedReferenceActive]
  · simp only [if_neg hi]
    by_cases ha : active i
    · simp only [if_pos ha, prssRevealData, aimedRevealInbox_aborted]
      by_cases hab : aimedRevealAborted D active revealed i = true
      · simp [hab, referenceRows, AimedReferenceActive]
      · have hab' := Bool.eq_false_iff.mpr hab
        simp only [if_neg hab]
        have hs := postReveal_supported i (parts i)
          (prssCommitInbox D (prssDataAt h parts) sent i)
          (prssRevealInbox D active parts revealed i) h
          (aimedReferenceKeys prims D h normal parts (fun i j => revealed j i) i)
          (echoValue D h (fun j => (aimedReferenceKeys prims D h (fun _ => 0)
            parts (fun i j => revealed j i) j).term) i)
          (fun T hT => by simp [aimedReferenceKeys, keygenMaskKeys, D_deriveKeys, hT])
          (by simp [aimedReferenceKeys, keygenMaskKeys, D_deriveKeys])
        rw [aimedOpenCheck_corrupt_iff D h active parts sent revealed i hab'] at hs
        simpa only [referenceRows, AimedReferenceActive, hi, not_false_eq_true, ha, hab',
          true_and] using hs
    · simp [ha, referenceRows, AimedReferenceActive]

theorem referenceRows_steps {α : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent revealed : C.Party → Mail C E)
    (next : C.Party → PrssKeys C → PartyM C E RealSpec α) :
    (fun i => suspendStep (next i) (prssFinishStep i
      (referenceRows prims D h normal active parts sent revealed i))) =
      echoSteps D (AimedReferenceActive D h active sent revealed)
        (echoValue D h (fun j => (aimedReferenceKeys prims D h (fun _ => 0)
          parts (fun i j => revealed j i) j).term))
        (fun i => next i (aimedReferenceKeys prims D h normal parts (fun i j => revealed j i) i)) := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [referenceRows, AimedReferenceActive, hi, echoSteps, prssFinishStep, suspendStep]
  · by_cases ha : AimedReferenceActive D h active sent revealed i
    · simp only [referenceRows, if_pos ha, echoSteps, if_neg hi]
      exact suspend_echo_row _ _ _ _
    · simp [referenceRows, ha, echoSteps, hi, prssFinishStep, suspendStep]

theorem referenceRows_after (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent revealed : C.Party → Mail C E) (state : A.State) :
    afterDerivation K circuits settings top tree D A x Z
      (state, some (referenceRows prims D h normal active parts sent revealed)) =
      aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
        sent revealed state := by
  simp only [afterDerivation, referenceRows_steps, aimedReferenceAfter]
  apply congrArg (fun p : OracleComp (WorldSpec C) (A.State × (C.Party → Option TreeOutput)) =>
    p >>= fun r => worldRoles.adversary (Z r))
  generalize ceremonyFuel circuits settings - 2 = fuel
  cases fuel with
  | zero =>
      simp only [executeRounds, aimedEchoReferenceExecution]
      apply congrArg pure
      apply congrArg (Prod.mk state)
      funext i
      unfold echoSteps
      split_ifs <;> rfl
  | succ fuel =>
      have hd : (∀ i, i ∉ D.1 →
          (echoSteps D (AimedReferenceActive D h active sent revealed)
            (echoValue D h (fun j => (aimedReferenceKeys prims D h (fun _ => 0)
              parts (fun i j => revealed j i) j).term))
            (fun i => ceremonyAfterSetup K circuits settings
              ⟨i, x i, aimedReferenceKeys prims D h normal parts (fun i j => revealed j i) i⟩ top tree) i).isDone) ↔
          ∀ i, i ∉ D.1 → ¬ AimedReferenceActive D h active sent revealed i := by
        apply forall_congr'
        intro i
        apply forall_congr'
        intro hi
        by_cases ha : AimedReferenceActive D h active sent revealed i <;>
          simp [echoSteps, hi, ha, Step.isDone]
      simp only [executeRounds, aimedEchoReferenceExecution, hd]
      split_ifs with hall
      · apply congrArg pure
        apply congrArg (Prod.mk state)
        funext i
        unfold echoSteps
        split_ifs <;> rfl
      · rw [echoSteps_round]
        rfl

end Rows

/-- Masking corrupt initialization rows does not change any honest reveal computation. -/
theorem revealRows_mask (D : C.Coalition) (active : C.Party → Prop)
    (data : C.Party → Parts C × List HashOutput) (sent revealed : C.Party → Mail C E) :
    prssRevealRows D active (fun i => (prssDataMask D data i).1)
      (prssCommitInbox D (prssDataMask D data) sent) revealed =
      prssRevealRows D active (fun i => (data i).1) (prssCommitInbox D data sent) revealed := by
  have hc : prssCommitInbox (E := E) D (prssDataMask D data) sent = prssCommitInbox D data sent := by
    funext i j
    by_cases hj : j ∈ D.1 <;> simp [prssCommitInbox, prssDataMask, hj]
  have hr : prssRevealInbox (E := E) D active (fun i => (prssDataMask D data i).1) revealed =
      prssRevealInbox D active (fun i => (data i).1) revealed := by
    funext i j
    by_cases hj : j ∈ D.1 <;> simp [prssRevealInbox, prssDataMask, hj]
  unfold prssRevealRows
  rw [hc]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
  · rw [hr]
    simp only [if_neg hi, prssDataMask]

section Budget

attribute [local irreducible] afterDerivation aimedReferenceAfter

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The fixed reference execution inherits the whole path budget of the real selected ceremony.
The proof chooses actual free initialization and reveal outputs before comparing continuations. -/
theorem reference_bound (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) (Q : ℕ)
    (budget : IsQueryBoundP (treeRealGame K circuits settings top tree D A x z Z) WorldCounted Q) :
    IsQueryBoundP (worldRoles.adversary (aimedEarlyProgram D A x z h parts) >>=
      aimedReferenceTail prims K circuits settings top tree D A x Z h normal parts) WorldCounted Q := by
  rw [treeRealGame_eq_split] at budget
  simp only [setupPrefix, bind_assoc] at budget
  simp only [aimedEarlyProgram, LifetimeKeygenCapQuiet.adversary_bind, bind_assoc]
  apply bound_bind_mono WorldCounted (worldRoles.adversary (A.start (corruptInputs D x) z))
    _ _ (fun state n hs => ?_) Q budget
  have picked := bound_after_free (prssInitialData D) _
    (prssDataMask D (prssDataAt h parts)) (initialData_supported D h parts) n hs
  simp only [prssEarlyDataRounds_mask, prssEarlyDataRounds_at] at picked
  apply bound_bind_mono WorldCounted (worldRoles.adversary (prssEarlyRounds D A state h parts))
    _ _ (fun r n hr => ?_) n picked
  rcases r with ⟨state', sent, _ | revealed⟩
  · exact isQueryBoundP_pure _ _ _
  · simp only [bind_assoc, pure_bind, revealRows_mask, prssDataAt] at hr
    have chosen := bound_after_free
      (prssRevealRows D (prssCommitActive D sent) parts
        (prssCommitInbox D (prssDataAt h parts) sent) revealed)
      (fun rows => afterDerivation K circuits settings top tree D A x Z (state', some rows))
      (referenceRows prims D h normal (prssCommitActive D sent) parts sent revealed)
      (referenceRows_supported prims D h normal (prssCommitActive D sent) parts sent revealed) n hr
    simpa only [aimedReferenceTail, pure_bind, referenceRows_after] using chosen

/-- The original whole joint-game budget implies the fixed reference budget, for every
reference table and parts assignment. -/
theorem referenceBudget (D : C.Coalition) (pre : LifetimeBridge.Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) (Q : ℕ)
    (budget : IsQueryBoundP (LifetimeBridge.jointGame K circuits settings false D pre A Z)
      WorldCounted Q) :
    LifetimePathCount.ReferenceBudget prims K circuits settings D pre A Z Q := by
  intro h normal parts
  simp only [LifetimeBridge.jointGame] at budget
  simp only [LifetimeJointHop.early, LifetimeKeygenCapQuiet.adversary_bind, bind_assoc]
  apply bound_bind_mono WorldCounted (worldRoles.adversary (LifetimeBridge.jointPrefix pre))
    _ _ (fun input n hi => ?_) Q budget
  simpa only [worldRoles_adversary_pure, pure_bind, LifetimeJointHop.referenceTail] using
    reference_bound prims K circuits settings input.2.1 input.2.2.1 D A input.1 input.2.2.2 Z
      h normal parts n hi

/-- The aimed flag estimate under the budget of the actual selected joint game alone. -/
theorem flagProgram_bound (D : C.Coalition) (pre : LifetimeBridge.Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) (Q : ℕ)
    (budget : IsQueryBoundP (LifetimeBridge.jointGame K circuits settings false D pre A Z)
      WorldCounted Q) :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true |
      (simulateQ (lazyKeyWorld prims D)
        (LifetimeJointHop.flagProgram K circuits settings D pre A Z)).run' (∅, ∅)] ≤
      ((3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  LifetimePathCount.flagProgram_bound_path prims K circuits settings D pre A Z Q
    (referenceBudget prims K circuits settings D pre A Z Q budget)

end Budget

end ThresholdLeanXmssSecurity.LifetimeReferenceBudget

/-- info: 'ThresholdLeanXmssSecurity.LifetimeReferenceBudget.echoSteps_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeReferenceBudget.echoSteps_round

/-- info: 'ThresholdLeanXmssSecurity.LifetimeReferenceBudget.referenceRows_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeReferenceBudget.referenceRows_supported

/-- info: 'ThresholdLeanXmssSecurity.LifetimeReferenceBudget.referenceRows_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeReferenceBudget.referenceRows_after

/-- info: 'ThresholdLeanXmssSecurity.LifetimeReferenceBudget.referenceBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeReferenceBudget.referenceBudget

/-- info: 'ThresholdLeanXmssSecurity.LifetimeReferenceBudget.flagProgram_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeReferenceBudget.flagProgram_bound
