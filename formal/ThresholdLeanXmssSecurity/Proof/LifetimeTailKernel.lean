import ThresholdLeanXmssSecurity.Proof.LifetimeReferenceBudget

/-!
# PRSS flag kernels with a state-dependent continuation

A tail driver retains per-party keys and top trees together with its suspended
programs. Its laws expose exactly the renaming, allowed-call and one-round
observations used by the PRSS key kernel. Both the run and stopped branches
obey the oracle restrictions.

The selected fixed ceremony is an instance. The local echo identities and
probability transports specialize the existing `TreeKeyAimed` and
`LifetimeReferenceBudget` arguments without identifying a lifetime tail with
an executor that discards final outboxes.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeTailKernel

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E σ : Type}

/-- Exactly the observations of a real step family that a driver may use. -/
structure RoundAlike (D : C.Coalition) (first second : C.Party → Step C E RealSpec TreeOutput) : Prop where
  visible : toCoalition D first = toCoalition D second
  output : ∀ i, (first i).output = (second i).output
  done : AllDone D first ↔ AllDone D second
  round : ∀ sent i, roundLocal D first sent i = roundLocal D second sent i

/-- The saved state determines the honest ceremony contexts and its actual driver. -/
structure TailDriver (C : Committee) (E σ : Type) where
  keys : σ → C.Party → Keys C
  top : σ → C.Party → TopTree
  tree : σ → Tree
  stop : σ → OracleComp (WorldSpec C) Bool
  run : σ → (C.Party → Step C E RealSpec TreeOutput) → OracleComp (WorldSpec C) Bool

namespace TailDriver

structure Lawful (D : C.Coalition) (T : TailDriver C E σ) : Prop where
  noProgram : ∀ s steps, IsQueryBoundP (T.run s steps) AimedProgramCall 0
  noProgramStop : ∀ s, IsQueryBoundP (T.stop s) AimedProgramCall 0
  rename : ∀ a b s steps, simulateQ (worldStreamRename D a b) (T.run s steps) =
    T.run s (fun i => renameStep D a b (steps i))
  renameStop : ∀ a b s, simulateQ (worldStreamRename D a b) (T.stop s) = T.stop s
  allowed : ∀ rows s steps, (∀ i, AimedSetupDomain.StepOk rows (steps i)) →
    IsQueryBoundP (T.run s steps) (AimedSetupDomain.Unallowed rows) 0
  allowedStop : ∀ rows s, IsQueryBoundP (T.stop s) (AimedSetupDomain.Unallowed rows) 0
  alike : ∀ s first second, RoundAlike D first second → T.run s first = T.run s second

variable [Field E] [Algebra Bit E]

def steps (T : TailDriver C E σ) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (s : σ) (rows : RevealRows C) : C.Party → Step C E RealSpec TreeOutput :=
  fun i => suspendStep (fun prss => ceremonyAfterSetup K circuits settings
    ⟨i, T.keys s i, prss⟩ (T.top s i) (T.tree s)) (prssFinishStep i (rows i))

def tail (T : TailDriver C E σ) (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    σ × Option (RevealRows C) → OracleComp (WorldSpec C) Bool
  | (s, none) => T.stop s
  | (s, some rows) => T.run s (T.steps K circuits settings s rows)

end TailDriver

section Fixed

variable (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)

theorem stepRound_alike (state : A.State) (first second : C.Party → Step C E RealSpec TreeOutput)
    (h : RoundAlike D first second) :
    stepRound worldRoles D A noFunctionality state first =
      stepRound worldRoles D A noFunctionality state second := by
  rw [stepRound_real, stepRound_real]
  change (do
    let (state', sent) ← worldRoles.adversary (A.round state (toCoalition D first))
    let next ← free (Concrete.sequenceFin (roundLocal D first sent))
    pure (state', next, sent)) = _
  rw [h.visible]
  apply bind_congr
  rintro ⟨state', sent⟩
  dsimp only
  rw [show roundLocal D first sent = roundLocal D second sent from funext (h.round sent)]

theorem executeRounds_alike (fuel : ℕ) (state : A.State)
    (first second : C.Party → Step C E RealSpec TreeOutput) (h : RoundAlike D first second) :
    executeRounds worldRoles D A noFunctionality fuel state first =
      executeRounds worldRoles D A noFunctionality fuel state second := by
  cases fuel with
  | zero => simp only [executeRounds, h.output]
  | succ fuel =>
    rw [executeRounds_succ, executeRounds_succ]
    by_cases done : AllDone D first
    · simp only [if_pos done, if_pos (h.done.mp done), h.output]
    · simp only [if_neg done, if_neg (fun h' => done (h.done.mpr h'))]
      rw [stepRound_alike D A state first second h]

variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The fixed selected-ceremony tail on the state of `LifetimeJointHop.remember`. -/
def selectedDriver (Z : Distinguisher C A.State TreeOutput) :
    TailDriver C E (LifetimeBridge.JointInput C × A.State) where
  keys s := s.1.1
  top s _ := s.1.2.1
  tree s := s.1.2.2.1
  stop s := worldRoles.adversary (Z (s.2, fun _ => none))
  run s steps := do
    let r ← executeRounds worldRoles D A noFunctionality (ceremonyFuel circuits settings - 2) s.2 steps
    worldRoles.adversary (Z r)

omit [Field E] [Algebra Bit E] in
theorem selectedDriver_lawful (Z : Distinguisher C A.State TreeOutput) :
    TailDriver.Lawful D (selectedDriver D A circuits settings Z) := by
  constructor
  · intro s steps
    dsimp only [selectedDriver]
    generalize ceremonyFuel circuits settings - 2 = fuel
    exact qb0_bind (aimed_noProgram_rounds D A fuel s.2 steps) (fun _ => aimed_noProgram_adversary _)
  · intro s
    exact aimed_noProgram_adversary _
  · intro a b s steps
    simp only [selectedDriver, simulateQ_bind, worldStreamRename_adversary, ← executeRounds_rename]
  · intro a b s
    exact worldStreamRename_adversary D a b _
  · intro rows s steps allowed
    dsimp only [selectedDriver]
    generalize ceremonyFuel circuits settings - 2 = fuel
    exact qb0_bind (AimedSetupDomain.executeRounds_ok rows D A fuel s.2 steps allowed)
      (fun _ => AimedSetupDomain.qb0_adversary_unallowed _ _)
  · intro rows s
    exact AimedSetupDomain.qb0_adversary_unallowed _ _
  · intro s first second alike
    dsimp only [selectedDriver]
    rw [executeRounds_alike D A (ceremonyFuel circuits settings - 2) s.2 first second alike]

theorem selectedDriver_tail (Z : Distinguisher C A.State TreeOutput)
    (r : (LifetimeBridge.JointInput C × A.State) × Option (RevealRows C)) :
    (selectedDriver D A circuits settings Z).tail K circuits settings r =
      LifetimeJointHop.tail K circuits settings D A Z r := by
  rcases r with ⟨s, _ | rows⟩ <;> rfl

end Fixed

section Driver

variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (T : TailDriver C E σ) (lawful : T.Lawful D)

theorem steps_rename (a b : HashOutput) (s : σ) (rows : RevealRows C) :
    (fun i => renameStep D a b (T.steps K circuits settings s rows i)) =
      T.steps K circuits settings s (aimedRowsSwap D a b rows) := by
  funext i
  exact renameStep_suspend_prssFinish K circuits settings (T.top s i) (T.tree s) D a b
    (T.keys s) i (rows i)

include lawful in
theorem tail_rename (a b : HashOutput) (s : σ) (rows : Option (RevealRows C)) :
    simulateQ (worldStreamRename D a b) (T.tail K circuits settings (s, rows)) =
      T.tail K circuits settings (s, rows.map (aimedRowsSwap D a b)) := by
  cases rows with
  | none => exact lawful.renameStop a b s
  | some rows =>
    change simulateQ (worldStreamRename D a b) (T.run s _) = T.run s _
    rw [lawful.rename, steps_rename]

include lawful in
theorem tail_noProgram (r : σ × Option (RevealRows C)) :
    IsQueryBoundP (T.tail K circuits settings r) AimedProgramCall 0 := by
  rcases r with ⟨s, _ | rows⟩
  · exact lawful.noProgramStop s
  · exact lawful.noProgram s _

end Driver

section Swap

variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (T : TailDriver C E σ) (lawful : T.Lawful D) (prims : Primitives)
include lawful

/-- The swap transports the private AES cache while preserving the hash cache and the flag.
This is `TreeKeyAimed`'s fixed-tail proof using the driver's renaming law. -/
theorem evalDist_tail_swap (a b : HashOutput) (st : σ) (watched rows : RevealRows C)
    (s : (HashCache C × KeyCache C) × Bool) :
    𝒟[Prod.map id (aimedStateSwap D a b) <$>
      (simulateQ (lazyAimedImpl prims D watched)
        (T.tail K circuits settings (st, some rows))).run s] =
    𝒟[(simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings
        (st, some (aimedRowsSwap D a b rows)))).run (aimedStateSwap D a b s)] := by
  rw [evalDist_lazyAimed_rename, tail_rename K circuits settings D T lawful]
  rfl

/-- At the boundary the private cache is empty, so the flag's law is invariant under the swap. -/
theorem probEvent_tail_swap (a b : HashOutput) (st : σ) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings
        (st, some (aimedRowsSwap D a b rows)))).run ((h, ∅), false)] := by
  have he := evalDist_tail_swap K circuits settings D T lawful prims a b st
    watched rows ((h, ∅), false)
  have hp := probEvent_congr' (p := fun y => y.2.2 = true) (fun _ _ => Iff.rfl) he
  simpa only [probEvent_map, Function.comp_def, Prod.map, aimedStateSwap,
    keyCacheSwap, involutionCache_empty] using hp

/-- Any finite chain of swaps preserves the flag probability. -/
theorem probEvent_tail_swaps (swaps : List (HashOutput × HashOutput)) (st : σ) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings
        (st, some (swaps.foldl (fun rs ab => aimedRowsSwap D ab.1 ab.2 rs) rows)))).run
          ((h, ∅), false)] := by
  induction swaps generalizing rows with
  | nil => rfl
  | cons ab swaps ih =>
    exact (probEvent_tail_swap K circuits settings D T lawful prims ab.1 ab.2
      st watched rows h).trans (ih (aimedRowsSwap D ab.1 ab.2 rows))

/-- The chain may be selected using fresh independent uniform values. This preserves the
flag's law; showing that the resulting computation is independent of the watched keys is separate. -/
theorem probEvent_tail_randomSwaps (m : ℕ) (swaps : (Fin m → HashOutput) → List (HashOutput × HashOutput))
    (st : σ) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | $ᵗ (Fin m → HashOutput) >>= fun u =>
      (simulateQ (lazyAimedImpl prims D watched)
        (T.tail K circuits settings
          (st, some ((swaps u).foldl (fun rs ab => aimedRowsSwap D ab.1 ab.2 rs) rows)))).run
            ((h, ∅), false)] := by
  rw [probEvent_bind_of_const _ (fun u _ =>
    (probEvent_tail_swaps K circuits settings D T lawful prims (swaps u)
      st watched rows h).symm)]
  simp

theorem probEvent_tail_perm (perm : Equiv.Perm HashOutput) (st : σ) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings
        (st, some (aimedRowsPerm D perm rows)))).run ((h, ∅), false)] := by
  induction perm using Equiv.Perm.swap_induction_on with
  | one => rw [aimedRowsPerm_one]
  | swap_mul perm a b hab ih =>
    rw [aimedRowsPerm_swap_mul]
    exact ih.trans (probEvent_tail_swap K circuits settings D T lawful prims a b
      st watched (aimedRowsPerm D perm rows) h)

/-- With distinct nonzero hidden keys, the executing keys may be replaced by any injective
named table. The watched keys and stored echo hashes stay fixed. -/
theorem probEvent_tail_mask (left right : KeyName C → HashOutput) (st : σ) (watched rows : RevealRows C) (h : HashCache C)
    (ha : KeysApart D (aimedRowsMask D left rows))
    (hr : Function.Injective
      (fun n : {n : KeyName C // Hidden D n ∧ ∃ k, RowKey rows n k} => right n))
    (hl0 : ∀ n, Hidden D n → (∃ k, RowKey rows n k) → left n ≠ 0)
    (hr0 : ∀ n, Hidden D n → (∃ k, RowKey rows n k) → right n ≠ 0) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings
        (st, some (aimedRowsMask D left rows)))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings
        (st, some (aimedRowsMask D right rows)))).run ((h, ∅), false)] := by
  obtain ⟨π, hs, ht⟩ := aimed_exists_perm_fix_zero
    (fun n : {n : KeyName C // Hidden D n ∧ ∃ k, RowKey rows n k} => left n)
    (fun n : {n : KeyName C // Hidden D n ∧ ∃ k, RowKey rows n k} => right n)
    (aimedRowsMask_injective D left rows ha) hr
    (fun n => hl0 n n.property.1 n.property.2) (fun n => hr0 n n.property.1 n.property.2)
  have he := probEvent_tail_perm K circuits settings D T lawful prims π
    st watched (aimedRowsMask D left rows) h
  rw [aimedRowsPerm_mask D π hs left right rows (fun n hn hrow => ht ⟨n, hn, hrow⟩)] at he
  exact he

end Swap

section Echo

open LifetimeReferenceBudget

variable {α : Type}

/-- The local identity inside `Tree.stepRound_prssEchoWith_split`. -/
theorem echoWith_roundLocal (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (next : C.Party → PrssKeys C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (prssEchoStepWith D active h out next) sent i =
      if prssEchoAccepted D active sent h (fun j => (out j).term) i then
        advance (next i (out i)).run else pure (.done none) := by
  unfold roundLocal
  by_cases hi : i ∈ D.1
  · simp [prssEchoStepWith, hi, prssEchoAccepted]
  · by_cases ha : active i
    · have hstep : prssEchoStepWith D active h out next i =
          .wait (prssEchoOutbox h (fun j => (out j).term) i)
            (fun inbox => (prssEchoResume h (fun j => (out j).term) i inbox (out i) >>= next i).run) := by
          simp [prssEchoStepWith, hi, ha]
      simp only [hstep, if_neg hi, prssEchoStepWith_delivered]
      rw [prssEchoStep_inbox, advance_bind, advance_prssEchoResume, pure_bind]
      simp only [prssEchoAccepted, hi, not_false_eq_true, ha, true_and]
      split_ifs <;> simp_all [continueStep]
    · simp [prssEchoStepWith, hi, ha, prssEchoAccepted]

/-- The pointwise body of `LifetimeReferenceBudget.echoSteps_round`. -/
theorem echoSteps_roundLocal (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (next : C.Party → PartyM C E RealSpec α) (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (echoSteps D active (echoValue D h keys) next) sent i =
      if AimedEchoAccepted D active sent h keys i then advance (next i).run else pure (.done none) := by
  unfold roundLocal
  by_cases hi : i ∈ D.1
  · simp [echoSteps, hi, AimedEchoAccepted]
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
      · simp only [AimedEchoAccepted, hab, not_true_eq_false, and_false, false_and, ↓reduceIte]
        rfl
      · rw [if_neg hab, advance_require_bind]
        rw [echoCheck_iff D active sent h keys i hi]
        simp only [AimedEchoAccepted, hi, ha, hab, Bool.false_eq_true, not_false_eq_true, true_and]
    · simp [echoSteps, hi, ha, AimedEchoAccepted]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives)

/-- `TreeKeyAimed.aimedReferenceRows_steps` for an arbitrary per-party continuation. -/
theorem referenceRows_steps_masked (D : C.Coalition)
    (h : Query C → HashOutput) (table normal : KeyName C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E)
    (next : C.Party → PrssKeys C → PartyM C E RealSpec α) (i : C.Party) :
    suspendStep (next i) (prssFinishStep i (aimedRowsMask D normal
      (aimedReferenceRows prims D h table active parts sentCommit sentReveal) i)) =
      prssEchoStepWith D (AimedReferenceActive D h active sentCommit sentReveal) h
        (aimedReferenceKeys prims D h table parts (fun i j => sentReveal j i))
        (fun i _ => next i (aimedReferenceKeys prims D h normal parts (fun i j => sentReveal j i) i)) i := by
  unfold aimedRowsMask
  rw [aimedReferenceRows_active]
  by_cases hi : i ∈ D.1
  · have ha : ¬ AimedReferenceActive D h active sentCommit sentReveal i := fun hh => hh.1 hi
    simp only [if_neg ha, Option.map_none, prssFinishStep, suspendStep, prssEchoStepWith, if_pos hi]
  · simp only [prssEchoStepWith, if_neg hi]
    by_cases ha : AimedReferenceActive D h active sentCommit sentReveal i
    · simp only [if_pos ha, Option.map_some, aimedMask_referenceKeys,
        prssFinishStep, suspendStep]
      have hd (j : C.Party) (f : C.Party → HashOutput) : (C.parties.map f).getD j.val 0 = f j := by
        simp [Committee.parties, List.getD_eq_getElem?_getD]
      simp only [hd]
      congr 1
      funext inbox
      simp only [exchangeResume, prssEchoResume, prssEchoCheck, prssEcho]
      split_ifs <;> simp [pure_bind, Option.elimM, Function.comp_def]
    · simp only [if_neg ha, Option.map_none, prssFinishStep, suspendStep]

/-- The named-key identity before lifting or sequencing any local program. -/
theorem echoWith_roundLocal_named (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next : C.Party → PartyM C E RealSpec α) (sent : C.Party → Mail C E) (i : C.Party)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h table parts revealed i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    roundLocal D (prssEchoStepWith D active h (aimedReferenceKeys prims D h table parts revealed)
      (fun i _ => next i)) sent i =
      if AimedEchoAccepted D active sent h
        (fun i => (aimedReferenceKeys prims D h (fun _ => 0) parts revealed i).term) i then
          advance (next i).run else pure (.done none) := by
  rw [echoWith_roundLocal]
  rw [aimedEchoAccepted_eq D active sent h _
    (fun i j T _ _ hT hiT hjT => aimedReferenceKeys_coherent prims D h table parts revealed i j T hT hiT hjT) hn i]
  have hc := aimedEchoCheck_known_congr D active sent h _ _
    (aimedReferenceKeys_known prims D h table (fun _ => 0) parts revealed) i
  simp only [AimedEchoAccepted, hc]
  split_ifs <;> rfl

end Echo

section Reference

open LifetimeReferenceBudget

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (T : TailDriver C E σ)

omit [Fintype E] [DecidableEq E] in
/-- The per-party form of `AimedSetupDomain.afterDerivation_allowed`. -/
theorem steps_allowed (s : σ) (rows : RevealRows C) (i : C.Party) :
    AimedSetupDomain.StepOk rows (T.steps K circuits settings s rows i) := by
  unfold TailDriver.steps
  rcases hrow : rows i with _ | ⟨out, shared⟩
  · exact trivial
  · intro inbox
    unfold exchangeResume
    dsimp only
    split_ifs
    · simp
    · have hp : AimedSetupDomain.POk (G := RealSpec) (⟨i, T.keys s i, out⟩ : Context C)
          ((do require (∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0]); pure out) >>=
            fun prss => (ceremonyAfterSetup K circuits settings
              ⟨i, T.keys s i, prss⟩ (T.top s i) (T.tree s) : PartyM C E RealSpec TreeOutput)) := by
        rw [bind_assoc]
        refine AimedSetupDomain.POk.bind (AimedSetupDomain.POk.require _) fun _ => ?_
        rw [pure_bind]
        exact AimedSetupDomain.POk.ceremonyAfterSetup K circuits settings (T.top s i) (T.tree s)
      exact IsQueryBoundP.of_imp
        (AimedSetupDomain.partyUnallowed_of_bad rows (ctx := ⟨i, T.keys s i, out⟩) hrow) hp

omit [Fintype E] [DecidableEq E] in
theorem tail_allowed (lawful : T.Lawful D) (r : σ × Option (RevealRows C)) :
    IsQueryBoundP (T.tail K circuits settings r) (AimedSetupDomain.Unallowed (rowsOf r.2)) 0 := by
  rcases r with ⟨s, _ | rows⟩
  · exact lawful.allowedStop _ _
  · exact lawful.allowed rows s _ (steps_allowed K circuits settings T s rows)

omit [Fintype E] [DecidableEq E] in
theorem tail_noSetup (lawful : T.Lawful D) (r : σ × Option (RevealRows C)) :
    IsQueryBoundP (T.tail K circuits settings r) aimedFreeSetup 0 :=
  IsQueryBoundP.of_imp (aimedFreeSetup_unallowed _) (tail_allowed K circuits settings D T lawful r)

variable (prims : Primitives)

theorem masked_alike (s : σ) (h : Query C → HashOutput)
    (table normal : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent revealed : C.Party → Mail C E)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h table parts (fun i j => revealed j i) i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    RoundAlike D
      (T.steps K circuits settings s (aimedRowsMask D normal
        (aimedReferenceRows prims D h table active parts sent revealed)))
      (T.steps K circuits settings s (referenceRows prims D h normal active parts sent revealed)) := by
  let cont := fun i prss => (ceremonyAfterSetup K circuits settings
    ⟨i, T.keys s i, prss⟩ (T.top s i) (T.tree s) : PartyM C E RealSpec TreeOutput)
  change RoundAlike D
    (fun i => suspendStep (cont i) (prssFinishStep i (aimedRowsMask D normal
      (aimedReferenceRows prims D h table active parts sent revealed) i)))
    (fun i => suspendStep (cont i) (prssFinishStep i
      (referenceRows prims D h normal active parts sent revealed i)))
  rw [funext (referenceRows_steps_masked prims D h table normal active parts sent revealed cont),
    referenceRows_steps prims D h normal active parts sent revealed cont]
  let act := AimedReferenceActive D h active sent revealed
  let raw := aimedReferenceKeys prims D h table parts (fun i j => revealed j i)
  let known := fun i => (aimedReferenceKeys prims D h (fun _ => 0) parts (fun i j => revealed j i) i).term
  let next := fun i => (ceremonyAfterSetup K circuits settings
    ⟨i, T.keys s i, aimedReferenceKeys prims D h normal parts (fun i j => revealed j i) i⟩
      (T.top s i) (T.tree s) : PartyM C E RealSpec TreeOutput)
  change RoundAlike D (prssEchoStepWith D act h raw (fun i _ => next i))
    (echoSteps D act (echoValue D h known) next)
  constructor
  · change (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      (prssEchoStepWith D act h raw (fun i _ => next i) i).outbox c else none) = _
    simp only [prssEchoStepWith_outbox, prssEchoStep_outbox]
    rw [show toCoalition D (echoSteps D act (echoValue D h known) next) =
      prssEchoVisible D act h known from echoSteps_visible _ _ _ _ _]
    exact prssEchoVisible_congr D act h h (fun i => (raw i).term) known
      (fun i j _ hj => congrArg h (sharedKeys_prss_congr D _ _ i j hj
        (aimedReferenceKeys_known prims D h table (fun _ => 0) parts (fun i j => revealed j i) i)))
  · intro i
    simp only [prssEchoStepWith, echoSteps]
    split_ifs <;> rfl
  · unfold AllDone
    apply forall_congr'
    intro i
    simp only [prssEchoStepWith, echoSteps]
    split_ifs <;> rfl
  · intro mail i
    exact (echoWith_roundLocal_named prims D act h table parts (fun i j => revealed j i)
      next mail i hn).trans (echoSteps_roundLocal D act h known next mail i).symm

/-- The reference is the actual driver on supported reference reveal answers. -/
def referenceAfterG (s : σ) (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (sent revealed : C.Party → Mail C E) :
    OracleComp (WorldSpec C) Bool :=
  T.run s (T.steps K circuits settings s (referenceRows prims D h normal active parts sent revealed))

theorem tail_masked_reference (lawful : T.Lawful D) (s : σ) (h : Query C → HashOutput)
    (table normal : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent revealed : C.Party → Mail C E)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h table parts (fun i j => revealed j i) i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    T.tail K circuits settings (s, some (aimedRowsMask D normal
      (aimedReferenceRows prims D h table active parts sent revealed))) =
        referenceAfterG K circuits settings D T prims s h normal active parts sent revealed :=
  lawful.alike s _ _ (masked_alike K circuits settings D T prims s h table normal active parts sent revealed hn)

omit [Fintype E] [DecidableEq E] in
theorem referenceAfterG_exposed (s : σ) (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (sent revealed : C.Party → Mail C E) :
    referenceAfterG K circuits settings D T prims s h normal active
      (keygenExposedParts D parts) sent revealed =
    referenceAfterG K circuits settings D T prims s h normal active parts sent revealed := by
  unfold referenceAfterG LifetimeReferenceBudget.referenceRows
  simp only [aimedReferenceKeys_exposed]

omit [Fintype E] [DecidableEq E] in
theorem referenceAfterG_noSetup (lawful : T.Lawful D) (s : σ) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent revealed : C.Party → Mail C E) :
    IsQueryBoundP (referenceAfterG K circuits settings D T prims s h normal active parts sent revealed)
      aimedFreeSetup 0 :=
  tail_noSetup K circuits settings D T lawful
    (s, some (referenceRows prims D h normal active parts sent revealed))

end Reference

section ReferenceCongruence

open LifetimeReferenceBudget

/-- Self echoes are omitted; distinct-party reference echoes depend only on
honest exposed keys and the corresponding public echo. -/
theorem echoValue_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (keys₁ keys₂ : C.Party → C.Term → HashOutput)
    (hk : ∀ i, i ∉ D.1 → keys₁ i = keys₂ i) (i j : C.Party)
    (he : prssEcho h₁ keys₁ i j = prssEcho h₂ keys₂ i j) :
    echoValue D h₁ keys₁ i j = echoValue D h₂ keys₂ i j := by
  by_cases hh : i ∉ D.1 ∧ j ∉ D.1 ∧ KeygenShareHidden D i j
  · have hex : ExposedAgree D keys₁ i j ↔ ExposedAgree D keys₂ i j := by
      simp only [ExposedAgree, hk i hh.1, hk j hh.2.1]
    simp only [echoValue, if_pos hh, hex]
  · simp only [echoValue, if_neg hh, he]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (T : TailDriver C E σ) (prims : Primitives)

omit [Fintype E] [DecidableEq E] in
/-- The reference step families agree even when unused self-echo list positions differ.
This is the pointwise form of `TreeKeyAimed.aimedReferenceAfter_oracle_congr`. -/
theorem referenceSteps_oracle_congr (s : σ) (h₁ h₂ : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent revealed : C.Party → Mail C E)
    (hc : ∀ i j values, h₁ (.commit .prss i j values) = h₂ (.commit .prss i j values))
    (hk : ∀ table i, i ∉ D.1 →
      aimedReferenceKeys prims D h₁ table parts (fun i j => revealed j i) i =
        aimedReferenceKeys prims D h₂ table parts (fun i j => revealed j i) i)
    (he : ∀ i j, i ∉ D.1 → j ≠ i →
      prssEcho h₁ (fun i => (aimedReferenceKeys prims D h₁ (fun _ => 0) parts
        (fun i j => revealed j i) i).term) i j =
      prssEcho h₂ (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts
        (fun i j => revealed j i) i).term) i j) :
    T.steps K circuits settings s (referenceRows prims D h₁ normal active parts sent revealed) =
      T.steps K circuits settings s (referenceRows prims D h₂ normal active parts sent revealed) := by
  have ha : AimedReferenceActive D h₁ active sent revealed =
      AimedReferenceActive D h₂ active sent revealed := by
    funext i
    simp only [AimedReferenceActive, aimedReferenceOpenCheck, hc]
  funext i
  unfold TailDriver.steps referenceRows
  rw [ha]
  by_cases hi : AimedReferenceActive D h₂ active sent revealed i
  · simp only [if_pos hi, hk normal i hi.1]
    apply congrArg (suspendStep _)
    apply aimedFinishStep_echo_congr
    intro j hji
    simp only [getD_parties]
    exact echoValue_congr D h₁ h₂ _ _
      (fun p hp => congrArg PrssKeys.term (hk (fun _ => 0) p hp)) i j (he i j hi.1 hji)
  · simp only [if_neg hi]

omit [Fintype E] [DecidableEq E] in
theorem referenceAfterG_oracle_congr (s : σ) (h₁ h₂ : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent revealed : C.Party → Mail C E)
    (hc : ∀ i j values, h₁ (.commit .prss i j values) = h₂ (.commit .prss i j values))
    (hk : ∀ table i, i ∉ D.1 →
      aimedReferenceKeys prims D h₁ table parts (fun i j => revealed j i) i =
        aimedReferenceKeys prims D h₂ table parts (fun i j => revealed j i) i)
    (he : ∀ i j, i ∉ D.1 → j ≠ i →
      prssEcho h₁ (fun i => (aimedReferenceKeys prims D h₁ (fun _ => 0) parts
        (fun i j => revealed j i) i).term) i j =
      prssEcho h₂ (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts
        (fun i j => revealed j i) i).term) i j) :
    referenceAfterG K circuits settings D T prims s h₁ normal active parts sent revealed =
      referenceAfterG K circuits settings D T prims s h₂ normal active parts sent revealed :=
  congrArg (T.run s) (referenceSteps_oracle_congr K circuits settings D T prims s h₁ h₂ normal active
    parts sent revealed hc hk he)

/-- Run the actual driver on reference rows chosen after the two setup sends. -/
def referenceTailG (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :
    OracleComp (WorldSpec C) Bool :=
  match r.2.2 with
  | none => pure false
  | some revealed => referenceAfterG K circuits settings D T prims r.1 h normal
      (prssCommitActive D r.2.1) parts r.2.1 revealed

omit [Fintype E] [DecidableEq E] in
theorem referenceTailG_exposed (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :
    referenceTailG K circuits settings D T prims h normal (keygenExposedParts D parts) r =
      referenceTailG K circuits settings D T prims h normal parts r := by
  unfold referenceTailG
  cases r.2.2
  · rfl
  · exact referenceAfterG_exposed K circuits settings D T prims _ _ _ _ _ _ _

omit [Fintype E] [DecidableEq E] in
theorem referenceTailG_noSetup (lawful : T.Lawful D) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :
    IsQueryBoundP (referenceTailG K circuits settings D T prims h normal parts r) aimedFreeSetup 0 := by
  unfold referenceTailG
  cases r.2.2
  · exact isQueryBoundP_pure _ _ _
  · exact referenceAfterG_noSetup K circuits settings D T prims lawful _ _ _ _ _ _ _

omit [Fintype E] [DecidableEq E] in
theorem referenceTailG_oracle_congr (h₁ h₂ : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (hc : ∀ i j values, h₁ (.commit .prss i j values) = h₂ (.commit .prss i j values))
    (hk : ∀ (revealed : C.Party → Mail C E) table i, i ∉ D.1 →
      aimedReferenceKeys prims D h₁ table parts (fun i j => revealed j i) i =
        aimedReferenceKeys prims D h₂ table parts (fun i j => revealed j i) i)
    (he : ∀ (revealed : C.Party → Mail C E) i j, i ∉ D.1 → j ≠ i →
      prssEcho h₁ (fun i => (aimedReferenceKeys prims D h₁ (fun _ => 0) parts
        (fun i j => revealed j i) i).term) i j =
      prssEcho h₂ (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts
        (fun i j => revealed j i) i).term) i j) :
    referenceTailG K circuits settings D T prims h₁ normal parts r =
      referenceTailG K circuits settings D T prims h₂ normal parts r := by
  unfold referenceTailG
  cases r.2.2 with
  | none => rfl
  | some revealed =>
    exact referenceAfterG_oracle_congr K circuits settings D T prims r.1 h₁ h₂ normal
      (prssCommitActive D r.2.1) parts r.2.1 revealed hc (hk revealed) (he revealed)

end ReferenceCongruence

section ReferenceProbability

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (T : TailDriver C E σ) (lawful : T.Lawful D) (prims : Primitives)
include lawful

/-- The fixed-oracle and eager comparison proofs of `TreeKeyAimed`, with the
actual lawful driver replacing its fixed executor. -/
theorem probEvent_tail_fixed_reference (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : σ)
    (watched : RevealRows C) (cache : HashCache C)
    (ha : KeysApart D (aimedRevealRowsFixed prims D h active parts
      (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal))
    (hzero : ∀ n, Hidden D n → h (hiddenInput parts n) ≠ 0)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hecho : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h (fun n => h (hiddenInput parts n))
        parts (fun i j => sentReveal j i) i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (T.tail K circuits settings
        (state, some (aimedRevealRowsFixed prims D h active parts
          (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal)))).run ((cache, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (referenceAfterG K circuits settings D T prims state h normal active parts
        sentCommit sentReveal)).run ((cache, ∅), false)] := by
  have he := aimedRevealRowsFixed_canonical prims D h active parts
    (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal
  have hm := probEvent_tail_mask K circuits settings D T lawful prims
    (fun n => h (hiddenInput parts n)) normal state watched
    (aimedRevealRowsFixed prims D h active parts (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal)
    cache (by rwa [he])
    (by intro a b hab; apply Subtype.ext; exact congrArg (fun n : {n : KeyName C // Hidden D n} => n.val) (hni (a₁ := ⟨a, a.property.1⟩)
      (a₂ := ⟨b, b.property.1⟩) hab))
    (fun n hn _ => hzero n hn) (fun n hn _ => hn0 n hn)
  rw [he] at hm
  rw [aimedRevealRowsFixed_reference, tail_masked_reference K circuits settings D T prims lawful state h _ normal active parts sentCommit sentReveal hecho] at hm
  rw [aimedRevealRowsFixed_reference]
  exact hm

theorem probEvent_tail_eager_reference (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : σ)
    (watched : RevealRows C)
    (ha : KeysApart D (aimedRevealRowsFixed prims D h active parts
      (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal))
    (hzero : ∀ n, Hidden D n → h (hiddenInput parts n) ≠ 0)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hecho : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h (fun n => h (hiddenInput parts n))
        parts (fun i j => sentReveal j i) i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    Pr[fun y => y.2 = true | aimedEagerFlag prims D h watched
      (T.tail K circuits settings
        (state, some (aimedRevealRowsFixed prims D h active parts
          (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal)))] =
    Pr[fun y => y.2 = true | aimedEagerFlag prims D h watched
      (referenceAfterG K circuits settings D T prims state h normal active parts
        sentCommit sentReveal)] := by
  unfold aimedEagerFlag
  rw [← probEvent_aimedFullCache, ← probEvent_aimedFullCache]
  exact probEvent_tail_fixed_reference K circuits settings D T lawful prims h normal
    active parts sentCommit sentReveal state watched (aimedFullCache h) ha hzero hni hn0 hecho

end ReferenceProbability

end ThresholdLeanXmssSecurity.LifetimeTailKernel

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.selectedDriver_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.selectedDriver_lawful

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.selectedDriver_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.selectedDriver_tail

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.probEvent_tail_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.probEvent_tail_mask

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.masked_alike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.masked_alike

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.referenceAfterG_oracle_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.referenceAfterG_oracle_congr

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.referenceTailG_oracle_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.referenceTailG_oracle_congr

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.referenceTailG_noSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.referenceTailG_noSetup

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.probEvent_tail_fixed_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.probEvent_tail_fixed_reference

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailKernel.probEvent_tail_eager_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailKernel.probEvent_tail_eager_reference
