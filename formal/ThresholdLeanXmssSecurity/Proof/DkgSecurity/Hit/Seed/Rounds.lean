import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Search
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Move

/-!
# One round of a phase from the values of the waiting operators

`levelRound` is one round of a phase from the values of the operators that wait in it.
`executeRounds_level` writes the run of a phase with `levelRound`, and `levelRound_congr` changes the
local step of a round where the round uses it.

`levelRound_congr_next` changes the local step `next` of a round only where the round
uses it, that is when no honest operator aborted and the inbox has no abort frame. There each honest
operator sends its message `out k x`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- The step of an operator from its values. `none` is an abort, and `some x` waits in a round with
the message `out x`. -/
def stageStep {X α : Type} (out : X → Mail C E) (resume : X → Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)) :
    Option X → Step C E RealSpec α
  | none => .done none
  | some x => .wait (out x) (resume x)

theorem advance_exchangeResume {α : Type} (f : Mail C E → PartyM C E RealSpec α) (inbox : Mail C E) :
    advance (exchangeResume f inbox) = if anyAbort inbox then pure (.done none) else advance (f inbox).run := by
  unfold exchangeResume anyAbort
  split_ifs <;> rfl

section Level

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The mail that the adversary reads in a round, from the values `d` of the operators. An operator
with `none` aborted and sends nothing. -/
def levelMail {X : Type} (d : C.Party → Option X) (out : C.Party → X → Mail C E) : C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (match d i with | none => none | some x => out i x c) else none

/-- The inbox of operator `j` after a round with the mail `sent` of the corrupt operators. An honest
operator that aborted sends the abort frame. -/
def levelInbox {X : Type} (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) : Mail C E :=
  fun k => if k ∈ D.1 then sent k j else match d k with | none => some .abort | some x => out k x j

/-- One round of a phase from the values `d` of the operators that wait in it, with at most `fuel`
rounds left. With no fuel the phase ends with no output. If each honest operator aborted, the phase
ends with no output and no round. Else the adversary reads the round. If one honest operator
aborted, each honest operator then ends with no output. Else each honest operator that reads no abort
frame takes its next local step `next`, and `cont` is the rest of the phase. -/
def levelRound {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option β)) :=
  match fuel with
  | 0 => pure (state, fun _ => none)
  | fuel + 1 =>
    if ∀ i, i ∉ D.1 → d i = none then pure (state, fun _ => none) else
    counted (liftComp (net.round state (levelMail D d out)) _) >>= fun r =>
      if ∃ i, i ∉ D.1 ∧ d i = none then pure (r.1, fun _ => none) else
      OverPermutation.sequenceFin (fun j => if j ∈ D.1 then pure none else
        match d j with
        | none => pure none
        | some x => if anyAbort (levelInbox D d out r.2 j) then pure none else
            free (next j x (levelInbox D d out r.2 j))) >>= cont fuel r.1

/-- The run of a phase from one round with the values `d` of the operators. The resume of each
operator aborts on an abort frame and else takes the local step `next`, which ends at a step `mk`. -/
theorem executeRounds_level {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (res : C.Party → X → Mail C E → OracleComp (PartySpec C E RealSpec) (Option β))
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y)) (mk : C.Party → Option Y → Step C E RealSpec β)
    (hmk : ∀ j, mk j none = .done none)
    (hadv : ∀ j x inbox, advance (res j x inbox) =
      if anyAbort inbox then pure (.done none) else next j x inbox >>= fun y => pure (mk j y)) :
    executeRounds worldRoles D net noFunctionality fuel state
        (fun j => if j ∈ D.1 then .done none else stageStep (out j) (res j) (d j)) =
      levelRound D net fuel state d out next fun fuel' state' d' =>
        executeRounds worldRoles D net noFunctionality fuel' state' (fun j => if j ∈ D.1 then .done none else mk j (d' j)) := by
  have hout : ∀ j, (if j ∈ D.1 then Step.done none else stageStep (out j) (res j) (d j) : Step C E RealSpec β).output =
      none := fun j => by
    by_cases hj : j ∈ D.1
    · simp [hj, Step.output]
    · rcases d j with _ | x <;> simp [hj, stageStep, Step.output]
  cases fuel with
  | zero =>
    simp only [executeRounds, levelRound, hout]
  | succ fuel =>
    have hdone : (∀ i, i ∉ D.1 → (if i ∈ D.1 then Step.done none else stageStep (out i) (res i) (d i) :
        Step C E RealSpec β).isDone) ↔ ∀ i, i ∉ D.1 → d i = none := by
      refine forall_congr' fun i => imp_congr_right fun hi => ?_
      rcases d i with _ | x <;> simp [hi, stageStep, Step.isDone]
    rw [executeRounds, levelRound]
    by_cases hall : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left (hdone.2 hall), ite_eq_left hall]
      simp only [hout]
    rw [ite_eq_right (fun h => hall (hdone.1 h)), ite_eq_right hall]
    have hcall : ¬ ((∃ i, i ∉ D.1 ∧ (if i ∈ D.1 then Step.done none else stageStep (out i) (res i) (d i) :
        Step C E RealSpec β).callInput.isSome) ∧ ∀ i, i ∉ D.1 →
          (if i ∈ D.1 then Step.done none else stageStep (out i) (res i) (d i) : Step C E RealSpec β).callInput.isSome ∨
          (if i ∈ D.1 then Step.done none else stageStep (out i) (res i) (d i) : Step C E RealSpec β).isDone) := by
      rintro ⟨⟨i, hi, h⟩, -⟩
      rcases hd : d i with _ | x <;> simp [hi, hd, stageStep, Step.callInput] at h
    have hmail : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
        (if i ∈ D.1 then Step.done none else stageStep (out i) (res i) (d i) : Step C E RealSpec β).outbox c else none) =
        levelMail D d out := by
      funext c i
      unfold levelMail
      by_cases h : c ∈ D.1 ∧ i ∉ D.1
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_right h.2]
        rcases d i with _ | x <;> rfl
      · rw [ite_eq_right h, ite_eq_right h]
    unfold stepRound
    rw [ite_eq_right hcall, hmail]
    simp only [worldRoles, bind_assoc]
    refine bind_congr fun r => ?_
    have hinbox : ∀ j, (fun k => if k ∈ D.1 then r.2 k j else
        (if k ∈ D.1 then Step.done none else stageStep (out k) (res k) (d k) : Step C E RealSpec β).delivered j) =
        levelInbox D d out r.2 j := fun j => by
      funext k
      unfold levelInbox
      by_cases hk : k ∈ D.1
      · rw [ite_eq_left hk, ite_eq_left hk]
      · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk]
        rcases d k with _ | x <;> rfl
    have hkey : ∀ (f g : C.Party → OracleComp (WorldSpec C) (Step C E RealSpec β)), (∀ j, f j = g j) →
        OverPermutation.sequenceFin f = OverPermutation.sequenceFin g := fun f g h => congrArg _ (funext h)
    by_cases hpart : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left hpart]
      obtain ⟨k0, hk0, hdk0⟩ := hpart
      rw [hkey _ (fun _ => pure (Step.done none)) (fun j => ?_), sequenceFin_pure, pure_bind, pure_bind]
      · rw [executeRounds_allDone D net noFunctionality _ fuel r.1 (fun _ => (Step.done none : Step C E RealSpec β))
          fun _ => trivial]
        simp [Step.output]
      · by_cases hj : j ∈ D.1
        · simp only [hj, ite_true]
        · rcases hd : d j with _ | x
          · simp only [hj, ite_false, stageStep]
          · simp only [hj, ite_false, stageStep]
            simp only [stageStep] at hinbox
            rw [hinbox j, hadv]
            have hab : anyAbort (levelInbox D d out r.2 j) = true := by
              unfold anyAbort
              refine List.any_eq_true.mpr ⟨k0, List.mem_finRange k0, ?_⟩
              simp [levelInbox, hk0, hdk0, Msg.isAbort]
            rw [ite_eq_left hab]
            simp [free]
    · rw [ite_eq_right hpart]
      rw [hkey _ (fun j => (if j ∈ D.1 then pure none else
          match d j with
          | none => pure none
          | some x => if anyAbort (levelInbox D d out r.2 j) then pure none else
              free (next j x (levelInbox D d out r.2 j))) >>= fun y =>
            pure (if j ∈ D.1 then Step.done none else mk j y)) (fun j => ?_), sequenceFin_bind_pure]
      · simp only [bind_assoc, pure_bind]
      · by_cases hj : j ∈ D.1
        · simp only [hj, ite_true, pure_bind]
        · rcases hd : d j with _ | x
          · simp only [hj, ite_false, stageStep, pure_bind, hmk]
          · simp only [hj, ite_false, stageStep]
            simp only [stageStep] at hinbox
            rw [hinbox j, hadv]
            split_ifs
            · simp [free, hmk]
            · simp [free]

theorem levelRound_congr {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont cont' : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (h : ∀ f s d', cont f s d' = cont' f s d') :
    levelRound D net fuel state d out next cont = levelRound D net fuel state d out next cont' := by
  rw [show cont = cont' from funext fun f => funext fun s => funext fun d' => h f s d']

/-- The local step of a round matters only for an honest operator `j` with values `x`, when no
honest operator aborted and the inbox of `j` has no abort frame. -/
theorem levelRound_congr_next {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (next next' : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (h : ∀ (sent : C.Party → C.Party → Option (Msg E)) j x, j ∉ D.1 → d j = some x → (∀ k, k ∉ D.1 → d k ≠ none) →
      anyAbort (levelInbox D d out sent j) = false →
      next j x (levelInbox D d out sent j) = next' j x (levelInbox D d out sent j)) :
    levelRound D net fuel state d out next cont = levelRound D net fuel state d out next' cont := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [levelRound, levelRound]
    by_cases hall : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left hall, ite_eq_left hall]
    rw [ite_eq_right hall, ite_eq_right hall]
    refine bind_congr fun r => ?_
    by_cases hpart : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left hpart, ite_eq_left hpart]
    rw [ite_eq_right hpart, ite_eq_right hpart]
    have hsome : ∀ k, k ∉ D.1 → d k ≠ none := fun k hk hdk => hpart ⟨k, hk, hdk⟩
    congr 1
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true]
    · simp only [hj, ite_false]
      rcases hd : d j with _ | x
      · rfl
      · dsimp only
        by_cases ha : anyAbort (levelInbox D d out r.2 j) = true
        · simp only [ha, ite_true]
        · have ha' : anyAbort (levelInbox D d out r.2 j) = false := by simpa using ha
          simp only [ha', Bool.false_eq_true, ite_false]
          rw [h r.2 j x hj hd hsome ha']

end Level

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.executeRounds_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.executeRounds_level

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.levelRound_congr_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.levelRound_congr_next
