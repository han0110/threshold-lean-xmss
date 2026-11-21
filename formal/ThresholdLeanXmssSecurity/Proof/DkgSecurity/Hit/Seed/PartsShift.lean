import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.NormalShift

/-!
# The shift of the parts of a hidden term

`partsShift` proves `PartsShift`. The term parts of a hidden term `T` enter the normal form only
through the commit addresses and the derive addresses. The other reads of the parts are these.

* The reveal to a corrupt receiver holds only the shared terms, so no part of `T`
  (`revealTo_shiftAll`).
* The local step after round 2 reads the inbox only at corrupt senders. The lengths of the reveals do
  not depend on the parts (`length_revealTo`).
* `programBlock` reads the parameter parts, the pair parts and the term parts of the known terms
  (`programBlockView_congr`).

`levelRound_congr_out` changes the messages and the local step of a round together.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare (shiftAll)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## A round with two message functions -/

/-- Two rounds with the same mail to the corrupt operators, the same abort tags, and local steps that
agree on the two inboxes are equal. -/
theorem levelRound_congr_out (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) {X Y β : Type} (fuel : ℕ)
    (state : net.State) (d : C.Party → Option X) (out out' : C.Party → X → Mail C E)
    (next next' : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (hmail : ∀ c i x, c ∈ D.1 → i ∉ D.1 → out i x c = out' i x c)
    (habort : ∀ k x j, Msg.isAbort (out k x j) = Msg.isAbort (out' k x j))
    (hnext : ∀ sent j x, j ∉ D.1 → d j = some x →
      next j x (levelInbox D d out sent j) = next' j x (levelInbox D d out' sent j)) :
    levelRound D net fuel state d out next cont = levelRound D net fuel state d out' next' cont := by
  have hm : levelMail D d out = levelMail D d out' := by
    funext c i
    unfold levelMail
    split_ifs with h
    · rcases d i with _ | x
      · rfl
      · exact hmail c i x h.1 h.2
    · rfl
  have ha : ∀ sent j, anyAbort (levelInbox D d out sent j) = anyAbort (levelInbox D d out' sent j) := by
    intro sent j
    unfold anyAbort
    congr 1
    funext k
    unfold levelInbox
    split_ifs
    · rfl
    · rcases d k with _ | x
      · rfl
      · exact habort k x j
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [levelRound, levelRound, hm]
    by_cases hall : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left hall, ite_eq_left hall]
    rw [ite_eq_right hall, ite_eq_right hall]
    refine bind_congr fun r => ?_
    by_cases hpart : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left hpart, ite_eq_left hpart]
    rw [ite_eq_right hpart, ite_eq_right hpart]
    congr 1
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true]
    · simp only [hj, ite_false]
      rcases hd : d j with _ | x
      · rfl
      · dsimp only
        rw [ha r.2 j]
        split_ifs
        · rfl
        · rw [hnext r.2 j x hj hd]

/-! ## The parts after the shift -/

theorem shiftAll_parameter (T : C.Term) (c : C.Party → HashOutput) (parts : C.Party → Parts C) (k : C.Party) :
    (shiftAll T c parts k).parameter = (parts k).parameter := rfl

theorem shiftAll_pair (T : C.Term) (c : C.Party → HashOutput) (parts : C.Party → Parts C) (k m : C.Party) :
    (shiftAll T c parts k).pair m = (parts k).pair m := by
  simp [shiftAll, shiftParts]

theorem shiftAll_term_ne (T T' : C.Term) (c : C.Party → HashOutput) (parts : C.Party → Parts C) (k : C.Party)
    (h : T' ≠ T) : (shiftAll T c parts k).term T' = (parts k).term T' := by
  simp [shiftAll, shiftParts, Ne.symm h]

theorem length_revealTo (phase : Phase) (a b : Parts C) (i j : C.Party) :
    (revealTo phase a i j).length = (revealTo phase b i j).length := by
  simp only [revealTo, List.length_append, List.length_map, List.length_singleton]
  split_ifs <;> rfl

/-- The reveal of `k` to a receiver `j` that does not hold `T` does not change under the shift of `T`. -/
theorem revealTo_shiftAll (T : C.Term) (c : C.Party → HashOutput) (parts : C.Party → Parts C) (k j : C.Party)
    (hj : j ∉ C.holders T) : revealTo .seedGen (shiftAll T c parts k) k j = revealTo .seedGen (parts k) k j := by
  unfold revealTo
  rw [shiftAll_parameter, shiftAll_pair]
  congr 2
  refine List.map_congr_left fun T' hT' => shiftAll_term_ne T T' c parts k fun e => ?_
  subst e
  simp [sharedTerms] at hT'
  exact hj hT'.2.2

theorem known_ne (D : C.Coalition) (T T' : C.Term) (hT : ¬ KnownTo D.1 T) (hT' : KnownTo D.1 T') : T' ≠ T :=
  fun e => hT (e ▸ hT')

/-! ## The programming block -/

/-- `programBlock` with the view `view` as a parameter. -/
def programBlockView (D : C.Coalition) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (view : C.Party → C.Party → Parts C) : OracleComp (WorldSpec C) Unit := do
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let high ← free (liftComp ($ᵗ HashOutput) _)
  let _ ← program (.derive .seedGen .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
    (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      program (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
        (view (firstHonest (C.holders T)) k).term T)) ((dealt j).seed T)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]) ((dealt j).pairKey i)
    else pure true
  pure ()

theorem programBlock_eq_view (D : C.Coalition) (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E))
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    programBlock D log sent parameter dealt parts = programBlockView D parameter dealt fun i j =>
      if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j := rfl

/-- The programming block reads the parameter parts, the pair parts and the term parts of the known
terms. -/
theorem programBlockView_congr (D : C.Coalition) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (view view' : C.Party → C.Party → Parts C)
    (hpar : ∀ i j, (view i j).parameter = (view' i j).parameter)
    (hpair : ∀ i j m, (view i j).pair m = (view' i j).pair m)
    (hterm : ∀ i j T, KnownTo D.1 T → (view i j).term T = (view' i j).term T) :
    programBlockView D parameter dealt view = programBlockView D parameter dealt view' := by
  simp only [programBlockView, hpar, hpair]
  refine bind_congr fun high => bind_congr fun _ => ?_
  have h : (fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (C := C) (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
        (view ((C.parties.find? fun i => i ∈ C.holders T ∧ i ∉ D.1).getD (firstParty C)) k).term T))
          ((dealt j).seed T)
      | none => pure true) = (fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
        (view' ((C.parties.find? fun i => i ∈ C.holders T ∧ i ∉ D.1).getD (firstParty C)) k).term T))
          ((dealt j).seed T)
      | none => pure true) := by
    funext T
    split
    · next j hj =>
      have hk : KnownTo D.1 T := by
        have := List.find?_some hj
        simp only [decide_eq_true_eq] at this
        exact ⟨j, this.1, this.2⟩
      simp only [hterm _ _ T hk]
    · rfl
  rw [h]

/-! ## The local step after round 2 -/

theorem normView_inbox (D : C.Coalition) (parts : C.Party → Parts C) (j : C.Party) (L L' : Mail C E)
    (hL : ∀ k, k ∈ D.1 → L' k = L k) : normView D parts j L' = normView D parts j L := by
  funext k
  unfold normView
  split_ifs with hk
  · rw [hL k hk]
  · rfl

/-- After the shift, the local step of round 2 is the step of `seedGenAt` with the shifted addresses. -/
theorem revealNext_shift (D : C.Coalition) (parts : C.Party → Parts C) (T : C.Term) (c : C.Party → HashOutput)
    (committed : C.Party → Mail C E) (j : C.Party) (L L' : Mail C E) (hj : j ∉ D.1)
    (hL : ∀ k, k ∈ D.1 → L' k = L k) :
    revealNext D (shiftAll T c parts) committed j L' =
      revealNextAt D parts (commitAddress (shiftAll T c parts)) (termAddress D (shiftAll T c parts)) committed j L := by
  have hopen : (fun k => hashQuery (C := C) (openAddress D (shiftAll T c parts) j L' k)) =
      fun k => hashQuery (if k ∈ D.1 ∨ k = j then openAddress D parts j L k
        else commitAddress (shiftAll T c parts) k j) := by
    funext k
    by_cases hk : k ∈ D.1
    · rw [ite_eq_left (Or.inl hk), openAddress_corrupt _ _ _ _ _ hk, openAddress_corrupt _ _ _ _ _ hk, hL k hk]
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left (Or.inr rfl), openAddress_self _ _ _ _ hk, openAddress_self _ _ _ _ hk]
    · rw [ite_eq_right (by tauto), openAddress_honest _ _ _ _ _ hk hkj]
  have hcheck : ∀ opens, openCheck .seedGen j (shiftAll T c parts j) (committed j)
      (normRevealed D (shiftAll T c parts) j L') opens ↔
      openCheck .seedGen j (parts j) (committed j) (normRevealed D parts j L) opens := by
    intro opens
    unfold openCheck
    refine forall_congr' fun k => imp_congr_right fun hkj => and_congr_left fun _ => ?_
    rw [length_revealTo .seedGen (shiftAll T c parts j) (parts j)]
    by_cases hk : k ∈ D.1
    · simp only [normRevealed, hk, ite_true, hL k hk]
    · simp only [normRevealed, hk, ite_false, revealOutbox, Ne.symm hkj, Msg.hashesOf]
      rw [length_revealTo .seedGen (shiftAll T c parts k) (parts k)]
  have hderive : deriveKeys .seedGen j (normView D (shiftAll T c parts) j L') =
      deriveAt D parts (termAddress D (shiftAll T c parts)) j L := by
    have hv := normView_inbox D (shiftAll T c parts) j L L' hL
    have htA : termAddress D (shiftAll T c parts) j L' = termAddress D (shiftAll T c parts) j L := by
      funext T'
      unfold termAddress
      rw [hv]
    have hparV : ∀ k, (normView D (shiftAll T c parts) j L k).parameter = (normView D parts j L k).parameter := by
      intro k
      unfold normView
      split_ifs <;> rfl
    have hpairV : ∀ k m, (normView D (shiftAll T c parts) j L k).pair m = (normView D parts j L k).pair m := by
      intro k m
      unfold normView
      split_ifs
      · rfl
      · exact shiftAll_pair T c parts k m
    rw [deriveKeys_normView, htA, hv]
    unfold deriveAt
    simp only [hparV, hpairV]
  unfold revealNext revealNextAt
  rw [hopen]
  refine bind_congr fun opens => ?_
  by_cases h : openCheck .seedGen j (parts j) (committed j) (normRevealed D parts j L) opens
  · rw [ite_eq_left ((hcheck opens).2 h), ite_eq_left h, hderive]
  · rw [ite_eq_right (fun h' => h ((hcheck opens).1 h')), ite_eq_right h]

/-! ## The statement -/

theorem partsShift (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : PartsShift D net := by
  intro state early parameter dealt parts T c hT
  have hblock : ∀ (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E)),
      programBlock D log sent parameter dealt (shiftAll T c parts) = programBlock D log sent parameter dealt parts := by
    intro log sent
    rw [programBlock_eq_view, programBlock_eq_view]
    refine programBlockView_congr D parameter dealt _ _ (fun i j => ?_) (fun i j m => ?_) (fun i j T' hT' => ?_)
    · split_ifs <;> rfl
    · split_ifs
      · rfl
      · exact shiftAll_pair T c parts j m
    · split_ifs
      · rfl
      · exact shiftAll_term_ne T T' c parts j (known_ne D T T' hT hT')
  unfold seedGenNormal seedGenNormalWith seedGenAt
  rw [show commitDraws D (shiftAll T c parts) = commitDrawsAt D (commitAddress (shiftAll T c parts)) from rfl]
  refine bind_congr fun commitments => bind_congr fun r => ?_
  rw [hblock]
  refine bind_congr fun _ => ?_
  refine levelRound_congr_out D net _ _ _ _ _ _ _ _ (fun c' i x hc hi => ?_) (fun k x j => ?_)
    (fun sent j x hj _ => ?_)
  · unfold revealOutbox
    split_ifs
    · rfl
    · rw [revealTo_shiftAll T c parts i c' fun h => hT ⟨c', hc, h⟩]
  · unfold revealOutbox
    split_ifs <;> rfl
  · refine revealNext_shift D parts T c _ j _ _ hj fun k hk => ?_
    simp [levelInbox, hk]

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.partsShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.partsShift
