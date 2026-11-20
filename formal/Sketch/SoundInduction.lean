import Sketch.Pilot

/-!
# The sound induction of the check from a start cache with earlier keys

`checkSoundFrom` is the sound induction of the batch check of
`ThresholdLeanXmssSecurity/Proof/CheckSound.lean` (`checkSoundRoundInduction`) in a more general
form. Each honest operator starts the check at the label `L` and the tag `tg`, and the start cache
satisfies `SoundCache L cache seen keys`. So the adversary can have earlier calls of `.coinKey` and
`.expand`, and the cache can hold the expansions of the earlier keys `keys`. The error is the
error of `pilotSoundError_sum`, with `keys.card` earlier expansion keys. The positive count of the
batch comes from the wrong tuple (`wrongTuple_sum_ne_zero`).

`checkSoundFrom_toReal` is the same bound in `ℝ` at the budget
`seen.card + checkRounds counts.sum * step`, which is the budget of `pilotSoundError`.
`checkSoundRoundInduction_of_from` gives the library form back at the label `0`, the tag `0` and
no earlier key.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity Finset
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra Bit E] [SampleableType E]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A wrong tuple has a position, so the batch has at least one position. -/
theorem wrongTuple_sum_ne_zero (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x) (hwrong : WrongTuple D x) :
    counts.sum ≠ 0 := by
  obtain ⟨m, hm, g, hg, _⟩ := hwrong
  rw [firstInput_length K hx] at hm
  rw [tupleAt_count K hx m, List.getD_eq_getElem _ _ hm] at hg
  have hle := List.le_sum_of_mem (List.getElem_mem hm)
  omega

/-- The sound induction of the check from the label `L`, the tag `tg` and a start cache with the
earlier coin key inputs `seen` and the earlier expansion keys `keys`. -/
def CheckSoundFrom (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (step q L tg : ℕ) (st : A.State)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput),
    TupleInputs K counts D x →
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) →
    (∀ state l, IsQueryBoundP (A.answer state l) Counted step) →
    SoundCache L cache seen keys → seen.card + checkRounds counts.sum * step ≤ q →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    WrongTuple D x →
    Pr{let out ←
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
            (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), L, tg⟩))).run' cache}[∃ i,
        i ∉ D.1 ∧ out.2 i = some ()] ≤
      ENNReal.ofReal (checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q +
        soundHashError counts.sum (q + keys.card))

/-- The sound induction of the check holds from each label, tag and start cache with earlier keys.
The proof is the proof of `checkSoundRoundInduction` in
`ThresholdLeanXmssSecurity/Proof/CheckSound.lean`, with the label `L`, the tag `tg`, the keys
`keys` in place of `0`, `0`, `∅`, and the key budget `keys.card + (halvings + 2)`. The wrong tuple
gives the positive count. -/
theorem checkSoundFrom (prims : Primitives) (K : Constants C E) : CheckSoundFrom prims K := by
  intro counts D A x step q L tg st cache seen keys hx hr ha hc hb hagree hwrong
  have hpos := wrongTuple_sum_ne_zero K hx hwrong
  let H := keys.card + (halvings counts.sum + 2)
  let F := 1 + 2 * (sliceBits + halvingSteps (sliceWidth counts.sum)) + 6
  let hs : C.Party → RunState C := fun i => ⟨filledHistory K i (x i), L, tg⟩
  let g : C.Party → List E → RunM C E (CheckSpec C E) Unit := fun i τ => do
    StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
    sliceProg K τ counts.sum sliceBits 0 (fun T k => wordWeightOf K τ counts.sum k * liftedPart (x i) (·.x) T k)
      (liftedPart (x i) (·.y)) (conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0) i
  let bad := soundInitialBad K D counts.sum (fun i => liftedPart (x i) (·.x))
    (fun i => liftedPart (x i) (·.y)) (fun i => liftedPart (x i) (·.z))
  have hF : checkRounds counts.sum = F + 1 := by unfold F checkRounds halvings; omega
  rw [hF]
  change Pr{let out ← (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) (F + 1) st
      (fun i => ((coinKey K (hybridCheckBuildingBlocks K i) >>= fun key => expand K key (coins counts.sum)) >>= g i).run'
        (hs i)))).run' cache}[∃ i, i ∉ D.1 ∧ out.2 i = some ()] ≤ _
  apply le_trans (sound_start_phase prims K D A F step (coins counts.sum) ha st hs tg L
    (fun i hi => ⟨rfl, rfl⟩) g cache seen keys hc bad
    ((coins counts.sum : ℝ≥0∞) / (Fintype.card E - 2 : ℕ))
    (sound_initial_weights K counts D x hx hpos hagree hwrong)
    ((halvings counts.sum + 1 : ℕ) * soundError E q H 2) ?_) ?_
  · intro p τ key cache' seen' hc' hn' hgood
    unfold soundStartNext
    simp only [g, require_bind_run']
    by_cases hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0
    · simp only [ite_eq_left hτ]
      apply sound_sliceRest_all prims K D A τ step q H counts.sum hr ha (sliceWidth_pos hpos) hτ
        sliceBits 0 1 (by omega) p.1 (fun i => i ∈ p.2)
        (fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) tg (L + 1)
        (fun i hi => ⟨rfl, rfl⟩)
      · exact hgood
      · exact hc'
      · simp only [checkRounds, halvings, Nat.add_mul, Nat.mul_add] at hb ⊢
        omega
      · have hk := Finset.card_insert_le key keys
        simp only [H, halvings]
        omega
    · simp only [ite_eq_right hτ, ite_self, executePhase_failure]
      simp
  · have hmono := soundError_mono (E := E) q H (coins counts.sum) seen keys (by omega) (by omega)
    calc
      _ ≤ soundError E q H (coins counts.sum) +
          (halvings counts.sum + 1 : ℕ) * soundError E q H 2 := by
        simpa only [add_assoc] using add_le_add hmono
          (le_refl ((halvings counts.sum + 1 : ℕ) * soundError E q H 2))
      _ = _ := pilotSoundError_sum K counts.sum q keys.card

/-- The sound induction at the budget `seen.card + checkRounds counts.sum * step`, as a real bound.
The bound is the sum of the first two terms of `pilotSoundError` with `seen.card` and
`keys.card`. -/
theorem checkSoundFrom_toReal (prims : Primitives) (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C))
    (step L tg : ℕ) (st : A.State) (cache : HashCache C) (seen : Finset (Query C))
    (keys : Finset HashOutput) (hx : TupleInputs K counts D x)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (ha : ∀ state l, IsQueryBoundP (A.answer state l) Counted step)
    (hc : SoundCache L cache seen keys)
    (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (hwrong : WrongTuple D x) :
    (Pr{let out ←
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
            (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), L, tg⟩))).run' cache}[∃ i,
        i ∉ D.1 ∧ out.2 i = some ()]).toReal ≤
      checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum)
          (seen.card + checkRounds counts.sum * step) +
        soundHashError counts.sum (seen.card + checkRounds counts.sum * step + keys.card) := by
  have hnonneg := add_nonneg
    (checkErrorOf_nonneg K (coins counts.sum) (halvings counts.sum) (seen.card + checkRounds counts.sum * step))
    (soundHashError_nonneg counts.sum (seen.card + checkRounds counts.sum * step + keys.card))
  exact (ENNReal.toReal_le_toReal (prEvent_ne_top _) ENNReal.ofReal_ne_top).mpr
    (checkSoundFrom prims K counts D A x step _ L tg st cache seen keys hx hr ha hc le_rfl hagree
      hwrong) |>.trans_eq (ENNReal.toReal_ofReal hnonneg)

/-- The sound induction from the label `0`, the tag `0` and no earlier key gives the library form
`CheckSoundRoundInduction`. -/
theorem checkSoundRoundInduction_of_from (prims : Primitives) (K : Constants C E) :
    CheckSoundRoundInduction prims K := by
  intro counts D A x step q st cache seen hx _ hr ha hc hb hagree hwrong
  simpa using checkSoundFrom prims K counts D A x step q 0 0 st cache seen ∅ hx hr ha
    (SoundCache.of_covered 0 cache seen hc) hb hagree hwrong

/-- info: 'ThresholdLeanXmss.Sketch.checkSoundFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkSoundFrom

/-- info: 'ThresholdLeanXmss.Sketch.checkSoundFrom_toReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkSoundFrom_toReal

end ThresholdLeanXmss.Sketch
