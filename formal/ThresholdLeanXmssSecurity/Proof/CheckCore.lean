import ThresholdLeanXmssSecurity.Proof.CheckSecurity
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# The core distance of the check

`CheckCoreDistance` of `Proof/CheckSecurity.lean`, split by the leak of `F_multVerify` on the
honest inputs.

* `F_multVerify` accepts. Masking the real outputs with the accept bit changes nothing
  (`checkMasked_eq_real_of_accept`), so step 4 compares the resulting runs.
* The honest copies agree but a tuple is wrong. Masking costs the probability that an honest
  operator accepts (`checkReal_masked_le`), which the soundness of step 2 bounds. The coupling of
  step 4 bounds the rest.
* The honest copies disagree. Steps 3 and 4 share one collision event, so this case keeps the whole
  bound.

The hash budget splits as `soundHashError + coupleHashError = checkHashError`
(`soundHash_add_coupleHash`). The soundness pays a collision of a coin key with one of the
`q + R + 2` cached expansion keys at each of the `R + 2` coins. The coupling pays a guess or a
collision of the `termHashes` honest history and digest points.

The file states two stages as named `Prop`s. `checkCoreDistanceSplit` of `Proof/CheckLast.lean`
uses them to prove `CheckCoreDistance`.

* `CheckSoundStage` (step 2) bounds the honest output probability of the real run when the copies
  agree and a tuple is wrong.
* `CheckCoupleStage` (step 4) bounds the masked real run against the ideal run when the copies agree.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable


/-! ## The corrupt operators output nothing -/

section CorruptNone

variable {C : Committee} {E : Type}

variable {ι : Type} {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
  (F : Functionality C I O L R)

/-- Every corrupt operator is done with no output. -/
def CorruptDone (steps : C.Party → Step C E (CallSpec I O) α) : Prop :=
  ∀ i ∈ D.1, steps i = Step.done none

theorem stepRound_corruptDone (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hs : CorruptDone D steps) :
    ∀ r ∈ support (stepRound localRoles D A F state steps), CorruptDone D r.2.1 := by
  intro r hr i hi
  unfold stepRound at hr
  split_ifs at hr
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨⟨st, out⟩, -, steps', hsteps', rfl⟩ := hr
    have h := mem_support_sequenceFin_oc _ steps' hsteps' i
    rw [hs i hi] at h
    simpa using h
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨⟨st, sent⟩, -, steps', hsteps', rfl⟩ := hr
    have h := mem_support_sequenceFin_oc _ steps' hsteps' i
    rw [hs i hi] at h
    simpa using h

theorem executeRounds_corrupt_none :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α), CorruptDone D steps →
      ∀ r ∈ support (executeRounds localRoles D A F fuel state steps), ∀ i ∈ D.1, r.2 i = none
  | 0, state, steps, hs => by
    intro r hr i hi
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [hs i hi, Step.output]
  | fuel + 1, state, steps, hs => by
    intro r hr i hi
    simp only [executeRounds] at hr
    split_ifs at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp [hs i hi, Step.output]
    · simp only [support_bind, Set.mem_iUnion] at hr
      obtain ⟨r', hr', hr⟩ := hr
      exact executeRounds_corrupt_none fuel r'.1 r'.2.1
        (stepRound_corruptDone D A F state steps hs r' hr') r hr i hi

/-- A corrupt operator has no output in a run of the local network. -/
theorem executePhase_corrupt_none (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E (CallSpec I O) α) :
    ∀ r ∈ support (executePhase localRoles D A F fuel state program), ∀ i ∈ D.1, r.2 i = none := by
  intro r hr
  unfold executePhase at hr
  simp only [support_bind, Set.mem_iUnion] at hr
  obtain ⟨steps, hsteps, hr⟩ := hr
  refine executeRounds_corrupt_none D A F fuel state steps (fun i hi => ?_) r hr
  have h := mem_support_sequenceFin_oc _ steps hsteps i
  simpa [hi] using h

end CorruptNone

/-! ## Identical until a bad event -/

section UntilBad

variable {C : Committee}

/-- Two local games that share a prefix and agree after each prefix output that is not bad differ
by at most the probability of a bad prefix output. -/
theorem localAccepts_bind_sub_le (prims : Primitives) {β : Type} (oa : OracleComp (LocalSpec C) β)
    (f g : β → OracleComp (LocalSpec C) Bool) (bad : β → Prop)
    (h : ∀ b ∈ support oa, ¬ bad b → f b = g b) :
    |localAccepts prims (oa >>= f) - localAccepts prims (oa >>= g)| ≤
      (Pr{let z ← (simulateQ (localAnswer prims) oa).run' ∅}[bad z]).toReal := by
  have hrun : ∀ k : β → OracleComp (LocalSpec C) Bool,
      Pr{let b ← (simulateQ (localAnswer prims) (oa >>= k)).run' ∅}[b = true] =
        Pr{let b ← (simulateQ (localAnswer prims) oa).run ∅ >>= fun p =>
          (simulateQ (localAnswer prims) (k p.1)).run' p.2}[b = true] := by
    intro k
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  have hbad : Pr{let z ← (simulateQ (localAnswer prims) oa).run' ∅}[bad z] =
      Pr{let p ← (simulateQ (localAnswer prims) oa).run ∅}[bad p.1] := by
    rw [StateT.run'_eq, prEvent_map]
  have hsupp : ∀ p ∈ support ((simulateQ (localAnswer prims) oa).run ∅), p.1 ∈ support oa := by
    intro p hp
    apply support_simulateQ_run'_subset (localAnswer prims) oa ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨p, hp, rfl⟩
  have h1 := prEvent_bind_le_add_of_disagree (ε₂ := 0) (q := fun b : Bool => b = true)
    (my := fun p => (simulateQ (localAnswer prims) (f p.1)).run' p.2)
    (oc := fun p => (simulateQ (localAnswer prims) (g p.1)).run' p.2) (le_of_eq hbad.symm)
    (fun p hp hn => by rw [h p.1 (hsupp p hp) hn, add_zero])
  have h2 := prEvent_bind_le_add_of_disagree (ε₂ := 0) (q := fun b : Bool => b = true)
    (my := fun p => (simulateQ (localAnswer prims) (g p.1)).run' p.2)
    (oc := fun p => (simulateQ (localAnswer prims) (f p.1)).run' p.2) (le_of_eq hbad.symm)
    (fun p hp hn => by rw [h p.1 (hsupp p hp) hn, add_zero])
  rw [add_zero, ← hrun, ← hrun] at h1 h2
  unfold localAccepts
  have hf : Pr{let b ← (simulateQ (localAnswer prims) (oa >>= f)).run' ∅}[b = true] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  have hg : Pr{let b ← (simulateQ (localAnswer prims) (oa >>= g)).run' ∅}[b = true] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  have he : Pr{let z ← (simulateQ (localAnswer prims) oa).run' ∅}[bad z] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  have h1' := (ENNReal.toReal_le_toReal hf (ENNReal.add_ne_top.mpr ⟨hg, he⟩)).mpr h1
  have h2' := (ENNReal.toReal_le_toReal hg (ENNReal.add_ne_top.mpr ⟨hf, he⟩)).mpr h2
  rw [ENNReal.toReal_add hg he] at h1'
  rw [ENNReal.toReal_add hf he] at h2'
  rw [abs_le]
  constructor <;> linarith

end UntilBad

/-! ## The masked real run -/

section Masked

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The real run of the check on the shared cache, before the distinguisher. -/
def checkRealRun (K : Constants C E) (fuel : ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option Unit)) := do
  let st ← A.start (corruptInputs D x) z
  executePhase localRoles D A (checkFunctionalities K) fuel st fun i => checkProtocol K i (x i)

/-- The real run with the honest outputs masked by the accept bit of `F_multVerify`, as the ideal run
masks them. -/
def checkMaskedLocal (K : Constants C E) (fuel : ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) :
    OracleComp (LocalSpec C) Bool := do
  let r ← checkRealRun K fuel D A x z
  let l := multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))
  Z (r.1, fun i => if i ∉ D.1 ∧ l.2.2 ∧ r.2 i = some () then some () else none)

/-- The honest holders agree on every copy, the first conjunct of the accept bit of `F_multVerify`. -/
def MultVerifyAgree (D : C.Coalition) (inputs : C.Party → Option (List (Tuple C))) : Prop :=
  ∀ k < (firstInput inputs).length, ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 →
    ∀ g < (((List.range (firstInput inputs).length).map (tupleAt inputs)).getD k
        ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count,
      ((inputs i).bind (·[k]?)).map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) =
        ((inputs j).bind (·[k]?)).map fun τ => (τ.x T g, τ.y T g, τ.z T g)

set_option linter.unusedSectionVars false in
theorem checkRealLocal_eq (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux)
    (Z : Distinguisher C A.State Unit) :
    checkRealLocal K fuel D A x z Z = checkRealRun K fuel D A x z >>= Z := by
  rw [checkRealRun, bind_assoc]
  rfl

set_option linter.unusedSectionVars false in
theorem checkMaskedLocal_eq (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux)
    (Z : Distinguisher C A.State Unit) :
    checkMaskedLocal K fuel D A x z Z = checkRealRun K fuel D A x z >>= fun r =>
      Z (r.1, fun i => if i ∉ D.1 ∧ (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 ∧
        r.2 i = some () then some () else none) := rfl

set_option linter.unusedSectionVars false in
theorem checkRealRun_corrupt_none (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux) :
    ∀ r ∈ support (checkRealRun K fuel D A x z), ∀ i ∈ D.1, r.2 i = none := by
  intro r hr
  unfold checkRealRun at hr
  simp only [support_bind, Set.mem_iUnion] at hr
  obtain ⟨st, -, hr⟩ := hr
  exact executePhase_corrupt_none D A _ fuel st _ r hr

/-- The masked output is the output when no corrupt operator outputs and `F_multVerify` accepts or no
honest operator outputs. -/
theorem mask_eq_self (D : C.Coalition) (accept : Bool) (out : C.Party → Option Unit)
    (hD : ∀ i ∈ D.1, out i = none) (h : accept = true ∨ ∀ i, i ∉ D.1 → out i = none) :
    (fun i => if i ∉ D.1 ∧ accept ∧ out i = some () then some () else none) = out := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, hD i hi]
  · rcases h with h | h
    · cases out i <;> simp [hi, h]
    · simp [hi, h i hi]

/-- With an accepting `F_multVerify`, masking changes nothing. -/
theorem checkMasked_eq_real_of_accept (prims : Primitives) (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux)
    (Z : Distinguisher C A.State Unit)
    (h : (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 = true) :
    localAccepts prims (checkMaskedLocal K fuel D A x z Z) = localAccepts prims (checkRealLocal K fuel D A x z Z) := by
  have hd := localAccepts_bind_sub_le prims (checkRealRun K fuel D A x z)
    (fun r => Z (r.1, fun i => if i ∉ D.1 ∧ (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 ∧
        r.2 i = some () then some () else none)) Z (fun _ => False)
    (fun r hr _ => by
      rw [mask_eq_self D _ r.2 (checkRealRun_corrupt_none K fuel D A x z r hr) (Or.inl h)])
  rw [checkMaskedLocal_eq, checkRealLocal_eq]
  have h0 : Pr{let _ : A.State × (C.Party → Option Unit) ←
      (simulateQ (localAnswer prims) (checkRealRun K fuel D A x z)).run' ∅}[False] = 0 := by simp
  rw [h0, ENNReal.toReal_zero] at hd
  linarith [abs_nonneg (localAccepts prims (checkRealRun K fuel D A x z >>= fun r =>
      Z (r.1, fun i => if i ∉ D.1 ∧ (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 ∧
        r.2 i = some () then some () else none)) - localAccepts prims (checkRealRun K fuel D A x z >>= Z)),
    abs_sub_abs_le_abs_sub (localAccepts prims (checkRealRun K fuel D A x z >>= fun r =>
      Z (r.1, fun i => if i ∉ D.1 ∧ (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 ∧
        r.2 i = some () then some () else none))) (localAccepts prims (checkRealRun K fuel D A x z >>= Z)),
    abs_le.mp hd]

/-- Masking the real run costs the probability that an honest operator outputs while `F_multVerify`
rejects (step 1). -/
theorem checkReal_masked_le (prims : Primitives) (K : Constants C E) (fuel : ℕ) (D : C.Coalition)
    (A : CheckAdversary C E (List (Tuple C))) (x : C.Party → List (Tuple C)) (z : Aux)
    (Z : Distinguisher C A.State Unit) :
    |localAccepts prims (checkRealLocal K fuel D A x z Z) - localAccepts prims (checkMaskedLocal K fuel D A x z Z)| ≤
      (Pr{let r ←
        (simulateQ (localAnswer prims) (checkRealRun K fuel D A x z)).run' ∅}[∃ i, i ∉ D.1 ∧ r.2 i = some ()]).toReal := by
  by_cases hacc : (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 = true
  · rw [checkMasked_eq_real_of_accept prims K fuel D A x z Z hacc, sub_self, abs_zero]
    exact ENNReal.toReal_nonneg
  rw [checkMaskedLocal_eq, checkRealLocal_eq]
  refine localAccepts_bind_sub_le prims _ _ _ _ fun r hr hn => ?_
  rw [mask_eq_self D _ r.2 (checkRealRun_corrupt_none K fuel D A x z r hr) (Or.inr fun i hi => ?_)]
  cases hout : r.2 i with
  | none => rfl
  | some u => exact absurd ⟨i, hi, hout⟩ hn

end Masked

/-! ## The hash budget -/

section Budget

variable {C : Committee}

/-- The soundness pays, at each of the `R + 2` coins, a collision of the coin key with one of the
`q + R + 2` cached expansion keys. -/
def soundHashError (count q : ℕ) : ℝ :=
  ((halvings count + 2) * (q + halvings count + 2) : ℕ) / 2 ^ 256

/-- The coupling pays a guess or a collision of the `termHashes` honest history and digest points
among the counted calls, `(q + termHashes)^2`, and the rest of `checkHashError`, namely a counted
call or an honest point that hits one of the `R + 2` coin keys. -/
def coupleHashError (C : Committee) (count q : ℕ) : ℝ :=
  ((q + termHashes C) ^ 2 + (halvings count + 2) * (q + 2 * termHashes C) : ℕ) / 2 ^ 256

lemma soundHashError_nonneg (count q : ℕ) : 0 ≤ soundHashError count q := by
  unfold soundHashError; positivity

/-- The two parts are exactly `checkHashError`. -/
theorem soundHash_add_coupleHash (count q : ℕ) :
    soundHashError count q + coupleHashError C count q = checkHashError C count q := by
  unfold soundHashError coupleHashError checkHashError
  rw [← add_div]
  congr 1
  push_cast
  ring

theorem soundHash_add_coupleHash_le (count q : ℕ) :
    soundHashError count q + coupleHashError C count q ≤ checkHashError C count q :=
  (soundHash_add_coupleHash count q).le

lemma coupleHashError_le (count q : ℕ) : coupleHashError C count q ≤ checkHashError C count q := by
  rw [← soundHash_add_coupleHash count q]
  linarith [soundHashError_nonneg count q]

end Budget

/-! ## The stages and the assembly -/

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- Step 2: when the honest copies agree but a tuple is wrong, an honest operator of the real run
outputs with probability at most the soundness error of GS20, Lemmas 8 to 10, plus the coin-key
collisions. -/
def CheckSoundStage (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) (q : ℕ),
    TupleInputs K counts D x → IsQueryBounded A Z (checkRounds counts.sum) q →
    counts.sum ≠ 0 → q < 2 ^ 128 →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 = false →
    (Pr{let r ←
      (simulateQ (localAnswer prims) (checkRealRun K (checkRounds counts.sum) D A x z)).run' ∅}[∃ i, i ∉ D.1 ∧ r.2 i = some ()]).toReal ≤
      checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q + soundHashError counts.sum q

/-- Step 4: when the honest copies agree, the masked real run and the ideal run on
`canonicalDummyTuples` differ only by a guess or a collision of the honest history and digest
points. -/
def CheckCoupleStage (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) (q : ℕ),
    TupleInputs K counts D x → IsQueryBounded A Z (checkRounds counts.sum) q →
    counts.sum ≠ 0 → q < 2 ^ 128 →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    |localAccepts prims (checkMaskedLocal K (checkRounds counts.sum) D A x z Z) -
      localAccepts prims (checkIdealLocal K (checkRounds counts.sum) D A x z Z)| ≤
      coupleHashError C counts.sum q

end Assembly

end ThresholdLeanXmssSecurity
