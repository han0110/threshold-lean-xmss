import ThresholdLeanXmssSecurity.Proof.CheckCore
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The three stages of the check core distance

The target is `CheckSoundStage`, `CheckCoupleStage` and `CheckSplitStage` of `Proof/CheckCore.lean`.
The stages are named hypotheses of `checkCoreDistanceProof`.

The local couplings for `CheckCoupleStage` (step 4 of the plan of `Proof/CheckSecurity.lean`):

* `finalStep_tv`: the final segment of the check (randomization, salts, digests, last challenge and
  opening), against any rushing adversary with any selective abort. From two states related by
  `FinalRel` (hidden-term differences, equal corrupt shares, equal claim errors) and related
  histories, the real and the simulated runs differ by twice the hiding bound of the salted digests
  (`saltDigestPhase_hide`). The proof moves the two hidden tables past the ghost digests, the digest
  round and the last coin (`sameRun_samples_swap`) and ends with `finalMaskNetwork_sameRun`.

* `halvRest_all`: the halving loop (GS20, Protocol 14) followed by the final segment. From two states
  related by `HalvRel` (Shamir vectors with hidden-term differences and equal corrupt shares, claims
  whose difference is the difference of the inner products) and `HistRel`, the two runs differ by at
  most `coupleBound`, for any live set. Each step: the multiplication leaks the same view
  (`halvInputs_view`), its hidden output difference goes to the lacked term (`multFinish_diff`), the
  coin and the challenge are common (`executePhase_afterChallenge_common'`), and `halvRel_step` keeps
  the relation for every challenge.

`CheckCoupleStage` additionally covers the start (first coin, `expand`, `require`), the slice loop (Gruen's
step with replicated products) with its transition into `HalvRel`, the initial relation of the inputs
and of `canonicalDummyTuples`, and the budget arithmetic of `coupleBound` against `coupleHashError`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

section Stages

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## The final segment of the check -/

/-- The check after the masked multiplication of the randomization. -/
def finalRest (K : Constants C E) (i : C.Party) (a b d : E) (w q : Shares C E) :
    RunM C E (CheckSpec C E) Unit := do
  let salts ← (hybridCheckGadgets K i).randBits 256
  compareDigests (localContext i) salts.1
  finalAfterDigests K i (conv K (localContext i) w 0) (conv K (localContext i) w 1) a b d
    (conv K (localContext i) q 0) (conv K (localContext i) q 1)

theorem finalStep_eq (K : Constants C E) (i : C.Party) (Av Bv : ℕ → E) (V : E) (A B : C.Party → E)
    (hA : A i = Av 0) (hB : B i = Bv 0) :
    finalStep K (localContext i) (hybridCheckGadgets K i) (Av, Bv, V) = (do
      let w ← (hybridCheckGadgets K i).randElements 2
      let q ← (hybridCheckGadgets K i).extendMult (maskedProducts K A B i w.1)
      finalRest K i (A i) (B i) V w.1 q) := by
  simp only [finalStep, finalRest, finalAfterDigests, finalOpenProgram, maskedProducts]
  rw [hA, hB]
  refine bind_congr fun w => bind_congr fun q => bind_congr fun s => bind_congr fun _ =>
    bind_congr fun r => ?_
  apply StateT.ext
  intro s
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  rfl

variable {Ia : Type}

/-- The program of an honest operator after the masked multiplication of the randomization. -/
def finalMaskedProgram (K : Constants C E) (D : C.Coalition) (A B V : C.Party → E) (hs : C.Party → RunState C)
    (known : Shares C E) (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (w q : MaskTable C E) (i : C.Party) : PartyM C E (CheckSpec C E) Unit :=
  afterExtend K i 2 ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
    (finalRest K i (A i) (B i) (V i) (randShares D 2 known w i))
    (multFinish D 2 (filler K .peer) (fun g => extendTotal K D (maskedInputs K D known w A B) g + attack g)
      knownQ offset receivers q i)

/-- The randomization phase: both adaptive replies come before the two hidden tables. -/
theorem finalStep_masks (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (Av Bv : C.Party → ℕ → E) (V : C.Party → E) (hs : C.Party → RunState C) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) st
        (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i)))
      (do
        let p ← (leftAdversary (rightAdversary Ad)).answer st ()
        let p' ← (rightAdversary (leftAdversary Ad)).answer p.1
          (maskedView K D p.2.1 0 (fun j => Av j 0) (fun j => Bv j 0))
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel p'.1
          (finalMaskedProgram K D (fun j => Av j 0) (fun j => Bv j 0) V hs p.2.1 p'.2.1 p'.2.2.1 p'.2.2.2.1
            p'.2.2.2.2 w q)) := by
  have he : (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i)) =
      (fun i => (do
        let w ← (hybridCheckGadgets K i).randElements 2
        let q ← (hybridCheckGadgets K i).extendMult
          (maskedProducts K (fun j => Av j 0) (fun j => Bv j 0) i w.1)
        finalRest K i (Av i 0) (Bv i 0) (V i) w.1 q).run' (hs i)) := by
    funext i
    rw [finalStep_eq K i (Av i) (Bv i) (V i) (fun j => Av j 0) (fun j => Bv j 0) rfl rfl]
  rw [he]
  exact executePhase_finalMasks prims K D Ad fuel st (fun j => Av j 0) (fun j => Bv j 0) hs
    (fun i w q => finalRest K i (Av i 0) (Bv i 0) (V i) w q)

/-- The output share of the masked multiplication at an honest receiver. -/
def finalOut (K : Constants C E) (D : C.Coalition) (A B : C.Party → E) (known : Shares C E) (attack : ℕ → E)
    (knownQ : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party) (w q : MaskTable C E)
    (i : C.Party) : Shares C E :=
  (multFinish D 2 (filler K .peer) (maskedResult K D known attack w A B)
    knownQ offset receivers q i).getD (fun _ _ => 0)

/-- The running state after the masked multiplication. -/
def finalState (K : Constants C E) (hs : C.Party → RunState C) (z : C.Party → Shares C E) (i : C.Party) :
    RunState C :=
  ⟨recordHistory K i (hs i).history (z i) 2, (hs i).label + 1, (hs i).tag⟩

lemma multFinish_honest (D : C.Coalition) (width : ℕ) (filled : C.Term → ℕ → Option C.Party)
    (result : ℕ → E) (known : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (fresh : C.Term → Fin width → E) (i : C.Party) (hi : i ∉ D.1) :
    multFinish D width filled result known offset receivers fresh i =
      if i ∈ receivers then some ((multFinish D width filled result known offset receivers fresh i).getD 0)
      else none := by
  by_cases hr : i ∈ receivers <;> simp [multFinish, hi, hr]

/-- A missing receiver of the masked multiplication stops the salts for everyone. -/
theorem finalMasked_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (A B V : C.Party → E) (hs : C.Party → RunState C)
    (known : Shares C E) (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (w q : MaskTable C E) (hmiss : ∃ i, i ∉ D.1 ∧ i ∉ receivers) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (finalMaskedProgram K D A B V hs known attack knownQ offset receivers w q) = pure (st, fun _ => none) := by
  rw [executePhase_congr_honest D Ad _ _ st _
    (fun i => if i ∈ receivers then
      ((hybridCheckGadgets K i).randBits 256 >>= fun salts => (do
        compareDigests (localContext i) salts.1
        finalAfterDigests K i (conv K (localContext i) (randShares D 2 known w i) 0)
          (conv K (localContext i) (randShares D 2 known w i) 1) (A i) (B i) (V i)
          (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 0)
          (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 1))).run'
        (finalState K (fun j => ⟨(hs j).history, (hs j).label + 1, (hs j).tag⟩)
          (finalOut K D A B known attack knownQ offset receivers w q) i)
      else failure)]
  · convert executePhase_randBits_missing K D Ad fuel st 256 _ (fun i => i ∈ receivers) _ hmiss using 4
  · intro i hi
    unfold finalMaskedProgram
    rw [multFinish_honest D 2 _ _ _ _ _ _ i hi]
    by_cases hr : i ∈ receivers
    · simp only [if_pos hr, afterExtend, finalRest, finalOut, finalState]
      rfl
    · simp only [if_neg hr, afterExtend]

/-! ### Generic reorderings -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma mixedGhostDigests_bind_pure {α : Type} (D : C.Coalition)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) :
    ∀ (Ts : List C.Term) (k : List (DigestColumn C) → OracleComp (LocalSpec C) α),
      mixedGhostDigests D known Ts k = mixedGhostDigests D known Ts pure >>= k
  | [], k => by simp [mixedGhostDigests]
  | T :: Ts, k => by
    simp only [mixedGhostDigests]
    split_ifs
    · simp only [bind_assoc]
      refine bind_congr fun col => ?_
      rw [mixedGhostDigests_bind_pure D known Ts, mixedGhostDigests_bind_pure D known Ts (fun cs => pure (col :: cs)),
        bind_assoc]
      simp only [pure_bind]
    · simp only [bind_assoc]
      refine bind_congr fun d => ?_
      rw [mixedGhostDigests_bind_pure D known Ts,
        mixedGhostDigests_bind_pure D known Ts (fun cs => pure (digestColumnValues D T d :: cs)), bind_assoc]
      simp only [pure_bind]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma mixedGhostDigests_congr {α : Type} (D : C.Coalition)
    (known known' : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (h : ∀ T, KnownTo D.1 T → known T = known' T) :
    ∀ (Ts : List C.Term) (k : List (DigestColumn C) → OracleComp (LocalSpec C) α),
      mixedGhostDigests D known Ts k = mixedGhostDigests D known' Ts k
  | [], k => rfl
  | T :: Ts, k => by
    simp only [mixedGhostDigests]
    split_ifs with hT
    · rw [h T hT]
      exact bind_congr fun col => mixedGhostDigests_congr D known known' h Ts _
    · exact bind_congr fun d => mixedGhostDigests_congr D known known' h Ts _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Two samples that a computation does not read commute with it. -/
lemma sameRun_samples_swap (prims : Primitives) {α β γ : Type} [SampleableType α]
    (ob : OracleComp (LocalSpec C) β) (k : α → α → β → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (do let w ← liftComp ($ᵗ α) (LocalSpec C); let q ← liftComp ($ᵗ α) (LocalSpec C); ob >>= k w q)
      (ob >>= fun b => do
        let w ← liftComp ($ᵗ α) (LocalSpec C); let q ← liftComp ($ᵗ α) (LocalSpec C); k w q b) := by
  have h := sameRun_swap prims
    (do let w ← liftComp ($ᵗ α) (LocalSpec C); let q ← liftComp ($ᵗ α) (LocalSpec C); pure (w, q)) ob
    (fun a b => k a.1 a.2 b)
  simpa only [bind_assoc, pure_bind] using h

/-- A challenge phase with some live honest operators. -/
theorem executePhase_challenge_live {α : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C)
    (g : C.Party → E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i) else failure) =
    if ∀ i, i ∉ D.1 → live i then (do
      let p ← runFunctionality localRoles D (leftAdversary (leftAdversary Ad)) (Fcoin (E := E)) st
        (fun i => if i ∈ D.1 then none else some 1)
      executePhase localRoles D Ad (checkFunctionalities K) fuel p.1
        (fun i => afterChallenge K (hs i) (g i) (p.2 i)))
    else pure (st, fun _ => none) := by
  split_ifs with hall
  · rw [executePhase_congr_honest D Ad _ _ st _ (fun i => (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i))
      (fun i hi => if_pos (hall i hi))]
    exact executePhase_challenge K D Ad fuel st hs g
  · push Not at hall
    let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
        PartyM C E (CheckSpec C E) α := fun i o => match o with
      | some (.inl (.inl v)) => oracleStep (challengeQuery K (hs i).tag (hs i).label v) >>= fun r => match r with
          | some r => (g i r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
          | none => failure
      | _ => failure
    have hp : (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i) else failure) =
        (fun i => optionalCall (if live i then some (.inl (.inl 1)) else none) (next i)) := by
      funext i
      by_cases hi : live i <;> simp only [hi, if_true, if_false, optionalCall, challenge_run', next]
      apply bind_congr
      intro o
      rcases o with _ | ((a | b) | (c | d)) <;> rfl
    rw [hp]
    apply executePhase_partialCall_abort
    · intro i hi; rfl
    · obtain ⟨i, hi, hl⟩ := hall
      exact ⟨i, hi, if_neg hl⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma localStep_pure' {ι α : Type} {G : OracleSpec ι} (a : α) :
    (localStep (pure a : OracleComp (LocalSpec C) α) : PartyM C E G α) = pure a := by
  simp [localStep]

/-- After a common coin, the honest operators read one common challenge. -/
theorem executePhase_afterChallenge_common (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (Ad : CheckAdversary C E Ia) (fuel : ℕ) (st : Ad.State) (hs : C.Party → RunState C) (tg L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tg ∧ (hs i).label = L) (v : List E) (rec : Finset C.Party)
    (hrec : ∃ i, i ∉ D.1 ∧ i ∈ rec) (P : C.Party → E → PartyM C E (CheckSpec C E) Unit) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) fuel st
        (fun i => afterChallenge K (hs i) (fun r => StateT.lift (P i r))
          (if i ∉ D.1 ∧ i ∈ rec then some v else none)))
      (do
        let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel st
          (fun i => match r with
            | some r => if i ∈ rec then P i r else failure
            | none => failure)) := by
  let f : C.Party → Option E → PartyM C E (CheckSpec C E) Unit := fun i r =>
    if i ∉ D.1 ∧ i ∈ rec then (match r with
      | some r => P i r
      | none => failure) else failure
  let oa : C.Party → OracleComp (LocalSpec C) (Option E) := fun i =>
    if i ∉ D.1 ∧ i ∈ rec then liftComp (challengeQuery K tg L v) (LocalSpec C) else pure none
  have hp : (fun i => afterChallenge K (hs i) (fun r => StateT.lift (P i r))
      (if i ∉ D.1 ∧ i ∈ rec then some v else none)) = (fun i => localStep (oa i) >>= f i) := by
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ rec
    · simp only [hi, afterChallenge, oa, f, oracleStep, (htag i hi.1).1, (htag i hi.1).2]
      refine bind_congr fun r => ?_
      rcases r with _ | r
      · rfl
      · simp [StateT.run'_eq, StateT.run_lift]
    · simp only [hi, if_false, afterChallenge, oa, f, localStep_pure', pure_bind]
  rw [hp]
  refine (executePhase_local_fallback prims D Ad _ fuel st oa (fun _ => none) f).trans ?_
  have hsel : SameRun prims (Concrete.sequenceFin (fun i => if i ∈ D.1 then pure none else oa i))
      (do let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
          pure (fun i => if i ∉ D.1 ∧ i ∈ rec then r else none)) := by
    convert sameRun_sequenceFin_selected prims (challengeQuery K tg L v) none
      (fun i => i ∉ D.1 ∧ i ∈ rec) hrec using 2
    · funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr, oa]
    · funext r
      congr 1
      funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr]
  refine (hsel.bind fun vs => SameRun.refl prims _).trans ?_
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro r
  apply SameRun.of_eq
  apply executePhase_congr_honest
  intro i hi
  by_cases hr : i ∈ rec
  · rcases r with _ | r <;> simp [f, hi, hr]
  · rcases r with _ | r <;> simp [f, hi, hr]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- `SameRun.bind_right` for continuations that agree on the support only. -/
lemma SameRun.bind_right_of_support (prims : Primitives) {α β : Type} (oa : OracleComp (LocalSpec C) α)
    {f g : α → OracleComp (LocalSpec C) β} (P : α → Prop) (hP : ∀ x ∈ support oa, P x)
    (h : ∀ a, P a → SameRun prims (f a) (g a)) : SameRun prims (oa >>= f) (oa >>= g) := by
  have hf : oa >>= f = oa >>= fun a => if P a then f a else g a :=
    bind_congr_of_forall_mem_support oa fun x hx => by simp [hP x hx]
  rw [hf]
  apply SameRun.bind_right
  intro a
  by_cases ha : P a
  · simpa [ha] using h a ha
  · simpa [ha] using SameRun.refl prims (g a)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma findChallenge_support (K : Constants C E) (key : HashOutput) :
    ∀ (tries index : ℕ) (x : Option E), x ∈ support (findChallenge K key tries index) →
      ∀ r, x = some r → r ≠ 0 ∧ r ≠ 1
  | 0, index, x, hx, r, hr => by
    simp only [findChallenge, support_pure, Set.mem_singleton_iff] at hx
    subst hx; cases hr
  | tries + 1, index, x, hx, r, hr => by
    simp only [findChallenge, support_bind, Set.mem_iUnion] at hx
    obtain ⟨h, -, hx⟩ := hx
    split at hx
    · rename_i hne _
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      cases hr
      exact hne
    · exact findChallenge_support K key tries (index + 1) x hx r hr

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma challengeQuery_support (K : Constants C E) (tg L : ℕ) (v : List E) (x : Option E)
    (hx : x ∈ support (liftComp (challengeQuery K tg L v) (LocalSpec C))) :
    ∀ r, x = some r → r ≠ 0 ∧ r ≠ 1 := by
  rw [support_liftComp] at hx
  simp only [challengeQuery, support_bind, Set.mem_iUnion] at hx
  obtain ⟨key, -, hx⟩ := hx
  exact findChallenge_support K key challengeTries 0 x hx

/-- The relation of the two final states: the masks hide a difference on the hidden terms only, and
the claim errors agree. -/
def FinalRel (K : Constants C E) (D : C.Coalition) (AR BR VR AD BD VD : C.Party → E) : Prop :=
  ∃ (delta : MaskTable C E) (deltaD : C.Term → E) (a b a' b' d d' : E),
    (∀ T, KnownTo D.1 T → ∀ g, delta T g = 0) ∧ (∀ T, KnownTo D.1 T → deltaD T = 0) ∧
    IsShamir K AR a ∧ IsShamir K BR b ∧ IsShamir K AD a' ∧ IsShamir K BD b' ∧
    (∀ i ∈ D.1, AR i = AD i) ∧ (∀ i ∈ D.1, BR i = BD i) ∧
    ∑ T, delta T 0 = a - a' ∧ ∑ T, delta T 1 = b - b' ∧ ∑ T, deltaD T = d - d' ∧ d - a * b = d' - a' * b' ∧
    (∀ i, i ∉ D.1 → AR i - AD i = conv K (localContext i) (fun T _ => delta T 0) 0) ∧
    (∀ i, i ∉ D.1 → BR i - BD i = conv K (localContext i) (fun T _ => delta T 1) 0) ∧
    (∀ i, i ∉ D.1 → VR i - VD i = conv K (localContext i) (fun T _ => deltaD T) 0)

/-- The last opening after a common coin, with the two hidden tables drawn first. -/
theorem ghostFinalCoin (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (p1 : Ad.State) (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (hrecv : ∀ i, i ∉ D.1 → i ∈ receivers)
    (rec : Finset C.Party) (v : List E) (tg L : ℕ)
    (hsR hsD : MaskTable C E → MaskTable C E → C.Party → RunState C)
    (htagR : ∀ w q i, i ∉ D.1 → (hsR w q i).tag = tg ∧ (hsR w q i).label = L)
    (htagD : ∀ w q i, i ∉ D.1 → (hsD w q i).tag = tg ∧ (hsD w q i).label = L)
    (AR BR VR AD BD VD : C.Party → E) (hrel : FinalRel K D AR BR VR AD BD VD)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    SameRun prims
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel p1
          (fun i => afterChallenge K (hsR w q i) (fun r => StateT.lift (finalOpenProgram K i
            (finalMaskVector K D known knownQ attack offset receivers r AR BR VR w q i)))
            (if i ∉ D.1 ∧ i ∈ rec then some v else none)) >>= tail)
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel p1
          (fun i => afterChallenge K (hsD w q i) (fun r => StateT.lift (finalOpenProgram K i
            (finalMaskVector K D known knownQ attack offset receivers r AD BD VD w q i)))
            (if i ∉ D.1 ∧ i ∈ rec then some v else none)) >>= tail) := by
  letI : CharP E 2 := charP_two
  obtain ⟨delta, deltaD, a, b, a', b', d, d', hknown, hknownD, hA, hB, hA', hB', hCA, hCB, hda, hdb, hdd, herr,
    hlA, hlB, hlD⟩ := hrel
  obtain ⟨T₀, -, hT₀⟩ := lackedTerm_spec D
  by_cases hrec : ∃ i, i ∉ D.1 ∧ i ∈ rec
  · -- the common challenge
    let KX : (C.Party → E) → (C.Party → E) → (C.Party → E) → MaskTable C E → MaskTable C E → Option E →
        OracleComp (LocalSpec C) β := fun A B V w q r =>
      executePhase localRoles D Ad (checkFunctionalities K) fuel p1 (fun i => match r with
        | some r => if i ∈ rec then finalOpenProgram K i
            (finalMaskVector K D known knownQ attack offset receivers r A B V w q i) else failure
        | none => failure) >>= tail
    have hcom : ∀ (hs : MaskTable C E → MaskTable C E → C.Party → RunState C)
        (htag : ∀ w q i, i ∉ D.1 → (hs w q i).tag = tg ∧ (hs w q i).label = L) (A B V : C.Party → E),
        SameRun prims
          (do
            let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            executePhase localRoles D Ad (checkFunctionalities K) fuel p1
              (fun i => afterChallenge K (hs w q i) (fun r => StateT.lift (finalOpenProgram K i
                (finalMaskVector K D known knownQ attack offset receivers r A B V w q i)))
                (if i ∉ D.1 ∧ i ∈ rec then some v else none)) >>= tail)
          (do
            let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
            let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            KX A B V w q r) := by
      intro hs htag A B V
      refine SameRun.trans ?_ (sameRun_samples_swap prims (liftComp (challengeQuery K tg L v) (LocalSpec C))
        (fun w q r => KX A B V w q r))
      apply SameRun.bind_right
      intro w
      apply SameRun.bind_right
      intro q
      have h := (executePhase_afterChallenge_common prims K D Ad fuel p1 (hs w q) tg L (htag w q) v rec hrec
        (fun i r => finalOpenProgram K i (finalMaskVector K D known knownQ attack offset receivers r A B V w q i))).bind
        (fun out => SameRun.refl prims (tail out))
      simpa only [bind_assoc, KX] using h
    refine (hcom hsR htagR AR BR VR).trans (SameRun.trans ?_ (hcom hsD htagD AD BD VD).symm)
    refine SameRun.bind_right_of_support prims _ (fun r => ∀ r', r = some r' → r' ≠ 0 ∧ r' ≠ 1)
      (challengeQuery_support K tg L v) ?_
    intro r hr
    rcases r with _ | r
    · apply SameRun.of_eq
      simp only [KX]
    · have hr1 : 1 + r ≠ 0 := by
        intro h
        apply (hr r rfl).2
        have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
        linear_combination h - h2
      have hnet : ∀ (A B V : C.Party → E) (w q : MaskTable C E), KX A B V w q (some r) =
          finalMaskNetwork K D Ad (checkFunctionalities K) fuel p1 (fun i => i ∈ rec) known knownQ attack offset
            receivers r A B V w q >>= tail := by
        intro A B V w q
        simp only [KX, finalMaskNetwork]
        congr 1
        apply executePhase_congr_honest
        intro i _
        by_cases h : i ∈ rec <;> simp [h]
      simp only [hnet]
      have h := (finalMaskNetwork_sameRun prims K D Ad (checkFunctionalities K) fuel p1 (fun i => i ∈ rec) known
        knownQ attack offset receivers T₀ hT₀ r delta deltaD AR BR VR AD BD VD a b a' b' d d' hr1 hknown hknownD
        hA hB hA' hB' hCA hCB hda hdb hdd herr (fun i hi _ => hrecv i hi) (fun i hi _ => hlA i hi)
        (fun i hi _ => hlB i hi) (fun i hi _ => hlD i hi)).bind (fun out => SameRun.refl prims (tail out))
      simpa only [bind_assoc] using h
  · push Not at hrec
    have hfail : ∀ (hs : MaskTable C E → MaskTable C E → C.Party → RunState C) (A B V : C.Party → E)
        (w q : MaskTable C E),
        executePhase localRoles D Ad (checkFunctionalities K) fuel p1
          (fun i => afterChallenge K (hs w q i) (fun r => StateT.lift (finalOpenProgram K i
            (finalMaskVector K D known knownQ attack offset receivers r A B V w q i)))
            (if i ∉ D.1 ∧ i ∈ rec then some v else none)) = pure (p1, fun _ => none) := by
      intro hs A B V w q
      rw [executePhase_congr_honest D Ad _ fuel p1 _ (fun _ => failure), executePhase_failure]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ rec) := fun h => hrec i h.1 h.2
      simp only [hn, if_false, afterChallenge]
    apply SameRun.of_eq
    simp only [hfail]

/-- The program of an honest operator after the digests. -/
def finalTail (K : Constants C E) (D : C.Coalition) (known knownQ : Shares C E) (attack : ℕ → E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (A B V : C.Party → E) (w q : MaskTable C E)
    (i : C.Party) : RunM C E (CheckSpec C E) Unit :=
  finalAfterDigests K i (maskShare K D known w 0 i) (maskShare K D known w 1 i) (A i) (B i) (V i)
    (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 0)
    (conv K (localContext i) (finalOut K D A B known attack knownQ offset receivers w q i) 1)

lemma finalTail_eq (K : Constants C E) (D : C.Coalition) (known knownQ : Shares C E) (attack : ℕ → E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (A B V : C.Party → E) (w q : MaskTable C E)
    (i : C.Party) :
    finalTail K D known knownQ attack offset receivers A B V w q i =
      challenge K (hybridCheckGadgets K i) >>= fun r => StateT.lift (finalOpenProgram K i
        (finalMaskVector K D known knownQ attack offset receivers r A B V w q i)) := rfl

/-- The coin of the last challenge and the adversary's reply to it. -/
def coinDraw (D : C.Coalition) (Ad : CheckAdversary C E Ia) (p0 : Ad.State) :
    OracleComp (LocalSpec C)
      ((Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
        (Ad.State × Finset C.Party)) := do
  let v ← liftComp ($ᵗ (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E))
    (LocalSpec C)
  let p ← (leftAdversary (leftAdversary Ad)).answer p0 (List.ofFn v)
  pure (v, p)

/-- The rest of the run after the coin of the last challenge. -/
def coinNext {β : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (fuel : ℕ)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (A B V : C.Party → E) (hs : MaskTable C E → MaskTable C E → C.Party → RunState C)
    (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) (w q : MaskTable C E)
    (x : (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
      (Ad.State × Finset C.Party)) : OracleComp (LocalSpec C) β :=
  executePhase localRoles D Ad (checkFunctionalities K) fuel x.2.1 (fun i =>
    afterChallenge K (hs w q i) (fun r => StateT.lift (finalOpenProgram K i
      (finalMaskVector K D known knownQ attack offset receivers r A B V w q i)))
      (if i ∉ D.1 ∧ i ∈ x.2.2 then some (List.ofFn x.1) else none)) >>= tail

/-- The challenge and the last opening, with the two hidden tables drawn first. -/
theorem ghostFinalChallenge (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (p0 : Ad.State) (live : C.Party → Prop) (known knownQ : Shares C E) (attack : ℕ → E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (hrecv : ∀ i, i ∉ D.1 → i ∈ receivers)
    (tg L : ℕ) (hsR hsD : MaskTable C E → MaskTable C E → C.Party → RunState C)
    (htagR : ∀ w q i, i ∉ D.1 → (hsR w q i).tag = tg ∧ (hsR w q i).label = L)
    (htagD : ∀ w q i, i ∉ D.1 → (hsD w q i).tag = tg ∧ (hsD w q i).label = L)
    (AR BR VR AD BD VD : C.Party → E) (hrel : FinalRel K D AR BR VR AD BD VD)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    SameRun prims
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) p0
          (fun i => if live i then
            (finalTail K D known knownQ attack offset receivers AR BR VR w q i).run' (hsR w q i)
            else failure) >>= tail)
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) p0
          (fun i => if live i then
            (finalTail K D known knownQ attack offset receivers AD BD VD w q i).run' (hsD w q i)
            else failure) >>= tail) := by
  simp only [finalTail_eq, executePhase_challenge_live]
  split_ifs with hall
  · have hin : ∀ i, i ∉ D.1 → ((if i ∈ D.1 then none else some 1 : Option ℕ)).isSome := by
      intro i hi; simp [hi]
    rw [runFunctionality_coin_local D (leftAdversary (leftAdversary Ad)) p0 _ hin]
    have side : ∀ (A B V : C.Party → E) (hs : MaskTable C E → MaskTable C E → C.Party → RunState C),
        SameRun prims
          (do
            let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            (do
              let p ← (do
                let v ← liftComp ($ᵗ (Fin (firstInput fun i => if i ∈ D.1 then none else some 1) → E))
                  (LocalSpec C)
                let p ← (leftAdversary (leftAdversary Ad)).answer p0 (List.ofFn v)
                pure (p.1, fun i => if i ∉ D.1 ∧ i ∈ p.2 then some (List.ofFn v) else none))
              executePhase localRoles D Ad (checkFunctionalities K) fuel p.1 fun i =>
                afterChallenge K (hs w q i) (fun r => StateT.lift (finalOpenProgram K i
                  (finalMaskVector K D known knownQ attack offset receivers r A B V w q i))) (p.2 i)) >>= tail)
          (coinDraw D Ad p0 >>= fun x => do
            let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
            coinNext K D Ad fuel known knownQ attack offset receivers A B V hs tail w q x) := by
      intro A B V hs
      refine SameRun.trans (SameRun.of_eq ?_) (sameRun_samples_swap prims (coinDraw D Ad p0)
        (coinNext K D Ad fuel known knownQ attack offset receivers A B V hs tail))
      simp only [coinDraw, coinNext, bind_assoc, pure_bind]
    refine (side AR BR VR hsR).trans (SameRun.trans ?_ (side AD BD VD hsD).symm)
    apply SameRun.bind_right
    intro x
    exact ghostFinalCoin prims K D Ad fuel x.2.1 known knownQ attack offset receivers hrecv x.2.2 (List.ofFn x.1)
      tg L hsR hsD htagR htagD AR BR VR AD BD VD hrel tail
  · simp only [pure_bind]
    exact SameRun.refl prims _

/-- The rest of the run after the digest round. -/
def roundNext {β : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (fuel : ℕ)
    (ds : C.Party → List HashOutput) (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (A B V : C.Party → E) (hs : MaskTable C E → MaskTable C E → C.Party → RunState C)
    (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) (w q : MaskTable C E)
    (pr : Ad.State × (C.Party → C.Party → Option (Msg E))) : OracleComp (LocalSpec C) β :=
  executePhase localRoles D Ad (checkFunctionalities K) fuel pr.1
    (fun i => if digestLive D ds pr.2 i then
      (finalTail K D known knownQ attack offset receivers A B V w q i).run' (hs w q i) else failure) >>= tail

/-- The digest round, the challenge and the last opening, with the two hidden tables drawn first. -/
theorem ghostDigestRound (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (p0 : Ad.State) (ds : C.Party → List HashOutput) (known knownQ : Shares C E) (attack : ℕ → E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (hrecv : ∀ i, i ∉ D.1 → i ∈ receivers)
    (tg L : ℕ) (hsR hsD : MaskTable C E → MaskTable C E → C.Party → RunState C)
    (htagR : ∀ w q i, i ∉ D.1 → (hsR w q i).tag = tg ∧ (hsR w q i).label = L)
    (htagD : ∀ w q i, i ∉ D.1 → (hsD w q i).tag = tg ∧ (hsD w q i).label = L)
    (AR BR VR AD BD VD : C.Party → E) (hrel : FinalRel K D AR BR VR AD BD VD)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    SameRun prims
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) p0
          (fun i => afterDigests i (ds i)
            ((finalTail K D known knownQ attack offset receivers AR BR VR w q i).run' (hsR w q i))) >>= tail)
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) p0
          (fun i => afterDigests i (ds i)
            ((finalTail K D known knownQ attack offset receivers AD BD VD w q i).run' (hsD w q i))) >>= tail) := by
  have side : ∀ (A B V : C.Party → E) (hs : MaskTable C E → MaskTable C E → C.Party → RunState C),
      SameRun prims
        (do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) p0
            (fun i => afterDigests i (ds i)
              ((finalTail K D known knownQ attack offset receivers A B V w q i).run' (hs w q i))) >>= tail)
        (Ad.round p0 (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then digestOutbox i (ds i) c else none) >>= fun pr => do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          roundNext K D Ad (fuel + 1) ds known knownQ attack offset receivers A B V hs tail w q pr) := by
    intro A B V hs
    refine SameRun.trans (SameRun.of_eq ?_) (sameRun_samples_swap prims
      (Ad.round p0 (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then digestOutbox i (ds i) c else none))
      (roundNext K D Ad (fuel + 1) ds known knownQ attack offset receivers A B V hs tail))
    simp only [executePhase_afterDigests_round, bind_assoc]
    rfl
  refine (side AR BR VR hsR).trans (SameRun.trans ?_ (side AD BD VD hsD).symm)
  apply SameRun.bind_right
  intro pr
  exact ghostFinalChallenge prims K D Ad fuel pr.1 (digestLive D ds pr.2) known knownQ attack offset receivers hrecv
    tg L hsR hsD htagR htagD AR BR VR AD BD VD hrel tail

/-- The running states after the masked multiplication, from the states before the randomization. -/
def finalHs (K : Constants C E) (hs : C.Party → RunState C) (z : C.Party → Shares C E) : C.Party → RunState C :=
  finalState K (fun j => ⟨(hs j).history, (hs j).label + 1, (hs j).tag⟩) z

/-- The known terms of the masked multiplication do not depend on the hidden tables. -/
lemma finalOut_known (K : Constants C E) (D : C.Coalition) (A B A' B' : C.Party → E) (known : Shares C E)
    (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (w q w' q' : MaskTable C E) (i : C.Party) (T : C.Term) (hT : KnownTo D.1 T) :
    finalOut K D A B known attack knownQ offset receivers w q i T =
      finalOut K D A' B' known attack knownQ offset receivers w' q' i T := by
  have hnot : lackedTerm D.1 ≠ some T := fun h => lackedTerm_unknown D T h hT
  unfold finalOut multFinish
  by_cases hi : i ∈ D.1 ∨ i ∉ receivers
  · simp only [if_pos hi, Option.getD_none]
  · simp only [if_neg hi, Option.getD_some, hnot, if_false, hT, if_true]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma ghost_reassoc {σ' γ δ : Type} (ans : OracleComp (LocalSpec C) σ') (mg : σ' → OracleComp (LocalSpec C) γ)
    (k : σ' → γ → OracleComp (LocalSpec C) δ) :
    (ans >>= fun p => mg p >>= k p) =
      (ans >>= fun p => mg p >>= fun cols => pure (p, cols)) >>= fun x => k x.1 x.2 := by
  simp only [bind_assoc, pure_bind]

/-- The salts, the digests, the challenge and the last opening in the ghost form, with the two hidden
tables drawn first. -/
theorem ghostSalt (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (p0 : Ad.State) (known knownQ : Shares C E) (attack : ℕ → E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (hrecv : ∀ i, i ∉ D.1 → i ∈ receivers)
    (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (htagR : ∀ i, i ∉ D.1 → (hsR i).tag = tg ∧ (hsR i).label = L)
    (htagD : ∀ i, i ∉ D.1 → (hsD i).tag = tg ∧ (hsD i).label = L)
    (hknownHist : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hsR i).history T = (hsD i).history T)
    (AR BR VR AD BD VD : C.Party → E) (hrel : FinalRel K D AR BR VR AD BD VD)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    SameRun prims
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        saltGhostPhase K D Ad (fuel + 2) p0
          (finalHs K hsR (finalOut K D AR BR known attack knownQ offset receivers w q))
          (fun i _ => finalTail K D known knownQ attack offset receivers AR BR VR w q i) tail)
      (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        saltGhostPhase K D Ad (fuel + 2) p0
          (finalHs K hsD (finalOut K D AD BD known attack knownQ offset receivers w q))
          (fun i _ => finalTail K D known knownQ attack offset receivers AD BD VD w q i) tail) := by
  -- the known digest columns do not depend on the side or on the tables
  let hist0 : C.Party → C.Term → List Bit := fun j =>
    (finalHs K hsR (finalOut K D AR BR known attack knownQ offset receivers 0 0) j).history
  let known0 : SaltReply Ad → C.Term → OracleComp (LocalSpec C) (DigestColumn C) := fun p T =>
    Concrete.sequenceFin (honestDigestColumn D T (randShares D 256 p.2.1 0) hist0)
  have hcol : ∀ (A B : C.Party → E) (hs : C.Party → RunState C)
      (hh : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hs i).history T = (hsR i).history T)
      (w q : MaskTable C E) (p : SaltReply Ad) (T : C.Term), KnownTo D.1 T →
      Concrete.sequenceFin (honestDigestColumn D T (randShares D 256 p.2.1 0)
        (fun j => (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) j).history)) =
        known0 p T := by
    intro A B hs hh w q p T hT
    congr 1
    funext i
    unfold honestDigestColumn
    by_cases hi : i ∉ D.1 ∧ i ∈ C.holders T
    · have he : (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i).history T =
          hist0 i T := by
        simp only [hist0, finalHs, finalState, recordHistory, if_pos hi.2, hh T hT i hi.1 hi.2]
        rw [finalOut_known K D A B AR BR known attack knownQ offset receivers w q 0 0 i T hT]
      simp only [if_pos hi, he]
    · simp only [if_neg hi]
  let OB : OracleComp (LocalSpec C) (SaltReply Ad × List (DigestColumn C)) :=
    (rightAdversary (rightAdversary Ad)).answer p0 () >>= fun p =>
      mixedGhostDigests D (known0 p) C.terms pure >>= fun cols => pure (p, cols)
  have side : ∀ (A B V : C.Party → E) (hs : C.Party → RunState C)
      (hh : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hs i).history T = (hsR i).history T),
      SameRun prims
        (do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          saltGhostPhase K D Ad (fuel + 2) p0
            (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q))
            (fun i _ => finalTail K D known knownQ attack offset receivers A B V w q i) tail)
        (OB >>= fun x => do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) x.1.1
            (fun i => afterDigests i (digestRows x.2 i)
              ((finalTail K D known knownQ attack offset receivers A B V w q i).run'
                (afterSalt (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)))) >>=
            tail) := by
    intro A B V hs hh
    refine SameRun.trans (SameRun.of_eq ?_) (sameRun_samples_swap prims OB (fun w q x =>
      executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) x.1.1
        (fun i => afterDigests i (digestRows x.2 i)
          ((finalTail K D known knownQ attack offset receivers A B V w q i).run'
            (afterSalt (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)))) >>= tail))
    refine bind_congr fun w => bind_congr fun q => ?_
    unfold saltGhostPhase
    have hfun : saltGhostContinuation K D Ad (fuel + 2)
        (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q))
        (fun i _ => finalTail K D known knownQ attack offset receivers A B V w q i) tail =
        fun p => mixedGhostDigests D (known0 p) C.terms pure >>= fun cols =>
          executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) p.1
            (fun i => afterDigests i (digestRows cols i)
              ((finalTail K D known knownQ attack offset receivers A B V w q i).run'
                (afterSalt (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)))) >>=
            tail := by
      funext p
      unfold saltGhostContinuation
      rw [mixedGhostDigests_congr D _ (known0 p) (hcol A B hs hh w q p), mixedGhostDigests_bind_pure]
    rw [hfun]
    exact ghost_reassoc _ _ _
  refine (side AR BR VR hsR (fun _ _ _ _ _ => rfl)).trans
    (SameRun.trans ?_ (side AD BD VD hsD (fun T hT i hi hh => (hknownHist T hT i hi hh).symm)).symm)
  apply SameRun.bind_right
  intro x
  exact ghostDigestRound prims K D Ad fuel x.1.1 (digestRows x.2) known knownQ attack offset receivers hrecv
    tg (L + 1 + 1 + 1)
    (fun w q i => afterSalt (finalHs K hsR (finalOut K D AR BR known attack knownQ offset receivers w q) i))
    (fun w q i => afterSalt (finalHs K hsD (finalOut K D AD BD known attack knownQ offset receivers w q) i))
    (fun w q i hi => by simp [afterSalt, finalHs, finalState, htagR i hi])
    (fun w q i hi => by simp [afterSalt, finalHs, finalState, htagD i hi])
    AR BR VR AD BD VD hrel tail

/-- The leak of the masked multiplication is the same on the two sides. -/
lemma maskedView_rel (K : Constants C E) (D : C.Coalition) (known : Shares C E) (A B A' B' : C.Party → E)
    (dA dB : C.Term → E) (hkA : ∀ T, KnownTo D.1 T → dA T = 0) (hkB : ∀ T, KnownTo D.1 T → dB T = 0)
    (hA : ∀ i, i ∉ D.1 → A i - A' i = conv K (localContext i) (fun T _ => dA T) 0)
    (hB : ∀ i, i ∉ D.1 → B i - B' i = conv K (localContext i) (fun T _ => dB T) 0) :
    maskedView K D known 0 A B = maskedView K D known 0 A' B' := by
  unfold maskedView
  apply extendView_eq_of_relation
  apply shamirPair_viewRelation
  · intro k; exact ShamirDifference.refl K D _
  · intro k; exact ShamirDifference.refl K D _
  · intro k
    exact ShamirDifference.of_conv K D _ _ (fun T _ => dA T) 0 (fun T hT _ => hkA T hT)
      (fun i hi => by rw [← hA i hi]; ring)
  · intro k
    exact ShamirDifference.of_conv K D _ _ (fun T _ => dB T) 0 (fun T hT _ => hkB T hT)
      (fun i hi => by rw [← hB i hi]; ring)

/-- With every honest receiver, the masked multiplication leads into the salts. -/
theorem finalMasked_all (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (A B V : C.Party → E) (hs : C.Party → RunState C)
    (known : Shares C E) (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (w q : MaskTable C E) (hall : ∀ i, i ∉ D.1 → i ∈ receivers) :
    executePhase localRoles D Ad (checkFunctionalities K) fuel st
      (finalMaskedProgram K D A B V hs known attack knownQ offset receivers w q) =
    executePhase localRoles D Ad (checkFunctionalities K) fuel st
      (fun i => ((hybridCheckGadgets K i).randBits 256 >>= fun salts =>
        compareDigests (localContext i) salts.1 >>= fun _ =>
          finalTail K D known knownQ attack offset receivers A B V w q i).run'
        (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)) := by
  apply executePhase_congr_honest
  intro i hi
  unfold finalMaskedProgram
  rw [multFinish_honest D 2 _ _ _ _ _ _ i hi, if_pos (hall i hi)]
  simp only [afterExtend, finalRest, finalTail, finalOut, finalHs, finalState, maskShare]
  rfl

/-- The unknown terms of the masked multiplication agree at the honest holders. -/
lemma finalOut_unknown (K : Constants C E) (D : C.Coalition) (A B : C.Party → E) (known : Shares C E)
    (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (hall : ∀ i, i ∉ D.1 → i ∈ receivers) (w q : MaskTable C E) (T : C.Term) (hT : ¬ KnownTo D.1 T)
    (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    finalOut K D A B known attack knownQ offset receivers w q i T =
      finalOut K D A B known attack knownQ offset receivers w q j T := by
  have hf := unknown_no_corrupt_filler K D T hT .peer
  unfold finalOut multFinish
  have hi' : ¬ (i ∈ D.1 ∨ i ∉ receivers) := by simp [hi, hall i hi]
  have hj' : ¬ (j ∈ D.1 ∨ j ∉ receivers) := by simp [hj, hall j hj]
  simp only [if_neg hi', if_neg hj', Option.getD_some, hiT, hjT, true_and]
  funext g
  simp only [hf, if_false]

/-- The histories of the unknown terms agree at the honest holders after the masked multiplication. -/
lemma finalHs_common (K : Constants C E) (D : C.Coalition) (A B : C.Party → E) (hs : C.Party → RunState C)
    (known : Shares C E) (attack : ℕ → E) (knownQ : Shares C E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (hall : ∀ i, i ∉ D.1 → i ∈ receivers) (w q : MaskTable C E)
    (hcommon : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hs i).history T = (hs j).history T) :
    ∃ hist : C.Term → List Bit, ∀ T, ¬ KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T →
      (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i).history T = hist T := by
  have hh := fun T => exists_honest_holder (C := C) D T
  refine ⟨fun T => (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q)
    (Classical.choose (hh T))).history T, ?_⟩
  intro T hT i hi hiT
  obtain ⟨hjT, hj⟩ := Classical.choose_spec (hh T)
  simp only [finalHs, finalState, recordHistory, if_pos hiT, if_pos hjT]
  rw [hcommon T hT i _ hi hj hiT hjT,
    finalOut_unknown K D A B known attack knownQ offset receivers hall w q T hT i _ hi hj hiT hjT]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma evalDist_run'_of_sameRun (prims : Primitives) {α : Type} {a b : OracleComp (LocalSpec C) α}
    (h : SameRun prims a b) (s : HashCache C) :
    𝒟[(simulateQ (localAnswer prims) a).run' s] = 𝒟[(simulateQ (localAnswer prims) b).run' s] := by
  simp only [StateT.run'_eq, evalDist_map, h s]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma tvDist_sameRun_congr (prims : Primitives) {α : Type} {a a' b b' : OracleComp (LocalSpec C) α}
    (ha : SameRun prims a a') (hb : SameRun prims b b') (s : HashCache C) :
    tvDist ((simulateQ (localAnswer prims) a).run' s) ((simulateQ (localAnswer prims) b).run' s) =
      tvDist ((simulateQ (localAnswer prims) a').run' s) ((simulateQ (localAnswer prims) b').run' s) := by
  unfold tvDist
  rw [evalDist_run'_of_sameRun prims ha, evalDist_run'_of_sameRun prims hb]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma tvDist_of_sameRun (prims : Primitives) {α : Type} {a b : OracleComp (LocalSpec C) α}
    (h : SameRun prims a b) (s : HashCache C) :
    tvDist ((simulateQ (localAnswer prims) a).run' s) ((simulateQ (localAnswer prims) b).run' s) = 0 := by
  unfold tvDist
  rw [evalDist_run'_of_sameRun prims h]
  exact SPMF.tvDist_self _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A common prefix with at most `n` outer-digest calls: the distance is bounded by any bound that holds
from every cache that the prefix can leave, with the salts covered by `n` more values. -/
lemma tvDist_prefix (prims : Primitives) {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (f g : α → OracleComp (LocalSpec C) β) (n : ℕ) (hq : IsQueryBoundP oa DigestQuery n)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (c : ℝ)
    (h : ∀ a (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ seen.card + n →
      tvDist ((simulateQ (localAnswer prims) (f a)).run' cache')
        ((simulateQ (localAnswer prims) (g a)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) (oa >>= f)).run' cache)
      ((simulateQ (localAnswer prims) (oa >>= g)).run' cache) ≤ c := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply tvDist_bind_left_le_const
  intro z hz
  obtain ⟨seen', hc', hcard⟩ := localProgram_digest_covered prims oa DigestQuery (fun _ ht => ht) n hq
    cache seen hc z hz
  simpa only [StateT.run'_eq] using h z.1 z.2 seen' hc' hcard

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Two uniform samples before two computations: they make no outer-digest call. -/
lemma tvDist_samples (prims : Primitives) {α β : Type} [SampleableType α]
    (f g : α → α → OracleComp (LocalSpec C) β)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (c : ℝ)
    (h : ∀ w q (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ seen.card →
      tvDist ((simulateQ (localAnswer prims) (f w q)).run' cache')
        ((simulateQ (localAnswer prims) (g w q)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ α) (LocalSpec C); let q ← liftComp ($ᵗ α) (LocalSpec C); f w q)).run' cache)
      ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ α) (LocalSpec C); let q ← liftComp ($ᵗ α) (LocalSpec C); g w q)).run' cache) ≤ c := by
  have h1 : IsQueryBoundP (liftComp ($ᵗ α) (LocalSpec C)) DigestQuery 0 := prob_lift_no_digest _
  have hq : IsQueryBoundP (do
      let w ← liftComp ($ᵗ α) (LocalSpec C)
      let q ← liftComp ($ᵗ α) (LocalSpec C)
      pure (w, q)) DigestQuery 0 :=
    isQueryBoundP_bind (n := 0) (m := 0) h1 fun w _ =>
      isQueryBoundP_bind (n := 0) (m := 0) h1 fun _ _ => isQueryBoundP_pure _ _ 0
  have hsplit : ∀ k : α → α → OracleComp (LocalSpec C) β,
      (do let w ← liftComp ($ᵗ α) (LocalSpec C); let q ← liftComp ($ᵗ α) (LocalSpec C); k w q) =
      (do let w ← liftComp ($ᵗ α) (LocalSpec C); let q ← liftComp ($ᵗ α) (LocalSpec C); pure (w, q)) >>=
        fun x => k x.1 x.2 := by
    intro k; simp only [bind_assoc, pure_bind]
  rw [hsplit f, hsplit g]
  exact tvDist_prefix prims _ _ _ 0 hq cache seen hc c fun x cache' seen' hc' hcard =>
    h x.1 x.2 cache' seen' hc' (by omega)

/-- The hiding bound of the salted digests of one side, after the masked multiplication. -/
theorem finalSalt_hide (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel step final : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st1 : Ad.State)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (hall : ∀ i, i ∉ D.1 → i ∈ receivers) (hs : C.Party → RunState C)
    (hcommon : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hs i).history T = (hs j).history T)
    (A B V : C.Party → E) {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    tvDist ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) st1
          (finalMaskedProgram K D A B V hs known attack knownQ offset receivers w q) >>= tail)).run' cache)
      ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        saltGhostPhase K D Ad (fuel + 2) st1
          (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q))
          (fun i _ => finalTail K D known knownQ attack offset receivers A B V w q i) tail)).run' cache) ≤
      ((C.terms.length * (seen.card + (fuel + 2 + 1) * step + final + (C.n + 1) * C.terms.length) : ℕ) : ℝ) /
        2 ^ 256 := by
  refine tvDist_samples prims _ _ cache seen hc _ ?_
  intro w q cache' seen' hc' hcard
  rw [finalMasked_all K D Ad _ st1 A B V hs known attack knownQ offset receivers w q hall]
  obtain ⟨hist, hhist⟩ := finalHs_common K D A B hs known attack knownQ offset receivers hall w q hcommon
  refine (saltDigestPhase_hide prims K D Ad (fuel + 2) step st1 hr ha
    (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q))
    (fun i _ => finalTail K D known knownQ attack offset receivers A B V w q i)
    (fun i _ => finalAfterDigests_no_digest K i _ _ _ _ _ _ _) hist hhist cache' seen' hc' tail final hq).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.mul_le_mul_left C.terms.length (by omega)

/-- After the two replies of the randomization, the two sides differ by twice the hiding bound. -/
theorem finalMasked_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel step final : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st1 : Ad.State)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (htagR : ∀ i, i ∉ D.1 → (hsR i).tag = tg ∧ (hsR i).label = L)
    (htagD : ∀ i, i ∉ D.1 → (hsD i).tag = tg ∧ (hsD i).label = L)
    (hknownHist : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hsR i).history T = (hsD i).history T)
    (hcommonR : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsR i).history T = (hsR j).history T)
    (hcommonD : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsD i).history T = (hsD j).history T)
    (AR BR VR AD BD VD : C.Party → E) (hrel : FinalRel K D AR BR VR AD BD VD)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    tvDist ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) st1
          (finalMaskedProgram K D AR BR VR hsR known attack knownQ offset receivers w q) >>= tail)).run' cache)
      ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) st1
          (finalMaskedProgram K D AD BD VD hsD known attack knownQ offset receivers w q) >>= tail)).run' cache) ≤
      2 * (((C.terms.length * (seen.card + (fuel + 2 + 1) * step + final + (C.n + 1) * C.terms.length) : ℕ) : ℝ) /
        2 ^ 256) := by
  have hB : (0 : ℝ) ≤ ((C.terms.length * (seen.card + (fuel + 2 + 1) * step + final +
      (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256 := by positivity
  by_cases hall : ∀ i, i ∉ D.1 → i ∈ receivers
  · have h1 := finalSalt_hide prims K D Ad fuel step final hr ha st1 known knownQ attack offset receivers hall
      hsR hcommonR AR BR VR tail hq cache seen hc
    have h3 := finalSalt_hide prims K D Ad fuel step final hr ha st1 known knownQ attack offset receivers hall
      hsD hcommonD AD BD VD tail hq cache seen hc
    have h2 := tvDist_of_sameRun prims (ghostSalt prims K D Ad fuel st1 known knownQ attack offset receivers hall
      tg L hsR hsD htagR htagD hknownHist AR BR VR AD BD VD hrel tail) cache
    refine (tvDist_triangle _ _ _).trans
      ((add_le_add h1 ((tvDist_triangle _ _ _).trans (add_le_add h2.le (le_of_eq (tvDist_comm _ _))))).trans ?_)
    linarith
  · push Not at hall
    have hmiss : ∀ (A B V : C.Party → E) (hs : C.Party → RunState C),
        (do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) st1
            (finalMaskedProgram K D A B V hs known attack knownQ offset receivers w q) >>= tail) =
        (do
          let _w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let _q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          tail (st1, fun _ => none)) := by
      intro A B V hs
      refine bind_congr fun w => bind_congr fun q => ?_
      rw [finalMasked_missing K D Ad (fuel + 2) st1 A B V hs known attack knownQ offset receivers w q hall, pure_bind]
    rw [hmiss, hmiss, tvDist_self]
    linarith

/-- The two replies of the randomization make at most `2 * step` outer-digest calls. -/
lemma finalReplies_digestBound (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State)
    (view : Ad.State × Shares C E × (C.Party → C.Party → ℕ → E) → C.Party → List (Product C E)) :
    IsQueryBoundP (do
      let p ← (leftAdversary (rightAdversary Ad)).answer st ()
      let p' ← (rightAdversary (leftAdversary Ad)).answer p.1 (view p)
      pure (p, p')) DigestQuery (step + step) := by
  have h1 : IsQueryBoundP ((leftAdversary (rightAdversary Ad)).answer st ()) DigestQuery step := by
    apply counted_digestBound
    dsimp only [leftAdversary, rightAdversary]
    simp only [bind_assoc, pure_bind]
    exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  have h2 : ∀ (s : Ad.State) (l : C.Party → List (Product C E)),
      IsQueryBoundP ((rightAdversary (leftAdversary Ad)).answer s l) DigestQuery step := by
    intro s l
    apply counted_digestBound
    dsimp only [leftAdversary, rightAdversary]
    simp only [bind_assoc, pure_bind]
    exact (isQueryBoundP_bind (m := 0) (ha s _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  exact isQueryBoundP_bind h1 fun p _ =>
    (isQueryBoundP_bind (m := 0) (h2 p.1 (view p)) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

/-- The final segment of the check (GS20, Protocol 15, and the digests of CGH+18): from related states,
the real and the simulated runs differ by twice the hiding bound of the salted digests. -/
theorem finalStep_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel step final : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State)
    (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (htagR : ∀ i, i ∉ D.1 → (hsR i).tag = tg ∧ (hsR i).label = L)
    (htagD : ∀ i, i ∉ D.1 → (hsD i).tag = tg ∧ (hsD i).label = L)
    (hknownHist : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hsR i).history T = (hsD i).history T)
    (hcommonR : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsR i).history T = (hsR j).history T)
    (hcommonD : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsD i).history T = (hsD j).history T)
    (AvR BvR AvD BvD : C.Party → ℕ → E) (VR VD : C.Party → E)
    (hrel : FinalRel K D (fun j => AvR j 0) (fun j => BvR j 0) VR (fun j => AvD j 0) (fun j => BvD j 0) VD)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3 + 2) st
          (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (AvR i, BvR i, VR i)).run' (hsR i)) >>=
          tail)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3 + 2) st
          (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (AvD i, BvD i, VD i)).run' (hsD i)) >>=
          tail)).run' cache) ≤
      2 * (((C.terms.length * (seen.card + (step + step) + (fuel + 2 + 1) * step + final +
        (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256) := by
  have hview : ∀ known : Shares C E, maskedView K D known 0 (fun j => AvD j 0) (fun j => BvD j 0) =
      maskedView K D known 0 (fun j => AvR j 0) (fun j => BvR j 0) := by
    intro known
    obtain ⟨delta, deltaD, a, b, a', b', d, d', hknown, -, -, -, -, -, -, -, -, -, -, -, hlA, hlB, -⟩ := hrel
    exact (maskedView_rel K D known _ _ _ _ (fun T => delta T 0) (fun T => delta T 1)
      (fun T hT => hknown T hT 0) (fun T hT => hknown T hT 1) hlA hlB).symm
  rw [tvDist_sameRun_congr prims
    ((finalStep_masks prims K D Ad (fuel + 3) st AvR BvR VR hsR).bind fun out => SameRun.refl prims (tail out))
    ((finalStep_masks prims K D Ad (fuel + 3) st AvD BvD VD hsD).bind fun out => SameRun.refl prims (tail out))]
  simp only [hview]
  let OB := (do
    let p ← (leftAdversary (rightAdversary Ad)).answer st ()
    let p' ← (rightAdversary (leftAdversary Ad)).answer p.1
      (maskedView K D p.2.1 0 (fun j => AvR j 0) (fun j => BvR j 0))
    pure (p, p'))
  have hform : ∀ (A B V : C.Party → E) (hs : C.Party → RunState C),
      (do
        let p ← (leftAdversary (rightAdversary Ad)).answer st ()
        let p' ← (rightAdversary (leftAdversary Ad)).answer p.1
          (maskedView K D p.2.1 0 (fun j => AvR j 0) (fun j => BvR j 0))
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) p'.1
          (finalMaskedProgram K D A B V hs p.2.1 p'.2.1 p'.2.2.1 p'.2.2.2.1 p'.2.2.2.2 w q)) >>= tail =
      OB >>= fun x => (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) x.2.1
          (finalMaskedProgram K D A B V hs x.1.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 w q) >>= tail) := by
    intro A B V hs
    simp only [OB, bind_assoc, pure_bind]
  rw [hform, hform]
  refine tvDist_prefix prims OB _ _ (step + step)
    (finalReplies_digestBound Ad step ha st fun p => maskedView K D p.2.1 0 (fun j => AvR j 0) (fun j => BvR j 0))
    cache seen hc _ ?_
  intro x cache' seen' hc' hcard
  refine (finalMasked_tv prims K D Ad fuel step final hr ha x.2.1 x.1.2.1 x.2.2.2.1 x.2.2.1 x.2.2.2.2.1
    x.2.2.2.2.2 tg L hsR hsD htagR htagD hknownHist hcommonR hcommonD _ _ VR _ _ VD hrel tail hq
    cache' seen' hc').trans ?_
  gcongr

/-- After a common coin, the honest operators read one common challenge, for any continuation. -/
theorem executePhase_afterChallenge_common' {α : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (Ad : CheckAdversary C E Ia) (fuel : ℕ) (st : Ad.State) (hs : C.Party → RunState C) (tg L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tg ∧ (hs i).label = L) (v : List E) (rec : Finset C.Party)
    (hrec : ∃ i, i ∉ D.1 ∧ i ∈ rec) (g : C.Party → E → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) fuel st
        (fun i => afterChallenge K (hs i) (g i) (if i ∉ D.1 ∧ i ∈ rec then some v else none)))
      (do
        let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel st
          (fun i => match r with
            | some r => if i ∈ rec then (g i r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure
            | none => failure)) := by
  let f : C.Party → Option E → PartyM C E (CheckSpec C E) α := fun i r =>
    if i ∉ D.1 ∧ i ∈ rec then (match r with
      | some r => (g i r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
      | none => failure) else failure
  let oa : C.Party → OracleComp (LocalSpec C) (Option E) := fun i =>
    if i ∉ D.1 ∧ i ∈ rec then liftComp (challengeQuery K tg L v) (LocalSpec C) else pure none
  have hp : (fun i => afterChallenge K (hs i) (g i)
      (if i ∉ D.1 ∧ i ∈ rec then some v else none)) = (fun i => localStep (oa i) >>= f i) := by
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ rec
    · simp only [hi, afterChallenge, oa, f, oracleStep, (htag i hi.1).1, (htag i hi.1).2]
      refine bind_congr fun r => ?_
      rcases r with _ | r <;> rfl
    · simp only [hi, if_false, afterChallenge, oa, f, localStep_pure', pure_bind]
  rw [hp]
  refine (executePhase_local_fallback prims D Ad _ fuel st oa (fun _ => none) f).trans ?_
  have hsel : SameRun prims (Concrete.sequenceFin (fun i => if i ∈ D.1 then pure none else oa i))
      (do let r ← liftComp (challengeQuery K tg L v) (LocalSpec C)
          pure (fun i => if i ∉ D.1 ∧ i ∈ rec then r else none)) := by
    convert sameRun_sequenceFin_selected prims (challengeQuery K tg L v) none
      (fun i => i ∉ D.1 ∧ i ∈ rec) hrec using 2
    · funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr, oa]
    · funext r
      congr 1
      funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr]
  refine (hsel.bind fun vs => SameRun.refl prims _).trans ?_
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro r
  apply SameRun.of_eq
  apply executePhase_congr_honest
  intro i hi
  by_cases hr : i ∈ rec
  · rcases r with _ | r <;> simp [f, hi, hr]
  · rcases r with _ | r <;> simp [f, hi, hr]

/-! ### The loops -/

/-- A multiplication phase with some live honest operators. -/
theorem executePhase_extend_live {α : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C)
    (products : C.Party → List (Product C E)) (f : C.Party → Shares C E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (fun i => if live i then ((hybridCheckGadgets K i).extendMult (products i) >>= f i).run' (hs i)
        else failure) =
    if ∀ i, i ∉ D.1 → live i then (do
      let p ← runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st
        (fun i => if i ∈ D.1 then none else some (products i))
      executePhase localRoles D Ad (checkFunctionalities K) fuel p.1
        (fun i => afterExtend K i (products i).length (hs i) (f i) (p.2 i)))
    else pure (st, fun _ => none) := by
  split_ifs with hall
  · rw [executePhase_congr_honest D Ad _ _ st _
      (fun i => ((hybridCheckGadgets K i).extendMult (products i) >>= f i).run' (hs i))
      (fun i hi => if_pos (hall i hi))]
    exact executePhase_extend K D Ad fuel st products hs f
  · push Not at hall
    let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
        PartyM C E (CheckSpec C E) α := fun i o => match o with
      | some (.inl (.inr z)) =>
          (f i z).run' ⟨recordHistory K i (hs i).history z (products i).length, (hs i).label + 1, (hs i).tag⟩
      | _ => failure
    have hp : (fun i => if live i then ((hybridCheckGadgets K i).extendMult (products i) >>= f i).run' (hs i)
        else failure) =
        (fun i => optionalCall (if live i then some (.inl (.inr (products i))) else none) (next i)) := by
      funext i
      by_cases hi : live i <;> simp only [hi, if_true, if_false, optionalCall, extendMult_run', next]
      apply bind_congr
      intro o
      rcases o with _ | ((a | b) | (c | d)) <;> rfl
    rw [hp]
    apply executePhase_partialCall_abort
    · intro i hi; rfl
    · obtain ⟨i, hi, hl⟩ := hall
      exact ⟨i, hi, if_neg hl⟩

/-- A missing honest operator at the masks of the randomization stops everyone. -/
theorem finalStep_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C)
    (Av Bv : C.Party → ℕ → E) (V : C.Party → E) (hmiss : ∃ i, i ∉ D.1 ∧ ¬ live i) :
    executePhase localRoles D Ad (checkFunctionalities K) (fuel + 1) st
      (fun i => if live i then
        (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i) else failure) =
      pure (st, fun _ => none) := by
  let g : C.Party → PrssOutput C E → RunM C E (CheckSpec C E) Unit := fun i w => do
    let q ← (hybridCheckGadgets K i).extendMult
      (maskedProducts K (fun j => Av j 0) (fun j => Bv j 0) i w.1)
    finalRest K i (Av i 0) (Bv i 0) (V i) w.1 q
  let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) Unit := fun i o => match o with
    | some (.inr (.inl w)) => (g i w).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
    | _ => failure
  have hp : (fun i => if live i then
      (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i) else failure) =
      (fun i => optionalCall (if live i then some (.inr (.inl 2)) else none) (next i)) := by
    funext i
    by_cases hi : live i
    · simp only [hi, if_true, optionalCall]
      rw [finalStep_eq K i (Av i) (Bv i) (V i) (fun j => Av j 0) (fun j => Bv j 0) rfl rfl, randElements_run']
      apply bind_congr
      intro o
      rcases o with _ | ((a | b) | (c | d)) <;> rfl
    · simp only [hi, if_false, optionalCall]
  rw [hp]
  apply executePhase_partialCall_abort
  · intro i hi; rfl
  · obtain ⟨i, hi, hl⟩ := hmiss
    exact ⟨i, hi, if_neg hl⟩

/-- The relation of the two halving states of length `len`: Shamir vectors with equal corrupt shares and
hidden-term differences, and claims whose difference is the difference of the inner products. -/
def HalvRel (K : Constants C E) (D : C.Coalition) (len : ℕ) (AR BR AD BD : C.Party → ℕ → E)
    (DR DD : C.Party → E) : Prop :=
  ∃ (a b a' b' : ℕ → E) (dA dB : ℕ → C.Term → E) (dD : C.Term → E),
    (∀ k, IsShamir K (fun i => AR i k) (a k)) ∧ (∀ k, IsShamir K (fun i => BR i k) (b k)) ∧
    (∀ k, IsShamir K (fun i => AD i k) (a' k)) ∧ (∀ k, IsShamir K (fun i => BD i k) (b' k)) ∧
    (∀ k, ∀ i ∈ D.1, AR i k = AD i k) ∧ (∀ k, ∀ i ∈ D.1, BR i k = BD i k) ∧
    (∀ k T, KnownTo D.1 T → dA k T = 0) ∧ (∀ k T, KnownTo D.1 T → dB k T = 0) ∧
    (∀ T, KnownTo D.1 T → dD T = 0) ∧
    (∀ k, ∑ T, dA k T = a k - a' k) ∧ (∀ k, ∑ T, dB k T = b k - b' k) ∧
    (∀ k i, i ∉ D.1 → AR i k - AD i k = conv K (localContext i) (fun T _ => dA k T) 0) ∧
    (∀ k i, i ∉ D.1 → BR i k - BD i k = conv K (localContext i) (fun T _ => dB k T) 0) ∧
    (∀ i, i ∉ D.1 → DR i - DD i = conv K (localContext i) (fun T _ => dD T) 0) ∧
    ∑ T, dD T = ∑ k ∈ range len, (a k * b k - a' k * b' k)

/-- At length one the halving relation is the relation of the final segment. -/
lemma halvRel_final (K : Constants C E) (D : C.Coalition) (AR BR AD BD : C.Party → ℕ → E) (DR DD : C.Party → E)
    (h : HalvRel K D 1 AR BR AD BD DR DD) :
    FinalRel K D (fun j => AR j 0) (fun j => BR j 0) DR (fun j => AD j 0) (fun j => BD j 0) DD := by
  obtain ⟨a, b, a', b', dA, dB, dD, hA, hB, hA', hB', hCA, hCB, hkA, hkB, hkD, hsA, hsB, hlA, hlB, hlD, hsum⟩ := h
  refine ⟨fun T g => if g = 0 then dA 0 T else dB 0 T, dD, a 0, b 0, a' 0, b' 0, ∑ T, dD T, 0,
    ?_, hkD, hA 0, hB 0, hA' 0, hB' 0, fun i hi => hCA 0 i hi, fun i hi => hCB 0 i hi, ?_, ?_, by simp, ?_,
    fun i hi => hlA 0 i hi, fun i hi => hlB 0 i hi, hlD⟩
  · intro T hT g
    dsimp only
    split_ifs
    · exact hkA 0 T hT
    · exact hkB 0 T hT
  · simpa using hsA 0
  · simpa using hsB 0
  · rw [hsum, Finset.sum_range_one]
    ring

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The honest additive shares of two inner products with equal corrupt shares differ by the difference
of the inner products. -/
lemma honest_mulSh_diff [CharP E 2] (K : Constants C E) (D : C.Coalition) (AR BR AD BD : C.Party → ℕ → E)
    (a b a' b' : ℕ → E) (hA : ∀ k, IsShamir K (fun i => AR i k) (a k)) (hB : ∀ k, IsShamir K (fun i => BR i k) (b k))
    (hA' : ∀ k, IsShamir K (fun i => AD i k) (a' k)) (hB' : ∀ k, IsShamir K (fun i => BD i k) (b' k))
    (hCA : ∀ k, ∀ i ∈ D.1, AR i k = AD i k) (hCB : ∀ k, ∀ i ∈ D.1, BR i k = BD i k) (n : ℕ) :
    ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range n, AR i k * BR i k -
      ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range n, AD i k * BD i k =
      ∑ k ∈ range n, (a k * b k - a' k * b' k) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  have h : ∀ i, (if i ∉ D.1 then lagrangeAll K i * ∑ k ∈ range n, AR i k * BR i k -
      lagrangeAll K i * ∑ k ∈ range n, AD i k * BD i k else 0) =
      lagrangeAll K i * ∑ k ∈ range n, AR i k * BR i k - lagrangeAll K i * ∑ k ∈ range n, AD i k * BD i k := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, not_true_eq_false, if_false]
      rw [Finset.sum_congr rfl fun k _ => by rw [hCA k i hi, hCB k i hi], sub_self]
    · simp only [hi, not_false_eq_true, if_true]
  simp only [h]
  rw [Finset.sum_sub_distrib, sum_lagrangeAll_shamir_sum K hA hB n, sum_lagrangeAll_shamir_sum K hA' hB' n,
    Finset.sum_sub_distrib]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma conv_lin (K : Constants C E) (i : C.Party) (u v : E) (f g : C.Term → E) :
    conv K (localContext i) (fun T _ => u * f T + v * g T) 0 =
      u * conv K (localContext i) (fun T _ => f T) 0 + v * conv K (localContext i) (fun T _ => g T) 0 := by
  simp only [conv, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => by ring

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma conv_sub_eq (K : Constants C E) (i : C.Party) (zR zD : Shares C E) (g : ℕ) (f : C.Term → E)
    (h : ∀ T, i ∈ C.holders T → zR T g - zD T g = f T) :
    conv K (localContext i) zR g - conv K (localContext i) zD g =
      ∑ T ∈ univ.filter (i ∈ C.holders ·), psi K T i * f T := by
  simp only [conv, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [← mul_sub, h T (Finset.mem_filter.mp hT).2]
  rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma conv_const_eq (K : Constants C E) (i : C.Party) (f : C.Term → E) :
    conv K (localContext i) (fun T _ => f T) 0 = ∑ T ∈ univ.filter (i ∈ C.holders ·), psi K T i * f T := rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- One halving step keeps the halving relation, for any challenge, when the hidden output difference
of the two inner products goes to the lacked term. -/
lemma halvRel_step [CharP E 2] (K : Constants C E) (D : C.Coalition) (len : ℕ) (AR BR AD BD : C.Party → ℕ → E)
    (DR DD : C.Party → E) (h : HalvRel K D len AR BR AD BD DR DD) (r : E) (zR zD : C.Party → Shares C E)
    (δ0 δ1 : E)
    (hz : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < 2,
      zR i T g - zD i T g = if lackedTerm D.1 = some T then (if g = 0 then δ0 else δ1) else 0)
    (h0 : δ0 = ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range (halvedLength len), AR i k * BR i k -
      ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range (halvedLength len), AD i k * BD i k)
    (h1 : δ1 = ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range (halvedLength len),
        (AR i k + (if k + halvedLength len < len then AR i (k + halvedLength len) else 0)) *
        (BR i k + (if k + halvedLength len < len then BR i (k + halvedLength len) else 0)) -
      ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range (halvedLength len),
        (AD i k + (if k + halvedLength len < len then AD i (k + halvedLength len) else 0)) *
        (BD i k + (if k + halvedLength len < len then BD i (k + halvedLength len) else 0))) :
    HalvRel K D (halvedLength len)
      (fun i k => AR i k + r * (AR i k + (if k + halvedLength len < len then AR i (k + halvedLength len) else 0)))
      (fun i k => BR i k + r * (BR i k + (if k + halvedLength len < len then BR i (k + halvedLength len) else 0)))
      (fun i k => AD i k + r * (AD i k + (if k + halvedLength len < len then AD i (k + halvedLength len) else 0)))
      (fun i k => BD i k + r * (BD i k + (if k + halvedLength len < len then BD i (k + halvedLength len) else 0)))
      (fun i => conv K (localContext i) (zR i) 0 + (DR i + conv K (localContext i) (zR i) 1) * r +
        conv K (localContext i) (zR i) 1 * r ^ 2)
      (fun i => conv K (localContext i) (zD i) 0 + (DD i + conv K (localContext i) (zD i) 1) * r +
        conv K (localContext i) (zD i) 1 * r ^ 2) := by
  obtain ⟨a, b, a', b', dA, dB, dD, hA, hB, hA', hB', hCA, hCB, hkA, hkB, hkD, hsA, hsB, hlA, hlB, hlD, hsum⟩ := h
  set half := halvedLength len with hhalf
  let hiF : (ℕ → E) → ℕ → E := fun v k => if k + half < len then v (k + half) else 0
  let fold : (ℕ → E) → ℕ → E := fun v k => v k + r * (v k + hiF v k)
  have hfold : ∀ (f : C.Party → ℕ → E) (x : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (x k)) →
      ∀ k, IsShamir K (fun i => f i k + r * (f i k + (if k + half < len then f i (k + half) else 0))) (fold x k) :=
    fun f x hf k => (hf k).add (((hf k).add ((hf (k + half)).ite K _)).mul_left r)
  have hsumv : ∀ (f : C.Party → ℕ → E) (x : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (x k)) →
      ∀ k, IsShamir K (fun i => f i k + (if k + half < len then f i (k + half) else 0)) (x k + hiF x k) :=
    fun f x hf k => (hf k).add ((hf (k + half)).ite K _)
  let lack : C.Term → E → E := fun T x => if lackedTerm D.1 = some T then x else 0
  have hlack : ∀ x : E, ∑ T, lack T x = x := by
    intro x
    obtain ⟨T₀, hT₀, -⟩ := lackedTerm_spec D
    simp only [lack, hT₀, Option.some.injEq]
    rw [Finset.sum_ite_eq univ T₀ (fun _ => x)]
    simp
  refine ⟨fold a, fold b, fold a', fold b',
    fun k T => dA k T + r * (dA k T + (if k + half < len then dA (k + half) T else 0)),
    fun k T => dB k T + r * (dB k T + (if k + half < len then dB (k + half) T else 0)),
    fun T => lack T δ0 + (dD T + lack T δ1) * r + lack T δ1 * r ^ 2,
    hfold AR a hA, hfold BR b hB, hfold AD a' hA', hfold BD b' hB', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k i hi; simp only [hCA k i hi, hCA (k + half) i hi]
  · intro k i hi; simp only [hCB k i hi, hCB (k + half) i hi]
  · intro k T hT; simp only [hkA k T hT, hkA (k + half) T hT]; split_ifs <;> ring
  · intro k T hT; simp only [hkB k T hT, hkB (k + half) T hT]; split_ifs <;> ring
  · intro T hT
    have hn : lackedTerm D.1 ≠ some T := fun h => lackedTerm_unknown D T h hT
    simp only [lack, hn, if_false, hkD T hT]; ring
  · intro k
    simp only [fold, hiF, Finset.sum_add_distrib, ← Finset.mul_sum, hsA]
    split_ifs <;> simp [hsA] <;> ring
  · intro k
    simp only [fold, hiF, Finset.sum_add_distrib, ← Finset.mul_sum, hsB]
    split_ifs <;> simp [hsB] <;> ring
  · intro k i hi
    rw [conv_const_eq]
    have h1 := hlA k i hi
    have h2 := hlA (k + half) i hi
    rw [conv_const_eq] at h1 h2
    dsimp only
    split_ifs with hc
    · rw [show AR i k + r * (AR i k + AR i (k + half)) - (AD i k + r * (AD i k + AD i (k + half))) =
        (AR i k - AD i k) + r * ((AR i k - AD i k) + (AR i (k + half) - AD i (k + half))) by ring, h1, h2,
        ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T _ => by ring
    · rw [show AR i k + r * (AR i k + 0) - (AD i k + r * (AD i k + 0)) = (1 + r) * (AR i k - AD i k) by ring, h1,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => by ring
  · intro k i hi
    rw [conv_const_eq]
    have h1 := hlB k i hi
    have h2 := hlB (k + half) i hi
    rw [conv_const_eq] at h1 h2
    dsimp only
    split_ifs with hc
    · rw [show BR i k + r * (BR i k + BR i (k + half)) - (BD i k + r * (BD i k + BD i (k + half))) =
        (BR i k - BD i k) + r * ((BR i k - BD i k) + (BR i (k + half) - BD i (k + half))) by ring, h1, h2,
        ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T _ => by ring
    · rw [show BR i k + r * (BR i k + 0) - (BD i k + r * (BD i k + 0)) = (1 + r) * (BR i k - BD i k) by ring, h1,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => by ring
  · intro i hi
    have e0 := conv_sub_eq K i (zR i) (zD i) 0 (fun T => lack T δ0)
      (fun T hT => by simpa [lack] using hz i hi T hT 0 (by norm_num))
    have e1 := conv_sub_eq K i (zR i) (zD i) 1 (fun T => lack T δ1)
      (fun T hT => by simpa [lack] using hz i hi T hT 1 (by norm_num))
    have eD := hlD i hi
    rw [conv_const_eq] at eD ⊢
    rw [show conv K (localContext i) (zR i) 0 + (DR i + conv K (localContext i) (zR i) 1) * r +
        conv K (localContext i) (zR i) 1 * r ^ 2 -
        (conv K (localContext i) (zD i) 0 + (DD i + conv K (localContext i) (zD i) 1) * r +
          conv K (localContext i) (zD i) 1 * r ^ 2) =
        (conv K (localContext i) (zR i) 0 - conv K (localContext i) (zD i) 0) + (DR i - DD i) * r +
          (conv K (localContext i) (zR i) 1 - conv K (localContext i) (zD i) 1) * (r + r ^ 2) by ring,
      e0, e1, eD, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun T _ => by ring
  · -- the claim difference is the difference of the folded inner products
    have hd0 : δ0 = ∑ k ∈ range half, (a k * b k - a' k * b' k) := by
      rw [h0]; exact honest_mulSh_diff K D AR BR AD BD a b a' b' hA hB hA' hB' hCA hCB half
    have hd1 : δ1 = ∑ k ∈ range half, ((a k + hiF a k) * (b k + hiF b k) -
        (a' k + hiF a' k) * (b' k + hiF b' k)) := by
      rw [h1]
      exact honest_mulSh_diff K D _ _ _ _ _ _ _ _ (hsumv AR a hA) (hsumv BR b hB) (hsumv AD a' hA')
        (hsumv BD b' hB') (fun k i hi => by simp only [hCA k i hi, hCA (k + half) i hi])
        (fun k i hi => by simp only [hCB k i hi, hCB (k + half) i hi]) half
    have hpad := sum_range_padded a b len
    have hpad' := sum_range_padded a' b' len
    have hfa := sum_range_halving_fold a b (hiF a) (hiF b) half r
    have hfa' := sum_range_halving_fold a' b' (hiF a') (hiF b') half r
    have hpad2 : ∑ k ∈ range len, a k * b k =
        ∑ k ∈ range half, a k * b k + ∑ k ∈ range half, hiF a k * hiF b k := hpad
    have hpad2' : ∑ k ∈ range len, a' k * b' k =
        ∑ k ∈ range half, a' k * b' k + ∑ k ∈ range half, hiF a' k * hiF b' k := hpad'
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hlack]
    rw [hsum, hd0, hd1]
    simp only [Finset.sum_sub_distrib]
    have hfa2 : ∑ k ∈ range half, fold a k * fold b k = _ := hfa
    have hfa2' : ∑ k ∈ range half, fold a' k * fold b' k = _ := hfa'
    rw [hfa2, hfa2', hpad2, hpad2']
    ring

lemma challengeQuery_no_digest (K : Constants C E) (tg L : ℕ) (v : List E) :
    IsQueryBoundP (liftComp (challengeQuery K tg L v) (LocalSpec C)) DigestQuery 0 := by
  simp only [challengeQuery, liftComp_bind]
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (hashQuery_no_digest _ (by simp [DigestQuery, digestSaltProjection])) fun key _ =>
      findChallenge_no_digest K key challengeTries 0

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma bind_sample_digestBound {σ' α β : Type} [SampleableType α] (oa : OracleComp (LocalSpec C) σ')
    (k : σ' → α → β) (n : ℕ) (h : IsQueryBoundP oa DigestQuery n) :
    IsQueryBoundP (oa >>= fun p => liftComp ($ᵗ α) (LocalSpec C) >>= fun f => pure (k p f)) DigestQuery n :=
  (isQueryBoundP_bind (m := 0) h fun p _ =>
    isQueryBoundP_bind (n := 0) (m := 0) (prob_lift_no_digest _) fun _ _ => isQueryBoundP_pure _ _ 0).mono
    (by omega)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma sample_bind_digestBound {σ' α : Type} [SampleableType α] (ans : α → OracleComp (LocalSpec C) σ')
    (n : ℕ) (h : ∀ a, IsQueryBoundP (ans a) DigestQuery n) :
    IsQueryBoundP (liftComp ($ᵗ α) (LocalSpec C) >>= fun v => ans v >>= fun pa => pure (v, pa)) DigestQuery n :=
  (isQueryBoundP_bind (n := 0) (m := n) (prob_lift_no_digest _) fun v _ =>
    (isQueryBoundP_bind (n := n) (m := 0) (h v) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)).mono (by omega)

lemma coinDraw_digestBound (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State) :
    IsQueryBoundP (coinDraw D Ad st) DigestQuery step := by
  unfold coinDraw
  refine sample_bind_digestBound _ step fun v => ?_
  apply counted_digestBound
  dsimp only [leftAdversary]
  simp only [bind_assoc, pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

lemma extend_digestBound (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State)
    (inputs : C.Party → Option (List (Product C E))) (h : ∀ i, i ∉ D.1 → (inputs i).isSome) :
    IsQueryBoundP (runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st inputs)
      DigestQuery step := by
  rw [runFunctionality_extend_local K D (rightAdversary (leftAdversary Ad)) st inputs h]
  refine bind_sample_digestBound _ _ step ?_
  apply counted_digestBound
  dsimp only [leftAdversary, rightAdversary]
  simp only [bind_assoc, pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

/-- The running states of the two sides: common tags and labels, equal histories of the known terms,
and common histories of the unknown terms at their honest holders. -/
def HistRel (D : C.Coalition) (tg L : ℕ) (hsR hsD : C.Party → RunState C) : Prop :=
  (∀ i, i ∉ D.1 → (hsR i).tag = tg ∧ (hsR i).label = L) ∧
  (∀ i, i ∉ D.1 → (hsD i).tag = tg ∧ (hsD i).label = L) ∧
  (∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hsR i).history T = (hsD i).history T) ∧
  (∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
    (hsR i).history T = (hsR j).history T) ∧
  (∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
    (hsD i).history T = (hsD j).history T)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Twice the hiding bound of the salted digests, from `s` covered salts and `f` remaining steps. -/
def coupleBound (C : Committee) (step final s f : ℕ) : ℝ :=
  2 * (((C.terms.length * (s + f * step + final + (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma coupleBound_nonneg (step final s f : ℕ) : 0 ≤ coupleBound C step final s f := by
  unfold coupleBound; positivity

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma coupleBound_mono {step final s s' f f' : ℕ} (h : s + f * step ≤ s' + f' * step) :
    coupleBound C step final s f ≤ coupleBound C step final s' f' := by
  unfold coupleBound
  gcongr

/-- The final segment with any live honest operators. -/
theorem finalStep_live_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel step final : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live]
    (tg L : ℕ) (hsR hsD : C.Party → RunState C) (hh : HistRel D tg L hsR hsD)
    (AvR BvR AvD BvD : C.Party → ℕ → E) (VR VD : C.Party → E)
    (hrel : FinalRel K D (fun j => AvR j 0) (fun j => BvR j 0) VR (fun j => AvD j 0) (fun j => BvD j 0) VD)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 5) st
          (fun i => if live i then
            (finalStep K (localContext i) (hybridCheckGadgets K i) (AvR i, BvR i, VR i)).run' (hsR i)
            else failure) >>= tail)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 5) st
          (fun i => if live i then
            (finalStep K (localContext i) (hybridCheckGadgets K i) (AvD i, BvD i, VD i)).run' (hsD i)
            else failure) >>= tail)).run' cache) ≤
      coupleBound C step final seen.card (fuel + 5) := by
  obtain ⟨htagR, htagD, hknownHist, hcommonR, hcommonD⟩ := hh
  by_cases hall : ∀ i, i ∉ D.1 → live i
  · rw [executePhase_congr_honest D Ad _ _ st _ _ (fun i hi => if_pos (hall i hi)),
      executePhase_congr_honest D Ad _ _ st (fun i => if live i then _ else failure) _ (fun i hi => if_pos (hall i hi))]
    refine (finalStep_tv prims K D Ad fuel step final hr ha st tg L hsR hsD htagR htagD hknownHist hcommonR hcommonD
      AvR BvR AvD BvD VR VD hrel tail hq cache seen hc).trans (le_of_eq ?_)
    unfold coupleBound
    congr 4
    ring
  · push Not at hall
    rw [finalStep_missing K D Ad (fuel + 4) st live hsR AvR BvR VR hall,
      finalStep_missing K D Ad (fuel + 4) st live hsD AvD BvD VD hall, tvDist_self]
    exact coupleBound_nonneg _ _ _ _

/-- The rest of the check from halving step `j`, with `n` steps left. -/
def halvProg (K : Constants C E) (width n j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) :
    RunM C E (CheckSpec C E) Unit :=
  (List.range' j n).foldlM (halvingStep K (localContext i) (hybridCheckGadgets K i) width) (A, B, V) >>=
    finalStep K (localContext i) (hybridCheckGadgets K i)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma halvProg_zero (K : Constants C E) (width j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) :
    halvProg K width 0 j A B V i = finalStep K (localContext i) (hybridCheckGadgets K i) (A, B, V) := by
  simp [halvProg]

/-- The halving vectors after a step with challenge `r`. -/
def halvFold (len : ℕ) (r : E) (v : ℕ → E) : ℕ → E := fun k =>
  v k + r * (v k + (if k + halvedLength len < len then v (k + halvedLength len) else 0))

/-- The two inner products of a halving step. -/
def halvProducts (len : ℕ) (A B : ℕ → E) : List (Product C E) :=
  [.shamir A B (halvedLength len),
   .shamir (fun k => A k + (if k + halvedLength len < len then A (k + halvedLength len) else 0))
    (fun k => B k + (if k + halvedLength len < len then B (k + halvedLength len) else 0)) (halvedLength len)]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma halvProg_succ (K : Constants C E) (width n j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) :
    halvProg K width (n + 1) j A B V i = (do
      let p ← (hybridCheckGadgets K i).extendMult (halvProducts (halvedLength^[j] width) A B)
      let r ← challenge K (hybridCheckGadgets K i)
      halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r A) (halvFold (halvedLength^[j] width) r B)
        (conv K (localContext i) p 0 + (V + conv K (localContext i) p 1) * r + conv K (localContext i) p 1 * r ^ 2)
        i) := by
  simp only [halvProg, List.range'_succ, List.foldlM_cons, halvingStep, bind_assoc, pure_bind]
  rfl

/-- The inputs of the multiplication of a halving step. -/
def halvInputs (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) : C.Party → Option (List (Product C E)) :=
  fun i => if i ∈ D.1 then none else some (halvProducts len (A i) (B i))

lemma halvInputs_width (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) :
    (firstInput (halvInputs D len A B)).length = 2 := by
  obtain ⟨j, _, hj⟩ := firstInput_honest D (fun i => halvProducts (C := C) len (A i) (B i))
  change (firstInput (fun i => if i ∈ D.1 then none else some (halvProducts len (A i) (B i)))).length = 2
  rw [hj]
  rfl

lemma halvInputs_some (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) :
    ∀ i, i ∉ D.1 → (halvInputs D len A B i).isSome := by
  intro i hi; simp [halvInputs, hi]

/-- The leak of the multiplication of a halving step is the same on the two sides. -/
lemma halvInputs_view (K : Constants C E) (D : C.Coalition) (len : ℕ) (AR BR AD BD : C.Party → ℕ → E)
    (DR DD : C.Party → E) (h : HalvRel K D len AR BR AD BD DR DD) :
    extendView K D.1 (halvInputs D len AR BR) = extendView K D.1 (halvInputs D len AD BD) := by
  obtain ⟨a, b, a', b', dA, dB, dD, -, -, -, -, -, -, hkA, hkB, -, -, -, hlA, hlB, -, -⟩ := h
  apply extendView_eq_of_relation
  have hs : ∀ (X : C.Party → ℕ → E), halvInputs D len X =
      fun Y => shamirPairInputs D X Y
        (fun i k => X i k + (if k + halvedLength len < len then X i (k + halvedLength len) else 0))
        (fun i k => Y i k + (if k + halvedLength len < len then Y i (k + halvedLength len) else 0))
        (halvedLength len) (halvedLength len) := by
    intro X; funext Y i; rfl
  rw [hs AR, hs AD]
  have hsum : ∀ (XR XD : C.Party → ℕ → E) (dX : ℕ → C.Term → E), (∀ k T, KnownTo D.1 T → dX k T = 0) →
      (∀ k i, i ∉ D.1 → XR i k - XD i k = conv K (localContext i) (fun T _ => dX k T) 0) → ∀ k,
      ShamirDifference K D
        (fun i => XR i k + (if k + halvedLength len < len then XR i (k + halvedLength len) else 0))
        (fun i => XD i k + (if k + halvedLength len < len then XD i (k + halvedLength len) else 0)) := by
    intro XR XD dX hk hl k
    refine ShamirDifference.of_conv K D _ _
      (fun T _ => dX k T + (if k + halvedLength len < len then dX (k + halvedLength len) T else 0)) 0
      (fun T hT _ => by simp [hk k T hT, hk (k + halvedLength len) T hT]) fun i hi => ?_
    have h1 := hl k i hi
    have h2 := hl (k + halvedLength len) i hi
    rw [conv_const_eq] at h1 h2
    change _ = ∑ T ∈ univ.filter (i ∈ C.holders ·), psi K T i *
      (dX k T + (if k + halvedLength len < len then dX (k + halvedLength len) T else 0))
    split_ifs
    · rw [show XR i k + XR i (k + halvedLength len) - (XD i k + XD i (k + halvedLength len)) =
        (XR i k - XD i k) + (XR i (k + halvedLength len) - XD i (k + halvedLength len)) by ring, h1, h2,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => by ring
    · rw [show XR i k + 0 - (XD i k + 0) = XR i k - XD i k by ring, h1]
      exact Finset.sum_congr rfl fun T _ => by ring
  exact shamirPair_viewRelation K D _ _ _ _ _ _ _ _ _ _
    (fun k => ShamirDifference.of_conv K D _ _ (fun T _ => dA k T) 0 (fun T hT _ => hkA k T hT) (hlA k))
    (fun k => ShamirDifference.of_conv K D _ _ (fun T _ => dB k T) 0 (fun T hT _ => hkB k T hT) (hlB k))
    (hsum AR AD dA hkA hlA) (hsum BR BD dB hkB hlB)

/-- The coupling of the rest of the check from halving step `j` with `n` steps left and `F` steps of fuel. -/
def HalvRest (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width n j F : ℕ) {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    Prop :=
  ∀ (st : Ad.State) (live : Finset C.Party) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (AR BR AD BD : C.Party → ℕ → E) (DR DD : C.Party → E) (cache : HashCache C) (seen : Finset (List Bit)),
    HalvRel K D (halvedLength^[j] width) AR BR AD BD DR DD → HistRel D tg L hsR hsD →
    DigestSaltsCovered cache seen →
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (halvProg K width n j (AR i) (BR i) (DR i) i).run' (hsR i) else failure) >>=
          tail)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (halvProg K width n j (AD i) (BD i) (DD i) i).run' (hsD i) else failure) >>=
          tail)).run' cache) ≤
      coupleBound C step final seen.card F

/-- The last halving state leads into the final segment. -/
theorem halvRest_zero (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width fuel : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final) :
    HalvRest prims K D Ad step final width 0 (halvingSteps width) (fuel + 5) tail := by
  intro st live tg L hsR hsD AR BR AD BD DR DD cache seen hrel hh hc
  rw [iterate_halvingSteps width hw] at hrel
  simp only [halvProg_zero]
  exact finalStep_live_tv prims K D Ad fuel step final hr ha st (· ∈ live) tg L hsR hsD hh AR BR AD BD DR DD
    (halvRel_final K D AR BR AD BD DR DD hrel) tail hq cache seen hc

/-- The rest of a halving step after its multiplication. -/
def halvNext (K : Constants C E) (width n j : ℕ) (A B : ℕ → E) (V : E) (i : C.Party) (p : Shares C E) :
    RunM C E (CheckSpec C E) Unit := do
  let r ← challenge K (hybridCheckGadgets K i)
  halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r A) (halvFold (halvedLength^[j] width) r B)
    (conv K (localContext i) p 0 + (V + conv K (localContext i) p 1) * r + conv K (localContext i) p 1 * r ^ 2) i

/-- The multiplication of a halving step, with every honest operator live. -/
theorem halvExtend_local (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hall : ∀ i, i ∉ D.1 → live i) (hs : C.Party → RunState C)
    (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
    (do
      let pa ← (rightAdversary (leftAdversary Ad)).answer st
        (extendView K D.1 (halvInputs D (halvedLength^[j] width) A B))
      let fresh ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
      executePhase localRoles D Ad (checkFunctionalities K) F pa.1
        (fun i => afterExtend K i 2 (hs i) (halvNext K width n j (A i) (B i) (V i) i)
          (multFinish D 2 (filler K .peer)
            (fun g => extendTotal K D (halvInputs D (halvedLength^[j] width) A B) g + pa.2.1 g)
            pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i))) := by
  have hp : (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
      (fun i => if live i then ((hybridCheckGadgets K i).extendMult (halvProducts (halvedLength^[j] width) (A i) (B i))
        >>= halvNext K width n j (A i) (B i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [halvProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs
    (fun i => halvProducts (halvedLength^[j] width) (A i) (B i)) (fun i => halvNext K width n j (A i) (B i) (V i) i),
    if_pos hall]
  change (runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st
    (halvInputs D (halvedLength^[j] width) A B) >>= _) = _
  rw [runFunctionality_extend_local K D (rightAdversary (leftAdversary Ad)) st _ (halvInputs_some D _ A B)]
  have hw := halvInputs_width D (halvedLength^[j] width) A B
  generalize (firstInput (halvInputs D (halvedLength^[j] width) A B)).length = w at hw ⊢
  subst hw
  simp only [bind_assoc, pure_bind]
  rfl

/-- A missing honest operator at the multiplication of a halving step stops everyone. -/
theorem halvExtend_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hmiss : ¬ ∀ i, i ∉ D.1 → live i) (hs : C.Party → RunState C)
    (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
      pure (st, fun _ => none) := by
  have hp : (fun i => if live i then (halvProg K width (n + 1) j (A i) (B i) (V i) i).run' (hs i) else failure) =
      (fun i => if live i then ((hybridCheckGadgets K i).extendMult (halvProducts (halvedLength^[j] width) (A i) (B i))
        >>= halvNext K width n j (A i) (B i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [halvProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs _ _, if_neg hmiss]

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma multFinish_some (D : C.Coalition) (w : ℕ) (filled : C.Term → ℕ → Option C.Party) (res : ℕ → E)
    (known : Shares C E) (offset : C.Party → Shares C E) (rec : Finset C.Party) (fresh : C.Term → Fin w → E)
    (i : C.Party) (hi : i ∉ D.1) (hr : i ∈ rec) (T : C.Term) (g : ℕ) :
    (multFinish D w filled res known offset rec fresh i).getD 0 T g =
      if i ∈ C.holders T ∧ g < w then
        (if lackedTerm D.1 = some T then res g - ∑ T' ∈ univ.erase T,
          (if KnownTo D.1 T' then known T' g else if h : g < w then fresh T' ⟨g, h⟩ else 0)
         else (if KnownTo D.1 T then known T g else if h : g < w then fresh T ⟨g, h⟩ else 0)) +
        (if ∃ j ∈ D.1, filled T g = some j then offset i T g else 0) else 0 := by
  have hn : ¬ (i ∈ D.1 ∨ i ∉ rec) := by simp [hi, hr]
  simp only [multFinish, if_neg hn, Option.getD_some]

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma multFinish_diff (D : C.Coalition) (w : ℕ) (filled : C.Term → ℕ → Option C.Party) (resR resD : ℕ → E)
    (known : Shares C E) (offset : C.Party → Shares C E) (rec : Finset C.Party) (fresh : C.Term → Fin w → E)
    (i : C.Party) (hi : i ∉ D.1) (hr : i ∈ rec) (T : C.Term) (hT : i ∈ C.holders T) (g : ℕ) (hg : g < w) :
    (multFinish D w filled resR known offset rec fresh i).getD 0 T g -
      (multFinish D w filled resD known offset rec fresh i).getD 0 T g =
      if lackedTerm D.1 = some T then resR g - resD g else 0 := by
  rw [multFinish_some D w filled resR known offset rec fresh i hi hr, multFinish_some D w filled resD known offset rec
    fresh i hi hr]
  simp only [hT, hg, and_self, if_true]
  split_ifs <;> ring

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma multFinish_known (D : C.Coalition) (w : ℕ) (filled : C.Term → ℕ → Option C.Party) (resR resD : ℕ → E)
    (known : Shares C E) (offset : C.Party → Shares C E) (rec : Finset C.Party) (fresh : C.Term → Fin w → E)
    (i : C.Party) (hi : i ∉ D.1) (hr : i ∈ rec) (T : C.Term) (hT : KnownTo D.1 T) :
    (multFinish D w filled resR known offset rec fresh i).getD 0 T =
      (multFinish D w filled resD known offset rec fresh i).getD 0 T := by
  have hn : lackedTerm D.1 ≠ some T := fun h => lackedTerm_unknown D T h hT
  funext g
  rw [multFinish_some D w filled resR known offset rec fresh i hi hr, multFinish_some D w filled resD known offset rec
    fresh i hi hr]
  simp only [hn, if_false]

omit [SampleableType E] in
lemma multFinish_unknown (K : Constants C E) (D : C.Coalition) (w : ℕ) (res : ℕ → E)
    (known : Shares C E) (offset : C.Party → Shares C E) (rec : Finset C.Party) (fresh : C.Term → Fin w → E)
    (T : C.Term) (hT : ¬ KnownTo D.1 T) (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1) (hir : i ∈ rec)
    (hjr : j ∈ rec) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    (multFinish D w (filler K .peer) res known offset rec fresh i).getD 0 T =
      (multFinish D w (filler K .peer) res known offset rec fresh j).getD 0 T := by
  have hf := unknown_no_corrupt_filler K D T hT .peer
  funext g
  rw [multFinish_some D w _ res known offset rec fresh i hi hir, multFinish_some D w _ res known offset rec fresh j hj hjr]
  simp only [hiT, hjT, true_and, hf, if_false]

lemma halvInputs_total0 (K : Constants C E) (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) :
    extendTotal K D (halvInputs D len A B) 0 =
      ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range (halvedLength len), A i k * B i k := by
  unfold extendTotal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ∉ D.1 := (Finset.mem_filter.mp hi).2
  simp only [halvInputs, hi', if_false, Option.map_some, Option.getD_some, halvProducts]
  rfl

lemma halvInputs_total1 (K : Constants C E) (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E) :
    extendTotal K D (halvInputs D len A B) 1 =
      ∑ i ∈ univ.filter (· ∉ D.1), lagrangeAll K i * ∑ k ∈ range (halvedLength len),
        (A i k + (if k + halvedLength len < len then A i (k + halvedLength len) else 0)) *
        (B i k + (if k + halvedLength len < len then B i (k + halvedLength len) else 0)) := by
  unfold extendTotal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ∉ D.1 := (Finset.mem_filter.mp hi).2
  simp only [halvInputs, hi', if_false, Option.map_some, Option.getD_some, halvProducts]
  rfl

/-- The output share of the multiplication of a halving step at an honest receiver. -/
def halvOut {σ' : Type} (K : Constants C E) (D : C.Coalition) (len : ℕ) (A B : C.Party → ℕ → E)
    (pa : σ' × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (i : C.Party) : Shares C E :=
  (multFinish D 2 (filler K .peer) (fun g => extendTotal K D (halvInputs D len A B) g + pa.2.1 g)
    pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i).getD 0

/-- The halving relation and the history relation after a halving step. -/
lemma halv_after {σ' : Type} (K : Constants C E) (D : C.Coalition) (len : ℕ) (AR BR AD BD : C.Party → ℕ → E)
    (DR DD : C.Party → E) (hrel : HalvRel K D len AR BR AD BD DR DD) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD)
    (pa : σ' × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2) (r : E) :
    HalvRel K D (halvedLength len) (fun i => halvFold len r (AR i)) (fun i => halvFold len r (BR i))
      (fun i => halvFold len r (AD i)) (fun i => halvFold len r (BD i))
      (fun i => conv K (localContext i) (halvOut K D len AR BR pa fresh i) 0 +
        (DR i + conv K (localContext i) (halvOut K D len AR BR pa fresh i) 1) * r +
        conv K (localContext i) (halvOut K D len AR BR pa fresh i) 1 * r ^ 2)
      (fun i => conv K (localContext i) (halvOut K D len AD BD pa fresh i) 0 +
        (DD i + conv K (localContext i) (halvOut K D len AD BD pa fresh i) 1) * r +
        conv K (localContext i) (halvOut K D len AD BD pa fresh i) 1 * r ^ 2) ∧
    HistRel D tg (L + 1 + 1)
      (fun i => ⟨recordHistory K i (hsR i).history (halvOut K D len AR BR pa fresh i) 2, (hsR i).label + 1 + 1,
        (hsR i).tag⟩)
      (fun i => ⟨recordHistory K i (hsD i).history (halvOut K D len AD BD pa fresh i) 2, (hsD i).label + 1 + 1,
        (hsD i).tag⟩) := by
  letI : CharP E 2 := charP_two
  obtain ⟨htagR, htagD, hknownHist, hcommonR, hcommonD⟩ := hh
  constructor
  · refine halvRel_step K D len AR BR AD BD DR DD hrel r _ _
      (extendTotal K D (halvInputs D len AR BR) 0 - extendTotal K D (halvInputs D len AD BD) 0)
      (extendTotal K D (halvInputs D len AR BR) 1 - extendTotal K D (halvInputs D len AD BD) 1)
      ?_ (by rw [halvInputs_total0, halvInputs_total0]) (by rw [halvInputs_total1, halvInputs_total1])
    intro i hi T hT g hg
    unfold halvOut
    rw [multFinish_diff D 2 _ _ _ _ _ _ fresh i hi (hrec i hi) T hT g hg]
    split_ifs with h1 h2
    · subst h2; ring
    · have : g = 1 := by omega
      subst this; ring
    · rfl
  · refine ⟨fun i hi => by simp [htagR i hi], fun i hi => by simp [htagD i hi], ?_, ?_, ?_⟩
    · intro T hT i hi hiT
      simp only [recordHistory, if_pos hiT, hknownHist T hT i hi hiT]
      unfold halvOut
      rw [multFinish_known D 2 _ _ _ _ _ _ fresh i hi (hrec i hi) T hT]
    · intro T hT i j hi hj hiT hjT
      simp only [recordHistory, if_pos hiT, if_pos hjT, hcommonR T hT i j hi hj hiT hjT]
      unfold halvOut
      rw [multFinish_unknown K D 2 _ _ _ _ fresh T hT i j hi hj (hrec i hi) (hrec j hj) hiT hjT]
    · intro T hT i j hi hj hiT hjT
      simp only [recordHistory, if_pos hiT, if_pos hjT, hcommonD T hT i j hi hj hiT hjT]
      unfold halvOut
      rw [multFinish_unknown K D 2 _ _ _ _ fresh T hT i j hi hj (hrec i hi) (hrec j hj) hiT hjT]

lemma rl_answer_bound (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State) (v : C.Party → List (Product C E)) :
    IsQueryBoundP ((rightAdversary (leftAdversary Ad)).answer st v) DigestQuery step := by
  apply counted_digestBound
  dsimp only [leftAdversary, rightAdversary]
  simp only [bind_assoc, pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

/-- The programs after the multiplication of a halving step. -/
lemma halvAfter_form (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F' : ℕ) (st : Ad.State)
    (hs : C.Party → RunState C) (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (fresh : C.Term → Fin 2 → E) :
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => afterExtend K i 2 (hs i) (halvNext K width n j (A i) (B i) (V i) i)
        (multFinish D 2 (filler K .peer)
          (fun g => extendTotal K D (halvInputs D (halvedLength^[j] width) A B) g + pa.2.1 g)
          pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i)) =
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => if i ∈ pa.2.2.2.2 then
        (challenge K (hybridCheckGadgets K i) >>= fun r =>
          halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r (A i))
            (halvFold (halvedLength^[j] width) r (B i))
            (conv K (localContext i) (halvOut K D (halvedLength^[j] width) A B pa fresh i) 0 +
              (V i + conv K (localContext i) (halvOut K D (halvedLength^[j] width) A B pa fresh i) 1) * r +
              conv K (localContext i) (halvOut K D (halvedLength^[j] width) A B pa fresh i) 1 * r ^ 2) i).run'
          ⟨recordHistory K i (hs i).history (halvOut K D (halvedLength^[j] width) A B pa fresh i) 2,
            (hs i).label + 1, (hs i).tag⟩
        else failure) := by
  apply executePhase_congr_honest
  intro i hi
  rw [multFinish_honest D 2 _ _ _ _ _ _ i hi]
  by_cases hr : i ∈ pa.2.2.2.2
  · simp only [hr, if_true, afterExtend, halvOut, halvNext]
  · simp only [hr, if_false, afterExtend]

/-- The challenge continuation of a halving step. -/
def halvCont (K : Constants C E) (width n j : ℕ) (A B : C.Party → ℕ → E) (V : C.Party → E)
    (z : C.Party → Shares C E) (i : C.Party) (r : E) : RunM C E (CheckSpec C E) Unit :=
  halvProg K width n (j + 1) (halvFold (halvedLength^[j] width) r (A i)) (halvFold (halvedLength^[j] width) r (B i))
    (conv K (localContext i) (z i) 0 + (V i + conv K (localContext i) (z i) 1) * r +
      conv K (localContext i) (z i) 1 * r ^ 2) i

/-- The rest of a halving step after the coin of its challenge. -/
def halvCoinNext {β : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (hs : C.Party → RunState C) (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
    (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (y : (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
      (Ad.State × Finset C.Party)) : OracleComp (LocalSpec C) β :=
  executePhase localRoles D Ad (checkFunctionalities K) F y.2.1
    (fun i => afterChallenge K (hs i) (g i) (if i ∉ D.1 ∧ i ∈ y.2.2 then some (List.ofFn y.1) else none)) >>= tail

/-- The challenge phase of a halving step, from its coin. -/
lemma halvChallenge_eq {β : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (rec : Finset C.Party) (hrec : ∀ i, i ∉ D.1 → i ∈ rec) (hs : C.Party → RunState C)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
    (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if i ∈ rec then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i) else failure) >>= tail =
    coinDraw D Ad st >>= halvCoinNext K D Ad F hs g tail := by
  rw [executePhase_challenge_live K D Ad F st (fun i => i ∈ rec) hs g, if_pos hrec]
  have hin : ∀ i, i ∉ D.1 → ((if i ∈ D.1 then none else some 1 : Option ℕ)).isSome := by
    intro i hi; simp [hi]
  rw [runFunctionality_coin_local D (leftAdversary (leftAdversary Ad)) st _ hin]
  simp only [coinDraw, halvCoinNext, bind_assoc, pure_bind]

/-- One coin of a halving step: the common challenge and then the rest of the check. -/
theorem halvCoin_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width n j F : ℕ) {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hIH : HalvRest prims K D Ad step final width n (j + 1) F tail) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD) (AR BR AD BD : C.Party → ℕ → E) (DR DD : C.Party → E)
    (hrel : HalvRel K D (halvedLength^[j] width) AR BR AD BD DR DD)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2)
    (y : (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
      (Ad.State × Finset C.Party))
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    tvDist ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsR i).history (halvOut K D (halvedLength^[j] width) AR BR pa fresh i) 2,
          (hsR i).label + 1, (hsR i).tag⟩)
        (halvCont K width n j AR BR DR (halvOut K D (halvedLength^[j] width) AR BR pa fresh)) tail y)).run' cache)
      ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsD i).history (halvOut K D (halvedLength^[j] width) AD BD pa fresh i) 2,
          (hsD i).label + 1, (hsD i).tag⟩)
        (halvCont K width n j AD BD DD (halvOut K D (halvedLength^[j] width) AD BD pa fresh)) tail y)).run' cache) ≤
      coupleBound C step final seen.card F := by
  have hafter := halv_after K D (halvedLength^[j] width) AR BR AD BD DR DD hrel tg L hsR hsD hh pa fresh hrec
  have hrel' := fun r => (hafter r).1
  have hh' := (hafter 0).2
  have htagR := hh.1
  have htagD := hh.2.1
  by_cases hy : ∃ i, i ∉ D.1 ∧ i ∈ y.2.2
  · unfold halvCoinNext
    rw [tvDist_sameRun_congr prims
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagR i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tail out))
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagD i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tail out)),
      bind_assoc, bind_assoc]
    refine tvDist_prefix prims _ _ _ 0 (challengeQuery_no_digest K tg (L + 1) (List.ofFn y.1)) cache seen hc _ ?_
    intro r cache' seen' hc' hcard
    rcases r with _ | r
    · simp only [executePhase_failure, tvDist_self]
      exact coupleBound_nonneg _ _ _ _
    · refine le_trans ?_ (coupleBound_mono (s := seen'.card) (f := F) (by omega))
      have hrelr := hrel' r
      rw [← Function.iterate_succ_apply' halvedLength j width] at hrelr
      exact hIH y.2.1 y.2.2 tg (L + 1 + 1) _ _ _ _ _ _ _ _ cache' seen' hrelr hh' hc'
  · push Not at hy
    have hfail : ∀ (hs : C.Party → RunState C) (g : C.Party → E → RunM C E (CheckSpec C E) Unit),
        halvCoinNext K D Ad F hs g tail y = tail (y.2.1, fun _ => none) := by
      intro hs g
      unfold halvCoinNext
      rw [executePhase_congr_honest D Ad _ F y.2.1 _ (fun _ => failure), executePhase_failure, pure_bind]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ y.2.2) := fun h => hy i h.1 h.2
      simp only [hn, if_false, afterChallenge]
    rw [hfail, hfail, tvDist_self]
    exact coupleBound_nonneg _ _ _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- One uniform sample before two computations: it makes no outer-digest call. -/
lemma tvDist_sample1 (prims : Primitives) {α β : Type} [SampleableType α]
    (f g : α → OracleComp (LocalSpec C) β)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (c : ℝ)
    (h : ∀ w (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ seen.card →
      tvDist ((simulateQ (localAnswer prims) (f w)).run' cache')
        ((simulateQ (localAnswer prims) (g w)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) (liftComp ($ᵗ α) (LocalSpec C) >>= f)).run' cache)
      ((simulateQ (localAnswer prims) (liftComp ($ᵗ α) (LocalSpec C) >>= g)).run' cache) ≤ c :=
  tvDist_prefix prims _ _ _ 0 (prob_lift_no_digest _) cache seen hc c fun w cache' seen' hc' hcard =>
    h w cache' seen' hc' (by omega)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma tvDist_prefix_tail (prims : Primitives) {α γ β : Type} (oa : OracleComp (LocalSpec C) α)
    (f g : α → OracleComp (LocalSpec C) γ) (tail : γ → OracleComp (LocalSpec C) β) (n : ℕ)
    (hq : IsQueryBoundP oa DigestQuery n)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (c : ℝ)
    (h : ∀ a (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ seen.card + n →
      tvDist ((simulateQ (localAnswer prims) (f a >>= tail)).run' cache')
        ((simulateQ (localAnswer prims) (g a >>= tail)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) ((oa >>= f) >>= tail)).run' cache)
      ((simulateQ (localAnswer prims) ((oa >>= g) >>= tail)).run' cache) ≤ c := by
  rw [bind_assoc, bind_assoc]
  exact tvDist_prefix prims oa _ _ n hq cache seen hc c h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma tvDist_sample1_tail (prims : Primitives) {α γ β : Type} [SampleableType α]
    (f g : α → OracleComp (LocalSpec C) γ) (tail : γ → OracleComp (LocalSpec C) β)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (c : ℝ)
    (h : ∀ w (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ seen.card →
      tvDist ((simulateQ (localAnswer prims) (f w >>= tail)).run' cache')
        ((simulateQ (localAnswer prims) (g w >>= tail)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) ((liftComp ($ᵗ α) (LocalSpec C) >>= f) >>= tail)).run' cache)
      ((simulateQ (localAnswer prims) ((liftComp ($ᵗ α) (LocalSpec C) >>= g) >>= tail)).run' cache) ≤ c := by
  rw [bind_assoc, bind_assoc]
  exact tvDist_sample1 prims _ _ cache seen hc c h

/-- One halving step keeps the coupling of the rest of the check. -/
theorem halvRest_succ (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width n j F : ℕ) (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hIH : HalvRest prims K D Ad step final width n (j + 1) F tail) :
    HalvRest prims K D Ad step final width (n + 1) j (F + 1 + 1) tail := by
  intro st live tg L hsR hsD AR BR AD BD DR DD cache seen hrel hh hc
  by_cases hall : ∀ i, i ∉ D.1 → i ∈ live
  swap
  · rw [halvExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsR width n j AR BR DR,
      halvExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsD width n j AD BD DD, tvDist_self]
    exact coupleBound_nonneg _ _ _ _
  rw [halvExtend_local K D Ad (F + 1) st (· ∈ live) hall hsR width n j AR BR DR,
    halvExtend_local K D Ad (F + 1) st (· ∈ live) hall hsD width n j AD BD DD,
    ← halvInputs_view K D _ AR BR AD BD DR DD hrel]
  have hq1 := rl_answer_bound Ad step ha st (extendView K D.1 (halvInputs D (halvedLength^[j] width) AR BR))
  refine tvDist_prefix_tail prims _ _ _ tail step hq1 cache seen hc _ ?_
  intro pa cache1 seen1 hc1 hcard1
  refine tvDist_sample1_tail prims _ _ tail cache1 seen1 hc1 _ ?_
  intro fresh cache2 seen2 hc2 hcard2
  rw [halvAfter_form K D Ad (F + 1) pa.1 hsR width n j AR BR DR pa fresh,
    halvAfter_form K D Ad (F + 1) pa.1 hsD width n j AD BD DD pa fresh]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  · rw [halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tail, halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tail]
    refine tvDist_prefix prims (coinDraw D Ad pa.1) _ _ step (coinDraw_digestBound D Ad step ha pa.1) cache2 seen2 hc2
      _ ?_
    intro y cache3 seen3 hc3 hcard3
    have hF : (F + 1 + 1) * step = F * step + step + step := by ring
    exact le_trans (halvCoin_tv prims K D Ad step final width n j F tail hIH tg L hsR hsD hh AR BR AD BD DR DD hrel pa
      fresh hrec y cache3 seen3 hc3) (coupleBound_mono (by omega))
  · rw [executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec,
      executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec, tvDist_self]
    exact coupleBound_nonneg _ _ _ _

/-- The halving loop and the final segment keep the coupling (GS20, Protocols 14 and 15). -/
theorem halvRest_all (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final) :
    ∀ n j fuel, j + n = halvingSteps width →
      HalvRest prims K D Ad step final width n j (fuel + 2 * n + 5) tail
  | 0, j, fuel, h => by
    simp only [Nat.add_zero] at h
    subst h
    simpa using halvRest_zero prims K D Ad step final width fuel hr ha hw tail hq
  | n + 1, j, fuel, h => by
    have he : fuel + 2 * (n + 1) + 5 = fuel + 2 * n + 5 + 1 + 1 := by ring
    rw [he]
    exact halvRest_succ prims K D Ad step final width n j (fuel + 2 * n + 5) ha tail
      (halvRest_all prims K D Ad step final width hr ha hw tail hq n (j + 1) fuel (by omega))

/-- `CheckCoreDistance` from the three open stages. -/
theorem checkCoreDistanceProof (prims : Primitives) (K : Constants C E)
    (hsound : CheckSoundStage prims K) (hcouple : CheckCoupleStage prims K)
    (hsplit : CheckSplitStage prims K) : CheckCoreDistance prims K :=
  checkCoreDistance prims K hsound hcouple hsplit

end Stages

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.checkCoreDistanceProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.checkCoreDistanceProof

/-- info: 'ThresholdLeanXmssSecurity.finalStep_tv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.finalStep_tv

/-- info: 'ThresholdLeanXmssSecurity.halvRest_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.halvRest_all
