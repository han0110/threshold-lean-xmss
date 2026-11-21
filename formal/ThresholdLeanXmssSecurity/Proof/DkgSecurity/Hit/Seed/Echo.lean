import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CompHit

/-!
# The echo comparison `EchoCompare` from three statements

`compRun` and `listRun` differ in the shared key cells of the honest pairs that share a hidden term,
and in the echo test of these pairs. This file puts one run between them and splits `EchoCompare`.

* `levelPre` is `levelRound` up to the local steps of the round. `levelRound_eq_pre` writes a round as
  `levelPre` and then the rest of the phase.
* `seedPre` is the seed generation of `compRun` to the end of round 2, and `seedPost out next` is round 3
  with the echo message `out` and the echo test `next`. `seedGenNormal_split` states that the seed
  generation of `compRun` is `seedPre` and then `seedPost` with the echo of the protocol.
* `preRun` is `compRun` to the end of round 2, and `postRun` is the rest. `compRun_split` states that
  `compRun` is `preRun` and then `postRun` with the echo of the protocol. `midRun` is `preRun` and then
  `postRun` with the round 3 of the list program. So `midRun` asks each shared key cell and compares the
  lists of the honest pairs that share a hidden term.
* `EchoBad e` states that at the end `e` of round 2 two honest operators that share a hidden term have
  values for which the test on the hashes and the test on the lists give different results.
  `seedPost_eq_of_not_bad` states that off `EchoBad` the two forms of round 3 are equal programs.
* `EchoPair` bounds `EchoBad` with no counted call at the list of an honest pair by `C(n,2) / 2^256`.
* `MidList` states that `midRun` and `listRun` give one law of the parts, the seeds and the log.
* `echoCompare_of_parts` gives `EchoCompare` from `EchoPair` and `MidList`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## A round up to its local steps -/

section Level

variable {E : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- `levelRound` up to the local steps of the round. The result is the output of the phase when the
phase ends in this round, or the fuel, the state and the values of the operators for the rest. -/
def levelPre {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y)) :
    OracleComp (WorldSpec C) ((net.State × (C.Party → Option β)) ⊕ (ℕ × net.State × (C.Party → Option Y))) :=
  match fuel with
  | 0 => pure (.inl (state, fun _ => none))
  | fuel + 1 =>
    if ∀ i, i ∉ D.1 → d i = none then pure (.inl (state, fun _ => none)) else
    counted (liftComp (net.round state (levelMail D d out)) _) >>= fun r =>
      if ∃ i, i ∉ D.1 ∧ d i = none then pure (.inl (r.1, fun _ => none)) else
      OverPermutation.sequenceFin (fun j => if j ∈ D.1 then pure none else
        match d j with
        | none => pure none
        | some x => if anyAbort (levelInbox D d out r.2 j) then pure none else
            free (next j x (levelInbox D d out r.2 j))) >>= fun d' => pure (.inr (fuel, r.1, d'))

theorem levelRound_eq_pre {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    levelRound D net fuel state d out next cont =
      levelPre (β := β) D net fuel state d out next >>= Sum.elim pure fun p => cont p.1 p.2.1 p.2.2 := by
  cases fuel with
  | zero => simp [levelRound, levelPre]
  | succ fuel =>
    simp only [levelRound, levelPre]
    by_cases h1 : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left h1, ite_eq_left h1, pure_bind]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h1, bind_assoc]
      refine bind_congr fun r => ?_
      by_cases h2 : ∃ i, i ∉ D.1 ∧ d i = none
      · rw [ite_eq_left h2, ite_eq_left h2, pure_bind]
        rfl
      · rw [ite_eq_right h2, ite_eq_right h2, bind_assoc]
        simp only [pure_bind]
        rfl

end Level

/-! ## The seed generation in two parts -/

section Parts

variable {E : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The end of round 2. The output of the seed generation when it ends there, or the fuel, the state
and the values of the operators for round 3. -/
abbrev EchoPoint (C : Committee) (σ : Type) :=
  (σ × (C.Party → Option (Keys C))) ⊕ (ℕ × σ × (C.Party → Option (SeedGenEchoData C)))

/-- The seed generation of the normal form to the end of round 2. -/
def seedPre (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) : OracleComp (WorldSpec C) (EchoPoint C net.State) :=
  commitDraws D parts >>= fun commitments =>
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  levelPre D net (setupRounds - 1) r.1.1 (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i))
    (fun i _ inbox => revealNext D parts (commitInbox D commitments r.1.2) i inbox)

/-- Round 3 of the seed generation with the echo message `out` and the echo test `next`. -/
def seedPost (out : C.Party → SeedGenEchoData C → Mail C E)
    (next : C.Party → SeedGenEchoData C → Mail C E → OracleComp (LocalSpec C) (Option (Keys C)))
    (e : EchoPoint C net.State) : OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) :=
  Sum.elim pure (fun p => levelRound D net p.1 p.2.1 p.2.2 out next fun _ s3 d3 =>
    pure (s3, fun j => if j ∈ D.1 then none else d3 j)) e

theorem seedGenNormal_split (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    seedGenNormal D net state early parameter dealt parts =
      seedPre D net state early parameter dealt parts >>=
        seedPost D net (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext := by
  unfold seedGenNormal seedGenNormalWith seedPre seedPost
  simp only [bind_assoc]
  refine bind_congr fun commitments => bind_congr fun r => bind_congr fun _ => ?_
  rw [levelRound_eq_pre]

end Parts

/-! ## The runs in two parts -/

section Runs

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The rest of the game after the seed generation with the output `y`. -/
def restOf (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (y : A.net.State × (C.Party → Option (Keys C))) : OracleComp (WorldSpec C) (RunOut C) := do
  let keys := fun i => (y.2 i).map fun _ => x.2.1.2.2 i
  let win ← (secRest K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.2.1.1 x.2.1.2.1 x.2.1.2.2 y.2).run'
    (startState D y.1 keys)
  pure (win, x.2.1.1, x.2.1.2.1, x.2.1.2.2, y.2)

/-- The result of `preRun`, namely the prefix with its world state, the seeds, and the end of round 2
with its world state. -/
abbrev PreOut (C : Committee) (σ : Type) :=
  (PrefixOut C σ × LogState C) × (C.Term → HashOutput) × (EchoPoint C σ × LogState C)

/-- `compRun` to the end of round 2. -/
def preRun (D : C.Coalition) (A : DkgTsigAdversary C E) : ProbComp (PreOut C A.net.State) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let seed ← $ᵗ (C.Term → HashOutput)
  let e ← (simulateQ (compWorld prims D x.1.2.2 seed)
    (seedPre D A.net x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2.2 x.1.2.2)).run x.2
  pure (x, seed, e)

/-- The rest of a run after round 2, with the echo message `out` and the echo test `next`. -/
def postRun (D : C.Coalition) (A : DkgTsigAdversary C E) (out : C.Party → SeedGenEchoData C → Mail C E)
    (next : C.Party → SeedGenEchoData C → Mail C E → OracleComp (LocalSpec C) (Option (Keys C)))
    (y : PreOut C A.net.State) : ProbComp (RunOut C × LogState C) :=
  (simulateQ (compWorld prims D y.1.1.2.2 y.2.1)
    (seedPost D A.net out next y.2.2.1 >>= restOf K circuits settings runLimit D A y.1.1)).run y.2.2.2

/-- The middle run. It is `compRun` to the end of round 2, and then round 3 of the list program. -/
def midRun (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ProbComp ((C.Party → Parts C) × (C.Term → HashOutput) × LogState C) := do
  let y ← preRun prims D A
  let z ← postRun prims K circuits settings runLimit D A (outList D) (echoNextList D) y
  pure (y.1.1.2.2, y.2.1, z.2)

omit [Fintype E] [DecidableEq E] in
theorem compRun_split (D : C.Coalition) (A : DkgTsigAdversary C E) :
    compRun prims K circuits settings runLimit D A = (do
      let y ← preRun prims D A
      let z ← postRun prims K circuits settings runLimit D A (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext y
      pure (y.1.1.2.2, y.2.1, z)) := by
  unfold compRun preRun postRun dealtSuffix
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun x => bind_congr fun seed => ?_
  rw [seedGenRest_eq_normal, seedGenNormal_split]
  simp only [bind_assoc, simulateQ_bind, StateT.run_bind]
  refine bind_congr fun e => bind_congr fun s => ?_
  simp only [restOf, simulateQ_bind, StateT.run_bind, bind_assoc]

end Runs

/-! ## The event on the end of round 2 -/

section Bad

variable {E : Type}

/-- At the end `e` of round 2, two honest operators that share a hidden term have values for which
the test on the hashes and the test on the lists give different results. -/
def EchoBad {σ : Type} (D : C.Coalition) : EchoPoint C σ → Prop
  | .inl _ => False
  | .inr p => ∃ (i j : C.Party) (x y : SeedGenEchoData C), i ∉ D.1 ∧ j ∉ D.1 ∧ i ≠ j ∧ SharesHidden D i j ∧
      p.2.2 i = some x ∧ p.2.2 j = some y ∧
      ¬ ((echoList i j x = echoList j i y) ↔ (echoOf .seedGen x.1 x.2 j = echoOf .seedGen y.1 y.2 i))


theorem mem_sharedTerms_comm (i j : C.Party) (T : C.Term) : T ∈ sharedTerms i j ↔ T ∈ sharedTerms j i := by
  simp [sharedTerms, and_comm]

theorem sharesHidden_symm (D : C.Coalition) {i j : C.Party} (hi : i ∉ D.1) (h : SharesHidden D i j) :
    SharesHidden D j i := by
  obtain ⟨-, T, hT, hk⟩ := h
  exact ⟨hi, T, (mem_sharedTerms_comm i j T).1 hT, hk⟩

theorem isAbort_outList (D : C.Coalition) (i : C.Party) (x : SeedGenEchoData C) (j : C.Party) :
    Msg.isAbort (outList (E := E) D i x j) = false := by
  unfold outList echoOutbox
  split_ifs <;> rfl

theorem isAbort_echoOutbox (i : C.Party) (x : SeedGenEchoData C) (j : C.Party) :
    Msg.isAbort (echoOutbox (E := E) .seedGen i x.1 x.2 j) = false := by
  unfold echoOutbox
  split_ifs <;> rfl

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

theorem levelMail_outList (d : C.Party → Option (SeedGenEchoData C)) :
    levelMail D d (outList D) = levelMail D d (fun i x => echoOutbox (E := E) .seedGen i x.1 x.2) := by
  funext c i
  unfold levelMail
  by_cases h : c ∈ D.1 ∧ i ∉ D.1
  · rw [ite_eq_left h, ite_eq_left h]
    rcases d i with _ | x
    · rfl
    · have hs : ¬ (c ≠ i ∧ SharesHidden D i c) := fun hc => hc.2.1 h.1
      simp only [outList, hs, ite_false]
  · rw [ite_eq_right h, ite_eq_right h]

theorem anyAbort_outList (d : C.Party → Option (SeedGenEchoData C)) (sent : C.Party → C.Party → Option (Msg E))
    (j : C.Party) :
    anyAbort (levelInbox D d (outList D) sent j) =
      anyAbort (levelInbox D d (fun i x => echoOutbox (E := E) .seedGen i x.1 x.2) sent j) := by
  unfold anyAbort
  congr 1
  funext k
  unfold levelInbox
  by_cases hk : k ∈ D.1
  · simp only [hk, ite_true]
  · simp only [hk, ite_false]
    rcases d k with _ | x
    · rfl
    · rw [isAbort_outList, isAbort_echoOutbox]

/-- Off `EchoBad`, the echo test of an honest operator on the hashes and on the lists agree. -/
theorem echoCheck_iff_list (d : C.Party → Option (SeedGenEchoData C)) (sent : C.Party → C.Party → Option (Msg E))
    (j : C.Party) (x : SeedGenEchoData C) (hj : j ∉ D.1) (hd : d j = some x) (hsome : ∀ k, k ∉ D.1 → d k ≠ none)
    (hbad : ¬ EchoBad D (.inr ((0 : ℕ), (), d) : EchoPoint C Unit)) :
    echoCheck .seedGen j x.1 x.2 (levelInbox D d (fun i x => echoOutbox (E := E) .seedGen i x.1 x.2) sent j) ↔
      echoListCheck D j x (levelInbox D d (outList D) sent j) := by
  unfold echoCheck echoListCheck
  refine forall_congr' fun k => imp_congr_right fun hkj => ?_
  unfold levelInbox
  by_cases hk : k ∈ D.1
  · have hs : ¬ SharesHidden D j k := fun h => h.1 hk
    simp only [hk, ite_true, hs, ite_false]
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hsome k hk)
    simp only [hk, ite_false, hy]
    have hjk : j ≠ k := Ne.symm hkj
    by_cases hs : SharesHidden D j k
    · have hs' : SharesHidden D k j := sharesHidden_symm D hj hs
      simp only [outList, echoOutbox, hjk, hs', hs, ne_eq, not_false_eq_true, and_self, ite_true, ite_false,
        Msg.hashesOf]
      by_contra hne
      refine hbad ⟨j, k, x, y, hj, hk, hjk, hs, hd, hy, fun hiff => hne ?_⟩
      constructor
      · intro h
        exact (hiff.2 h.symm).symm
      · intro h
        exact (hiff.1 h.symm).symm
    · have hs' : ¬ (j ≠ k ∧ SharesHidden D k j) := fun h => hs (sharesHidden_symm D hk h.2)
      simp only [outList, hs', hs, ite_false]


/-- Off `EchoBad`, round 3 with the echo of the protocol and round 3 of the list program are equal
programs. -/
theorem seedPost_eq_of_not_bad (e : EchoPoint C net.State) (hbad : ¬ EchoBad D e) :
    seedPost D net (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext e = seedPost D net (outList D) (echoNextList D) e := by
  rcases e with y | ⟨fuel, state, d⟩
  · rfl
  simp only [seedPost, Sum.elim_inr]
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [levelRound]
    rw [levelMail_outList]
    by_cases h1 : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left h1, ite_eq_left h1]
    rw [ite_eq_right h1, ite_eq_right h1]
    refine bind_congr fun r => ?_
    by_cases h2 : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left h2, ite_eq_left h2]
    rw [ite_eq_right h2, ite_eq_right h2]
    have hsome : ∀ k, k ∉ D.1 → d k ≠ none := fun k hk hdk => h2 ⟨k, hk, hdk⟩
    congr 1
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true]
    simp only [hj, ite_false]
    rcases hd : d j with _ | x
    · rfl
    dsimp only
    rw [anyAbort_outList]
    by_cases ha : anyAbort (levelInbox D d (fun i x => echoOutbox (E := E) .seedGen i x.1 x.2) r.2 j) = true
    · simp only [ha, ite_true]
    simp only [ha, Bool.false_eq_true, ite_false]
    have hiff := echoCheck_iff_list D d r.2 j x hj hd hsome hbad
    simp only [echoNext, echoNextList]
    rw [if_congr hiff rfl rfl]

end Bad

/-! ## The statements -/

section Statements

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The bound for the pairs. At the end of round 2 of `compRun`, two honest operators that share a
hidden term have values for which the test on the hashes and the test on the lists differ, and no
counted call asked the list of an honest pair (`EchoPrior` on the log at the end of round 2). The
probability is at most `C(n,2) / 2^256`. The lists of all honest operators are fixed by their derive
calls before a test reads a shared key answer. A cell that no counted call asked has a fresh value at
its first read, also when an honest call for another pair read it first. Two distinct lists of one
unordered pair then get equal hashes with probability `1 / 2^256`. Equal lists ask one cell and get
equal hashes. The bound is a mean over the run from the empty start. -/
def EchoPair : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    Pr{let y ← preRun prims D A}[EchoBad D y.2.2.1 ∧ ¬ EchoPrior D y.1.1.2.2 y.2.1 y.2.2.2] ≤
      (C.n.choose 2 : ℝ≥0∞) / 2 ^ 256

/-- The middle run and the list run give one law of the parts, the seeds and the log. The middle run
asks the shared key cells of the honest pairs that share a hidden term, and no later step reads these
answers. A later counted call or an honest call at such a cell reads the stored answer in the middle
run and a fresh answer in the list run, which have one law. The caches are not equal. -/
def MidList : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    (fun r => (r.1, r.2.1, r.2.2.2)) <$> midRun prims K circuits settings runLimit D A =ᵈ
      (fun r => (r.1, r.2.1, r.2.2.2)) <$> listRun prims K circuits settings runLimit D A

end Statements

/-! ## The glue -/

section Glue

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

theorem compWorld_step_log (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)
    (t : (WorldSpec C).Domain) (s : LogState C) :
    ∀ z ∈ support ((compWorld prims D parts seed t).run s), z.2 = s ∨ z.2.2 = s.2 ++ countedCells t := by
  intro z hz
  unfold compWorld at hz
  split at hz
  · split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
    · exact Or.inr (loggedWorld_log prims D _ s z hz)
  · exact Or.inr (loggedWorld_log prims D _ s z hz)

/-- The log only grows along a world program in `compWorld`. -/
theorem compWorld_log_mono (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) {β : Type}
    (oa : OracleComp (WorldSpec C) β) (w : LogState C) :
    ∀ z ∈ support ((simulateQ (compWorld prims D parts seed) oa).run w), ∀ q ∈ w.2, q ∈ z.2.2 := by
  refine OracleComp.simulateQ_run_preservesInv (compWorld prims D parts seed) (fun s => ∀ q ∈ w.2, q ∈ s.2)
    (fun t s hs z hz => ?_) oa w fun q hq => hq
  intro q hq
  rcases compWorld_step_log prims D parts seed t s z hz with h | h
  · rw [h]
    exact hs q hq
  · rw [h]
    exact List.mem_append_left _ (hs q hq)

theorem echoPrior_mono (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)
    {w w' : LogState C} (h : ∀ q ∈ w.2, q ∈ w'.2) (hp : EchoPrior D parts seed w) : EchoPrior D parts seed w' := by
  obtain ⟨q, hq, rest⟩ := hp
  exact ⟨q, h q hq, rest⟩

omit [Fintype E] [DecidableEq E] in
/-- The bound for one end of round 2. -/
theorem post_le (D : C.Coalition) (A : DkgTsigAdversary C E) (y : PreOut C A.net.State) :
    Pr{let r ← (postRun prims K circuits settings runLimit D A (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext y >>=
        fun z => pure (y.1.1.2.2, y.2.1, z))}[CompHitOf D r] ≤
      (if EchoBad D y.2.2.1 ∧ ¬ EchoPrior D y.1.1.2.2 y.2.1 y.2.2.2 then 1 else 0) +
        Pr{let r ← (postRun prims K circuits settings runLimit D A (outList D) (echoNextList D) y >>=
          fun z => pure (y.1.1.2.2, y.2.1, z.2))}[ListHit D r] := by
  by_cases hb : EchoBad D y.2.2.1
  · by_cases hp : EchoPrior D y.1.1.2.2 y.2.1 y.2.2.2
    · have h1 : Pr{let r ← (postRun prims K circuits settings runLimit D A (outList D) (echoNextList D) y >>=
          fun z => pure (y.1.1.2.2, y.2.1, z.2))}[ListHit D r] = 1 := by
        refine prEvent_eq_one_of_forall_mem_support _ _ fun r hr => ?_
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
        obtain ⟨z, hz, rfl⟩ := hr
        exact Or.inr (echoPrior_mono D _ _ (compWorld_log_mono prims D _ _ _ _ z hz) hp)
      rw [h1]
      exact (prEvent_le_one _).trans (le_add_left le_rfl)
    · rw [ite_eq_left ⟨hb, hp⟩]
      exact le_add_right (prEvent_le_one _)
  · have he : postRun prims K circuits settings runLimit D A (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext y =
        postRun prims K circuits settings runLimit D A (outList D) (echoNextList D) y := by
      unfold postRun
      rw [seedPost_eq_of_not_bad D A.net _ hb]
    rw [he, ite_eq_right fun h => hb h.1, zero_add, bind_pure_comp, bind_pure_comp, prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun z hz => Or.inl hz

omit [Fintype E] [DecidableEq E] in
/-- `EchoPair` and `MidList` give `EchoCompare`. -/
theorem echoCompare_of_parts (pair : EchoPair (C := C) (E := E) prims) (mid : MidList prims K circuits settings runLimit) :
    EchoCompare prims K circuits settings runLimit := by
  intro D A
  have e : ∀ r : (C.Party → Parts C) × (C.Term → HashOutput) × LogState C,
      ListHit D r ↔ ListHit D (r.1, r.2.1, (((∅, ∅) : StreamState C), r.2.2.2)) := fun r => Iff.rfl
  have hlist : Pr{let r ← listRun prims K circuits settings runLimit D A}[ListHit D r] =
      Pr{let r ← midRun prims K circuits settings runLimit D A}[ListHit D r] := by
    let proj := fun r : (C.Party → Parts C) × (C.Term → HashOutput) × LogState C => (r.1, r.2.1, r.2.2.2)
    have h1 : Pr{let p ← (proj <$> midRun prims K circuits settings runLimit D A)}[
        ListHit D (p.1, p.2.1, (((∅, ∅) : StreamState C), p.2.2))] =
        Pr{let p ← (proj <$> listRun prims K circuits settings runLimit D A)}[
          ListHit D (p.1, p.2.1, (((∅, ∅) : StreamState C), p.2.2))] :=
      (mid D A).prEvent_eq _
    rw [prEvent_map, prEvent_map] at h1
    rw [prEvent_congr _ _ _ e, prEvent_congr _ _ _ e]
    exact h1.symm
  rw [hlist, compRun_split, prEvent_bind_wp]
  unfold midRun
  rw [prEvent_bind_wp]
  calc _ ≤ wp (preRun prims D A) (fun y =>
        (if EchoBad D y.2.2.1 ∧ ¬ EchoPrior D y.1.1.2.2 y.2.1 y.2.2.2 then 1 else 0) +
          Pr{let r ← (postRun prims K circuits settings runLimit D A (outList D) (echoNextList D) y >>=
            fun z => pure (y.1.1.2.2, y.2.1, z.2))}[ListHit D r]) :=
        wp_mono _ fun y => post_le prims K circuits settings runLimit D A y
    _ = _ := by rw [wp_add, ← prEvent_eq_wp_indicator]
    _ ≤ _ := add_le_add (pair D A) le_rfl

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.echoCompare_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.echoCompare_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.seedPost_eq_of_not_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.seedPost_eq_of_not_bad
