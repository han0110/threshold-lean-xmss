import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Clash
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Rounds

/-!
# The normal form of the seed generation after the draw of the parts

`seedGenRest` runs the seed generation of the honest operators on the parts `parts`.
This file writes it as one explicit program of three rounds.

* `commitDraws` is the start. Each honest operator `i` asks the commit cell `commitAddress parts i j`
  for each operator `j` on the free copy.
* Round 1 is one call of the adversary on the commit messages, with the log of its calls.
  `commitInbox` is the inbox of each operator after it.
* `programBlock` is the programming block of `seedGenRest`, with no change.
* Round 2 is one `levelRound` with the reveal messages. `revealNext` is the local step of an honest
  operator `i` after it. It asks the open cells `openAddress`, tests them, asks the derive cells of
  `deriveKeys` on the view `normView`, and asks the shared key cells `sharedAddress`.
* Round 3 is one `levelRound` with the echo messages. `echoNext` is the echo test.

`seedGenRest_eq_raw` is the closed form with the local step `revealBody` of the library, which reads
the inbox of round 2. `seedGenRest_eq_normal` is the closed form with `revealNext`. In `revealNext` the
message of an honest sender is not read from the inbox. Its place holds the message that the sender
computes from its parts. So each address of an honest free call is a function of the operator, the
term and the parts. `termAddress_hidden` states that the derive address of a term with no corrupt
holder is `hiddenInput parts T` at each holder.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The addresses -/

/-- The commit cell of operator `i` for operator `j`. -/
def commitAddress (parts : C.Party → Parts C) (i j : C.Party) : Query C :=
  .commit .seedGen i j (revealTo .seedGen (parts i) i j)

/-- The reveals that operator `i` reads in round 2. A corrupt sender gives the entry of the inbox. An
honest sender gives its reveal from its parts. -/
def normRevealed (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E) : Mail C E :=
  fun k => if k ∈ D.1 then inbox k else revealOutbox .seedGen k (parts k) i

/-- The open cell that operator `i` asks for the commitment of operator `k`. -/
def openAddress (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E) (k : C.Party) :
    Query C :=
  .commit .seedGen k i (Msg.hashesOf (normRevealed D parts i inbox k))

/-- The parts that operator `i` uses for operator `k` after round 2. A corrupt `k` gives the reveal in
the inbox. An honest `k` gives its own parts. -/
def normView (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E) : C.Party → Parts C :=
  fun k => if k ∈ D.1 then readReveal .seedGen (Msg.hashesOf (inbox k)) i k else parts k

/-- The derive cell of the term `T` at operator `i`. -/
def termAddress (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E) (T : C.Term) :
    Query C :=
  .derive .seedGen .term ((seedGenHolderList T).map fun k => (normView D parts i inbox k).term T)

/-- The shared key cell of operator `i` for operator `j`, from the seeds `seeds` of `i`. -/
def sharedAddress (i j : C.Party) (seeds : C.Term → HashOutput) : Query C :=
  .sharedKeys .seedGen ((sharedTerms i j).map seeds)

/-! ## The program -/

/-- The commit calls of the honest operators on the free copy. A corrupt operator has no commitment. -/
def commitDraws (D : C.Coalition) (parts : C.Party → Parts C) : OracleComp (WorldSpec C) (C.Party → List HashOutput) :=
  OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure [] else
    free (liftComp (C.parties.mapM fun j => hashQuery (commitAddress parts i j)) (LocalSpec C))

/-- The mail that the adversary reads in round 1. -/
def commitMail (D : C.Coalition) (commitments : C.Party → List HashOutput) : C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∉ D.1 then commitOutbox i (commitments i) c else none

/-- The inbox of operator `j` after round 1, with the mail `sent` of the corrupt operators. -/
def commitInbox (D : C.Coalition) (commitments : C.Party → List HashOutput) (sent : C.Party → C.Party → Option (Msg E))
    (j : C.Party) : Mail C E :=
  fun k => if k ∈ D.1 then sent k j else commitOutbox k (commitments k) j

/-- The programming block of `seedGenRest` after round 1, with the log `log` and the mail `sent`. -/
def programBlock (D : C.Coalition) (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E))
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    OracleComp (WorldSpec C) Unit := do
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let view := fun (i j : C.Party) =>
    if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
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

/-- The abort pattern of round 2. An operator with an abort frame in its inbox of round 1 aborts. -/
def revealReady (committed : C.Party → Mail C E) : C.Party → Option Unit :=
  fun i => if anyAbort (committed i) then none else some ()

/-- The local step of operator `i` after round 2 in the library form. It reads the inbox `inbox`. -/
def revealBody (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (i : C.Party) (inbox : Mail C E) :
    OracleComp (LocalSpec C) (Option (SeedGenEchoData C)) :=
  liftComp (openQueries .seedGen i inbox) (LocalSpec C) >>= fun opens =>
    if openCheck .seedGen i (parts i) (committed i) inbox opens then
      liftComp (deriveKeys .seedGen i (setupView .seedGen i (parts i) inbox)) (LocalSpec C) >>= fun keys =>
        liftComp (sharedQueries .seedGen i keys) (LocalSpec C) >>= fun shared => pure (some (keys, shared))
    else pure none

/-- The local step of operator `i` after round 2 in the normal form. It asks the open cells, tests them,
asks the derive cells on the view `normView` and asks the shared key cells. -/
def revealNext (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (i : C.Party)
    (inbox : Mail C E) : OracleComp (LocalSpec C) (Option (SeedGenEchoData C)) :=
  liftComp (C.parties.mapM fun k => hashQuery (openAddress D parts i inbox k)) (LocalSpec C) >>= fun opens =>
    if openCheck .seedGen i (parts i) (committed i) (normRevealed D parts i inbox) opens then
      liftComp (deriveKeys .seedGen i (normView D parts i inbox)) (LocalSpec C) >>= fun keys =>
        liftComp (C.parties.mapM fun j => hashQuery (sharedAddress i j keys.2.1)) (LocalSpec C) >>= fun shared =>
          pure (some (keys, shared))
    else pure none

/-- The local step of operator `i` after round 3, the echo test. -/
def echoNext (i : C.Party) (x : SeedGenEchoData C) (inbox : Mail C E) : OracleComp (LocalSpec C) (Option (Keys C)) :=
  pure (if echoCheck .seedGen i x.1 x.2 inbox then some (_root_.ThresholdLeanXmssSecurity.keysOf x.1) else none)

/-- The seed generation after the draw of the parts as three explicit rounds, with the local step
`next` after round 2. -/
def seedGenNormalWith (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (next : (C.Party → Mail C E) → C.Party → Mail C E → OracleComp (LocalSpec C) (Option (SeedGenEchoData C))) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) :=
  commitDraws D parts >>= fun commitments =>
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  levelRound D net (setupRounds - 1) r.1.1 (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i))
    (fun i _ inbox => next (commitInbox D commitments r.1.2) i inbox) fun f2 s2 d2 =>
  levelRound D net f2 s2 d2 (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext fun _ s3 d3 =>
  pure (s3, fun j => if j ∈ D.1 then none else d3 j)

/-- The normal form of the seed generation after the draw of the parts. -/
def seedGenNormal (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) :=
  seedGenNormalWith D net state early parameter dealt parts (revealNext D parts)

/-! ## The raw closed form -/

section Raw

theorem startSteps_seedGen (D : C.Coalition) (parts : C.Party → Parts C) :
    startSteps worldRoles D (fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))) =
      commitDraws D parts >>= fun commitments => pure (setupInitialSteps .seedGen D parts commitments) := by
  have hstart : ∀ i, (if i ∈ D.1 then pure (Step.done none) else
      worldRoles.honest (advance (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C)).run) :
        OracleComp (WorldSpec C) _) =
      (if i ∈ D.1 then pure [] else
        free (liftComp (C.parties.mapM fun j => hashQuery (commitAddress parts i j)) (LocalSpec C))) >>= fun c =>
        pure (if i ∈ D.1 then Step.done none else setupStart .seedGen i (parts i) c) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · have h : (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C)) = setupWith .seedGen i (parts i) := rfl
      simp only [hi, ite_false, h, advance_setupWith, worldRoles, free_bind, free_pure]
      rfl
  unfold startSteps
  simp only [hstart, sequenceFin_bind_pure]
  rfl

theorem setupCommitInbox_eq (D : C.Coalition) (parts : C.Party → Parts C) (commitments : C.Party → List HashOutput)
    (sent : C.Party → C.Party → Option (Msg E)) :
    setupCommitInbox .seedGen D parts commitments sent = commitInbox D commitments sent := by
  funext j k
  unfold setupCommitInbox roundInbox commitInbox
  by_cases hk : k ∈ D.1
  · simp [hk]
  · simp [hk, setupInitialSteps, setupStart]

/-- The resume of operator `j` after round 2. -/
def revealResume (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (j : C.Party) :
    Unit → Mail C E → OracleComp (PartySpec C E RealSpec) (Option (Keys C)) :=
  fun _ => exchangeResume fun revealed =>
    setupRest .seedGen j (parts j) (committed j) revealed >>= fun keys => pure (_root_.ThresholdLeanXmssSecurity.keysOf keys)

/-- The resume of operator `j` after round 3. -/
def echoResume (j : C.Party) : SeedGenEchoData C → Mail C E → OracleComp (PartySpec C E RealSpec) (Option (Keys C)) :=
  fun x => exchangeResume fun received =>
    require (echoCheck .seedGen j x.1 x.2 received) >>= fun _ => pure (_root_.ThresholdLeanXmssSecurity.keysOf x.1)

theorem setupRevealSteps_eq (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    setupRevealSteps .seedGen D parts committed = fun j => if j ∈ D.1 then .done none else
      stageStep (fun _ => revealOutbox .seedGen j (parts j)) (revealResume parts committed j) (revealReady committed j) := by
  funext j
  unfold setupRevealSteps revealReady anyAbort
  by_cases hj : j ∈ D.1
  · simp [hj]
  · by_cases ha : (C.parties.any fun k => Msg.isAbort (committed j k)) = true
    · simp [hj, ha, stageStep]
    · simp [hj, ha, stageStep, revealResume]

theorem setupEchoDataStep_eq (j : C.Party) (y : Option (SeedGenEchoData C)) :
    (setupEchoDataStep .seedGen j y : Step C E RealSpec (Keys C)) =
      stageStep (fun x => echoOutbox .seedGen j x.1 x.2) (echoResume j) y := by
  rcases y with _ | ⟨keys, shared⟩ <;> rfl

theorem advance_revealResume (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (j : C.Party) (x : Unit)
    (inbox : Mail C E) :
    advance (revealResume parts committed j x inbox) =
      if anyAbort inbox then pure (.done none) else
        revealBody parts committed j inbox >>= fun y => pure (setupEchoDataStep .seedGen j y) := by
  unfold revealResume
  rw [advance_exchangeResume]
  split_ifs
  · rfl
  rw [advance_setupRest]
  unfold revealBody
  rw [bind_assoc]
  refine bind_congr fun opens => ?_
  split_ifs
  · simp only [bind_assoc, pure_bind]
    rfl
  · rw [pure_bind]
    rfl

theorem advance_echoResume (j : C.Party) (x : SeedGenEchoData C) (inbox : Mail C E) :
    advance (echoResume j x inbox) =
      if anyAbort inbox then pure (.done none) else
        echoNext j x inbox >>= fun y => pure (Step.done y) := by
  unfold echoResume echoNext
  rw [advance_setupEchoResume, pure_bind]
  unfold anyAbort
  split_ifs <;> rfl

/-- Rounds 2 and 3 for each fuel and each pattern of aborts, with the local step `revealBody`. -/
theorem executeRounds_reveal (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (state : net.State)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    executeRounds worldRoles D net noFunctionality fuel state (setupRevealSteps .seedGen D parts committed) =
      levelRound D net fuel state (revealReady committed) (fun i _ => revealOutbox .seedGen i (parts i))
        (fun i _ inbox => revealBody parts committed i inbox) fun f2 s2 d2 =>
      levelRound D net f2 s2 d2 (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext fun _ s3 d3 =>
      pure (s3, fun j => if j ∈ D.1 then none else d3 j) := by
  rw [setupRevealSteps_eq]
  refine (executeRounds_level D net fuel state (revealReady committed) _ (revealResume parts committed) _
    (fun j => setupEchoDataStep .seedGen j) (fun _ => rfl) (fun j x inbox => advance_revealResume parts committed j x inbox)).trans ?_
  refine levelRound_congr D net _ _ _ _ _ _ _ fun f2 s2 d2 => ?_
  simp only [setupEchoDataStep_eq]
  refine (executeRounds_level D net f2 s2 d2 _ echoResume echoNext (fun _ y => (Step.done y : Step C E RealSpec (Keys C)))
    (fun _ => rfl) (fun j x inbox => advance_echoResume j x inbox)).trans ?_
  refine levelRound_congr D net _ _ _ _ _ _ _ fun f3 s3 d3 => ?_
  rw [executeRounds_allDone D net noFunctionality _ f3 s3 _ fun j => by by_cases hj : j ∈ D.1 <;> simp [hj, Step.isDone]]
  congr 2
  funext j
  by_cases hj : j ∈ D.1 <;> simp [hj, Step.output]

theorem eraseLog_run {α β : Type} (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) (α × β)) :
    (p.run >>= fun x => match x with | ((a, b), _) => (pure (a, b) : OracleComp (WorldSpec C) (α × β))) =
      seedGenEraseLog p := by
  unfold seedGenEraseLog
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  rcases x with ⟨⟨a, b⟩, w⟩
  rfl

/-- The closed form of `seedGenRest` with the local step `revealBody` of the library after round 2. -/
theorem seedGenRest_eq_raw (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    seedGenRest D net state early parameter dealt parts =
      seedGenNormalWith D net state early parameter dealt parts (revealBody parts) := by
  unfold seedGenRest seedGenNormalWith
  rw [startSteps_seedGen]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun commitments => ?_
  rw [stepRound_setupInitialSteps_observed]
  simp only [observedRoles, WriterT.run_bind, WriterT.run_pure, map_pure, pure_bind, bind_assoc,
    show (∅ : CallLog C) = [] from rfl, List.append_nil, WriterT.run_mk]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨st, sent⟩, calls⟩
  simp only [programBlock, bind_assoc, pure_bind]
  refine bind_congr fun high => bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
  rw [eraseLog_run]
  refine (seedGenEraseLog_executeRounds D net (setupRounds - 1) st _).trans ?_
  rw [setupCommitInbox_eq, executeRounds_reveal]

end Raw

/-! ## The normal form -/

section Normal

/-- `deriveKeys` reads only the parts of `P`, the term parts of the held terms at their holders, and
the pair parts of the pairs of `i`. -/
theorem deriveKeys_congr (phase : Phase) (i : C.Party) (v w : C.Party → Parts C)
    (hpar : ∀ k, (v k).parameter = (w k).parameter)
    (hterm : ∀ T k, i ∈ C.holders T → k ∈ C.holders T → (v k).term T = (w k).term T)
    (hpair : ∀ a b, a = i ∨ b = i → (v a).pair b = (w a).pair b) :
    deriveKeys phase i v = deriveKeys phase i w := by
  have hP : (C.parties.map fun j => (v j).parameter) = C.parties.map fun j => (w j).parameter :=
    List.map_congr_left fun k _ => hpar k
  have h1 : C.terms.mapM (fun T => if i ∈ C.holders T then
      hashQuery (C := C) (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (v j).term T)) else pure 0) =
      C.terms.mapM (fun T => if i ∈ C.holders T then
      hashQuery (C := C) (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (w j).term T)) else pure 0) := by
    congr 1
    funext T
    split_ifs with hiT
    · rw [List.map_congr_left fun k hk => hterm T k hiT (by simpa using (List.mem_filter.1 hk).2)]
    · rfl
  have h2 : C.parties.mapM (fun j => if h : j = i then pure 0 else
      hashQuery (C := C) (.derive phase .pair [(v (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
        (v (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) =
      C.parties.mapM (fun j => if h : j = i then pure 0 else
      hashQuery (C := C) (.derive phase .pair [(w (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
        (w (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) := by
    congr 1
    funext j
    split_ifs with h
    · rfl
    · have hor := pairOf_left_or_right i j (Ne.symm h)
      rw [hpair _ _ hor, hpair _ _ hor.symm]
  simp only [deriveKeys]
  rw [hP, h1, h2]

/-- The inbox of operator `j` after round 2, when no honest operator aborted. -/
abbrev revealInbox (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) : Mail C E :=
  levelInbox D (revealReady committed) (fun i _ => revealOutbox .seedGen i (parts i)) sent j

theorem normRevealed_eq (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) (hsome : ∀ k, k ∉ D.1 → revealReady committed k ≠ none) :
    normRevealed D parts j (revealInbox D parts committed sent j) = revealInbox D parts committed sent j := by
  funext k
  unfold normRevealed revealInbox levelInbox
  by_cases hk : k ∈ D.1
  · simp [hk]
  · have h := hsome k hk
    rcases hr : revealReady committed k with _ | u
    · exact absurd hr h
    · simp [hk]

theorem setupView_revealInbox (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (sent : C.Party → C.Party → Option (Msg E)) (j k : C.Party) (hsome : ∀ k, k ∉ D.1 → revealReady committed k ≠ none)
    (hk : k ∉ D.1) :
    setupView .seedGen j (parts j) (revealInbox D parts committed sent j) k = honestView (E := E) .seedGen parts j k := by
  unfold honestView setupView honestReveals
  by_cases hkj : k = j
  · simp [hkj]
  · have h := congrFun (normRevealed_eq D parts committed sent j hsome) k
    simp only [normRevealed, hk, ite_false] at h
    simp only [hkj, ite_false, ← h]

/-- On the inbox of round 2 with no honest abort, the library step `revealBody` is the normal step
`revealNext`. -/
theorem revealBody_eq_next (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) (hj : j ∉ D.1)
    (hsome : ∀ k, k ∉ D.1 → revealReady committed k ≠ none) :
    revealBody parts committed j (revealInbox D parts committed sent j) =
      revealNext D parts committed j (revealInbox D parts committed sent j) := by
  have hL := normRevealed_eq D parts committed sent j hsome
  have hopen : openQueries .seedGen j (revealInbox D parts committed sent j) =
      C.parties.mapM fun k => hashQuery (openAddress D parts j (revealInbox D parts committed sent j) k) := by
    unfold openQueries openAddress
    rw [hL]
  have hview : deriveKeys .seedGen j (setupView .seedGen j (parts j) (revealInbox D parts committed sent j)) =
      deriveKeys .seedGen j (normView D parts j (revealInbox D parts committed sent j)) := by
    have hD : ∀ k, k ∈ D.1 → setupView .seedGen j (parts j) (revealInbox D parts committed sent j) k =
        normView D parts j (revealInbox D parts committed sent j) k := fun k hk => by
      have hkj : k ≠ j := fun e => hj (e ▸ hk)
      simp [setupView, normView, hk, hkj]
    refine deriveKeys_congr .seedGen j _ _ (fun k => ?_) (fun T k hjT hkT => ?_) (fun a b hab => ?_)
    · by_cases hk : k ∈ D.1
      · rw [hD k hk]
      · rw [setupView_revealInbox D parts committed sent j k hsome hk, honestView_parameter]
        simp [normView, hk]
    · by_cases hk : k ∈ D.1
      · rw [hD k hk]
      · rw [setupView_revealInbox D parts committed sent j k hsome hk, honestView_term .seedGen parts hkT hjT]
        simp [normView, hk]
    · by_cases ha : a ∈ D.1
      · rw [hD a ha]
      · rw [setupView_revealInbox D parts committed sent j a hsome ha, honestView_pair .seedGen parts hab]
        simp [normView, ha]
  unfold revealBody revealNext
  rw [hopen, hL, hview]
  rfl

/-- The local step after round 2 can be taken in its normal form. -/
theorem seedGenNormalWith_body_eq_next (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    seedGenNormalWith D net state early parameter dealt parts (revealBody parts) =
      seedGenNormal D net state early parameter dealt parts := by
  unfold seedGenNormal seedGenNormalWith
  refine bind_congr fun commitments => bind_congr fun r => bind_congr fun _ => ?_
  refine levelRound_congr_next D net _ _ _ _ _ _ _ fun sent j x hj hd hsome _ => ?_
  exact revealBody_eq_next D parts _ sent j hj hsome

/-- The normal form of `seedGenRest`, for each coalition, each adversary and each pattern of aborts. -/
theorem seedGenRest_eq_normal (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    seedGenRest D net state early parameter dealt parts =
      seedGenNormal D net state early parameter dealt parts :=
  (seedGenRest_eq_raw D net state early parameter dealt parts).trans
    (seedGenNormalWith_body_eq_next D net state early parameter dealt parts)

end Normal

/-! ## The addresses in the normal form -/

section Addresses

/-- The derive calls of operator `i` in the normal form. The call of a held term `T` asks
`termAddress D parts i inbox T`. -/
theorem deriveKeys_normView (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E) :
    deriveKeys .seedGen i (normView D parts i inbox) =
      hashQuery (.derive .seedGen .parameter (C.parties.map fun k => (normView D parts i inbox k).parameter)) >>=
        fun parameter =>
      C.terms.mapM (fun T => if i ∈ C.holders T then hashQuery (termAddress D parts i inbox T) else pure 0) >>=
        fun term =>
      C.parties.mapM (fun j => if h : j = i then pure 0 else
        hashQuery (.derive .seedGen .pair
          [(normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
            (normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) >>=
        fun pair =>
      pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun j => pair.getD j.val 0) := by
  simp only [deriveKeys, ↓reduceIte]
  rfl

/-- The derive address of a term with no corrupt holder is `hiddenInput parts T` at each operator. -/
theorem termAddress_hidden (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E)
    (T : C.Term) (hT : ¬ KnownTo D.1 T) : termAddress D parts i inbox T = hiddenInput parts T := by
  unfold termAddress hiddenInput
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hkT : k ∈ C.holders T := by simpa [seedGenHolderList] using (List.mem_filter.1 hk).2
  have hkD : k ∉ D.1 := fun h => hT ⟨k, h, hkT⟩
  simp [normView, hkD]

/-- The derive address of `T` reads the parts only at the term parts of `T` of its honest holders. -/
theorem termAddress_congr (D : C.Coalition) (parts parts' : C.Party → Parts C) (i : C.Party) (inbox : Mail C E)
    (T : C.Term) (h : ∀ k, k ∉ D.1 → k ∈ C.holders T → (parts k).term T = (parts' k).term T) :
    termAddress D parts i inbox T = termAddress D parts' i inbox T := by
  unfold termAddress
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hkT : k ∈ C.holders T := by simpa [seedGenHolderList] using (List.mem_filter.1 hk).2
  by_cases hkD : k ∈ D.1
  · simp [normView, hkD]
  · simp [normView, hkD, h k hkD hkT]

/-- The open address of an honest operator `i` for an honest sender `k ≠ i` is the commit address of
`k` for `i`. -/
theorem openAddress_honest (D : C.Coalition) (parts : C.Party → Parts C) (i k : C.Party) (inbox : Mail C E)
    (hk : k ∉ D.1) (hki : k ≠ i) : openAddress D parts i inbox k = commitAddress parts k i := by
  simp [openAddress, normRevealed, commitAddress, hk, revealOutbox, Ne.symm hki, Msg.hashesOf]

/-- The open address of an honest operator `i` for itself has the empty reveal. -/
theorem openAddress_self (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E)
    (hi : i ∉ D.1) : openAddress D parts i inbox i = .commit .seedGen i i [] := by
  simp [openAddress, normRevealed, hi, revealOutbox, Msg.hashesOf]

/-- The open address of a corrupt sender `k` reads only the inbox. -/
theorem openAddress_corrupt (D : C.Coalition) (parts : C.Party → Parts C) (i k : C.Party) (inbox : Mail C E)
    (hk : k ∈ D.1) : openAddress D parts i inbox k = .commit .seedGen k i (Msg.hashesOf (inbox k)) := by
  simp [openAddress, normRevealed, hk]

end Addresses

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.seedGenRest_eq_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.seedGenRest_eq_raw

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.seedGenRest_eq_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.seedGenRest_eq_normal
