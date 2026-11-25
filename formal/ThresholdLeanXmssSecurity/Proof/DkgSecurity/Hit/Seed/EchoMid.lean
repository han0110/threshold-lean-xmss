import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoInv
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.CountProgram

/-!
# `MidList` from the law of the block and the drop of free reads

* `passTwoList D j` is pass 2 of the list program. It asks no shared key cell for an operator with which
  `j` shares a hidden term. `localBlockList` is the block of round 2 of the list program, and
  `revealBlockList_eq` states that it is the block of `seedGenList` on the free copy.
* `zeroD D d` sets the shared key answers of the pairs with `SharesHidden` to `0`. `seedPost_zeroD` states
  that round 3 of the list program reads no such answer.
* `discards D d` asks the shared key cells of the pairs with `SharesHidden` and forgets the answers.
* `BlockLaw` states that the block of `midRun` with the answers set to `0` has the law of the block of the
  list program and then `discards`.
* `TailDrop` states that a free program with no stream call in front of a world program with no
  programming call can be dropped, for the result and the log.
* `midList_of_parts` gives `MidList` from `BlockLaw` and `TailDrop`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_map
  noCall_mono noCall_mapM noCall_sequenceFin noCall_query)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The list block -/

section ListBlock

variable {E : Type} (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
  (d : C.Party → Option Unit) (sent : C.Party → C.Party → Option (Msg E))

/-- Pass 2 of the list program. -/
def passTwoList (j : C.Party) :
    Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      OracleComp (LocalSpec C) (Option (SeedGenEchoData C))
  | none => pure none
  | some keys => liftComp (C.parties.mapM fun l => if SharesHidden D j l then pure 0 else
      hashQuery (sharedAddress j l keys.2.1)) (LocalSpec C) >>= fun sh => pure (some (keys, sh))

/-- The block of round 2 of the list program on the local oracles. -/
def localBlockList : OracleComp (LocalSpec C) (C.Party → Option (SeedGenEchoData C)) :=
  OverPermutation.sequenceFin fun j => passOne D parts committed d sent j >>= passTwoList D j

/-- The block of round 2 of the list program. -/
def revealBlockList : OracleComp (WorldSpec C) (C.Party → Option (SeedGenEchoData C)) :=
  OverPermutation.sequenceFin (fun j => if j ∈ D.1 then pure none else
    match d j with
    | none => pure none
    | some _ => if anyAbort (blockInbox D parts d sent j) then pure none else
        free (revealNextList D parts (fun _ _ keys => keys) committed j (blockInbox D parts d sent j)))

theorem revealBlockList_eq :
    revealBlockList D parts committed d sent = free (localBlockList D parts committed d sent) := by
  unfold revealBlockList localBlockList
  rw [free_sequenceFin]
  congr 1
  funext j
  by_cases hj : j ∈ D.1
  · simp [passOne, hj, passTwoList]
  rcases hd : d j with _ | u
  · simp [passOne, hj, hd, passTwoList]
  by_cases ha : anyAbort (blockInbox D parts d sent j) = true
  · simp [passOne, hj, hd, ha, passTwoList]
  simp only [passOne, hj, hd, ha, ite_false, Bool.false_eq_true, revealNextList, bind_assoc, free_bind]
  refine bind_congr fun opens => ?_
  split_ifs
  · simp only [free_bind, bind_assoc, free_pure, pure_bind, passTwoList]
  · simp only [free_pure, pure_bind, passTwoList]

/-- The answers of operator `j` with the answers of the pairs with `SharesHidden` set to `0`. -/
def zeroShared (j : C.Party) (x : SeedGenEchoData C) : SeedGenEchoData C :=
  (x.1, List.zipWith (fun l v => if SharesHidden D j l then 0 else v) C.parties x.2)

/-- The values of the operators with the answers of the pairs with `SharesHidden` set to `0`. -/
def zeroD (d' : C.Party → Option (SeedGenEchoData C)) : C.Party → Option (SeedGenEchoData C) :=
  fun j => (d' j).map (zeroShared D j)

/-- The shared key calls of the pairs with `SharesHidden`, with the answers forgotten. -/
def discards (d' : C.Party → Option (SeedGenEchoData C)) : OracleComp (LocalSpec C) Unit :=
  OverPermutation.sequenceFin (fun j => match d' j with
    | none => pure ()
    | some x => liftComp (C.parties.mapM fun l => if SharesHidden D j l then hashQuery (sharedAddress j l x.1.2.1)
        else pure 0) (LocalSpec C) >>= fun _ => pure ()) >>= fun _ => pure ()

end ListBlock

/-! ## Round 3 of the list program reads no answer of a pair with `SharesHidden` -/

section Zero

variable {E : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- A round with values changed by `g`, where the message and the local step read only the unchanged
part, is the same round. -/
theorem levelRound_map {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X) (g : C.Party → X → X)
    (out : C.Party → X → Mail C E) (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (hout : ∀ k x, out k (g k x) = out k x) (hnext : ∀ j x inbox, next j (g j x) inbox = next j x inbox) :
    levelRound D net fuel state (fun j => (d j).map (g j)) out next cont = levelRound D net fuel state d out next cont := by
  have hmail : levelMail D (fun j => (d j).map (g j)) out = levelMail D d out := by
    funext c i
    unfold levelMail
    split_ifs
    · dsimp only
      rcases d i with _ | x
      · rfl
      · simp only [Option.map_some, hout]
    · rfl
  have hinbox : ∀ sent j, levelInbox D (fun j => (d j).map (g j)) out sent j = levelInbox D d out sent j := by
    intro sent j
    funext k
    unfold levelInbox
    split_ifs
    · rfl
    · dsimp only
      rcases d k with _ | x
      · rfl
      · simp only [Option.map_some, hout]
  have hnone : ∀ i, (d i).map (g i) = none ↔ d i = none := fun i => Option.map_eq_none_iff
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [levelRound, hmail, hnone]
    by_cases h1 : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left h1, ite_eq_left h1]
    rw [ite_eq_right h1, ite_eq_right h1]
    refine bind_congr fun r => ?_
    by_cases h2 : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left h2, ite_eq_left h2]
    rw [ite_eq_right h2, ite_eq_right h2]
    congr 1
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true]
    simp only [hj, ite_false, hinbox]
    rcases d j with _ | x
    · rfl
    · simp only [Option.map_some, hnext]

theorem zeroShared_getD (j k : C.Party) (x : SeedGenEchoData C) (h : ¬ SharesHidden D j k) :
    (zeroShared D j x).2.getD k.val 0 = x.2.getD k.val 0 := by
  unfold zeroShared
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  have hk : C.parties[k.val]? = some k := by simp [Committee.parties]
  rw [hk]
  rcases x.2[k.val]? with _ | v
  · rfl
  · simp [h]

theorem outList_zeroShared (k : C.Party) (x : SeedGenEchoData C) :
    outList (E := E) D k (zeroShared D k x) = outList D k x := by
  funext j
  unfold outList
  by_cases h : j ≠ k ∧ SharesHidden D k j
  · simp only [h, ne_eq, not_false_eq_true, and_self, ite_true, echoList, zeroShared]
  · rw [ite_eq_right h, ite_eq_right h]
    unfold echoOutbox
    by_cases hjk : j = k
    · simp [hjk]
    · have hs : ¬ SharesHidden D k j := fun hs => h ⟨hjk, hs⟩
      simp only [hjk, ite_false, echoOf, zeroShared_getD D k j x hs]
      rfl

theorem echoNextList_zeroShared (j : C.Party) (x : SeedGenEchoData C) (inbox : Mail C E) :
    echoNextList D j (zeroShared D j x) inbox = echoNextList D j x inbox := by
  have h : echoListCheck D j (zeroShared D j x) inbox ↔ echoListCheck D j x inbox := by
    unfold echoListCheck
    refine forall_congr' fun k => imp_congr_right fun _ => ?_
    by_cases hs : SharesHidden D j k
    · simp only [hs, ite_true, echoList, zeroShared]
    · simp only [hs, ite_false, echoOf, zeroShared_getD D j k x hs]
      rfl
  unfold echoNextList
  rw [if_congr h rfl rfl]
  rfl

theorem seedPost_zeroD (fuel : ℕ) (state : net.State) (d' : C.Party → Option (SeedGenEchoData C)) :
    seedPost D net (outList D) (echoNextList D) (.inr (fuel, state, zeroD D d')) =
      seedPost D net (outList D) (echoNextList D) (.inr (fuel, state, d')) := by
  simp only [seedPost, Sum.elim_inr]
  exact levelRound_map D net fuel state d' (zeroShared D) _ _ _ (outList_zeroShared D)
    (echoNextList_zeroShared D)

end Zero

/-! ## The list run in parts -/

section ListParts

variable {E : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The rest of the seed generation of the list program after the head, to the end of round 2. -/
def blockStepList (parts : C.Party → Parts C) : (net.State × (C.Party → Option (Keys C))) ⊕ BlockIn C E net.State →
    OracleComp (WorldSpec C) (EchoPoint C net.State)
  | .inl e => pure (.inl e)
  | .inr b => revealBlockList D parts b.2.2.1 (revealReady b.2.2.1) b.2.2.2 >>= fun d' => pure (.inr (b.1, b.2.1, d'))

theorem seedGenList_head_split (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    seedGenList D net state early parameter dealt parts (fun _ _ keys => keys) =
      seedHead D net state early parameter dealt parts >>= fun h => blockStepList D net parts h >>=
        seedPost D net (outList D) (echoNextList D) := by
  unfold seedGenList seedHead
  simp only [bind_assoc]
  refine bind_congr fun commitments => bind_congr fun r => bind_congr fun _ => ?_
  rw [show setupRounds - 1 = (setupRounds - 2) + 1 from rfl]
  simp only [levelRound]
  by_cases h1 : ∀ i, i ∉ D.1 → revealReady (commitInbox D commitments r.1.2) i = none
  · rw [ite_eq_left h1, ite_eq_left h1, pure_bind]
    rfl
  · rw [ite_eq_right h1, ite_eq_right h1, bind_assoc]
    refine bind_congr fun r2 => ?_
    by_cases h2 : ∃ i, i ∉ D.1 ∧ revealReady (commitInbox D commitments r.1.2) i = none
    · rw [ite_eq_left h2, ite_eq_left h2, pure_bind]
      rfl
    · rw [ite_eq_right h2, ite_eq_right h2, pure_bind]
      simp only [blockStepList, revealBlockList, bind_assoc, pure_bind]
      congr 1
      congr 1
      funext j
      by_cases hj : j ∈ D.1
      · simp only [hj, ite_true]
      · simp only [hj, ite_false]
        rcases revealReady (commitInbox D commitments r.1.2) j with _ | u <;> rfl

end ListParts

section ListSuffix

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
theorem listSuffix_head_split (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) :
    listSuffix K circuits settings runLimit D A x (fun _ _ keys => keys) =
      seedHead D A.net x.1.1 x.1.2 x.2.1.1 x.2.1.2.2 x.2.2 >>= fun h => blockStepList D A.net x.2.2 h >>= fun e =>
        seedPost D A.net (outList D) (echoNextList D) e >>= restOf K circuits settings runLimit D A x := by
  unfold listSuffix
  rw [seedGenList_head_split]
  simp only [bind_assoc]
  rfl

end ListSuffix

/-! ## The calls of the list block and of round 3 -/

section Calls

open ThresholdLeanXmssSecurity.DkgCorrectnessProof.Collision (noProgram_adversary noProgram_free)

variable {E : Type} (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
  (d : C.Party → Option Unit) (sent : C.Party → C.Party → Option (Msg E))

theorem passTwoList_noStream (j : C.Party) (k : Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))) :
    AllQueriesSatisfy (passTwoList D j k) NoStream := by
  rcases k with _ | keys
  · exact allQueriesSatisfy_pure _ _
  · refine allQueriesSatisfy_bind ((avoid_liftComp (fun _ => False) _ (avoid_mapM _ _ (fun l => ?_) _)).mono
      fun t ht => noStream_of_avoid _ t ht) fun _ => allQueriesSatisfy_pure _ _
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact avoid_hashQuery _ _ id

theorem discards_noStream (d' : C.Party → Option (SeedGenEchoData C)) :
    AllQueriesSatisfy (discards D d') NoStream := by
  unfold discards
  refine allQueriesSatisfy_bind (avoid_sequenceFin _ _ fun j => ?_) fun _ => allQueriesSatisfy_pure _ _
  split
  · exact allQueriesSatisfy_pure _ _
  · refine allQueriesSatisfy_bind ((avoid_liftComp (fun _ => False) _ (avoid_mapM _ _ (fun l => ?_) _)).mono
      fun t ht => noStream_of_avoid _ t ht) fun _ => allQueriesSatisfy_pure _ _
    split_ifs
    · exact avoid_hashQuery _ _ id
    · exact allQueriesSatisfy_pure _ _

theorem localBlockList_noStream : AllQueriesSatisfy (localBlockList D parts committed d sent) NoStream := by
  unfold localBlockList
  refine avoid_sequenceFin _ _ fun j => allQueriesSatisfy_bind ?_ fun k => passTwoList_noStream D j k
  exact (passOne_avoid D parts committed d sent j).mono fun t ht => noStream_of_avoid _ t ht

theorem noProgram_levelRound (net : Adversary C E Unit PEmpty PEmpty) {X Y β : Type} (fuel : ℕ) (state : net.State)
    (d' : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (hcont : ∀ f s d'', NoCall WorldProgramQuery (cont f s d'')) :
    NoCall WorldProgramQuery (levelRound D net fuel state d' out next cont) := by
  cases fuel with
  | zero => exact noCall_pure _ _
  | succ fuel =>
    simp only [levelRound]
    by_cases h1 : ∀ i, i ∉ D.1 → d' i = none
    · rw [ite_eq_left h1]
      exact noCall_pure _ _
    rw [ite_eq_right h1]
    refine noCall_bind _ (noProgram_adversary _) fun r => ?_
    by_cases h2 : ∃ i, i ∉ D.1 ∧ d' i = none
    · rw [ite_eq_left h2]
      exact noCall_pure _ _
    rw [ite_eq_right h2]
    refine noCall_bind _ (noCall_sequenceFin _ _ fun j => ?_) fun _ => hcont _ _ _
    by_cases hj : j ∈ D.1
    · rw [ite_eq_left hj]
      exact noCall_pure _ _
    rw [ite_eq_right hj]
    rcases d' j with _ | x
    · exact noCall_pure _ _
    · dsimp only
      by_cases ha : anyAbort (levelInbox D d' out r.2 j) = true
      · rw [ite_eq_left ha]
        exact noCall_pure _ _
      · rw [ite_eq_right ha]
        exact noProgram_free _

end Calls

section Statements

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
theorem noProgram_tail (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (e : EchoPoint C A.net.State) :
    NoCall WorldProgramQuery (seedPost D A.net (outList D) (echoNextList D) e >>= restOf K circuits settings runLimit D A x) := by
  refine noCall_bind _ ?_ fun y => ?_
  · rcases e with y | ⟨f, st, d'⟩
    · exact noCall_pure _ _
    · simp only [seedPost, Sum.elim_inr]
      exact noProgram_levelRound D A.net f st d' _ _ _ fun _ _ _ => noCall_pure _ _
  · unfold restOf
    refine noCall_bind _ (noCall_map _ _ ?_) fun _ => noCall_pure _ _
    exact DkgSecurityProof.noProg_secRest K circuits settings runLimit D _ (fun _ => rfl) A x.2.1.1 x.2.1.2.1
      x.2.1.2.2 y.2 _

/-- The block of `midRun` with the answers of the pairs with `SharesHidden` set to `0` has the law of the
block of the list program and then `discards`, for the result and the cache, from each cache. All calls
are calls of one lazy random oracle, so they commute. -/
def BlockLaw : Prop :=
  ∀ (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) (committed : C.Party → Mail C E)
    (d : C.Party → Option Unit) (sent : C.Party → C.Party → Option (Msg E)) (c : HashCache C),
    (fun r => (zeroD D r.1, r.2)) <$> (simulateQ (compLocal prims D parts seed) (localBlock D parts committed d sent)).run c =ᵈ
      (simulateQ (compLocal prims D parts seed)
        (localBlockList D parts committed d sent >>= fun d' => discards D d' >>= fun _ => pure d')).run c

/-- A free program with no stream call in front of a world program with no programming call can be
dropped, for the result and the log, from each state. The free program changes only the cache. Each of its
calls commutes with each call of the world program, so it moves to the end. -/
def TailDrop : Prop :=
  ∀ (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) {α β : Type}
    (X : OracleComp (LocalSpec C) β), AllQueriesSatisfy X NoStream →
    ∀ (T : OracleComp (WorldSpec C) α), NoCall WorldProgramQuery T → ∀ s : LogState C,
      (fun z => (z.1, z.2.2)) <$> (simulateQ (compWorld prims D parts seed) (free X >>= fun _ => T)).run s =ᵈ
        (fun z => (z.1, z.2.2)) <$> (simulateQ (compWorld prims D parts seed) T).run s

omit [Fintype E] [DecidableEq E] in
/-- The rest after the head for one end `h` of the head. The middle run and the list run give one law of
the log. -/
theorem tail_eq (block : BlockLaw (C := C) (E := E) prims) (tail : TailDrop (C := C) prims) (D : C.Coalition)
    (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) (seed : C.Term → HashOutput)
    (h : (A.net.State × (C.Party → Option (Keys C))) ⊕ BlockIn C E A.net.State) (s : LogState C) :
    (fun z => z.2.2) <$> (simulateQ (compWorld prims D x.2.2 seed) (blockStep D A.net x.2.2 h >>= fun e =>
      seedPost D A.net (outList D) (echoNextList D) e >>= restOf K circuits settings runLimit D A x)).run s =ᵈ
    (fun z => z.2.2) <$> (simulateQ (compWorld prims D x.2.2 seed) (blockStepList D A.net x.2.2 h >>= fun e =>
      seedPost D A.net (outList D) (echoNextList D) e >>= restOf K circuits settings runLimit D A x)).run s := by
  rcases h with e | b
  · exact EvalDistEq.rfl
  let T : (C.Party → Option (SeedGenEchoData C)) → OracleComp (WorldSpec C) (RunOut C) := fun d' =>
    seedPost D A.net (outList D) (echoNextList D) (.inr (b.1, b.2.1, d')) >>= restOf K circuits settings runLimit D A x
  let M := localBlock D x.2.2 b.2.2.1 (revealReady b.2.2.1) b.2.2.2
  let Lb := localBlockList D x.2.2 b.2.2.1 (revealReady b.2.2.1) b.2.2.2
  have hmid : (blockStep D A.net x.2.2 (.inr b) >>= fun e => seedPost D A.net (outList D) (echoNextList D) e >>=
      restOf K circuits settings runLimit D A x) = free M >>= fun d' => T (zeroD D d') := by
    simp only [blockStep, bind_assoc, pure_bind, revealBlock_eq, T, M, seedPost_zeroD]
  have hlist : (blockStepList D A.net x.2.2 (.inr b) >>= fun e => seedPost D A.net (outList D) (echoNextList D) e >>=
      restOf K circuits settings runLimit D A x) = free Lb >>= T := by
    simp only [blockStepList, bind_assoc, pure_bind, revealBlockList_eq, T, Lb]
  have hdisc : (free (Lb >>= fun d' => discards D d' >>= fun _ => pure d') >>= T) =
      free Lb >>= fun d' => free (discards D d') >>= fun _ => T d' := by
    simp only [free_bind, bind_assoc, free_pure, pure_bind]
  have hnsM : AllQueriesSatisfy M NoStream := localBlock_noStream _ _ _ _ _
  have hnsL : AllQueriesSatisfy (Lb >>= fun d' => discards D d' >>= fun _ => pure d') NoStream :=
    allQueriesSatisfy_bind (localBlockList_noStream _ _ _ _ _) fun d' =>
      allQueriesSatisfy_bind (discards_noStream D d') fun _ => allQueriesSatisfy_pure _ _
  rw [hmid, hlist]
  calc (fun z => z.2.2) <$> (simulateQ (compWorld prims D x.2.2 seed) (free M >>= fun d' => T (zeroD D d'))).run s
      = (fun z => z.2.2) <$> (((fun r => (zeroD D r.1, r.2)) <$>
          (simulateQ (compLocal prims D x.2.2 seed) M).run s.1.1) >>= fun r =>
            (simulateQ (compWorld prims D x.2.2 seed) (T r.1)).run ((r.2, s.1.2), s.2)) := by
        rw [simulateQ_bind, StateT.run_bind, compWorld_free_run prims D x.2.2 seed M hnsM s, bind_map_left,
          bind_map_left]
    _ =ᵈ (fun z => z.2.2) <$> ((simulateQ (compLocal prims D x.2.2 seed)
          (Lb >>= fun d' => discards D d' >>= fun _ => pure d')).run s.1.1 >>= fun r =>
            (simulateQ (compWorld prims D x.2.2 seed) (T r.1)).run ((r.2, s.1.2), s.2)) :=
        EvalDistEq.map_congr _ ((block D x.2.2 seed b.2.2.1 (revealReady b.2.2.1) b.2.2.2 s.1.1).bind_left _)
    _ = (fun z => z.2.2) <$> (simulateQ (compWorld prims D x.2.2 seed)
          (free (Lb >>= fun d' => discards D d' >>= fun _ => pure d') >>= T)).run s := by
        conv_rhs => rw [simulateQ_bind, StateT.run_bind, compWorld_free_run prims D x.2.2 seed _ hnsL s, bind_map_left]
    _ = (fun z => z.2.2) <$> ((simulateQ (compWorld prims D x.2.2 seed) (free Lb)).run s >>= fun p =>
          (simulateQ (compWorld prims D x.2.2 seed) (free (discards D p.1) >>= fun _ => T p.1)).run p.2) := by
        rw [hdisc, simulateQ_bind, StateT.run_bind]
    _ =ᵈ (fun z => z.2.2) <$> ((simulateQ (compWorld prims D x.2.2 seed) (free Lb)).run s >>= fun p =>
          (simulateQ (compWorld prims D x.2.2 seed) (T p.1)).run p.2) := by
        simp only [map_bind]
        refine EvalDistEq.bind_right _ fun p => ?_
        have ht := tail D x.2.2 seed (discards D p.1) (discards_noStream D p.1) (T p.1)
          (noProgram_tail K circuits settings runLimit D A x _) p.2
        have e1 : ∀ (m : ProbComp (RunOut C × LogState C)),
            (fun z => z.2.2) <$> m = (fun w => w.2) <$> ((fun z => (z.1, z.2.2)) <$> m) := fun m => by
          rw [Functor.map_map]
        rw [e1, e1]
        exact EvalDistEq.map_congr _ ht
    _ = (fun z => z.2.2) <$> (simulateQ (compWorld prims D x.2.2 seed) (free Lb >>= T)).run s := by
        rw [simulateQ_bind, StateT.run_bind]

omit [Fintype E] [DecidableEq E] in
/-- `BlockLaw` and `TailDrop` give `MidList`. -/
theorem midList_of_parts (block : BlockLaw (C := C) (E := E) prims) (tail : TailDrop (C := C) prims) :
    MidList prims K circuits settings runLimit := by
  intro D A
  unfold midRun listRun listRunWith
  rw [preRun_split]
  simp only [headRun, postRun, listSuffix_head_split, bind_assoc, pure_bind, map_bind, map_pure, simulateQ_bind,
    StateT.run_bind, id]
  refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun seed => EvalDistEq.bind_right _ fun h => ?_
  have ht := tail_eq prims K circuits settings runLimit block tail D A x.1 seed h.1 h.2
  simp only [simulateQ_bind, StateT.run_bind, map_bind] at ht
  have e2 : ∀ (m : ProbComp (RunOut C × LogState C)),
      (m >>= fun z => (pure (x.1.2.2, seed, z.2.2) : ProbComp _)) =
        (fun w => (x.1.2.2, seed, w)) <$> ((fun z => z.2.2) <$> m) := fun m => by
    simp only [Functor.map_map, bind_pure_comp]
  simp only [e2]
  simp only [← map_bind]
  simp only [← map_bind] at ht
  exact EvalDistEq.map_congr _ ht

end Statements

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.midList_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.midList_of_parts
