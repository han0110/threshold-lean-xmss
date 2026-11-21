import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.ListShiftStep

/-!
# The shift of the held hidden seeds does not change the list run

`listSafe` proves `ListSafe`. With `δ` added to the seed of each held hidden term, the list program
asks the same cells and the adversary reads the same mail.

* A shared key call of operator `i` for an operator `j` with no `SharesHidden D i j` reads only seeds
  of known terms (`known_of_not_sharesHidden`).
* The echo to a corrupt operator reads only the key of `P` and the shared key hashes.
* The list test of two honest operators with a shared hidden term compares two lists with `δ` added
  at the same positions (`echoListCheck_safe`).
* The output keys change only in their values. The rest of the game reads only which operators have
  keys (`secRest_emu_eq`, `startState`).

`levelRound_map_next`, `levelRound_map_values` and `levelRound_map_result` move a map on the result
of a local step, on the values of the operators, and on the result of a round.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## Maps through a round -/

section Level

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- A map on the result of the local step moves into the rest of the phase. -/
theorem levelRound_map_next {X Y Z β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (g : C.Party → Y → Z)
    (cont : ℕ → net.State → (C.Party → Option Z) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    levelRound D net fuel state d out (fun j x inbox => Option.map (g j) <$> next j x inbox) cont =
      levelRound D net fuel state d out next (fun f s d' => cont f s (fun j => (d' j).map (g j))) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [levelRound_succ, levelRound_succ]
    split_ifs
    · rfl
    refine bind_congr fun r => ?_
    unfold levelTail
    split_ifs
    · rfl
    have h : OverPermutation.sequenceFin (fun j => if j ∈ D.1 then pure none else
        match d j with
        | none => pure none
        | some x => if anyAbort (levelInbox D d out r.2 j) then pure none else
            free (Option.map (g j) <$> next j x (levelInbox D d out r.2 j))) =
        OverPermutation.sequenceFin (fun j => (if j ∈ D.1 then pure none else
          match d j with
          | none => pure none
          | some x => if anyAbort (levelInbox D d out r.2 j) then pure none else
              free (next j x (levelInbox D d out r.2 j))) >>= fun y => pure (y.map (g j))) := by
      congr 1
      funext j
      by_cases hj : j ∈ D.1
      · simp [hj]
      · simp only [hj, ite_false]
        rcases d j with _ | x
        · simp
        · dsimp only
          split_ifs
          · simp
          · rw [map_eq_bind_pure_comp]
            simp only [free, simulateQ_bind, simulateQ_pure, Function.comp_def]
    refine Eq.trans (congrArg (fun m => m >>= cont fuel r.1) h) ?_
    rw [sequenceFin_bind_pure, bind_assoc]
    simp only [pure_bind]
    rfl

/-- Values mapped for each operator move into the messages and the local steps. -/
theorem levelRound_map_values {X X' Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (g : C.Party → X → X') (out : C.Party → X' → Mail C E)
    (next : C.Party → X' → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    levelRound D net fuel state (fun j => (d j).map (g j)) out next cont =
      levelRound D net fuel state d (fun i x => out i (g i x)) (fun j x inbox => next j (g j x) inbox) cont := by
  have hmail : levelMail D (fun j => (d j).map (g j)) out = levelMail D d (fun i x => out i (g i x)) := by
    funext c i
    unfold levelMail
    split_ifs
    · beta_reduce
      rcases d i with _ | x <;> rfl
    · rfl
  have hinbox : ∀ sent, levelInbox D (fun j => (d j).map (g j)) out sent =
      levelInbox D d (fun i x => out i (g i x)) sent := by
    intro sent
    funext j k
    unfold levelInbox
    split_ifs
    · rfl
    · beta_reduce
      rcases d k with _ | x <;> rfl
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [levelRound_succ, levelRound_succ, hmail]
    simp only [Option.map_eq_none_iff]
    split_ifs
    · rfl
    refine bind_congr fun r => ?_
    unfold levelTail
    simp only [Option.map_eq_none_iff, hinbox]
    split_ifs
    · rfl
    congr 1
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true]
    · simp only [hj, ite_false]
      rcases d j with _ | x <;> rfl

/-- A map on the result of a round moves into the rest of the phase, if it keeps an empty result. -/
theorem levelRound_map_result {X Y β β' : Type} (F : net.State × (C.Party → Option β) → net.State × (C.Party → Option β'))
    (hF : ∀ s, F (s, fun _ => none) = (s, fun _ => none)) (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    F <$> levelRound D net fuel state d out next cont =
      levelRound D net fuel state d out next (fun f s d' => F <$> cont f s d') := by
  cases fuel with
  | zero => simp [levelRound, hF]
  | succ fuel =>
    rw [levelRound_succ, levelRound_succ]
    split_ifs
    · simp [hF]
    rw [map_bind]
    refine bind_congr fun r => ?_
    unfold levelTail
    split_ifs
    · simp [hF]
    rw [map_bind]

end Level

/-! ## The local steps -/

section Steps

variable (D : C.Coalition) (δ : HashOutput)

/-- The values of operator `i` after round 2 with `δ` added to the seed of each held hidden term. -/
def safeData (i : C.Party) (x : SeedGenEchoData C) : SeedGenEchoData C := (shiftKeysSafe D δ i x.1, x.2)

/-- The keys of operator `i` with `δ` added to the seed of each held hidden term. -/
def keysSafe (i : C.Party) (k : Keys C) : Keys C :=
  ⟨k.parameter, fun T => if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then k.seed T ^^^ δ else k.seed T, k.pairKey⟩

theorem mem_sharedTerms {i j : C.Party} {T : C.Term} (h : T ∈ sharedTerms i j) : i ∈ C.holders T ∧ j ∈ C.holders T := by
  unfold sharedTerms at h
  simpa using (List.mem_filter.1 h).2

theorem known_of_not_sharesHidden {i j : C.Party} (h : ¬ SharesHidden D i j) {T : C.Term} (hT : T ∈ sharedTerms i j) :
    KnownTo D.1 T := by
  by_cases hj : j ∈ D.1
  · exact ⟨j, hj, (mem_sharedTerms hT).2⟩
  · by_contra hk
    exact h ⟨hj, T, hT, hk⟩

theorem sharesHidden_comm {i j : C.Party} (hi : i ∉ D.1) (hj : j ∉ D.1) : SharesHidden D i j ↔ SharesHidden D j i := by
  unfold SharesHidden
  rw [sharedTerms_comm i j]
  simp [hi, hj]

theorem revealNextList_safe (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (i : C.Party)
    (inbox : Mail C E) :
    revealNextList D parts (fun i _ => shiftKeysSafe D δ i) committed i inbox =
      Option.map (safeData D δ i) <$> revealNextList D parts (fun _ _ keys => keys) committed i inbox := by
  unfold revealNextList
  rw [map_bind]
  refine bind_congr fun opens => ?_
  split_ifs
  · rw [map_bind]
    refine bind_congr fun keys => ?_
    have hs : (fun j => if SharesHidden D i j then (pure 0 : OracleComp (RoSpec C) HashOutput) else
        hashQuery (sharedAddress i j (shiftKeysSafe D δ i keys).2.1)) =
        fun j => if SharesHidden D i j then (pure 0 : OracleComp (RoSpec C) HashOutput) else
          hashQuery (sharedAddress i j keys.2.1) := by
      funext j
      split_ifs with hj
      · rfl
      · unfold sharedAddress
        congr 2
        refine List.map_congr_left fun T hT => ?_
        have hk := known_of_not_sharesHidden D hj hT
        simp [shiftKeysSafe, hk]
    simp only [hs, map_bind, map_pure, Option.map_some]
    rfl
  · simp

theorem xor_right_inj (a b δ : HashOutput) : a ^^^ δ = b ^^^ δ ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· ^^^ δ) h
    simpa [BitVec.xor_assoc] using this
  · rintro rfl
    rfl

/-- The list test of an honest operator does not change when each honest operator adds `δ` to the
seed of each held hidden term. -/
theorem echoListCheck_safe (d : C.Party → Option (SeedGenEchoData C)) (sent : C.Party → C.Party → Option (Msg E))
    (j : C.Party) (hj : j ∉ D.1) (x : SeedGenEchoData C) :
    echoListCheck D j (safeData D δ j x) (levelInbox D d (fun i y => outList D i (safeData D δ i y)) sent j) ↔
      echoListCheck D j x (levelInbox D d (outList D) sent j) := by
  unfold echoListCheck
  refine forall_congr' fun k => imp_congr_right fun hkj => ?_
  unfold levelInbox
  by_cases hk : k ∈ D.1
  · have hs : ¬ SharesHidden D j k := fun h => h.1 hk
    simp only [hk, ite_true, hs, ite_false]
    rfl
  · simp only [hk, ite_false]
    rcases d k with _ | xk
    · dsimp only
      split_ifs
      · simp [echoList, Msg.hashesOf]
      · rfl
    · dsimp only
      unfold outList
      have hjk : j ≠ k := fun e => hkj e.symm
      by_cases hs : SharesHidden D j k
      · have hs' : SharesHidden D k j := (sharesHidden_comm D hj hk).1 hs
        simp only [hjk, ne_eq, not_false_eq_true, hs', and_self, ite_true, hs, Msg.hashesOf]
        unfold echoList safeData shiftKeysSafe
        rw [sharedTerms_comm k j]
        simp only [List.cons.injEq]
        refine and_congr_right fun _ => ?_
        rw [List.map_inj_left, List.map_inj_left]
        refine forall_congr' fun T => imp_congr_right fun hT => ?_
        have hh := mem_sharedTerms hT
        by_cases hK : KnownTo D.1 T
        · simp [hK]
        · simp only [hh.1, hh.2, hK, not_false_eq_true, and_self, ite_true]
          exact xor_right_inj _ _ _
      · have hs' : ¬ SharesHidden D k j := fun h => hs ((sharesHidden_comm D hk hj).1 h)
        simp only [hs', and_false, ite_false, hs]
        rfl

end Steps

/-! ## The seed generation and the runs -/

section Runs

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The seed generation of the list program with `shiftKeysSafe` is the seed generation of the list
program with the output keys changed by `keysSafe`. -/
theorem seedGenList_safe (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (δ : HashOutput) :
    seedGenList D net state early parameter dealt parts (fun i _ => shiftKeysSafe D δ i) =
      (fun p => (p.1, fun j => (p.2 j).map (keysSafe D δ j))) <$>
        seedGenList D net state early parameter dealt parts (fun _ _ keys => keys) := by
  have hF : ∀ s : net.State, ((fun p : net.State × (C.Party → Option (Keys C)) =>
      (p.1, fun j => (p.2 j).map (keysSafe D δ j))) (s, fun _ => none)) = (s, fun _ => none) := fun _ => rfl
  unfold seedGenList
  simp only [map_bind]
  refine bind_congr fun commitments => bind_congr fun r => bind_congr fun _ => ?_
  have hnext : (fun i (_ : Unit) inbox => revealNextList D parts (fun i _ => shiftKeysSafe D δ i)
      (commitInbox D commitments r.1.2) i inbox) = fun i _ inbox =>
        Option.map (safeData D δ i) <$> revealNextList D parts (fun _ _ keys => keys) (commitInbox D commitments r.1.2) i inbox := by
    funext i u inbox
    exact revealNextList_safe D δ parts _ i inbox
  rw [hnext, levelRound_map_next, levelRound_map_result D net _ hF]
  refine levelRound_congr D net _ _ _ _ _ _ _ fun f2 s2 d2 => ?_
  rw [levelRound_map_values, levelRound_map_result D net _ hF]
  rw [levelRound_congr_out D net _ _ _ _ (outList D) _ (fun j x inbox => Option.map (keysSafe D δ j) <$> echoNextList D j x inbox)
    _ (fun c i x hc hi => ?_) (fun k x j => ?_) (fun sent j x hj _ => ?_)]
  · rw [levelRound_map_next]
    refine levelRound_congr D net _ _ _ _ _ _ _ fun f3 s3 d3 => ?_
    simp only [map_pure]
    congr 2
    funext j
    split_ifs <;> rfl
  · have hs : ¬ SharesHidden D i c := fun h => h.1 hc
    simp only [outList, hs, and_false, ite_false]
    rfl
  · unfold outList echoOutbox
    split_ifs <;> rfl
  · unfold echoNextList
    rw [map_pure]
    congr 1
    by_cases hc : echoListCheck D j x (levelInbox D d2 (outList D) sent j)
    · have hc' := (echoListCheck_safe D δ d2 sent j hj x).2 hc
      simp only [hc, hc', ↓reduceIte, Option.map_some]
      rfl
    · have hc' : ¬ echoListCheck D j (safeData D δ j x) (levelInbox D d2 (fun i y => outList D i (safeData D δ i y))
          sent j) := fun h => hc ((echoListCheck_safe D δ d2 sent j hj x).1 h)
      simp only [hc, hc', ↓reduceIte, Option.map_none]

omit [Fintype E] [DecidableEq E] in
theorem listSuffix_safe (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) (δ : HashOutput) :
    listSuffix K circuits settings runLimit D A x (fun i _ => shiftKeysSafe D δ i) =
      (fun o : RunOut C => (o.1, o.2.1, o.2.2.1, o.2.2.2.1, fun j => (o.2.2.2.2 j).map (keysSafe D δ j))) <$>
        listSuffix K circuits settings runLimit D A x (fun _ _ keys => keys) := by
  unfold listSuffix
  rw [seedGenList_safe, bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  rcases p with ⟨state, emu⟩
  dsimp only
  have hkeys : (fun i => ((emu i).map (keysSafe D δ i)).map fun _ => x.2.1.2.2 i) =
      fun i => (emu i).map fun _ => x.2.1.2.2 i := by
    funext i
    rw [Option.map_map]
    rfl
  rw [hkeys, secRest_emu_eq K circuits settings runLimit D _ (fun _ => rfl) x.2.1.1 x.2.1.2.1 x.2.1.2.2 A _ emu,
    map_bind]
  refine bind_congr fun win => ?_
  rw [map_pure]

omit [Fintype E] [DecidableEq E] in
/-- The proof of `ListSafe`. -/
theorem listSafe : ListSafe prims K circuits settings runLimit := by
  intro D A δ
  unfold listRun listRunWith
  refine bind_congr fun x => bind_congr fun seed => ?_
  rw [listSuffix_safe, simulateQ_map, StateT.run_map, bind_map_left]

omit [Fintype E] [DecidableEq E] in
/-- `ListAliasBound` gives `ListShiftStep`. -/
theorem listShiftStep_of_alias (bound : ListAliasBound (C := C) (E := E) prims) :
    ListShiftStep prims K circuits settings runLimit :=
  listShiftStep_of_parts prims K circuits settings runLimit bound (listSafe prims K circuits settings runLimit)

end Runs

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listSafe

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listShiftStep_of_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listShiftStep_of_alias
