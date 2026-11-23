import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.ListShift

/-!
# The step of the common shift up to an alias

`ListShiftStep` compares the list program with the keys shifted by `shiftKeysHidden` and the list
program. The proof splits the seed generation of the list program at the call of the adversary in
round 2 (`seedGenList_split`).

* `listPre` is the part before that call, with the call. Its result `ListMid` holds the commitments,
  the result of round 1 and the result of the call of round 2, if the round takes place.
* `MidAlias D net parts w` states that an honest operator `j` holds a known term `T` whose derive
  address at the inbox of round 2 is a hidden cell. This is the alias.
* `shiftKeysSafe D δ i` adds `δ` to the seed of each held hidden term. Off the alias,
  `shiftKeysHidden` at the inbox of round 2 is `shiftKeysSafe` (`listPost_agree`).
* `listRun_alias_le` bounds an event of the shifted run by the probability of the alias in
  `listMidRun` and the probability of the event in the run with `shiftKeysSafe`.
* `ListAliasBound` states the bound `aliasCost D` of the alias. `ListSafe` states that the run with
  `shiftKeysSafe` is the list run. `listShiftStep_of_parts` gives `ListShiftStep` from the two.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## An event after a bind -/

/-- Two continuations that agree off the event `bad` of the first part give probabilities of an event
that differ by at most the probability of `bad`. -/
theorem prEvent_bind_le_add_of_agree {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β) (bad : α → Prop)
    (event : β → Prop) (h : ∀ a ∈ support oa, ¬ bad a → f a = g a) :
    Pr{let y ← oa >>= f}[event y] ≤ Pr{let a ← oa}[bad a] + Pr{let y ← oa >>= g}[event y] := by
  have hbad : Pr{let a ← oa}[bad a] = ∑' x, Pr{let z ← oa}[z = x] * Pr{let a ← (pure x : ProbComp α)}[bad a] := by
    rw [← prEvent_bind_eq_tsum, bind_pure]
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, hbad, ← tsum_add]
  refine tsum_le_tsum fun x => ?_
  rw [← mul_add]
  by_cases hx : x ∈ support oa
  · by_cases hb : bad x
    · gcongr
      have h1 : Pr{let a ← (pure x : ProbComp α)}[bad a] = 1 := by simp [hb]
      rw [h1]
      exact le_add_right (prEvent_le_one _)
    · rw [h x hx hb]
      gcongr
      exact le_add_self
  · simp [prEvent_eq_zero_of_not_mem_support oa hx]

/-! ## The head and the tail of a round -/

section Level

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The part of a round after the call of the adversary with the result `r`. -/
def levelTail {X Y β : Type} (fuel : ℕ) (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (r : net.State × (C.Party → C.Party → Option (Msg E))) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option β)) :=
  if ∃ i, i ∉ D.1 ∧ d i = none then pure (r.1, fun _ => none) else
  OverPermutation.sequenceFin (fun j => if j ∈ D.1 then pure none else
    match d j with
    | none => pure none
    | some x => if anyAbort (levelInbox D d out r.2 j) then pure none else
        free (next j x (levelInbox D d out r.2 j))) >>= cont fuel r.1

theorem levelRound_succ {X Y β : Type} (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    levelRound D net (fuel + 1) state d out next cont =
      if ∀ i, i ∉ D.1 → d i = none then pure (state, fun _ => none) else
      counted (liftComp (net.round state (levelMail D d out)) _) >>= levelTail D net fuel d out next cont :=
  rfl

end Level

/-! ## The split of the list program at round 2 -/

section Split

/-- The result of the list program before the local steps of round 2. The commitments, the result of
round 1 with its log, and the result of the call of round 2 if the round takes place. -/
abbrev ListMid (C : Committee) (E σ : Type) :=
  (C.Party → List HashOutput) × ((σ × (C.Party → C.Party → Option (Msg E))) × CallLog C) ×
    Option (σ × (C.Party → C.Party → Option (Msg E)))

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The list program up to the call of the adversary in round 2. -/
def listPre (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) : OracleComp (WorldSpec C) (ListMid C E net.State) :=
  commitDraws D parts >>= fun commitments =>
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  if ∀ i, i ∉ D.1 → revealReady (commitInbox D commitments r.1.2) i = none then pure (commitments, r, none) else
  counted (liftComp (net.round r.1.1 (levelMail D (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i)))) _) >>= fun r2 => pure (commitments, r, some r2)

/-- The list program after the call of the adversary in round 2, with the change `adj` of the keys. -/
def listPost (parts : C.Party → Parts C)
    (adj : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (w : ListMid C E net.State) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) :=
  match w.2.2 with
  | none => pure (w.2.1.1.1, fun _ => none)
  | some r2 =>
    levelTail D net 1 (revealReady (commitInbox D w.1 w.2.1.1.2)) (fun i _ => revealOutbox .seedGen i (parts i))
      (fun i _ inbox => revealNextList D parts adj (commitInbox D w.1 w.2.1.1.2) i inbox)
      (fun f2 s2 d2 => levelRound D net f2 s2 d2 (outList D) (echoNextList D) fun _ s3 d3 =>
        pure (s3, fun j => if j ∈ D.1 then none else d3 j)) r2

theorem seedGenList_split (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (adj : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    seedGenList D net state early parameter dealt parts adj =
      listPre D net state early parameter dealt parts >>= listPost D net parts adj := by
  unfold seedGenList listPre
  simp only [bind_assoc]
  refine bind_congr fun commitments => bind_congr fun r => bind_congr fun _ => ?_
  rw [show setupRounds - 1 = 1 + 1 from rfl, levelRound_succ]
  split_ifs
  · rw [pure_bind]
    rfl
  · simp only [bind_assoc, pure_bind]
    rfl

/-- The alias. An honest operator `j` holds a known term `T` whose derive address at its inbox of
round 2 is a hidden cell. -/
def MidAlias (parts : C.Party → Parts C) (w : ListMid C E net.State) : Prop :=
  match w.2.2 with
  | none => False
  | some r2 => ∃ j, j ∉ D.1 ∧ ∃ T, KnownTo D.1 T ∧ j ∈ C.holders T ∧
      HiddenCell D parts (termAddress D parts j (levelInbox D (revealReady (commitInbox D w.1 w.2.1.1.2))
        (fun i _ => revealOutbox .seedGen i (parts i)) r2.2 j) T)

/-- The keys of operator `i` with `δ` added to the seed of each held hidden term. -/
def shiftKeysSafe (δ : HashOutput) (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) :=
  (keys.1, fun T => if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then keys.2.1 T ^^^ δ else keys.2.1 T, keys.2.2)

theorem revealNextList_congr (parts : C.Party → Parts C)
    (adj adj' : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (committed : C.Party → Mail C E) (i : C.Party) (inbox : Mail C E) (h : adj i inbox = adj' i inbox) :
    revealNextList D parts adj committed i inbox = revealNextList D parts adj' committed i inbox := by
  unfold revealNextList
  simp only [h]

/-- Off the alias, the shift by `shiftKeysHidden` and the shift by `shiftKeysSafe` give the same rest of
the seed generation. -/
theorem listPost_agree (parts : C.Party → Parts C) (δ : HashOutput) (w : ListMid C E net.State)
    (h : ¬ MidAlias D net parts w) :
    listPost D net parts (shiftKeysHidden D parts δ) w = listPost D net parts (fun i _ => shiftKeysSafe D δ i) w := by
  unfold listPost
  unfold MidAlias at h
  rcases hw : w.2.2 with _ | r2
  · rfl
  · rw [hw] at h
    simp only
    unfold levelTail
    split_ifs
    · rfl
    congr 1
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true]
    simp only [hj, ite_false]
    rcases revealReady (commitInbox D w.1 w.2.1.1.2) j with _ | x
    · rfl
    dsimp only
    split_ifs
    · rfl
    congr 1
    refine revealNextList_congr D parts _ _ _ j _ ?_
    funext keys
    unfold shiftKeysHidden shiftKeysSafe
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext T
    dsimp only
    by_cases hT : KnownTo D.1 T
    · have hc : ¬ (j ∈ C.holders T ∧ HiddenCell D parts (termAddress D parts j (levelInbox D
          (revealReady (commitInbox D w.1 w.2.1.1.2)) (fun i _ => revealOutbox .seedGen i (parts i)) r2.2 j) T)) :=
        fun hc => h ⟨j, hj, T, hT, hc.1, hc.2⟩
      simp only [hc, hT, not_true_eq_false, and_false, ite_false]
    · have hcell : HiddenCell D parts (termAddress D parts j (levelInbox D
          (revealReady (commitInbox D w.1 w.2.1.1.2)) (fun i _ => revealOutbox .seedGen i (parts i)) r2.2 j) T) := by
        rw [termAddress_hidden D parts j _ T hT]
        exact ⟨T, hT, rfl⟩
      simp only [hcell, hT, not_false_eq_true, and_true]

end Split

/-! ## The runs -/

section Runs

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
theorem listSuffix_split (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (adj : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    listSuffix K circuits settings runLimit D A x adj =
      listPre D A.net x.1.1 x.1.2 x.2.1.1 x.2.1.2.2 x.2.2 >>= fun w =>
        listPost D A.net x.2.2 adj w >>= restOf K circuits settings runLimit D A x := by
  unfold listSuffix
  rw [seedGenList_split, bind_assoc]
  refine bind_congr fun w => bind_congr fun p => ?_
  rcases p with ⟨state, emu⟩
  rfl

/-- The list run up to the call of the adversary in round 2. The result is the prefix with its world
state, the seeds, and the result of `listPre` with its world state. The run starts from the empty
state, and the parts are drawn inside it. -/
def listMidRun (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ProbComp ((PrefixOut C A.net.State × LogState C) × (C.Term → HashOutput) ×
      (ListMid C E A.net.State × LogState C)) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let seed ← $ᵗ (C.Term → HashOutput)
  let m ← (simulateQ (compWorld prims D x.1.2.2 seed)
    (listPre D A.net x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2.2 x.1.2.2)).run x.2
  pure (x, seed, m)

/-- The list run after `listMidRun`, with the keys changed by `adj parts`. -/
def listTail (D : C.Coalition) (A : DkgTsigAdversary C E)
    (adj : (C.Party → Parts C) → C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (m : (PrefixOut C A.net.State × LogState C) × (C.Term → HashOutput) × (ListMid C E A.net.State × LogState C)) :
    ProbComp ((C.Party → Parts C) × (C.Term → HashOutput) × LogState C) := do
  let z ← (simulateQ (compWorld prims D m.1.1.2.2 m.2.1)
    (listPost D A.net m.1.1.2.2 (adj m.1.1.2.2) m.2.2.1 >>= restOf K circuits settings runLimit D A m.1.1)).run
      m.2.2.2
  pure (m.1.1.2.2, m.2.1, z.2)

omit [Fintype E] [DecidableEq E] in
theorem listRunWith_split (D : C.Coalition) (A : DkgTsigAdversary C E)
    (adj : (C.Party → Parts C) → C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    listRunWith prims K circuits settings runLimit D A adj id =
      listMidRun prims D A >>= listTail prims K circuits settings runLimit D A adj := by
  unfold listRunWith listMidRun listTail
  simp only [bind_assoc, pure_bind, id]
  refine bind_congr fun x => bind_congr fun seed => ?_
  rw [listSuffix_split, simulateQ_bind, StateT.run_bind, bind_assoc]

omit [Fintype E] [DecidableEq E] in
/-- An event of the run with the keys shifted by `shiftKeysHidden` has at most the probability of the
alias in `listMidRun` and the probability of the event in the run with `shiftKeysSafe`. The bound is a
mean over the whole run from the empty start. -/
theorem listRun_alias_le (D : C.Coalition) (A : DkgTsigAdversary C E) (δ : HashOutput)
    (event : (C.Party → Parts C) × (C.Term → HashOutput) × LogState C → Prop) :
    Pr{let r ← listRunShift prims K circuits settings runLimit D A δ}[event r] ≤
      Pr{let m ← listMidRun prims D A}[MidAlias D A.net m.1.1.2.2 m.2.2.1] +
        Pr{let r ← listRunWith prims K circuits settings runLimit D A (fun _ i _ => shiftKeysSafe D δ i) id}[event r] := by
  unfold listRunShift
  rw [listRunWith_split, listRunWith_split]
  refine prEvent_bind_le_add_of_agree _ _ _ _ _ fun m _ hm => ?_
  unfold listTail
  rw [listPost_agree D A.net m.1.1.2.2 δ m.2.2.1 hm]

/-- The bound of the alias. In the list run up to the call of the adversary in round 2, an honest
operator holds a known term whose derive address at its inbox of round 2 is a hidden cell with
probability at most `aliasCost D`. The inbox of round 2 is chosen on a view with no part of a hidden
term, and each of the at most `n k` known derivations meets one of the `h` hidden inputs with
probability `2^-(256 t)`. The bound is a mean over the whole run from the empty start. -/
def ListAliasBound : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    Pr{let m ← listMidRun prims D A}[MidAlias D A.net m.1.1.2.2 m.2.2.1] ≤ aliasCost D

/-- The run with `δ` added to the seed of each held hidden term is the list run. -/
def ListSafe : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (δ : HashOutput),
    listRunWith prims K circuits settings runLimit D A (fun _ i _ => shiftKeysSafe D δ i) id =
      listRun prims K circuits settings runLimit D A

omit [Fintype E] [DecidableEq E] in
/-- `ListAliasBound` and `ListSafe` give `ListShiftStep`. -/
theorem listShiftStep_of_parts (bound : ListAliasBound (C := C) (E := E) prims) (safe : ListSafe prims K circuits settings runLimit) :
    ListShiftStep prims K circuits settings runLimit := by
  intro D A δ event
  refine (listRun_alias_le prims K circuits settings runLimit D A δ event).trans ?_
  rw [safe D A δ]
  gcongr
  exact bound D A

end Runs

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listShiftStep_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listShiftStep_of_parts
