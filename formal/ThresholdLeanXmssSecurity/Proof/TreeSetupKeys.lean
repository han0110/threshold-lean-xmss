import ThresholdLeanXmssSecurity.Proof.TreeAgreement

/-!
# Agreement of the PRSS setup keys

The reveal round logs every shared-key hash that the echo round compares. Two
successful honest outputs therefore have equal shared-key inputs unless the
setup log contains a budget collision. The setup's early-abort branches return
no keys. The argument works from any incoming world state.

The pinned and current leanVM preparations were searched first. Their
`XmssSecurity.Seeded.resolves_sequenceFin` concerns the XMSS hash cache; the
existing threshold `sequenceFin_state_post` supplies the log traversal here.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}
variable (prims : Primitives) (D : C.Coalition)

private theorem setupAnswer_mono {a b : TreeSimLog C} (hab : a ⊆ b)
    {q : Query C} {h : HashOutput} (ha : TreeSimHashAnswer a q h) :
    TreeSimHashAnswer b q h := ha.imp (fun x => hab x) (fun x => hab x)

/-- Every hash call is recorded, including a call answered from the incoming cache. -/
theorem treeSetup_hash_logged (q : Query C) (s : TreeSimState C)
    (r : HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C)))).run s)) :
    TreeSimHashAnswer r.2.2 q r.1 := by
  have he := simulateQ_spec_query (treeSimLoggedWorld prims D) (.inr (.inr (.inl q)))
  change simulateQ (treeSimLoggedWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C))) =
    treeSimLoggedWorld prims D (.inr (.inr (.inl q))) at he
  rw [he] at hr
  change r ∈ support ((fun a : HashOutput × (HashCache C × HiddenCache C) =>
    (a.1, a.2, s.2 ++ [⟨.inr (.inr (.inl q)), a.1⟩])) <$>
      (streamWorld prims D (.inr (.inr (.inl q)))).run s.1) at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨a, _, rfl⟩ := hr
  exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))

/-- All answers of a hash traversal remain in its final log. -/
theorem treeSetup_hashes_logged {ι : Type} (qs : ι → Query C) (xs : List ι)
    (s : TreeSimState C) (r : List HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (xs.mapM fun i => hashQuery (qs i)) (LocalSpec C)))).run s)) :
    List.Forall₂ (fun i h => TreeSimHashAnswer r.2.2 (qs i) h) xs r.1 := by
  induction xs generalizing s r with
  | nil =>
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact .nil
  | cons i xs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hr
    exact .cons
      (setupAnswer_mono (treeSimLoggedWorld_prefix prims D _ a.2 b hb).subset
        (treeSetup_hash_logged prims D (qs i) s a ha))
      (ih a.2 b hb)

/-- A successful reveal row records the exact hashes that it later echoes. -/
theorem treeSetup_revealData_logged (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) (s : TreeSimState C)
    (r : Option (PrssKeys C × List HashOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealData i own committed revealed))).run s)) :
    ∀ row, r.1 = some row → ∀ j : C.Party,
      TreeSimHashAnswer r.2.2 (.sharedKeys .prss ((sharedTerms i j).map row.1.term))
        (row.2.getD j.val 0) := by
  unfold prssRevealData at hr
  split_ifs at hr with ha
  · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    intro row he
    cases he
  · unfold prssPostRevealData at hr
    simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨opens, _, hr⟩ := hr
    split_ifs at hr with hc
    · simp only [free_bind, free_pure, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨keys, _, shared, hshared, rfl⟩ := hr
      intro row he j
      cases he
      have hall := treeSetup_hashes_logged prims D
        (fun j => Query.sharedKeys .prss ((sharedTerms i j).map keys.1.2.1))
        C.parties keys.2 shared hshared
      have hj := forall₂_getD_idxOf _ _ _ hall j (by simp [Committee.parties]) 0
      simpa [Committee.parties] using hj
    · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      intro row he
      cases he

/-- The joint reveal traversal retains every successful operator's echo answers. -/
theorem treeSetup_revealRows_logged (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (s : TreeSimState C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealRows D active parts committed sent))).run s)) :
    ∀ i row, r.1 i = some row → i ∉ D.1 ∧ ∀ j : C.Party,
      TreeSimHashAnswer r.2.2 (.sharedKeys .prss ((sharedTerms i j).map row.1.term))
        (row.2.getD j.val 0) := by
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  rw [prssRevealRows, free_sequenceFin, simulateQ_sequenceFin] at hr
  apply (sequenceFin_state_post _
    (fun i out cache => ∀ row, out = some row → i ∉ D.1 ∧ ∀ j : C.Party,
      TreeSimHashAnswer cache.2 (.sharedKeys .prss ((sharedTerms i j).map row.1.term))
        (row.2.getD j.val 0)) ?_ ?_ s r hr).2
  · intro i cache result hresult
    refine ⟨(treeSimLoggedWorld_prefix prims D _ cache result hresult).subset, ?_⟩
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hresult
      subst result
      intro row he
      cases he
    · by_cases ha : active i
      · simp only [if_neg hi, if_pos ha] at hresult
        exact fun row he => ⟨hi, treeSetup_revealData_logged prims D i (parts i)
          (committed i) _ cache result hresult row he⟩
      · simp only [if_neg hi, if_neg ha, free_pure, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at hresult
        subst result
        intro row he
        cases he
  · intro i out cache next hle h row he
    exact ⟨(h row he).1, fun j => setupAnswer_mono hle ((h row he).2 j)⟩

private def setupFinishResult
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) : Option (PrssKeys C) :=
  if i ∈ D.1 then none else
    match rows i with
    | none => none
    | some row =>
      let inbox := fun j => if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i
      if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
        if ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [row.2.getD j.val 0]
        then some row.1 else none

private theorem setupFinish_local
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (fun j => prssFinishStep j (rows j)) sent i =
      pure (.done (setupFinishResult D rows sent i)) := by
  by_cases hi : i ∈ D.1
  · cases hrow : rows i <;> simp [roundLocal, prssFinishStep, hrow, hi, setupFinishResult]
  · cases hrow : rows i with
    | none => simp [roundLocal, prssFinishStep, hrow, hi, setupFinishResult]
    | some row =>
      simp only [roundLocal, hrow, prssFinishStep, if_neg hi]
      let inbox : Mail C E := fun j => if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i
      change advance (exchangeResume (fun received => do
        require (∀ j, j ≠ i → Msg.hashesOf (received j) = [row.2.getD j.val 0])
        pure row.1) inbox) = pure (.done (setupFinishResult D rows sent i))
      simp only [setupFinishResult, if_neg hi, hrow]
      change _ = (pure (Step.done (C := C) (E := E) (G := RealSpec)
        (if C.parties.any (fun j => Msg.isAbort (inbox j)) then none
        else if ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [row.2.getD j.val 0]
          then some row.1 else none)) : OracleComp (LocalSpec C) _)
      rw [exchangeResume]
      by_cases ha : C.parties.any (fun j => Msg.isAbort (inbox j)) = true
      · simp only [if_pos ha]
        rfl
      · simp only [if_neg ha]
        rw [advance_require_bind]
        split_ifs <;> rfl

/-- The final setup round only exchanges and checks the recorded echo hashes. -/
private theorem setupFinish_round (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (rows : C.Party → Option (PrssKeys C × List HashOutput)) :
    stepRound worldRoles D A noFunctionality state (fun i => prssFinishStep i (rows i)) = (do
      let adv ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (prssFinishStep i (rows i)).outbox c else none)
      pure (adv.1, fun i => Step.done (C := C) (E := E) (G := RealSpec)
        (setupFinishResult D rows adv.2 i), adv.2)) := by
  rw [stepRound_real]
  apply bind_congr
  rintro ⟨state', sent⟩
  dsimp only
  rw [show roundLocal D (fun i => prssFinishStep i (rows i)) sent =
    (fun i => pure (.done (setupFinishResult D rows sent i))) from
      funext (setupFinish_local D rows sent)]
  simp only [sequenceFin_pure, free_pure, pure_bind]

private theorem setupFinish_some
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) (ki : PrssKeys C)
    (hi : setupFinishResult D rows sent i = some ki) :
    i ∉ D.1 ∧ ∃ shared, rows i = some (ki, shared) ∧
      ∀ j, j ≠ i → Msg.hashesOf (if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i) = [shared.getD j.val 0] := by
  unfold setupFinishResult at hi
  split_ifs at hi with hcorrupt
  cases hrow : rows i with
  | none => simp [hrow] at hi
  | some row =>
    simp only [hrow] at hi
    split_ifs at hi with ha hc
    cases hi
    exact ⟨hcorrupt, row.2, rfl, hc⟩

/-- The echo agreement argument using the actual lists returned by the reveal round. -/
theorem treeSetup_echo_agree
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (log : TreeSimLog C)
    (logged : ∀ i row, rows i = some row → ∀ j : C.Party,
      TreeSimHashAnswer log (.sharedKeys .prss ((sharedTerms i j).map row.1.term))
        (row.2.getD j.val 0))
    (good : ¬ TreeSimHashBudgetCollision log)
    (i j : C.Party) (ki kj : PrssKeys C)
    (hi : setupFinishResult D rows sent i = some ki)
    (hj : setupFinishResult D rows sent j = some kj) :
    ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T := by
  by_cases hij : i = j
  · subst j
    have hk : ki = kj := Option.some.inj (hi.symm.trans hj)
    subst kj
    exact fun _ _ _ => rfl
  obtain ⟨_, si, hri, hci⟩ := setupFinish_some D rows sent i ki hi
  obtain ⟨hjD, sj, hrj, _⟩ := setupFinish_some D rows sent j kj hj
  have he := hci j (Ne.symm hij)
  simp only [if_neg hjD, hrj, prssFinishStep, Step.delivered, if_neg hij,
    Msg.hashesOf, List.cons.injEq, and_true] at he
  have hq : Query.sharedKeys (C := C) .prss ((sharedTerms i j).map ki.term) =
      Query.sharedKeys .prss ((sharedTerms j i).map kj.term) := by
    by_contra hn
    exact good ⟨.sharedKeys .prss ((sharedTerms i j).map ki.term),
      .sharedKeys .prss ((sharedTerms j i).map kj.term), si.getD j.val 0, trivial, trivial, hn,
      logged i (ki, si) hri j, he ▸ logged j (kj, sj) hrj i⟩
  have hl := (Query.sharedKeys.inj hq).2
  rw [sharedTerms_comm j i] at hl
  intro T hiT hjT
  exact List.map_eq_map_iff.mp hl T (by simp [sharedTerms, Committee.terms, hiT, hjT])

/-- One echo round gives agreement from its logged reveal rows. -/
theorem treeSetup_finish_agree (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (s : TreeSimState C)
    (logged : ∀ i row, rows i = some row → ∀ j : C.Party,
      TreeSimHashAnswer s.2 (.sharedKeys .prss ((sharedTerms i j).map row.1.term))
        (row.2.getD j.val 0))
    (r : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executeRounds worldRoles D A noFunctionality 1 state
        (fun i => prssFinishStep i (rows i)))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (i j : C.Party) (ki kj : PrssKeys C)
    (hi : r.1.2 i = some ki) (hj : r.1.2 j = some kj) :
    ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T := by
  rw [executeRounds] at hr
  split_ifs at hr with hd
  · simp only [prssFinishStep_output, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hr
    subst r
    cases hi
  · rw [setupFinish_round] at hr
    simp only [bind_assoc, pure_bind, executeRounds, Step.output, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      mem_support_pure_iff] at hr
    obtain ⟨adv, hadv, rfl⟩ := hr
    exact treeSetup_echo_agree D rows adv.1.2 adv.2.2
      (fun i row hrow j => setupAnswer_mono
        (treeSimLoggedWorld_prefix prims D _ s adv hadv).subset (logged i row hrow j))
      good i j ki kj hi hj

/-- The complete setup establishes agreement from every incoming world state. -/
theorem treeSetup_phase_agree (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (s : TreeSimState C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      setupRounds state (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s))
    (good : ¬ TreeSimHashBudgetCollision p.2.2)
    (i j : C.Party) (ki kj : PrssKeys C)
    (hi : p.1.2 i = some ki) (hj : p.1.2 j = some kj) :
    ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T := by
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  change p ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (1 + 2) state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run s) at hp
  rw [executePhase_prssSetup_prefix] at hp
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨data, _, adv, _, hp⟩ := hp
  split_ifs at hp with habort
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hp
    subst p
    cases hi
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
    obtain ⟨adv', _, rows, hrows, hp⟩ := hp
    have logged := treeSetup_revealRows_logged prims D _ _ _ _ adv'.2 rows hrows
    exact treeSetup_finish_agree prims D A _ rows.1 rows.2
      (fun i row hrow => (logged i row hrow).2) p hp good i j ki kj hi hj

/-- The exact setup-key agreement obligation of `TreeAgreement`. -/
theorem treeAgreementSetupKeys : TreeAgreementSetupKeys (C := C) (E := E) prims := by
  intro D A x z p hp good i j ki kj hi hj
  simp only [treeSaltSetup, mem_support_bind_iff] at hp
  obtain ⟨start, _, hp⟩ := hp
  exact treeSetup_phase_agree prims D A start.1 start.2 p hp good i j ki kj hi hj

/-- info: 'ThresholdLeanXmssSecurity.treeSetup_revealRows_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSetup_revealRows_logged

/-- info: 'ThresholdLeanXmssSecurity.treeSetup_phase_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSetup_phase_agree

/-- info: 'ThresholdLeanXmssSecurity.treeAgreementSetupKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeAgreementSetupKeys

end ThresholdLeanXmssSecurity
