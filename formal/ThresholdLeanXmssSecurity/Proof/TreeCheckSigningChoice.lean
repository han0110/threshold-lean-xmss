import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkHeadInputs
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSigning

/-! # Agreement of signing choices in the actual ordered local pass

The selection witness keeps its original cache and log prefixes. Later heads
are compared only along clean supported runs of that same pass.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckSigningChoice
open TreeCheckWalkRecipe TreeCheckWalkCoverage TreeCheckWalkState TreeCheckWalkEntry
open TreeCheckWalkEncoding
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E α β : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition)

-- Port of TreeCheckWalkRecipe.select_some, retaining both original prefixes.
theorem select_some_prefix : ∀ {n : ℕ} (gate : Fin n → OracleComp (WorldSpec C) (Option α))
    (s : TreeSimState C) (chosen : First α n) (after : TreeSimState C),
    (some chosen, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D) (select gate)).run s) →
    ∃ i before, s.1.1 ≤ before.1.1 ∧ s.2 <+: before.2 ∧
      (some chosen.value, after) ∈ support
        ((simulateQ (treeSimLoggedWorld prims D) (gate i)).run before)
  | 0, gate, s, chosen, after, run => by cases chosen
  | n + 1, gate, s, chosen, after, run => by
      simp only [select, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨out, ho, run⟩ := run
      cases accepted : out.1 with
      | some a =>
          simp only [accepted, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
          cases run
          exact ⟨0, s, le_rfl, (by simp),
            by simpa only [First.value, ← accepted, Prod.mk.eta] using ho⟩
      | none =>
          simp only [accepted, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at run
          obtain ⟨r, hr, he⟩ := run
          cases result : r.1 with
          | none => simp only [result, Option.map_none] at he; cases he
          | some next =>
              simp only [result, Option.map_some] at he
              cases he
              obtain ⟨i, before, grows, pref, hit⟩ := select_some_prefix (fun i : Fin n => gate i.succ) out.2 next r.2
                (by simpa only [← result] using hr)
              exact ⟨i.succ, before, (treeSim_logged_grows prims D _ _ _ ho).trans grows,
                (treeSimLoggedWorld_prefix prims D _ _ _ ho).trans pref, hit⟩

/-- One component of a logged sequence keeps its actual input and output worlds. -/
theorem sequence_member : ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α)
    (s : TreeSimState C) (r : (Fin n → α) × TreeSimState C),
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (Concrete.sequenceFin f)).run s) →
    ∀ i, ∃ before after, s.1.1 ≤ before.1.1 ∧ s.2 <+: before.2 ∧ after.2 <+: r.2.2 ∧
      (r.1 i, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D) (f i)).run before)
  | 0, _, _, _, _, i => i.elim0
  | n+1, f, s, r, run, i => by
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨head, hh, tail, ht, rfl⟩ := run
    cases i using Fin.cases with
    | zero => exact ⟨s, head.2, le_rfl, (by simp),
        treeSimLoggedWorld_prefix prims D _ head.2 tail ht, hh⟩
    | succ i =>
      obtain ⟨before, after, grows, pref, suffix, hit⟩ :=
        sequence_member (fun i : Fin n => f i.succ) head.2 tail ht i
      exact ⟨before, after, (treeSim_logged_grows prims D _ _ _ hh).trans grows,
        (treeSimLoggedWorld_prefix prims D _ _ _ hh).trans pref, suffix, hit⟩

/-- A selected continuation advances only the common chosen branch when its
later successful heads agree along this actual clean pref. -/
theorem remaining_advance_common (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec β) (chosen : First α C.n)
    (s : TreeSimState C)
    (r : (C.Party → Step C E RealSpec β) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (Concrete.sequenceFin fun i => free (advance (remainingPrograms gate cont (some chosen) i).run))).run s))
    (agree : ∀ i before after value, s.1.1 ≤ before.1.1 → s.2 <+: before.2 → after.2 <+: r.2.2 →
      (some value, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (gate i))).run before) →
      value = chosen.value) :
    ∀ i, r.1 i = .done none ∨ r.1 i ∈ support (advance (cont i chosen.value).run) := by
  intro i
  obtain ⟨before, after, grows, pref, suffix, hit⟩ := sequence_member prims D _ _ _ run i
  rw [remainingPrograms_typed, localOption_advance] at hit
  rcases remainingGates_kind gate chosen i with dead | common | untouched
  · simp only [dead, free_pure, localContinue, pure_bind, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq] at hit
    exact .inl hit.1
  · simp only [common, free_pure, localContinue, pure_bind] at hit
    exact .inr (treeSimCheck_support_free _ (treeCheck_logged_support prims D _ _ hit))
  · rw [untouched] at hit
    simp only [localContinue, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hit
    obtain ⟨out, head, tail⟩ := hit
    cases value : out.1 with
    | none =>
      simp only [value, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at tail
      exact .inl tail.1
    | some value' =>
      simp only [value] at tail
      have equal := agree i before out.2 value' grows pref
        ((treeSimLoggedWorld_prefix prims D _ _ _ tail).trans suffix)
        (by simpa only [← value, Prod.mk.eta] using head)
      rw [equal] at tail
      exact .inr (treeSimCheck_support_free _ (treeCheck_logged_support prims D _ _ tail))

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (top : TopTree) (b : Fin (2 ^ layerHeight))
variable (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
variable (z : Aux) (Z : Distinguisher C A.State TreeOutput)

/-- Positive batch size gives a first signing chunk for every encoding. -/
theorem signing_chunks_nonempty (positive : 0 < settings.batchSize) (encoding : Encoding) :
    ∃ head rest, chunks settings.batchSize (signJobs b encoding) = head :: rest := by
  apply List.exists_cons_of_ne_nil
  apply List.ne_nil_of_length_pos
  rw [length_chunks]
  have jobs : 0 < (signJobs b encoding).length := by
    simp only [signJobs, List.length_map]
    decide
  exact Nat.div_pos (by omega) positive

/-- The selected original head and every later successful head in the same
clean pass have the same choice. Their callers advance one exchange. -/
theorem selected_pass_common (positive : 0 < settings.batchSize)
    (dealt : DealtInputs D x)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : p ∈ support (treeSaltSetup prims D A x z))
    (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings (.bottom b)).length) q)
    (point : SigningPoint C)
    (matching : SigningMatches K D A circuits settings top x p.1.2
      (firstChunks settings (.bottom b)).length b q point)
    (chosen : First PublicChoice C.n) (selected : TreeSimState C)
    (selection : (some chosen, selected) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (select fun i => free (maskedGate D
        (fun i => signingHead (x i).parameter b (point.outputs i) (point.tail i)) i))).run q.world))
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (remainingPrograms
        (maskedGate D fun i => signingHead (x i).parameter b (point.outputs i) (point.tail i))
        (maskedCont D fun i => signingCont K circuits settings ⟨i, x i, setupKeys p.1.2 i⟩ top b
          (point.outputs i) (point.records i) (signingInitial K D circuits settings (.bottom b) x))
        (some chosen)))).run selected))
    (clean : ¬ TreeSimHashBudgetCollision out.2.2) :
    ∀ i, i ∉ D.1 → out.1 i = .done none ∨ ∀ inbox,
      Residual 1
        (callerProgram K D circuits settings top (.bottom b) x p.1.2 (firstChunks settings (.bottom b)).length
          (signingCaller point.outputs point.records (fun _ => pure (some chosen.value)) chosen.value) i).run
        (resumed (out.1 i) inbox) := by
  obtain ⟨first, before, grows, pref, firstRun⟩ := select_some_prefix prims D _ _ _ _ selection
  have honest : first ∉ D.1 := by
    intro corrupt
    simp only [maskedGate, if_pos corrupt, free_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at firstRun
  simp only [maskedGate, if_neg honest] at firstRun
  rw [remainingPrograms_start, ← remainingPrograms_pass] at run
  have each := remaining_advance_common prims D _ _ chosen selected out run (by
    intro i current after value hg hp suffix headRun
    by_cases corrupt : i ∈ D.1
    · simp only [maskedGate, if_pos corrupt, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at headRun
    · simp only [maskedGate, if_neg corrupt] at headRun
      exact (TreeCheckWalkHeadInputs.signingHeadsAgree K circuits settings prims positive top b D A x z Z
        dealt p setupRun q reached point matching first i honest corrupt before grows pref chosen.value selected
        firstRun current hg hp value after headRun
        (fun bad => clean (treeSimHashBudgetCollision_mono suffix bad))).symm)
  intro i hi
  rcases each i with aborted | continued
  · exact .inl aborted
  · simp only [maskedCont, if_neg hi] at continued
    obtain ⟨head, rest, chunks⟩ := signing_chunks_nonempty settings b positive chosen.value.2.2
    rw [signingCont_caller K D circuits settings top x p.1.2 b point.outputs point.records
      chosen.value head rest chunks i] at continued
    exact .inr (fun inbox => Residual.of_advance (out.1 i) continued inbox)

/-- Every clean actual pass from the reached first signing boundary either
aborts everywhere or advances callers of its actual first successful choice. -/
theorem actual_pass_common (positive : 0 < settings.batchSize)
    (dealt : DealtInputs D x)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : p ∈ support (treeSaltSetup prims D A x z))
    (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings (.bottom b)).length) q)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D q.program)).run q.world))
    (clean : ¬ TreeSimHashBudgetCollision out.2.2) :
    ∃ point : SigningPoint C,
      SigningMatches K D A circuits settings top x p.1.2
        (firstChunks settings (.bottom b)).length b q point ∧
      ((∀ i, i ∉ D.1 → out.1 i = .done none) ∨
        ∃ (chosen : First PublicChoice C.n) (selected : TreeSimState C),
          (some chosen, selected) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
            (select fun i => free (maskedGate D
              (fun i => signingHead (x i).parameter b (point.outputs i) (point.tail i)) i))).run q.world) ∧
          ∀ i, i ∉ D.1 → out.1 i = .done none ∨ ∀ inbox,
            Residual 1
              (callerProgram K D circuits settings top (.bottom b) x p.1.2 (firstChunks settings (.bottom b)).length
                (signingCaller point.outputs point.records (fun _ => pure (some chosen.value)) chosen.value) i).run
              (resumed (out.1 i) inbox)) := by
  obtain ⟨point, matching⟩ := walkStateEntry prims K circuits settings positive top b D A x z Z dealt p setupRun q reached
  refine ⟨point, matching, ?_⟩
  let gate := fun i => signingHead (x i).parameter b (point.outputs i) (point.tail i)
  let cont := fun i => signingCont K circuits settings ⟨i, x i, setupKeys p.1.2 i⟩ top b
    (point.outputs i) (point.records i) (signingInitial K D circuits settings (.bottom b) x)
  have start : startSteps worldRoles D q.program =
      startSteps worldRoles D (fun i => treeLockstepLocalOption (gate i) >>= cont i) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
    · simp only [if_neg hi, matching.2 i hi, signingHead_program, gate, cont]
  rw [start, start_select_programs] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨selected, selection, run⟩ := run
  cases chosen : selected.1 with
  | none =>
    rw [chosen, remainingPrograms_start, ← remainingPrograms_pass] at run
    simp only [remainingPrograms, advance_run_failure, free_pure, sequenceFin_pure,
      simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst out
    exact .inl (fun _ _ => rfl)
  | some chosen' =>
    have actual : (some chosen', selected.2) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (select fun i => free (maskedGate D gate i))).run q.world) := by
      simpa only [← chosen, Prod.mk.eta] using selection
    refine .inr ⟨chosen', selected.2, actual, ?_⟩
    rw [chosen] at run
    exact selected_pass_common prims D K circuits settings top b A x z Z positive dealt p setupRun q reached
      point matching chosen' selected.2 actual out run clean

end ThresholdLeanXmssSecurity.TreeCheckSigningChoice

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningChoice.select_some_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningChoice.select_some_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningChoice.sequence_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningChoice.sequence_member

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningChoice.remaining_advance_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningChoice.remaining_advance_common

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningChoice.selected_pass_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningChoice.selected_pass_common

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSigningChoice.actual_pass_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckSigningChoice.actual_pass_common
